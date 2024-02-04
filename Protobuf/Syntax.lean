import Lean.Syntax
import Lean.Data.Parsec

namespace Protobuf.Syntax

open Lean Data Parsec ParseResult

-- https://protobuf.dev/reference/protobuf/proto3-spec/

-- Helpers

syntax:20 term:21 " <!> " term:20 : term

macro_rules | `($x <!> $y) => `(binop_lazy% HOrElse.hOrElse (attempt $x) $y)

def hexVal (c : Char) : Nat :=
  let base := if c.val >= 'A'.val && c.val <= 'F'.val then 'A'.val - 10
    else if c.val >= 'a'.val && c.val <= 'f'.val then 'a'.val - 10
    else '0'.val
  (c.val - base).toNat

def octVal (c : Char) : Nat := (c.val - '0'.val).toNat

def optional (p : Parsec α) := fun it => match p it with
  | success rem a => success rem (some a)
  | error _ _ => success it none

-- TODO: Why aren't comments mentioned in the grammar?
def lineComment := pstring "//" *> many (satisfy (· != '\n')) *> pure ()

def blockComment := pstring "/*" *>
  many ((satisfy (· != '*')) <!> (anyChar *> satisfy (· != '/'))) *> pure () <*
  pstring "*/"

def ws := many (lineComment <!> blockComment <!>
    (pchar ' ' *> pure ()) <!>
    (pchar '\n' *> pure ()) <!>
    (pchar '\r' *> pure ()) <!>
    (pchar '\t' *> pure ())) *> pure ()

-- TODO: Fix builtin many, need to figure out what's wrong with <|>
partial def manyCore (p : Parsec α) (acc : Array α) : Parsec $ Array α :=
  (do manyCore p (acc.push $ <- p)) <!> pure acc

def many (p : Parsec α) : Parsec $ Array α := manyCore p #[]

def many1 (p : Parsec α) : Parsec $ Array α := do manyCore p #[<- p]

partial def sepByCore (p : Parsec α) (s : Parsec β) (acc : Array α) : Parsec $ Array α :=
  (s *> do sepByCore p s (acc.push $ <- p)) <!> (pure acc)

def sepBy1 (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do sepByCore p s #[<- p]

def sepBy (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  let res <- optional (sepBy1 p s)
  return Option.getD res #[]

def pack (arr : Array Char) := String.mk arr.toList

def manyn (n : Nat) (p : Parsec α) : Parsec $ Array α := do
  if n = 0 then return Array.empty else
  let init <- manyn (n - 1) p
  let last <- p
  return init.push last

private
partial def untilEofCore (p : Parsec α) (acc : Array α) : Parsec $ Array α := do
  (ws *> eof *> pure acc) <!> (do manyCore p (acc.push $ <- p))

def untilEof (p : Parsec α) : Parsec $ Array α := untilEofCore p #[]

def sepBy1UntilEof (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  let start <- p
  let rest <- untilEof (s *> p)
  return (Array.singleton start).append rest

def sepByUntilEof (p : Parsec α) (s : Parsec β) : Parsec $ Array α := do
  (ws *> eof *> pure #[]) <!> (sepBy1UntilEof p s)

-- Parser

--- Lexical Elements

---- Letters and Digits

def letter := satisfy Char.isAlpha

def decimalDigit := satisfy Char.isDigit

def octalDigit := satisfy fun c => c.val >= '0'.val && c.val <= '7'.val

def hexDigit :=
  satisfy fun c => c.isDigit ||
  (c.val >= 'A'.val && c.val <= 'F'.val) ||
  (c.val >= 'a'.val && c.val <= 'f'.val)

---- Identifiers

def ident :=
  let ident := do
    let start <- letter
    let rest <- many $ letter <!> decimalDigit <!> pchar '_'
    return start.toString.append (pack rest)
  orElse ident fun () => fail "expected identifier"

def fullIdent := sepBy1 ident (pchar '.')

def messageName := ident

def enumName := ident

def fieldName := ident

def oneofName := ident

def mapName := ident

def serviceName := ident

def rpcName := ident

structure MessageType where
  leadingDot : Bool
  name : Array String
  deriving Repr

def messageType : Parsec MessageType := do
  let leadingDot <- Option.isSome <$> optional (pchar '.')
  let idents <- many (ident <* pchar '.')
  let messageName <- messageName
  return { leadingDot, name := idents.push messageName }

structure EnumType where
  leadingDot : Bool
  name : Array String
  deriving Repr

def enumType : Parsec EnumType := do
  let leadingDot <- Option.isSome <$> optional (pchar '.')
  let name <- sepBy1 ident (pchar '.')
  return { leadingDot, name }

---- Integer Literals

def decimalLit : Parsec Int := do
  let neg <- Option.isSome <$> optional (pchar '-')
  ws
  let start <- satisfy fun c => Char.isDigit c && c != '0'
  let rest <- pack <$> many decimalDigit
  let base := (start.toString.append rest).toInt!
  return if neg then base.neg else base

def octalLit : Parsec Int := do
  let neg <- Option.isSome <$> optional (pchar '-')
  ws *> pchar '0' *> do
  let base <- Array.foldl (fun sum c => sum * 8 + (Int.ofNat (octVal c))) 0 <$> many octalDigit
  return if neg then base.neg else base

def hexLit : Parsec Int := do
  let neg <- Option.isSome <$> optional (pchar '-')
  ws *> pchar '0' *> (pchar 'x' <!> pchar 'X') *> do
  let base <- Array.foldl (fun sum c => sum * 16 + (Int.ofNat (hexVal c))) 0 <$> many hexDigit
  return if neg then base.neg else base

def intLit : Parsec Int :=
  let intLit := decimalLit <!> octalLit <!> hexLit
  orElse intLit fun () => fail "expected integer literal"

---- Floating-point Literals

structure Decimals where
  minus : Bool
  value : Nat

def decimals := many1 decimalDigit

def exponent := (pchar 'e' <!> pchar 'E') *> do
  let sign <- optional (pchar '+' <!> pchar '-')
  let decimals <- decimals
  match sign with
  | some sign => return String.mk (sign :: decimals.toList)
  | none => return pack decimals

def floatLit : Parsec Float :=
  let floatLit := do
    let sign <- optional (pchar '+' <!> pchar '-')
    let rest <- pstring "inf" <!> pstring "nan"
    match sign with
    | some sign => return String.mk (sign :: rest.toList)
    | none => return rest
  let parseFloat! s :=
    let (m, sign, e) := Option.get! $ Syntax.decodeScientificLitVal? s
    OfScientific.ofScientific m sign e
  orElse (parseFloat! <$> floatLit) fun () => fail "expected float literal"

---- Boolean

def boolLit : Parsec Bool :=
  pstring "true" *> pure Bool.true <!> pstring "false" *> pure Bool.false

---- String Literals

def hexEscape : Parsec Char := pchar '\\' *> (pchar 'x' <!> pchar 'X') *> do
  let d1 <- hexDigit
  let d2 <- optional hexDigit
  match d2 with
  | some d2 => return Char.ofNat $ (hexVal d1) * 16 + hexVal d2
  | none => return Char.ofNat $ hexVal d1

def octEscape := pchar '\\' *> do
  let d1 <- octalDigit
  let d2 <- optional octalDigit
  match d2 with
  | some d2 =>
    let d3 <- optional octalDigit
    match d3 with
    | some d3 => return Char.ofNat $ (octVal d1) * 16 * 16 + (octVal d2) * 16 + octVal d3
    | none => return Char.ofNat $ (octVal d1) * 16 + octVal d2
  | none => return Char.ofNat $ octVal d1

def charEscape : Parsec Char := pchar '\\' *> do
  (pchar 'a' *> pure (Char.ofNat 7)) <!>
  (pchar 'b' *> pure (Char.ofNat 8)) <!>
  (pchar 'f' *> pure (Char.ofNat 12)) <!>
  (pchar 'n' *> pure '\n') <!>
  (pchar 'r' *> pure '\r') <!>
  (pchar 't' *> pure '\t') <!>
  (pchar 'v' *> pure (Char.ofNat 11)) <!>
  (pchar '\\') <!>
  (pchar '\'') <!>
  (pchar '"')

def unicodeEscape := pchar '\\' *> pchar 'u' *>
  Char.ofNat <$> Array.foldl (fun sum c => sum * 16 + hexVal c) 0 <$> manyn 4 hexDigit

def unicodeLongEscape :=
  let hexes n := Char.ofNat <$> Array.foldl (fun sum c => sum * 16 + hexVal c) 0 <$> manyn n hexDigit
  pchar '\\' *> pchar 'U' *>
  (pstring "000" *> hexes 5) <!> (pstring "0010" *> hexes 4)
  
def charValue (quote : Char) : Parsec Char := do
  let normalChar := satisfy fun x => [(Char.ofNat 0), '\n', '\\', quote].notElem x
  normalChar <!> hexEscape <!> octEscape <!> charEscape <!> unicodeEscape <!> unicodeLongEscape

-- TODO: The grammar allows quotes inside strings...
def strLitSingle : Parsec String :=
  let strLitSingle := (String.mk ∘ Array.toList) <$>
    ((pchar '\'' *> many (charValue '\'') <* pchar '\'') <!> (pchar '"' *> many (charValue '"') <* pchar '"'))
  orElse strLitSingle fun () => fail "expected string literal"

def strLit : Parsec String := do
  let strlitSingles <- many strLitSingle
  return "".intercalate strlitSingles.toList

---- EmptyStatement

def emptyStatement := pchar ';'

---- Constant

inductive PMPrefix where
  | plus
  | minus
  deriving Repr

inductive Constant where
  | ident (i : Array String)
  | intLit (i : (Option PMPrefix) × Int)
  | floatLit (f : (Option PMPrefix) × Float)
  | strLit (s : String)
  | boolLit (b : Bool)
  -- TODO: MessageValue
  deriving Repr

def pmPrefixed (a : Parsec α) : Parsec $ (Option PMPrefix) × α := do
  let prefix' <- optional (((pchar '+' *> pure PMPrefix.plus) <!> (pchar '-' *> pure PMPrefix.minus)) <* ws)
  let value <- a
  pure (prefix', value)

def constant :=
  (Constant.boolLit <$> boolLit) <!>
  (Constant.ident <$> fullIdent) <!>
  (Constant.intLit <$> pmPrefixed intLit) <!>
  (Constant.floatLit <$> pmPrefixed floatLit) <!>
  (Constant.strLit <$> strLit)
  -- TODO: MessageValue

--- Syntax

def syntax' : Parsec Unit :=
  pstring "syntax" *> ws *>
  pchar '=' *> ws *>
  (pstring "\"proto3\"" <!> pstring "'proto3'") *> pure ()

--- Import Statement

inductive ImportKind where
  | weak
  | public
  | normal
  deriving Repr

structure Import where
  kind : ImportKind
  name : String
  deriving Repr

def import' : Parsec Import := do
  pstring "import" *> ws
  let kind <- optional
    ((pstring "weak" *> pure ImportKind.weak <* ws <!>
      (pstring "public" *> pure ImportKind.public <* ws)) <* ws)
  let name <- strLit
  pchar ';' *> pure { kind := Option.getD kind ImportKind.normal, name : Import }

--- Package

def package := pstring "package" *> ws *> fullIdent <* ws <* pchar ';'

--- Option

structure FullIdentOptionNamePart where
  leadingDot : Bool
  fullIdent : Array String
  deriving Repr

inductive OptionNamePart where
  | ident (i : String)
  | fullIdent (f : FullIdentOptionNamePart)
  deriving Repr

-- TODO: Ask upstream what the proper definition for this is, the grammar says:
--
-- optionNamePart = { ident | "(" ["."] fullIdent ")" }
--
-- ...but that's obviously wrong. For now we're going with:
--
-- optionNamePart = ident | "(" ["."] fullIdent ")"
def optionNamePart : Parsec OptionNamePart :=
  let bracketedFullIdent : Parsec FullIdentOptionNamePart := do
    pchar '(' *> ws
    let leadingDot <- Option.isSome <$> optional (pchar '.' <* ws)
    let fullIdent <- fullIdent
    <* ws <* pchar ')'
    pure { leadingDot, fullIdent }
  (OptionNamePart.ident <$> ident) <!> (OptionNamePart.fullIdent <$> bracketedFullIdent)

def optionName : Parsec $ Array OptionNamePart := sepBy1 optionNamePart (ws *> pchar '.' <* ws)

structure Option' where
  name : Array OptionNamePart
  constant : Constant
  deriving Repr

def option : Parsec Option' := do
  pstring "option" *> ws
  let name <- optionName
  ws *> pchar '=' *> ws
  let constant <- constant
  ws *> pchar ';' *>
  pure { name, constant }

--- Fields

inductive Type' where
  | double
  | float
  | int32
  | int64
  | uint32
  | uint64
  | sint32
  | sint64
  | fixed32
  | fixed64
  | sfixed32
  | sfixed64
  | bool
  | string
  | bytes
  | messageType (m : MessageType)
  | enumType (e : EnumType)
  deriving Repr

def type : Parsec Type' :=
  pstring "double" *> pure Type'.double <!>
  pstring "float" *> pure Type'.float <!>
  pstring "int32" *> pure Type'.int32 <!>
  pstring "int64" *> pure Type'.int64 <!>
  pstring "uint32" *> pure Type'.uint32 <!>
  pstring "uint64" *> pure Type'.uint64 <!>
  pstring "sint32" *> pure Type'.sint32 <!>
  pstring "sint64" *> pure Type'.sint64 <!>
  pstring "fixed32" *> pure Type'.fixed32 <!>
  pstring "fixed64" *> pure Type'.fixed64 <!>
  pstring "sfixed32" *> pure Type'.sfixed32 <!>
  pstring "sfixed64" *> pure Type'.sfixed64 <!>
  pstring "bool" *> pure Type'.bool <!>
  pstring "string" *> pure Type'.string <!>
  pstring "bytes" *> pure Type'.bytes <!>
  (Type'.messageType <$> messageType) <!>
  (Type'.enumType <$> enumType)

def fieldNumber := intLit

---- Normal Field

structure FieldOption where
  name : Array OptionNamePart
  value : Constant
  deriving Repr

def fieldOption : Parsec FieldOption := do
  let name <- optionName
  ws *> pchar '=' *> ws
  let value <- constant
  return { name, value }

def fieldOptions := sepBy1 fieldOption (ws *> pchar ',' <* ws)

inductive FieldModifier where
  | repeated
  | optional
  deriving Repr

structure Field where
  modifier : Option FieldModifier
  type : Type'
  name : String
  number : Int
  options : Array FieldOption
  deriving Repr

def field : Parsec Field := do
  let modifier <- optional (((pstring "repeated" *> pure FieldModifier.repeated) <!>
    (pstring "optional" *> pure FieldModifier.optional)) <* ws)
  let type <- type
  ws
  let name <- fieldName
  ws *> pchar '=' *> ws
  let number <- fieldNumber
  let options <- optional (ws *> pchar '[' *> ws *> fieldOptions <* ws <* pchar ']')
  ws *> pchar ';' *>
  return { modifier, type, name, number, options := Option.getD options #[] }

---- Oneof and Oneof Field

structure OneofField where
  type : Type'
  name : String
  number : Int
  options : Array FieldOption
  deriving Repr

def oneofField : Parsec OneofField := do
  let type <- type
  ws
  let name <- fieldName
  ws *> pchar '=' *> ws
  let number <- fieldNumber
  let options <- optional (ws *> pchar '[' *> ws *> fieldOptions <* ws <* pchar ']')
  ws *> pchar ';' *>
  return { type, name, number, options := Option.getD options #[] }

inductive OptionOrOneofField where
  | option (o : Option')
  | field (o : OneofField)
  deriving Repr

structure Oneof where
  name : String
  optionsAndFields : Array OptionOrOneofField
  deriving Repr

def oneof : Parsec Oneof := do
  pstring "oneof" *> ws
  let name <- oneofName
  ws *> pchar '{' *> ws
  let optionsAndFields <- sepBy
    (OptionOrOneofField.option <$> option <!>
      OptionOrOneofField.field <$> oneofField) ws
  ws *> pchar '}' *>
  return { name, optionsAndFields }

---- Map Field

inductive KeyType where
  | int32
  | int64
  | uint32
  | uint64
  | sint32
  | sint64
  | fixed32
  | fixed64
  | sfixed32
  | sfixed64
  | bool
  | string
  deriving Repr

def keyType : Parsec KeyType :=
  pstring "int32" *> pure KeyType.int32 <!>
  pstring "int64" *> pure KeyType.int64 <!>
  pstring "uint32" *> pure KeyType.uint32 <!>
  pstring "uint64" *> pure KeyType.uint64 <!>
  pstring "sint32" *> pure KeyType.sint32 <!>
  pstring "sint64" *> pure KeyType.sint64 <!>
  pstring "fixed32" *> pure KeyType.fixed32 <!>
  pstring "fixed64" *> pure KeyType.fixed64 <!>
  pstring "sfixed32" *> pure KeyType.sfixed32 <!>
  pstring "sfixed64" *> pure KeyType.sfixed64 <!>
  pstring "bool" *> pure KeyType.bool <!>
  pstring "string" *> pure KeyType.string

structure MapField where
  keyType : KeyType
  valueType : Type'
  name : String
  number : Int
  options : Array FieldOption
  deriving Repr

def mapField : Parsec MapField := do
  pstring "map" *> ws *> pchar '<' *> ws
  let keyType <- keyType
  ws *> pchar ',' *> ws
  let valueType <- type
  ws *> pchar '>' *> ws
  let name <- mapName
  ws *> pchar '=' *> ws
  let number <- fieldNumber
  let options <- optional (ws *> pchar '[' *> ws *> fieldOptions <* ws <* pchar ']')
  ws *> pchar ';' *>
  return { keyType, valueType, name, number, options := Option.getD options #[] }

--- Reserved

inductive RangeMax where
  | explicit (i : Int)
  | max
  deriving Repr

def rangeMax := RangeMax.explicit <$> intLit <!>
  (pstring "max" *> pure RangeMax.max)

structure Range where
  min : Int
  max : Option RangeMax
  deriving Repr

def range : Parsec Range := do
  let min <- intLit
  let max <- optional (ws *> pstring "to" *> ws *> rangeMax)
  return { min, max }

def ranges := sepBy1 range (ws *> pchar ',' <* ws)

def strFieldName := pchar '\'' *> fieldName <* pchar '\'' <!>
  (pchar '"' *> fieldName <* pchar '"')

def strFieldNames := sepBy1 strFieldName (ws *> pchar ',' <* ws)

inductive Reserved where
  | ranges (rs : Array Range)
  | strFieldNames (ns : Array String)
  deriving Repr

def reserved :=
  pstring "reserved" *> ws *>
    (Reserved.ranges <$> ranges <!> (Reserved.strFieldNames <$> strFieldNames)) <*
    ws <* pchar ';'

--- Top Level Definitions

---- Enum Definition

structure EnumValueOption where
  name : Array OptionNamePart
  value : Constant
  deriving Repr

def enumValueOption : Parsec EnumValueOption := do
  let name <- optionName
  ws *> pchar '=' *> ws
  let value <- constant
  return { name, value }

structure EnumField where
  name : String
  value : Int
  options : Array EnumValueOption
  deriving Repr

def enumField : Parsec EnumField := do
  let name <- ident
  ws *> pchar '=' *> ws
  let value <- intLit
  let options <- optional (ws *> pchar '[' *> ws *> sepBy1 enumValueOption
    (ws *> pchar ',' <* ws) <* ws <* pchar ']' <* ws)
  ws *> pchar ';' *>
  return { name, value, options := Option.getD options #[] }

inductive EnumBodyEntry where
  | option (o : Option')
  | field (f : EnumField)
  | reserved (r : Reserved)
  deriving Repr

def enumBody :=
  let entry := (some <$> EnumBodyEntry.option <$> option) <!>
    (some <$> EnumBodyEntry.field <$> enumField) <!>
    (some <$> EnumBodyEntry.reserved <$> reserved) <!>
    (emptyStatement *> pure none)
  pchar '{' *> ws *> do
  let entries <- sepBy entry ws
  <* ws <* pchar '}'
  return Array.filterMap id entries

structure Enum where
  name : Name
  body : Array EnumBodyEntry
  deriving Repr

def enum : Parsec Enum := do
  pstring "enum" *> ws
  let name <- enumName
  ws
  let body <- enumBody
  return { name, body }

---- Message Definition

mutual
inductive MessageBodyEntry where
  | field (o : Field)
  | enum (e : Enum)
  | message (m : Message)
  | option (o : Option')
  | oneof (o : Oneof)
  | mapField (m : MapField)
  | reserved (r : Reserved)
  deriving Repr

inductive Message where
  | m (name : String) (body : Array MessageBodyEntry)
  deriving Repr
end

def messageBody (message : Parsec Message) : Parsec $ Array MessageBodyEntry :=
  let entry : Parsec $ Option MessageBodyEntry := (some <$> MessageBodyEntry.field <$> field) <!>
    (some <$> MessageBodyEntry.enum <$> enum) <!>
    (some <$> MessageBodyEntry.message <$> message) <!>
    (some <$> MessageBodyEntry.option <$> option) <!>
    (some <$> MessageBodyEntry.oneof <$> oneof) <!>
    (some <$> MessageBodyEntry.mapField <$> mapField) <!>
    (some <$> MessageBodyEntry.reserved <$> reserved) <!>
    (emptyStatement *> pure none)
  pchar '{' *> ws *> do
  let entries <- sepBy entry ws
  <* ws <* pchar '}'
  return Array.filterMap id entries

-- TODO: Figure out how to make this non-partial with a proper recursive definition.
partial def message : Parsec Message := do
  pstring "message" *> ws
  let name <- messageName
  ws
  let body <- messageBody message
  return Message.m name body

---- Service Definition

structure RPC where
  name : String
  argStream : Bool
  argType : MessageType
  returnStream : Bool
  returnType : MessageType
  options : Array Option'
  deriving Repr

def rpc : Parsec RPC := do
  pstring "rpc" *> ws
  let name <- rpcName
  ws *> pchar '(' *> ws
  let argStream <- Option.isSome <$> optional (pstring "stream" <* ws)
  let argType <- messageType
  ws *> pchar ')' *> ws *> pstring "returns" *> ws *> pchar '(' *> ws
  let returnStream <- Option.isSome <$> optional (pstring "stream" <* ws)
  let returnType <- messageType
  ws *> pchar ')' *> ws
  let optionOption := (some <$> option) <!> (emptyStatement *> pure none)
  let options <- (pchar '{' *> ws *> sepBy optionOption ws <* ws <* pchar '}') <!> (pchar ';' *> pure #[])
  let options := Array.filterMap id options
  return { name, argStream, argType, returnStream, returnType, options }

inductive ServiceEntry where
  | option (o : Option')
  | rpc (r : RPC)
  deriving Repr

structure Service where
  name : String
  entries : Array ServiceEntry
  deriving Repr

def service : Parsec Service := do
  pstring "service" *> ws
  let name <- serviceName
  ws
  let entry := (ServiceEntry.option <$> option) <!> (ServiceEntry.rpc <$> rpc)
  let entries <- pchar '{' *> ws *> sepBy entry (ws *> sepBy emptyStatement ws <* ws) <* ws <* pchar '}'
  return { name, entries }

--- Proto File

inductive TopLevelDef where
  | message (m : Message)
  | enum (e : Enum)
  | service (s : Service)
  deriving Repr

def topLevelDef := (TopLevelDef.message <$> message) <!>
  (TopLevelDef.enum <$> enum) <!>
  (TopLevelDef.service <$> service)

inductive TopLevel where
  | import (i : Import)
  | package (p : Array String)
  | option (o : Option')
  | topLevelDef (t : TopLevelDef)
  deriving Repr

def Proto := Array TopLevel

-- TODO: Grammar doesn't include extend... what's that about in $protobuf/upb/test/proto3_test.proto
def proto : Parsec Proto :=
  let entry : Parsec $ Option TopLevel := (some <$> TopLevel.import <$> import') <!>
    (some <$> TopLevel.package <$> package) <!>
    (some <$> TopLevel.option <$> option) <!>
    (some <$> TopLevel.topLevelDef <$> topLevelDef) <!>
    (emptyStatement *> pure none)
  ws *> syntax' *> ws *> do
  let entries <- sepByUntilEof entry ws
  return Array.filterMap id entries

def parse (s : String) : Except String Proto :=
  match proto s.mkIterator with
  | success _ res => Except.ok res
  | error it err => Except.error s!"{it.i}: {err}"

end Protobuf.Syntax
