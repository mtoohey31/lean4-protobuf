import Lake
open Lake DSL

package protobuf

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.6.0"

@[default_target]
lean_lib Protobuf
