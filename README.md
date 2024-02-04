# lean4-protobuf

A WIP [Protobuf](https://protobuf.dev/) package for [Lean 4](https://lean-lang.org/).

## Roadmap

- [x] Parsing of `.proto` files (except for [MessageValue constants](https://protobuf.dev/reference/protobuf/proto3-spec/#constant), adding this is a TODO).
- [ ] Varint encoding and decoding.
- [ ] Type definition codegen. (Planning to support both an `import_protobuf` macro for doing this at compile time, as well as a `protoc` plugin for if you want to view and commit the generated code.)
- [ ] Encoding and decoding codegen. (Planning to do this with `deriving ProtobufMessage`.)
- [ ] Passing [Protobuf conformance tests](https://github.com/protocolbuffers/protobuf/tree/main/conformance).
- [ ] Visibility refactor (ensure things that should be `private` are).
- [ ] Good docs and examples.
