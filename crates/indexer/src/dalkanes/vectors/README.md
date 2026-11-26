# Test vectors

Every vector here comes from the reference indexer's unit tests, or from the vectors in the original draft. None was made up for this repo. Each one names its source in a `source` field. Byte strings were computed from those test values with the LEB128 and push rules in spec §5.

| File | Covers |
| --- | --- |
| [wire.json](wire.json) | Magic bytes, cellpack encoding, `OP_RETURN` scripts, calldata layout |
| [parser.json](parser.json) | Positive/negative strict script and cellpack cases, mirrored in Rust and both explorer test suites |
| [host-abi/](host-abi/) | Small WAT contracts with the outputs the reference runtime is tested to produce (including nested rollback and setup-failure fuel) |
| [block-fuel.json](block-fuel.json) | Per-block fuel budget: grants, `fuel_used` and the exhausted receipt across a block |

The schema is in [../schemas/vectors.schema.json](../schemas/vectors.schema.json).

A conforming implementation MUST:

1. decode every `script_hex` to the listed `cellpack`, and encode the `cellpack` back to the listed bytes;
2. running each `host-abi` case with the listed parameters, produce the listed `ok` and `return_hex`, or the listed decoded fields.

`parser.json` includes bad versions, truncation, oversized ids/counts and u128 overflow from `strict_parser_vectors`. Host cases name their Rust test; WAT is copied from that test. Run the reference wire checker for wire/parser cases, and dogex's `cargo test --lib alkanes` for execution cases. Independent replays, reorg and adversarial cases are still wanted.
