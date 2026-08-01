# Upstream provenance

- Repository: <https://github.com/openai/ten-proofs>
- Revision: `6fefffdbab0dfa726fcfde6cefae23aa7a1888f3`
- Upstream Lean toolchain: `leanprover/lean4:v4.32.0`
- Integrated Lean toolchain: `leanprover/lean4:v4.32.2`
- License: Apache-2.0; see `LICENSE` in this directory.

Imported proof sources comprise ten headline `.lean` files, `All.lean`, and complete
`ConnesRigidity/` certificate dependency graph.  `ComparatorChallenges/` is excluded: it is a
standalone comparison harness, not a dependency of `All.lean` or any proof certificate.

Upstream source files are retained without namespace or proof edits.  Lake exposes their original
module roots from this directory through separate `TenProofs` Lean library; local code imports the
stable umbrella `GaloisForLFunctions.TenProofs`.
