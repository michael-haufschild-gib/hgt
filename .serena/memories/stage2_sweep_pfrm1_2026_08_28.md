Continuation of `mem:stage2_sweep_progress_2026_08_28`.

ULF-PFRM-1 completed/promoted. New modules:
- `formal/GaloisForLFunctions/HTGeometry/TwoPacketRationalPrimitiveRigidity.lean`
- `formal/GaloisForLFunctions/HTGeometry/TwoPacketRationalPrimitiveDomainRigidity.lean`
- `formal/GaloisForLFunctions/HTGeometry/PrimeRadialTwoPacketPrimitiveRigidity.lean`

Formal surface: characteristic-zero rational Cauchy theorem with unique finite linear form; free-coordinate add/left/right maps and derivation laws; algebraically independent fraction evaluation; exact denominator-safe domain transport for noninjective packet restrictions; unital prime-packet restriction algebra maps commuting with rotated logarithmic derivation; disjoint-union additivity on positive-prime-power currents; literal two-disjoint-infinite-prime-packet jet algebraic independence; finite jet-rectangle extraction; finite-palette no-new-current theorem; canonical even/odd infinite prime packets; arbitrary profile-subspace intersection theorem `primeRadial_differentialField_primitive_rigidity`; fixed common-cutoff coefficient uniqueness; finite rational formation corollary.

Wired through `formal/GaloisForLFunctions/HTGeometry.lean`. Direct checks for all three modules passed. Targeted builds for domain and arithmetic leaves passed. One batched key-capstone axiom audit found only `[propext, Classical.choice, Quot.sound]`; never re-audit unless source changes. `scripts/formal_tools.py lint` found no forbidden declarations in these modules but still exits on unrelated concurrent umbrella reachability gaps. Card promoted to `docs/drafts/pipeline/3-formalized/universal-law-field/primitive-formation-rigidity-mechanics/two-packet-rational-primitive-rigidity-and-finite-formation-no-new-current-law.md`. PFRM1 `/tmp` files deleted.

Do not recheck/rebuild/audit these modules in the continued Stage-2 sweep.