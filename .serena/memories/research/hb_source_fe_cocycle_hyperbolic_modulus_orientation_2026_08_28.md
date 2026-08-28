# HC78: HB source-FE cocycle hyperbolic modulus orientation

Formalized in `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFECocycleHyperbolicModulusOrientation` and wired into `GaloisForLFunctions.RHTower`.

For exact carrier `P(s)=(1+s/2)(s/2)^2`, both reflected norm factors change with sign `1-2 Re(s)`:
`|1-s|²-|s|²=1-2 Re(s)`, `|3-s|²-|s+2|²=5(1-2 Re(s))`.
Thus no cross-factor cancellation. The literal source-FE cocycle satisfies:
- `1 < normSq κ(q) ↔ Re(q)<1/2`
- `normSq κ(q)<1 ↔ 1/2<Re(q)`
- `normSq κ(q)=1 ↔ Re(q)=1/2`
- reflected squared gains multiply to one
- universal unit gain iff RH.

Unit gain is pointwise equivalent to HB optical darkness, Deninger shared Ward zero, FZZ-P information-force zero, all PW-B balances, and canonical first-copy RBH balance.

Verification: direct Lean pass; targeted build pass 12017/12017; audited theorem axioms only `propext`, `Classical.choice`, `Quot.sound`. Global lint has only unrelated pre-existing unreachable modules. Card: `docs/drafts/pipeline/3-formalized/hb-source-fe-cocycle-hyperbolic-modulus-orientation.md`.

Next hard survivor: seek exact factorization of gain defect as `(1-2 Re(q))` times a strictly positive source-native cofactor, then compare exactly with shared route Ward charge. Do not treat HC78 as physical forcing; it remains a receiver until fixed Peierls/Einstein action yields unit gain.