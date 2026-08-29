# Stage-3 sweep ledger — 06-integrable-qft-yang-baxter (5 cards remaining of 9)

Goal: unconditional Lean for every proven theorem on every remaining card; promote to
`3-formalized/not_new_scientific_knowledge/06-integrable-qft-yang-baxter`.
Rules: no hypotheses wrapping unproven external input; no umbrella builds; `lake env lean` to
check, `lake build <module>` only for the final audit; `#print axioms` only on new capstones.

Already promoted (earlier session): `collision-regular-relative-yang-baxter-chamber-frame`,
`fixed-particle-holomorphic-acyclicity-identity-zero-yang-baxter`,
`scalar-cdd-invariance-of-intertwiner-property`, `unitary-pair-twist-hardy-exponential-bound`.

| # | Card | Lean obligation | Status |
|---|---|---|---|
| 1 | bounded-syntax-singular-ade-prime-capacity-law | Ritt order bound `kappa(P) <= ord(P)` (replaces Harrison-Trainor–Klys–Moosa entirely), Kolchin frequency ineq `(14)`, cofinal prime growth `(19)` | TODO |
| 2 | diagonal-projective-ht-local-qft | DONE — `FlipDiagonalScattering` | **PROMOTED** |
| 3 | non-difference-projective-ht-yang-baxter-control | DONE — `CorcoranDeLeeuwModelOne`, `UnipotentDiagonalizationObstruction`, `DifferenceFormReparametrisation`, `SingleGeneratorDifferentialDegree`, `AnchoredProjectiveEntryField` | **PROMOTED** |
| 4 | relative-modular-hypertranscendental-scattering-carrier | DONE — `RelativeModularScattering` | **PROMOTED** |
| 5 | two-state-regular-quantum-projective-da-rigidity | **classification-free route**: Sutherland equation ⇒ projective first-order rational ODE ⇒ finite trdeg ⇒ projectively DA, in every dimension; plus positive-metric cut `H*=-H` and the `B=RP` convention boundary | TODO |

## Route notes (established before any Lean was written)

### Card 1 — Harrison-Trainor–Klys–Moosa is not needed
For a nonzero `P` in one differential indeterminate over a constant field of characteristic zero
and any *proper prime differential ideal* `q` containing `P`, the truncation transcendence degrees
obey `trdeg_C C(y_0,…,y_m) <= ord(P)` for every `m`.  Induction on
`(ord P, deg_{Y_ord P} P)` lexicographically:
- separant `S = ∂P/∂Y_h` is nonzero (char 0, `deg_{Y_h} P >= 1`), `ord S <= h`,
  `deg_{Y_h} S = deg_{Y_h} P - 1`;
- if `S ∉ q`, then `y_h` is algebraic over `C(y_0,…,y_{h-1})` and every higher `y_m` lies in
  `C(y_0,…,y_h)` by differentiating `P(y)=0` and dividing by `S(y) ≠ 0`;
- if `S ∈ q`, apply the induction hypothesis to `S`;
- a nonzero constant cannot lie in a proper prime ideal, so the induction terminates.
Hence `kappa(P) <= n` — sharper than `B(n,d)`, and *unconditional*.

### Card 5 — the classification is not needed either
Braid difference form `Ř(a) = P R(a)`, regular `Ř(0) = I`, `H = Ř'(0)`.  Differentiating the
braid YBE `Ř_12(a)Ř_23(a+b)Ř_12(b) = Ř_23(b)Ř_12(a+b)Ř_23(a)` in `b` at `b=0` gives the
Sutherland equation
```
Ř_12(a) Ř'_23(a) − Ř'_12(a) Ř_23(a) = H_23 Ř_12(a)Ř_23(a) − Ř_12(a)Ř_23(a) H_12.
```
Write `L_X(Y) = X_12 Y_23 − Y_12 X_23`.  At `X = I` the kernel of `L_X` is exactly the scalars
(partial-trace argument), and `X ∈ ker L_X` always, so by lower semicontinuity of rank
`ker L_X = C·X` near `I`.  Normalizing by a nonvanishing entry `x_p` and using bihomogeneity
(`L` bilinear, right side quadratic) the scalar drops out and the normalized matrix
`Y = X/x_p` satisfies a *first-order rational ODE with constant coefficients*
`Y' = G(Y)`.  Hence `C(entries of Y)` is derivation-closed of transcendence degree `< aleph0`,
so every entry ratio is differentially algebraic — for every state dimension, with no
classification input.  Corpus interface:
`HTGeometry.FiniteAlgebraicStateBoundary.differentialAlgebraicOver_of_mem_derivationClosed_finiteTrdeg`.

## Log
- 2026-08-29 — ledger created; five cards read; two external-theorem dependencies (HTKM Thm 6.1
  and the de Leeuw et al. `4x4` classification) replaced by direct proofs, as recorded above.
- 2026-08-29 — card 3 promoted.  The quantum Yang--Baxter equation of the whole model-1 family
  (arbitrary `A`, arbitrary increments) is now proved in Lean instead of cited: the adjacent braid
  identity is a `64`-entry finite check on the braid form, transported by the corpus's right-flip
  bridge.  Reusable layers built: `UnipotentDiagonalizationObstruction` (diagonalisable + unipotent
  ⇒ identity; and the spectral-theorem-free positive-metric obstruction from comparing the isometry
  identity at `M²` and `M⁴`), `DifferenceFormReparametrisation` (two clocks in one difference
  coordinate force a constant derivative), `SingleGeneratorDifferentialDegree` (`dtrdeg F F<h> = 1`
  for one hypertranscendental generator), `AnchoredProjectiveEntryField` (pivot-normalised entry
  family at an arbitrary index type, its scalar invariance, and the `F<h>` identification).
- 2026-08-29 — card 2 promoted.  `HTGeometry/FlipDiagonalScattering.lean`: the flip-diagonal
  family `P · diagonal ω` over an arbitrary commutative ring, its adjacent braid identity for
  *arbitrary* coefficient functions (so the Yang--Baxter input is proved, not cited), the
  commuting channel algebra from coefficient symmetry, the diagonal logarithmic connection
  `S⁻¹ ∂S = diag(logDeriv ω)`, the traceless part, the `-i u` relative reporter, and the
  projective field `K<h>` with `dtrdeg = 1`.  Also added arbitrary-index `entrywiseDeriv`,
  `wignerSmithOf` and `tracelessPartOf` with `rfl`-level agreement lemmas to the corpus's
  `Fin (n+1)` versions.
- 2026-08-29 — card 4 promoted.  `HTGeometry/RelativeModularScattering.lean`: real-linear
  isometric equivalences with `IsComplexLinearMap` / `IsConjugateLinearMap` as the
  unitary/antiunitary split; `S_phys = J_in J` and `J = J_in S_phys`; antiunitarity of both
  conjugations and unitarity of their product; the incoming Fock form `(9)`; the reality law
  `J_in M J_in = M⁻¹`; and the factorizing multiplier with its boost invariance and the
  two-particle chamber identification.  Non-vacuity is proved (complex conjugation, free case).
