# OWU: the blind odd window is closed at pole weight 1 (sub-critical sources give the critical source)

- **ID:** owu-odd-window-closed-at-one
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU, Need "odd-positive source";
  successor of `3-formalized/owu-dilation-ray-criterion-2026-10-16.md`
- **Statement:** `PrimeBlindPositiveOddAt 1 ⟺ ∀ β < 1, PrimeBlindPositiveOddAt β`, hence an odd
  Weil-positive weight at the critical pole weight exists iff odd Weil-positive weights exist at
  every sub-critical pole weight `β < 1` (`exists_weilPositiveOdd_iff_forall_lt_one`).

## Structural contribution

The OWU source problem is `∃ lam, WeilPositiveOdd lam`, i.e. `PrimeBlindPositiveOddAt 1`. The
corpus knew the blind odd window `{β : PrimeBlindPositiveOddAt β}` is a down-set capped at `1`.
The pole-weight functional `poleWeightArchRe β f = A(k_f) + (β − 1)Re P(k_f)` is affine in `β`, so
for every fixed blind combination the value at `1` is the limit of the values at `β < 1`; the window
is closed at its cap. Consequently the critical source problem is exactly the family of sub-critical
source problems, in which the archimedean pole only has to be cancelled to density `β < 1`
(odd positivity at pole weight `β` forces Abel density `≥ β` at `s = 1`). Together with the
dilation-ray criterion: RH ⟺ a weight that is odd-positive at every `β < 1`, hence at `1`, and
positive on the dilates of one bump.

Lean (`formal/GaloisForLFunctions/RHTower/WeilOddWindowClosedAtOne.lean`, namespace `RHTower`,
wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`):
`sum_poleWeightArchRe_eq` (affinity), `primeBlindPositiveOddAt_one_of_forall_lt`,
`primeBlindPositiveOddAt_one_iff_forall_lt`, `exists_weilPositiveOdd_iff_forall_lt_one`.

## Paper proof
For a blind nonnegative combination `c` write `S(β) = A + (β − 1)B` with
`A = Σ c_f poleWeightArchRe 1 f`, `B = Σ c_f Re P(k_f)`. If `S(1 − ε) ≥ 0` for all `ε > 0` then
`A ≥ εB` for all `ε > 0`; with `ε = ε'/(|B| + 1)` this gives `A ≥ −ε'` for every `ε' > 0`, so
`A ≥ 0`. The converse is the down-set property; the weight statement is odd Farkas at `1` and at
each `β` (`exists_weilPositiveOddAt_iff`) with `WeilPositiveOddAt 1 = WeilPositiveOdd`.

## Conjecture ledger
1. Pole-weight dichotomy (conjecture): sources at `β ≤ 0` are RH-free (the corpus's tempered
   weights `λ(p) = c log p/√p` at `β = 0`, pending the line inequality `c Re P₁(1+iτ) ≤ w(τ)`),
   while any source at a positive pole weight needs density `≥ β > 0` and a boundary real part
   bounded by the archimedean density on the critical line; for density-positive Dirichlet series
   the lattice resonances (Kronecker alignment of `n^{−iτ}`) exceed `½ log τ` unless cancelled by
   critical zeros, so such sources are `Λ`-like. Under RH the segment `(1−ε)Λ + ε λ_temp` lies in
   the cone at pole weight `1 − ε`, so sub-critical cones are not `{βΛ}`; the conjecture is that
   every density-`β` source is `βΛ + (density-zero part)`.
2. Transfer `β → 1` by adding `(1 − β)·𝟙` fails on the line (`1 − Re ζ(½+iτ)` changes sign).
3. The critical source, once obtained from sub-critical ones, is only known to give RH together
   with ray positivity (dilation-ray criterion) or Q*; the sub-critical reduction does not bypass
   odd uniqueness.

## Validation
- `lake --old env lean`: no output after the unused-name fix. `lake build --old`: built.
- Axiom audit (scratch, removed): two theorems, standard axioms. Lint: only another agent's
  unwired module (`PaperThetaContourControl`). Umbrella import appended; scratch cleaned.

## Log
- 2026-10-16 — created; Lean module compiled, audited, wired; moved to 3-formalized
