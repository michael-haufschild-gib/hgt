# OWU: the dilation-ray criterion (obstacles 1 and 2 on a single ray of tests)

- **ID:** owu-dilation-ray-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) + conjecture ledger for the three open OWU obstacles
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU; successor of
  `3-formalized/owu-cut-is-even-mean-zero-deficit-2026-10-16.md`
- **Statement:** Let `φ` be the reference bump (`1` on `[−1,1]`, supported in `(−2,2)`, even,
  `0 ≤ φ ≤ 1`) and `φ_T(x) = φ(x/T)`. If `lam` is odd Weil-positive and
  `Re W_lam(φ_T ⋆ φ̃_T) ≥ 0` for every `T ≥ 1`, then `lam = Λ` and RH. Hence
  RH ⟺ some odd Weil-positive weight is Weil-positive on the dilation ray of one bump
  (`riemannHypothesis_iff_exists_weilPositiveOdd_dilationRay`).

## Structural contribution

After the previous card the OWU Needs were (1) even mean-zero positivity (= cut removal),
(2) central nonnegativity of the extension, (3) an odd-positive source. The dilates `φ_T` are not
mean-zero (`φ̂_T(0) = T∫φ`); their spectral weights are
`Θ = [(1+γ²)T²|φ̂(T√γ)|² − T²D²]/γ` on the critical ordinates and
`Θ = T²[D² − (1+γ²)E(Tr)²]/r²` on the cut (`D = ∫φ`, `E(Tr) = ∫φ(u)e^{−Tru}du ≥ 2 + T²r²/6`).
Three bounds drive everything:
`Θ ≤ T²(D² + 2N₂²)` uniformly on the support, `Θ(−1) ≤ −T⁴D/6` at the centre,
`Θ ≤ −4T²(T⁴r₀⁴/36 − 12)` on the cut at distance `≥ r₀`. Positivity on the ray therefore forces
no cut mass (quartic beats quadratic), no central atom, and the far-ordinate inequality
`∫_{γ≥δ} dν/γ ≤ δν(S¹) − c` for every `δ > 0`, which makes the cut-free extension
`Φ(s) = (∫(γz−1)/(z+γ) dν − c)/(s−½)` nonnegative on `(½,∞)`; the square-root Herglotz transfer
then gives `λ = Λ` and RH. So the two remaining analytic obstacles are the single one-parameter
family of inequalities `W_lam(φ_T⋆φ̃_T) ≥ 0`, whose arithmetic content is the scale-`T` excess of
the `½`-weighted sum of `lam` over its archimedean prediction. The even sector of the
primitive-hyperplane certificate (MUST-1519) collapses to a ray.

Exact Lean theorems (`formal/GaloisForLFunctions/RHTower/WeilDilationRayCriterion.lean`,
namespace `RHTower.OddResolvent`, wired into `RHTower.lean`):

| Theorem | Content |
|---|---|
| `refProfile_*`, `two_le_integral_refProfile`, `integral_refProfile_le_four`, `two_thirds_le_integral_sq_mul_refProfile` | the reference bump and its moments |
| `paperFT_refProfileC_ofReal`, `sq_div_six_le_integral_refProfile_sub_cos`, `expMoment_refProfile_ge` | cosine transform, `φ̂(0) − φ̂(v) ≥ v²/6` for `|v| ≤ ½`, `E(r) ≥ 2 + r²/6` |
| `dilate`, `paperFT_dilate`, `paperFT_dilate_I_mul` | `φ̂_T(z) = Tφ̂(Tz)` |
| `spectralWeight_dilate_le_of_pos`, `_le_mul_of_pos`, `_le_near_centre`, `_le_of_pos_decay`, `_nonpos_of_cut`, `_le_of_cut`, `_le_uniform`, `_neg_one_le` | the weight bounds |
| `mul_measureReal_le_of_weight_bounds` | `Kν(A) ≤ M₀ν(S¹) − c|f̂(0)|²` from positivity on one test |
| `measure_cutSet_eq_zero_of_dilationRay`, `cut_measure_eq_zero_of_dilationRay` | cut removal on the ray |
| `measure_centre_eq_zero_of_dilationRay` | no central atom |
| `integral_farSet_inv_le_of_dilationRay` | the far-ordinate inequality |
| `le_re_integral_nevKernel`, `re_cutFreeExtension_nonneg` | `Re Φ ≥ 0` on `(½,∞)` |
| `eq_vonMangoldt_and_riemannHypothesis_of_dilationRay_nonneg`, `riemannHypothesis_iff_exists_weilPositiveOdd_dilationRay` | the criterion |

## Paper proof

1. Transforms: `paperFT (φ(·/T)) z = T φ̂(Tz)` by the change of variables `x = Ty`; on the real
   line `φ̂(v) = ∫φ cos(vx)` (the sine part vanishes by evenness), so `0 ≤ φ̂(v) ≤ D` and
   `D − φ̂(v) ≥ ∫_{|x|≤1}(1 − cos vx) ≥ v²/6` for `|v| ≤ ½` (`1 − cos y ≥ y²/4` for `|y| ≤ 1`);
   on the imaginary axis `φ̂(ir) = ∫φ cosh(rx) ≥ D + (r²/4)∫x²φ ≥ 2 + r²/6`.
2. Weights. Critical ordinates: `Θ = T²[γ²B² − (D² − B²)]/γ` with `B = φ̂(T√γ) ≤ D`, hence
   `Θ ≤ T²γD²`; with `T²γB ≤ N₂`: `Θ ≤ (1+γ²)N₂²/(T²γ³) − T²D²/γ`; for `T√γ ≤ ½`:
   `D² − B² ≥ D·T²γ/6`, so `Θ ≤ T²γD² − T⁴D/6`. Cut: `Θ = T²[D² − (1+γ²)E²]/r² ≤ 0` and, for
   `r ≥ r₀` with `T⁴r₀⁴ ≥ 432`, `D² ≤ 16 ≤ E² − T⁴r⁴/36 + 12` gives `Θ ≤ 4T²(12 − T⁴r₀⁴/36)`.
   Centre: the limit along `bdryPt(1/(n+1))` of the near-centre bound is `≤ −T⁴D/6`.
3. The measure inequality: if `Θ ≤ M₀` off `A` and `≤ −K` on `A` then
   `0 ≤ W = ∫Θ dν − cT²D² ≤ M₀ν(S¹) − (M₀+K)ν(A) − cT²D²`. With `A = cut_{r₀}` this gives
   `4(T⁴r₀⁴/36 − 12)ν(A) ≤ C₁ν(S¹) − cD²` for all large `T`, so `ν(A) = 0`; with
   `A = {−1}`: `(T²D/6)ν(A) ≤ C₁ν(S¹) − cD²`, so `ν(A) = 0`.
4. Far ordinates: with `b = 1_{γ≥δ}(K_δ/T² − T²D²/γ) + 1_{γ<δ}T²δD²`, `K_δ = N₂²(1/δ³ + 1/δ)`,
   `Θ ≤ b` a.e. and `0 ≤ ∫b − cT²D²`, hence `∫_{γ≥δ}dν/γ ≤ K_δν(S¹)/(D²T⁴) + δν(S¹) − c`; let `T → ∞`.
5. Positivity of the extension: for real `z > 0`, `Re k(z,ζ) ≥ −1/γ` on `γ ≥ δ`, `≥ −1/z` on
   `0 < γ < δ`, `= z ≥ 0` at `ζ = 1`; so `Re∫k dν ≥ c − δν(S¹) − ν(0<γ<δ)/z` and `ν(0<γ<δ) → 0`
   (the near sets shrink to the null set `{cut} ∪ {−1}`). Hence `Re Φ(x) ≥ 0` for `x > ½`.

## Conjecture ledger (this loop)
1. Obstacle 3 (`PrimeBlindPositiveOddAt 1`): by odd Farkas it is `∃` odd-positive `lam`; by the
   Nevanlinna characterisation it is `∃` a real Dirichlet series `D` (abs. conv. on `Re s>1`) with
   `a(Ψ₀ − D)(½+a)` Nevanlinna off `(−∞,¼]`. On the critical line this reads
   `Re D(½+0+iτ) ≤ w(τ)` (archimedean density), with equality a.e. for `Λ` under RH, and the pole
   condition forces `Σ_{n≤x} lam(n) ∼ r x`, `r ≥ 1` (the corpus caps `r ≤ 1`). Absolutely convergent
   series on the line cannot carry the pole; `ζ(s) − 1`, `2Σ Λ(n)n^{−2s}`, Euler-product
   perturbations all violate the line condition. Unconditional provability of the source is
   `RH ∨ (existence of odd fakes)`: not reachable by construction. Recorded, not solved.
2. Short-support odd tests are automatically blind; the corpus's window programme proves
   `weilArchRe ≥ 0` for nonnegative tests up to window `4/9` and for signed tests up to `~1/36`
   (`half_window_signed_short_support_le_weilArchRe`). This covers `PrimeBlindPositiveOddAt 1` on
   tiny supports only; the long-support blind combinations are the RH-hard core.
3. Obstacle 2 is invisible to all mean-zero tests but visible to the dilation ray (this card):
   the central value is `−c − ∫dν/γ`, the limit of `W(φ_T)/T²D²`.
4. Obstacle 1 was the even mean-zero deficit (previous card); on the dilation ray it is the
   quartic-versus-quadratic growth, no exponential estimates needed (`E(Tr) ≥ 2 + T²r²/6`).
5. Wide tests `φ(x/T)/T` would need `T`-explicit real-line decay; the bound `T²γB ≤ N₂` with
   `B = φ̂(T√γ)` suffices because the `1/γ` weight is only needed for `γ ≥ δ`.
6. Source at pole weight `0` (`PrimeBlindPositiveOddAt 0`, open in the corpus, not known to imply
   RH): by Farkas and the Nevanlinna characterisation it is a real Dirichlet series `D` with
   `Re D(½+0+iτ) ≤ w(τ)` on the whole line and no pole condition. The archimedean density is a
   deep narrow well: `w(0) = ½ψ(¼) − ½log π ≈ −2.69`, `w(1) ≈ −1.0`, `w(2) ≈ −0.57`,
   `w(4) ≈ −0.23`, zero crossing near `τ ≈ 6.3`, then `w ≈ 0.24` at `10`, `0.5` at `17`, `1.1` at
   `45`, growing like `½ log τ`. For `Λ` under RH the inequality is an equality a.e. (the slack is the
   singular zero measure). Any `D` absolutely convergent on the line has `Re D` almost periodic with
   mean zero and coefficient mass `≥ 2.69`; the lowest node `log 2` forces sign changes at scale
   `≈ 2`, so one-signed coefficients fail at `τ ≈ 2–4`, smooth coefficient profiles give
   amplitude `≈ 2.69/(1+τ²)` which exceeds `w` near the crossing `τ ≈ 6.5`, and generic mixed
   profiles have fluctuations `≈ 2.69/√K` against `w ≈ 0.05–0.2` on `[7, 10]`. Expected outcome:
   no absolutely convergent source exists; sources must carry a singular boundary measure on the
   line, i.e. they are `Λ`-like. Not formalised; it is a conjecture for the next loop
   (`no odd-positive weight at pole weight 0 with Σ|λ(n)|n^{−1/2} < ∞`).
7. Pole-weight transfer `β → 1` by adding `(1−β)·𝟙` fails on the line (`1 − Re ζ(½+iτ)` changes
   sign); the pole weight is not a free parameter of the source problem.

## Gates
- [x] 0 → 1  well-posed
- [x] 1 → 2  paper proof above
- [x] 2 → 3  Lean module audited with `lake --old env lean` (no output), built with
  `lake build --old`, axioms of seven theorems exactly `[propext, Classical.choice, Quot.sound]`

## Validation
- `lake --old env lean`: no output. `lake build --old`: built.
- Axiom audit (scratch, removed): seven theorems, standard axioms.
- `scripts/formal_tools.py lint`: the only error names another agent's untracked module
  (`DeningerMeyerFiniteNativeDensity`); pre-existing large-file warnings only.
- Umbrella: import appended to `RHTower.lean`; scratch files removed.

## Log
- 2026-10-16 — created; Lean module compiled, audited, wired; moved to 3-formalized
