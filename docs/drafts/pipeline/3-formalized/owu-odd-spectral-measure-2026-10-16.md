# OWU: the odd Weil functional is the spectral integral of its Nevanlinna measure

- **ID:** owu-odd-spectral-measure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, route OWU; successor of
  `3-formalized/owu-square-root-herglotz-transfer-2026-10-16.md`
- **Statement:** For a slit continuation `Ψ` of the Weil function of `lam` with the
  squared-variable sign law, with Nevanlinna data `(ν, c)` of `g(z) = aΨ(½ + a)`, `z = a²`,
  every odd `C²` compactly supported `f` satisfies
  `Re W_lam(f ⋆ f̃) = ∫ Θ_f(e^{iθ}) dν(θ)`, `Θ_f ≥ 0` on the support of `ν`,
  `Θ_f(ζ) = (1 + γ²)|f̂(√γ)|²/γ` on the critical ordinates `γ > 0`,
  `Θ_f(ζ) = (1 + γ²)|f̂(i√(−γ))|²/(−γ)` on the cut `−¼ ≤ γ < 0`, `Θ_f(1) = 0`.
  Hence the odd Weil cone is exactly the set of weights with absolutely convergent Dirichlet
  series on `Re s > 1` and a slit continuation obeying the sign law.

## Structural contribution

The full-cone uniqueness theorem rests on the Bochner boundary measure of the full functional.
The odd cone had no spectral measure; the Pick continuation was its surrogate, valid only on the
exponential test family. This card supplies the odd spectral measure on every compactly supported
odd test. Consequences:

- the odd Weil cone is characterised (`weilPositiveOdd_iff_exists_slit`): odd positivity is
  equivalent to absolute convergence plus a holomorphic slit continuation with the sign law
  `Im s · Im((s − ½)Ψ(s)) ≥ 0`; nothing beyond the Nevanlinna property of `g` is encoded in odd
  positivity, so the real cut and the Nevanlinna constant are invisible to it (the cut enters every
  odd test with the positive weight `(1 + γ²)|f̂(i√(−γ))|²/(−γ)`, the constant `c` enters through
  `c|f̂(0)|² = 0`);
- combined with the square-root transfer, the remaining OWU inputs (cut removal, real-axis
  nonnegativity) are exactly the conditions under which the odd Nevanlinna measure is also the
  Herglotz measure of the full cone; they must come from the arithmetic (fixed archimedean term,
  integer frequencies), not from further tests.

Exact Lean theorems (`formal/GaloisForLFunctions/RHTower/`, namespace `RHTower.OddResolvent`,
wired into `RHTower.lean`):

| Module | Theorem | Content |
|---|---|---|
| `OddWeilLineKernel.lean` | `oddLineKernel_eq`, `oddLineKernel_neg`, `norm_oddLineKernel_le` | kernel `K_ζ(5/4 + it) = ((γa² − 1)/(a² + γ))/a`, real coefficients, bound `44(1 + t²)` on the support |
| `OddWeilSpectralMeasure.lean` | `exists_nevanlinna_measure_of_slit` | Nevanlinna data of any slit continuation with the sign law |
| same | `slit_conj`, `slit_eq_integral_oddLineKernel` | real coefficients of the slit continuation; representation on the whole line `Re w = 5/4` |
| same | `re_weilFullFunctional_eq_integral_oddSpectralWeight` | the spectral representation |
| same | `oddSpectralWeight_one`, `oddSpectralWeight_eq_of_pos`, `oddSpectralWeight_eq_of_neg`, `oddSpectralWeight_neg_one_nonneg`, `oddSpectralWeight_nonneg` | evaluation and nonnegativity of the weight |
| same | `weilPositiveOdd_of_slit`, `weilPositiveOdd_iff_exists_slit` | odd Herglotz bridge and the characterisation of the odd cone |

## Paper proof

1. (Representation on the whole line.) For `a` in the first quadrant
   `a Ψ(½ + a) = ∫ k(a², ζ) dν − c`, `k(z, ζ) = i K(½ − iz, ζ)`. The kernel has real coefficients
   on the line (`oddLineKernel_neg`), and `Ψ(s̄) = conj Ψ(s)` on the slit domain by the identity
   theorem on the quadrant (`slit_conj`), so for `w = 5/4 + it`, `t ≠ 0`,
   `Ψ(w) = ∫ K_ζ(w) dν(ζ) − c/(w − ½)`, `K_ζ(w) = k((w − ½)², ζ)/(w − ½)`.
2. (Kernel bound.) For `ζ ≠ 1` and `t ≠ 0`, `K_ζ(w) = ((γa² − 1)/(a² + γ))/a`, `a = ¾ + it`,
   with `γa² − 1 = (a² + γ)a² − a⁴ − 1`, `|a² + γ| ≥ 3|t|/2`, and `|a² + γ| ≥ 1/16` for
   `|t| ≤ ½`, `γ ≥ −¼`; so `|K_ζ(w)| ≤ 44(1 + t²)` on `{ζ = 1} ∪ {γ ≥ −¼}`; `K_1(w) = a`.
3. (Fubini.) `W_lam(f ⋆ f̃) = (1/2π)∫ F(t) Ψ(5/4 + it) dt`, `F(t) = H(5/4 + it) + H(1 − 5/4 − it)`,
   `|F| ≤ 2D/(1 + t²)²`. The product `F(t) K_ζ(w)` is integrable on `volume × ν` by the bound of
   step 2 on the support (which carries all of `ν`), and the `c`-term is
   `c (1/2π)∫ F/(w − ½) = c H(½) = c|f̂(0)|² = 0` for odd `f` (`two_line_pair` at `z₀ = ½`).
4. (Per-point evaluation.) `Θ_f(ζ) := Re[(1/2π)∫ F(t) K_ζ(5/4 + it) dt]`. For `ζ ≠ ±1`,
   `K_ζ(w) = −(1/γ) g_{½}(w)/2 + ((1 + γ²)/(2γ)) g_{½+ρ}(w)` with `ρ² = −γ`; the two-line
   residue identity gives `Θ_f(ζ) = Re[((1 + γ²)/(2γ))(H(½ + ρ) + H(½ − ρ))]`. On the critical
   ordinates `H(½ ± i√γ) = |f̂(±√γ)|²`; on the cut `H(½ ± r) = f̂(∓ir) conj f̂(±ir) = −|f̂(ir)|²`
   for odd `f`. At `ζ = 1` the linear term has zero real part. At `ζ = −1`, `Θ_f` is the limit
   of its values at `bdryPt(1/(n+1))` (dominated convergence with the bound of step 2 and
   continuity of the kernel in `ζ`), hence nonnegative.
5. (Conclusions.) `Re W_lam(f ⋆ f̃) = ∫ Θ_f dν ≥ 0` for every odd test, so a slit continuation
   with the sign law gives odd positivity; the converse is the existing slit continuation.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof above
- [x] 2 → 3  Lean modules audited individually with `lake --old env lean`, built with
  `lake build --old`, axioms of nine theorems exactly `[propext, Classical.choice, Quot.sound]`

## Conjecture ledger
1. Central integrability `∫ dν/|γ| < ∞` from the representation: false as a consequence, the
   weight `(1 + γ²)|f̂(√γ)|²/γ` tends to `|f̂′(0)|²` and is bounded at the centre; compact odd tests
   do not see `1/|γ|`. Withdrawn.
2. Triple-pole evaluation at `ζ = −1`: replaced by continuity in `ζ`; the exact central value is
   not needed, only its nonnegativity.
3. The nested-integral notation `∫ θ, ∫ t, g (t, θ) ∂ν` binds `∂ν` to the inner integral; the
   outer-`ν` form must be written `∫ θ, (∫ t, g (t, θ)) ∂ν`.

## Validation
- `lake --old env lean` on both modules: no output.
- `lake build --old` on both modules: built.
- Axiom audit (scratch file, removed): nine theorems, each `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint`: the new modules are reachable from `RHTower`; remaining errors
  name untracked modules of other agents; pre-existing large-file warnings only.
- Umbrella: two imports appended to `RHTower.lean`; scratch files removed.

## Log
- 2026-10-16 — created; paper proof; two Lean modules compiled, audited, wired; moved to 3-formalized
