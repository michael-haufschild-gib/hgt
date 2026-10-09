# The exponential Liouville sum: a one-sided `√t` bound forces RH and simple zeros

- **ID:** liouville-exponential-sum-rh-simplicity
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM. Receiver for route MC's paper-only candidate "Liouville `K(t) ≥ 0`", strengthened to RH + simplicity.
- **Parents:** route MC (frontier map: "Liouville K(t)≥0 remains paper-only candidate"); cards `1-in-progress/mc-scaled-liouville-density-cone.md` (C12.93), `1-in-progress/mc-complete-signed-correlation.md`; corpus `LiouvilleSummatoryPolyaBoundary` (Pólya/Ingham for `L(x)`).

## Statement
Let `J(t) = Σ_{n≥1} λ(n) e^{−nt}/n` and `K(t) = J(t) − tJ′(t)`.
- **(A) [L]** `∫_0^∞ J(t)t^{s−1}dt = Γ(s)ζ(2s+2)/ζ(s+1)` for `Re s > 0`.
- **(B) [L]** If `J(t) ≥ −C√t` for `0 < t ≤ t₀`, then RH holds and every zero of `ζ` on the critical line is simple.
- **(C) [P, one line]** If `K ≥ 0` on `(0, t₀]`, then `J(t)/t` decreases there, so `J(t) ≥ tJ(t₀)/t₀ ≥ −C√t`, and (B) applies. The MC candidate `K ≥ 0`, and C12.93's "`K_P ≥ 0` for every finite `P`" (which gives `K ≥ 0` in the limit), each imply RH and the simplicity of every critical zero.

## Proof
1. **Mellin.** Apply mathlib's `hasSum_mellin` with coefficients `λ(n)/n` and frequencies `n`. Absolute summability is `Σ n^{−1−σ} < ∞`. Corpus `LSeries_liouvilleC_eq_div` and `Γ(s+1) = sΓ(s)` turn `Γ(s)ζ(2s+2)/ζ(s+1)` into `κ(s) = Γ(s+1)Z(2s+2)/((2s+1)Z(s+1))`, with `Z(w) = (w−1)ζ(w)`.
2. **Logarithmic variable.** With `t = e^{−u}`, `mellin f s = ∫_ℝ e^{−su}f(e^{−u})du`. The bounds `|J(t)| ≤ −log(1−e^{−t}) ≤ 1 + log(1/t)` (for `t ≤ 1`) and `≤ 2e^{−t}` (for `t ≥ 1`) give the split `∫_0^∞ = Γ(s)L(λ,s+1) − E(s)`. Here `E(s) = ∫_{−∞}^0 e^{−su}J(e^{−u})du` is entire, since `exp(−e^{−u}) ≤ k!e^{ku}` for `u ≤ 0`.
3. **Landau.** For `u > 0`, the density `J(e^{−u}) + C′e^{−u/2}` (with `C′ = C₀ + 1`) is `≥ e^{−u/2}`, so its abscissa is `≥ −½`. The continuation `κ − E + C′/(z+½)` is analytic at every real point of `(−½, ∞)`, since `Z(σ+1) ≠ 0` for `σ > −1`. So Landau's theorem (corpus `false_of_analyticAt_abscissa`) puts the abscissa at `−½`. The identity theorem then gives `(∫e^{−zu}dν + E − C′/(z+½))(2z+1)Z(z+1) = Γ(z+1)Z(2z+2)` on `Re z > −½`.
4. **RH.** A zero of `Z` at `w` with `Re w > ½` kills the left side at `z = w − 1`, while `Γ(w)Z(2w) ≠ 0`.
5. **Simplicity.** `r∫e^{(½−r)u}dν` stays bounded as `r ↓ 0`, because `r·κ(−½+r) = Γ(½+r)Z(1+2r)/(2Z(½+r))` is continuous at `0`. Along `z = ρ − 1 + r`, at a critical zero of order `m`, the left side is `O(r^{m−1})`. The right side tends to `|Γ(ρ)Z(2ρ)| > 0`, so `m = 1`.

## Reading for the frontier
- **Route MC.** The paper-only candidate "Liouville `K(t) ≥ 0`" is now a Lean-certified sufficient condition, and it yields more than RH: it implies simplicity of every critical zero. Exact (ε-free) one-sided Liouville laws are RH+SZC-strength. Only ε-lossy targets (`J ≥ −C_εt^{½−ε}`, the corpus's stated MC target) are RH-equivalent.
- **Contrast with the prime lane.** ψ-type one-sided `√X` laws (wall 1) see `−ζ′/ζ`, whose poles are always simple (residue = multiplicity), so they are multiplicity-blind. Liouville/Möbius laws see `1/ζ`, whose poles have the zeros' order, so an exact positivity there forces simplicity.
- **Bias.** The real pole of `κ` at `−½` has residue `−√π/ζ(½) ≈ 1.214 > 0` [P]. This is the opposite sign to `L(x)`'s bias `√x/ζ(½) < 0`. The Γ-damping `|Γ(ρ−1)| ≍ e^{−π|γ|/2}` makes the zero terms tiny, so `J(t) ≈ 1.214√t` near `0` is plausible under RH + SZC. The candidate is not refutable by the bias, unlike Pólya's `L ≤ 0`.
- Relative to the corpus: `LiouvilleSummatoryPolyaBoundary` proves the `L(x)` version. The `J` version has a weaker hypothesis (an Abelian smoothing: `L ≥ −c√x` ⇒ `J ≥ −C√t`, not conversely) and attaches directly to the MC candidate.

## Lean
Module `RHTower/LiouvilleExponentialSumSimplicity.lean` (namespace `RHTower`), wired after `LiouvilleSummatoryPolyaBoundary`. `lake build --old` passed, the direct `lake env lean` gave zero messages, axioms `[propext, Classical.choice, Quot.sound]`, and lint reports nothing for this module.

| Claim | Declaration |
|-|-|
| Mellin transform of `J` | `mellin_liouvilleExpSum`, `Gamma_mul_LSeries_eq_kernel` |
| Bounds on `J` | `abs_liouvilleExpSum_le`, `abs_liouvilleExpSum_le_small`, `abs_liouvilleExpSum_le_large` |
| Exponential substitution | `mellin_eq_integral_cexp` |
| Entire tail | `liouvilleExpTail`, `hasDerivAt_liouvilleExpTail`, `differentiable_liouvilleExpTail` |
| Landau abscissa `−½` | `abscissa_liouvilleExpMeasure_eq` |
| Continuation identity | `liouvilleExp_continuation_identity` |
| RH | `riemannHypothesis_of_liouvilleExpSum_lower` (also `..._liouvilleExpLog_lower`) |
| Simplicity | `deriv_zetaResidueUnit_ne_zero_of_liouvilleExpSum_lower`, `liouvilleExp_zero_simple` |

## Novelty
- The mechanism (Landau plus a triangle inequality at poles) is Ingham's, and the corpus already uses it for `L(x)`.
- New: the statement for the Γ-smoothed exponential sum `J`, its attachment to MC's `K`-candidate, and the multiplicity reading (exact Liouville positivity ⇒ SZC).
- No external search (user directive). The corpus has no prior statement for `J`.

## Log
- 2026-10-09 (loop row 572): proved and formalized.

## Novelty correction (2026-10-09, after audit)
- The one-sided Abel-smoothed template is classical. Hardy–Littlewood (1918) and Landau proved: `Σ_{p>2}(−1)^{(p−1)/2}e^{−p/x} → −∞` ⟺ GRH for `L(s, χ₋₄)`, and the "⟹ GRH" half runs on Landau's theorem as here. So statement (B) is the Liouville/`1/ζ` analogue of the Hardy–Littlewood–Landau theorem, not a new kind of criterion.
- What remains new relative to the corpus:
  - the explicit Mellin identity for `J` and its RH + simplicity receiver in Lean;
  - the lane law: pole orders at critical zeros decide whether an exact one-sided law is RH-strength (`−ζ′/ζ`, `log ζ`), RH + SZC-strength (`1/ζ`), or impossible (`1/ζᵏ` with `k ≥ 2`, `(1/ζ)′`, `(ζ′/ζ)′`), the last by Hardy's theorem.
- Γ-damping is what makes the converse plausible for `J`, just as in Hardy–Littlewood–Landau, where the Abel weight `e^{−p/x}` damps the zero terms by `|Γ(ρ)|`.
- **Second correction (corpus audit).** The multiplicity mechanism is already in the corpus for the two-sided Möbius–Laplace bound `|Σμ(n)e^{−nx}| ≤ Cx^{−½}`:
  - `MobiusLaplaceBoundaryMultiplicity`: a one-pole Abel bound forbids double zeros on the line;
  - `MobiusLaplaceSimpleZeroResidueCap`: simplicity plus `‖Γ(ρ)/ζ′(ρ)‖ ≤ C`;
  - `MobiusLaplaceHedenmalmSimplicityUniversalityLaw`.
  
  The RH half follows Liflandsky (arXiv 2607.09797, recorded in `MobiusLaplaceCriterionFrontier`). New in MUST-834: the bound is one-sided; the Liouville sum carries a positive bias pole (`ζ(2s+2)`), which makes a one-sided hypothesis natural; and the result attaches to MC's `K ≥ 0` candidate. The "lane law" reading is therefore not new to the corpus.
- **Third correction (corpus audit, 2026-10-09).** `1-in-progress/mc-liouville-k-sign-conjecture-loop-opus.md` (2026-10-05) already had on paper:
  - the Mellin transform of `K`;
  - the bias `(√π/2)/|ζ(½)|`;
  - the residue squeeze: `K ≥ 0` ⇒ RH, simple zeros, and `|Γ(ρ+1)ζ(2ρ)/((ρ−1)ζ′(ρ))| ≤ (√π/2)/|ζ(½)|`.
  
  MUST-834 is therefore the Lean formalization of that loop's RH + simplicity half, under the weaker hypothesis `J ≥ −C√t`. The residue cap is not formalized.
