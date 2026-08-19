# The Γ-module M_∞ — the archimedean Euler factor as a rank-1 polynomial-multiplier difference module

- **ID:** gamma-module-construction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / CONSTRUCTION — Door grade **BRIDGE** (Source A alone; the weld is where it turns native)
- **Priority:** FOUNDATIONAL (the Source-A object of the completed constraint module `M_Λ=M_∞⊗M_ζ`)
- **Source:** the Hölder-recentering (Source A = Γ; `00-foundations` N1⁺); `#90 §64` (`Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`,
  the unique non-constant polynomial multiplier); Lerch 1894 / Kurokawa absolute zeta (`Γ` = ζ-reg det);
  builds `completed-base-archimedean-coordinate.md`; feeds `lambda-difference-differential-hypertranscendence.md`,
  `archimedean-prime-cross-term.md`. 00-status row #27, #130.
- **Numerics:** `computations/2026-06-19-gamma-module-Minfty.py(.out)` — recurrence, connection, Lerch all ≥30 digits.

---

## Result — `M_∞` constructed

`Γ_ℝ(s) := π^{-s/2}Γ(s/2)` is realized as a **rank-1 `(σ_∞, ∂_s)`-module** `M_∞ = R⁺·e`:

**(1) Difference structure (the polynomial multiplier).** With `σ_∞ : s ↦ s+2`,
> `σ_∞ e = a(s)·e`, `a(s) = s/2π`  —  i.e. `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)`.
*Proof:* `Γ_ℝ(s+2)=π^{-(s+2)/2}Γ(s/2+1)=π^{-s/2}π^{-1}(s/2)Γ(s/2)=(s/2π)Γ_ℝ(s)`. ∎ The multiplier `a(s)=s/2π`
is the **unique non-constant (degree-1 polynomial) multiplier** among the places (#90 §64) — the Source-A
signature (vs the prime places' **constant** multipliers `p^{-1}`); this is the multiplier-dichotomy divide
(#131): `a(s)` is **non-CC** (`∂_s\log a = 1/s ≠ 0`, the Hölder obstruction). *(Recurrence verified ≥30 digits.)*

**(2) Differential structure (the rank-1 `∂_s`-connection).**
> `∇_s e = (−½\log π + ½ψ(s/2))·e`  —  i.e. `∂_s\log Γ_ℝ = −½\log π + ½ψ(s/2)` (digamma `ψ`).
*Proof:* `\log Γ_ℝ = −\tfrac{s}{2}\log π + \logΓ(s/2)`; differentiate. ∎ `[∂_s, σ_∞]` acts compatibly
(`∂_s` and the shift commute as operators); the connection is the archimedean generator restricted to `M_∞`.
*(Connection verified ≥30 digits.)*

**(3) `Γ_ℝ` = INVERSE ζ-regularized determinant (the Euler-factor convention; Kurokawa link).** Via **Lerch's
formula** (IMPORT) `\tfrac{d}{dz}ζ_H(z,a)\big|_{z=0} = \logΓ(a) − ½\log(2π)`, the ζ-regularized determinant of
the shift/number generator `N+s/2` (spectrum `{s/2+k}_{k≥0}`, `N` the number operator) is
> `det_ζ(N+s/2) = exp(−ζ_H'(0,s/2)) = {\prod_{k≥0}}^{\mathrm{reg}}(s/2+k) = \sqrt{2π}/Γ(s/2)`,
so `Γ(s/2)` is the **reciprocal** of this determinant (up to the constant `√(2π)`):
> `Γ(s/2) = \sqrt{2π}·det_ζ(N+s/2)^{−1}`,  equivalently  `Γ(s/2)·det_ζ(N+s/2)=\sqrt{2π}`.
Hence `Γ_ℝ(s)=π^{−s/2}Γ(s/2)=π^{−s/2}\sqrt{2π}·det_ζ(N+s/2)^{−1}` — the `π^{−s/2}` is the archimedean conductor
power, separate from the determinant. **This is the universal "local Euler factor = inverse determinant"
structure**, uniform across all places: finite primes give `L_p(s)=det(1−p^{−s}\mathrm{Fr}_p)^{−1}`, the
archimedean place gives `Γ_ℝ(s)=π^{−s/2}\sqrt{2π}·det_ζ(N+s/2)^{−1}` — both *inverse* determinants of the
place's generator. (Connes scaling / Kurokawa absolute-zeta, #90 §1; matches the verified one-sided-ladder
identity `Γ(a)·det_ζ(N+a)=√2π`, DeWitt #347/#357.) `M_∞` is exactly the object whose **inverse** regularized
determinant is the archimedean Γ-factor. *(Verified ≥35 digits incl. complex argument
`a=0.25+7i`: `computations/2026-06-19-gamma-module-invdet.py`; det−reciprocal `≤8e−36`, `Γ·det−√2π ≤2e−40`.)*

**(4) The completed constraint object.** `M_Λ := M_∞ ⊗ M_ζ` carries the completed `Λ(s)=Γ_ℝ(s)ζ(s)` as its
diagonal section; the FE `Λ(s)=Λ(1−s)` acts on it. `M_∞` is the rigorous archimedean factor the weld cards
(#132, #134) previously used only as "the concrete analytic incarnation `Γ_ℝ`."

## Door passport
- **Door-2:** `M_∞` **alone** is differential Galois / Hölder (Source A = a border) — **BRIDGE** by itself, as
  the multiplier dichotomy predicts (non-CC polynomial multiplier). Its value is being a *constructed object*
  the weld consumes; native content lives in `M_∞⊗M_ζ` under the joint structure (the cross-term / weld cards).
- **Door-5:** over `F_q` there is **no archimedean place** ⟹ `M_∞` is absent; the completed module degenerates
  to `M_ζ` alone (all places constant-multiplier/CC, holonomic — corank 1, #121).

## Gates
- [x] 0 → 1 in-progress: `M_∞` defined; recurrence + `∂_s`-connection fixed; `Γ=ζ-reg det` link stated;
  `M_Λ` posed; numerics planned; Door passport.
- [x] 1 → 2 fully-proven: recurrence (multiplier `s/2π`) and connection (digamma) **proved + verified ≥30
  digits**; `Γ_ℝ` = **inverse** ζ-reg det via **Lerch** (`det_ζ(N+s/2)=√2π/Γ(s/2)`; import, verified ≥35
  digits); `M_Λ=M_∞⊗M_ζ` diagonal `=Λ`; `F_q` degeneration. Grade BRIDGE (Source A alone).
- [x] 2 → 3 formalized: rank-one `(σ∞, ∂s)` module `archimedeanGammaModule`, connection
  `logDeriv_Gammaℝ`, Lerch `deriv_hurwitzZetaEM_zero` with `Gamma_mul_zetaRegDet`, and the completed
  object `completedZetaModule` with `completedZetaModule_gen_eq`; `lake build` green; axioms clean.
  See "Lean certification (complete)" below.
- [ ] 3 → 4 publication-ready: "the archimedean Euler factor as a polynomial-multiplier difference module."

## Cross-references
- `completed-base-archimedean-coordinate.md` — the base `R⁺` (dependency).
- `multiplier-dichotomy-theorem.md` (#131) — `M_∞` is the polynomial-multiplier / non-CC worked example.
- `lambda-difference-differential-hypertranscendence.md` (#134), `archimedean-prime-cross-term.md` (#132) —
  consume `M_∞`/`M_Λ`; now rest on this rigorous object instead of the analytic incarnation.
- `../../door/bucket-the-seam-archimedean-obstruction.md`, `compute-omega-h2-gl.md` — own the `Γ=ζ-reg det`/`ω` face.

## Log
- 2026-06-19 — created in 0-backlog (Source-A object).
- 2026-06-19 — Professor: built to 2-fully-proven, acting on the "constraint, not flow" steer (constructing
  the archimedean factor of the completed *constraint* object `M_Λ`). Proved + verified (≥30 digits): (1)
  recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)`, unique non-constant polynomial / non-CC multiplier (#131 divide); (2)
  rank-1 `∂_s`-connection `∂_s\logΓ_ℝ=−½\logπ+½ψ(s/2)`; (3) `Γ_ℝ` = ζ-regularized determinant of the shift
  generator via **Lerch** (`ζ_H'(0,a)=\logΓ(a)−½\log(2π)` ⟹ reg-`∏(s/2+k)=\sqrt{2π}/Γ(s/2)`). `M_Λ=M_∞⊗M_ζ`
  carries `Λ`. Grade **BRIDGE** (Source A alone — the weld is native). Numerics
  `computations/2026-06-19-gamma-module-Minfty.*`.
</content>

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. The recurrence `Γ_ℝ(s+2)=(s/2π)Γ_ℝ(s)` and the displayed logarithmic-connection calculation are fine as paper identities, but the ζ-regularized determinant conclusion has the determinant/inverse determinant reversed. Lerch's formula gives
`ζ_H'(0,a)=log Γ(a)-1/2 log(2π)`, so the standard ζ-regularized product/determinant is
`exp(-ζ_H'(0,a)) = √(2π)/Γ(a)`, exactly as the card and numeric script compute. That is reciprocal to `Γ(a)` up to the constant, not `Γ(a)` itself. Therefore the statement that `Γ(s/2)` / `Γ_ℝ(s)` is the ζ-regularized determinant of the shift generator is not proven as written. A repaired ticket should state the inverse determinant (or specify a reciprocal determinant convention/operator) and then re-check the `π^{-s/2}` normalization.

## Repair note — 2026-06-19 (Professor): Leaner's det/inverse-det return CLOSED (and it improved the card)
Leaner's return (correct): the ζ-reg determinant of the shift generator is `√2π/Γ(s/2)`, the **reciprocal** of
Γ, not Γ itself — so "Γ_ℝ IS the ζ-reg determinant" was wrong as written. **Fixed** claim (3): Γ_ℝ is the
**inverse** ζ-reg determinant — `det_ζ(N+s/2)=exp(−ζ_H'(0,s/2))=√2π/Γ(s/2)`, hence
`Γ_ℝ(s)=π^{−s/2}√2π·det_ζ(N+s/2)^{−1}` (the `π^{−s/2}` re-checked: it is the archimedean conductor power,
independent of the determinant). The correction is **not a patch but a clarification on-mission**: it makes the
archimedean factor obey the **universal "local Euler factor = inverse determinant"** law — finite primes
`L_p=det(1−p^{−s}Fr)^{−1}`, ∞ `Γ_ℝ=π^{−s/2}√2π·det_ζ^{−1}` — and aligns exactly with the verified one-sided
ladder `Γ(a)·det_ζ(N+a)=√2π` (DeWitt #347/#357). Verified ≥35 digits incl. complex `a=0.25+7i`
(`computations/2026-06-19-gamma-module-invdet.py`: det−reciprocal ≤8e−36, Γ·det−√2π ≤2e−40). Re-banked to
`2-fully-proven`. Grade BRIDGE (Source A alone) unchanged. Downstream (`lambda-…`, `archimedean-prime-cross-term`)
should read M_∞'s determinant as **inverse** ζ-det where they cite it.

## Lean certification update — 2026-06-19 (Leaner)

The scalar recurrence/connection part of Result (1)-(2) is already Lean-backed by
`../3-formalized/archimedean-gamma-shift-connection.md`: `gammaReal_shift_two`,
`digamma_half_add_one`, and `gammaRealLogConnection_shift_compat` are in
`formal/GaloisForLFunctions/RHTower/ArchimedeanGamma.lean` and audited in `scripts/check_axioms.sh`.
The parent ticket remains in `2-fully-proven` because the full rank-one module construction,
Lerch inverse determinant import, and completed-object wiring are not formalized as Lean theorems.

## Lean certification (complete)

Four new modules, all wired into their umbrellas, all `lake build` green, every declaration below
depending only on `propext`, `Classical.choice`, `Quot.sound`:

| Module | Contents |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/EulerMaclaurinSecondOrder.lean` | second-order Euler-Maclaurin summation with the periodic `B₂` kernel |
| `formal/GaloisForLFunctions/HTGeometry/BinetLogGamma.lean` | Binet's first formula for `log Γ` |
| `formal/GaloisForLFunctions/HTGeometry/LerchHurwitzDerivative.lean` | the Hurwitz continuation, Lerch's formula, the ζ-regularized determinant |
| `formal/GaloisForLFunctions/RHTower/ArchimedeanGammaModule.lean` | `M_∞`, `M_ζ`, `M_Λ`, the multiplier dichotomy |

### (1) Difference structure — the polynomial multiplier

- `gammaReal_shift_two` (already owned): `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)`.
- `archimedeanGammaModule` — the rank-one datum itself, with generator `Γ_ℝ`, shift `s ↦ s+2`,
  multiplier `s/(2π)`, connection `gammaRealLogConnection`, domain `{Re s > 0}`; the structure
  `RankOneShiftDiffDatum` carries shift-stability, nonvanishing, differentiability, the multiplier
  identity and the connection identity as fields, so the datum cannot be built without all five.
- `archimedeanGammaModule_mult_polynomial`, `archimedeanGammaModule_mult_natDegree` — the multiplier
  is the evaluation of a polynomial of degree exactly one.

### (2) Differential structure — the rank-one connection

- `logDeriv_Gammaℝ` : `∂_s log Γ_ℝ(s) = −½ log π + ½ ψ(s/2)` for `Re s > 0`.  **This closes the
  card's item (2)**; the corpus previously owned only the shift-compatibility of the connection
  coefficient (`gammaRealLogConnection_shift_compat`), not the identification with `∂_s log Γ_ℝ`.
- supporting: `differentiableAt_Gammaℝ`, `Gammaℝ_ne_zero`, `half_re`, `half_ne_negNat`.

### The multiplier dichotomy (#131)

- `logDeriv_archimedeanGammaModule_mult` : `∂_s log a(s) = 1/s` for `s ≠ 0` — the Hölder obstruction.
- `logDeriv_const` : a constant multiplier has vanishing logarithmic derivative.
- `archimedeanGammaModule_mult_not_const` : hence `a(s)` is **not** constant — the archimedean place
  is on the non-CC side of the divide.

### (3) `Γ_ℝ` = INVERSE ζ-regularized determinant — Lerch, proved from scratch

Mathlib has neither Lerch's formula nor `ζ'(0)`, so the whole chain is new corpus infrastructure.
The route runs through one integral kernel `K(a) = ∫_0^∞ P₂(x)(x+a)^{-2}dx`, `P₂(x) = ({x}²−{x})/2`:

| Step | Lean name |
|---|---|
| second-order Euler-Maclaurin, `∑_{m≤N} f(m) = ∫_0^N f + (f(0)+f(N))/2 − ∫_0^N P₂ f''` | `euler_maclaurin_second_order`, `euler_maclaurin_second_order_real` |
| the periodic `B₂` kernel: bounded by `1/8`, vanishing at integers | `bernoulliHalfPer`, `abs_bernoulliHalfPer_le`, `bernoulliHalfPer_natCast` |
| Binet: `log Γ(a) = (a−½) log a − a + ½ log(2π) − K(a)` | `log_Gamma_eq_binet`, `Gamma_eq_binet_exp` |
| the `√(2π)` enters through Stirling and Euler's Gauss product | `tendsto_stirlingCorrection`, `tendsto_gaussLogSeq`, `tendsto_shiftLogTerm` |
| the Euler-Maclaurin continuation of `ζ_H(s,a)` | `hurwitzZetaEM` |
| it *is* the spectral series `∑_{n≥0}(n+a)^{-s}` on `Re s > 1` | `hurwitzZetaEM_eq_tsum` |
| the continuation integral is continuous at `s = 0` (dominated convergence) | `continuousAt_emKernel_zero` |
| **Lerch**: `ζ_H'(0,a) = log Γ(a) − ½ log(2π)` | `hasDerivAt_hurwitzZetaEM_zero_lerch`, `deriv_hurwitzZetaEM_zero` |
| `det_ζ(N+a) = exp(−ζ_H'(0,a)) = √(2π)/Γ(a)` — the **inverse** determinant, as the repair note requires | `zetaRegDet`, `zetaRegDet_eq` |
| the one-sided ladder `Γ(a)·det_ζ(N+a) = √(2π)` | `Gamma_mul_zetaRegDet` |
| `Γ_ℝ(s)·det_ζ(N+s/2) = π^{−s/2}√(2π)` | `Gammaℝ_mul_zetaRegDet`, `archimedeanGammaModule_gen_mul_zetaRegDet` |

The direction is the corrected one: `Γ_ℝ` is `π^{−s/2}√(2π)` times the **inverse** of the
regularized determinant, matching the repair note and the universal "local Euler factor = inverse
determinant" law.

### (4) The completed object `M_Λ`

- `RankOneShiftDiffDatum.tensor` — the tensor of two rank-one data: multipliers multiply,
  connections add, generators multiply.
- `completedZetaModule = archimedeanGammaModule.tensor zetaModule` (`M_Λ = M_∞ ⊗ M_ζ`).
- `completedZetaModule_gen_eq` : the diagonal section is `Λ(s) = Γ_ℝ(s)·ζ(s) = completedRiemannZeta s`.
- `completedZetaModule_mult`, `completedZetaModule_conn`, `completedZetaModule_domain`.
- `completedZetaModule_functional_equation` : `Λ(1−s) = Λ(s)`.

### Not formalized

The Door-5 remark (over `F_q` there is no archimedean place, so the completed module degenerates to
`M_ζ`) is a statement about a different geometry, not a theorem about the objects this card builds.
