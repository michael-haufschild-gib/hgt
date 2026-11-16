# Spectral Theory of the Cubic Cover (STCC)

Namespace `GaloisForLFunctions.SpectralTheoryOfTheCubicCover`; umbrella
`SpectralTheoryOfTheCubicCover.lean`. Source: the long columns of the floor bin in
`CoherenceTheoryOfReciprocityFamilies` (CRF, question Q1 = B175).

## 1. Why this field

The cubic-theta probe reads the zeros of `ζ` through a family of rows `u ∈ ℤ[ω]`. CRF reduced the
binding part of its floor bin (B175) to one first moment: the root number of row `u` is
`G(u) γ₂(u)²`, a phase times the square of the normalized cubic Gauss sum
(`rowRootNumber_eq_thetaPhase_mul_sq`). STCC’s Fourier-square weight uses the conjugate Gauss sum;
passing to the row-root moment also requires its conductor phase. The untwisted squarefree series has a Gaussian-smoothed main term of size `U^{2/3}`,
with a remainder `O_a(U^a)` for every `5/8<a<2/3`. The remaining phase and column dependence
belong to the long-column problem.

The tool for squares of automorphic forms is the Rankin–Selberg method: unfold `θ²` against an
Eisenstein series and read the Dirichlet series `Σ_ν T(ν)² N(ν)^{−w}` of the squared Fourier
coefficients from the analytic behaviour of the Eisenstein series. On the cubic cover, `θ²` is
not square integrable; subtracting its four rational cusp profiles leaves a bounded remainder.
MMD supplies the quotient, its self-adjoint Laplacian, the Fredholm pencil and resolvent, and the
identity of the Eisenstein series with its seed plus resolvent correction. STCC unfolds the bounded
remainder and computes the explicit scattering of the cusp subtraction. Opposite translations
then separate the untwisted squarefree series and identify its nonzero simple pole at `2/3`.
Real spectral removability and vertical resolvent bounds extend it across the real axis and
permit a Gaussian Mellin contour shift to an actual arithmetic asymptotic.

## 2. Objects

| Object | Meaning |
|---|---|
| `Γ`, `κ` | the principal level-three group `levelThree ⊂ SL₂(ℤ[ω])` and the cubic Kubota character `κ = complexCharacter` |
| `Γ∞`, `P` | the cusp stabilizer (translations by `3ℤ[ω]`) and a period parallelogram of `3ℤ[ω]` |
| `ℍ³`, `μ`, `v` | hyperbolic three-space, the invariant volume `dx dy dv/v³`, the height |
| multiplier `j` | `F(Mw) = κ(M)^j F(w)`; products add multipliers modulo three |
| `E(w, s)` | the cubic Eisenstein series `Σ_{Γ∞\Γ} κ(M)^{−1} v(Mw)^s`, multiplier `1`, `Re s > 2` |
| `E(w ∣ ψ)` | the incomplete Eisenstein series `Σ_{Γ∞\Γ} κ(M)^{−1} ψ(v(Mw))` for a height profile `ψ` |
| `θ` | the residue of `E` at `s = 4/3`: multiplier `1`, eigenvalue `8/9`, constant term `c v^{2/3}`, Fourier coefficients `T(ν)` |
| constant term | `a₀(F; v) = |P|^{−1} ∫_P F(z + jv) dz` |
| `E_{κ²}`, `E*` | the Eisenstein series of multiplier `2` (the conjugate of `E`), its residue `\overline{θ}` at `4/3`, its constant Laurent coefficient `E*` there |
| `R(F, s)` | the renormalized Rankin–Selberg integral of a function of moderate growth |
| `D(w)`, `S(w)` | `Σ_ν T(ν)² N(ν)^{−w}` and its squarefree part |

## 3. Language

- **Unfolding**: the integral of `F · E(·∣ψ)` over `Γ\ℍ³` is the integral of `F · ψ(v)` over `Γ∞\ℍ³`,
  i.e. the Mellin pairing of `ψ` with the constant term of `F`.
- **Multiplier bookkeeping**: `θ²` has multiplier `κ²`; it pairs with an Eisenstein series of
  multiplier `κ` (`κ³ = 1`), and it is renormalized by one of multiplier `κ²`.
- **Growth exponent**: the power `v^α` of the constant term at a cusp; `θ²` has `α = 4/3`.
- **Coinciding pole**: a growth exponent equal to a pole of the renormalizing Eisenstein series; it
  produces `v^{2/3} log v` in the renormalized constant term.

## 4. Mechanisms

1. *Unfolding on the cubic cover.* A strict fundamental domain for `Γ` and one for `Γ∞`
   (`hyperbolicFundamentalSet_unique`), the invariant volume, and the coset sum of `E(·∣ψ)`.
2. *Continuation by seed and resolvent* (MMD). `E(s) = seed(s) − R(s(2 − s)) defect(s)`, the defect
   compactly supported and entire in `s`; the resolvent exists off the spectrum and is meromorphic at
   `8/9`.
3. *Renormalization by the rational cusp subtraction.* `G = θ_s² − H`,
   `H = c² Σ_q conj E_1(r_q · ∣ 1_{v≥2} v^{4/3})` over the four rational cusps. `θ_s` grows only in
   the rational cusp class and is exponentially small at the two ramified classes, so `G` is bounded
   and square integrable. Its pairing with `E(s)` is a seed term (holomorphic for `Re s < 13/3`) plus
   the `L²` pairing with MMD's resolvent correction (at most a simple pole at `4/3`). No pointwise
   continuation of `E` is needed.
4. *The double pole.* The scattering of `H` into `∞` has Mellin transform `c² Φ(s) f̃(s)`,
   `f̃(s) = 2^{4/3−s}/(s − 4/3)`, `Φ(s) = Φ₀(s)/(s − 4/3)`, `Φ₀(4/3) = 12π|P| r`; the four rational
   cusps contribute `1 + 3 = 4`. So `(s − 4/3)² M(s) D(s) → 12π c² r = 108 π³ r³ ≠ 0`.
5. *Cube frequencies.* `D(w) = \overline{C}² ζ_K(3w − 1) S(w)` on unramified indices; a double pole of `D`
   is a simple pole of `S`: the squarefree part is coherent at `2/3`.
6. *Gaussian arithmetic transfer.* Compact forcing grows linearly in height, cancelled by the
   self-adjoint resolvent bound. Cutoff-independent spectral residues remove real poles except
   `4/3`; the Hecke seed controls cube removal on `Re w>5/8`. With
   `W(y)=exp(−(log y)²/4)/(2√π)`, shifting the Mellin contour gives
   `Σ_A σ(A)W(N(A)/X)=exp(4/9)R X^(2/3)+O_a(X^a)` for `5/8<a<2/3`, `R≠0`
   (`gaussianSmoothedUntwistedTheta_main_term`).

## 5. Pillar theorems

**From MMD.**

| Theorem | Lean |
|---|---|
| strict fundamental domains for every subgroup of level three; invariant volume | `hyperbolicFundamentalSet_unique`, `hyperbolicFundamentalSet_isFundamentalDomain`, `hyperbolicVolume_invariant` |
| the Eisenstein series as a sum of cusp-height powers; automorphy | `hyperbolicEisenstein_eq_height_series`, `cosetHeight_cosetOf`, `hyperbolicEisenstein_automorphy` |
| the self-adjoint quotient Laplacian; the Fredholm pencil on `0 ≤ λ < 1`; the meromorphic resolvent at `8/9` | `TheCubicVariationalLaplacian`, `TheCubicSpectralPencilIsFredholm`, `kernelSpectralResolvent_meromorphicAt` |
| the Eisenstein remainder equals the resolvent correction (`Re s > 4`, `Im s > 0`) | `TheCubicInitialResolventMatching` |
| the residue `θ` is nonzero, has eigenvalue `8/9` and transforms by `κ` | `TheCubicResidueIsNonzero`, `TheCubicResidualCharacter` |
| the Fourier coefficients of `θ` on squarefree times cube indices | `normalized_sourceFourier_squarefree_cube`, `sourceFourier_squarefree_cube_support_iff` |

**Of this programme.**

| Theorem | Lean | Answers |
|---|---|---|
| unfolding: for `F` of multiplier `κ⁻¹` and any strict fundamental set `D_∞` of `Γ∞`, `∫_{D_Γ} F · E(·∣ψ) = ∫_{D_∞} F · ψ(v)`, with absolute convergence; the complete series `ψ(t) = t^s` | `integral_mul_incompleteEisenstein`, `lintegral_norm_mul_incompleteEisenstein`, `integral_mul_hyperbolicEisenstein`, `cuspSelect` | SQ1 |
| `Γ∞` is the period lattice `3ℤ[ω]`; the period strip is a strict fundamental set; in coordinates `dμ = v^{−3} dv dz` | `translationOf_injective`, `translationOf_surjective`, `cuspStrip_unique`, `cuspStrip_coordinates` | SQ1 |
| the incomplete Eisenstein series reads the constant term: `∫_{D_Γ} F · E(·∣ψ) = ∫_0^∞ ψ(v) (∫_P F(z + jv) dz) v^{−3} dv`; for `ψ = t^s` the Mellin transform of the constant term | `integral_mul_incompleteEisenstein_eq_constantTerm`, `integral_mul_hyperbolicEisenstein_eq_constantTerm` | SQ1, SQ3 |
| the scattering coefficient continues across `4/3`: `(s − 4/3)φ(s)` is holomorphic on `Re s > 1` with value `r ≠ 0` at `4/3`; `Res ζ_K = L(1, χ₋₃)` | `sub_mul_scatteringCoefficient`, `clearedScattering_differentiableOn`, `clearedScattering_four_thirds`, `dedekindZeta_residue_eq` | SQ2, SQ4 |
| the constant term of `E` continues across `4/3` with residue `3πr v^{2/3}`; its constant Laurent coefficient is `v^{4/3} + v^{2/3}(g'(4/3) − 3πr log v)` | `sub_mul_constantTerm`, `clearedConstantTerm_four_thirds`, `hasDerivAt_clearedConstantTerm` | SQ2, SQ4 |
| Parseval on `P` for absolutely convergent cusp-character series; Rankin–Selberg for the square of any multiplier-`κ` function with such expansions; the instance `θ_s` (projected theta), with `b(v,h)b(v,−h) = T_s(h)² v² K_{1/3}(4π|ξ_h|v)²` | `integral_cuspCharacterSeries_sq`, `integral_sq_mul_incompleteEisenstein`, `integral_sourceThetaSq_mul_incompleteEisenstein`, `sourceAmplitude_mul_neg` | SQ3 |
| the cube frequencies factor out: `A B³` determines `A` (squarefree) and `B`; `T_s(gen(A)gen(B)³)² = \overline{C}² N(B) σ(A)` with `|σ(A)| = 1`; for `Re w > 1`, `Σ_I N(I)^{−w} T_s(gen I)² = \overline{C}² Z₀(3w − 1) Σ_{A sqfree} N(A)^{−w} σ(A)` (unramified ideals) | `thetaSquarefreePart_mul_cube`, `thetaCubePart_mul_cube`, `sourceCoefficient_sq`, `thetaSquareDirichlet_eq` | SQ5 |
| Hecke bound `|T_s(h)| ≤ C(1 + |ξ_h|)` at every frequency, from `θ_s ∈ L²` and the cusp-height count `#{x : v_x(w) ≥ Y} ≤ K/Y²` | `sourceCoefficient_hecke_bound`, `card_cuspCosets_height_le` | SQ5 |
| Mellin link: `∫_0^∞ v^s R(v) v^{−3} dv = M(s) Σ_{h≠0} T_s(h)²(4π|ξ_h|)^{−s}` (`Re s > 4`), `M` holomorphic on `Re s > 2/3`, `M(4/3) ≠ 0` | `integral_thetaSqRemainder`, `besselSqMellin_differentiableAt`, `besselSqMellin_four_thirds_ne_zero` | SQ4 |
| the positive-ray and cosh Bessel kernels agree; `M(s)=2^(s−3) Γ(s/2+1/3) Γ(s/2)^2 Γ(s/2−1/3)/Γ(s) ≠ 0` on `Re s>2/3`; the untwisted continuation is holomorphic on its upper strip | `schlafliBesselK_eq_modifiedBesselKOrder`, `besselSqMellin_ne_zero`, `untwistedSquarefreeSeries_holomorphic_simple_pole` | SQ4, SQ5 |
| the Eisenstein pairing of an `L²` function splits into seed term and resolvent correction; the correction pairing is holomorphic off `ℝ` and has at most a simple pole at `4/3` | `integral_mul_eisenstein_eq`, `levelPairing_correction_analyticAt`, `levelPairing_correction_center` | SQ2 |
| the rational cusp subtraction `H`: multiplier `κ⁻¹`, `= c² f(v)` above height `1/2`; its scattering `Mellin(a₀(H) − |P|c²f) = c² Φ(s) f̃(s)` (`Re s > 10/3`) | `cuspSubtraction_upper`, `integral_scatterPart`, `sub_mul_scatterTotal` | SQ4, SQ6 |
| `G = θ_s² − H` is bounded on `ℍ³`, `O(v^{−7/3})` high in the cusp, square integrable | `renormalizedThetaSq_bounded`, `renormalizedThetaSq_memLp` | SQ4, SQ6 |
| **double pole**: `M(s) D(s)` continues to `{1 < Re s < 13/3, Im s > 0}` and to a punctured disc at `4/3`, with `(s − 4/3)² M(s) D(s) → 108 π³ r³ ≠ 0` | `thetaSqDirichlet_double_pole` | SQ4 |
| twisted multiplicativity `T(h₀ gen I) T(1) = (h₀/gen I)₃ T(h₀) T(gen I)`; every `h ≠ 0` is uniquely `u λ^m gen I`; `D(s) = \overline{C}² Z₀(3s/2 − 1) Σ_{u,m} (T(uλ^m)/T(1))² (4π|ξ_{uλ^m}|)^{−s} S_{uλ^m}(s/2)` with nine twisted squarefree series `S_{h₀}(w) = Σ_A (h₀/gen A)₃² σ(A) N(A)^{−w}` (`u` mod `±1`, `m` mod 3); `T(uλ) = 0`, `T(u) ≠ 0 ⇒ u = ±1` | `sourceCoefficient_twisted_mul`, `thetaSqDirichlet_eq_zeta_mul`, `twistedSquarefreeSeries_lambda_mod`, `sourceCoefficient_unit_mul_lambda`, `sourceCoefficient_unit_eq` | SQ5 |
| the twisted squarefree combination `Q` has a simple pole at `4/3`: `(s − 4/3) M(s) Q(s) → 243 π³ r³ / (\overline{C}² L(1, χ₋₃)) ≠ 0` | `twistedSquarefreeCombination_simple_pole` | SQ5 |
| rotated correlations `C_ε = Σ T(εh) T(h) |ξ_h|^{−s}` split the same way with twists `S_{ε²uλ^m}`; for `ε ≠ ±1` only frequencies divisible by 3 contribute | `rotatedCorrelation_eq_zeta_mul`, `rotatedCorrelation_eq_three_layer` | SQ5 |
| the rotated product `θ_s(R·)θ_s(R⁻¹·)` (`R = diag(ω, ω²)`) has multiplier `κ⁻¹`; renormalized by the two-cusp subtraction `h(R·)h(R⁻¹·)` (`h` the linear subtraction of `θ_s`) it is bounded; **`(s − 4/3)² M(s) C_ω(s) → 54π³r³`**, half of `D` | `rotatedRenormalized_bounded`, `rotatedCorrelation_double_pole` | SQ5 |
| the three-divisible twisted combination `Q₃` has a simple pole with half the residue of `Q`: the coefficients at frequencies divisible by 3 are not negligible | `threeLayerCombination_simple_pole` | SQ5 |
| opposite translations by `±ω` leave one growing cusp and read `C_U(s)=Σ T(h)²e(2ωξ_h)(4π‖ξ_h‖)^{−s}`; its completed double-pole coefficient is `27π³r³` | `thetaLinear_translation_mul`, `translatedCorrelation_double_pole` | SQ5 |
| `D−C_U=(3/2)D₀`; the two primary signs give `D₀(s)=2(4π‖ξ₁‖)^{−s} C̄²Z₀(3s/2−1)S₁(s/2)`; **the actual untwisted squarefree series has a nonzero simple pole at `w=2/3`**, with residue `untwistedThetaResidue` | `thetaSqDirichlet_sub_translated`, `unramifiedSquare_eq_squarefree`, `untwistedSquarefreeSeries_simple_pole` | SQ5 |
| `θ²` has multiplier `κ⁻¹`; its constant term is `|P|(c² v^{4/3} + Σ_h a(v, h) a(v, −h))`, `c = 3πr`, `a(v, h)a(v, −h) = T(h)T(−h)v²K_{1/3}(4π|ξ_h|v)²`; Rankin–Selberg: `∫_{D_Γ} θ² E(·∣ψ) = |P| ∫_0^∞ ψ(v)(c²v^{4/3} + Σ_h a(v,h)a(v,−h)) v^{−3} dv`, unconditional for continuous `ψ` of compact support in `(0, ∞)` | `thetaSq_automorphy`, `integral_thetaSq_periodDomain`, `thetaAmplitude_mul_neg`, `integral_thetaSq_mul_incompleteEisenstein_of_compact` | SQ3 |

## 6. Questions

| # | Question | State |
|---|---|---|
| SQ1 | Unfolding: is `∫_{Γ\ℍ³} F · E(·∣ψ) = ∫_{Γ∞\ℍ³} F · ψ(v)` for every `F` of multiplier `κ^{−1}` with the right integrability? | yes (Lean) |
| SQ2 | Is `E(w, s)` meromorphic on `Re s > 1` as a function on `ℍ³`, with the single pole `4/3`, and of polynomial growth on vertical lines? | not needed: pairings of `L²` functions with `E(s)` continue by MMD's resolvent (Lean); the pointwise form stays open |
| SQ3 | The constant term of `θ²`: `c² v^{4/3} + Σ_ν T(ν)T(−ν) W_ν(v)²`, `T(−ν) = T(ν)` | yes (Lean) |
| SQ4 | The renormalized `R(θ², s)`: continuation past `4/3`, the double pole, its leading coefficient | yes for `θ_s`: `(s − 4/3)² M(s)D(s) → 108π³r³` (Lean) |
| SQ5 | The main term of `Σ_{N(ν) ≤ X} T(ν)² ω(N(ν)/X)` and of the squarefree part `S` | the actual untwisted `S₁` is separated by opposite translations and has an explicit nonzero simple pole at `2/3` (Lean); the contour shift and smoothed asymptotic remain open |
| SQ6 | The other cusps of `Γ` where `θ` has a constant term | for `θ_s`: the four rational cusps, none at the two ramified classes (Lean) |
| SQ7 | The twisted versions read by the long columns: `θ · θ_n` for the column index `n` | open |

## 7. Traps

| Trap | Truth |
|---|---|
| `⟨θ², E(·, s)⟩` converges for `Re s` large | `θ²` grows like `v^{4/3}` and `E` like `v^s`: it converges for no `s`; unfolding needs incomplete series or renormalization |
| `θ²` pairs with `θ̄` | `θ²` has multiplier `κ²`; the residual eigenfunction of multiplier `κ²` is `\overline{θ}`, and the pairing partner of `θ²` is `E` of multiplier `κ` |
| A growth exponent gives a simple pole | when it coincides with a pole of the renormalizing series it gives a logarithm and a double pole |
| A pole of `D` at `2/3` shows the squarefree part is coherent | the cube frequencies alone give a simple pole; the squarefree part needs the double pole |
| The resolvent continuation covers the real segment `1 < s < 2` | off the real axis self-adjointness suffices; on the segment it needs the Fredholm pencil |
| The double pole needs `E(s)` continued pointwise with cusp expansions | a bounded renormalization `G = θ_s² − H` pairs with the `L²` correction; only the explicit scattering of `H` is computed pointwise |

## 8. Tools this programme develops

Unfolding for incomplete and complete cubic Eisenstein series; constant terms on the cusp strip;
the Rankin–Selberg integral of products of automorphic functions with multipliers; renormalization
with coinciding poles; Mellin and contour transfer from the renormalized integral to Dirichlet series
of Fourier coefficients.

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| MetaplecticMobiusDescent | the quotient, its Laplacian, resolvent, Eisenstein series, residue and theta coefficients |
| CoherenceTheoryOfReciprocityFamilies | the consumer: the long columns of the floor bin are first moments of `γ₂²` |
| RHTower (half-weight Rankin–Selberg, Selberg unfoldings) | the same method on `ℍ²` for `SL₂(ℤ)`-type groups |

## 10. Success criteria

1. SQ1 in Lean for incomplete and complete Eisenstein series. (done)
2. The Eisenstein series continued as a function to `Re s > 1` near `4/3`, with growth control.
   (bypassed by the `L²` route)
3. The double pole of `R(θ², s)` at `4/3` with its leading coefficient, unconditionally. (done for `θ_s`)
4. A main term for the smoothed first moment of the squarefree squares, and the consequence for
   CRF's Q1.

## 11. What a contribution must be

- It is a theorem about the actual cubic cover (MMD's objects), not a model.
- It proves an analytic identity or estimate that the next step uses.
- It keeps the multiplier bookkeeping explicit.
- It is unconditional; integrability conditions on the functions it treats are part of the statement.

## 12. Open research topics

1. The contour shift turning the isolated simple pole of the untwisted squarefree series into a
   smoothed first moment, with a controlled remainder.
2. The triple product `∫ θ³` and the next Laurent coefficient of `R(θ², s)`.
3. The products `θ(z) θ(nz)` and their constant terms (the column twists of CRF).
4. Uniformity in the column index (the remainder of the long columns).
