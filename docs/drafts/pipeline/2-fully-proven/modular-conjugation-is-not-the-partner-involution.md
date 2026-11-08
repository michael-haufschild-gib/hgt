# Modular conjugation of the AdS₄ wedge is not the partner involution

- **ID:** modular-conjugation-is-not-the-partner-involution
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../../../reports/review-0811/obstacles-summary.md · §2.7 Q1, §2.10 Q1
- **Statement:** On the `SL₂(ℤ)`-quotient of the AdS₄ Rindler wedge, geometric modular conjugation cannot realize the Eisenstein partner involution on integer sources; abstractly, on any standard-form von Neumann algebra `M` whose Tomita conjugation `J · J` preserves a subalgebra, `J · J` collapses to the Hilbert adjoint `star`, so a standard-form partner realization of the integer Born rule `Q` exists if and only if `RiemannHypothesis` holds.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `CountingHolography/ModularConjugationIsNotThePartnerInvolution.lean`, `lake --old env lean` green, `#print axioms` PASS

## Exact result

1. **Spacelike separation of the AdS₄ Rindler wedges modulo `SL₂(ℤ)`.** Let `X = adsEmbedding t r x y` (`r > 1`, `y > 0`) lie in the right Rindler wedge (`X₃ > |X₄|`) and `X' = wedgeReflect (adsEmbedding t' r' (g • z').re (g • z').im)` lie in the left Rindler wedge (`X₃' < -|X₄'|`) for any `g ∈ SL₂(ℤ)`. Then `ambientForm X X' < -1` and the chordal separation satisfies `ambientForm (X - X') (X - X') > 0`.
2. **Uniqueness of the boost-commuting wedge reflection and KMS period mismatch.** Every real `2 × 2` linear involution commuting with all Rindler boosts `!![cosh τ, sinh τ; sinh τ, cosh τ]` and exchanging the right and left wedges equals `-I₂`, fixing `(t, r)` and `(x, y)`. Moreover, geometric Rindler time is `2πi`-periodic while the arithmetic horizon KMS strip (`kms_condition`) has period `i` (`2π ≠ 1`).
3. **Normalizer rigidity of `PSL₂(ℤ)` in `PGL₂(ℝ)`.** Every `g ∈ GL₂(ℝ)` with `det g = ±1` normalizing `±SL₂(ℤ)` has integer entries (`g ∈ GL₂(ℤ)`), hence decomposes as `γ` or `γ · diag(-1, 1)` with `γ ∈ SL₂(ℤ)`. Every isometry descending to `SL₂(ℤ) \ ℍ` acts on `[x + iy]` as `[±x + iy]`, fixing cusp height `y` identically and preserving every `pseudoEisenstein ψ`; no geometric involution of `SL₂(ℤ) \ AdS₄` exchanges `y ↔ 1/y` or `n ↔ 1/n`.
4. **Non-closure of integer shifts.** For every integer `n ≥ 2`, `-log n ∉ {log m : m ≥ 1}`; closing integer dilations under the partner involution `u ↦ u⁻¹` generates the multiplicative group `ℚ_{>0}`.
5. **Tomita central collapse.** Let `M` be a `VonNeumannAlgebra H` in standard form `(Ω, J)` with `J M J = M'` and natural-cone positivity `Re ⟪Ω, A J A J Ω⟫ ≥ 0` (`A ∈ M`). For every operator `Z ∈ M` whose Tomita conjugate `J Z J` also lies in `M`, one has `Z ∈ M ∩ M'`, `J Z J = Z*`, and `⟪Ω, Z J Z J Ω⟫ = ‖Z Ω‖²`.
6. **Exact classification (graph calibration and `ℤ`).**
   - A nontrivial standard-form von Neumann algebra carries a unital `ℝ`-algebra representation `π : QuadraticAlgebra ℝ (-q) t → M` intertwining `J · J` with the partner involution `star` if and only if `t² ≤ 4q`.
   - Over `ℤ`, there exists a standard-form `VonNeumannAlgebra H` and a multiplicative representation `U : ℚ_{>0} → M` with `J (U r) J = U(r⁻¹)` whose natural-cone form on integer combinations `X_a = ∑_{n=1}^N a_n U(n)` equals `integerProbe N a` (or has Tate limit `integerProbe`) if and only if `RiemannHypothesis` holds. When `RiemannHypothesis` holds, `H = ℓ²({n : c_n > 0})` with diagonal `M = M'` realizes the algebra on the critical-zero spectrum.

## Proof

1. The ambient pairing is `-r r′ ((x-x′)²+y²+y′²)/(2yy′) - √(r²-1)√(r′²-1) cosh(t-t′)`. The hyperbolic factor is at least `1`, `rr′ > 1`, and the second term is nonpositive, so the pairing is strictly below `-1`. Both points have ambient square `-1`; therefore their difference has square `-2 - 2 ambientForm X X′ > 0`.
2. Commutation with the boost at `τ = 1` gives `L = !![a,b;b,a]`. The involution identity gives `a²+b² = 1` and `2ab = 0`; wedge exchange gives `a < 0`. Hence `b = 0`, `a = -1`. Complex hyperbolic sine and cosine have period `2πi`, with `2π ≠ 1`.
3. Conjugating the two elementary unipotents and `ST` shows that all entry squares and pairwise products of `g = !![a,b;c,d]` are integers. Put `A=a²`, `B=b²`, `C=c²`, `D=d²` in `ℕ`. Since `ad-bc = ±1`, the integer squares `AD=(ad)²` and `BC=(bc)²` are coprime. Thus `A,B` are coprime, as are `C,D`; their products `AB=(ab)²` and `CD=(cd)²` are squares. Each factor is consequently a square, so `a,b,c,d` are integers. The determinant splits the matrix into an `SL₂(ℤ)` element or such an element followed by `diag(-1,1)`. Reflection preserves pseudo-Eisenstein series by reindexing `(c,d) ↦ (c,-d)`.
4. For `n ≥ 2`, `log n > 0` while `log m ≥ 0` for `m ≥ 1`, so `-log n ≠ log m`.
5. Since `J A J ∈ M'` iff `A ∈ M`, double commutation `M'' = M` gives `J Z J ∈ M ↔ Z ∈ M'`. Thus `Z ∈ M` and `J Z J ∈ M` place `Z` in the center `M ∩ M'`. Using `⟨ξ, (J Z J) η⟩ = ⟨J η, Z J ξ⟩ = ⟨(J Z* J) ξ, η⟩`, `(J Z J)* = J Z* J`. For self-adjoint `Z = Z* ∈ M ∩ M'`, `D := Z - J Z J ∈ M` satisfies `D* = D` and `J D J = -D`, so `0 ≤ Re ⟪Ω, D J D J Ω⟫ = -⟪Ω, D² Ω⟫ = -‖D Ω‖²`, forcing `D Ω = 0` and `D = 0` by separation. Decomposing general `Z ∈ M ∩ M'` into `(Z + Z*)/2 + i(Z - Z*)/(2i)` gives `J Z J = Z*` and `⟪Ω, Z J Z J Ω⟫ = ⟪Ω, Z Z* Ω⟫ = ‖Z* Ω‖² = ‖Z Ω‖²`.
6. By Tomita central collapse, any `J`-covariant representation into `(M, Ω, J)` becomes a Hilbert `*`-representation (`π(z*) = π(z)*`, `U(r⁻¹) = U(r)*`), reducing positivity of the natural cone to `‖X Ω‖² ≥ 0`. On `QuadraticAlgebra ℝ (-q) t`, evaluating at `Ω ≠ 0` gives `norm_nonneg_iff` (`t² ≤ 4q`). Over `ℤ`, positivity on integer combinations gives `integerProbe N a ≥ 0` (hence `RiemannHypothesis` by `riemannHypothesis_iff_tateLimit_of_count`). Conversely, under `RiemannHypothesis`, `ratCorr_eq_tsum` decomposes `W(B, B(· - log r)) = ∑_{c_n > 0} c_n r^{-i γ_n}` with `c_n > 0` and `∑ c_n < ∞`; taking `H = ℓ²({n : c_n > 0})`, `M` the bounded diagonal operators (`M' = M`), `Ω_n = √c_n`, `(J ψ)_n = conj(ψ_n)`, and `(U(r) ψ)_n = r^{-i γ_n} ψ_n` satisfies every axiom.

## No-go closure
- **Exact killing theorem/mechanism:** Normalizer rigidity of `PSL₂(ℤ)` in `PGL₂(ℝ)` (`normalizer_psl2z_entries_int`) forbids any geometric cusp inversion `y ↦ 1/y` on `SL₂(ℤ) \ AdS₄`, and Tomita central collapse (`tomita_central_eq_star`) forces `J Z J = Z*` on every `J`-stable subalgebra, eliminating modular conjugation as an independent source of positivity beyond Hilbert-space `*`-positivity.
- **Strongest positive survivor:** Complete characterization (`tomita_central_eq_star`, `exists_standardForm_partner_rep_iff_damped`, `riemannHypothesis_iff_exists_standardForm_bornRule`): a standard-form von Neumann algebra realizing the partner involution on rational dilations and Born rule `Q` on integer sources exists if and only if `RiemannHypothesis` holds, and in that realization `M` is abelian on the source algebra with `J U(r) J = U(r)*`.
- **New insight:** Tomita–Takesaki modular theory cannot bypass the count half of a count law: requiring `J · J` to act internally on commutative arithmetic dilations forces those dilations into the center `M ∩ M'`, where natural-cone positivity is literally norm-square positivity `‖X Ω‖² ≥ 0`.
- **Status:** Dependency-closed paper proof complete; formalizing in `CountingHolography/ModularConjugationIsNotThePartnerInvolution.lean`.

## Lean declarations

Module: [ModularConjugationIsNotThePartnerInvolution.lean](../../../../formal/GaloisForLFunctions/CountingHolography/ModularConjugationIsNotThePartnerInvolution.lean). Namespace: `GaloisForLFunctions.CountingHolography`.

| Result | Declarations |
|---|---|
| Wedge geometry | `spacelike_right_left_mod_sl2z`, `rindler_wedge_involution_unique`, `rindler_kms_period_mismatch` |
| Arithmetic symmetries | `normalizer_psl2z_entries_int`, `gl2z_eq_sl2z_or_reflect`, `pseudoEisenstein_reflect_eq`, `integer_shifts_not_partner_closed` |
| Central collapse | `StandardForm.tomita_central_eq_star`, `standardForm_partner_rep_is_central_unitary` |
| Graph criterion | `exists_standardForm_partner_rep_iff_damped` |
| Explicit diagonal construction | `diagVN_commutant_eq`, `diagStandardForm` |
| RH characterizations | `riemannHypothesis_iff_exists_standardForm_bornRule`, `riemannHypothesis_iff_exists_standardForm_tateLimit` |
