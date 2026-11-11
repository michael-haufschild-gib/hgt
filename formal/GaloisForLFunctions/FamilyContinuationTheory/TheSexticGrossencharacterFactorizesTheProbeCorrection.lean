import GaloisForLFunctions.FamilyContinuationTheory.ThePrincipalCorrectionContinuesToTheResiduePoint
import GaloisForLFunctions.HeckeLFunctions.HeckeEulerLogarithmsGiveTheThreeFourOneInequality

/-!
# The sextic Grossencharacter factorizes the probe correction

At every prime `v` of `O = ℤ[ω]` not dividing `λ = ω − 1`, the sixth power of the local probe phase
`κ_v = (π̄_v / |π_v|) η(v)` is independent of the choice of primary generator: since `O` is a
principal ideal domain with unit group `Oˣ` of order `6`, the archimedean sixth-power phase
`ψ₆((a)) = (ā / |a|)⁶` (`a ≠ 0`, `ψ₆(0) = 0`) is unit-invariant and strictly multiplicative on all
integral ideals of `O`. Consequently

`κ_v⁶ = ψ₆(v) · η⁶(v)`   (`primeKappaAt_pow_six`),

and more generally `(conj(π_v / |π_v|) · ψ₆(v)^k η(v))⁶ = ψ₆(v)^{6k + 1} · η⁶(v)` at every step of
the sextic Grossencharacter tower.

Factoring `(1 − A_v N(v)^{3 − 6s})⁻¹` out of `principalLocalFactor` leaves the numerator
`residualLocalFactor`, whose only denominator is `1 − η(v) N(v)^{−s}`. Because
`‖Q⁻¹ R + (1 − Q⁻¹) D‖ < Q⁻¹ + (1 − Q⁻¹) = 1` for every `Q ≥ 2`, `‖A‖, ‖η‖ ≤ 1`, and `Re s ≥ 1/2`,
every local residual factor is holomorphic on `Re s > 0` and nonvanishing on `Re s ≥ 1/2` without
any small-prime norm cutoff, while its local defect on `Re s ≥ σ > 1/2` is
`O(N(v)^{−min(6σ − 2, 1 + σ, 2)})`. Splitting off a finite prime set on each open half-plane
`Re s > σ` (`σ > 1/2`) shows that `fullResidualCorrection` is holomorphic and everywhere
nonvanishing on `Re s > 1/2` and bounded on `Re s ≥ 2` for **every** finite prime set `S`, and
factorizes `fullPrincipalCorrection` on `Re s > 2/3` and `probeCorrection` on `Re s ≥ 7/8`.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped BigOperators Classical ComplexConjugate

namespace GaloisForLFunctions.FamilyContinuationTheory

open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein

local instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

/-! ### The unit-conjugate phase and the sextic ideal Grossencharacter `ψ₆` -/

/-- The normalized conjugate `z̄ / |z|` on `ℂ` (with `0 ↦ 0`), multiplicative on all of `ℂ`. -/
def complexUnitConj : ℂ →*₀ ℂ where
  toFun z := conj z / (‖z‖ : ℂ)
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [map_mul, norm_mul, Complex.ofReal_mul]
    exact div_mul_div_comm _ _ _ _

@[simp]
theorem complexUnitConj_apply (z : ℂ) : complexUnitConj z = conj z / (‖z‖ : ℂ) := rfl

theorem norm_complexUnitConj_of_ne_zero {z : ℂ} (hz : z ≠ 0) : ‖complexUnitConj z‖ = 1 := by
  have hn : (‖z‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [complexUnitConj_apply, norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self hn]

theorem norm_complexUnitConj_le_one (z : ℂ) : ‖complexUnitConj z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · exact (norm_complexUnitConj_of_ne_zero hz).le

/-- The sixth-power archimedean phase `a ↦ (ā / |a|)⁶` on `O = ℤ[ω]`. -/
def elemPsiSix : O →*₀ ℂ :=
  (powMonoidWithZeroHom (M₀ := ℂ) (6 : ℕ) (by decide)).comp
    (complexUnitConj.comp ringComplex.toMonoidWithZeroHom)

theorem elemPsiSix_apply (a : O) : elemPsiSix a = complexUnitConj (ringComplex a) ^ 6 := rfl

theorem elemPsiSix_unit (u : Oˣ) : elemPsiSix (u : O) = 1 := by
  have hu6 : u ^ 6 = 1 := by
    rw [← card_units_thirdCyclotomic K]
    exact pow_card_eq_one'
  have hcoe : (u : O) ^ 6 = 1 := by exact_mod_cast hu6
  calc elemPsiSix (u : O)
      = complexUnitConj (ringComplex ((u : O) ^ 6)) := by
          rw [elemPsiSix_apply, map_pow, map_pow]
    _ = 1 := by rw [hcoe, map_one, map_one]

theorem norm_elemPsiSix_of_ne_zero {a : O} (ha : a ≠ 0) : ‖elemPsiSix a‖ = 1 := by
  have hrc : ringComplex a ≠ 0 := fun h =>
    ha (ringComplex_injective (h.trans ringComplex.map_zero.symm))
  rw [elemPsiSix_apply, norm_pow, norm_complexUnitConj_of_ne_zero hrc, one_pow]

theorem norm_elemPsiSix_le_one (a : O) : ‖elemPsiSix a‖ ≤ 1 := by
  rw [elemPsiSix_apply, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_complexUnitConj_le_one _)

/-- **The sextic archimedean ideal Grossencharacter `ψ₆` on ideals of `O = ℤ[ω]`.** Since `O` is a
PID and `elemPsiSix` is trivial on the six units `Oˣ`, evaluating `elemPsiSix` on a principal
generator is independent of the generator and strictly multiplicative on all ideals of `O`. -/
def idealPsiSix (I : Ideal O) : ℂ :=
  elemPsiSix (Submodule.IsPrincipal.generator I)

theorem idealPsiSix_span_singleton (a : O) : idealPsiSix (Ideal.span {a}) = elemPsiSix a := by
  unfold idealPsiSix
  obtain ⟨u, hu⟩ : Associated (Submodule.IsPrincipal.generator (Ideal.span ({a} : Set O))) a :=
    Ideal.span_singleton_eq_span_singleton.mp (Ideal.span_singleton_generator _)
  rw [← hu, map_mul, elemPsiSix_unit, mul_one]

@[simp]
theorem idealPsiSix_bot : idealPsiSix ⊥ = 0 := by
  rw [← Ideal.span_singleton_zero, idealPsiSix_span_singleton, map_zero]

@[simp]
theorem idealPsiSix_top : idealPsiSix ⊤ = 1 := by
  rw [← Ideal.span_singleton_one, idealPsiSix_span_singleton, map_one]

@[simp]
theorem idealPsiSix_one : idealPsiSix 1 = 1 := idealPsiSix_top

theorem idealPsiSix_mul (I J : Ideal O) : idealPsiSix (I * J) = idealPsiSix I * idealPsiSix J := by
  conv_lhs =>
    rw [← Ideal.span_singleton_generator I, ← Ideal.span_singleton_generator J,
      Ideal.span_singleton_mul_span_singleton, idealPsiSix_span_singleton, map_mul]
  rfl

theorem norm_idealPsiSix_of_ne_bot {I : Ideal O} (hI : I ≠ ⊥) : ‖idealPsiSix I‖ = 1 := by
  have hg : Submodule.IsPrincipal.generator I ≠ 0 := by
    intro h0
    apply hI
    rw [← Ideal.span_singleton_generator I, h0, Ideal.span_singleton_zero]
  exact norm_elemPsiSix_of_ne_zero hg

theorem norm_idealPsiSix_prime (v : HeightOneSpectrum O) : ‖idealPsiSix v.asIdeal‖ = 1 :=
  norm_idealPsiSix_of_ne_bot v.ne_bot

theorem norm_idealPsiSix_le_one (I : Ideal O) : ‖idealPsiSix I‖ ≤ 1 :=
  norm_elemPsiSix_le_one _

/-- Any prime containing `λ = ω − 1` lies over `3` and therefore has norm dividing `9` (`≤ 9`). -/
theorem absNorm_le_nine_of_lambda_mem {v : HeightOneSpectrum O} (hlam : lambda ∈ v.asIdeal) :
    v.asIdeal.absNorm ≤ 9 := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  have hl3 : -omega * (3 : O) = lambda * lambda := by
    dsimp [lambda]
    linear_combination -hrel
  have hmem3 : (3 : O) ∈ v.asIdeal := by
    refine (v.asIdeal.unit_mul_mem_iff_mem neg_omega_isUnit).mp ?_
    rw [hl3]
    exact v.asIdeal.mul_mem_left lambda hlam
  have hdvd : v.asIdeal ∣ Ideal.span ({(3 : O)} : Set O) :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hmem3)
  have hnorm3 : Ideal.absNorm (Ideal.span ({(3 : O)} : Set O)) = 9 := by
    have h9 : Algebra.norm ℤ (3 : O) = 9 := by
      have h3 : (3 : O) = (3 : ℤ) • (1 : O) + (0 : ℤ) • eisEta K := by simp
      rw [h3, algebraNorm_eq_eisNorm K]
      decide
    rw [Ideal.absNorm_span_singleton, h9]
    rfl
  exact Nat.le_of_dvd (by norm_num) (hnorm3 ▸ map_dvd Ideal.absNorm hdvd)

/-! ### Identification of the sixth power of the probe phase -/

/-- Raising a ray class character to a nonzero power `n` raises every extended ideal value to `n`. -/
theorem heckeValue_pow_ne_zero {L : Type*} [Field L] [NumberField L] (𝔪 : Modulus L)
    (ψ : HeckeCharacter 𝔪) {n : ℕ} (hn : n ≠ 0) (I : Ideal (𝓞 L)) :
    heckeValue 𝔪 (ψ ^ n) I = heckeValue 𝔪 ψ I ^ n := by
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    rw [heckeValue_of_mem 𝔪 (ψ ^ n) hI hm, heckeValue_of_mem 𝔪 ψ hI hm,
      MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  · rw [heckeValue_of_not_mem 𝔪 (ψ ^ n) h, heckeValue_of_not_mem 𝔪 ψ h, zero_pow hn]

theorem primeKappa_eq_complexUnitConj_mul (π : O) (ηp : ℂ) :
    primeKappa π ηp = complexUnitConj (ringComplex π) * ηp := by
  unfold primeKappa primeAbs
  rw [map_div₀, Complex.conj_ofReal, complexUnitConj_apply]

/-- At any good prime `v` (`λ ∉ v`), the sixth power of `(π̄_v / |π_v|) · ηp` is `ψ₆(v) · ηp⁶`. -/
theorem primeKappa_primeGen_pow_six {v : HeightOneSpectrum O} (hlam : lambda ∉ v.asIdeal)
    (ηp : ℂ) :
    primeKappa (primeGen v) ηp ^ 6 = idealPsiSix v.asIdeal * ηp ^ 6 := by
  rw [primeKappa_eq_complexUnitConj_mul, mul_pow, ← elemPsiSix_apply,
    ← idealPsiSix_span_singleton, ← (primeGen_spec v hlam).1]

/-- **Sextic Grossencharacter law for the local probe phase.** At every prime `v` of `O` with
`λ ∉ v`, `κ_v⁶ = ψ₆(v) · η⁶(v)`. -/
theorem primeKappaAt_pow_six (𝔪 : Modulus K) (η : HeckeCharacter 𝔪) {v : HeightOneSpectrum O}
    (hlam : lambda ∉ v.asIdeal) :
    primeKappaAt 𝔪 η v ^ 6 = idealPsiSix v.asIdeal * heckeValue 𝔪 (η ^ 6) v.asIdeal := by
  unfold primeKappaAt
  rw [primeKappa_primeGen_pow_six hlam, heckeValue_pow_ne_zero 𝔪 η (by decide : (6 : ℕ) ≠ 0)]

/-- **Tower shift law for the local probe phase.** Replacing `η(v)` by the level-`k` Grossencharacter
value `ψ₆(v)^k · ψ(v)` shifts `(k, ψ)` to `(6k + 1, ψ⁶)`. -/
theorem primeKappa_tower_pow_six (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    {v : HeightOneSpectrum O} (hlam : lambda ∉ v.asIdeal) :
    primeKappa (primeGen v) (idealPsiSix v.asIdeal ^ k * heckeValue 𝔪 ψ v.asIdeal) ^ 6 =
      idealPsiSix v.asIdeal ^ (6 * k + 1) * heckeValue 𝔪 (ψ ^ 6) v.asIdeal := by
  rw [primeKappa_primeGen_pow_six hlam, mul_pow, ← pow_mul, mul_comm k 6,
    heckeValue_pow_ne_zero 𝔪 ψ (by decide : (6 : ℕ) ≠ 0)]
  ring

/-! ### The residual local factor and its cutoff-free nonvanishing on `Re s ≥ 1/2` -/

/-- The residual local factor left after factoring `(1 − A Q^{3 − 6s})⁻¹` out of
`principalLocalFactor`: its only denominator is `1 − η Q^{−s}`. -/
def residualLocalFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  (1 - ((Q : ℂ)⁻¹) ^ 2) *
    (1 - (Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s) - η * (Q : ℂ) ^ (-s)) /
      (1 - η * (Q : ℂ) ^ (-s)))

/-- Exact local factorization `principalLocalFactor = (1 − A Q^{3 − 6s})⁻¹ · residualLocalFactor`. -/
theorem principalLocalFactor_eq_inv_mul_residual (Q : ℝ) (A η s : ℂ) :
    principalLocalFactor Q A η s =
      (1 - A * (Q : ℂ) ^ (3 - 6 * s))⁻¹ * residualLocalFactor Q A η s := by
  unfold principalLocalFactor residualLocalFactor
  rw [div_eq_inv_mul]

/-- Algebraic rewriting of `residualLocalFactor` showing its numerator `1 − (q R + (1 − q) D)`. -/
theorem residualLocalFactor_eq_div {Q : ℝ} {A η s : ℂ} (hD : 1 - η * (Q : ℂ) ^ (-s) ≠ 0) :
    residualLocalFactor Q A η s =
      (1 - ((Q : ℂ)⁻¹) ^ 2) *
        (1 - ((Q : ℂ)⁻¹ * (A * (Q : ℂ) ^ (3 - 6 * s)) +
          (1 - (Q : ℂ)⁻¹) * (η * (Q : ℂ) ^ (-s)))) /
        (1 - η * (Q : ℂ) ^ (-s)) := by
  unfold residualLocalFactor
  generalize (Q : ℂ)⁻¹ = q
  generalize A * (Q : ℂ) ^ (3 - 6 * s) = R
  generalize η * (Q : ℂ) ^ (-s) = D at hD ⊢
  field_simp [hD]
  ring

/-- **Cutoff-free local nonvanishing.** For every `Q ≥ 2`, `‖A‖ ≤ 1`, `‖η‖ ≤ 1`, and `Re s ≥ 1/2`,
`residualLocalFactor Q A η s ≠ 0`. -/
theorem residualLocalFactor_ne_zero {Q : ℝ} (hQ : 2 ≤ Q) {A η s : ℂ} (hA : ‖A‖ ≤ 1)
    (hη : ‖η‖ ≤ 1) (hs : 1 / 2 ≤ s.re) :
    residualLocalFactor Q A η s ≠ 0 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQinv_pos : 0 < Q⁻¹ := inv_pos.mpr hQ0
  have hQinv_le : Q⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hQ0 (by norm_num)]
    linarith
  set q : ℂ := (Q : ℂ)⁻¹
  set R : ℂ := A * (Q : ℂ) ^ (3 - 6 * s)
  set D : ℂ := η * (Q : ℂ) ^ (-s)
  have hq_norm : ‖q‖ = Q⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le]
  have h1q_norm : ‖(1 : ℂ) - q‖ = 1 - Q⁻¹ := by
    have hcast : (1 : ℂ) - q = ((1 - Q⁻¹ : ℝ) : ℂ) := by push_cast [q]; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hD_lt : ‖D‖ < 1 := by
    have h1 : ‖D‖ ≤ Q ^ (-(1 / 2 : ℝ)) := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
        (norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith))
    exact h1.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num))
  have hD_ne : 1 - D ≠ 0 := by
    intro h
    have := norm_sub_norm_le (1 : ℂ) D
    rw [h, norm_zero, norm_one] at this
    linarith
  have hR_le : ‖R‖ ≤ 1 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans ?_
    calc ‖(Q : ℂ) ^ (3 - 6 * s)‖ ≤ Q ^ (0 : ℝ) := by
          refine norm_ofReal_cpow_le hQ1 ?_
          simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
          linarith
      _ = 1 := Real.rpow_zero Q
  have hsum_lt : ‖q * R + (1 - q) * D‖ < 1 := by
    have hqR : ‖q * R‖ ≤ Q⁻¹ := by
      rw [norm_mul, hq_norm]
      exact mul_le_of_le_one_right hQinv_pos.le hR_le
    have h1qD : ‖(1 - q) * D‖ < 1 - Q⁻¹ := by
      rw [norm_mul, h1q_norm]
      exact mul_lt_of_lt_one_right (by linarith) hD_lt
    calc ‖q * R + (1 - q) * D‖ ≤ ‖q * R‖ + ‖(1 - q) * D‖ := norm_add_le _ _
      _ < Q⁻¹ + (1 - Q⁻¹) := add_lt_add_of_le_of_lt hqR h1qD
      _ = 1 := by ring
  have hnum_ne : 1 - (q * R + (1 - q) * D) ≠ 0 := by
    intro h
    have := norm_sub_norm_le (1 : ℂ) (q * R + (1 - q) * D)
    rw [h, norm_zero, norm_one] at this
    linarith
  have hq2_ne : 1 - q ^ 2 ≠ 0 := by
    have hq2 : ‖q ^ 2‖ ≤ 1 / 4 := by
      rw [norm_pow, hq_norm]
      nlinarith
    intro h
    have := norm_sub_norm_le (1 : ℂ) (q ^ 2)
    rw [h, norm_zero, norm_one] at this
    linarith
  rw [residualLocalFactor_eq_div hD_ne]
  exact div_ne_zero (mul_ne_zero hq2_ne hnum_ne) hD_ne

/-- `residualLocalFactor` is holomorphic wherever `1 − η Q^{−s} ≠ 0` (in particular on `Re s > 0`). -/
theorem differentiableAt_residualLocalFactor {Q : ℝ} (hQ : 0 < Q) (A η : ℂ) {s : ℂ}
    (hD : 1 - η * (Q : ℂ) ^ (-s) ≠ 0) :
    DifferentiableAt ℂ (residualLocalFactor Q A η) s := by
  have hQ' : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (-s)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hQ')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => (Q : ℂ) ^ (3 - 6 * s)) s :=
    ((differentiableAt_const 3).sub ((differentiableAt_const 6).mul differentiableAt_id)).const_cpow
      (Or.inl hQ')
  unfold residualLocalFactor
  exact (differentiableAt_const _).mul ((differentiableAt_const 1).sub
    (((differentiableAt_const _).mul ((h2.const_mul A).sub (h1.const_mul η))).div
      ((differentiableAt_const 1).sub (h1.const_mul η)) hD))

/-- Uniform bound `‖residualLocalFactor Q A η s‖ ≤ 4` on `Re s ≥ 2` for every `Q ≥ 2`. -/
theorem norm_residualLocalFactor_le_four {Q : ℝ} (hQ : 2 ≤ Q) {A η s : ℂ} (hA : ‖A‖ ≤ 1)
    (hη : ‖η‖ ≤ 1) (hs : 2 ≤ s.re) :
    ‖residualLocalFactor Q A η s‖ ≤ 4 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  set q : ℂ := (Q : ℂ)⁻¹
  set R : ℂ := A * (Q : ℂ) ^ (3 - 6 * s)
  set D : ℂ := η * (Q : ℂ) ^ (-s)
  have hq : ‖q‖ ≤ 1 / 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, inv_le_comm₀ hQ0 (by norm_num)]
    linarith
  have hD : ‖D‖ ≤ 1 / 2 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hη).trans ?_
    calc ‖(Q : ℂ) ^ (-s)‖ ≤ Q ^ (-(1 : ℝ)) := norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith)
      _ = Q⁻¹ := Real.rpow_neg_one Q
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ hQ0 (by norm_num)]; linarith
  have hR : ‖R‖ ≤ 1 := by
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans ?_
    calc ‖(Q : ℂ) ^ (3 - 6 * s)‖ ≤ Q ^ (0 : ℝ) := by
          refine norm_ofReal_cpow_le hQ1 ?_
          simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
          linarith
      _ = 1 := Real.rpow_zero Q
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at this
    linarith
  have hq2 : ‖1 - q ^ 2‖ ≤ 5 / 4 := by
    calc ‖1 - q ^ 2‖ ≤ 1 + ‖q‖ ^ 2 := by simpa [norm_pow] using norm_sub_le (1 : ℂ) (q ^ 2)
      _ ≤ 5 / 4 := by nlinarith [norm_nonneg q]
  have hmid : ‖1 - q * (R - D) / (1 - D)‖ ≤ 5 / 2 := by
    have hdiv : ‖q * (R - D) / (1 - D)‖ ≤ 3 / 2 := by
      rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
      calc ‖q‖ * ‖R - D‖ ≤ (1 / 2) * (‖R‖ + ‖D‖) :=
            mul_le_mul hq (norm_sub_le R D) (norm_nonneg _) (by norm_num)
        _ ≤ 3 / 4 := by linarith
        _ ≤ 3 / 2 * ‖1 - D‖ := by linarith
    calc ‖1 - q * (R - D) / (1 - D)‖ ≤ 1 + ‖q * (R - D) / (1 - D)‖ := by
          simpa using norm_sub_le (1 : ℂ) (q * (R - D) / (1 - D))
      _ ≤ 5 / 2 := by linarith
  unfold residualLocalFactor
  rw [norm_mul]
  calc ‖1 - q ^ 2‖ * ‖1 - q * (R - D) / (1 - D)‖ ≤ (5 / 4) * (5 / 2) :=
        mul_le_mul hq2 hmid (norm_nonneg _) (by norm_num)
    _ ≤ 4 := by norm_num

/-- **Local defect of the residual factor.** For `Q ≥ 4`, `‖A‖, ‖η‖ ≤ 1`, and `Re s ≥ σ ≥ 1/2`,
`‖residualLocalFactor Q A η s − 1‖ ≤ 9 Q^{−e}` whenever `e ≤ min(6σ − 2, 1 + σ, 2)`. -/
theorem norm_residualLocalFactor_sub_one_le {Q σ e : ℝ} {A η s : ℂ} (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : σ ≤ s.re) (hσ : 1 / 2 ≤ σ) (he6 : e ≤ 6 * σ - 2)
    (heσ : e ≤ 1 + σ) (he2 : e ≤ 2) :
    ‖residualLocalFactor Q A η s - 1‖ ≤ 9 * Q ^ (-e) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  set D := η * (Q : ℂ) ^ (-s)
  set R := A * (Q : ℂ) ^ (3 - 6 * s)
  set q : ℂ := (Q : ℂ)⁻¹
  set T := Q ^ (-e)
  have hq : ‖q‖ = Q ^ (-1 : ℝ) := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hQ0.le, Real.rpow_neg_one]
  have hD : ‖D‖ ≤ Q ^ (-σ) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hη).trans
      (norm_ofReal_cpow_le hQ1 (by rw [neg_re]; linarith))
  have hDh : ‖D‖ ≤ 1 / 2 := hD.trans (rpow_le_half_of_four_le hQ (by linarith))
  have h1D : 1 / 2 ≤ ‖1 - D‖ := by
    have := norm_sub_norm_le (1 : ℂ) D
    rw [norm_one] at this
    linarith
  have hq2 : ‖q‖ ^ 2 ≤ T := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num; linarith)
  have hqR : ‖q‖ * ‖R‖ ≤ T := by
    have hR : ‖R‖ ≤ Q ^ (3 - 6 * σ) := by
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) hA).trans (norm_ofReal_cpow_le hQ1 ?_)
      simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      linarith
    rw [hq]
    calc Q ^ (-1 : ℝ) * ‖R‖ ≤ Q ^ (-1 : ℝ) * Q ^ (3 - 6 * σ) :=
          mul_le_mul_of_nonneg_left hR (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 + (3 - 6 * σ)) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hqD : ‖q‖ * ‖D‖ ≤ T := by
    rw [hq]
    calc Q ^ (-1 : ℝ) * ‖D‖ ≤ Q ^ (-1 : ℝ) * Q ^ (-σ) :=
          mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (-1 + -σ) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have ha : ‖q * (R - D) / (1 - D)‖ ≤ 4 * T := by
    rw [norm_div, norm_mul, div_le_iff₀ (by linarith)]
    calc ‖q‖ * ‖R - D‖ ≤ ‖q‖ * (‖R‖ + ‖D‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ = ‖q‖ * ‖R‖ + ‖q‖ * ‖D‖ := by ring
      _ ≤ T + T := add_le_add hqR hqD
      _ ≤ 4 * T * ‖1 - D‖ := by nlinarith [Real.rpow_nonneg hQ0.le (-e)]
  have hq2' : ‖1 - q ^ 2‖ ≤ 2 := by
    have hq_le : ‖q‖ ≤ 1 := by
      rw [hq, Real.rpow_neg_one]
      exact inv_le_one_of_one_le₀ hQ1
    have h := norm_sub_le (1 : ℂ) (q ^ 2)
    rw [norm_one, norm_pow] at h
    nlinarith [norm_nonneg q]
  have hid : residualLocalFactor Q A η s - 1 =
      -(q ^ 2) - (1 - q ^ 2) * (q * (R - D) / (1 - D)) := by
    unfold residualLocalFactor
    ring
  rw [hid]
  calc ‖-(q ^ 2) - (1 - q ^ 2) * (q * (R - D) / (1 - D))‖
      ≤ ‖q ^ 2‖ + ‖(1 - q ^ 2) * (q * (R - D) / (1 - D))‖ := by
        simpa [norm_neg] using norm_sub_le (-(q ^ 2)) ((1 - q ^ 2) * (q * (R - D) / (1 - D)))
    _ ≤ T + 2 * (4 * T) := by
        rw [norm_pow, norm_mul]
        exact add_le_add hq2 (mul_le_mul hq2' ha (norm_nonneg _) (by norm_num))
    _ = 9 * T := by ring

/-! ### Cutoff-free holomorphy and nonvanishing of the residual Euler product on `Re s > 1/2` -/

/-- Splitting any infinite product at a finite set once its complement is multipliable. -/
theorem tprod_eq_finset_prod_mul_compl {ι : Type*} {f : ι → ℂ} (T : Finset ι)
    (hsub : Multipliable fun i : {i : ι // i ∈ (↑T : Set ι)ᶜ} => f i.1) :
    ∏' i, f i = (∏ i ∈ T, f i) * ∏' i : {i : ι // i ∈ (↑T : Set ι)ᶜ}, f i.1 := by
  have hfin : HasProd (fun i : {i : ι // i ∈ (↑T : Set ι)} => f i.1) (∏ i ∈ T, f i) := by
    have hft := hasProd_fintype (fun i : {i : ι // i ∈ (↑T : Set ι)} => f i.1)
    rwa [Finset.prod_coe_sort T f] at hft
  exact (HasProd.mul_compl hfin hsub.hasProd).tprod_eq

section ResidualProduct

variable {L : Type*} [Field L] [NumberField L]

/-- The residual Euler product `∏_{v ∉ S} residualLocalFactor N(v) A(v) η(v) s`. -/
def residualCorrection (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
    residualLocalFactor (primeNorm v.1) (A v.1) (η v.1) s

/-- The residual defect exponent `min(6σ − 2, 1 + σ, 2)`, which exceeds `1` for every `σ > 1/2`. -/
def residualDefectExponent (σ : ℝ) : ℝ := min (6 * σ - 2) (min (1 + σ) 2)

theorem one_lt_residualDefectExponent {σ : ℝ} (hσ : 1 / 2 < σ) :
    1 < residualDefectExponent σ :=
  lt_min (by linarith) (lt_min (by linarith) (by norm_num))

/-- The summable residual defect majorant `9 N(v)^{−e}`. -/
def residualDefectWeight (e : ℝ) (v : HeightOneSpectrum (𝓞 L)) : ℝ :=
  9 * primeNorm v ^ (-e)

theorem residualDefectWeight_nonneg (e : ℝ) (v : HeightOneSpectrum (𝓞 L)) :
    0 ≤ residualDefectWeight e v :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith [two_le_primeNorm v]) _)

private theorem residual_denominator_ne_zero {η : ℂ} (hη : ‖η‖ ≤ 1)
    (v : HeightOneSpectrum (𝓞 L)) {s : ℂ} (hs : 0 < s.re) :
    1 - η * (primeNorm v : ℂ) ^ (-s) ≠ 0 := by
  have hv := two_le_primeNorm v
  have hlt : ‖η * (primeNorm v : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact ((mul_le_of_le_one_left (norm_nonneg _) hη).trans
      (norm_ofReal_cpow_le (by linarith) (a := -s.re) (by rw [neg_re]))).trans_lt
      (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith))
  intro h
  have := norm_sub_norm_le (1 : ℂ) (η * (primeNorm v : ℂ) ^ (-s))
  rw [h, norm_zero, norm_one] at this
  linarith

/-- On each half-plane `Re s > σ` (`σ > 1/2`), `residualCorrection A η S` is holomorphic,
everywhere nonvanishing, multipliable at every point, and bounded on `Re s ≥ 2`, with **no**
norm cutoff on `S`. -/
theorem differentiableOn_and_ne_zero_residualCorrection_gt {σ : ℝ} (hσ : 1 / 2 < σ)
    (A η : HeightOneSpectrum (𝓞 L) → ℂ) (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    DifferentiableOn ℂ (residualCorrection A η S) {s : ℂ | σ < s.re} ∧
      (∀ s : ℂ, σ < s.re → residualCorrection A η S s ≠ 0) ∧
      (∀ s : ℂ, σ < s.re → Multipliable fun v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S} =>
        residualLocalFactor (primeNorm v.1) (A v.1) (η v.1) s) ∧
      (σ < 2 → ∃ M : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖residualCorrection A η S s‖ ≤ M) := by
  set e := residualDefectExponent σ
  have he1 : 1 < e := one_lt_residualDefectExponent hσ
  have he6 : e ≤ 6 * σ - 2 := min_le_left _ _
  have heσ : e ≤ 1 + σ := (min_le_right _ _).trans (min_le_left _ _)
  have he2 : e ≤ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hB : Summable (residualDefectWeight (L := L) e) :=
    (numberField_summable_finitePlace_absNorm_rpow (K := L) he1).mul_left 9
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero
    (residualDefectWeight (L := L) e))).2 (1 / 6) (by norm_num)).exists
  let ι := {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
  let T : Finset ι := F.subtype fun v => v ∉ S
  have hnotF : ∀ i : {i : ι // i ∈ (↑T : Set ι)ᶜ}, i.1.1 ∉ F := by
    intro i hiF
    apply i.2
    exact Finset.mem_coe.mpr (Finset.mem_subtype.mpr hiF)
  have hBF : Summable fun v : {v : HeightOneSpectrum (𝓞 L) // v ∉ F} =>
      residualDefectWeight e v.1 := hB.comp_injective Subtype.val_injective
  have hinj : Function.Injective fun i : {i : ι // i ∈ (↑T : Set ι)ᶜ} =>
      (⟨i.1.1, hnotF i⟩ : {v : HeightOneSpectrum (𝓞 L) // v ∉ F}) :=
    fun i j h => Subtype.ext (Subtype.ext (congrArg Subtype.val h))
  have hBTc : Summable fun i : {i : ι // i ∈ (↑T : Set ι)ᶜ} => residualDefectWeight e i.1.1 :=
    hBF.comp_injective hinj
  have hsmall : ∑' i : {i : ι // i ∈ (↑T : Set ι)ᶜ}, residualDefectWeight e i.1.1 ≤ 1 / 6 :=
    (Summable.tsum_le_tsum_of_inj _ hinj (fun _ _ => residualDefectWeight_nonneg e _)
      (fun _ => le_rfl) hBTc hBF).trans hF.le
  have hfour : ∀ i : {i : ι // i ∈ (↑T : Set ι)ᶜ}, 4 ≤ primeNorm i.1.1 := by
    intro i
    by_contra hlt
    have hv_le3 : primeNorm i.1.1 ≤ 3 := by
      have hnat : i.1.1.asIdeal.absNorm < 4 := by
        unfold primeNorm at hlt
        exact_mod_cast not_le.mp hlt
      unfold primeNorm
      exact_mod_cast Nat.le_of_lt_succ hnat
    have hv2 := two_le_primeNorm i.1.1
    have hpow : primeNorm i.1.1 ^ e ≤ 9 := by
      calc primeNorm i.1.1 ^ e ≤ primeNorm i.1.1 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) he2
        _ ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow (by linarith) hv_le3 (by norm_num)
        _ = 9 := by norm_num
    have hge1 : 1 ≤ residualDefectWeight e i.1.1 := by
      unfold residualDefectWeight
      rw [Real.rpow_neg (by linarith)]
      have hpos : 0 < primeNorm i.1.1 ^ e := Real.rpow_pos_of_pos (by linarith) e
      rw [← div_eq_mul_inv, one_le_div hpos]
      exact hpow
    have hle_sixth : residualDefectWeight e i.1.1 ≤ 1 / 6 :=
      (Summable.le_tsum hBTc i fun j _ => residualDefectWeight_nonneg e j.1.1).trans hsmall
    linarith
  have hhalf : ∀ i : {i : ι // i ∈ (↑T : Set ι)ᶜ}, residualDefectWeight e i.1.1 ≤ 1 / 2 :=
    fun i => (Summable.le_tsum hBTc i fun j _ => residualDefectWeight_nonneg e j.1.1).trans
      (hsmall.trans (by norm_num))
  set U : Set ℂ := {s : ℂ | σ < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hdef : ∀ (i : {i : ι // i ∈ (↑T : Set ι)ᶜ}), ∀ s ∈ U,
      ‖residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s - 1‖ ≤
        residualDefectWeight e i.1.1 :=
    fun i s hs => norm_residualLocalFactor_sub_one_le (hfour i) (hA i.1.1) (hη i.1.1)
      (le_of_lt hs) hσ.le he6 heσ he2
  obtain ⟨hdiff_tail, hrep_tail⟩ := hasProd_and_bounds_of_defect
    (f := fun (i : {i : ι // i ∈ (↑T : Set ι)ᶜ}) s =>
      residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)
    (b := fun i => residualDefectWeight e i.1.1) hU hBTc
    (fun i s hs => by
      have hs0 : 0 < s.re := by have : σ < s.re := hs; linarith
      exact (differentiableAt_residualLocalFactor (by linarith [two_le_primeNorm i.1.1]) _ _
        (residual_denominator_ne_zero (hη i.1.1) i.1.1 hs0)).differentiableWithinAt)
    hdef hhalf
  have hmul_tail : ∀ s ∈ U, Multipliable fun i : {i : ι // i ∈ (↑T : Set ι)ᶜ} =>
      residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s := by
    intro s hs
    have hsum : Summable fun i : {i : ι // i ∈ (↑T : Set ι)ᶜ} =>
        residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s - 1 :=
      (hBTc.of_nonneg_of_le (fun _ => norm_nonneg _) fun i => hdef i s hs).of_norm
    exact (Complex.multipliable_one_add_of_summable hsum).congr fun _ => by ring
  have hsplit : ∀ s ∈ U, residualCorrection A η S s =
      (∏ i ∈ T, residualLocalFactor (primeNorm i.1) (A i.1) (η i.1) s) *
        ∏' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
          residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s :=
    fun s hs => tprod_eq_finset_prod_mul_compl T (hmul_tail s hs)
  have hdiff_fin : DifferentiableOn ℂ
      (fun s => ∏ i ∈ T, residualLocalFactor (primeNorm i.1) (A i.1) (η i.1) s) U := by
    refine DifferentiableOn.fun_finsetProd fun i _ s hs => ?_
    have hs0 : 0 < s.re := by have : σ < s.re := hs; linarith
    exact (differentiableAt_residualLocalFactor (by linarith [two_le_primeNorm i.1]) _ _
      (residual_denominator_ne_zero (hη i.1) i.1 hs0)).differentiableWithinAt
  refine ⟨(hdiff_fin.mul hdiff_tail).congr hsplit, fun s hs => ?_, fun s hs => ?_, fun hσ2 => ?_⟩
  · rw [hsplit s hs]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) ?_
    · exact residualLocalFactor_ne_zero (two_le_primeNorm i.1) (hA i.1) (hη i.1)
        (by have : σ < s.re := hs; linarith)
    · rw [(hrep_tail s hs).1]
      exact Complex.exp_ne_zero _
  · have hfin : HasProd (fun i : {i : ι // i ∈ (↑T : Set ι)} =>
        residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)
        (∏ i ∈ T, residualLocalFactor (primeNorm i.1) (A i.1) (η i.1) s) := by
      have hft := hasProd_fintype (fun i : {i : ι // i ∈ (↑T : Set ι)} =>
        residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)
      rwa [Finset.prod_coe_sort T _] at hft
    exact ⟨_, HasProd.mul_compl hfin (hmul_tail s hs).hasProd⟩
  · refine ⟨4 ^ T.card * (3 / 2), fun s hs => ?_⟩
    have hsU : s ∈ U := by show σ < s.re; linarith
    rw [hsplit s hsU, norm_mul]
    have hfin_le : ‖∏ i ∈ T, residualLocalFactor (primeNorm i.1) (A i.1) (η i.1) s‖ ≤
        4 ^ T.card := by
      refine (Finset.norm_prod_le _ _).trans ?_
      calc ∏ i ∈ T, ‖residualLocalFactor (primeNorm i.1) (A i.1) (η i.1) s‖
          ≤ ∏ _i ∈ T, (4 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
            norm_residualLocalFactor_le_four (two_le_primeNorm i.1) (hA i.1) (hη i.1) hs
        _ = 4 ^ T.card := Finset.prod_const _
    have htail_le : ‖∏' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
        residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s‖ ≤ 3 / 2 := by
      obtain ⟨hexp, hlog⟩ := hrep_tail s hsU
      have hz : ‖∑' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
          Complex.log (residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)‖ ≤ 1 / 4 :=
        hlog.trans (by linarith)
      have hsub1 : ‖cexp (∑' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
          Complex.log (residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)) - 1‖ ≤
            1 / 2 := by
        calc _ ≤ 2 * ‖∑' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
              Complex.log (residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s)‖ :=
              Complex.norm_exp_sub_one_le (hz.trans (by norm_num))
          _ ≤ 1 / 2 := by linarith
      rw [hexp]
      have htri := norm_sub_norm_le (cexp (∑' i : {i : ι // i ∈ (↑T : Set ι)ᶜ},
        Complex.log (residualLocalFactor (primeNorm i.1.1) (A i.1.1) (η i.1.1) s))) 1
      rw [norm_one] at htri
      linarith
    exact mul_le_mul hfin_le htail_le (norm_nonneg _) (by positivity)

/-- **Cutoff-free holomorphy of `residualCorrection` on all of `Re s > 1/2`.** -/
theorem differentiableOn_residualCorrection (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 L))) :
    DifferentiableOn ℂ (residualCorrection A η S) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 1 / 2 < s₀.re := hs₀
  set σ : ℝ := (1 / 2 + s₀.re) / 2
  have hσ : 1 / 2 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s₀.re := by dsimp [σ]; linarith
  have hopen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const continuous_re
  have hd := (differentiableOn_and_ne_zero_residualCorrection_gt hσ A η hA hη S).1
  exact (hd.differentiableAt (hopen.mem_nhds hsσ)).differentiableWithinAt

/-- **Cutoff-free nonvanishing of `residualCorrection` on all of `Re s > 1/2`.** -/
theorem residualCorrection_ne_zero (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    residualCorrection A η S s ≠ 0 := by
  set σ : ℝ := (1 / 2 + s.re) / 2
  exact (differentiableOn_and_ne_zero_residualCorrection_gt (σ := σ) (by dsimp [σ]; linarith)
    A η hA hη S).2.1 s (by dsimp [σ]; linarith)

/-- Multipliability of the residual local factors at every point of `Re s > 1/2`. -/
theorem multipliable_residualCorrection (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S} =>
      residualLocalFactor (primeNorm v.1) (A v.1) (η v.1) s := by
  set σ : ℝ := (1 / 2 + s.re) / 2
  exact (differentiableOn_and_ne_zero_residualCorrection_gt (σ := σ) (by dsimp [σ]; linarith)
    A η hA hη S).2.2.1 s (by dsimp [σ]; linarith)

/-- Uniform boundedness of `residualCorrection` on `Re s ≥ 2` for every finite prime set `S`. -/
theorem exists_norm_residualCorrection_le (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ M : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖residualCorrection A η S s‖ ≤ M :=
  (differentiableOn_and_ne_zero_residualCorrection_gt (σ := 1) (by norm_num)
    A η hA hη S).2.2.2 (by norm_num)

/-- **The full residual correction** `residualCorrection · deletedEulerFactors` attached to a ray
class character `ψ` and phases `A`. -/
def fullResidualCorrection (𝔪 : Modulus L) (ψ : HeckeCharacter 𝔪)
    (A : HeightOneSpectrum (𝓞 L) → ℂ) (S : Finset (HeightOneSpectrum (𝓞 L))) (s : ℂ) : ℂ :=
  residualCorrection A (fun v => heckeValue 𝔪 ψ v.asIdeal) S s * deletedEulerFactors 𝔪 ψ S s

/-- **Cutoff-free analytic package for `fullResidualCorrection`.** For **every** finite prime set
`S`, `fullResidualCorrection 𝔪 ψ A S` is holomorphic and everywhere nonvanishing on `Re s > 1/2`
and uniformly bounded on `Re s ≥ 2`. -/
theorem fullResidualCorrection_properties (𝔪 : Modulus L) (ψ : HeckeCharacter 𝔪)
    (A : HeightOneSpectrum (𝓞 L) → ℂ) (hA : ∀ v, ‖A v‖ ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 L))) :
    DifferentiableOn ℂ (fullResidualCorrection 𝔪 ψ A S) {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 / 2 < s.re → fullResidualCorrection 𝔪 ψ A S s ≠ 0) ∧
      ∃ M : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖fullResidualCorrection 𝔪 ψ A S s‖ ≤ M := by
  have hη : ∀ v : HeightOneSpectrum (𝓞 L), ‖heckeValue 𝔪 ψ v.asIdeal‖ ≤ 1 :=
    fun v => norm_heckeValue_le_one 𝔪 ψ _
  have hsub : {s : ℂ | 1 / 2 < s.re} ⊆ {s : ℂ | 0 < s.re} := fun s hs => by
    simp only [Set.mem_setOf_eq] at hs ⊢; linarith
  refine ⟨(differentiableOn_residualCorrection A _ hA hη S).mul
      ((differentiableOn_deletedEulerFactors 𝔪 ψ S).mono hsub),
    fun s hs => mul_ne_zero (residualCorrection_ne_zero A _ hA hη S hs)
      (Finset.prod_ne_zero_iff.mpr fun v _ =>
        inv_ne_zero (deletedTerm_denominator_ne_zero 𝔪 ψ v (hsub hs))), ?_⟩
  obtain ⟨M₀, hM₀⟩ := exists_norm_residualCorrection_le A _ hA hη S
  refine ⟨max M₀ 0 * (4 / 3) ^ S.card, fun s hs => ?_⟩
  unfold fullResidualCorrection
  rw [norm_mul]
  have hdel : ‖deletedEulerFactors 𝔪 ψ S s‖ ≤ (4 / 3) ^ S.card := by
    unfold deletedEulerFactors
    refine (Finset.norm_prod_le _ _).trans ?_
    calc ∏ v ∈ S, ‖(1 - heckeValue 𝔪 ψ v.asIdeal * (primeNorm v : ℂ) ^ (-s))⁻¹‖
        ≤ ∏ _v ∈ S, (4 / 3 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            fun v _ => norm_deletedEulerFactor_le 𝔪 ψ v hs
      _ = (4 / 3) ^ S.card := Finset.prod_const _
  exact mul_le_mul ((hM₀ s hs).trans (le_max_left _ _)) hdel (norm_nonneg _) (le_max_right _ _)

/-- **Exact Euler-product factorization on `Re s > 2/3`.** For every finite prime set `S`, on
`Re s > 2/3` the principal correction splits into the inverse-linear Euler product in `3 − 6s`
times `residualCorrection`. -/
theorem principalCorrection_eq_euler_mul_residual (A η : HeightOneSpectrum (𝓞 L) → ℂ)
    (hA : ∀ v, ‖A v‖ ≤ 1) (hη : ∀ v, ‖η v‖ ≤ 1) (S : Finset (HeightOneSpectrum (𝓞 L)))
    {s : ℂ} (hs : 2 / 3 < s.re) :
    principalCorrection A η S s =
      (∏' v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        (1 - A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s))⁻¹) *
        residualCorrection A η S s := by
  have heuler : Multipliable fun v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S} =>
      (1 - A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s))⁻¹ := by
    have hexp : 1 < 6 * s.re - 3 := by linarith
    have hmaj : Summable fun v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S} =>
        primeNorm v.1 ^ (-(6 * s.re - 3)) :=
      (numberField_summable_finitePlace_absNorm_rpow (K := L) hexp).subtype _
    have hbd : ∀ v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        ‖A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s)‖ ≤ primeNorm v.1 ^ (-(6 * s.re - 3)) := by
      intro v
      have hv1 : 1 ≤ primeNorm v.1 := by linarith [two_le_primeNorm v.1]
      rw [norm_mul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (hA v.1)).trans (norm_ofReal_cpow_le hv1 ?_)
      simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      linarith
    refine multipliable_one_sub_inv
      (hmaj.of_nonneg_of_le (fun _ => norm_nonneg _) hbd) fun v => (hbd v).trans ?_
    have hv2 := two_le_primeNorm v.1
    calc primeNorm v.1 ^ (-(6 * s.re - 3)) ≤ primeNorm v.1 ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (primeNorm v.1)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hres := multipliable_residualCorrection A η hA hη S (by linarith : 1 / 2 < s.re)
  unfold principalCorrection residualCorrection
  rw [← heuler.tprod_mul hres]
  exact tprod_congr fun v => principalLocalFactor_eq_inv_mul_residual _ _ _ _

/-- Exact factorization of `fullPrincipalCorrection` on `Re s > 2/3` for every finite `S`. -/
theorem fullPrincipalCorrection_eq_euler_mul_residual (𝔪 : Modulus L) (ψ : HeckeCharacter 𝔪)
    (A : HeightOneSpectrum (𝓞 L) → ℂ) (hA : ∀ v, ‖A v‖ ≤ 1)
    (S : Finset (HeightOneSpectrum (𝓞 L))) {s : ℂ} (hs : 2 / 3 < s.re) :
    fullPrincipalCorrection 𝔪 ψ A S s =
      (∏' v : {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
        (1 - A v.1 * (primeNorm v.1 : ℂ) ^ (3 - 6 * s))⁻¹) *
        fullResidualCorrection 𝔪 ψ A S s := by
  unfold fullPrincipalCorrection fullResidualCorrection
  rw [principalCorrection_eq_euler_mul_residual A _ hA (fun _ => norm_heckeValue_le_one 𝔪 ψ _) S hs,
    mul_assoc]

end ResidualProduct

/-! ### Specialization to the Eisenstein probe and its Grossencharacter Euler product -/

/-- The `S`-deleted Euler product of the Grossencharacter `ψ₆^k ψ` modulo `𝔪` on `Re w > 1`:
`∏_{v ∉ S} (1 − ψ₆(v)^k ψ(v) N(v)^{−w})⁻¹`. -/
def grossenEulerProductModS (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (k : ℕ)
    (S : Finset (HeightOneSpectrum O)) (w : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum O // v ∉ S},
    (1 - idealPsiSix v.1.asIdeal ^ k * heckeValue 𝔪 ψ v.1.asIdeal * (primeNorm v.1 : ℂ) ^ (-w))⁻¹

/-- **Exact factorization of the probe's full principal correction on `Re s > 2/3`.** Whenever `S`
contains the ramified prime above `3`, `fullPrincipalCorrection` with phases `κ_v⁶` factors on
`Re s > 2/3` as `L_{𝔪}^S(6s − 3, ψ₆ η⁶)` times `fullResidualCorrection`. -/
theorem fullPrincipalCorrection_probe_eq_grossen_mul_residual (𝔪 : Modulus K)
    (η : HeckeCharacter 𝔪) (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S) {s : ℂ} (hs : 2 / 3 < s.re) :
    fullPrincipalCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s =
      grossenEulerProductModS 𝔪 (η ^ 6) 1 S (6 * s - 3) *
        fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s := by
  have hA : ∀ v, ‖primeKappaAt 𝔪 η v ^ 6‖ ≤ 1 := fun v => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_primeKappaAt_le 𝔪 η v)
  rw [fullPrincipalCorrection_eq_euler_mul_residual 𝔪 η _ hA S hs]
  congr 1
  unfold grossenEulerProductModS
  refine tprod_congr fun v => ?_
  have hlam : lambda ∉ v.1.asIdeal := fun h => v.2 (hS v.1 h)
  rw [primeKappaAt_pow_six 𝔪 η hlam, pow_one, show (3 - 6 * s : ℂ) = -(6 * s - 3) by ring]

/-- **Exact factorization of `probeCorrection` on `Re s ≥ 7/8`.** For any `S` containing the primes
of norm `≤ 160` (which automatically includes the prime above `3`),
`probeCorrection 𝔪 η S s = L_{𝔪}^S(6s − 3, ψ₆ η⁶) · fullResidualCorrection 𝔪 η (κ_v⁶) S s`. -/
theorem probeCorrection_eq_grossen_mul_residual (𝔪 : Modulus K) (η : HeckeCharacter 𝔪)
    (S : Finset (HeightOneSpectrum O))
    (hS : ∀ v : HeightOneSpectrum O, v.asIdeal.absNorm ≤ 160 → v ∈ S) {s : ℂ}
    (hs : 7 / 8 ≤ s.re) :
    probeCorrection 𝔪 η S s =
      grossenEulerProductModS 𝔪 (η ^ 6) 1 S (6 * s - 3) *
        fullResidualCorrection 𝔪 η (fun v => primeKappaAt 𝔪 η v ^ 6) S s := by
  have hlamS : ∀ v : HeightOneSpectrum O, lambda ∈ v.asIdeal → v ∈ S :=
    fun v hv => hS v ((absNorm_le_nine_of_lambda_mem hv).trans (by norm_num))
  rw [probeCorrection_eq 𝔪 η S hS hs]
  exact fullPrincipalCorrection_probe_eq_grossen_mul_residual 𝔪 η S hlamS (by linarith)

end GaloisForLFunctions.FamilyContinuationTheory
