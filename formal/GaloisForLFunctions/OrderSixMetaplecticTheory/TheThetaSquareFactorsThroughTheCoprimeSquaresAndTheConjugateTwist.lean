import GaloisForLFunctions.OrderSixMetaplecticTheory.TheConjugateCubicTwistAndTheCoprimeSquaresShareTheDoublePole

/-!
# The theta square factors through the q-coprime squares and the conjugate twist

Patterson's relations at an odd primary prime q (ρ = |q|, t = ρ^{−s}): T(xq³) = ρT(x), T(xq²) = 0 for q ∤ x. Splitting
the squared theta series D(s) = Σ T(h)²(4π|ξ_h|)^{−s} by v_q(h) ∈ {0}, {1}, {2}, [3, ∞) gives (`thetaSq_euler`)

(1 − ρ²t³) D(s) = D_{cop}(s) + t D_q(s),   D_q(s) = Σ_{q∤x} T(xq)²(4π|ξ_x|)^{−s}.

With T(xq) = g₂(9x)T(x)/ρ and the Gauss-sum shifts g(x) = χ(x)⁻¹g₁, g₂(9x) = χ²(9x)⁻¹g₂, one has
g₁ g₂(9x)² = χ(9)⁻¹g₂² g(x) (`gauss_sq_shift`), so g₁D_q = ρ⁻²χ(9)⁻¹g₂² D_g (`gaussDirichlet_pCoeff`): the q-divisible
part of θ² is the **conjugate twist**. The Gauss sums have |g₁| = |g₂| = ρ and N(q) = ρ² (`norm_gaussAt_one`, `card_res_eq`).
-/

noncomputable section

open Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Gauss sums at shifted frequencies -/

/-- g₂(h) = Σ_u χ²(u)ψ(uh). -/
def gaussAt2 (h : O) : ℂ := ∑ u : P.Res, (P.chi ^ 2) u * P.traceChar (u * P.res h)

theorem mulChar_inv_apply (χ' : MulChar P.Res ℂ) (a : P.Res) (ha : a ≠ 0) : χ' a⁻¹ = (χ' a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel₀ ha, MulChar.map_one])

theorem sum_mulChar_shift (χ' : MulChar P.Res ℂ) (a c : P.Res) (ha : a ≠ 0) :
    ∑ u : P.Res, χ' u * P.traceChar (u * (a * c)) = (χ' a)⁻¹ * ∑ u : P.Res, χ' u * P.traceChar (u * c) := by
  rw [← (mulRight_bijective₀ a⁻¹ (inv_ne_zero ha)).sum_comp (fun u => χ' u * P.traceChar (u * (a * c))),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, P.mulChar_inv_apply χ' a ha, show v * a⁻¹ * (a * c) = v * c by field_simp]
  ring

/-- g(h) = χ(h)⁻¹g₁ (both sides vanish when q ∣ h). -/
theorem gaussAt_eq (h : O) : P.gaussAt h = (P.chi (P.res h))⁻¹ * P.gaussAt 1 := by
  by_cases hh : P.res h = 0
  · rw [hh, MulChar.map_zero, inv_zero, zero_mul, gaussAt, hh]
    simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one P.chi_ne_one
  · have := P.sum_mulChar_shift P.chi (P.res h) 1 hh
    simp only [mul_one] at this
    simp only [gaussAt, map_one, mul_one]
    exact this

/-- g₂(9h) = χ²(9h)⁻¹g₂ for q ∤ h. -/
theorem gaussAt2_eq (h : O) (hh : ¬ P.p ∣ h) :
    P.gaussAt2 (9 * h) = ((P.chi ^ 2) (9 * P.res h))⁻¹ * P.gaussAt2 1 := by
  have hx : P.res h ≠ 0 := fun h0 => hh ((P.res_eq_zero_iff h).mp h0)
  have ha : (9 : P.Res) * P.res h ≠ 0 := mul_ne_zero P.nine_ne_zero' hx
  have := P.sum_mulChar_shift (P.chi ^ 2) (9 * P.res h) 1 ha
  simp only [mul_one] at this
  simp only [gaussAt2, map_one, mul_one]
  rw [show P.res (9 * h) = 9 * P.res h by rw [map_mul, map_ofNat]]
  exact this

/-- **The square shift.** g₁ g₂(9h)² = χ(9)⁻¹g₂² g(h) for q ∤ h. -/
theorem gauss_sq_shift (h : O) (hh : ¬ P.p ∣ h) :
    P.gaussAt 1 * P.gaussAt2 (9 * h) ^ 2 = (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * P.gaussAt h := by
  have hx : P.res h ≠ 0 := fun h0 => hh ((P.res_eq_zero_iff h).mp h0)
  have h9 := P.nine_ne_zero'
  have hA := P.chi_cube 9 h9
  have hB := P.chi_cube (P.res h) hx
  rw [P.gaussAt2_eq h hh, P.gaussAt_eq h, MulChar.pow_apply' _ (by norm_num), map_mul, P.chi_inv_eq_sq 9 h9,
    P.chi_inv_eq_sq _ hx]
  have e : ((P.chi 9 * P.chi (P.res h)) ^ 2)⁻¹ = P.chi 9 * P.chi (P.res h) := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (P.chi (P.res h) ^ 3) * hA + hB
  rw [e]
  ring

/-! ### Norms -/

theorem card_res_eq : (Fintype.card P.Res : ℝ) = ‖ringComplex P.p‖ ^ 2 := by
  have h : Fintype.card P.Res = Ideal.absNorm (Ideal.span {P.p}) := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [ringComplex_norm_sq_eq_absNorm_span, h]

theorem norm_gaussSum_traceChar (χ' : MulChar P.Res ℂ) (hχ : χ' ≠ 1) :
    ‖gaussSum χ' P.traceChar‖ = ‖ringComplex P.p‖ := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (principalTraceChar_primitive P.p P.ne_zero)
  rw [← star_gaussSum_eq] at h
  have hn : (‖gaussSum χ' P.traceChar‖ : ℂ) ^ 2 = (Fintype.card P.Res : ℂ) := by
    rw [← Complex.conj_mul', mul_comm]
    exact h
  have hr : ‖gaussSum χ' P.traceChar‖ ^ 2 = ‖ringComplex P.p‖ ^ 2 := by
    rw [← P.card_res_eq]
    exact_mod_cast hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hr

theorem gaussAt_one_eq : P.gaussAt 1 = gaussSum P.chi P.traceChar := by
  simp only [gaussAt, map_one, mul_one, gaussSum]

theorem gaussAt2_one_eq : P.gaussAt2 1 = gaussSum (P.chi ^ 2) P.traceChar := by
  simp only [gaussAt2, map_one, mul_one, gaussSum]

theorem norm_gaussAt_one : ‖P.gaussAt 1‖ = ‖ringComplex P.p‖ := by
  rw [P.gaussAt_one_eq]
  exact P.norm_gaussSum_traceChar _ P.chi_ne_one

theorem norm_gaussAt2_one : ‖P.gaussAt2 1‖ = ‖ringComplex P.p‖ := by
  rw [P.gaussAt2_one_eq]
  exact P.norm_gaussSum_traceChar _ P.chi_sq_ne_one

theorem gaussAt_one_ne_zero : P.gaussAt 1 ≠ 0 := by
  intro h
  have := P.norm_gaussAt_one
  rw [h, norm_zero] at this
  exact P.norm_pos.ne' this.symm

/-! ### Patterson's relation through the conjugate twist -/

theorem primeCubicGauss_two (h : O) : primeCubicGauss P.p P.prime P.primary 2 h = P.gaussAt2 h := by
  rw [primeCubicGauss_eq_gaussSum, gaussSum, gaussAt2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show residueTraceQuotientChar h P.p P.prime.ne_zero = P.psi h from rfl, P.psi_eq_traceChar]

/-- The q-divisible coefficients T(xq)² on x coprime to q. -/
def pCoeff (h : O) : ℂ := if P.p ∣ h then 0 else rationalSourceResidualFourierCoefficient (h * P.p) ^ 2

theorem pCoeff_gauss (h : O) : P.gaussAt 1 * P.pCoeff h =
    (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * P.gaussCoeff h := by
  have hP : (‖ringComplex P.p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.norm_pos.ne'
  unfold pCoeff gaussCoeff
  split_ifs with hh
  · have h0 : P.res h = 0 := (P.res_eq_zero_iff h).mpr hh
    rw [P.gaussAt_eq h, h0, MulChar.map_zero, inv_zero]
    ring
  · rw [rationalSourceResidualFourierCoefficient_prime_factor P.p P.prime P.primary h hh, P.primeCubicGauss_two,
      div_mul_eq_mul_div, div_pow]
    have key := P.gauss_sq_shift h hh
    field_simp
    linear_combination (rationalSourceResidualFourierCoefficient h ^ 2) * key

theorem gaussDirichlet_pCoeff (s : ℂ) : P.gaussAt 1 * besselDirichlet P.pCoeff s =
    (P.chi 9)⁻¹ * P.gaussAt2 1 ^ 2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselDirichlet P.gaussCoeff s := by
  rw [besselDirichlet, besselDirichlet, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun h => ?_
  split_ifs
  · ring
  · rw [← mul_assoc, P.pCoeff_gauss]
    ring


/-! ### The Euler identity at q -/

/-- **The theta square factors through the q-coprime squares and the q-divisible part.** For Re s > 4:
(1 − ρ²t³)D(s) = D_{cop}(s) + tD_q(s), t = ρ^{−s}. -/
theorem thetaSq_euler (s : ℂ) (hs : 4 < s.re) :
    (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3) * thetaSqDirichlet s =
      besselDirichlet P.coprimeCoeff s + ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet P.pCoeff s := by
  set ρ := ‖ringComplex P.p‖ with hρ
  set t : ℂ := ((ρ : ℝ) : ℂ) ^ (-s) with ht
  set w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s) with hw
  set F : O → ℂ := fun h => if h = 0 then 0 else rationalSourceResidualFourierCoefficient h ^ 2 * w h with hF
  have hD : thetaSqDirichlet s = ∑' h, F h := rfl
  have hFs : Summable (fun h => ‖F h‖) := by
    refine ((summable_sq_coeff hs).mul_left ((4 * Real.pi) ^ (-s.re))).congr fun h => ?_
    by_cases h0 : h = 0
    · simp [hF, h0]
    · have hξ : 0 < ‖cuspFrequency h‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero h h0)
      simp only [hF, if_neg h0, norm_mul, hw]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, Real.mul_rpow (by positivity) hξ.le]
      ring
  have hw_mul : ∀ h c : O, w (h * c) = w h * ((‖ringComplex c‖ : ℝ) : ℂ) ^ (-s) := by
    intro h c
    simp only [hw, cuspFrequency_mul_right, norm_mul]
    rw [show 4 * Real.pi * (‖cuspFrequency h‖ * ‖ringComplex c‖) =
        (4 * Real.pi * ‖cuspFrequency h‖) * ‖ringComplex c‖ by ring, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
  have hp3 : ((‖ringComplex (P.p ^ 3)‖ : ℝ) : ℂ) ^ (-s) = t ^ 3 := by
    rw [map_pow, norm_pow, ofReal_pow_cpow _ (norm_nonneg _)]
  set Fc : O → ℂ := fun h => if h = 0 then 0 else P.coprimeCoeff h * w h with hFc
  set F1 : O → ℂ := fun h => if P.p ∣ h ∧ ¬ P.p ^ 2 ∣ h then F h else 0 with hF1
  set F3 : O → ℂ := fun h => if P.p ^ 3 ∣ h then F h else 0 with hF3
  have hsplit : ∀ h, F h = Fc h + F1 h + F3 h := by
    intro h
    by_cases h0 : h = 0
    · simp [hF, hFc, hF1, hF3, h0]
    · by_cases h1 : P.p ∣ h
      · have hc : Fc h = 0 := by simp [hFc, h0, coprimeCoeff, h1]
        by_cases h2 : P.p ^ 2 ∣ h
        · by_cases h3 : P.p ^ 3 ∣ h
          · simp [hF1, hF3, hc, h2, h3]
          · have hz : F h = 0 := by
              obtain ⟨m, rfl⟩ := h2
              have hm : ¬ P.p ∣ m := fun hm => h3 (by obtain ⟨k, rfl⟩ := hm; exact ⟨k, by ring⟩)
              simp only [hF, h0, if_false]
              rw [show P.p ^ 2 * m = m * P.p ^ 2 by ring,
                rationalSourceResidualFourierCoefficient_prime_power_vanish P.p P.prime P.primary m hm 2 (by norm_num)]
              ring
            simp [hF1, hF3, hc, h2, h3, hz]
        · have h3 : ¬ P.p ^ 3 ∣ h := fun h3 => h2 ((pow_dvd_pow P.p (by norm_num : 2 ≤ 3)).trans h3)
          simp [hF1, hF3, hc, h1, h2, h3]
      · have h3 : ¬ P.p ^ 3 ∣ h := fun h3 => h1 ((dvd_pow_self P.p (by norm_num : 3 ≠ 0)).trans h3)
        simp [hF, hFc, hF1, hF3, h0, coprimeCoeff, h1, h3]
  have hFc_le : ∀ h, ‖Fc h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hFc, hF, coprimeCoeff]
    split_ifs <;> simp
  have hF1_le : ∀ h, ‖F1 h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hF1]
    split_ifs <;> simp
  have hF3_le : ∀ h, ‖F3 h‖ ≤ ‖F h‖ := by
    intro h
    simp only [hF3]
    split_ifs <;> simp
  have sc := Summable.of_norm_bounded hFs hFc_le
  have s1 := Summable.of_norm_bounded hFs hF1_le
  have s3 := Summable.of_norm_bounded hFs hF3_le
  have hsum : ∑' h, F h = ∑' h, Fc h + ∑' h, F1 h + ∑' h, F3 h := by
    rw [← sc.tsum_add s1, ← (sc.add s1).tsum_add s3]
    exact tsum_congr hsplit
  have hinj3 : Injective (fun h : O => h * P.p ^ 3) := fun a b hab =>
    mul_right_cancel₀ (pow_ne_zero 3 P.ne_zero) hab
  have h3 : ∑' h, F3 h = (ρ : ℂ) ^ 2 * t ^ 3 * ∑' h, F h := by
    have hsupp : support F3 ⊆ Set.range (fun h : O => h * P.p ^ 3) := by
      intro h hh
      by_contra hn
      apply hh
      have : ¬ P.p ^ 3 ∣ h := fun ⟨c, hc⟩ => hn ⟨c, by rw [hc]; ring⟩
      simp [hF3, this]
    rw [← hinj3.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    simp only [hF3, dvd_mul_left, if_true, hF]
    by_cases h0 : h = 0
    · simp [h0]
    · have hc3 : rationalSourceResidualFourierCoefficient (h * P.p ^ 3) =
          (ρ : ℂ) * rationalSourceResidualFourierCoefficient h := by
        simpa using P.coeff_mul_cube_pow h h0 1
      rw [if_neg (mul_ne_zero h0 (pow_ne_zero 3 P.ne_zero)), if_neg h0, hc3, hw_mul, hp3]
      ring
  have hinj1 : Injective (fun h : O => h * P.p) := fun a b hab => mul_right_cancel₀ P.ne_zero hab
  have h1 : ∑' h, F1 h = t * besselDirichlet P.pCoeff s := by
    have hsupp : support F1 ⊆ Set.range (fun h : O => h * P.p) := by
      intro h hh
      by_contra hn
      apply hh
      have : ¬ P.p ∣ h := fun ⟨c, hc⟩ => hn ⟨c, by rw [hc]; ring⟩
      simp [hF1, this]
    rw [← hinj1.tsum_eq hsupp, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun x => ?_
    have hiff : (P.p ∣ x * P.p ∧ ¬ P.p ^ 2 ∣ x * P.p) ↔ ¬ P.p ∣ x := by
      constructor
      · rintro ⟨-, h2⟩ hx
        obtain ⟨c, rfl⟩ := hx
        exact h2 ⟨c, by ring⟩
      · intro hx
        refine ⟨dvd_mul_left _ _, fun h2 => hx ?_⟩
        rw [pow_two] at h2
        exact (mul_dvd_mul_iff_right P.ne_zero).mp h2
    simp only [hF1]
    rw [if_congr hiff rfl rfl]
    by_cases hx : P.p ∣ x
    · rw [if_neg (not_not.mpr hx)]
      simp [pCoeff, hx]
    · have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0]; exact dvd_zero _)
      rw [if_pos hx, if_neg hx0]
      simp only [hF, if_neg (mul_ne_zero hx0 P.ne_zero), pCoeff, if_neg hx, hw_mul]
      ring
  rw [hD, hsum, h3, h1]
  ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
