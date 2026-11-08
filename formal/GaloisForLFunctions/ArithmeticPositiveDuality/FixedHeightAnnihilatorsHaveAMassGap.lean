import GaloisForLFunctions.ArithmeticPositiveDuality.TheHyperbolicCostOfReflectedZeroPairs

/-!
# Fixed-height mass gaps for positive annihilators

The isolated lowest frequency gives a height-dependent mass bound.
Reflected pairs approach the unrestricted mass floor precisely when the
prime-two phase is minus one.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- The first prime-two monomial is isolated from every other nonconstant frequency. -/
theorem log_three_le_monomialLog_of_ne_first (d : Fin 2 →₀ ℕ)
    (hd : d ≠ 0) (hfirst : d ≠ Finsupp.single 0 1) :
    Real.log 3 ≤ monomialLog d := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 2 * 2)
    rw [Real.log_mul (by norm_num) (by norm_num)] at h
    linarith only [h]
  change Real.log 3 ≤ (d 0 : ℝ) * Real.log 2 + (d 1 : ℝ) * Real.log 3
  by_cases h1 : d 1 = 0
  · have hn : 2 ≤ d 0 := by
      by_contra hn
      have hz : d 0 = 0 ∨ d 0 = 1 := by omega
      rcases hz with hz | hz
      · apply hd
        ext i
        fin_cases i <;> simp [hz, h1]
      · apply hfirst
        ext i
        fin_cases i <;> simp [hz, h1]
    have hn' : (2 : ℝ) ≤ (d 0 : ℝ) := by exact_mod_cast hn
    simpa only [h1, Nat.cast_zero, zero_mul, add_zero] using
      h34.trans (mul_le_mul_of_nonneg_right hn' h2.le)
  · have hn : (1 : ℝ) ≤ (d 1 : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr h1)
    have hm := mul_le_mul_of_nonneg_right hn h3.le
    have h0 : 0 ≤ (d 0 : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) h2.le
    linarith only [hm, h0]

/-- Maximum cancellation per unit central mass, separating the first frequency. -/
def firstFrequencyCancellation (δ γ : ℝ) : ℝ :=
  max (-Real.cos (γ * Real.log 2) * Real.exp (-δ * Real.log 2))
    (Real.exp (-δ * Real.log 3))

private theorem firstFrequencyCancellation_pos (δ γ : ℝ) :
    0 < firstFrequencyCancellation δ γ :=
  (Real.exp_pos _).trans_le (le_max_right _ _)

private theorem shifted_real_cancellation {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ}
    (hz : dirichletEval (ρ + (δ : ℂ)) P = 0) :
    1 = ∑ d ∈ P.support.erase 0,
      (((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * ρ.re)) *
        (-Real.cos (ρ.im * monomialLog d) * Real.exp (-δ * monomialLog d)) := by
  have he := dirichletTailMass_sub_one_eq_phase_defect hP hz
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im,
    add_zero, dirichletTailMass, mul_add, mul_one, Finset.sum_add_distrib] at he
  have hs : (∑ d ∈ P.support.erase 0,
      ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * (ρ.re + δ)) *
        Real.cos (monomialLog d * ρ.im)) = -1 := by
    simp only [mul_add]
    linarith only [he]
  calc
    1 = -(∑ d ∈ P.support.erase 0,
        ((P.coeff d : ℝ≥0) : ℝ) * Real.exp (-monomialLog d * (ρ.re + δ)) *
          Real.cos (monomialLog d * ρ.im)) := by rw [hs]; ring
    _ = _ := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d _
      rw [show -monomialLog d * (ρ.re + δ) =
        -monomialLog d * ρ.re + -δ * monomialLog d by ring, Real.exp_add]
      rw [mul_comm (monomialLog d) ρ.im]
      ring

/-- A fixed-height zero imposes a mass bound independent of the available bandwidth. -/
theorem fixed_height_forces_mass {P : MvPolynomial (Fin 2) ℝ≥0}
    (hP : MvPolynomial.constantCoeff P = 1) {ρ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hz : dirichletEval (ρ + (δ : ℂ)) P = 0) :
    1 / firstFrequencyCancellation δ ρ.im ≤ dirichletTailMass P ρ.re := by
  have hterm (d : Fin 2 →₀ ℕ) (hd : d ∈ P.support.erase 0) :
      -Real.cos (ρ.im * monomialLog d) * Real.exp (-δ * monomialLog d) ≤
        firstFrequencyCancellation δ ρ.im := by
    by_cases hfirst : d = Finsupp.single 0 1
    · subst d
      simp [monomialLog, primeBase, firstFrequencyCancellation]
    · have hL := log_three_le_monomialLog_of_ne_first d (Finset.mem_erase.mp hd).1 hfirst
      calc
        _ ≤ Real.exp (-δ * monomialLog d) := by
          have hc : -Real.cos (ρ.im * monomialLog d) ≤ 1 := by
            linarith only [Real.neg_one_le_cos (ρ.im * monomialLog d)]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
        _ ≤ Real.exp (-δ * Real.log 3) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonpos_left hL (neg_nonpos.mpr hδ.le)
        _ ≤ _ := le_max_right _ _
  have hm : 1 ≤ firstFrequencyCancellation δ ρ.im * dirichletTailMass P ρ.re := by
    rw [shifted_real_cancellation hP hz, dirichletTailMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hterm d hd)
      (mul_nonneg (P.coeff d).coe_nonneg (Real.exp_pos (-monomialLog d * ρ.re)).le)
  exact (div_le_iff₀ (firstFrequencyCancellation_pos δ ρ.im)).mpr
    (by simpa only [mul_comm] using hm)

/-- Away from the first frequency's opposite phase, the fixed-height bound is
strictly above the unrestricted one-root floor. -/
theorem fixed_height_bound_gt_floor {δ γ : ℝ} (hδ : 0 < δ)
    (hphase : Real.cos (γ * Real.log 2) ≠ -1) :
    Real.exp (δ * Real.log 2) < 1 / firstFrequencyCancellation δ γ := by
  have hc : -Real.cos (γ * Real.log 2) < 1 := by
    have h := Real.neg_one_le_cos (γ * Real.log 2)
    have hn : -1 < Real.cos (γ * Real.log 2) := lt_of_le_of_ne h (Ne.symm hphase)
    linarith only [hn]
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hM : firstFrequencyCancellation δ γ < Real.exp (-δ * Real.log 2) := by
    apply max_lt
    · simpa only [one_mul] using mul_lt_mul_of_pos_right hc (Real.exp_pos _)
    · apply Real.exp_lt_exp.mpr
      exact mul_lt_mul_of_neg_left h23 (neg_neg_of_pos hδ)
  apply (lt_div_iff₀ (firstFrequencyCancellation_pos δ γ)).mpr
  calc
    Real.exp (δ * Real.log 2) * firstFrequencyCancellation δ γ <
        Real.exp (δ * Real.log 2) * Real.exp (-δ * Real.log 2) :=
      mul_lt_mul_of_pos_left hM (Real.exp_pos _)
    _ = 1 := by rw [← Real.exp_add, show δ * Real.log 2 + -δ * Real.log 2 = 0 by ring, Real.exp_zero]


private theorem scaledTwoMonomial_at_opposite_phase {ρ : ℂ}
    (hphase : Real.cos (ρ.im * Real.log 2) = -1) :
    dirichletEval ρ (scaledTwoMonomial ρ.re) = -1 := by
  have hs : Real.sin (ρ.im * Real.log 2) = 0 := by
    apply sq_eq_zero_iff.mp
    have h := Real.sin_sq_add_cos_sq (ρ.im * Real.log 2)
    rw [hphase] at h
    nlinarith only [h]
  rw [dirichletEval_scaledTwoMonomial]
  apply Complex.ext
  · simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, mul_zero,
      zero_mul, zero_sub, add_zero, mul_neg, Real.cos_neg, neg_zero,
      Real.exp_zero, one_mul, Complex.neg_re, Complex.one_re]
    rw [mul_comm (Real.log 2) ρ.im, hphase]
  · simp only [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, mul_zero,
      zero_mul, zero_sub, add_zero, mul_neg, Real.sin_neg,
      Real.exp_zero, one_mul, Complex.neg_im, Complex.one_im, neg_zero]
    rw [mul_comm (Real.log 2) ρ.im, hs, neg_zero]

private theorem scaledTwoMonomial_shift (σ : ℝ) (ρ : ℂ) (t : ℝ) :
    dirichletEval (ρ + (t : ℂ)) (scaledTwoMonomial σ) =
      dirichletEval ρ (scaledTwoMonomial σ) * (Real.exp (-Real.log 2 * t) : ℂ) := by
  rw [dirichletEval_scaledTwoMonomial, dirichletEval_scaledTwoMonomial,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem reflectedPairAnnihilator_eval_congr (σ δ : ℝ) (m : ℕ) {s t : ℂ}
    (h : dirichletEval s (scaledTwoMonomial σ) =
      dirichletEval t (scaledTwoMonomial σ)) :
    dirichletEval s (reflectedPairAnnihilator σ δ m) =
      dirichletEval t (reflectedPairAnnihilator σ δ m) := by
  have hc (c : ℝ≥0) : dirichletEval s (MvPolynomial.C c) =
      dirichletEval t (MvPolynomial.C c) := by simp [dirichletEval]
  simp only [reflectedPairAnnihilator, map_add, map_one, map_mul, map_pow, hc, h]

/-- The explicit endpoint trinomials work at every opposite prime-two phase. -/
theorem reflectedPairAnnihilator_zeros_of_opposite_phase {ρ : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hphase : Real.cos (ρ.im * Real.log 2) = -1) (m : ℕ) :
    dirichletEval (ρ + (δ : ℂ)) (reflectedPairAnnihilator ρ.re δ m) = 0 ∧
      dirichletEval (ρ - (δ : ℂ)) (reflectedPairAnnihilator ρ.re δ m) = 0 := by
  have he (t : ℝ) :
      dirichletEval (ρ + (t : ℂ)) (reflectedPairAnnihilator ρ.re δ m) =
        dirichletEval (sharpBinomialRoot ρ.re + (t : ℂ))
          (reflectedPairAnnihilator ρ.re δ m) := by
    apply reflectedPairAnnihilator_eval_congr
    rw [scaledTwoMonomial_shift, scaledTwoMonomial_shift,
      scaledTwoMonomial_at_opposite_phase hphase, scaledTwoMonomial_at_root]
  have hz := reflectedPairAnnihilator_zeros ρ.re hδ m
  constructor
  · rw [he δ]
    exact hz.1
  · have hm := he (-δ)
    simp only [Complex.ofReal_neg, ← sub_eq_add_neg] at hm
    rw [hm]
    exact hz.2

private theorem reflectedPairFrequency_tendsto :
    Tendsto reflectedPairFrequency atTop atTop := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  apply tendsto_atTop_mono _ (ht.atTop_mul_const hlog)
  intro m
  dsimp only [reflectedPairFrequency]
  push_cast
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith only [mul_nonneg hm hlog.le, hlog]

/-- At an opposite first phase, reflected-pair mass approaches the unrestricted floor. -/
theorem exists_fixed_height_reflected_pair_near_floor {ρ : ℂ} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hphase : Real.cos (ρ.im * Real.log 2) = -1) :
    ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      dirichletEval (ρ + (δ : ℂ)) P = 0 ∧ dirichletEval (ρ - (δ : ℂ)) P = 0 ∧
      Real.exp (δ * Real.log 2) < dirichletTailMass P ρ.re ∧
      dirichletTailMass P ρ.re < Real.exp (δ * Real.log 2) + ε := by
  have ht := (tendsto_reflected_pair_cost_atTop hδ (Real.log 2)).comp
    reflectedPairFrequency_tendsto
  obtain ⟨m, hm⟩ := (ht.eventually_lt_const (lt_add_of_pos_right _ hε)).exists
  have hz := reflectedPairAnnihilator_zeros_of_opposite_phase hδ hphase m
  refine ⟨reflectedPairAnnihilator ρ.re δ m,
    reflectedPairAnnihilator_constantCoeff ρ.re δ m, hz.1, hz.2,
    reflected_pair_mass_gt_single_root_floor
      (reflectedPairAnnihilator_constantCoeff ρ.re δ m) hδ hz.1 hz.2, ?_⟩
  rw [reflectedPairAnnihilator_mass ρ.re hδ m]
  exact hm

/-- Exact height classification for approaching the reflected-pair mass floor. -/
theorem fixed_height_reflected_pair_floor_iff (ρ : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    (∀ ε : ℝ, 0 < ε → ∃ P : MvPolynomial (Fin 2) ℝ≥0,
      MvPolynomial.constantCoeff P = 1 ∧
      dirichletEval (ρ + (δ : ℂ)) P = 0 ∧ dirichletEval (ρ - (δ : ℂ)) P = 0 ∧
      dirichletTailMass P ρ.re < Real.exp (δ * Real.log 2) + ε) ↔
      Real.cos (ρ.im * Real.log 2) = -1 := by
  constructor
  · intro h
    by_contra hp
    have hg := fixed_height_bound_gt_floor hδ hp
    obtain ⟨P, hP, hz, _, hm⟩ := h
      ((1 / firstFrequencyCancellation δ ρ.im - Real.exp (δ * Real.log 2)) / 2)
      (by linarith only [hg])
    have hb := fixed_height_forces_mass hP hδ hz
    linarith only [hg, hm, hb]
  · intro hp ε hε
    obtain ⟨P, hP, hz, hm, _, hmass⟩ := exists_fixed_height_reflected_pair_near_floor hδ hε hp
    exact ⟨P, hP, hz, hm, hmass⟩

#print axioms log_three_le_monomialLog_of_ne_first
#print axioms fixed_height_forces_mass
#print axioms fixed_height_bound_gt_floor
#print axioms exists_fixed_height_reflected_pair_near_floor
#print axioms fixed_height_reflected_pair_floor_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
