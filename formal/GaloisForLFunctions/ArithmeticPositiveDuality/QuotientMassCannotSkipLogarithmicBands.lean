import GaloisForLFunctions.ArithmeticPositiveDuality.AnnihilatorDivisionForcesCoefficientOscillation
import Mathlib.Data.Finsupp.Interval

/-!
# A zero forces quotient mass in every logarithmic band

Truncating the formal convolution at logarithmic frequency leaves only a
boundary band. At a zero of the polynomial, this band must carry the nonzero
geometric numerator. Its absolute mass therefore has a uniform positive
lower bound at all sufficiently large cutoffs.
-/

noncomputable section
open Complex Finset Filter Topology
open scoped NNReal

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator

/-- All two-prime monomials below a logarithmic cutoff. -/
def frequencyCutoff (T : ℝ) : Finset (Fin 2 →₀ ℕ) := by
  classical
  exact (Iic (Finsupp.equivFunOnFinite.symm (fun _ : Fin 2 => ⌈T / Real.log 2⌉₊))).filter
    (fun d => monomialLog d ≤ T)

theorem mem_frequencyCutoff {d : Fin 2 →₀ ℕ} {T : ℝ} :
    d ∈ frequencyCutoff T ↔ monomialLog d ≤ T := by
  classical
  simp only [frequencyCutoff, mem_filter, mem_Iic]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  intro i
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hi : (d i : ℝ) * Real.log 2 ≤ monomialLog d := by
    fin_cases i
    · dsimp only [monomialLog, primeBase]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (hlog.le.trans h23))
    · dsimp only [monomialLog, primeBase]
      exact (mul_le_mul_of_nonneg_left h23 (Nat.cast_nonneg _)).trans
        (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hlog.le))
  have hb : (d i : ℝ) ≤ ⌈T / Real.log 2⌉₊ :=
    ((le_div_iff₀ hlog).mpr (hi.trans h)).trans (Nat.le_ceil _)
  exact_mod_cast hb

theorem frequencyCutoff_mono {A B : ℝ} (h : A ≤ B) :
    frequencyCutoff A ⊆ frequencyCutoff B := by
  intro d hd
  exact mem_frequencyCutoff.mpr ((mem_frequencyCutoff.mp hd).trans h)

theorem tendsto_frequencyCutoff : Tendsto frequencyCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (∑ d ∈ S, monomialLog d)] with T hT
  intro d hd
  apply mem_frequencyCutoff.mpr
  exact (single_le_sum (fun e _ => frequency_nonneg e) hd).trans hT

/-- A finite logarithmic band, open at its lower boundary. -/
def logarithmicBand (A B : ℝ) : Finset (Fin 2 →₀ ℕ) :=
  frequencyCutoff B \ frequencyCutoff A

theorem mem_logarithmicBand {d : Fin 2 →₀ ℕ} {A B : ℝ} :
    d ∈ logarithmicBand A B ↔ A < monomialLog d ∧ monomialLog d ≤ B := by
  classical
  simp only [logarithmicBand, Finset.mem_sdiff, mem_frequencyCutoff, not_le, and_comm]

/-- A monomial shift translates the logarithmic cutoff by exactly its frequency. -/
theorem sum_shifted_frequencyCutoff (b : (Fin 2 →₀ ℕ) → ℂ) (s : ℂ)
    (e : Fin 2 →₀ ℕ) (T : ℝ) :
    (∑ d ∈ frequencyCutoff T, if e ≤ d then
      b (d - e) * Complex.exp (-(monomialLog d : ℂ) * s) else 0) =
      Complex.exp (-(monomialLog e : ℂ) * s) *
        ∑ f ∈ frequencyCutoff (T - monomialLog e),
          b f * Complex.exp (-(monomialLog f : ℂ) * s) := by
  classical
  rw [← sum_filter, mul_sum]
  symm
  apply sum_bij (fun f _ => e + f)
  · intro f hf
    apply mem_filter.mpr
    refine ⟨mem_frequencyCutoff.mpr ?_, le_add_of_nonneg_right zero_le⟩
    rw [frequency_add]
    have h := mem_frequencyCutoff.mp hf
    linarith only [h]
  · intro f _ g _ he
    exact add_left_cancel he
  · intro d hd
    obtain ⟨hdT, he⟩ := mem_filter.mp hd
    refine ⟨d - e, mem_frequencyCutoff.mpr ?_, add_tsub_cancel_of_le he⟩
    have hid := frequency_add e (d - e)
    rw [add_tsub_cancel_of_le he] at hid
    have h := mem_frequencyCutoff.mp hdT
    linarith only [h, hid]
  · intro f _
    rw [add_tsub_cancel_left, frequency_add, Complex.ofReal_add]
    rw [show -((monomialLog e : ℂ) + (monomialLog f : ℂ)) * s =
      -(monomialLog e : ℂ) * s + -(monomialLog f : ℂ) * s by ring,
      Complex.exp_add]
    ring

/-- The difference of two nested truncations is exactly their boundary band. -/
theorem sum_frequencyCutoff_sub {A B : ℝ} (hAB : A ≤ B)
    (f : (Fin 2 →₀ ℕ) → ℂ) :
    (∑ d ∈ frequencyCutoff B, f d) - (∑ d ∈ frequencyCutoff A, f d) =
      ∑ d ∈ logarithmicBand A B, f d := by
  rw [← sum_sdiff (frequencyCutoff_mono hAB), add_sub_cancel_right]
  rfl

/-- The finite convolution identity includes the constant monomial. -/
theorem quotient_convolution (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (d : Fin 2 →₀ ℕ) :
    (∑ e ∈ P.support, if e ≤ d then
      ((P.coeff e : ℝ≥0) : ℝ) * annihilatorQuotientCoeff P (d - e) else 0) = 1 := by
  have h := congrArg (MvPowerSeries.coeff d) (quotient_mul P hP)
  rw [coeff_polynomial_mul,
    MvPolynomial.support_map_of_injective P NNReal.coe_injective] at h
  simpa only [MvPolynomial.coeff_map, NNReal.coe_toRealHom,
    annihilatorQuotientCoeff, MvPowerSeries.coeff_apply] using h

/-- The weighted truncated recurrence translates each cutoff by its kernel frequency. -/
theorem quotient_truncated_convolution (P : MvPolynomial (Fin 2) ℝ≥0)
    (hP : MvPolynomial.constantCoeff P = 1) (s : ℂ) (T : ℝ) :
    (∑ e ∈ P.support,
      (((P.coeff e : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog e : ℂ) * s) *
        ∑ d ∈ frequencyCutoff (T - monomialLog e),
          (annihilatorQuotientCoeff P d : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s)) =
      ∑ d ∈ frequencyCutoff T, Complex.exp (-(monomialLog d : ℂ) * s) := by
  classical
  have hc (d : Fin 2 →₀ ℕ) : (∑ e ∈ P.support, if e ≤ d then
      (((P.coeff e : ℝ≥0) : ℝ) : ℂ) * (annihilatorQuotientCoeff P (d - e) : ℂ) else 0) = 1 := by
    have h := congrArg Complex.ofReal (quotient_convolution P hP d)
    push_cast at h
    calc
      _ = ∑ e ∈ P.support, Complex.ofReal (if e ≤ d then
          ((P.coeff e : ℝ≥0) : ℝ) * annihilatorQuotientCoeff P (d - e) else 0) := by
        apply sum_congr rfl
        intro e _
        by_cases he : e ≤ d
        · simp only [if_pos he, Complex.ofReal_mul]
        · simp only [if_neg he, Complex.ofReal_zero]
      _ = 1 := h
  calc
    _ = ∑ e ∈ P.support, (((P.coeff e : ℝ≥0) : ℝ) : ℂ) *
        ∑ d ∈ frequencyCutoff T, if e ≤ d then
          (annihilatorQuotientCoeff P (d - e) : ℂ) *
            Complex.exp (-(monomialLog d : ℂ) * s) else 0 := by
      apply sum_congr rfl
      intro e _
      rw [sum_shifted_frequencyCutoff (fun d => (annihilatorQuotientCoeff P d : ℂ)) s e T]
      ring
    _ = ∑ d ∈ frequencyCutoff T,
        (∑ e ∈ P.support, if e ≤ d then
          (((P.coeff e : ℝ≥0) : ℝ) : ℂ) * (annihilatorQuotientCoeff P (d - e) : ℂ) else 0) *
          Complex.exp (-(monomialLog d : ℂ) * s) := by
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring
    _ = _ := by simp only [hc, one_mul]

/-- Critical absolute coefficient mass in a finite logarithmic band. -/
def quotientBandMass (P : MvPolynomial (Fin 2) ℝ≥0) (β A B : ℝ) : ℝ :=
  ∑ d ∈ logarithmicBand A B,
    |annihilatorQuotientCoeff P d| * Real.exp (-monomialLog d * β)

theorem quotientBandMass_nonneg (P : MvPolynomial (Fin 2) ℝ≥0) (β A B : ℝ) :
    0 ≤ quotientBandMass P β A B :=
  sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)

private theorem quotient_term_norm (P : MvPolynomial (Fin 2) ℝ≥0) (s : ℂ)
    (d : Fin 2 →₀ ℕ) :
    ‖(annihilatorQuotientCoeff P d : ℂ) * Complex.exp (-(monomialLog d : ℂ) * s)‖ =
      |annihilatorQuotientCoeff P d| * Real.exp (-monomialLog d * s.re) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

/-- At a polynomial zero, only the boundary of the truncated convolution remains. -/
theorem geometric_truncation_le_quotient_band
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hz : dirichletEval ρ P = 0) {B : ℝ}
    (hB : ∀ e ∈ P.support, monomialLog e ≤ B) (T : ℝ) :
    ‖∑ d ∈ frequencyCutoff T, Complex.exp (-(monomialLog d : ℂ) * ρ)‖ ≤
      (∑ e ∈ P.support, ((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * ρ.re)) *
        quotientBandMass P ρ.re (T - B) T := by
  classical
  let F := fun u => ∑ d ∈ frequencyCutoff u,
    (annihilatorQuotientCoeff P d : ℂ) * Complex.exp (-(monomialLog d : ℂ) * ρ)
  let c := fun e => (((P.coeff e : ℝ≥0) : ℝ) : ℂ) * Complex.exp (-(monomialLog e : ℂ) * ρ)
  have hid : (∑ e ∈ P.support, c e * (F T - F (T - monomialLog e))) =
      -(∑ d ∈ frequencyCutoff T, Complex.exp (-(monomialLog d : ℂ) * ρ)) := by
    simp only [mul_sub, sum_sub_distrib]
    rw [← sum_mul, show (∑ e ∈ P.support, c e) = 0 by
      rw [← dirichletEval_eq_frequency_sum]; exact hz, zero_mul, zero_sub]
    congr 1
    exact quotient_truncated_convolution P hP ρ T
  have hdiff (e : Fin 2 →₀ ℕ) (he : e ∈ P.support) :
      ‖F T - F (T - monomialLog e)‖ ≤ quotientBandMass P ρ.re (T - B) T := by
    dsimp only [F]
    rw [sum_frequencyCutoff_sub (sub_le_self T (frequency_nonneg e))]
    apply (norm_sum_le _ _).trans
    simp only [quotient_term_norm]
    apply sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hlo, hhi⟩ := mem_logarithmicBand.mp hd
      exact mem_logarithmicBand.mpr ⟨lt_of_le_of_lt (by linarith only [hB e he]) hlo, hhi⟩
    · intro d _ _
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  calc
    _ = ‖∑ e ∈ P.support, c e * (F T - F (T - monomialLog e))‖ := by rw [hid, norm_neg]
    _ ≤ ∑ e ∈ P.support, ‖c e * (F T - F (T - monomialLog e))‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ P.support, ‖c e‖ * quotientBandMass P ρ.re (T - B) T := by
      apply sum_le_sum
      intro e he
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hdiff e he) (norm_nonneg _)
    _ = _ := by
      rw [← sum_mul]
      congr 1
      apply sum_congr rfl
      intro e _
      simp only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (P.coeff e).coe_nonneg, Complex.norm_exp,
        Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

/-- At the exact real part of a right-hand zero, every sufficiently high band
of a fixed width carries uniformly positive absolute quotient mass. -/
theorem quotient_band_mass_eventually_lower
    (P : MvPolynomial (Fin 2) ℝ≥0) (hP : MvPolynomial.constantCoeff P = 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : dirichletEval ρ P = 0) {B : ℝ}
    (hB : ∀ e ∈ P.support, monomialLog e ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop, c ≤ quotientBandMass P ρ.re (T - B) T := by
  classical
  let A := ∑ e ∈ P.support, ((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * ρ.re)
  have h0 : (0 : Fin 2 →₀ ℕ) ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, show P.coeff 0 = 1 from hP]
    exact one_ne_zero
  have hA : 0 < A := by
    have h := single_le_sum (f := fun e =>
      ((P.coeff e : ℝ≥0) : ℝ) * Real.exp (-monomialLog e * ρ.re))
      (fun e _ => mul_nonneg (P.coeff e).coe_nonneg (Real.exp_pos _).le) h0
    have hc : P.coeff 0 = 1 := hP
    simp only [hc, NNReal.coe_one, monomialLog, Finsupp.zero_apply, Nat.cast_zero,
      zero_mul, zero_add, neg_zero, Real.exp_zero, one_mul] at h
    exact zero_lt_one.trans_le h
  let G := ∑' d : Fin 2 →₀ ℕ, Complex.exp (-(monomialLog d : ℂ) * ρ)
  have hG : 0 < ‖G‖ := norm_pos_iff.mpr (frequency_geometric_sum_ne_zero hρ)
  have hlim : Tendsto (fun T => ‖∑ d ∈ frequencyCutoff T,
      Complex.exp (-(monomialLog d : ℂ) * ρ)‖) atTop (𝓝 ‖G‖) :=
    ((frequency_geometric hρ).summable.hasSum.comp tendsto_frequencyCutoff).norm
  have hev : ∀ᶠ T : ℝ in atTop,
      ‖G‖ / 2 < ‖∑ d ∈ frequencyCutoff T,
        Complex.exp (-(monomialLog d : ℂ) * ρ)‖ :=
    hlim.eventually (Ioi_mem_nhds (half_lt_self hG))
  refine ⟨(‖G‖ / 2) / A, div_pos (half_pos hG) hA, ?_⟩
  filter_upwards [hev] with T hT
  apply (div_le_iff₀ hA).mpr
  have h := geometric_truncation_le_quotient_band P hP hz hB T
  change _ ≤ A * quotientBandMass P ρ.re (T - B) T at h
  nlinarith only [hT, h]

#print axioms quotient_band_mass_eventually_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator
