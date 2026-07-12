import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantRatioSplit

/-!
# Atom decomposition of the theta-cusp raw moments

Every even raw moment of the positive theta-cusp source is the sum of the corresponding moments
of its individual integer atoms.  The proof supplies the required `L¹` majorant and performs the
sum--integral interchange.  It also isolates the dominant `n = 1` atom and proves that the
remaining raw moment is nonnegative.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The `2j`-th raw logarithmic moment contributed by one theta-cusp integer atom. -/
def thetaCuspAtomRawEvenMoment (j n : ℕ) : ℝ :=
  2 * ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspSourceTerm x n

theorem thetaCuspAtomRawEvenMoment_nonneg (j n : ℕ) :
    0 ≤ thetaCuspAtomRawEvenMoment j n := by
  rw [thetaCuspAtomRawEvenMoment]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (pow_nonneg hx.le _)
    (thetaCuspSourceTerm_nonneg_of_pos hx n)

@[simp]
theorem thetaCuspAtomRawEvenMoment_zero (j : ℕ) :
    thetaCuspAtomRawEvenMoment j 0 = 0 := by
  simp [thetaCuspAtomRawEvenMoment, thetaCuspSourceTerm, thetaCuspSeed]

/-- Exact positive-atom expansion of every theta-cusp even raw moment. -/
theorem thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment (j : ℕ) :
    thetaCuspRawEvenMoment j =
      ∑' n : ℕ, thetaCuspAtomRawEvenMoment j n := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun n x =>
    2 * (x ^ (2 * j) * thetaCuspSourceTerm x n)
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F n))).aestronglyMeasurable
  have hfull : Integrable (fun x : ℝ =>
      2 * (x ^ (2 * j) * thetaCuspFullSource x)) mu := by
    exact (integrableOn_thetaCuspRawMoment (2 * j)).const_mul 2
  have hnormsum : ∀ᵐ x ∂mu,
      (∑' n : ℕ, ‖F n x‖₊) =
        ‖2 * (x ^ (2 * j) * thetaCuspFullSource x)‖₊ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hterm (n : ℕ) : 0 ≤ F n x := by
      exact mul_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg hx.le _)
          (thetaCuspSourceTerm_nonneg_of_pos hx n))
    have hsum : Summable (fun n : ℕ => F n x) := by
      simpa only [F, mul_assoc] using
        (summable_thetaCuspSourceTerm x).mul_left (2 * x ^ (2 * j))
    apply NNReal.eq
    rw [NNReal.coe_tsum]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (hterm _)]
    rw [abs_of_nonneg]
    · calc
        (∑' n : ℕ, F n x) =
            (2 * x ^ (2 * j)) *
              (∑' n : ℕ, thetaCuspSourceTerm x n) := by
                simpa only [F, mul_assoc] using
                  Summable.tsum_mul_left (2 * x ^ (2 * j))
                    (summable_thetaCuspSourceTerm x)
        _ = 2 * (x ^ (2 * j) * thetaCuspFullSource x) := by
          simp only [thetaCuspFullSource]
          ring
    · exact mul_nonneg (by norm_num)
        (mul_nonneg (pow_nonneg hx.le _)
          (le_of_lt (thetaCuspFullSource_pos_of_pos hx)))
  have hnormsumE : ∀ᵐ x ∂mu,
      (∑' n : ℕ, ‖F n x‖ₑ) =
        ‖2 * (x ^ (2 * j) * thetaCuspFullSource x)‖ₑ := by
    filter_upwards [hnormsum] with x hx
    have hsum : Summable (fun n : ℕ => F n x) := by
      simpa only [F, mul_assoc] using
        (summable_thetaCuspSourceTerm x).mul_left (2 * x ^ (2 * j))
    have hnorm : Summable (fun n : ℕ => ‖F n x‖₊) := by
      exact NNReal.summable_coe.mp (by
        simpa only [coe_nnnorm] using hsum.norm)
    calc
      (∑' n : ℕ, ‖F n x‖ₑ) =
          ((∑' n : ℕ, ‖F n x‖₊ : NNReal) : ENNReal) := by
            exact (ENNReal.coe_tsum hnorm).symm
      _ = (‖2 * (x ^ (2 * j) * thetaCuspFullSource x)‖₊ : ENNReal) := by
        rw [hx]
      _ = ‖2 * (x ^ (2 * j) * thetaCuspFullSource x)‖ₑ := rfl
  have hfinite : (∑' n : ℕ, ∫⁻ x, ‖F n x‖ₑ ∂mu) ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hFmeas n).enorm)]
    rw [lintegral_congr_ae hnormsumE]
    exact ne_of_lt hfull.hasFiniteIntegral
  have hswap := integral_tsum hFmeas hfinite
  rw [thetaCuspRawEvenMoment]
  change 2 * ∫ x, x ^ (2 * j) * thetaCuspFullSource x ∂mu = _
  rw [← integral_const_mul]
  rw [show (fun x => 2 * (x ^ (2 * j) * thetaCuspFullSource x)) =
      fun x => ∑' n, F n x by
    funext x
    calc
      2 * (x ^ (2 * j) * thetaCuspFullSource x) =
          (2 * x ^ (2 * j)) *
            (∑' n : ℕ, thetaCuspSourceTerm x n) := by
              simp only [thetaCuspFullSource]
              ring
      _ = ∑' n : ℕ, F n x := by
        simpa only [F, mul_assoc] using
          (Summable.tsum_mul_left (2 * x ^ (2 * j))
            (summable_thetaCuspSourceTerm x)).symm]
  rw [hswap]
  apply tsum_congr
  intro n
  rw [thetaCuspAtomRawEvenMoment, integral_const_mul]

/-- The nonnegative remainder after removing the dominant `n = 1` theta-cusp atom. -/
def thetaCuspHigherAtomRawEvenMoment (j : ℕ) : ℝ :=
  thetaCuspRawEvenMoment j - thetaCuspAtomRawEvenMoment j 1

theorem thetaCuspAtomRawEvenMoment_one_le_raw (j : ℕ) :
    thetaCuspAtomRawEvenMoment j 1 ≤ thetaCuspRawEvenMoment j := by
  rw [thetaCuspAtomRawEvenMoment, thetaCuspRawEvenMoment]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x 1
  let g : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspFullSource x
  have hg : Integrable g mu := integrableOn_thetaCuspRawMoment (2 * j)
  have hmeas : AEStronglyMeasurable f mu := by
    exact ((by
      dsimp [f]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous f)).aestronglyMeasurable
  have hle : ∀ᵐ x ∂mu, f x ≤ g x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hterm : thetaCuspSourceTerm x 1 ≤ thetaCuspFullSource x := by
      rw [thetaCuspFullSource]
      exact (summable_thetaCuspSourceTerm x).le_tsum 1
        (fun n _ => thetaCuspSourceTerm_nonneg_of_pos hx n)
    exact mul_le_mul_of_nonneg_left hterm (pow_nonneg hx.le _)
  have hnorm : ∀ᵐ x ∂mu, ‖f x‖ ≤ ‖g x‖ := by
    filter_upwards [hle, ae_restrict_mem measurableSet_Ioi] with x hxle hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
    · exact hxle
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspFullSource_pos_of_pos hx).le
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspSourceTerm_nonneg_of_pos hx 1)
  have hf : Integrable f mu := hg.mono hmeas hnorm
  exact integral_mono_ae hf hg hle

theorem thetaCuspHigherAtomRawEvenMoment_nonneg (j : ℕ) :
    0 ≤ thetaCuspHigherAtomRawEvenMoment j := by
  exact sub_nonneg.mpr (thetaCuspAtomRawEvenMoment_one_le_raw j)

theorem thetaCuspRawEvenMoment_eq_one_add_higher (j : ℕ) :
    thetaCuspRawEvenMoment j =
      thetaCuspAtomRawEvenMoment j 1 + thetaCuspHigherAtomRawEvenMoment j := by
  rw [thetaCuspHigherAtomRawEvenMoment]
  ring

end

end RHTower
