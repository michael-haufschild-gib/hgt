import GaloisForLFunctions.HTGeometry.FinitePiProductSummability
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

/-! # From polynomial growth of field-window lengths to a Gaussian probability -/

open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
noncomputable section

/-- Field magnitude between consecutive integers. -/
def shell (n : ℕ) : Set ℝ := {y | (n:ℝ)≤|y| ∧ |y|<(n:ℝ)+1}

theorem shell_measurable (n : ℕ) : MeasurableSet (shell n) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

private theorem shell_pdf {n : ℕ} {y : ℝ} (hy : y∈shell n) :
    gaussianPDF 0 1 y≤ENNReal.ofReal (exp (-(1/2:ℝ)*(n:ℝ)^2)) := by
  apply ENNReal.ofReal_le_ofReal
  have hroot : 1≤sqrt (2*π) := (Real.le_sqrt (by norm_num) (by positivity)).mpr
    (by linarith only [pi_gt_three])
  have hs := mul_self_le_mul_self (Nat.cast_nonneg n) hy.1
  have hh : -(y-0)^2/(2*(1:ℝ))≤-(1/2:ℝ)*(n:ℝ)^2 := by
    rw [sub_zero,mul_one]
    nlinarith only [hs,sq_abs y]
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one,mul_one]
  exact (mul_le_of_le_one_left (exp_pos _).le (inv_le_one_of_one_le₀ hroot)).trans
    (exp_le_exp.mpr (by simpa only [mul_one] using hh))

/-- A polynomial bound on Lebesgue lengths of covers of the field shells
gives a Gaussian probability with the same small parameter. The event
itself need not be measurable. -/
theorem gaussian_of_shell_covers (d : ℕ) :
    ∃ C : ℝ, ∀ (A : Set ℝ) (u : ℝ), 0≤u →
      (∀ n, ∃ B : Set ℝ, MeasurableSet B ∧ B⊆shell n ∧ A∩shell n⊆B ∧
        volume B≤ENNReal.ofReal (u*(1+(n:ℝ))^d)) → (gaussianReal 0 1).real A≤u*C := by
  let g (n : ℕ) := (1+(n:ℝ))^d*exp (-(1/2:ℝ)*(n:ℝ)^2)
  have hs : Summable g := summable_one_add_pow_mul_exp_neg_nat_sq d (by norm_num : 0<(1/2:ℝ))
  refine ⟨∑' n, g n,fun A u hu h => ?_⟩
  choose B hm hb hcover hvol using h
  have hsub : A⊆⋃ n, B n := by
    intro y hy
    let n := ⌊|y|⌋₊
    exact mem_iUnion.mpr ⟨n,hcover n ⟨hy,Nat.floor_le (abs_nonneg y),Nat.lt_floor_add_one _⟩⟩
  have hμ (n : ℕ) : gaussianReal 0 1 (B n)≤ENNReal.ofReal (u*g n) := by
    let w := exp (-(1/2:ℝ)*(n:ℝ)^2)
    rw [gaussianReal_apply 0 one_ne_zero]
    calc
      _ ≤ ∫⁻ _y in B n, ENNReal.ofReal w := lintegral_mono_ae
        ((ae_restrict_mem (hm n)).mono fun y hy => shell_pdf (hb n hy))
      _ = ENNReal.ofReal w*volume (B n) := by simp
      _ ≤ ENNReal.ofReal w*ENNReal.ofReal (u*(1+(n:ℝ))^d) := mul_le_mul_left' (hvol n) _
      _ = ENNReal.ofReal (u*g n) := by
        rw [←ENNReal.ofReal_mul (exp_pos _).le]
        congr 1
        dsimp only [g,w]
        ring
  have hg (n : ℕ) : 0≤u*g n := mul_nonneg hu (mul_nonneg (by positivity) (exp_pos _).le)
  have hbound : gaussianReal 0 1 A≤ENNReal.ofReal (u*∑' n, g n) := calc
    _ ≤ gaussianReal 0 1 (⋃ n, B n) := measure_mono hsub
    _ ≤ ∑' n, gaussianReal 0 1 (B n) := measure_iUnion_le _
    _ ≤ ∑' n, ENNReal.ofReal (u*g n) := ENNReal.tsum_le_tsum hμ
    _ = _ := by rw [←ENNReal.ofReal_tsum_of_nonneg hg (hs.mul_left u),tsum_mul_left]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rwa [ENNReal.toReal_ofReal (mul_nonneg hu (tsum_nonneg fun n => mul_nonneg (by positivity) (exp_pos _).le))] at h

#print axioms gaussian_of_shell_covers
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
