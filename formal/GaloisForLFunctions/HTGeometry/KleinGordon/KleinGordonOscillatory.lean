import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonFreeMultipliers

/-!
# A clock in a weak static potential is purely oscillatory

The free multipliers lie on the unit circle because the free evolution and its inverse are both
isometries. The same conclusion needs much less: **two-sided power boundedness**. If `a` is invertible
and the powers of `a` and of `a⁻¹` are separately bounded, then no spectral value of `a` can lie off
the unit circle — `‖k‖ ≤ 1` from the powers of `a`, and `‖k⁻¹‖ ≤ 1` from those of `a⁻¹`, because the
spectrum of an inverse is the inverse of the spectrum.

That applies to a clock in a weak static real potential. Its monodromy over `T` and over `−T` are
inverse to each other, and statement 319 bounds the powers of both by `√((1+b)/(1−b))`. So all of its
Floquet multipliers lie on the unit circle: such a clock oscillates, with no secular growth and no
decay — exactly what an instrument that keeps time must do.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Topology

/-! ## Two-sided power bounds put the spectrum on the circle -/

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **A power bound confines the spectrum to the closed unit disc.** -/
theorem norm_le_one_of_mem_spectrum_of_pow_bound' {a : A} (h1 : ‖(1 : A)‖ ≤ 1)
    {C : ℝ} (hC : ∀ n : ℕ, ‖a ^ n‖ ≤ C) {k : ℂ} (hk : k ∈ spectrum ℂ a) : ‖k‖ ≤ 1 := by
  have hpow : ∀ n : ℕ, ‖k‖ ^ n ≤ C := by
    intro n
    have hmem : k ^ n ∈ spectrum ℂ (a ^ n) := spectrum.pow_mem_pow _ n hk
    have hle := spectrum.norm_le_norm_mul_of_mem hmem
    have hstep : ‖a ^ n‖ * ‖(1 : A)‖ ≤ C * 1 :=
      mul_le_mul (hC n) h1 (norm_nonneg _) (le_trans (norm_nonneg _) (hC n))
    rw [mul_one] at hstep
    rw [← norm_pow]
    exact hle.trans hstep
  by_contra hlt
  push Not at hlt
  have hdiv : Tendsto (fun n : ℕ => ‖k‖ ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hlt
  obtain ⟨n, hn⟩ := (hdiv.eventually_gt_atTop C).exists
  exact absurd (hpow n) (not_le.mpr hn)

/-- **Two-sided power boundedness puts the whole spectrum on the unit circle.** -/
theorem norm_eq_one_of_mem_spectrum_of_inverse {a b : A} (h1 : ‖(1 : A)‖ ≤ 1)
    (hab : a * b = 1) (hba : b * a = 1) {C C' : ℝ}
    (hC : ∀ n : ℕ, ‖a ^ n‖ ≤ C) (hC' : ∀ n : ℕ, ‖b ^ n‖ ≤ C')
    {k : ℂ} (hk : k ∈ spectrum ℂ a) : ‖k‖ = 1 := by
  set u : Aˣ := ⟨a, b, hab, hba⟩ with hudef
  have hval : (u : A) = a := rfl
  have hvalinv : ((u⁻¹ : Aˣ) : A) = b := rfl
  have hu : IsUnit a := ⟨u, rfl⟩
  have hk0 : k ≠ 0 := by
    intro hzero
    rw [hzero] at hk
    exact absurd hu (spectrum.not_isUnit_of_zero_mem (R := ℂ) hk)
  have hle : ‖k‖ ≤ 1 := norm_le_one_of_mem_spectrum_of_pow_bound' h1 hC hk
  have hmem : k⁻¹ ∈ (spectrum ℂ (u : A))⁻¹ := by
    rw [Set.mem_inv, inv_inv, hval]
    exact hk
  rw [spectrum.map_inv u, hvalinv] at hmem
  have hle' : ‖k⁻¹‖ ≤ 1 := norm_le_one_of_mem_spectrum_of_pow_bound' h1 hC' hmem
  rw [norm_inv] at hle'
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
  have hmul := mul_le_mul_of_nonneg_left hle' hkpos.le
  rw [mul_inv_cancel₀ hkpos.ne', mul_one] at hmul
  exact le_antisymm hle hmul

end BanachAlgebra

/-! ## A clock in a weak static potential -/

section StaticPotential

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {W₀ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b T : ℝ}

/-- The monodromies of a constant background over opposite periods are inverse to each other. -/
theorem kgMonodromy_const_mul_inv (hb0 : 0 ≤ b)
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x) :
    kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T
        * kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs (-T) = 1
      ∧ kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs (-T)
        * kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T = 1 := by
  have hper := periodic_const W₀ T
  constructor
  · refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_right_inverse hb0 hWb hWs hper v
  · refine ContinuousLinearMap.ext fun v => ?_
    exact kgPeriodMap_left_inverse hb0 hWb hWs hper v

/-- **A clock in a weak static real potential is purely oscillatory.** All of its Floquet multipliers
lie on the unit circle: no secular growth and no decay. -/
theorem norm_eq_one_of_mem_spectrum_of_small_potential (hb0 : 0 ≤ b) (hb1 : b < 1) (hW : ‖W₀‖ ≤ b)
    (hsa : ∀ x y : Lp ℂ 2 (volume : Measure E), (inner ℂ (W₀ x) y : ℂ) = inner ℂ x (W₀ y))
    (hWb : ∀ r : ℝ, ‖(fun _ : ℝ => W₀) r‖ ≤ b)
    (hWs : ∀ x : Lp ℂ 2 (volume : Measure E), Continuous fun r : ℝ => (fun _ : ℝ => W₀) r x)
    {k : ℂ} (hk : k ∈ spectrum ℂ (kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T)) :
    ‖k‖ = 1 := by
  obtain ⟨hab, hba⟩ := kgMonodromy_const_mul_inv (T := T) hb0 hWb hWs
  have hC : ∀ n : ℕ, ‖kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs T ^ n‖
      ≤ Real.sqrt ((1 + b) / (1 - b)) := fun n =>
    norm_kgMonodromy_pow_le_of_small (T := T) hb0 hb1 hW hsa hWb hWs n
  have hC' : ∀ n : ℕ, ‖kgMonodromy (fun _ : ℝ => W₀) b hb0 hWb hWs (-T) ^ n‖
      ≤ Real.sqrt ((1 + b) / (1 - b)) := fun n =>
    norm_kgMonodromy_pow_le_of_small (T := -T) hb0 hb1 hW hsa hWb hWs n
  exact norm_eq_one_of_mem_spectrum_of_inverse (le_of_eq norm_one_kgEnergy) hab hba hC hC' hk

end StaticPotential

end GaloisForLFunctions.HTGeometry
