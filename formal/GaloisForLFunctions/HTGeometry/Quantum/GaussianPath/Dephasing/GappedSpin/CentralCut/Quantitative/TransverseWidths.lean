import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.BoxMass

/-! # Relative transverse widths in a Gaussian coefficient box -/
open Set MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
noncomputable section

/-- Each ordinary coordinate contributes at most nine to the sum
of squared density radii. The large central field is counted once. -/
private theorem squared_radii {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (a : ι→ℝ) {H : ℝ} (_hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ 2+(if i=i₀ then H else 0)) :
    ∑ i, (|a i|+1)^2 ≤ 9*(Fintype.card ι:ℝ)+(H+3)^2 := by
  calc
    _ ≤ ∑ i : ι, (9+(if i=i₀ then (H+3)^2 else 0)) := by
      apply sum_le_sum
      intro i _
      by_cases hi : i=i₀
      · have hb := ha i
        rw [if_pos hi] at hb ⊢
        have hs : |a i|+1 ≤ H+3 := by linarith only [hb]
        linarith only [pow_le_pow_left₀ (by positivity : 0 ≤ |a i|+1) hs 2]
      · have hb := ha i
        rw [if_neg hi,add_zero] at hb ⊢
        have hs := pow_le_pow_left₀ (by positivity : 0 ≤ |a i|+1) (by linarith only [hb] : |a i|+1 ≤ 3) 2
        linarith only [hs]
    _ = _ := by simp [sum_add_distrib,nsmul_eq_mul,mul_comm]

/-- The uniform bulk radius appears only to the number of physical
coordinates. Fourteen shrinking entries cost at most T⁷. -/
theorem gapped_box_relative_widths {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι)
    (S : Finset ι) (hS : S.card ≤ 14) (a : ι→ℝ) (hz : ∀ i∈S, a i=0)
    {H r : ℝ} (hH : 0 ≤ H) (ha : ∀ i, |a i| ≤ 2+(if i=i₀ then H else 0))
    (hr : 0 < r) (hr₁ : r ≤ 1) (T : ℝ) (hT : 1 ≤ T) :
    let M := Fintype.card ι
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    ∃ E : Set (ι→ℝ), MeasurableSet E ∧
      (2*(sqrt (2*π))⁻¹*r)^M * exp (-(9*(M:ℝ)+(H+3)^2)/2) ≤
        ((1800:ℝ)^14*T^7)*μ.real E ∧
      ∀ x∈E, (∀ i, |x i-a i| ≤ r) ∧ ∀ i∈S, |x i| ≤ r/(1800*sqrt T) := by
  intro M μ
  let s := 1800*sqrt T
  have hs₀ := one_le_sqrt.mpr hT
  have hs : 1 ≤ s := by dsimp only [s]; linarith only [hs₀]
  let w (i : ι) := if i∈S then r/s else r
  let E := Set.univ.pi fun i => Icc (a i-w i) (a i+w i)
  have hm : MeasurableSet E := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
  refine ⟨E,hm,?_,?_⟩
  · have he := gaussian_rectangular_floor S a hr hr₁ hs
    have hb := squared_radii i₀ a hH ha
    have hscale : s^S.card ≤ (1800:ℝ)^14*T^7 := calc
      _ ≤ s^14 := pow_le_pow_right₀ hs hS
      _ = _ := by
        rw [show s=1800*sqrt T from rfl,mul_pow,show (sqrt T)^14=((sqrt T)^2)^7 by ring,
          sq_sqrt (zero_le_one.trans hT)]
    calc
      _ ≤ (2*(sqrt (2*π))⁻¹*r)^M * exp (-(∑ i, (|a i|+1)^2)/2) :=
        mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hb])) (by positivity)
      _ ≤ s^S.card*μ.real E := he
      _ ≤ _ := mul_le_mul_of_nonneg_right hscale measureReal_nonneg
  · intro x hx
    have hwidth (i : ι) : |x i-a i| ≤ w i := by
      have hi : x i∈Icc (a i-w i) (a i+w i) := hx i (Set.mem_univ i)
      exact abs_le.mpr ⟨by linarith only [hi.1],by linarith only [hi.2]⟩
    constructor
    · intro i
      by_cases hi : i∈S
      · exact (hwidth i).trans ((if_pos hi).le.trans (div_le_self hr.le hs))
      · exact (hwidth i).trans_eq (if_neg hi)
    · intro i hi
      have hb := hwidth i
      rw [hz i hi,sub_zero,show w i=r/s from if_pos hi] at hb
      exact hb

#print axioms gapped_box_relative_widths
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
