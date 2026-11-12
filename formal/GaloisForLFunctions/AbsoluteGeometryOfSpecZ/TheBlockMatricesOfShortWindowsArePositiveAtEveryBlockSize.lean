import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.StepPacketMassAndGroundEnergy
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartOfTheFirstBlockMatricesIsLorentzian
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheMatrixOfAStepPacketIsTheMixedDifferenceOfItsWindows

/-!
# The block matrices of short windows are positive at every block size

Weil's form is at least `1/5000` times the mass on the tests supported in an interval of length
`181/250`, which is longer than `log 2`. Smoothing carries the ground energy of an aperture to
the bounded packets of every shorter window, so the margin holds on step packets, whatever the
number of their blocks:

* `𝔚_Q ≥ (1/5000) Σ σ_j²` on the step packets of the unit blocks of `(R, R + J]` for every
  block size `R ≥ 1`, every `J` with `50 J ≤ 53 R` and every `Q ≥ 2`
  (`packetForm_stepPacket_ge_of_short`): the window has ratio at most `103/50`, and
  `log(103/50) < 181/250`;
* the block matrix of the window is positive definite with this margin
  (`sum_blockMatrix_ge_of_short`), and so is its neutral part on each of the two hyperplanes
  where a charge of the packet vanishes (`sum_neutralBlock_ge_of_short`).

The dyadic windows `(R, 2R]` carry no contact. The windows of ratio above two carry the contacts
of the prime `2`: the blocks `b ≥ 2R` are joined to their images `⌊b/2⌋`.
-/

open Finset MeasureTheory Set Zeta23

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- A combination of nested flat packets inherits the ground energy of every aperture wider than
half the logarithmic length of its window. -/
theorem groundEnergy_mul_nested_mass_le_packetForm_of_log_lt
    {ι : Type*} {s : Finset ι} {x : ι → ℕ} {x₀ X Q : ℕ}
    (hx₀ : 1 ≤ x₀) (hx : ∀ j ∈ s, x₀ ≤ x j ∧ x j ≤ X) (τ : ι → ℝ)
    {A : _root_.RHTower.SuzukiPositiveAperture}
    (hA : Real.log X - Real.log x₀ < 2 * A.1)
    (hQ : Real.log X - Real.log x₀ < Real.log ((Q : ℝ) + 1)) :
    _root_.RHTower.ccmRestrictedWeilGroundEnergy A *
        packetAutocorr (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) 0 ≤
      packetForm Q (fun u => ∑ j ∈ s, τ j * flatPacket x₀ (x j) u) := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  apply groundEnergy_mul_packetAutocorr_le_packetForm
    (M := ∑ j ∈ s, |τ j| * Real.exp (Real.log (x j) / 2))
    (l := Real.log x₀) (r := Real.log X)
  · exact Finset.measurable_sum _ fun j _ => (measurable_flatPacket _ _).const_mul (τ j)
  · intro u
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_flatPacket_le _ _ _) (abs_nonneg _)
  · -- the support lies in the logarithmic window
    intro u hu
    obtain ⟨j, hj, hne⟩ : ∃ j ∈ s, τ j * flatPacket x₀ (x j) u ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      exact hu (Finset.sum_eq_zero hcon)
    have hfp : flatPacket (x₀ : ℝ) (x j) u ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    have hmem : u ∈ Ioc (Real.log x₀) (Real.log (x j)) := by
      by_contra hnot
      exact hfp (by simp only [flatPacket]; exact indicator_of_notMem hnot _)
    have hxj0 : (0 : ℝ) < x j := hx₀'.trans_le (by exact_mod_cast (hx j hj).1)
    have hlog : Real.log (x j) ≤ Real.log X :=
      Real.log_le_log hxj0 (by exact_mod_cast (hx j hj).2)
    exact ⟨hmem.1.le, hmem.2.trans hlog⟩
  · exact hA
  · exact hQ
  · exact integrableOn_levyJump_step hx₀ (fun j hj => (hx j hj).1) τ

/-- A window of ratio at most `103/50` is shorter than `181/250` in the logarithmic
coordinate: `log 2 + log(103/100) < 0.6932 + 0.03`. -/
theorem log_window_lt {R J : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R) :
    Real.log ((R + J : ℕ) : ℝ) - Real.log R < 181 / 250 := by
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hJ' : (50 : ℝ) * J ≤ 53 * R := by exact_mod_cast hJ
  have hle : ((R + J : ℕ) : ℝ) ≤ 2 * (103 / 100) * R := by
    push_cast
    linarith
  have hpos : (0 : ℝ) < ((R + J : ℕ) : ℝ) := by
    push_cast
    linarith [show (0 : ℝ) ≤ J from Nat.cast_nonneg J]
  have h1 := Real.log_le_log hpos hle
  rw [Real.log_mul (by norm_num) hR'.ne', Real.log_mul (by norm_num) (by norm_num)] at h1
  have h3 : Real.log (103 / 100 : ℝ) ≤ 103 / 100 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 := Real.log_two_lt_d9
  linarith

/-- **Weil's form has the margin `1/5000` on the step packets of every window of ratio at most
`103/50`, at every block size.** -/
theorem packetForm_stepPacket_ge_of_short {R J Q : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R)
    (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    1 / 5000 * ∑ j ∈ range J, σ j ^ 2 ≤ packetForm Q (stepPacket R J σ) := by
  obtain ⟨A, hA⟩ : ∃ A : _root_.RHTower.SuzukiPositiveAperture, A.1 = 181 / 500 :=
    ⟨⟨181 / 500, by norm_num⟩, rfl⟩
  have hlen := log_window_lt hR hJ
  have hμ : 1 / 5000 ≤ _root_.RHTower.ccmRestrictedWeilGroundEnergy A :=
    SelectivePositivityAndThresholdLaws.one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths
      hA.le
  have hlogQ : Real.log ((R + J : ℕ) : ℝ) - Real.log R < Real.log ((Q : ℝ) + 1) := by
    have h3 := log_three_mem.1
    have hQ' : (3 : ℝ) ≤ (Q : ℝ) + 1 := by
      have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hQ'
    linarith
  have hfloor : _root_.RHTower.ccmRestrictedWeilGroundEnergy A * ∑ j ∈ range J, σ j ^ 2 ≤
      packetForm Q (stepPacket R J σ) := by
    rw [← packetAutocorr_stepPacket_zero hR J σ]
    simp only [stepPacket_eq_nested hR J σ]
    exact groundEnergy_mul_nested_mass_le_packetForm_of_log_lt hR (nested_bounds R J)
      (nestedCoeff J σ) (by rw [hA]; linarith) hlogQ
  exact (mul_le_mul_of_nonneg_right hμ (Finset.sum_nonneg fun j _ => sq_nonneg _)).trans hfloor

/-- **The block matrix of a window of ratio at most `103/50` is positive definite with the
margin `1/5000`, at every block size.** -/
theorem sum_blockMatrix_ge_of_short {R J Q : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R)
    (hQ : 2 ≤ Q) (σ : ℕ → ℝ) :
    1 / 5000 * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * blockMatrix Q (R + j) (R + l) := by
  rw [← packetForm_stepPacket_eq_sum_blockMatrix hR Q J σ]
  exact packetForm_stepPacket_ge_of_short hR hJ hQ σ

/-- **The neutral part of the block matrix of a short window is positive where a charge
vanishes**, with the margin of the block matrix. -/
theorem sum_neutralBlock_ge_of_short {R J Q : ℕ} (hR : 1 ≤ R) (hJ : 50 * J ≤ 53 * R)
    (hQ : 2 ≤ Q) {σ : ℕ → ℝ}
    (hσ : ∑ j ∈ range J, σ j = 0 ∨ ∑ j ∈ range J, σ j * blockDegree (R + j) = 0) :
    1 / 5000 * ∑ j ∈ range J, σ j ^ 2 ≤
      ∑ j ∈ range J, ∑ l ∈ range J, σ j * σ l * neutralBlock Q (R + j) (R + l) := by
  rw [sum_neutralBlock_eq_of_charge_zero hσ]
  exact sum_blockMatrix_ge_of_short hR hJ hQ σ

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
