import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

/-! # Cost of weak bonds with all retained couplings of order one -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinates in S are weak. Every other coordinate belongs to the bulk set. -/
def coefficientBox (S : Finset ι) (δ : ℝ) (bulk : Set ℝ) : Set (ι → ℝ) :=
  univ.pi fun i => if i ∈ S then Icc (-δ) δ else bulk

theorem coefficientBox_mass (S : Finset ι) (δ : ℝ) (bulk : Set ℝ) :
    let γ := gaussianReal 0 1
    (Measure.pi (fun _ : ι => γ)).real (coefficientBox S δ bulk) =
      γ.real (Icc (-δ) δ)^S.card * γ.real bulk^Sᶜ.card := by
  intro γ
  let F (i : ι) := if i ∈ S then Icc (-δ) δ else bulk
  change ((Measure.pi (fun _ : ι => γ)) (univ.pi F)).toReal = _
  rw [Measure.pi_pi,ENNReal.toReal_prod,← Finset.prod_mul_prod_compl S (fun i => (γ (F i)).toReal)]
  congr 1
  · calc
      _ = ∏ _i ∈ S, γ.real (Icc (-δ) δ) := Finset.prod_congr rfl fun i hi => by
        simp only [F,if_pos hi,measureReal_def]
      _ = _ := Finset.prod_const _
  · calc
      _ = ∏ _i ∈ Sᶜ, γ.real bulk := Finset.prod_congr rfl fun i hi => by
        simp only [F,if_neg (Finset.mem_compl.mp hi),measureReal_def]
      _ = _ := Finset.prod_const _

/-- Shrinking only the erased coordinates costs a power equal to their number.
Each retained coordinate independently pays its prescribed bulk probability. -/
theorem coefficientBox_floor (S : Finset ι) (bulk : Set ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    let γ := gaussianReal 0 1
    (2*gaussianDensityFloor)^S.card * γ.real bulk^Sᶜ.card * δ^S.card ≤
      (Measure.pi (fun _ : ι => γ)).real (coefficientBox S δ bulk) := by
  intro γ
  have h := ENNReal.toReal_mono (measure_ne_top γ (Icc (-δ) δ)) (gaussianReal_Icc_lower hδ')
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg (by norm_num) hδ))] at h
  have h₁ : (2*gaussianDensityFloor)*δ ≤ γ.real (Icc (-δ) δ) :=
    (show 2*gaussianDensityFloor*δ = gaussianDensityFloor*(2*δ) by ring).trans_le h
  rw [coefficientBox_mass]
  calc
    _ = ((2*gaussianDensityFloor)*δ)^S.card * γ.real bulk^Sᶜ.card := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (by norm_num) gaussianDensityFloor_pos.le) hδ) h₁ _)
      (pow_nonneg measureReal_nonneg _)

#print axioms coefficientBox_floor
end
end GaloisForLFunctions.HTGeometry.WeakBonds
