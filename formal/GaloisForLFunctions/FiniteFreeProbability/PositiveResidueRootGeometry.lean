import GaloisForLFunctions.FiniteFreeProbability.EulerRootFilters
import Mathlib.Algebra.BigOperators.Option

/-!
# Geometry of zeros of positive-residue logarithmic derivatives

Shi's Lemma 2.2 uses positive residues to localize zeros in a convex hull.
The same barycentric equation gives an exact squared-distance identity at
every center. Inside a disk containing the poles it measures a strictly
positive radial deficit, even if every pole is on the boundary.
-/

open Finset Polynomial
open scoped ComplexConjugate RealInnerProductSpace

namespace FiniteFreeProbability

noncomputable section

variable {ι : Type*} (s : Finset ι) (r : ι → ℂ) (a : ι → ℝ)

/-- Logarithmic field of finitely many poles with specified real residues. -/
def residueField (z : ℂ) : ℂ := ∑ i ∈ s, (a i : ℂ) / (z-r i)

/-- Inverse-square weights evaluated at the observation point. -/
def poleWeight (z : ℂ) (i : ι) : ℝ := a i / ‖z-r i‖^2

private theorem pole_force (z : ℂ) (hz : ∀ i ∈ s, z ≠ r i) :
    ∑ i ∈ s, poleWeight r a z i • (z-r i) = conj (residueField s r a z) := by
  rw [residueField, map_sum]
  apply sum_congr rfl
  intro i hi
  have h : z-r i ≠ 0 := sub_ne_zero.mpr (hz i hi)
  simp [poleWeight, Complex.real_smul, ← Complex.conj_mul', field]

private theorem weight_sum_pos (z : ℂ) (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i)
    (hz : ∀ i ∈ s, z ≠ r i) : 0 < ∑ i ∈ s, poleWeight r a z i :=
  sum_pos (fun i hi => div_pos (ha i hi) (sq_pos_of_pos (norm_pos_iff.mpr
    (sub_ne_zero.mpr (hz i hi))))) hs

/-- Every regular field zero is the inverse-square barycenter of its poles. -/
theorem residue_zero_eq_centerMass (z : ℂ) (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i)
    (hz : ∀ i ∈ s, z ≠ r i) (hzero : residueField s r a z = 0) :
    z = s.centerMass (poleWeight r a z) r := by
  have hf := pole_force s r a z hz
  rw [hzero, map_zero] at hf
  calc
    z = s.centerMass (poleWeight r a z) (fun _ => z) := by
      rw [Finset.centerMass, ← Finset.sum_smul, inv_smul_smul₀ (weight_sum_pos s r a z hs ha hz).ne']
    _ = s.centerMass (poleWeight r a z) (fun i => z-r i) + s.centerMass (poleWeight r a z) r := by
      simp only [Finset.centerMass, ← smul_add, ← Finset.sum_add_distrib, sub_add_cancel]
    _ = _ := by simp only [Finset.centerMass, hf, smul_zero, zero_add]

/-- Weighted Gauss–Lucas inclusion for arbitrary positive real residues, including
repeated pole locations. -/
theorem residue_zero_mem_hull (z : ℂ) (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 < a i)
    (hz : ∀ i ∈ s, z ≠ r i) (hzero : residueField s r a z = 0) :
    z ∈ convexHull ℝ (r '' (s : Set ι)) := by
  have hmem : s.centerMass (poleWeight r a z) r ∈ convexHull ℝ (r '' (s : Set ι)) :=
    s.centerMass_mem_convexHull
      (fun i hi => div_nonneg (ha i hi).le (sq_nonneg _)) (weight_sum_pos s r a z hs ha hz)
      (fun i hi => ⟨i, hi, rfl⟩)
  rwa [← residue_zero_eq_centerMass s r a z hs ha hz hzero] at hmem

/-- At a regular zero the weighted excess in squared distance to any center equals
the total residue. The identity also holds for signed residues. -/
theorem residue_zero_radial_identity (z c : ℂ) (hz : ∀ i ∈ s, z ≠ r i)
    (hzero : residueField s r a z = 0) :
    ∑ i ∈ s, poleWeight r a z i * (‖r i-c‖^2-‖z-c‖^2) = ∑ i ∈ s, a i := by
  have hf := pole_force s r a z hz
  rw [hzero, map_zero] at hf
  have hinner := congrArg (fun v : ℂ => ⟪z-c,v⟫) hf
  simp only [inner_sum, real_inner_smul_right, inner_zero_right] at hinner
  have hterm (i : ι) (hi : i ∈ s) : poleWeight r a z i * (‖r i-c‖^2-‖z-c‖^2) =
      a i - 2 * (poleWeight r a z i * ⟪z-c,z-r i⟫) := by
    rw [show r i-c = (z-c)-(z-r i) by abel, norm_sub_sq_real]
    have he : poleWeight r a z i * ‖z-r i‖^2 = a i :=
      div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz i hi))))
    linarith only [he]
  rw [sum_congr rfl hterm, sum_sub_distrib, ← mul_sum, hinner, mul_zero, sub_zero]

/-- Quantitative open-disk Gauss–Lucas bound at every regular field zero. -/
theorem residue_zero_disk_deficit (z c : ℂ) (R : ℝ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i) (hz : ∀ i ∈ s, z ≠ r i) (hzero : residueField s r a z = 0)
    (hR : ∀ i ∈ s, ‖r i-c‖ ≤ R) :
    (∑ i ∈ s, a i) / (∑ i ∈ s, poleWeight r a z i) ≤ R^2-‖z-c‖^2 := by
  apply (div_le_iff₀ (weight_sum_pos s r a z hs ha hz)).mpr
  rw [← residue_zero_radial_identity s r a z c hz hzero, mul_comm, sum_mul]
  apply sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right
    (pow_le_pow_left₀ (norm_nonneg _) (hR i hi) 2) _) (div_nonneg (ha i hi).le (sq_nonneg _))

/-- Every zero away from the poles lies in the open disk whenever all poles belong
to its closure. -/
theorem residue_zero_in_open_disk (z c : ℂ) (R : ℝ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i) (hz : ∀ i ∈ s, z ≠ r i) (hzero : residueField s r a z = 0)
    (hR : ∀ i ∈ s, ‖r i-c‖ ≤ R) : ‖z-c‖ < R := by
  have hd := residue_zero_disk_deficit s r a z c R hs ha hz hzero hR
  have hpos := (div_pos (sum_pos ha hs) (weight_sum_pos s r a z hs ha hz)).trans_le hd
  obtain ⟨i, hi⟩ := hs
  nlinarith only [hpos, norm_nonneg (z-c), (norm_nonneg _).trans (hR i hi)]


end

end FiniteFreeProbability
