import GaloisForLFunctions.RHTower.Sieve.FiniteAdditiveLargeSieve
import GaloisForLFunctions.RHTower.Sieve.KloostermanSum
import GaloisForLFunctions.RHTower.FieldOneFiniteCyclicFourierParseval

/-!
# Complete Kloosterman transform

The complete Kloosterman kernel is a restriction of two finite additive Fourier transforms with
unit-residue inversion between them.  Exact character orthogonality therefore gives operator norm
at most `q`: the summed output square energy is at most `q²` times the input square energy.
-/

open scoped BigOperators ComplexConjugate

namespace RHTower.Sieve

noncomputable section

/-- Additive Fourier coefficient of the input vector at a unit residue. -/
def kloostermanUnitFourierCoeff (q : ℕ) [NeZero q] (a : ZMod q → ℂ)
    (x : (ZMod q)ˣ) : ℂ :=
  ∑ m : ZMod q, a m * ZMod.stdAddChar (m * (x : ZMod q))

/-- Complete Kloosterman transform of a coefficient vector modulo `q`. -/
def kloostermanTransform (q : ℕ) [NeZero q] (a : ZMod q → ℂ)
    (n : ZMod q) : ℂ :=
  ∑ m : ZMod q, a m * kloostermanSum q m n

/-- The Kloosterman transform is the additive transform of its unit-restricted first transform. -/
theorem kloostermanTransform_eq_unitFourier
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) (n : ZMod q) :
    kloostermanTransform q a n =
      ∑ x : (ZMod q)ˣ, kloostermanUnitFourierCoeff q a x *
        ZMod.stdAddChar (n * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  unfold kloostermanTransform kloostermanUnitFourierCoeff
    kloostermanSum kloostermanPhase
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [AddChar.map_add_eq_mul]
  ring

private theorem unitInverseResidue_injective (q : ℕ) [NeZero q] :
    Function.Injective (fun x : (ZMod q)ˣ => ((x⁻¹ : (ZMod q)ˣ) : ZMod q)) := by
  intro x y h
  have hi : x⁻¹ = y⁻¹ := Units.ext h
  simpa using congrArg Inv.inv hi

/-- Exact output energy in terms of the first transform restricted to unit residues. -/
theorem sum_normSq_kloostermanTransform_eq_unitEnergy
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) :
    ∑ n : ZMod q, Complex.normSq (kloostermanTransform q a n) =
      (q : ℝ) * ∑ x : (ZMod q)ˣ,
        Complex.normSq (kloostermanUnitFourierCoeff q a x) := by
  simpa only [kloostermanTransform_eq_unitFourier] using
    sum_normSq_weighted_stdAddChar_mul_of_injective q
      (fun x : (ZMod q)ˣ => ((x⁻¹ : (ZMod q)ˣ) : ZMod q))
      (unitInverseResidue_injective q) (kloostermanUnitFourierCoeff q a)

/-- Full first additive transform before restricting to unit residues. -/
def kloostermanFullFourierCoeff (q : ℕ) [NeZero q]
    (a : ZMod q → ℂ) (x : ZMod q) : ℂ :=
  ∑ m : ZMod q, a m * ZMod.stdAddChar (x * m)

theorem kloostermanFullFourierCoeff_eq_dft
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) (x : ZMod q) :
    kloostermanFullFourierCoeff q a x = ZMod.dft a (-x) := by
  unfold kloostermanFullFourierCoeff ZMod.dft
  apply Finset.sum_congr rfl
  intro m _
  simp only [smul_eq_mul]
  rw [show -(m * -x) = x * m by ring]
  ring

theorem kloostermanUnitFourierCoeff_eq_full
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) (x : (ZMod q)ˣ) :
    kloostermanUnitFourierCoeff q a x =
      kloostermanFullFourierCoeff q a (x : ZMod q) := by
  unfold kloostermanUnitFourierCoeff kloostermanFullFourierCoeff
  apply Finset.sum_congr rfl
  intro m _
  congr 2
  ring

/-- Restriction to unit frequencies can only decrease square energy. -/
theorem sum_normSq_kloostermanUnitFourierCoeff_le_full
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) :
    (∑ x : (ZMod q)ˣ, Complex.normSq (kloostermanUnitFourierCoeff q a x)) ≤
      ∑ x : ZMod q, Complex.normSq (kloostermanFullFourierCoeff q a x) := by
  simp_rw [kloostermanUnitFourierCoeff_eq_full]
  classical
  let s : Finset (ZMod q) := Finset.univ.image fun x : (ZMod q)ˣ => (x : ZMod q)
  have hinj : Set.InjOn (fun x : (ZMod q)ˣ => (x : ZMod q))
      ((Finset.univ : Finset (ZMod q)ˣ) : Set (ZMod q)ˣ) := by
    intro x _ y _ h
    exact Units.ext h
  have heq :
      (∑ x : (ZMod q)ˣ, Complex.normSq
        (kloostermanFullFourierCoeff q a (x : ZMod q))) =
        ∑ y ∈ s, Complex.normSq (kloostermanFullFourierCoeff q a y) := by
    dsimp only [s]
    rw [Finset.sum_image hinj]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => Complex.normSq_nonneg _)

/-- Full first-transform energy is exactly `q` times input energy. -/
theorem sum_normSq_kloostermanFullFourierCoeff
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) :
    ∑ x : ZMod q, Complex.normSq (kloostermanFullFourierCoeff q a x) =
      (q : ℝ) * ∑ m : ZMod q, Complex.normSq (a m) := by
  simp_rw [kloostermanFullFourierCoeff_eq_dft]
  have hneg : (∑ x : ZMod q, Complex.normSq (ZMod.dft a (-x))) =
      ∑ x : ZMod q, Complex.normSq (ZMod.dft a x) := by
    let e : ZMod q ≃ ZMod q := Equiv.neg (ZMod q)
    exact e.sum_comp (fun x : ZMod q => Complex.normSq (ZMod.dft a x))
  rw [hneg]
  exact GaloisForLFunctions.RHTower.fieldOneFiniteCyclicFourier_parseval q a

/-- Sharp finite `L²` operator bound for the complete Kloosterman transform. -/
theorem sum_normSq_kloostermanTransform_le
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) :
    (∑ n : ZMod q, Complex.normSq (kloostermanTransform q a n)) ≤
      (q : ℝ) ^ 2 * ∑ m : ZMod q, Complex.normSq (a m) := by
  rw [sum_normSq_kloostermanTransform_eq_unitEnergy]
  have h := sum_normSq_kloostermanUnitFourierCoeff_le_full q a
  rw [sum_normSq_kloostermanFullFourierCoeff] at h
  have hq : (0 : ℝ) ≤ q := by positivity
  calc
    _ ≤ (q : ℝ) * ((q : ℝ) * ∑ m : ZMod q, Complex.normSq (a m)) :=
      mul_le_mul_of_nonneg_left h hq
    _ = _ := by ring

/-- Norm-square form of the complete Kloosterman-transform large sieve. -/
theorem sum_norm_kloostermanTransform_sq_le
    (q : ℕ) [NeZero q] (a : ZMod q → ℂ) :
    (∑ n : ZMod q, ‖kloostermanTransform q a n‖ ^ 2) ≤
      (q : ℝ) ^ 2 * ∑ m : ZMod q, ‖a m‖ ^ 2 := by
  simpa only [Complex.normSq_eq_norm_sq] using
    sum_normSq_kloostermanTransform_le q a

end

end RHTower.Sieve
