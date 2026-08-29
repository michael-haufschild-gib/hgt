import GaloisForLFunctions.RHTower.ChenGuptaLiAffinePoisson
import GaloisForLFunctions.RHTower.CommonProfileAnchorResponseMobius
import GaloisForLFunctions.RHTower.CCMRationalArchimedeanSchwartzLattice

/-!
# The physical occupancy, its Euler vacuum, and the anchored Fourier response

The occupancy of the reducible quadratic `m (m + h)` at a modulus `l` is the physical profile
summed over the integers the modulus divides.  Splitting the integers into residue classes and
applying Poisson summation on each root progression expresses the occupancy as the frequency sum
of the transform against the root response.  The zero frequency contributes exactly the Euler
vacuum, so the occupancy defect is the nonzero-frequency anchored response.

This is the exact bridge from the arithmetic Möbius layer to the physical profile.
-/

open scoped BigOperators FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-! ## Residue classes of the integers -/

/-- The residue-class equivalence of the integers modulo a positive modulus. -/
def intResidueClassesEquiv (N : ℕ) [NeZero N] : ZMod N × ℤ ≃ ℤ where
  toFun p := (p.1.val : ℤ) + N * p.2
  invFun n := ((n : ZMod N), (n - (((n : ZMod N)).val : ℤ)) / N)
  left_inv := by
    rintro ⟨j, m⟩
    have hcast : ((((j.val : ℤ) + N * m : ℤ)) : ZMod N) = j := by
      push_cast
      simp
    have hN : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    refine Prod.ext hcast ?_
    simp only [hcast]
    rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hN]
  right_inv := by
    intro n
    have hdvd : (N : ℤ) ∣ (n - (((n : ZMod N)).val : ℤ)) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp
    show ((((n : ZMod N)).val : ℤ)) + (N : ℤ) * ((n - (((n : ZMod N)).val : ℤ)) / N) = n
    rw [mul_comm, Int.ediv_mul_cancel hdvd]
    ring

@[simp] theorem intResidueClassesEquiv_apply (N : ℕ) [NeZero N] (p : ZMod N × ℤ) :
    intResidueClassesEquiv N p = (p.1.val : ℤ) + N * p.2 := rfl

/-- **Summing the integers by residue classes.** -/
theorem Int.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R]
    [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] {f : ℤ → R} (hf : Summable f)
    (N : ℕ) [NeZero N] :
    ∑' n : ℤ, f n = ∑ j : ZMod N, ∑' m : ℤ, f ((j.val : ℤ) + N * m) := by
  rw [← (intResidueClassesEquiv N).tsum_eq f, Summable.tsum_prod, tsum_fintype]
  · rfl
  · exact hf.comp_injective (intResidueClassesEquiv N).injective

/-! ## The physical occupancy and its Euler vacuum -/

/-- A Schwartz profile is summable along the integers. -/
theorem summable_schwartz_int (W : 𝓢(ℝ, ℂ)) : Summable fun m : ℤ => W (m : ℝ) := by
  have hnorm := GaloisForLFunctions.RHTower.ccmRationalArchimedeanSchwartz_lattice_summable
    W (a := 1) one_ne_zero
  simp only [one_mul] at hnorm
  exact hnorm.of_norm

/-- The physical occupancy of the reducible quadratic at modulus `l`. -/
def occupancy (W : 𝓢(ℝ, ℂ)) (l : ℕ) (h : ℤ) : ℂ :=
  ∑' m : ℤ, (if (l : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0)

theorem summable_occupancyTerm (W : 𝓢(ℝ, ℂ)) (l : ℕ) (h : ℤ) :
    Summable fun m : ℤ => (if (l : ℤ) ∣ m * (m + h) then W (m : ℝ) else 0) := by
  classical
  refine ((summable_schwartz_int W).indicator {m : ℤ | (l : ℤ) ∣ m * (m + h)}).congr ?_
  intro m
  rw [Set.indicator_apply]
  rfl

/-- The divisibility condition depends only on the residue class. -/
theorem dvd_quadratic_iff_zmod {l : ℕ} [NeZero l] (h : ℤ) (m : ℤ) :
    (l : ℤ) ∣ m * (m + h) ↔ ((m : ZMod l) * ((m : ZMod l) + (h : ZMod l)) = 0) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rfl

/-- **The occupancy is the root-class periodization.** -/
theorem occupancy_eq_sum_roots (W : 𝓢(ℝ, ℂ)) (l : ℕ) [NeZero l] (h : ℤ) :
    occupancy W l h =
      ∑ r : quadraticCongruenceRoots l h,
        ∑' k : ℤ, W ((((r.1.val : ℤ) + l * k : ℤ) : ℝ)) := by
  classical
  rw [occupancy, Int.sumByResidueClasses (summable_occupancyTerm W l h) l]
  have hclass : ∀ j : ZMod l,
      (∑' k : ℤ, (if (l : ℤ) ∣ ((j.val : ℤ) + l * k) * (((j.val : ℤ) + l * k) + h) then
          W ((((j.val : ℤ) + l * k : ℤ) : ℝ)) else 0)) =
        if j * (j + (h : ZMod l)) = 0 then
          ∑' k : ℤ, W ((((j.val : ℤ) + l * k : ℤ) : ℝ)) else 0 := by
    intro j
    have hcond : ∀ k : ℤ, ((l : ℤ) ∣ ((j.val : ℤ) + l * k) * (((j.val : ℤ) + l * k) + h)) ↔
        j * (j + (h : ZMod l)) = 0 := by
      intro k
      rw [dvd_quadratic_iff_zmod]
      have : (((j.val : ℤ) + l * k : ℤ) : ZMod l) = j := by push_cast; simp
      rw [this]
    by_cases hj : j * (j + (h : ZMod l)) = 0
    · rw [if_pos hj]
      exact tsum_congr fun k => if_pos ((hcond k).2 hj)
    · rw [if_neg hj]
      rw [show (fun k : ℤ => (if (l : ℤ) ∣ ((j.val : ℤ) + l * k) * (((j.val : ℤ) + l * k) + h)
          then W ((((j.val : ℤ) + l * k : ℤ) : ℝ)) else 0)) = fun _ : ℤ => (0 : ℂ) from by
        funext k
        exact if_neg (fun hcon => hj ((hcond k).1 hcon))]
      exact tsum_zero
  rw [Finset.sum_congr rfl fun j _ => hclass j, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun j => by simp) _

/-! ## Poisson summation on each root class -/

/-- A finite sum of summable families is summable. -/
theorem summable_finsetSum {ι M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] {s : Finset ι} {f : ι → ℤ → M} (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b : ℤ => ∑ i ∈ s, f i b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using summable_zero
  | @insert i s hi ih =>
      have h1 : Summable (f i) := hf i (Finset.mem_insert_self i s)
      have h2 : Summable fun b : ℤ => ∑ j ∈ s, f j b :=
        ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      simpa only [Finset.sum_insert hi] using h1.add h2

/-- The unit physical length. -/
def unitLength : CGLPositiveLength := ⟨1, one_pos⟩

/-- A positive modulus packaged for the affine Poisson layer. -/
def modulusOf (l : ℕ) [NeZero l] : CGLPositiveModulus :=
  ⟨l, Nat.pos_of_ne_zero (NeZero.ne l)⟩

/-- The dual lattice spacing of the modulus. -/
def fourierScale (l : ℕ) : ℝ := ((1 : ℕ) : ℝ) / ((l : ℕ) : ℝ)

theorem cglAffineFourierScale_unit (Q : CGLPositiveModulus) :
    cglAffineFourierScale unitLength Q = fourierScale Q.value := rfl

theorem fourierScale_eq_inv (l : ℕ) : fourierScale l = ((l : ℝ))⁻¹ := by
  rw [fourierScale]
  simp

/-- The Fourier-side term of the Poisson image at frequency `m`. -/
def fourierTerm (W : 𝓢(ℝ, ℂ)) (l : ℕ) (m : ℤ) : ℂ :=
  ((fourierScale l : ℝ) : ℂ) * 𝓕 (W : ℝ → ℂ) (fourierScale l * (m : ℝ))

/-- **Poisson summation on one residue progression.** -/
theorem tsum_residueClass_eq (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (a : ZMod Q.value) :
    (∑' k : ℤ, W ((((a.val : ℤ) + Q.value * k : ℤ) : ℝ))) =
      ∑' m : ℤ, ZMod.stdAddChar (a * (m : ZMod Q.value)) * fourierTerm W Q.value m := by
  have h := cglAffineResidue_tsum_eq_tsum_fourier_addChar W unitLength Q a
  calc (∑' k : ℤ, W ((((a.val : ℤ) + Q.value * k : ℤ) : ℝ)))
      = ∑' k : ℤ, W ((((a.val : ℕ) : ℝ) + (Q.value : ℝ) * (k : ℝ)) /
          ((unitLength).value : ℝ)) := by
        refine tsum_congr fun k => ?_
        congr 1
        show ((((a.val : ℤ) + (Q.value : ℤ) * k : ℤ)) : ℝ) =
          (((a.val : ℕ) : ℝ) + ((Q.value : ℕ) : ℝ) * (k : ℝ)) / ((1 : ℕ) : ℝ)
        push_cast
        ring
    _ = _ := h

/-- Each root class contributes a summable Fourier family. -/
theorem summable_residueClass_fourier (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus)
    (a : ZMod Q.value) :
    Summable fun m : ℤ =>
      ZMod.stdAddChar (a * (m : ZMod Q.value)) * fourierTerm W Q.value m := by
  refine (cglSchwartz_summable_fourier_int
    (cglAffineResidueSchwartz W unitLength Q a)).congr fun m => ?_
  rw [cglAffineResidueSchwartz_fourier W unitLength Q a (m : ℝ),
    cglAffineFourierPhase_eq_stdAddChar_mul]
  rfl

/-- The root sum is the class sum of standard additive characters. -/
theorem rootSum_eq_sum_stdAddChar (l : ℕ) [NeZero l] (h : ℤ) (m : ℤ) :
    quadraticCongruenceRootSumTotal l h m =
      ∑ r : quadraticCongruenceRoots l h, ZMod.stdAddChar (r.1 * (m : ZMod l)) := by
  rw [quadraticCongruenceRootSumTotal_of_ne_zero (NeZero.ne l), quadraticCongruenceRootSum]
  exact Finset.sum_congr rfl fun r _ => by rw [mul_comm]

/-- **The occupancy as a frequency sum.**  Summing the Poisson image over the root classes gives
the root response against the transform at the reduced frequencies. -/
theorem occupancy_eq_tsum_rootSum (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    occupancy W Q.value h =
      ∑' m : ℤ, quadraticCongruenceRootSumTotal Q.value h m * fourierTerm W Q.value m := by
  have hclasses : ∑ r : quadraticCongruenceRoots Q.value h,
      (∑' k : ℤ, W ((((r.1.val : ℤ) + Q.value * k : ℤ) : ℝ))) =
      ∑ r : quadraticCongruenceRoots Q.value h,
        ∑' m : ℤ, ZMod.stdAddChar (r.1 * (m : ZMod Q.value)) * fourierTerm W Q.value m :=
    Finset.sum_congr rfl fun r _ => tsum_residueClass_eq W Q r.1
  have hswap : (∑ r : quadraticCongruenceRoots Q.value h,
      ∑' m : ℤ, ZMod.stdAddChar (r.1 * (m : ZMod Q.value)) * fourierTerm W Q.value m) =
      ∑' m : ℤ, ∑ r : quadraticCongruenceRoots Q.value h,
        ZMod.stdAddChar (r.1 * (m : ZMod Q.value)) * fourierTerm W Q.value m :=
    (Summable.tsum_finsetSum (fun r _ => summable_residueClass_fourier W Q r.1)).symm
  rw [occupancy_eq_sum_roots W Q.value h, hclasses, hswap]
  refine tsum_congr fun m => ?_
  rw [← Finset.sum_mul, ← rootSum_eq_sum_stdAddChar Q.value h m]

/-! ## The Euler vacuum and the occupancy defect -/

/-- `delta_h(e_l)`: the occupancy minus its Euler vacuum. -/
def occupancyDefect (W : 𝓢(ℝ, ℂ)) (l : ℕ) (h : ℤ) : ℂ :=
  occupancy W l h - 𝓕 (W : ℝ → ℂ) 0 * rootDensity l h

theorem summable_rootSum_fourier (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    Summable fun m : ℤ =>
      quadraticCongruenceRootSumTotal Q.value h m * fourierTerm W Q.value m := by
  have hsum := summable_finsetSum
    (s := (Finset.univ : Finset (quadraticCongruenceRoots Q.value h)))
    (f := fun (r : quadraticCongruenceRoots Q.value h) (m : ℤ) =>
      ZMod.stdAddChar (r.1 * (m : ZMod Q.value)) * fourierTerm W Q.value m)
    (fun r _ => summable_residueClass_fourier W Q r.1)
  refine hsum.congr fun m => ?_
  rw [← Finset.sum_mul, ← rootSum_eq_sum_stdAddChar Q.value h m]

theorem fourierTerm_eq (W : 𝓢(ℝ, ℂ)) (l : ℕ) (m : ℤ) :
    fourierTerm W l m = ((l : ℂ))⁻¹ * 𝓕 (W : ℝ → ℂ) ((m : ℝ) / l) := by
  rw [fourierTerm, fourierScale_eq_inv, inv_mul_eq_div]
  push_cast
  rw [div_eq_inv_mul]

/-- **`(PF1)`.**  Poisson summation on the root progressions expresses the occupancy defect as the
nonzero-frequency response of the transform against the root sums.  The zero frequency is exactly
the Euler vacuum. -/
theorem occupancyDefect_eq_tsum (W : 𝓢(ℝ, ℂ)) (Q : CGLPositiveModulus) (h : ℤ) :
    occupancyDefect W Q.value h =
      ∑' m : ℤ, (if m = 0 then 0 else
        ((Q.value : ℂ))⁻¹ * (𝓕 (W : ℝ → ℂ) ((m : ℝ) / Q.value) *
          quadraticCongruenceRootSumTotal Q.value h m)) := by
  classical
  have hsum := summable_rootSum_fourier W Q h
  rw [occupancyDefect, occupancy_eq_tsum_rootSum W Q h, hsum.tsum_eq_add_tsum_ite (0 : ℤ)]
  have hS : quadraticCongruenceRootSumTotal Q.value h 0 =
      (quadraticCongruenceRootCountTotal Q.value h : ℂ) := by
    rw [quadraticCongruenceRootSumTotal_of_ne_zero (NeZero.ne Q.value),
      quadraticCongruenceRootCountTotal_of_ne_zero (NeZero.ne Q.value),
      quadraticCongruenceRootSum, quadraticCongruenceRootCount]
    simp
  have hlC : ((Q.value : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne Q.value)
  have hzero : quadraticCongruenceRootSumTotal Q.value h 0 * fourierTerm W Q.value 0 =
      𝓕 (W : ℝ → ℂ) 0 * rootDensity Q.value h := by
    rw [hS, fourierTerm_eq, rootDensity]
    simp only [Int.cast_zero, zero_div]
    field_simp
  rw [hzero, add_sub_cancel_left]
  refine tsum_congr fun m => ?_
  by_cases hm : m = 0
  · rw [if_pos hm, if_pos hm]
  · rw [if_neg hm, if_neg hm, fourierTerm_eq]
    ring

end RHTower
