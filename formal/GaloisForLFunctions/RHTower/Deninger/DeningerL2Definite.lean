import GaloisForLFunctions.RHTower.Deninger.DeningerKummerSpaceInnerPos
import GaloisForLFunctions.RHTower.Deninger.DeningerHeightZeroKummer

/-!
# Definiteness of the `L²` place norm

A sum of nonnegative terms vanishes only if every term does, so a vanishing `L²` place norm forces
every place to take the value one.  Then the logarithmic height vanishes, and the height-zero
theorem makes the element a root of unity.

* `deningerL2NormSq_eq_zero_places` : all places take the value one.
* `deningerL2NormSq_eq_zero` : the element is a root of unity.
-/

namespace RHTower

open NumberField

section Definite

variable {K : Type*} [Field K] [NumberField K]

/-- **A vanishing `L²` norm forces every place to take the value one.** -/
theorem deningerL2NormSq_eq_zero_places {x : K} (hx : x ≠ 0) (h : deningerL2NormSq x = 0) :
    (∀ v : InfinitePlace K, v x = 1) ∧ ∀ w : FinitePlace K, w x = 1 := by
  classical
  set A : ℝ := ∑ v : InfinitePlace K, (v.mult : ℝ) * (Real.log (v x)) ^ (2 : ℕ) with hA
  set B : ℝ := ∑ᶠ w : FinitePlace K, (Real.log (w x)) ^ (2 : ℕ) / (deningerPlaceDegree w : ℝ) with hB
  have hAnn : 0 ≤ A := Finset.sum_nonneg fun v _ => by positivity
  have hBnn : 0 ≤ B := finsum_nonneg fun w => by positivity
  have hsum : A + B = 0 := h
  have hA0 : A = 0 := by linarith
  have hB0 : B = 0 := by linarith
  constructor
  · intro v
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by positivity)).mp hA0 v
      (Finset.mem_univ v)
    have hmult : ((v.mult : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr InfinitePlace.mult_ne_zero
    have hlog : Real.log (v x) = 0 := by
      have hsq : (Real.log (v x)) ^ (2 : ℕ) = 0 := by
        rcases mul_eq_zero.mp hterm with hc | hc
        · exact absurd hc hmult
        · exact hc
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    have hexp := congrArg Real.exp hlog
    rwa [Real.exp_log (InfinitePlace.pos_iff.mpr hx), Real.exp_zero] at hexp
  · intro w
    set S : Finset (FinitePlace K) := (FinitePlace.hasFiniteMulSupport hx).toFinset with hS
    have hmemS : ∀ u : FinitePlace K, u ∈ S ↔ u x ≠ 1 := by
      intro u
      simp [hS, Function.mulSupport]
    by_cases hw : w ∈ S
    · have hsub : Function.support (fun u : FinitePlace K =>
          (Real.log (u x)) ^ (2 : ℕ) / (deningerPlaceDegree u : ℝ)) ⊆ (S : Set (FinitePlace K)) := by
        intro u hu
        by_contra huS
        refine hu ?_
        show (Real.log (u x)) ^ (2 : ℕ) / (deningerPlaceDegree u : ℝ) = 0
        have hone : u x = 1 := by
          by_contra hne
          exact huS (Finset.mem_coe.mpr ((hmemS u).mpr hne))
        rw [hone, Real.log_one]
        simp
      rw [hB, finsum_eq_finsetSum_of_support_subset _ hsub] at hB0
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun u _ => by positivity)).mp hB0 w hw
      have hd : ((deningerPlaceDegree w : ℝ)) ≠ 0 := by
        have := deningerPlaceDegree_pos w
        positivity
      have hsq : (Real.log (w x)) ^ (2 : ℕ) = 0 := by
        rcases div_eq_zero_iff.mp hterm with hc | hc
        · exact hc
        · exact absurd hc hd
      have hlog : Real.log (w x) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      have hexp := congrArg Real.exp hlog
      rwa [Real.exp_log (FinitePlace.pos_iff.mpr hx), Real.exp_zero] at hexp
    · by_contra hne
      exact hw ((hmemS w).mpr hne)

/-- **Definiteness of the `L²` place norm.**  A nonzero element with vanishing `L²` norm is a root
of unity. -/
theorem deningerL2NormSq_eq_zero {x : K} (hx : x ≠ 0) (h : deningerL2NormSq x = 0) :
    IsOfFinOrder x := by
  obtain ⟨harch, hfin⟩ := deningerL2NormSq_eq_zero_places hx h
  refine (deningerLogHeightZero_iff_isOfFinOrder hx).mp ?_
  rw [NumberField.logHeight₁_eq]
  have h1 : (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x)) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [harch v]
    simp [Real.posLog]
  have h2 : (∑ᶠ w : FinitePlace K, Real.posLog (w x)) = 0 := by
    have hzero : (fun w : FinitePlace K => Real.posLog (w x)) = fun _ => (0 : ℝ) := by
      funext w
      rw [hfin w]
      simp [Real.posLog]
    rw [hzero, finsum_zero]
  rw [h1, h2, add_zero]

end Definite

end RHTower
