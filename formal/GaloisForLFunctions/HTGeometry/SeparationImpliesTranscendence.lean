import GaloisForLFunctions.HTGeometry.PrefixStateIndependence
import GaloisForLFunctions.HTGeometry.PolynomialGrowthBound
import GaloisForLFunctions.HTGeometry.TranscendentalEntireOrderOne

/-!
# A growth separation already forces transcendence

The separation predicate makes the new state outgrow every fixed multiple of the joint scale of the
earlier ones.  Since the coordinate is among those, it in particular outgrows every fixed multiple of
`log⁺|z|`, which no polynomial does.

So the separation hypothesis of the lower bound carries transcendence of the composite with it; that
does not have to be assumed separately.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **The logarithmic growth bound for a one-variable polynomial.** -/
theorem posLog_norm_eval_poly_le (q : Polynomial ℂ) (z : ℂ) :
    Real.posLog ‖q.eval z‖
      ≤ Real.posLog (coeffNormSum q)
        + q.natDegree * (Real.log 2 + Real.posLog ‖z‖) := by
  have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hC0 : 0 ≤ coeffNormSum q := coeffNormSum_nonneg q
  have hprod0 : (0 : ℝ) ≤ coeffNormSum q * (1 + ‖z‖) ^ q.natDegree := by positivity
  have h1 : Real.posLog ‖q.eval z‖
      ≤ Real.posLog (coeffNormSum q * (1 + ‖z‖) ^ q.natDegree) :=
    Real.monotoneOn_posLog (Set.mem_Ici.mpr (norm_nonneg _)) (Set.mem_Ici.mpr hprod0)
      (norm_eval_le_coeffNormSum q z)
  have h2 : Real.posLog (coeffNormSum q * (1 + ‖z‖) ^ q.natDegree)
      ≤ Real.posLog (coeffNormSum q) + Real.posLog ((1 + ‖z‖) ^ q.natDegree) :=
    Real.posLog_mul
  have h3 : Real.posLog ((1 + ‖z‖) ^ q.natDegree)
      ≤ q.natDegree * (Real.log 2 + Real.posLog ‖z‖) := by
    rw [Real.posLog_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have hadd := Real.posLog_add (x := (1 : ℝ)) (y := ‖z‖)
    rw [Real.posLog_one] at hadd
    linarith
  linarith

/-- **A separated state is transcendental.**  If the coordinate is among the earlier states, the
separation forces growth beyond every polynomial. -/
theorem transcendentalEntire_of_stepSeparation {m : ℕ} {X : Fin m → ℂ → ℂ} {F : ℂ → ℂ}
    (hm : 0 < m) (hX0 : ∀ z : ℂ, X ⟨0, hm⟩ z = z)
    (hF : Differentiable ℂ F) (hsep : StepSeparation X F) :
    TranscendentalEntire F := by
  refine ⟨hF, ?_⟩
  rintro ⟨q, hq⟩
  set d : ℝ := (q.natDegree : ℝ) with hd
  set K : ℝ := Real.posLog (coeffNormSum q) + d * Real.log 2 with hK
  set c : ℝ := max d K + 1 with hc
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hK0 : 0 ≤ K := by
    have h1 : (0 : ℝ) ≤ Real.posLog (coeffNormSum q) := Real.posLog_nonneg
    have h2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [hK]
    positivity
  have hc0 : 0 ≤ c := by
    have := le_max_right d K
    rw [hc]
    linarith
  obtain ⟨z, ε, hε, _, hsplit⟩ := hsep 1 one_ne_zero c hc0
  have hP0 : (0 : ℝ) ≤ Real.posLog ‖z‖ := Real.posLog_nonneg
  have hε0 : (0 : ℝ) ≤ Real.posLog ε⁻¹ := Real.posLog_nonneg
  -- the coordinate contributes at least its own scale
  have hS : Real.posLog ‖z‖ ≤ ∑ j : Fin m, Real.posLog ‖X j z‖ := by
    have hmem : (⟨0, hm⟩ : Fin m) ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
    have hle := Finset.single_le_sum (f := fun j : Fin m => Real.posLog ‖X j z‖)
      (fun _ _ => Real.posLog_nonneg) hmem
    rwa [hX0 z] at hle
  -- the polynomial bound
  have hpoly : Real.posLog ‖F z‖ ≤ K + d * Real.posLog ‖z‖ := by
    rw [hq z]
    have := posLog_norm_eval_poly_le q z
    rw [hK, hd]
    linarith [this]
  -- combine
  have hlow : c * (1 + Real.posLog ‖z‖) ≤ c * (1 + (∑ j : Fin m, Real.posLog ‖X j z‖)
      + Real.posLog ε⁻¹) := by
    refine mul_le_mul_of_nonneg_left ?_ hc0
    linarith
  have hcd : d ≤ c := by
    have := le_max_left d K
    rw [hc]
    linarith
  have hcK : K < c := by
    have := le_max_right d K
    rw [hc]
    linarith
  nlinarith [hsplit, hlow, hpoly, hP0, hcd, hcK]

end GaloisForLFunctions.HTGeometry
