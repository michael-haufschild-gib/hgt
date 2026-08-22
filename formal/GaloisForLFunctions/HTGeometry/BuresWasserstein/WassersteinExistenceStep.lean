import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinGradientStep
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinNearIdentity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtBanach

/-!
# One continuation step for the Wasserstein equation

If the Wasserstein vector field is small at a point `X₀` of the Loewner interval, the explicit
gradient step `X ↦ X - tΦ(X)` contracts on the Hilbert–Schmidt ball around `X₀` and the Banach
fixed point produces an exact Wasserstein point nearby.  This is the step of the homotopy
continuation, and its size depends only on the Loewner constants `α, β`.
-/

open scoped NNReal Ring BigOperators
open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

open GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]
variable {ι : Type*} {s : Finset ι} {w : ι → ℝ} {Av : ι → E →L[ℂ] E}

/-- **One continuation step.**  A small defect at `X₀` yields an exact Wasserstein point within
Hilbert–Schmidt distance `r`. -/
theorem exists_isWassersteinPoint_of_small_defect {X₀ : E →L[ℂ] E} {α β r t θ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (_hr : 0 < r) (ht : 0 < t) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : E →L[ℂ] E) ≤ Av i)
    (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : E →L[ℂ] E))
    (hAHS : ∀ i ∈ s, IsHilbertSchmidt (Av i - 1))
    (hX₀sa : IsSelfAdjoint X₀)
    (hX₀α : (α + r) • (1 : E →L[ℂ] E) ≤ X₀) (hX₀β : X₀ ≤ (β - r) • (1 : E →L[ℂ] E))
    (hX₀HS : IsHilbertSchmidt (X₀ - 1))
    (hfac : 1 - 2 * t * (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (2 * r))
      + t ^ 2 * (wassLipConst α β) ^ 2 ≤ θ ^ 2)
    (hdefect : t * hsNorm (wassField s w Av X₀) ≤ (1 - θ) * r) :
    ∃ X : E →L[ℂ] E, IsSelfAdjoint X ∧ IsHilbertSchmidt (X - X₀) ∧ hsNorm (X - X₀) ≤ r
      ∧ IsWassersteinPoint s w Av X := by
  classical
  -- basic consequences of the ball
  have hball : ∀ X : E →L[ℂ] E, IsSelfAdjoint X → IsHilbertSchmidt (X - X₀) →
      hsNorm (X - X₀) ≤ r →
      α • (1 : E →L[ℂ] E) ≤ X ∧ X ≤ β • (1 : E →L[ℂ] E) ∧ IsStrictlyPositive X
        ∧ IsHilbertSchmidt (X - 1) := by
    intro X hXsa hXHS hXb
    have hopn : ‖X - X₀‖ ≤ r := (norm_le_hsNorm hXHS).trans hXb
    have hsa : IsSelfAdjoint (X - X₀) := hXsa.sub hX₀sa
    have hlow : α • (1 : E →L[ℂ] E) ≤ X := by
      have h := smul_one_le_of_norm_sub_le hsa hopn hX₀α
      rwa [show α + r - r = α by ring] at h
    have hhigh : X ≤ β • (1 : E →L[ℂ] E) := by
      have h := le_smul_one_of_norm_sub_le hsa hopn hX₀β
      rwa [show β - r + r = β by ring] at h
    refine ⟨hlow, hhigh, isStrictlyPositive_of_smul_one_le hα hlow, ?_⟩
    have h1 : (X : E →L[ℂ] E) - 1 = (X - X₀) + (X₀ - 1) := by abel
    rw [h1]
    exact hXHS.add hX₀HS
  have hXAHS : ∀ X : E →L[ℂ] E, IsHilbertSchmidt (X - 1) → ∀ i ∈ s,
      IsHilbertSchmidt (X - Av i) := by
    intro X hX i hi
    have h1 : (X : E →L[ℂ] E) - Av i = (X - 1) - (Av i - 1) := by abel
    rw [h1]
    exact hX.sub (hAHS i hi)
  -- the units at each point
  have hunit : ∀ Y : E →L[ℂ] E, IsStrictlyPositive Y →
      ∃ v : ι → ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ, ∀ i ∈ s,
        (↑(v i) : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
            + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj) := by
    intro Y hY
    have hex : ∀ i, ∃ v : ((E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))ˣ, i ∈ s →
        (↑v : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E))
          = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Y⁻¹ʳ))).comp (saProj)
            + ((1 : (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E)) - saProj) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨v, hvv⟩ := exists_twisted_unit (hA i hi) hY
        exact ⟨v, fun _ => hvv⟩
      · exact ⟨1, fun h => absurd h hi⟩
    choose v hv using hex
    exact ⟨v, hv⟩
  have hCnn : (0 : ℝ) ≤ secondOrderConst α β := by
    unfold secondOrderConst
    have hai : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
    positivity
  obtain ⟨X, hXsa, hXHS, hXb, hfix⟩ :=
    exists_fixedPoint_hs (G := fun X => X - t • wassField s w Av X) (X₀ := X₀) (r := r)
      (θ := θ) (P := fun X : E →L[ℂ] E => IsSelfAdjoint X) hθ0 hθ1 hX₀sa
      (fun X hXsa hXHS hXb => by
        obtain ⟨hlow, hhigh, hpos, hHS1⟩ := hball X hXsa hXHS hXb
        exact hXsa.sub (IsSelfAdjoint.smul (star_trivial t) (isSelfAdjoint_wassField hpos)))
      (fun Y Z hP hHS hlim => isSelfAdjoint_of_hs_limit hP hHS hlim)
      (fun X hXsa hXHS hXb => by
        obtain ⟨hlow, hhigh, hpos, hHS1⟩ := hball X hXsa hXHS hXb
        have hΦ : IsHilbertSchmidt (wassField s w Av X) :=
          isHilbertSchmidt_wassField hα hβ hA hpos hAα hAβ hhigh (hXAHS X hHS1)
        have hid : (X - t • wassField s w Av X) - X₀
            = (X - X₀) - t • wassField s w Av X := by abel
        rw [hid]
        exact hXHS.sub (hΦ.real_smul t))
      (fun X Y hXsa hXHS hXb hYsa hYHS hYb => by
        obtain ⟨hXlow, hXhigh, hXpos, hXHS1⟩ := hball X hXsa hXHS hXb
        obtain ⟨hYlow, hYhigh, hYpos, hYHS1⟩ := hball Y hYsa hYHS hYb
        obtain ⟨v, hv⟩ := hunit Y hYpos
        have hdiffid : (X : E →L[ℂ] E) - Y = (X - X₀) - (Y - X₀) := by abel
        have hPHS : IsHilbertSchmidt (X - Y) := by rw [hdiffid]; exact hXHS.sub hYHS
        have hPsa : IsSelfAdjoint (X - Y) := hXsa.sub hYsa
        have hXY : ‖X - Y‖ ≤ 2 * r := by
          rw [hdiffid]
          refine (norm_sub_le _ _).trans ?_
          have hx := (norm_le_hsNorm hXHS).trans hXb
          have hy := (norm_le_hsNorm hYHS).trans hYb
          linarith
        have hstep := hsNormSq_gradientStep_sub_le hα hβ ht.le hw hwsum hA hXpos hYpos
          hAα hAβ hXlow hXhigh hYlow hYhigh hPHS hPsa hv
        have hmono : 1 - 2 * t * (α * α / (2 * (β * (β * β)))
              - secondOrderConst α β * ‖X - Y‖) + t ^ 2 * (wassLipConst α β) ^ 2
            ≤ 1 - 2 * t * (α * α / (2 * (β * (β * β)))
              - secondOrderConst α β * (2 * r)) + t ^ 2 * (wassLipConst α β) ^ 2 := by
          have hkey : (2 * t * secondOrderConst α β) * ‖X - Y‖
              ≤ (2 * t * secondOrderConst α β) * (2 * r) :=
            mul_le_mul_of_nonneg_left hXY
              (mul_nonneg (mul_nonneg (by norm_num) ht.le) hCnn)
          nlinarith [hkey]
        have hfinal : hsNormSq ((X - t • wassField s w Av X) - (Y - t • wassField s w Av Y))
            ≤ θ ^ 2 * hsNormSq (X - Y) :=
          hstep.trans (mul_le_mul_of_nonneg_right (hmono.trans hfac) (hsNormSq_nonneg _))
        show Real.sqrt (hsNormSq _) ≤ θ * Real.sqrt (hsNormSq (X - Y))
        have h := Real.sqrt_le_sqrt hfinal
        rwa [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ0] at h)
      (by
        have hid : (X₀ - t • wassField s w Av X₀) - X₀
            = -(t • wassField s w Av X₀) := by abel
        rw [hid]
        have hneg : hsNorm (-(t • wassField s w Av X₀))
            = hsNorm (t • wassField s w Av X₀) := by
          show Real.sqrt (hsNormSq _) = Real.sqrt (hsNormSq _)
          rw [hsNormSq_neg_eq_self]
        rw [hneg, hsNorm_real_smul, abs_of_pos ht]
        exact hdefect)
  refine ⟨X, hXsa, hXHS, hXb, ?_⟩
  obtain ⟨hlow, hhigh, hpos, hHS1⟩ := hball X hXsa hXHS hXb
  have hzero : wassField s w Av X = 0 := by
    have h : t • wassField s w Av X = 0 := sub_eq_self.mp hfix
    rcases smul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (ne_of_gt ht)
    · exact h1
  exact (wassField_eq_zero_iff hwsum hpos).mp hzero

/-! ### The step constants -/

lemma secondOrderConst_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < secondOrderConst α β := by
  unfold secondOrderConst
  have hai : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  positivity

lemma wassLipConst_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < wassLipConst α β := by
  unfold wassLipConst
  have hai : (0 : ℝ) < α⁻¹ := inv_pos.mpr hα
  have hs : (0 : ℝ) < Real.sqrt (α * β⁻¹) := Real.sqrt_pos.mpr (by positivity)
  positivity

/-- **Admissible step constants.**  For any target radius `r₀` there are a radius `r ≤ r₀`, a step
length `t` and a contraction factor `θ < 1` for which the gradient step contracts on the ball of
radius `r`. -/
lemma exists_step_constants {α β r₀ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hr₀ : 0 < r₀) :
    ∃ r t θ : ℝ, 0 < r ∧ r ≤ r₀ ∧ 0 < t ∧ 0 ≤ θ ∧ θ < 1 ∧
      1 - 2 * t * (α * α / (2 * (β * (β * β))) - secondOrderConst α β * (2 * r))
        + t ^ 2 * (wassLipConst α β) ^ 2 ≤ θ ^ 2 := by
  have hC : 0 < secondOrderConst α β := secondOrderConst_pos hα hβ
  have hL : 0 < wassLipConst α β := wassLipConst_pos hα hβ
  have hκ : (0 : ℝ) < α * α / (2 * (β * (β * β))) := by positivity
  refine ⟨min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β)),
    α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2),
    Real.sqrt (max 0 (1 - 3 * (α * α / (2 * (β * (β * β)))) ^ 2
      / (16 * (wassLipConst α β) ^ 2))), ?_, min_le_left _ _, by positivity,
    Real.sqrt_nonneg _, ?_, ?_⟩
  · exact lt_min hr₀ (by positivity)
  · have hlt : max 0 (1 - 3 * (α * α / (2 * (β * (β * β)))) ^ 2
        / (16 * (wassLipConst α β) ^ 2)) < 1 := by
      refine max_lt one_pos ?_
      have : (0 : ℝ) < 3 * (α * α / (2 * (β * (β * β)))) ^ 2
          / (16 * (wassLipConst α β) ^ 2) := by positivity
      linarith
    have h1 : Real.sqrt (max 0 (1 - 3 * (α * α / (2 * (β * (β * β)))) ^ 2
        / (16 * (wassLipConst α β) ^ 2))) < Real.sqrt 1 := by
      refine Real.sqrt_lt_sqrt (le_max_left _ _) hlt
    rwa [Real.sqrt_one] at h1
  · rw [Real.sq_sqrt (le_max_left _ _)]
    refine le_trans ?_ (le_max_right _ _)
    have hrle : min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β))
        ≤ α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β) := min_le_right _ _
    have hbound : secondOrderConst α β
        * (2 * min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β)))
        ≤ α * α / (2 * (β * (β * β))) / 2 := by
      have h := mul_le_mul_of_nonneg_left hrle hC.le
      rw [mul_div_assoc'] at h
      calc secondOrderConst α β
            * (2 * min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β)))
          = 2 * (secondOrderConst α β
            * min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β))) := by ring
        _ ≤ 2 * (secondOrderConst α β
            * (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β))) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrle hC.le)
                (by norm_num)
        _ = α * α / (2 * (β * (β * β))) / 2 := by field_simp; ring
    have hstep : 1 - 2 * (α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2))
          * (α * α / (2 * (β * (β * β)))
            - secondOrderConst α β
              * (2 * min r₀ (α * α / (2 * (β * (β * β))) / (4 * secondOrderConst α β))))
          + (α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2)) ^ 2
            * (wassLipConst α β) ^ 2
        ≤ 1 - 2 * (α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2))
          * (α * α / (2 * (β * (β * β))) / 2)
          + (α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2)) ^ 2
            * (wassLipConst α β) ^ 2 := by
      have htpos : (0 : ℝ) ≤ 2 * (α * α / (2 * (β * (β * β))) / (4 * (wassLipConst α β) ^ 2)) := by
        positivity
      nlinarith [hbound, htpos]
    refine hstep.trans (le_of_eq ?_)
    field_simp
    ring

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
