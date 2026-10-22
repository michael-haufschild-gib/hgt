import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeDiagonalGreenSummability

/-!
# Pullback transport of convergent Green-form families

Once local Green forms converge in operator norm on an orthogonal target, a bounded comparison map
pulls the entire family back to any source Banach space.  Cross-prime incidence need not preserve a
coordinatewise maximum-tail estimate: continuity of the single comparison map transports the
already-convergent unordered series.  If the target global form has zero radical, the pulled-back
radical is exactly the kernel of the comparison map.

For Route L this isolates the remaining arithmetic statement sharply.  One must construct a
bounded source-to-prime comparison whose kernel is the closed middle-boundary space; no second
termwise `ℓ¹` or maximum-tail proof is required after that comparison exists.
-/

namespace RHTower

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Pull a continuous bilinear Green form back along a bounded linear comparison map. -/
def deningerPullbackGreenForm (U : E →L[ℝ] H)
    (G : H →L[ℝ] H →L[ℝ] ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ E H ℝ).flip U).comp (G.comp U)

@[simp] theorem deningerPullbackGreenForm_apply_apply
    (U : E →L[ℝ] H) (G : H →L[ℝ] H →L[ℝ] ℝ) (x y : E) :
    deningerPullbackGreenForm U G x y = G (U x) (U y) := rfl

/-- Pullback by a fixed comparison map is itself continuous linear on the Green-form space. -/
def deningerPullbackGreenFormL (U : E →L[ℝ] H) :
    (H →L[ℝ] H →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ E (H →L[ℝ] ℝ) (E →L[ℝ] ℝ)
    ((ContinuousLinearMap.compL ℝ E H ℝ).flip U)).comp
      ((ContinuousLinearMap.compL ℝ E H (H →L[ℝ] ℝ)).flip U)

@[simp] theorem deningerPullbackGreenFormL_apply
    (U : E →L[ℝ] H) (G : H →L[ℝ] H →L[ℝ] ℝ) :
    deningerPullbackGreenFormL U G = deningerPullbackGreenForm U G := rfl

/-- Operator-norm summability survives bounded pullback. -/
theorem summable_deningerPullbackGreenForm
    {ι : Type*} (U : E →L[ℝ] H)
    (localForm : ι → H →L[ℝ] H →L[ℝ] ℝ)
    (hforms : Summable localForm) :
    Summable (fun i => deningerPullbackGreenForm U (localForm i)) :=
  hforms.mapL (deningerPullbackGreenFormL U)

/-- Pullback commutes with the unordered operator-norm sum. -/
theorem deningerSummedPullbackGreenForm_eq
    {ι : Type*} (U : E →L[ℝ] H)
    (localForm : ι → H →L[ℝ] H →L[ℝ] ℝ)
    (hforms : Summable localForm) :
    (∑' i, deningerPullbackGreenForm U (localForm i)) =
      deningerPullbackGreenForm U (∑' i, localForm i) := by
  exact (hforms.hasSum.mapL (deningerPullbackGreenFormL U)).tsum_eq

/-- Nonnegativity of a Green energy survives pullback. -/
theorem deningerPullbackGreenForm_nonneg
    (U : E →L[ℝ] H) (G : H →L[ℝ] H →L[ℝ] ℝ)
    (hG : ∀ y, 0 ≤ G y y) (x : E) :
    0 ≤ deningerPullbackGreenForm U G x x := by
  rw [deningerPullbackGreenForm_apply_apply]
  exact hG (U x)

/-- If the target energy has zero radical, the pulled-back radical is exactly the comparison
kernel. -/
theorem deningerPullbackGreenForm_self_eq_zero_iff_mem_ker
    (U : E →L[ℝ] H) (G : H →L[ℝ] H →L[ℝ] ℝ)
    (hG : ∀ y, G y y = 0 ↔ y = 0) (x : E) :
    deningerPullbackGreenForm U G x x = 0 ↔
      x ∈ LinearMap.ker U.toLinearMap := by
  rw [deningerPullbackGreenForm_apply_apply, hG]
  rfl

/-- An injective comparison pulls a zero-radical target energy back to a zero-radical source
energy. -/
theorem deningerPullbackGreenForm_self_eq_zero_iff
    (U : E →L[ℝ] H) (G : H →L[ℝ] H →L[ℝ] ℝ)
    (hG : ∀ y, G y y = 0 ↔ y = 0)
    (hU : Function.Injective U) (x : E) :
    deningerPullbackGreenForm U G x x = 0 ↔ x = 0 := by
  rw [deningerPullbackGreenForm_self_eq_zero_iff_mem_ker U G hG]
  constructor
  · intro hx
    apply hU
    rw [map_zero]
    change U x = 0 at hx
    exact hx
  · rintro rfl
    simp

/-! ## Orthogonal prime target -/

/-- Pullback of the prime-diagonal local Green family along a bounded source comparison. -/
def deningerPrimeComparisonLocalGreenForm
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) (p : Nat.Primes) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  deningerPullbackGreenForm U (deningerPrimeDiagonalGreenForm p)

/-- Every bounded source-to-prime comparison inherits unordered local-form summability. -/
theorem summable_deningerPrimeComparisonLocalGreenForm
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) :
    Summable (deningerPrimeComparisonLocalGreenForm U) :=
  summable_deningerPullbackGreenForm U deningerPrimeDiagonalGreenForm
    summable_deningerPrimeDiagonalGreenForm

/-- Global Green form transported from the orthogonal prime target. -/
def deningerPrimeComparisonSummedGreenForm
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑' p, deningerPrimeComparisonLocalGreenForm U p

/-- The transported global form is the pullback of the prime-diagonal global form. -/
theorem deningerPrimeComparisonSummedGreenForm_eq
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) :
    deningerPrimeComparisonSummedGreenForm U =
      deningerPullbackGreenForm U deningerPrimeDiagonalSummedGreenForm :=
  deningerSummedPullbackGreenForm_eq U deningerPrimeDiagonalGreenForm
    summable_deningerPrimeDiagonalGreenForm

/-- The transported prime energy is nonnegative on every source vector. -/
theorem deningerPrimeComparisonSummedGreenForm_nonneg
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) (x : E) :
    0 ≤ deningerPrimeComparisonSummedGreenForm U x x := by
  rw [deningerPrimeComparisonSummedGreenForm_eq]
  exact deningerPullbackGreenForm_nonneg U deningerPrimeDiagonalSummedGreenForm
    deningerPrimeDiagonalSummedGreenForm_nonneg x

/-- **Comparison-kernel radical law.**  On any Banach source, the radical of the transported
all-prime Green energy is exactly the kernel of the bounded prime comparison. -/
theorem deningerPrimeComparisonSummedGreenForm_self_eq_zero_iff_mem_ker
    (U : E →L[ℝ] DeningerRealEllTwo Nat.Primes) (x : E) :
    deningerPrimeComparisonSummedGreenForm U x x = 0 ↔
      x ∈ LinearMap.ker U.toLinearMap := by
  rw [deningerPrimeComparisonSummedGreenForm_eq]
  exact deningerPullbackGreenForm_self_eq_zero_iff_mem_ker U
    deningerPrimeDiagonalSummedGreenForm
    deningerPrimeDiagonalSummedGreenForm_self_eq_zero_iff x

end

end RHTower
