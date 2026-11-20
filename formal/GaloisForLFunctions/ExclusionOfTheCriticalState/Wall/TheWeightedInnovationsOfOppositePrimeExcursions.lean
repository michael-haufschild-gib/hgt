import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositePrimeExcursionsOnOneFixedBand

/-!
# Weighted innovations at a common numerator

Groenevelt and Ledoux prove multivariate Plancherel by successively
applying weighted one-variable isometries (arXiv:2611.00445, Theorem 6.10).
Here each step combines one selected numerator with the preceding ones.
The resulting mixed term measures both prime excursions at that same
numerator relative to their two preceding weighted means.
-/

open Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
noncomputable section
open scoped Classical

def numeratorMass (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, w i

def numeratorMoment (w f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, w i*f i

/-- The complete constant-mode term on the prefix. Empty prefixes contribute zero. -/
def numeratorMeanProduct (w f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  numeratorMoment w f n * numeratorMoment w g n / numeratorMass w n

/-- Inner product of the two new weighted contrast coordinates. -/
def numeratorInnovation (w f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  numeratorMass w n*w n/(numeratorMass w n+w n) *
    (f n-numeratorMoment w f n/numeratorMass w n) *
    (g n-numeratorMoment w g n/numeratorMass w n)

private theorem mean_product_update (W u F G x y : ℝ) (hW : 0 ≤ W) (hu : 0 ≤ u)
    (hz : W=0 → F=0 ∧ G=0) :
    F*G/W + u*(x*y) = (F+u*x)*(G+u*y)/(W+u) +
      W*u/(W+u)*(x-F/W)*(y-G/W) := by
  by_cases h : W=0
  · obtain ⟨rfl,rfl⟩ := hz h
    rcases eq_or_lt_of_le hu with he|he
    · simp [h,← he]
    · rw [h]
      field_simp [he.ne']
      ring
  · have hsum : W+u ≠ 0 := (add_pos_of_pos_of_nonneg (lt_of_le_of_ne hW (Ne.symm h)) hu).ne'
    field_simp [h,hsum]
    ring

/-- Weighted Plancherel for two different real readings. Each innovation is
evaluated using only earlier selected numerators, including across gaps. -/
theorem weighted_numerator_plancherel (w f g : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i) (n : ℕ) :
    numeratorMoment w (fun i => f i*g i) n = numeratorMeanProduct w f g n +
      ∑ i ∈ range n, numeratorInnovation w f g i := by
  induction n with
  | zero => simp [numeratorMoment,numeratorMeanProduct,numeratorMass]
  | succ n ih =>
    have hmass : 0 ≤ numeratorMass w n := sum_nonneg fun i _ => hw i
    have hz (v : ℕ → ℝ) (h : numeratorMass w n=0) : numeratorMoment w v n=0 :=
      sum_eq_zero fun i hi => by
        have hh := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ range n) => hw i)).mp h i hi
        rw [hh,zero_mul]
    have step := mean_product_update (numeratorMass w n) (w n) (numeratorMoment w f n)
      (numeratorMoment w g n) (f n) (g n) hmass (hw n) (fun h => ⟨hz f h,hz g h⟩)
    have hstep : numeratorMeanProduct w f g n + w n*(f n*g n) =
        numeratorMeanProduct w f g (n+1) + numeratorInnovation w f g n := by
      simpa only [numeratorMeanProduct,numeratorInnovation,numeratorMoment,numeratorMass,
        Finset.sum_range_succ] using step
    rw [show numeratorMoment w (fun i => f i*g i) (n+1) =
      numeratorMoment w (fun i => f i*g i) n + w n*(f n*g n) from Finset.sum_range_succ ..,
      ih, Finset.sum_range_succ]
    linarith only [hstep]

/-- Joint-event weights for the opposite prime excursions. The whole
dependence on the thresholds and the moving flank is retained in the mask. -/
def excursionNumeratorWeight (left : Bool) (s a g d T : ℝ) (k L H : ℕ) : ℝ :=
  if H ∈ largeOppositePrimeNumerators left s a g d T k L then (L:ℝ)/(H:ℝ)^2 else 0

/-- The signed mixed upper-tail moment is the prefix mean product plus
its individual cross-innovations. Both profiles use the same selected H. -/
theorem oppositePrimeProduct_innovations (left : Bool) (s a g d T : ℝ) (k L : ℕ) :
    let E := largeOppositePrimeNumerators left s a g d T k L
    let w := excursionNumeratorWeight left s a g d T k L
    let f := fun H => max 0 (s*oddQuotientPrimeExcess (Ioc k L) H)
    let v := fun H => max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H)
    (L:ℝ)*∑ H ∈ E, oppositePrimeProduct left s k L H =
      numeratorMeanProduct w f v (L^2) + ∑ H ∈ E, numeratorInnovation w f v H := by
  let E := largeOppositePrimeNumerators left s a g d T k L
  let w := excursionNumeratorWeight left s a g d T k L
  let f (H : ℕ) := max 0 (s*oddQuotientPrimeExcess (Ioc k L) H)
  let v (H : ℕ) := max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H)
  have hin : E ⊆ range (L^2) := (filter_subset _ _).trans (filter_subset _ _)
  have h0 (i : ℕ) (hi : i ∉ E) : w i=0 := if_neg hi
  have hintegral : numeratorMoment w (fun i => f i*v i) (L^2) =
      (L:ℝ)*∑ H ∈ E, oppositePrimeProduct left s k L H := by
    unfold numeratorMoment
    rw [← sum_subset hin (fun i _ hi => by rw [h0 i hi,zero_mul]), mul_sum]
    apply sum_congr rfl
    intro H hH
    have hW : w H = (L:ℝ)/(H:ℝ)^2 := if_pos hH
    rw [hW]
    unfold oppositePrimeProduct
    dsimp only [f,v]
    ring
  have hdetail : ∑ H ∈ E, numeratorInnovation w f v H =
      ∑ H ∈ range (L^2), numeratorInnovation w f v H := by
    refine sum_subset hin fun H _ hH => ?_
    simp [numeratorInnovation,h0 H hH]
  have hw (i : ℕ) : 0 ≤ w i := by
    unfold w excursionNumeratorWeight
    split_ifs <;> positivity
  change (L:ℝ)*∑ H ∈ E, oppositePrimeProduct left s k L H = _
  rw [← hintegral,weighted_numerator_plancherel w f v hw,hdetail]


end
end GaloisForLFunctions.ExclusionOfTheCriticalState
