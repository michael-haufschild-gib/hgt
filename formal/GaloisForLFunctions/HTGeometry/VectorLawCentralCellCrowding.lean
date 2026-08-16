import GaloisForLFunctions.HTGeometry.EuclideanPackingPigeonhole
import Mathlib.Algebra.Order.Chebyshev

/-!
# The central-cell crowding floor of a vector-valued finite law

A finite probability law taking values in a finite-dimensional real normed space cannot spread its
pair mass arbitrarily thinly.  Chebyshev's inequality confines three quarters of the mass to the
ball of radius twice the root second moment; a maximal `δ/2`-separated subset of that ball is a
net whose Voronoi cells have diameter below `δ`, and Cauchy–Schwarz forces one cell to be heavy.
Two independent samples landing in a common cell differ by less than `δ`.

The resulting floor `9/(16 (1 + 8√V/δ)^d)` on the near-pair mass is uniform in the law and depends
only on the second moment `V`, the resolution `δ`, and the dimension `d` of the observer space.
-/

open MeasureTheory Metric

noncomputable section

open scoped Classical

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

variable {A : Type*} [Fintype A]

/-- Mass of all ordered pairs whose observed vectors are closer than `δ`. -/
def vectorLawWithinMass (a : A → ℝ) (X : A → E) (δ : ℝ) : ℝ :=
  ∑ α, ∑ β, if ‖X α - X β‖ < δ then a α * a β else 0

/-- Mass of the diagonal pairs of a finite law. -/
def vectorLawDiagonalMass (a : A → ℝ) : ℝ := ∑ α, a α * a α

/-- Mass of all ordered pairs of distinct indices whose observed vectors are closer than `δ`. -/
def vectorLawOffDiagonalWithinMass (a : A → ℝ) (X : A → E) (δ : ℝ) : ℝ :=
  ∑ α, ∑ β, if α ≠ β ∧ ‖X α - X β‖ < δ then a α * a β else 0

/-- **Chebyshev for a vector-valued finite law.**  At most a quarter of the mass sits beyond twice
the root second moment. -/
theorem vectorLaw_tail_le_quarter {a : A → ℝ} {X : A → E} (hnn : ∀ α, 0 ≤ a α) {c : E} {V : ℝ}
    (hV : 0 ≤ V) (hmom : ∑ α, a α * ‖X α - c‖ ^ 2 ≤ V) :
    ∑ α ∈ Finset.univ.filter fun α => ¬ (‖X α - c‖ ≤ 2 * Real.sqrt V), a α ≤ 1 / 4 := by
  classical
  set F := Finset.univ.filter fun α => ¬ (‖X α - c‖ ≤ 2 * Real.sqrt V) with hF
  have hterms : ∀ β ∈ (Finset.univ : Finset A), 0 ≤ a β * ‖X β - c‖ ^ 2 :=
    fun β _ => mul_nonneg (hnn β) (sq_nonneg _)
  rcases eq_or_lt_of_le hV with hV0 | hVpos
  · have hzero : ∀ α ∈ F, a α = 0 := by
      intro α hα
      rw [hF, Finset.mem_filter] at hα
      have hgt : 0 < ‖X α - c‖ := by
        have hnot := hα.2
        rw [← hV0, Real.sqrt_zero, mul_zero] at hnot
        exact not_le.mp hnot
      have hsum0 : ∑ β, a β * ‖X β - c‖ ^ 2 = 0 := by
        refine le_antisymm ?_ (Finset.sum_nonneg hterms)
        rw [← hV0] at hmom
        exact hmom
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum0 α (Finset.mem_univ α)
      rcases mul_eq_zero.mp hz with h | h
      · exact h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgt.ne'
    rw [Finset.sum_eq_zero hzero]
    norm_num
  · have hstep : ∀ α ∈ F, a α * (4 * V) ≤ a α * ‖X α - c‖ ^ 2 := by
      intro α hα
      rw [hF, Finset.mem_filter] at hα
      have hgt : 2 * Real.sqrt V < ‖X α - c‖ := not_le.mp hα.2
      have hnn2 : 0 ≤ 2 * Real.sqrt V := by positivity
      have hsq : (2 * Real.sqrt V) ^ 2 ≤ ‖X α - c‖ ^ 2 := by nlinarith
      have hval : (2 * Real.sqrt V) ^ 2 = 4 * V := by
        rw [mul_pow, Real.sq_sqrt hV]
        ring
      rw [hval] at hsq
      exact mul_le_mul_of_nonneg_left hsq (hnn α)
    have hkey : (∑ α ∈ F, a α) * (4 * V) ≤ V := by
      calc (∑ α ∈ F, a α) * (4 * V) = ∑ α ∈ F, a α * (4 * V) := by rw [Finset.sum_mul]
        _ ≤ ∑ α ∈ F, a α * ‖X α - c‖ ^ 2 := Finset.sum_le_sum hstep
        _ ≤ ∑ α, a α * ‖X α - c‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun i hi _ => hterms i hi)
        _ ≤ V := hmom
    nlinarith [hkey, hVpos]

/-- **Theorem B: the vector-valued central-cell crowding floor.**  For every finite probability law
on a finite-dimensional observer space with second moment at most `V` about some centre, and every
resolution `δ > 0`, the mass of ordered pairs whose observed vectors are closer than `δ` is at
least `9/(16 (1 + 8√V/δ)^d)`. -/
theorem vectorLaw_crowding_floor (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : A → ℝ} {X : A → E} (hnn : ∀ α, 0 ≤ a α) (hsum : ∑ α, a α = 1)
    (c : E) {V : ℝ} (hV : 0 ≤ V) (hmom : ∑ α, a α * ‖X α - c‖ ^ 2 ≤ V) {δ : ℝ} (hδ : 0 < δ) :
    (9 : ℝ) / 16 / (1 + 8 * Real.sqrt V / δ) ^ (Module.finrank ℝ E) ≤
      vectorLawWithinMass a X δ := by
  classical
  set d := Module.finrank ℝ E with hd
  set ρ := 2 * Real.sqrt V with hρ
  have hρnn : 0 ≤ ρ := by positivity
  set G : Finset A := Finset.univ.filter fun α => ‖X α - c‖ ≤ ρ with hG
  have hgood : 3 / 4 ≤ ∑ α ∈ G, a α := by
    have htail := vectorLaw_tail_le_quarter hnn hV hmom
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset A)
      (fun α => ‖X α - c‖ ≤ ρ) a
    rw [hsum] at hsplit
    linarith [htail]
  obtain ⟨T, hTne, hT1, hTcov, hTpack⟩ := exists_finset_net μ ρ (δ / 2) hρnn (by linarith)
  have hassign : ∀ α ∈ G, ∃ t ∈ T, ‖(X α - c) - t‖ < δ / 2 := by
    intro α hα
    rw [hG, Finset.mem_filter] at hα
    exact hTcov _ hα.2
  choose! f hfT hfd using hassign
  set b : E → ℝ := fun t => ∑ α ∈ G.filter fun α => f α = t, a α with hb
  have hbsum : ∑ t ∈ T, b t = ∑ α ∈ G, a α :=
    Finset.sum_fiberwise_of_maps_to (fun α hα => hfT α hα) a
  set g : A → A → ℝ := fun α β => if ‖X α - X β‖ < δ then a α * a β else 0 with hgdef
  have hgnn : ∀ α β, 0 ≤ g α β := by
    intro α β
    show (0 : ℝ) ≤ if ‖X α - X β‖ < δ then a α * a β else 0
    by_cases h : ‖X α - X β‖ < δ
    · rw [if_pos h]
      exact mul_nonneg (hnn α) (hnn β)
    · rw [if_neg h]
  have hcell : ∀ t ∈ T, (b t) ^ 2 = ∑ α ∈ G.filter fun α => f α = t,
      ∑ β ∈ G.filter fun α => f α = t, g α β := by
    intro t ht
    rw [hb, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun α hα => Finset.sum_congr rfl fun β hβ => ?_
    rw [Finset.mem_filter] at hα hβ
    have hdα := hfd α hα.1
    have hdβ := hfd β hβ.1
    rw [hα.2] at hdα
    rw [hβ.2] at hdβ
    have hdist : ‖X α - X β‖ < δ := by
      have hsplit : X α - X β = ((X α - c) - t) - ((X β - c) - t) := by abel
      calc ‖X α - X β‖ = ‖((X α - c) - t) - ((X β - c) - t)‖ := by rw [hsplit]
        _ ≤ ‖(X α - c) - t‖ + ‖(X β - c) - t‖ := norm_sub_le _ _
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    show a α * a β = if ‖X α - X β‖ < δ then a α * a β else 0
    rw [if_pos hdist]
  have hpairs : ∑ t ∈ T, (b t) ^ 2 ≤ vectorLawWithinMass a X δ := by
    calc ∑ t ∈ T, (b t) ^ 2
        = ∑ t ∈ T, ∑ α ∈ G.filter fun α => f α = t,
            ∑ β ∈ G.filter fun α => f α = t, g α β := Finset.sum_congr rfl hcell
      _ ≤ ∑ t ∈ T, ∑ α ∈ G.filter fun α => f α = t, ∑ β, g α β := by
          refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun α hα => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun β _ _ => hgnn α β
      _ = ∑ α ∈ G, ∑ β, g α β :=
          Finset.sum_fiberwise_of_maps_to (fun α hα => hfT α hα) _
      _ ≤ ∑ α, ∑ β, g α β :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun α _ _ => Finset.sum_nonneg fun β _ => hgnn α β
      _ = vectorLawWithinMass a X δ := rfl
  have hMpos : 0 < (T.card : ℝ) := by
    have hc := Finset.card_pos.mpr hTne
    exact_mod_cast hc
  have hcs : (∑ t ∈ T, b t) ^ 2 ≤ (T.card : ℝ) * ∑ t ∈ T, (b t) ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsq : (9 : ℝ) / 16 ≤ (T.card : ℝ) * ∑ t ∈ T, (b t) ^ 2 := by
    have hsumb : (3 : ℝ) / 4 ≤ ∑ t ∈ T, b t := by
      rw [hbsum]
      exact hgood
    nlinarith [hcs, hsumb]
  have hquarter : (0 : ℝ) < δ / 4 := by linarith
  have hBpos : (0 : ℝ) < (1 + 8 * Real.sqrt V / δ) ^ d := by positivity
  have hB : (T.card : ℝ) ≤ (1 + 8 * Real.sqrt V / δ) ^ d := by
    have hqe : δ / 2 / 2 = δ / 4 := by ring
    rw [hqe] at hTpack
    have hdiv : (T.card : ℝ) ≤ (ρ + δ / 4) ^ d / (δ / 4) ^ d := by
      rw [le_div_iff₀ (by positivity)]
      exact hTpack
    have hval : (ρ + δ / 4) ^ d / (δ / 4) ^ d = (1 + 8 * Real.sqrt V / δ) ^ d := by
      rw [← div_pow]
      congr 1
      rw [hρ]
      field_simp
      ring
    rw [hval] at hdiv
    exact hdiv
  have hstep : (9 : ℝ) / 16 ≤ (1 + 8 * Real.sqrt V / δ) ^ d * ∑ t ∈ T, (b t) ^ 2 := by
    have hSnn : (0 : ℝ) ≤ ∑ t ∈ T, (b t) ^ 2 :=
      Finset.sum_nonneg fun t _ => sq_nonneg _
    nlinarith [hsq, hB, hSnn]
  rw [div_le_iff₀ hBpos]
  calc (9 : ℝ) / 16 ≤ (1 + 8 * Real.sqrt V / δ) ^ d * ∑ t ∈ T, (b t) ^ 2 := hstep
    _ ≤ (1 + 8 * Real.sqrt V / δ) ^ d * vectorLawWithinMass a X δ := by
        exact mul_le_mul_of_nonneg_left hpairs hBpos.le
    _ = vectorLawWithinMass a X δ * (1 + 8 * Real.sqrt V / δ) ^ d := by ring

/-- The off-diagonal form: the near mass of distinct pairs is the within mass minus the diagonal
mass. -/
theorem vectorLawOffDiagonalWithinMass_eq (a : A → ℝ) (X : A → E) {δ : ℝ} (hδ : 0 < δ) :
    vectorLawOffDiagonalWithinMass a X δ =
      vectorLawWithinMass a X δ - vectorLawDiagonalMass a := by
  classical
  rw [vectorLawOffDiagonalWithinMass, vectorLawWithinMass, vectorLawDiagonalMass,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hstep : ∀ β : A,
      (if α ≠ β ∧ ‖X α - X β‖ < δ then a α * a β else 0) =
        (if ‖X α - X β‖ < δ then a α * a β else 0) - (if β = α then a α * a α else 0) := by
    intro β
    by_cases hβ : β = α
    · subst hβ
      rw [if_neg (by simp), sub_self (X β), norm_zero, if_pos hδ, if_pos rfl, sub_self]
    · rw [if_neg hβ, sub_zero]
      by_cases hd : ‖X α - X β‖ < δ
      · rw [if_pos ⟨fun h => hβ h.symm, hd⟩, if_pos hd]
      · rw [if_neg (fun h => hd h.2), if_neg hd]
  rw [Finset.sum_congr rfl fun β (_ : β ∈ Finset.univ) => hstep β, Finset.sum_sub_distrib]
  congr 1
  simp

/-- **Theorem B in the card's form.**  The mass of distinct pairs whose observed vectors are closer
than `δ` is at least `9/(16 (1 + 8√V/δ)^d)` minus the collision mass. -/
theorem vectorLaw_offDiagonal_crowding_floor (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : A → ℝ} {X : A → E} (hnn : ∀ α, 0 ≤ a α) (hsum : ∑ α, a α = 1)
    (c : E) {V : ℝ} (hV : 0 ≤ V) (hmom : ∑ α, a α * ‖X α - c‖ ^ 2 ≤ V) {δ : ℝ} (hδ : 0 < δ) :
    (9 : ℝ) / 16 / (1 + 8 * Real.sqrt V / δ) ^ (Module.finrank ℝ E) - vectorLawDiagonalMass a ≤
      vectorLawOffDiagonalWithinMass a X δ := by
  rw [vectorLawOffDiagonalWithinMass_eq a X hδ]
  have := vectorLaw_crowding_floor μ hnn hsum c hV hmom hδ
  linarith


/-! ## Splitting by an arbitrary collision key -/

variable {K : Type*} [DecidableEq K]

/-- Mass of all ordered pairs carrying the same key. -/
def vectorLawKeyCollisionMass (a : A → ℝ) (key : A → K) : ℝ :=
  ∑ α, ∑ β, if key α = key β then a α * a β else 0

/-- Mass of all ordered pairs with distinct keys whose observed vectors are closer than `δ`. -/
def vectorLawOffKeyWithinMass (a : A → ℝ) (X : A → E) (key : A → K) (δ : ℝ) : ℝ :=
  ∑ α, ∑ β, if key α ≠ key β ∧ ‖X α - X β‖ < δ then a α * a β else 0

/-- When the observed vector factors through the key, the within mass splits exactly into the key
collision mass and the distinct-key near mass. -/
theorem vectorLawOffKeyWithinMass_eq (a : A → ℝ) (X : A → E) (key : A → K)
    (hfac : ∀ α β, key α = key β → X α = X β) {δ : ℝ} (hδ : 0 < δ) :
    vectorLawOffKeyWithinMass a X key δ =
      vectorLawWithinMass a X δ - vectorLawKeyCollisionMass a key := by
  classical
  rw [vectorLawOffKeyWithinMass, vectorLawWithinMass, vectorLawKeyCollisionMass,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  by_cases hk : key α = key β
  · have hx : X α = X β := hfac α β hk
    rw [if_neg (fun h => h.1 hk), if_pos hk, hx, sub_self, norm_zero, if_pos hδ, sub_self]
  · rw [if_neg hk, sub_zero]
    by_cases hd : ‖X α - X β‖ < δ
    · rw [if_pos ⟨hk, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2), if_neg hd]

/-- **Theorem B for an arbitrary collision key.**  The distinct-key near mass is at least the
crowding floor minus the key collision mass. -/
theorem vectorLaw_offKey_crowding_floor (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : A → ℝ} {X : A → E} (key : A → K) (hnn : ∀ α, 0 ≤ a α) (hsum : ∑ α, a α = 1)
    (hfac : ∀ α β, key α = key β → X α = X β)
    (c : E) {V : ℝ} (hV : 0 ≤ V) (hmom : ∑ α, a α * ‖X α - c‖ ^ 2 ≤ V) {δ : ℝ} (hδ : 0 < δ) :
    (9 : ℝ) / 16 / (1 + 8 * Real.sqrt V / δ) ^ (Module.finrank ℝ E) -
        vectorLawKeyCollisionMass a key ≤
      vectorLawOffKeyWithinMass a X key δ := by
  rw [vectorLawOffKeyWithinMass_eq a X key hfac hδ]
  have hfloor := vectorLaw_crowding_floor μ hnn hsum c hV hmom hδ
  linarith

end GaloisForLFunctions.HTGeometry
