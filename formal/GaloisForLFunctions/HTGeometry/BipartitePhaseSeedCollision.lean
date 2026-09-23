import GaloisForLFunctions.HTGeometry.SteinhausFourthMoment
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Product phase seeds have small spectral collision in every bipartite basis

A product of two independent uniform phase vectors, one on each factor of a bipartite index set,
pairs with any fixed unit vector in a fourth moment governed by the frequency multiplicity of the
squared expansion.  The squared pairing is a character combination whose frequency is the pair of
unordered index pairs of the two factors, so each frequency is carried by at most four terms, and
Parseval gives a fourth moment at most `4 / D²` for one unit vector, hence at most `4 / D` summed
over an orthonormal basis of the bipartite space.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance bipartitePhaseSeedCollisionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance bipartitePhaseSeedCollisionIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance bipartitePhaseSeedCollisionIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

section Multiplicity

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Boundedly integrable real reporters on the box. -/
theorem integrableOn_box_of_bounded_real {G : (d → ℝ) → ℝ} (hG : Continuous G) {C : ℝ}
    (hC : ∀ x, ‖G x‖ ≤ C) : IntegrableOn G (torusBox d) volume := by
  haveI := isFiniteMeasure_restrict_torusBox (d := d)
  exact Integrable.of_bound hG.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

/-- **Parseval with bounded frequency multiplicity.**  If every frequency of a character
combination is carried by at most `N` terms, the mean square is at most `N` times the squared
coefficient sum. -/
theorem integral_box_normSq_trigLift_le_mul {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ))
    (a : ι → ℂ) {N : ℝ}
    (hN : ∀ p ∈ P, (((P.filter fun q => ν p = ν q).card : ℕ) : ℝ) ≤ N) :
    (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ (2 : ℕ)) ≤ N * ∑ p ∈ P, ‖a p‖ ^ (2 : ℕ) := by
  classical
  have hnn : 0 ≤ ∫ x in torusBox d, ‖trigLift P ν a x‖ ^ (2 : ℕ) :=
    integral_nonneg fun x => sq_nonneg _
  have heq := ofReal_integral_box_normSq_trigLift P ν a
  have hnorm : (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ (2 : ℕ)) =
      ‖∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0‖ := by
    rw [← heq, Complex.norm_real, Real.norm_of_nonneg hnn]
  have hstep : ‖∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0‖ ≤
      ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then (‖a p‖ ^ (2 : ℕ) + ‖a q‖ ^ (2 : ℕ)) / 2 else 0 := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun q _ => ?_)
    by_cases h : ν p = ν q
    · rw [if_pos h, if_pos h, norm_mul, RCLike.norm_conj]
      nlinarith [sq_nonneg (‖a p‖ - ‖a q‖)]
    · rw [if_neg h, if_neg h, norm_zero]
  have hsym : (∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a q‖ ^ (2 : ℕ) else 0) =
      ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a p‖ ^ (2 : ℕ) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    exact if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl
  have hAB : (∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then (‖a p‖ ^ (2 : ℕ) + ‖a q‖ ^ (2 : ℕ)) / 2 else 0) * 2 =
      (∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a p‖ ^ (2 : ℕ) else 0) +
        ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a q‖ ^ (2 : ℕ) else 0 := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : ν p = ν q
    · rw [if_pos h, if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h, if_neg h]
      ring
  rw [hsym] at hAB
  have hsplit : (∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then (‖a p‖ ^ (2 : ℕ) + ‖a q‖ ^ (2 : ℕ)) / 2 else 0) =
      ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a p‖ ^ (2 : ℕ) else 0 := by linarith
  have hrow : ∀ p ∈ P, (∑ q ∈ P, if ν p = ν q then ‖a p‖ ^ (2 : ℕ) else 0) ≤ N * ‖a p‖ ^ (2 : ℕ) := by
    intro p hp
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hN p hp) (sq_nonneg _)
  calc (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ (2 : ℕ))
      = ‖∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then a p * (starRingEnd ℂ) (a q) else 0‖ := hnorm
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then (‖a p‖ ^ (2 : ℕ) + ‖a q‖ ^ (2 : ℕ)) / 2 else 0 := hstep
    _ = ∑ p ∈ P, ∑ q ∈ P, if ν p = ν q then ‖a p‖ ^ (2 : ℕ) else 0 := hsplit
    _ ≤ ∑ p ∈ P, N * ‖a p‖ ^ (2 : ℕ) := Finset.sum_le_sum hrow
    _ = N * ∑ p ∈ P, ‖a p‖ ^ (2 : ℕ) := (Finset.mul_sum _ _ _).symm

end Multiplicity

section Bipartite

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The frequency of a pair of bipartite indices: one unit on each of the four coordinates it
touches. -/
def prodPairFreq (p : (α × β) × (α × β)) : (α ⊕ β) → ℤ :=
  Pi.single (Sum.inl p.1.1) 1 + Pi.single (Sum.inl p.2.1) 1 +
    (Pi.single (Sum.inr p.1.2) 1 + Pi.single (Sum.inr p.2.2) 1)

theorem pairFreq_inl_of_prodPairFreq {p q : (α × β) × (α × β)}
    (h : prodPairFreq p = prodPairFreq q) :
    pairFreq (p.1.1, p.2.1) = pairFreq (q.1.1, q.2.1) := by
  funext u
  have hu := congrFun h (Sum.inl u)
  simpa [prodPairFreq, pairFreq, Pi.single_apply] using hu

theorem pairFreq_inr_of_prodPairFreq {p q : (α × β) × (α × β)}
    (h : prodPairFreq p = prodPairFreq q) :
    pairFreq (p.1.2, p.2.2) = pairFreq (q.1.2, q.2.2) := by
  funext v
  have hv := congrFun h (Sum.inr v)
  simpa [prodPairFreq, pairFreq, Pi.single_apply] using hv

/-- **At most four terms share a frequency.**  The two factor pairs are determined as unordered
pairs, so each admits one transposition. -/
theorem card_filter_prodPairFreq_le (p : (α × β) × (α × β)) :
    (((Finset.univ.filter fun q : (α × β) × (α × β) =>
      prodPairFreq p = prodPairFreq q).card : ℕ) : ℝ) ≤ 4 := by
  classical
  have hsub : (Finset.univ.filter fun q : (α × β) × (α × β) =>
        prodPairFreq p = prodPairFreq q) ⊆
      ({p, ((p.1.1, p.2.2), (p.2.1, p.1.2)), ((p.2.1, p.1.2), (p.1.1, p.2.2)), (p.2, p.1)} :
        Finset ((α × β) × (α × β))) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    have hA := pairFreq_eq_iff (pairFreq_inl_of_prodPairFreq hq.2)
    have hB := pairFreq_eq_iff (pairFreq_inr_of_prodPairFreq hq.2)
    obtain ⟨⟨u, v⟩, ⟨u', v'⟩⟩ := q
    obtain ⟨⟨x, y⟩, ⟨x', y'⟩⟩ := p
    simp only [Prod.mk.injEq] at hA hB
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hB with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;> simp
  have hcard : ({p, ((p.1.1, p.2.2), (p.2.1, p.1.2)), ((p.2.1, p.1.2), (p.1.1, p.2.2)), (p.2, p.1)} :
      Finset ((α × β) × (α × β))).card ≤ 4 := by
    calc ({p, ((p.1.1, p.2.2), (p.2.1, p.1.2)), ((p.2.1, p.1.2), (p.1.1, p.2.2)), (p.2, p.1)} :
          Finset ((α × β) × (α × β))).card
        ≤ ({((p.1.1, p.2.2), (p.2.1, p.1.2)), ((p.2.1, p.1.2), (p.1.1, p.2.2)), (p.2, p.1)} :
            Finset ((α × β) × (α × β))).card + 1 := Finset.card_insert_le _ _
      _ ≤ (({((p.2.1, p.1.2), (p.1.1, p.2.2)), (p.2, p.1)} :
            Finset ((α × β) × (α × β))).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ((({(p.2, p.1)} : Finset ((α × β) × (α × β))).card + 1) + 1) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ = 4 := by simp
  exact_mod_cast le_trans (Finset.card_le_card hsub) hcard

/-- The unnormalized product phase vector: one independent uniform phase per index of each
factor. -/
def phaseVec (θ : (α ⊕ β) → ℝ) : α × β → ℂ :=
  fun p => charLift (Pi.single (Sum.inl p.1) 1) θ * charLift (Pi.single (Sum.inr p.2) 1) θ

theorem norm_phaseVec (θ : (α ⊕ β) → ℝ) (p : α × β) : ‖phaseVec θ p‖ = 1 := by
  rw [phaseVec, norm_mul, norm_charLift, norm_charLift, mul_one]

theorem continuous_phaseVec_apply (p : α × β) :
    Continuous fun θ : (α ⊕ β) → ℝ => phaseVec θ p :=
  (continuous_charLift _).mul (continuous_charLift _)

theorem continuous_inner_phaseVec (e : α × β → ℂ) :
    Continuous fun θ : (α ⊕ β) → ℝ => finiteComplexInner e (phaseVec θ) := by
  refine continuous_finsetSum (Finset.univ : Finset (α × β)) fun p _ => ?_
  exact continuous_const.mul (continuous_phaseVec_apply p)

theorem norm_inner_phaseVec_le (e : α × β → ℂ) (θ : (α ⊕ β) → ℝ) :
    ‖finiteComplexInner e (phaseVec θ)‖ ≤ ∑ p, ‖e p‖ := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, RCLike.norm_conj, norm_phaseVec, mul_one]

/-- **The squared pairing is a character combination.**  Its frequency is the pair of factor index
pairs. -/
theorem sq_inner_phaseVec (e : α × β → ℂ) (θ : (α ⊕ β) → ℝ) :
    finiteComplexInner e (phaseVec θ) ^ (2 : ℕ) =
      trigLift (Finset.univ : Finset ((α × β) × (α × β))) prodPairFreq
        (fun pq => (starRingEnd ℂ) (e pq.1) * (starRingEnd ℂ) (e pq.2)) θ := by
  classical
  have hR : trigLift (Finset.univ : Finset ((α × β) × (α × β))) prodPairFreq
      (fun pq => (starRingEnd ℂ) (e pq.1) * (starRingEnd ℂ) (e pq.2)) θ =
      ∑ p : α × β, ∑ q : α × β,
        (starRingEnd ℂ) (e p) * (starRingEnd ℂ) (e q) * charLift (prodPairFreq (p, q)) θ := by
    rw [trigLift, Fintype.sum_prod_type]
  rw [hR, sq, finiteComplexInner, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [prodPairFreq, charLift_add_index, charLift_add_index, charLift_add_index, phaseVec, phaseVec]
  ring

/-- **Fourth moment of the unnormalized product phase pairing.** -/
theorem integral_box_inner_phaseVec_fourth_le (e : α × β → ℂ) :
    (∫ θ in torusBox (α ⊕ β), ‖finiteComplexInner e (phaseVec θ)‖ ^ (4 : ℕ)) ≤
      4 * (∑ p, ‖e p‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  classical
  have hpt : ∀ θ : (α ⊕ β) → ℝ, ‖finiteComplexInner e (phaseVec θ)‖ ^ (4 : ℕ) =
      ‖trigLift (Finset.univ : Finset ((α × β) × (α × β))) prodPairFreq
        (fun pq => (starRingEnd ℂ) (e pq.1) * (starRingEnd ℂ) (e pq.2)) θ‖ ^ (2 : ℕ) := by
    intro θ
    rw [← sq_inner_phaseVec e θ, norm_pow, ← pow_mul]
  simp_rw [hpt]
  refine le_trans (integral_box_normSq_trigLift_le_mul (Finset.univ : Finset ((α × β) × (α × β)))
    prodPairFreq _ (N := 4) fun p _ => card_filter_prodPairFreq_le p) ?_
  have hcoeff : (∑ pq : (α × β) × (α × β),
      ‖(starRingEnd ℂ) (e pq.1) * (starRingEnd ℂ) (e pq.2)‖ ^ (2 : ℕ)) = (∑ p, ‖e p‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
    rw [sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [norm_mul, RCLike.norm_conj, RCLike.norm_conj, mul_pow]
  rw [hcoeff]

/-- The normalized product phase seed. -/
def prodPhaseSeed (θ : (α ⊕ β) → ℝ) : α × β → ℂ :=
  fun p => ((Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) : ℝ) : ℂ)⁻¹ * phaseVec θ p

theorem sum_normSq_prodPhaseSeed [Nonempty α] [Nonempty β] (θ : (α ⊕ β) → ℝ) :
    (∑ p, ‖prodPhaseSeed θ p‖ ^ (2 : ℕ)) = 1 := by
  classical
  have hD : (0 : ℝ) < (Fintype.card α : ℝ) * Fintype.card β := by
    have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
    have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
    exact mul_pos hα hβ
  have hsqrt : Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) =
      (Fintype.card α : ℝ) * Fintype.card β := Real.sq_sqrt hD.le
  have hne : Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hD)
  have hterm : ∀ p : α × β, ‖prodPhaseSeed θ p‖ ^ (2 : ℕ) =
      ((Fintype.card α : ℝ) * Fintype.card β)⁻¹ := by
    intro p
    rw [prodPhaseSeed, norm_mul, norm_phaseVec, mul_one, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow, hsqrt]
  rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_prod]
  push_cast
  field_simp

/-- **Equation `(9)` for one basis vector.**  A product phase seed pairs with any fixed unit vector
of the bipartite space in fourth moment at most `4 / D²`. -/
theorem integral_box_inner_prodPhaseSeed_fourth_le (e : α × β → ℂ) :
    (∫ θ in torusBox (α ⊕ β), ‖finiteComplexInner e (prodPhaseSeed θ)‖ ^ (4 : ℕ)) ≤
      4 * (∑ p, ‖e p‖ ^ (2 : ℕ)) ^ (2 : ℕ) / ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) := by
  classical
  have hD : (0 : ℝ) ≤ (Fintype.card α : ℝ) * Fintype.card β := by positivity
  have hsqrt : Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) =
      (Fintype.card α : ℝ) * Fintype.card β := Real.sq_sqrt hD
  have hlin : ∀ θ : (α ⊕ β) → ℝ, finiteComplexInner e (prodPhaseSeed θ) =
      ((Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) : ℝ) : ℂ)⁻¹ *
        finiteComplexInner e (phaseVec θ) := by
    intro θ
    rw [finiteComplexInner, finiteComplexInner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prodPhaseSeed]
    ring
  have hpt : ∀ θ : (α ⊕ β) → ℝ, ‖finiteComplexInner e (prodPhaseSeed θ)‖ ^ (4 : ℕ) =
      (((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ))⁻¹ *
        ‖finiteComplexInner e (phaseVec θ)‖ ^ (4 : ℕ) := by
    intro θ
    rw [hlin θ, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
    congr 2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsqrt]
  simp_rw [hpt]
  rw [integral_const_mul, div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left (integral_box_inner_phaseVec_fourth_le e) ?_
  positivity

/-- **Equation `(9)`.**  Summed over an orthonormal family of the bipartite space, the fourth
moment of the product phase seed is at most `4 |ι| / D²`; at `|ι| = D` this is `4 / D`. -/
theorem integral_box_sum_inner_prodPhaseSeed_fourth_le {ι : Type*} [Fintype ι]
    (e : ι → α × β → ℂ) (he : ∀ j, (∑ p, ‖e j p‖ ^ (2 : ℕ)) = 1) :
    (∫ θ in torusBox (α ⊕ β), ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ)) ≤
      4 * (Fintype.card ι : ℝ) / ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) := by
  classical
  have hint : ∀ j : ι, IntegrableOn
      (fun θ : (α ⊕ β) → ℝ => ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      (torusBox (α ⊕ β)) volume := by
    intro j
    have hcont : Continuous fun θ : (α ⊕ β) → ℝ =>
        ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ) := by
      have hc : Continuous fun θ : (α ⊕ β) → ℝ => finiteComplexInner (e j) (prodPhaseSeed θ) := by
        refine continuous_finsetSum (Finset.univ : Finset (α × β)) fun p _ => ?_
        exact continuous_const.mul (continuous_const.mul (continuous_phaseVec_apply p))
      exact (hc.norm).pow 4
    refine integrableOn_box_of_bounded_real hcont
      (C := (∑ p, ‖e j p‖ * ‖((Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) : ℝ) : ℂ)⁻¹‖) ^ (4 : ℕ))
      fun θ => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 4
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
    rw [prodPhaseSeed, norm_mul, RCLike.norm_conj, norm_mul, norm_phaseVec, mul_one]
  rw [integral_finsetSum _ fun j _ => hint j]
  calc (∑ j : ι, ∫ θ in torusBox (α ⊕ β), ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      ≤ ∑ _j : ι, 4 * (1 : ℝ) ^ (2 : ℕ) / ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have := integral_box_inner_prodPhaseSeed_fourth_le (e j)
        rwa [he j] at this
    _ = 4 * (Fintype.card ι : ℝ) / ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring

end Bipartite

end GaloisForLFunctions.HTGeometry
