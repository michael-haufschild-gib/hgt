/-
# The bipartite eighth-root transfer

Two independent eighth-root ensembles, one on each factor of a bipartite register, kill every
nontrivial character of the sum index whose support is small on each side: a character of `α ⊕ β`
factorizes, and whichever half carries a nonzero residue averages to zero.  The bipartite collision
is a trigonometric polynomial on eight coordinates with entries of absolute value at most four, so
its Steinhaus mean transfers verbatim to the finite product cubic-phase ensemble, and one product
cubic seed has spectral collision at most `4/D` against any orthonormal basis of the bipartite
space.

Main results:
* `charLift_eighthPhase_sumElim`, `eighthPhaseUniform_sumElim` — the product uniformity.
* `prodQuarticSum_eq_trigLift` — **the bipartite collision as a trigonometric polynomial**.
* `average_prodQuarticSum_polyEval_eq_integral`, `average_prodCollision_polyEval_eq_integral` —
  the moment transfer.
* `exists_prodPolyEval_collision_le_four_div` — **Theorem B for the finite product ensemble**.
-/
import GaloisForLFunctions.HTGeometry.CubicPhaseCollisionTransfer
import GaloisForLFunctions.HTGeometry.BipartiteSeedSelection

open Finset MeasureTheory

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A character of a sum index at a pair of eighth-root phases factorizes. -/
theorem charLift_eighthPhase_sumElim (n : (α ⊕ β) → ℤ) (wA : α → ZMod 8) (wB : β → ZMod 8) :
    charLift n (eighthPhase (Sum.elim wA wB))
      = charLift (fun a => n (Sum.inl a)) (eighthPhase wA)
        * charLift (fun b => n (Sum.inr b)) (eighthPhase wB) := by
  rw [charLift_eighthPhase, charLift_eighthPhase, charLift_eighthPhase, Fintype.prod_sum_type]
  rfl

theorem card_freqSupport_comp_inl_le (n : (α ⊕ β) → ℤ) :
    (freqSupport (fun a => n (Sum.inl a))).card ≤ (freqSupport n).card := by
  classical
  refine Finset.card_le_card_of_injOn Sum.inl ?_ (fun a _ b _ h => Sum.inl_injective h)
  intro a ha
  simp only [Finset.coe_filter, Set.mem_setOf_eq, freqSupport] at ha ⊢
  exact ⟨Finset.mem_univ _, ha.2⟩

theorem card_freqSupport_comp_inr_le (n : (α ⊕ β) → ℤ) :
    (freqSupport (fun b => n (Sum.inr b))).card ≤ (freqSupport n).card := by
  classical
  refine Finset.card_le_card_of_injOn Sum.inr ?_ (fun a _ b _ h => Sum.inr_injective h)
  intro b hb
  simp only [Finset.coe_filter, Set.mem_setOf_eq, freqSupport] at hb ⊢
  exact ⟨Finset.mem_univ _, hb.2⟩

/-- **Two independent low-support-uniform ensembles give one on the sum index.** -/
theorem eighthPhaseUniform_sumElim {ΩA ΩB : Type*} [Fintype ΩA] [Fintype ΩB]
    (evA : ΩA → (α → ZMod 8)) (evB : ΩB → (β → ZMod 8)) {K : ℕ}
    (hA : EighthPhaseUniform evA K) (hB : EighthPhaseUniform evB K) :
    EighthPhaseUniform (fun h : ΩA × ΩB => Sum.elim (evA h.1) (evB h.2)) K := by
  classical
  rintro n hcard ⟨t₀, ht₀⟩
  have hsplit : ∀ h : ΩA × ΩB,
      charLift n (eighthPhase (Sum.elim (evA h.1) (evB h.2)))
        = charLift (fun a => n (Sum.inl a)) (eighthPhase (evA h.1))
          * charLift (fun b => n (Sum.inr b)) (eighthPhase (evB h.2)) :=
    fun h => charLift_eighthPhase_sumElim n (evA h.1) (evB h.2)
  rw [Finset.sum_congr rfl (fun h _ => hsplit h), Fintype.sum_prod_type]
  have hfac : ∑ hA' : ΩA, ∑ hB' : ΩB,
      charLift (fun a => n (Sum.inl a)) (eighthPhase (evA hA'))
        * charLift (fun b => n (Sum.inr b)) (eighthPhase (evB hB'))
      = (∑ hA' : ΩA, charLift (fun a => n (Sum.inl a)) (eighthPhase (evA hA')))
        * (∑ hB' : ΩB, charLift (fun b => n (Sum.inr b)) (eighthPhase (evB hB'))) := by
    rw [Finset.sum_mul_sum]
  rw [hfac]
  cases t₀ with
  | inl a₀ =>
      rw [hA (fun a => n (Sum.inl a)) (le_trans (card_freqSupport_comp_inl_le n) hcard)
        ⟨a₀, ht₀⟩, zero_mul]
  | inr b₀ =>
      rw [hB (fun b => n (Sum.inr b)) (le_trans (card_freqSupport_comp_inr_le n) hcard)
        ⟨b₀, ht₀⟩, mul_zero]


section Collision

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem conj_trigLift {κ : Type*} (P : Finset κ) (ν : κ → ((α ⊕ β) → ℤ)) (a : κ → ℂ)
    (x : (α ⊕ β) → ℝ) :
    (starRingEnd ℂ) (trigLift P ν a x)
      = trigLift P (fun p => -(ν p)) (fun p => (starRingEnd ℂ) (a p)) x := by
  rw [trigLift, trigLift, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul, charLift_neg_index]

/-- The frequency of a quartic term of the bipartite collision. -/
def prodCollFreq (pq : ((α × β) × (α × β)) × ((α × β) × (α × β))) : (α ⊕ β) → ℤ :=
  prodPairFreq pq.1 + -(prodPairFreq pq.2)

/-- The coefficient of a quartic term of the bipartite collision. -/
def prodCollCoeff (e : ι → α × β → ℂ)
    (pq : ((α × β) × (α × β)) × ((α × β) × (α × β))) : ℂ :=
  ∑ j, ((starRingEnd ℂ) (e j pq.1.1) * (starRingEnd ℂ) (e j pq.1.2)) *
    ((starRingEnd ℂ) ((starRingEnd ℂ) (e j pq.2.1) * (starRingEnd ℂ) (e j pq.2.2)))

/-- The unnormalized bipartite collision. -/
def prodQuarticSum (e : ι → α × β → ℂ) (θ : (α ⊕ β) → ℝ) : ℝ :=
  ∑ j, ‖finiteComplexInner (e j) (phaseVec θ)‖ ^ (4 : ℕ)

/-- **The bipartite collision is a trigonometric polynomial** on eight register coordinates. -/
theorem prodQuarticSum_eq_trigLift (e : ι → α × β → ℂ) (θ : (α ⊕ β) → ℝ) :
    ((prodQuarticSum e θ : ℝ) : ℂ)
      = trigLift (Finset.univ : Finset (((α × β) × (α × β)) × ((α × β) × (α × β))))
          prodCollFreq (prodCollCoeff e) θ := by
  classical
  have hterm : ∀ j : ι, ((‖finiteComplexInner (e j) (phaseVec θ)‖ ^ (4 : ℕ) : ℝ) : ℂ)
      = trigLift (Finset.univ : Finset (((α × β) × (α × β)) × ((α × β) × (α × β))))
          prodCollFreq
          (fun pq => ((starRingEnd ℂ) (e j pq.1.1) * (starRingEnd ℂ) (e j pq.1.2)) *
            ((starRingEnd ℂ) ((starRingEnd ℂ) (e j pq.2.1) *
              (starRingEnd ℂ) (e j pq.2.2)))) θ := by
    intro j
    obtain ⟨z, hz⟩ : ∃ z, z = finiteComplexInner (e j) (phaseVec θ) := ⟨_, rfl⟩
    have hquartic : ((‖z‖ ^ (4 : ℕ) : ℝ) : ℂ) = z ^ (2 : ℕ) * (starRingEnd ℂ) (z ^ (2 : ℕ)) := by
      rw [map_pow, ← mul_pow, Complex.mul_conj,
        show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm]
      push_cast
      ring
    rw [hz] at hquartic
    rw [hquartic, sq_inner_phaseVec, conj_trigLift, trigLift_mul]
    rfl
  rw [prodQuarticSum, Complex.ofReal_sum, Finset.sum_congr rfl (fun j _ => hterm j)]
  simp only [trigLift]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [prodCollCoeff, Finset.sum_mul]


theorem freqSupport_prodPairFreq_subset (p : (α × β) × (α × β)) :
    freqSupport (prodPairFreq p)
      ⊆ ({Sum.inl p.1.1, Sum.inl p.2.1, Sum.inr p.1.2, Sum.inr p.2.2} : Finset (α ⊕ β)) := by
  classical
  intro t ht
  by_contra hcon
  refine absurd (notMem_freqSupport_iff.mpr ?_) (fun h => h ht)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
  rw [prodPairFreq]
  simp only [Pi.add_apply, Pi.single_apply]
  rw [if_neg (fun h => hcon.1 h), if_neg (fun h => hcon.2.1 h),
    if_neg (fun h => hcon.2.2.1 h), if_neg (fun h => hcon.2.2.2 h)]
  ring

theorem card_freqSupport_prodPairFreq_le (p : (α × β) × (α × β)) :
    (freqSupport (prodPairFreq p)).card ≤ 4 := by
  classical
  refine le_trans (Finset.card_le_card (freqSupport_prodPairFreq_subset p)) ?_
  exact le_trans (Finset.card_insert_le _ _)
    (by
      refine Nat.succ_le_succ ?_
      exact le_trans (Finset.card_insert_le _ _)
        (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _)
          (Nat.succ_le_succ (le_of_eq (Finset.card_singleton _))))))

theorem abs_prodPairFreq_le (p : (α × β) × (α × β)) (t : α ⊕ β) : |prodPairFreq p t| ≤ 2 := by
  classical
  rw [prodPairFreq]
  cases t with
  | inl a =>
      simp only [Pi.add_apply, Pi.single_apply]
      rw [if_neg (by simp : ¬ (Sum.inl a : α ⊕ β) = Sum.inr p.1.2),
        if_neg (by simp : ¬ (Sum.inl a : α ⊕ β) = Sum.inr p.2.2)]
      split_ifs <;> norm_num
  | inr b =>
      simp only [Pi.add_apply, Pi.single_apply]
      rw [if_neg (by simp : ¬ (Sum.inr b : α ⊕ β) = Sum.inl p.1.1),
        if_neg (by simp : ¬ (Sum.inr b : α ⊕ β) = Sum.inl p.2.1)]
      split_ifs <;> norm_num

theorem card_freqSupport_prodCollFreq_le
    (pq : ((α × β) × (α × β)) × ((α × β) × (α × β))) :
    (freqSupport (prodCollFreq pq)).card ≤ 8 := by
  classical
  have hsub : freqSupport (prodCollFreq pq)
      ⊆ freqSupport (prodPairFreq pq.1) ∪ freqSupport (prodPairFreq pq.2) := by
    intro t ht
    by_contra hcon
    rw [Finset.mem_union, not_or] at hcon
    refine absurd (notMem_freqSupport_iff.mpr ?_) (fun h => h ht)
    rw [prodCollFreq]
    show prodPairFreq pq.1 t + -(prodPairFreq pq.2 t) = 0
    rw [notMem_freqSupport_iff.mp hcon.1, notMem_freqSupport_iff.mp hcon.2]
    ring
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  exact Nat.add_le_add (card_freqSupport_prodPairFreq_le pq.1)
    (card_freqSupport_prodPairFreq_le pq.2)

theorem exists_prodCollFreq_ne_zero_mod_eight
    {pq : ((α × β) × (α × β)) × ((α × β) × (α × β))} (h : prodCollFreq pq ≠ 0) :
    ∃ t, ((prodCollFreq pq t : ℤ) : ZMod 8) ≠ 0 := by
  obtain ⟨t, ht⟩ : ∃ t, prodCollFreq pq t ≠ 0 := by
    by_contra hcon
    exact h (funext fun t => not_not.mp (fun hc => hcon ⟨t, hc⟩))
  refine ⟨t, intCast_zmod_eight_ne_zero_of_abs_le ht ?_⟩
  have h1 := abs_prodPairFreq_le pq.1 t
  have h2 := abs_prodPairFreq_le pq.2 t
  have hval : prodCollFreq pq t = prodPairFreq pq.1 t + -(prodPairFreq pq.2 t) := rfl
  rw [hval]
  have := abs_add_le (prodPairFreq pq.1 t) (-(prodPairFreq pq.2 t))
  rw [abs_neg] at this
  omega

end Collision


section Transfer

variable {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product cubic-phase evaluation of a pair of degree-`≤ m` polynomials. -/
def prodPolyEval (m : ℕ) (c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) :
    ((ιA → Bool) ⊕ (ιB → Bool)) → ZMod 8 :=
  Sum.elim (polyEval m c.1) (polyEval m c.2)

theorem eighthPhaseUniform_prodPolyEval (m : ℕ) :
    EighthPhaseUniform (prodPolyEval (ιA := ιA) (ιB := ιB) m) (2 ^ (m + 1) - 1) :=
  eighthPhaseUniform_sumElim (polyEval m) (polyEval m)
    (eighthPhaseUniform_polyEval m) (eighthPhaseUniform_polyEval m)

/-- **The bipartite collision moment of the finite product cubic ensemble is the Steinhaus
one.** -/
theorem average_prodQuarticSum_polyEval_eq_integral (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : ι → ((ιA → Bool) × (ιB → Bool)) → ℂ) :
    ((Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) : ℝ))⁻¹ *
        ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
          prodQuarticSum e (eighthPhase (prodPolyEval m c))
      = ∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)), prodQuarticSum e θ := by
  classical
  haveI : Nonempty ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) :=
    ⟨⟨fun _ => 0, fun _ => 0⟩⟩
  have hcomplex : ((Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) : ℂ))⁻¹ *
      ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
        ((prodQuarticSum e (eighthPhase (prodPolyEval m c)) : ℝ) : ℂ)
      = ∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)),
          ((prodQuarticSum e θ : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl (fun c _ =>
      prodQuarticSum_eq_trigLift e (eighthPhase (prodPolyEval m c)))]
    rw [average_trigLift_eighthPhase_eq_integral_box (prodPolyEval m)
      (eighthPhaseUniform_prodPolyEval m) _ _ _
      (fun pq _ => le_trans (card_freqSupport_prodCollFreq_le pq) hm)
      (fun pq _ hpq => exists_prodCollFreq_ne_zero_mod_eight hpq)]
    refine setIntegral_congr_fun measurableSet_torusBox fun θ _ => ?_
    exact (prodQuarticSum_eq_trigLift e θ).symm
  have hint : ∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)), ((prodQuarticSum e θ : ℝ) : ℂ)
      = ((∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)), prodQuarticSum e θ : ℝ) : ℂ) :=
    integral_ofReal
  rw [hint] at hcomplex
  refine Complex.ofReal_injective ?_
  push_cast
  exact hcomplex


theorem sum_inner_prodPhaseSeed_fourth_eq (e : ι → α × β → ℂ) (θ : (α ⊕ β) → ℝ) :
    (∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      = (((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ))⁻¹ * prodQuarticSum e θ := by
  classical
  have hD : (0 : ℝ) ≤ (Fintype.card α : ℝ) * Fintype.card β := by positivity
  have hsqrt : Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ) =
      (Fintype.card α : ℝ) * Fintype.card β := Real.sq_sqrt hD
  have hpt : ∀ j : ι, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ)
      = (((Fintype.card α : ℝ) * Fintype.card β) ^ (2 : ℕ))⁻¹ *
        ‖finiteComplexInner (e j) (phaseVec θ)‖ ^ (4 : ℕ) := by
    intro j
    have hlin : finiteComplexInner (e j) (prodPhaseSeed θ) =
        ((Real.sqrt ((Fintype.card α : ℝ) * Fintype.card β) : ℝ) : ℂ)⁻¹ *
          finiteComplexInner (e j) (phaseVec θ) := by
      rw [finiteComplexInner, finiteComplexInner, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [prodPhaseSeed]
      ring
    rw [hlin, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
    congr 2
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsqrt]
  rw [Finset.sum_congr rfl (fun j _ => hpt j), prodQuarticSum, Finset.mul_sum]

/-- **The bipartite collision moment of the product cubic ensemble is the Steinhaus one**, in the
normalized seed. -/
theorem average_prodCollision_polyEval_eq_integral (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : ι → ((ιA → Bool) × (ιB → Bool)) → ℂ) :
    ((Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) : ℝ))⁻¹ *
        ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
          (∑ j, ‖finiteComplexInner (e j)
            (prodPhaseSeed (eighthPhase (prodPolyEval m c)))‖ ^ (4 : ℕ))
      = ∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)),
          ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ) := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ((Fintype.card (ιA → Bool) : ℝ) *
    Fintype.card (ιB → Bool)) ^ (2 : ℕ) := ⟨_, rfl⟩
  have hleft : ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
      (∑ j, ‖finiteComplexInner (e j)
        (prodPhaseSeed (eighthPhase (prodPolyEval m c)))‖ ^ (4 : ℕ))
      = D⁻¹ * ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
        prodQuarticSum e (eighthPhase (prodPolyEval m c)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hDdef]
    exact sum_inner_prodPhaseSeed_fourth_eq e _
  have hright : (∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)),
        ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      = D⁻¹ * ∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)), prodQuarticSum e θ := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_torusBox fun θ _ => ?_
    rw [hDdef]
    exact sum_inner_prodPhaseSeed_fourth_eq e θ
  rw [hleft, hright, ← mul_assoc, mul_comm _ D⁻¹, mul_assoc,
    average_prodQuarticSum_polyEval_eq_integral m hm e]


/-- **Theorem B for the finite product cubic ensemble.**  Against any orthonormal basis of the
bipartite space there is one exactly preparable product cubic-phase seed whose spectral collision is
at most `4/D`. -/
theorem exists_prodPolyEval_collision_le_four_div (m : ℕ) (hm : 8 ≤ 2 ^ (m + 1) - 1)
    (e : ι → ((ιA → Bool) × (ιB → Bool)) → ℂ) (he : ∀ j, (∑ p, ‖e j p‖ ^ (2 : ℕ)) = 1)
    (hcard : Fintype.card ι =
      Fintype.card (ιA → Bool) * Fintype.card (ιB → Bool)) :
    ∃ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
      (∑ j, ‖finiteComplexInner (e j)
        (prodPhaseSeed (eighthPhase (prodPolyEval m c)))‖ ^ (4 : ℕ))
        ≤ 4 / ((Fintype.card (ιA → Bool) : ℝ) * Fintype.card (ιB → Bool)) := by
  classical
  have hApos : (0 : ℝ) < (Fintype.card (ιA → Bool) : ℝ) := by
    have : 0 < Fintype.card (ιA → Bool) := Fintype.card_pos
    exact_mod_cast this
  have hBpos : (0 : ℝ) < (Fintype.card (ιB → Bool) : ℝ) := by
    have : 0 < Fintype.card (ιB → Bool) := Fintype.card_pos
    exact_mod_cast this
  have hNpos : (0 : ℝ) <
      (Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) : ℝ) := by
    have : 0 < Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) := Fintype.card_pos
    exact_mod_cast this
  have hbound : (∫ θ in torusBox ((ιA → Bool) ⊕ (ιB → Bool)),
      ∑ j, ‖finiteComplexInner (e j) (prodPhaseSeed θ)‖ ^ (4 : ℕ))
      ≤ 4 / ((Fintype.card (ιA → Bool) : ℝ) * Fintype.card (ιB → Bool)) := by
    refine le_trans (integral_box_sum_inner_prodPhaseSeed_fourth_le e he) (le_of_eq ?_)
    rw [hcard]
    push_cast
    field_simp
  have havg := average_prodCollision_polyEval_eq_integral m hm e
  have hsum : ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
      (∑ j, ‖finiteComplexInner (e j)
        (prodPhaseSeed (eighthPhase (prodPolyEval m c)))‖ ^ (4 : ℕ))
      ≤ ∑ _c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
        4 / ((Fintype.card (ιA → Bool) : ℝ) * Fintype.card (ιB → Bool)) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hle : ((Fintype.card ((MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8)) : ℝ))⁻¹ *
        ∑ c : (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8),
          (∑ j, ‖finiteComplexInner (e j)
            (prodPhaseSeed (eighthPhase (prodPolyEval m c)))‖ ^ (4 : ℕ))
        ≤ 4 / ((Fintype.card (ιA → Bool) : ℝ) * Fintype.card (ιB → Bool)) := by
      rw [havg]
      exact hbound
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hNpos)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul] at hmul
    exact hmul
  obtain ⟨c, -, hc⟩ := Finset.exists_le_of_sum_le
    (Finset.univ_nonempty (α := (MonLe ιA m → ZMod 8) × (MonLe ιB m → ZMod 8))) hsum
  exact ⟨c, hc⟩

end Transfer

end GaloisForLFunctions.HTGeometry

end
