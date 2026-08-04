import GaloisForLFunctions.HTGeometry.PaddedMonomialSlotOrder
import GaloisForLFunctions.HTGeometry.BlockGradedOstrowski
import GaloisForLFunctions.HTGeometry.PaletteRelationBounds

/-!
# No polynomial relation among the jets of a palette of exponential carriers

A palette is a finite family of exponential carriers built from one rationally independent frequency
sequence by splitting the amplitudes into blocks.  Each block has infinitely many nonzero amplitudes,
so no block is degenerate, and different blocks use different frequencies.

A polynomial relation among all the jets of all the carriers, valid along the real line, must be the
zero polynomial.  The proof is the several-carrier form of the one-carrier argument: bound the orders
and the multi-degrees occurring in the relation, group the monomials by multi-degree, lay each
monomial out as a slot tuple padded to its multi-degree, and apply the graded frequency-separation
theorem.  The layout is faithful in each multi-degree, so every monomial is alone in its cell and its
coefficient is the coefficient the theorem kills.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι] {n : ℕ} {a : ι → ℂ} {omega : ι → ℝ} {bidx : ι → Fin n}

/-- The amplitudes of one block of a palette: the amplitudes carried by that block's own indices. -/
def blockAmp (a : ι → ℂ) (bidx : ι → Fin n) (k : Fin n) : ι → ℂ :=
  fun y => if bidx y = k then a y else 0

/-- The exponential carrier of one block of a palette. -/
def blockCarrier (a : ι → ℂ) (bidx : ι → Fin n) (omega : ι → ℝ) (k : Fin n) : ℂ → ℂ :=
  cexpSeriesCarrier (blockAmp a bidx k) omega

/-- **A polynomial relation among the jets of a palette is trivial.**  The monomials are grouped by
multi-degree and laid out as slot tuples padded to that multi-degree; the layout is faithful, so the
graded frequency-separation theorem kills every coefficient. -/
theorem eq_zero_of_paletteJetRelation_vanishing
    (hom : RationallyIndependentSequence omega)
    (hb : ∀ k : Fin n, ExpSeriesNormallySummable (blockAmp a bidx k) omega)
    (hinf : ∀ k : Fin n, {y : ι | bidx y = k ∧ a y ≠ 0}.Infinite)
    (Q : MvPolynomial (Fin n × ℕ) ℂ)
    (hQ : ∀ t : ℝ, MvPolynomial.eval
      (fun q : Fin n × ℕ => iteratedDeriv q.2 (blockCarrier a bidx omega q.1) (t : ℂ)) Q = 0) :
    Q = 0 := by
  classical
  obtain ⟨N, hord, hdeg⟩ : ∃ N : ℕ, (∀ m ∈ Q.support, ∀ (k : Fin n) (j : ℕ), N < j → m (k, j) = 0)
      ∧ ∀ m ∈ Q.support, ∀ k : Fin n, (∑ j : Fin (N + 1), m (k, (j : ℕ))) ≤ N := by
    obtain ⟨N₀, hN₀⟩ := exists_order_bound Q
    refine ⟨max N₀ Q.totalDegree,
      fun m hm k j hj => hN₀ m hm k j (lt_of_le_of_lt (le_max_left _ _) hj), ?_⟩
    intro m hm k
    rw [Fin.sum_univ_eq_sum_range (fun j => m (k, j)) (max N₀ Q.totalDegree + 1)]
    exact le_trans (sum_le_totalDegree Q hm k _) (le_max_right _ _)
  set e : ((Fin n × ℕ) →₀ ℕ) → Fin n → Fin (N + 1) → ℕ := fun m k j => m (k, (j : ℕ)) with hedef
  set L : ((Fin n × ℕ) →₀ ℕ) → Fin n → Fin (N + 1) :=
    fun m k => ⟨min (∑ j, e m k j) N, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hLdef
  have hLval : ∀ m ∈ Q.support, ∀ k, ((L m k : ℕ)) = ∑ j, e m k j := by
    intro m hm k
    show min (∑ j, e m k j) N = _
    exact min_eq_left (hdeg m hm k)
  -- the monomial is the product over the box of orders
  have hbox : ∀ m ∈ Q.support, ∀ g : Fin n → ℕ → ℂ,
      (∏ k, ∏ j : Fin (N + 1), g k (j : ℕ) ^ e m k j)
        = ∏ q ∈ m.support, g q.1 q.2 ^ m q := by
    intro m hm g
    have h1 : (∏ k, ∏ j : Fin (N + 1), g k (j : ℕ) ^ e m k j)
        = ∏ q ∈ (Finset.univ : Finset (Fin n)) ×ˢ Finset.range (N + 1), g q.1 q.2 ^ m q := by
      rw [Finset.prod_product]
      refine Finset.prod_congr rfl fun k _ => ?_
      exact Fin.prod_univ_eq_prod_range (fun j => g k j ^ m (k, j)) (N + 1)
    rw [h1]
    refine (Finset.prod_subset ?_ ?_).symm
    · intro q hq
      refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_range.2 ?_⟩
      by_contra hlt
      exact (Finsupp.mem_support_iff.1 hq) (hord m hm q.1 q.2 (by omega))
    · intro q _ hq
      rw [Finsupp.notMem_support_iff.1 hq, pow_zero]
  set fib : (Fin n → Fin (N + 1)) → Finset ((Fin n × ℕ) →₀ ℕ) :=
    fun d => Q.support.filter fun m => L m = d with hfibdef
  set K : (d : Fin n → Fin (N + 1)) → Finset (Fin (gradeSlots d) → ℕ) :=
    fun d => (fib d).image fun m => padSlotOrder (e m) fun k => ((d k : ℕ)) with hKdef
  set c : (d : Fin n → Fin (N + 1)) → (Fin (gradeSlots d) → ℕ) → ℂ :=
    fun d s => ∑ m ∈ (fib d).filter fun m => (padSlotOrder (e m) fun k => ((d k : ℕ))) = s,
      Q.coeff m with hcdef
  -- the padded layout of a monomial of the right multi-degree lies in that grade's family
  have hmaps : ∀ (d : Fin n → Fin (N + 1)), ∀ m ∈ fib d,
      (padSlotOrder (e m) fun k => ((d k : ℕ))) ∈ K d := fun d m hm =>
    Finset.mem_image_of_mem _ hm
  -- the length of a monomial's layout is its own multi-degree
  have hlen : ∀ (d : Fin n → Fin (N + 1)), ∀ m ∈ fib d, ∀ k, (∑ j, e m k j) = ((d k : ℕ)) := by
    intro d m hm k
    rw [hfibdef, Finset.mem_filter] at hm
    rw [← hLval m hm.1 k, hm.2]
  have hkey : ∀ d : Fin n → Fin (N + 1), ∀ s ∈ K d, c d s = 0 := by
    refine eq_zero_of_gradedBlockMonomialCombination_vanishing hom
      (fun d j => hb (gradeBlk d j)) hinf K ?_ c ?_
    · -- the layout is faithful in each multi-degree
      intro d s hs s' hs' hcount
      rw [hKdef] at hs hs'
      simp only [Finset.mem_image] at hs hs'
      obtain ⟨m, hm, rfl⟩ := hs
      obtain ⟨m', hm', rfl⟩ := hs'
      exact congrArg (fun ee => padSlotOrder ee fun k => ((d k : ℕ)))
        (padSlotOrder_injOn (hlen d m hm) (hlen d m' hm') hcount)
    · -- the grades repackage the whole relation
      intro t
      refine Eq.trans ?_ (hQ t)
      have hstep : ∀ d : Fin n → Fin (N + 1),
          (∑ s ∈ K d, c d s *
              ∏ j, iteratedDeriv (s j) (cexpSeriesCarrier (gradeAmp a bidx d j) omega) (t : ℂ))
            = ∑ m ∈ fib d, Q.coeff m * ∏ q ∈ m.support,
                iteratedDeriv q.2 (blockCarrier a bidx omega q.1) (t : ℂ) ^ m q := by
        intro d
        rw [← Finset.sum_fiberwise_of_maps_to (hmaps d)
          (fun m => Q.coeff m * ∏ q ∈ m.support,
            iteratedDeriv q.2 (blockCarrier a bidx omega q.1) (t : ℂ) ^ m q)]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hcdef]
        simp only
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [Finset.mem_filter] at hm
        have hmQ : m ∈ Q.support := by
          have := hm.1
          rw [hfibdef, Finset.mem_filter] at this
          exact this.1
        have hprod : (∏ j, iteratedDeriv ((padSlotOrder (e m) fun k => ((d k : ℕ))) j)
              (cexpSeriesCarrier (gradeAmp a bidx d j) omega) (t : ℂ))
            = ∏ q ∈ m.support,
                iteratedDeriv q.2 (blockCarrier a bidx omega q.1) (t : ℂ) ^ m q := by
          rw [← hbox m hmQ fun (k : Fin n) (r : ℕ) =>
            iteratedDeriv r (blockCarrier a bidx omega k) (t : ℂ)]
          exact prod_padSlotOrder (e m) (fun k => ((d k : ℕ))) (hlen d m hm.1)
            (fun (k : Fin n) (r : ℕ) => iteratedDeriv r (blockCarrier a bidx omega k) (t : ℂ))
        rw [← hm.2]
        exact congrArg (fun z : ℂ => Q.coeff m * z) hprod
      rw [Finset.sum_congr rfl fun d _ => hstep d, eval_eq]
      exact Finset.sum_fiberwise Q.support L _
  -- each monomial is alone in its cell
  refine MvPolynomial.ext Q 0 fun m => ?_
  rw [MvPolynomial.coeff_zero]
  by_cases hm : m ∈ Q.support
  · have hmfib : m ∈ fib (L m) := by
      rw [hfibdef, Finset.mem_filter]
      exact ⟨hm, rfl⟩
    have hc0 := hkey (L m) _ (hmaps (L m) m hmfib)
    have hsingle : ((fib (L m)).filter fun m' =>
        (padSlotOrder (e m') fun k => (((L m) k : ℕ)))
          = padSlotOrder (e m) fun k => (((L m) k : ℕ))) = {m} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hmfib, rfl⟩, ?_⟩
      intro m' hm'
      rw [Finset.mem_filter] at hm'
      obtain ⟨hm'fib, hpadeq⟩ := hm'
      have hm'Q : m' ∈ Q.support := by
        have := hm'fib
        rw [hfibdef, Finset.mem_filter] at this
        exact this.1
      have hee : e m' = e m :=
        padSlotOrder_injOn (hlen (L m) m' hm'fib) (hlen (L m) m hmfib)
          fun k => by rw [hpadeq]
      refine Finsupp.ext fun q => ?_
      by_cases hq : q.2 ≤ N
      · have h1 : e m' q.1 ⟨q.2, Nat.lt_succ_of_le hq⟩ = e m q.1 ⟨q.2, Nat.lt_succ_of_le hq⟩ := by
          rw [hee]
        have h2 : m' (q.1, q.2) = m (q.1, q.2) := h1
        rw [← Prod.mk.eta (p := q)] at *
        exact h2
      · rw [hord m' hm'Q q.1 q.2 (by omega), hord m hm q.1 q.2 (by omega)]
    rw [hcdef] at hc0
    simp only at hc0
    rw [hsingle, Finset.sum_singleton] at hc0
    exact hc0
  · exact MvPolynomial.notMem_support_iff.1 hm

end

end GaloisForLFunctions.HTGeometry
