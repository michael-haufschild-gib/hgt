import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeIndex

/-!
# Adic completeness of the completed pseudodifferential skew field

The completed skew field `𝔻` is the uniform completion of the rational pseudodifferential operators
for the order valuation.  This leaf turns that topological statement into the algebraic form the
slope theory consumes: a sequence whose consecutive differences have valuation tending to infinity
has a limit, and the limit is approached in valuation.

* `DiffOp.min_le_completedPseudoDiffOpAddValue_add` — the ultrametric inequality in additive form.
* `DiffOp.eventually_completedPseudoDiffOpValuation_eq` — the extended valuation is locally constant
  away from zero, because it factors through a continuous map into a value group whose nonzero
  points are open.
* `DiffOp.isClosed_setOf_le_completedPseudoDiffOpAddValue` — valuation balls are closed.
* `DiffOp.exists_forall_le_addValue_mem_of_mem_nhds_zero` — every neighbourhood of zero contains a
  valuation ball.  A neighbourhood `U'` with `U' + U' ⊆ U` pulls back to a valuation ball of the
  dense rational operators; an arbitrary completed element of high valuation is approximated by a
  rational one of the *same* valuation (local constancy) and lies in `U' + U'`.
* `DiffOp.exists_limit_of_eventually_le_addValue_sub` — **adic completeness**: if the successive
  differences eventually have valuation above every bound, the sequence converges and every bound is
  eventually met by the distance to the limit.
-/

open Filter Topology
open scoped WithZeroTopology

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

theorem completedPseudoDiffOpAddValue_zero :
    completedPseudoDiffOpAddValue (0 : CompletedPseudoDiffOp K) = ⊤ := by
  unfold completedPseudoDiffOpAddValue
  rw [Valuation.map_zero]
  rfl

theorem completedPseudoDiffOpAddValue_neg (x : CompletedPseudoDiffOp K) :
    completedPseudoDiffOpAddValue (-x) = completedPseudoDiffOpAddValue x := by
  unfold completedPseudoDiffOpAddValue
  rw [Valuation.map_neg]

theorem completedPseudoDiffOpAddValue_sub_comm (x y : CompletedPseudoDiffOp K) :
    completedPseudoDiffOpAddValue (x - y) = completedPseudoDiffOpAddValue (y - x) := by
  rw [← neg_sub, completedPseudoDiffOpAddValue_neg]

/-- The ultrametric inequality in additive form. -/
theorem min_le_completedPseudoDiffOpAddValue_add (x y : CompletedPseudoDiffOp K) :
    min (completedPseudoDiffOpAddValue x) (completedPseudoDiffOpAddValue y) ≤
      completedPseudoDiffOpAddValue (x + y) := by
  have h := (completedPseudoDiffOpValuation (K := K)).map_add x y
  rcases le_total (completedPseudoDiffOpValuation x) (completedPseudoDiffOpValuation y) with
    hxy | hxy
  · rw [max_eq_right hxy] at h
    exact min_le_of_right_le h
  · rw [max_eq_left hxy] at h
    exact min_le_of_left_le h

/-- A lower valuation bound survives addition. -/
theorem le_completedPseudoDiffOpAddValue_add {n : WithTop ℤ} {x y : CompletedPseudoDiffOp K}
    (hx : n ≤ completedPseudoDiffOpAddValue x) (hy : n ≤ completedPseudoDiffOpAddValue y) :
    n ≤ completedPseudoDiffOpAddValue (x + y) :=
  (le_min hx hy).trans (min_le_completedPseudoDiffOpAddValue_add x y)

/-- The completed valuation is locally constant away from zero. -/
theorem eventually_completedPseudoDiffOpValuation_eq {x : CompletedPseudoDiffOp K} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, completedPseudoDiffOpValuation y = completedPseudoDiffOpValuation x := by
  have hne : DivisionValuedCompletion.extension (D := WithVal (pseudoDiffOpValuation (K := K)))
      (Γ₀ := PseudoDiffOpValueGroup) x ≠ 0 := by
    intro h0
    have hv : completedPseudoDiffOpValuation x = 0 := by
      change MonoidWithZeroHom.ValueGroup₀.embedding
        (DivisionValuedCompletion.extension (D := WithVal (pseudoDiffOpValuation (K := K)))
          (Γ₀ := PseudoDiffOpValueGroup) x) = 0
      rw [h0, map_zero]
    exact (Valuation.ne_zero_iff _).2 hx hv
  have hnhds := (DivisionValuedCompletion.continuous_extension
    (D := WithVal (pseudoDiffOpValuation (K := K))) (Γ₀ := PseudoDiffOpValueGroup)).continuousAt
    (x := x) |>.preimage_mem_nhds (WithZeroTopology.singleton_mem_nhds_of_ne_zero hne)
  filter_upwards [hnhds] with y hy
  change MonoidWithZeroHom.ValueGroup₀.embedding
      (DivisionValuedCompletion.extension (D := WithVal (pseudoDiffOpValuation (K := K)))
        (Γ₀ := PseudoDiffOpValueGroup) y) =
    MonoidWithZeroHom.ValueGroup₀.embedding
      (DivisionValuedCompletion.extension (D := WithVal (pseudoDiffOpValuation (K := K)))
        (Γ₀ := PseudoDiffOpValueGroup) x)
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
  rw [hy]

/-- The additive valuation is locally constant away from zero. -/
theorem eventually_completedPseudoDiffOpAddValue_eq {x : CompletedPseudoDiffOp K} (hx : x ≠ 0) :
    ∀ᶠ y in 𝓝 x, completedPseudoDiffOpAddValue y = completedPseudoDiffOpAddValue x := by
  filter_upwards [eventually_completedPseudoDiffOpValuation_eq hx] with y hy
  unfold completedPseudoDiffOpAddValue
  rw [hy]

/-- Valuation balls are closed. -/
theorem isClosed_setOf_le_completedPseudoDiffOpAddValue (n : ℤ) :
    IsClosed {x : CompletedPseudoDiffOp K | (n : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hx
    change (n : WithTop ℤ) ≤ completedPseudoDiffOpAddValue 0
    rw [completedPseudoDiffOpAddValue_zero]
    exact le_top
  filter_upwards [eventually_completedPseudoDiffOpAddValue_eq hx0] with y hy
  change ¬ (n : WithTop ℤ) ≤ completedPseudoDiffOpAddValue y
  rw [hy]
  exact hx

/-- A rational operator of large additive valuation has small multiplicative valuation. -/
theorem exists_forall_le_addValue_valued_lt (g : PseudoDiffOpValueGroup) (hg : g ≠ 0) :
    ∃ N : ℤ, ∀ d : WithVal (pseudoDiffOpValuation (K := K)),
      (N : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (d : CompletedPseudoDiffOp K) →
        Valued.v d < g := by
  set m : WithTop ℤ := OrderDual.ofDual (Multiplicative.toAdd g) with hm
  have hmtop : m ≠ ⊤ := by
    intro htop
    apply hg
    have : g = Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ)) := by
      rw [← htop, hm]
      rfl
    rw [this]
    rfl
  refine ⟨m.untop hmtop + 1, fun d hd => ?_⟩
  have hval : completedPseudoDiffOpAddValue (d : CompletedPseudoDiffOp K) =
      OrderDual.ofDual (Multiplicative.toAdd (Valued.v d)) := by
    unfold completedPseudoDiffOpAddValue
    rw [completedPseudoDiffOpValuation_apply_coe]
    rfl
  rw [hval] at hd
  have hlt : m < OrderDual.ofDual (Multiplicative.toAdd (Valued.v d)) := by
    refine lt_of_lt_of_le ?_ hd
    have hcoe : m = ((m.untop hmtop : ℤ) : WithTop ℤ) := (WithTop.coe_untop m hmtop).symm
    calc m = ((m.untop hmtop : ℤ) : WithTop ℤ) := hcoe
      _ < ((m.untop hmtop + 1 : ℤ) : WithTop ℤ) := WithTop.coe_lt_coe.2 (lt_add_one _)
  exact hlt

/-- Every neighbourhood of zero in the completed skew field contains a valuation ball. -/
theorem exists_forall_le_addValue_mem_of_mem_nhds_zero {U : Set (CompletedPseudoDiffOp K)}
    (hU : U ∈ 𝓝 (0 : CompletedPseudoDiffOp K)) :
    ∃ N : ℤ, ∀ x, (N : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x → x ∈ U := by
  obtain ⟨U', hU'o, h0, hU'⟩ := exists_open_nhds_zero_half hU
  have hpre : (fun d : WithVal (pseudoDiffOpValuation (K := K)) =>
      (d : CompletedPseudoDiffOp K)) ⁻¹' U' ∈ 𝓝 (0 : WithVal (pseudoDiffOpValuation (K := K))) := by
    refine (UniformSpace.Completion.continuous_coe _).continuousAt.preimage_mem_nhds ?_
    rw [UniformSpace.Completion.coe_zero]
    exact hU'o.mem_nhds h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hpre
  obtain ⟨N, hN⟩ := exists_forall_le_addValue_valued_lt (K := K)
    (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
    (by rw [ne_eq, map_eq_zero]; exact γ.ne_zero)
  refine ⟨N, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · subst x
    simpa using hU' 0 h0 0 h0
  have hsub : ∀ᶠ y in 𝓝 x, x - y ∈ U' := by
    have hc : Continuous fun y : CompletedPseudoDiffOp K => x - y := by fun_prop
    have := hc.continuousAt (x := x) |>.preimage_mem_nhds
      (hU'o.mem_nhds (by simpa using h0))
    exact this
  obtain ⟨d, hd⟩ := (UniformSpace.Completion.denseRange_coe).mem_nhds
    ((eventually_completedPseudoDiffOpAddValue_eq hx0).and hsub)
  obtain ⟨hdval, hdsub⟩ := hd
  have hdU : (d : CompletedPseudoDiffOp K) ∈ U' := by
    apply hγ
    change Valued.v.restrict d < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding]
    exact hN d (hdval.symm ▸ hx)
  have := hU' _ hdU _ hdsub
  simpa using this

/-- Tails of a valuation-Cauchy sequence are uniformly small. -/
theorem le_completedPseudoDiffOpAddValue_sub_of_forall_succ {c : ℕ → CompletedPseudoDiffOp K}
    {k : WithTop ℤ} {n₀ : ℕ}
    (hc : ∀ n, n₀ ≤ n → k ≤ completedPseudoDiffOpAddValue (c (n + 1) - c n)) :
    ∀ n, n₀ ≤ n → ∀ m, n ≤ m → k ≤ completedPseudoDiffOpAddValue (c m - c n) := by
  intro n hn m hm
  induction m, hm using Nat.le_induction with
  | base =>
      rw [sub_self, completedPseudoDiffOpAddValue_zero]
      exact le_top
  | succ m hnm ih =>
      have hsplit : c (m + 1) - c n = (c (m + 1) - c m) + (c m - c n) := by abel
      rw [hsplit]
      exact le_completedPseudoDiffOpAddValue_add (hc m (hn.trans hnm)) ih

/-- **Adic completeness.**  If the successive differences of a sequence eventually have valuation
above every bound, the sequence has a limit, and the distance to the limit eventually has valuation
above every bound. -/
theorem exists_limit_of_eventually_le_addValue_sub (c : ℕ → CompletedPseudoDiffOp K)
    (hc : ∀ k : ℤ, ∀ᶠ n in atTop,
      (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (c (n + 1) - c n)) :
    ∃ y, ∀ k : ℤ, ∀ᶠ n in atTop, (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (y - c n) := by
  have htail : ∀ k : ℤ, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ m, n ≤ m →
      (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue (c m - c n) := by
    intro k
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hc k)
    exact ⟨n₀, le_completedPseudoDiffOpAddValue_sub_of_forall_succ hn₀⟩
  have hcauchy : CauchySeq c := by
    rw [cauchySeq_iff]
    intro V hV
    rw [uniformity_eq_comap_nhds_zero] at hV
    obtain ⟨U, hU, hUV⟩ := Filter.mem_comap.1 hV
    obtain ⟨N, hN⟩ := exists_forall_le_addValue_mem_of_mem_nhds_zero hU
    obtain ⟨n₀, hn₀⟩ := htail N
    refine ⟨n₀, fun k hk l hl => hUV ?_⟩
    change c l - c k ∈ U
    apply hN
    rcases le_total k l with hkl | hlk
    · exact hn₀ k hk l hkl
    · rw [completedPseudoDiffOpAddValue_sub_comm]
      exact hn₀ l hl k hlk
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨y, fun k => ?_⟩
  obtain ⟨n₀, hn₀⟩ := htail k
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have hclosed : IsClosed ((fun z => z - c n) ⁻¹'
      {x : CompletedPseudoDiffOp K | (k : WithTop ℤ) ≤ completedPseudoDiffOpAddValue x}) :=
    (isClosed_setOf_le_completedPseudoDiffOpAddValue k).preimage (by fun_prop)
  exact hclosed.mem_of_tendsto hy (eventually_atTop.2 ⟨n, fun m hm => hn₀ n hn m hm⟩)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
