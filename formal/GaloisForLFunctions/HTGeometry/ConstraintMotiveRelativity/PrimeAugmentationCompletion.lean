import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationSymplectic

/-!
# Completion phases of the prime port

The finitely supported prime coordinates embed in every `lp` chart.  Whether the constraint cut out
by a unimodular covector `c` survives the completion is decided by one quantity: whether the chart
contains vectors of port value one and arbitrarily small norm.

In `ℓ¹` it does not — the port extends to a continuous functional of norm at most one, the closure
of the constraint is its kernel, closed of codimension one, and the annihilator of that kernel is
the line of the extended port.  In `ℓ^p` for `1 < p < ∞`, and in the closure of the finitely
supported vectors inside `ℓ^∞` (that is, `c₀`), the spread vector
`N^{-1}(c_{q_1}^{-1} e_{q_1} + … + c_{q_N}^{-1} e_{q_N})` has port value one and norm `N^{1/p-1}`
respectively `N^{-1}`, so the constraint is dense, its continuous annihilator is zero, and Hausdorff
reduction of the port vanishes.

The augmentation `ε x = ∑ x_p` is the case `c ≡ 1`; every statement is recorded in that form as
well.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section Completion

variable {P : Type*} [DecidableEq P]

/-- The chart embedding of the finitely supported prime coordinates. -/
noncomputable def lpEmb (P : Type*) [DecidableEq P] (p : ENNReal) [Fact (1 ≤ p)] :
    (P →₀ ℂ) →ₗ[ℂ] lp (fun _ : P => ℂ) p :=
  Finsupp.linearCombination ℂ fun q => lp.single p q 1

variable {p : ENNReal} [Fact (1 ≤ p)]

theorem lpEmb_single (q : P) (a : ℂ) : lpEmb P p (Finsupp.single q a) = lp.single p q a := by
  rw [lpEmb, Finsupp.linearCombination_single, ← lp.single_smul]
  simp

theorem lpEmb_eq_sum (l : P →₀ ℂ) : lpEmb P p l = ∑ q ∈ l.support, lp.single p q (l q) := by
  rw [lpEmb, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun q _ => by rw [← lp.single_smul]; simp

theorem lpEmb_apply_coord (l : P →₀ ℂ) (i : P) : (lpEmb P p l : P → ℂ) i = l i := by
  classical
  rw [lpEmb_eq_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  rw [Finset.sum_pi_single]
  by_cases hi : i ∈ l.support
  · rw [if_pos hi]
  · rw [if_neg hi]
    exact (Finsupp.notMem_support_iff.1 hi).symm

/-! ### The generic erasure criterion -/

omit [DecidableEq P] in
/-- **If the chart contains vectors of port value one and arbitrarily small norm, the constraint is
dense in the chart image.** -/
theorem mem_closure_image_wtIdeal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : P → ℂ) (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, wtPort c u = 1 ∧ ‖emb u‖ < ε) (l : P →₀ ℂ) :
    emb l ∈ closure (emb '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hu1, hu2⟩ := hsmall (ε / (‖wtPort c l‖ + 1)) (by positivity)
  refine ⟨emb (l - wtPort c l • u), ⟨l - wtPort c l • u, ?_, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, mem_wtIdeal_iff, map_sub, map_smul, hu1, smul_eq_mul, mul_one, sub_self]
  · rw [dist_eq_norm, map_sub, map_smul, sub_sub_cancel, norm_smul]
    have h1 : ‖wtPort c l‖ * ‖emb u‖ ≤ ‖wtPort c l‖ * (ε / (‖wtPort c l‖ + 1)) := by
      by_cases h0 : ‖wtPort c l‖ = 0
      · rw [h0]; simp
      · exact mul_le_mul_of_nonneg_left hu2.le (norm_nonneg _)
    have h2 : ‖wtPort c l‖ * (ε / (‖wtPort c l‖ + 1)) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (wtPort c l), hε]
    calc ‖(wtPort c l : ℂ)‖ * ‖emb u‖ ≤ ‖wtPort c l‖ * (ε / (‖wtPort c l‖ + 1)) := h1
      _ < ε := h2

omit [DecidableEq P] in
/-- The augmentation form of the criterion. -/
theorem mem_closure_image_augIdeal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε) (l : P →₀ ℂ) :
    emb l ∈ closure (emb '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) :=
  mem_closure_image_wtIdeal _ emb hsmall l

/-- The spread vector `N⁻¹(c_{q₁}⁻¹ e_{q₁} + ⋯ + c_{q_N}⁻¹ e_{q_N})`. -/
noncomputable def spreadVec (c : P → ℂ) (G : Finset P) : P →₀ ℂ :=
  ∑ q ∈ G, Finsupp.single q ((G.card : ℂ)⁻¹ * (c q)⁻¹)

omit [DecidableEq P] in
theorem wtPort_spreadVec {c : P → ℂ} (hc : ∀ q, c q ≠ 0) {G : Finset P} (hG : G.Nonempty) :
    wtPort c (spreadVec c G) = 1 := by
  have hcard : (G.card : ℂ) ≠ 0 := by
    have h : 0 < G.card := Finset.card_pos.2 hG
    exact_mod_cast h.ne'
  rw [spreadVec, map_sum]
  have hterm : ∀ q ∈ G, wtPort c (Finsupp.single q ((G.card : ℂ)⁻¹ * (c q)⁻¹))
      = (G.card : ℂ)⁻¹ := by
    intro q _
    rw [wtPort_single, mul_assoc, inv_mul_cancel₀ (hc q), mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem lpEmb_spreadVec (c : P → ℂ) (G : Finset P) :
    lpEmb P p (spreadVec c G) = ∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹ * (c q)⁻¹) := by
  rw [spreadVec, map_sum]
  exact Finset.sum_congr rfl fun q _ => lpEmb_single q _

/-! ### The erasure phases -/

/-- The spread vectors of an `ℓ^p` chart with `p > 1` have arbitrarily small norm. -/
theorem exists_small_spread_lp [Infinite P] {c : P → ℂ} (hc : ∀ q, c q ≠ 0)
    (hc1 : ∀ q, ‖c q‖ = 1) (hp : 1 < p.toReal) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : P →₀ ℂ, wtPort c u = 1 ∧ ‖lpEmb P p u‖ < ε := by
  set r : ℝ := p.toReal with hr
  have hr0 : 0 < r := by linarith
  have htend : Filter.Tendsto (fun N : ℕ => ((N : ℝ)) ^ (1 - r)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => x ^ (-(r - 1))) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith)
    have h2 := h1.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h2.congr fun N => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have hpos : (0 : ℝ) < ε ^ r := Real.rpow_pos_of_pos hε r
  obtain ⟨N, hN⟩ := ((htend.eventually (eventually_lt_nhds hpos)).and
    (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨G, hGcard⟩ := Infinite.exists_subset_card_eq P N
  have hGne : G.Nonempty := Finset.card_pos.1 (by rw [hGcard]; omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hcardR : ((G.card : ℝ)) = (N : ℝ) := by exact_mod_cast hGcard
  refine ⟨spreadVec c G, wtPort_spreadVec hc hGne, ?_⟩
  rw [lpEmb_spreadVec]
  have hnormterm : ∀ q : P, ‖((G.card : ℂ)⁻¹ * (c q)⁻¹)‖ = ((N : ℝ))⁻¹ := by
    intro q
    rw [norm_mul, norm_inv, norm_inv, Complex.norm_natCast, hc1 q, inv_one, mul_one, hcardR]
  have hns : ‖∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹ * (c q)⁻¹)‖ ^ r = (N : ℝ) ^ (1 - r) := by
    have hbase := lp.norm_sum_single (E := fun _ : P => ℂ) (p := p) hr0
      (fun q => ((G.card : ℂ)⁻¹ * (c q)⁻¹)) G
    rw [hbase, Finset.sum_congr rfl (fun q _ => by rw [hnormterm q]), Finset.sum_const, hGcard,
      nsmul_eq_mul, Real.inv_rpow hNpos.le, Real.rpow_sub hNpos, Real.rpow_one, div_eq_mul_inv]
  have hlt : ‖∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹ * (c q)⁻¹)‖ ^ r < ε ^ r := by
    rw [hns]; exact hN.1
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hr0).1 hlt

/-- The spread vectors of the `ℓ^∞` chart have arbitrarily small norm. -/
theorem exists_small_spread_top [Infinite P] {c : P → ℂ} (hc : ∀ q, c q ≠ 0)
    (hc1 : ∀ q, ‖c q‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : P →₀ ℂ, wtPort c u = 1 ∧ ‖lpEmb P ⊤ u‖ < ε := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hz | hpos
    · exfalso
      have hp1 : (0 : ℝ) < 1 / ε := by positivity
      rw [hz, Nat.cast_zero] at hN
      linarith
    · exact hpos
  obtain ⟨G, hGcard⟩ := Infinite.exists_subset_card_eq P N
  have hGne : G.Nonempty := Finset.card_pos.1 (by rw [hGcard]; omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hcardR : ((G.card : ℝ)) = (N : ℝ) := by exact_mod_cast hGcard
  refine ⟨spreadVec c G, wtPort_spreadVec hc hGne, ?_⟩
  rw [lpEmb_spreadVec]
  have hcoord : ∀ i : P,
      ‖((∑ q ∈ G, lp.single (⊤ : ENNReal) q ((G.card : ℂ)⁻¹ * (c q)⁻¹) :
          lp (fun _ : P => ℂ) ⊤) : P → ℂ) i‖ ≤ ((N : ℝ))⁻¹ := by
    intro i
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
    rw [Finset.sum_pi_single]
    by_cases hi : i ∈ G
    · rw [if_pos hi, norm_mul, norm_inv, norm_inv, Complex.norm_natCast, hc1 i, inv_one, mul_one,
        hcardR]
    · rw [if_neg hi]
      simp only [norm_zero]
      positivity
  have hle := lp.norm_le_of_forall_le (E := fun _ : P => ℂ) (by positivity) hcoord
  have hlt : ((N : ℝ))⁻¹ < ε := by
    rw [inv_lt_comm₀ hNpos hε]
    rw [one_div] at hN
    exact hN
  linarith

/-- **In `ℓ^p` with `p > 1` the constraint is dense in the chart image.** -/
theorem closure_image_wtIdeal_lp [Infinite P] {c : P → ℂ} (hc : ∀ q, c q ≠ 0)
    (hc1 : ∀ q, ‖c q‖ = 1) (hp : 1 < p.toReal) :
    closure ((lpEmb P p) '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P p)) := by
  apply le_antisymm
  · exact closure_mono (Set.image_subset_range _ _)
  · rw [← closure_closure (s := (lpEmb P p) '' _)]
    refine closure_mono ?_
    rintro x ⟨l, rfl⟩
    exact mem_closure_image_wtIdeal _ _ (fun ε hε => exists_small_spread_lp hc hc1 hp ε hε) l

/-- **Inside `ℓ^∞` the constraint is dense in the closure of the finitely supported vectors, which
is `c₀`.** -/
theorem closure_image_wtIdeal_top [Infinite P] {c : P → ℂ} (hc : ∀ q, c q ≠ 0)
    (hc1 : ∀ q, ‖c q‖ = 1) :
    closure ((lpEmb P ⊤) '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P ⊤)) := by
  apply le_antisymm
  · exact closure_mono (Set.image_subset_range _ _)
  · rw [← closure_closure (s := (lpEmb P ⊤) '' _)]
    refine closure_mono ?_
    rintro x ⟨l, rfl⟩
    exact mem_closure_image_wtIdeal _ _ (fun ε hε => exists_small_spread_top hc hc1 ε hε) l

/-- **Theorem 3, `(RC.8)`.**  The augmentation form of the `ℓ^p` erasure. -/
theorem closure_image_augIdeal_lp [Infinite P] (hp : 1 < p.toReal) :
    closure ((lpEmb P p) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P p)) :=
  closure_image_wtIdeal_lp one_ne_zero_family (fun _ => norm_one) hp

/-- **Theorem 3, `(RC.8)` for `c₀`.** -/
theorem closure_image_augIdeal_top [Infinite P] :
    closure ((lpEmb P ⊤) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P ⊤)) :=
  closure_image_wtIdeal_top one_ne_zero_family (fun _ => norm_one)

omit [DecidableEq P] in
/-- **`(RC.8)`, the annihilator.**  A continuous functional vanishing on the constraint vanishes on
the whole chart image. -/
theorem eq_zero_on_range_of_vanishing_on_wtIdeal {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (c : P → ℂ) (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, wtPort c u = 1 ∧ ‖emb u‖ < ε)
    (g : X →L[ℂ] ℂ) (hg : ∀ l ∈ (wtIdeal c : Submodule ℂ (P →₀ ℂ)), g (emb l) = 0) (l : P →₀ ℂ) :
    g (emb l) = 0 := by
  have hmem := mem_closure_image_wtIdeal c emb hsmall l
  have hcl : closure ((emb) '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      ⊆ g ⁻¹' {0} := by
    refine closure_minimal ?_ (IsClosed.preimage g.continuous isClosed_singleton)
    rintro z ⟨m, hm, rfl⟩
    exact hg m hm
  exact hcl hmem

omit [DecidableEq P] in
/-- The augmentation form of the annihilator statement. -/
theorem eq_zero_on_range_of_vanishing_on_augIdeal {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε)
    (g : X →L[ℂ] ℂ) (hg : ∀ l ∈ (augIdeal : Submodule ℂ (P →₀ ℂ)), g (emb l) = 0) (l : P →₀ ℂ) :
    g (emb l) = 0 :=
  eq_zero_on_range_of_vanishing_on_wtIdeal _ emb hsmall g hg l

end Completion

/-! ### The `ℓ¹` phase -/

section L1

variable {P : Type*} [DecidableEq P]

omit [DecidableEq P] in
theorem summable_norm_lp_one (x : lp (fun _ : P => ℂ) 1) :
    Summable fun q => ‖(x : P → ℂ) q‖ := by
  have h := lp.memℓp x
  rw [memℓp_gen_iff (p := 1) (by norm_num)] at h
  simpa using h

omit [DecidableEq P] in
theorem summable_lp_one (x : lp (fun _ : P => ℂ) 1) : Summable fun q => (x : P → ℂ) q :=
  Summable.of_norm (summable_norm_lp_one x)

omit [DecidableEq P] in
theorem norm_eq_tsum_one (x : lp (fun _ : P => ℂ) 1) : ‖x‖ = ∑' q, ‖(x : P → ℂ) q‖ := by
  rw [lp.norm_eq_tsum_rpow (p := 1) (by norm_num)]
  simp

variable {c : P → ℂ}

omit [DecidableEq P] in
theorem summable_wt_lp_one (hc1 : ∀ q, ‖c q‖ = 1) (x : lp (fun _ : P => ℂ) 1) :
    Summable fun q => c q * (x : P → ℂ) q := by
  refine Summable.of_norm ((summable_norm_lp_one x).congr fun q => ?_)
  rw [norm_mul, hc1 q, one_mul]

/-- The port as a linear functional on `ℓ¹`. -/
noncomputable def wtLin (c : P → ℂ) (hc1 : ∀ q, ‖c q‖ = 1) : lp (fun _ : P => ℂ) 1 →ₗ[ℂ] ℂ where
  toFun := fun x => ∑' q, c q * (x : P → ℂ) q
  map_add' := fun x y => by
    have hrw : ∀ q, c q * ((x + y : lp (fun _ : P => ℂ) 1) : P → ℂ) q
        = c q * (x : P → ℂ) q + c q * (y : P → ℂ) q := by
      intro q
      rw [lp.coeFn_add]
      simp only [Pi.add_apply]
      ring
    rw [tsum_congr hrw]
    exact (summable_wt_lp_one hc1 x).tsum_add (summable_wt_lp_one hc1 y)
  map_smul' := fun a x => by
    have hrw : ∀ q, c q * ((a • x : lp (fun _ : P => ℂ) 1) : P → ℂ) q
        = a * (c q * (x : P → ℂ) q) := by
      intro q
      rw [lp.coeFn_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [tsum_congr hrw]
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [tsum_mul_left]

/-- **Theorem 2.**  The port extends to a continuous functional of norm at most one on `ℓ¹`. -/
noncomputable def wtCLM (c : P → ℂ) (hc1 : ∀ q, ‖c q‖ = 1) : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous (wtLin c hc1) 1 fun x => by
    rw [one_mul, norm_eq_tsum_one]
    have hb : ‖∑' q, c q * (x : P → ℂ) q‖ ≤ ∑' q, ‖c q * (x : P → ℂ) q‖ :=
      norm_tsum_le_tsum_norm ((summable_norm_lp_one x).congr fun q => by
        rw [norm_mul, hc1 q, one_mul])
    refine le_trans hb (le_of_eq (tsum_congr fun q => ?_))
    rw [norm_mul, hc1 q, one_mul]

omit [DecidableEq P] in
@[simp] theorem wtCLM_apply (hc1 : ∀ q, ‖c q‖ = 1) (x : lp (fun _ : P => ℂ) 1) :
    wtCLM c hc1 x = ∑' q, c q * (x : P → ℂ) q := rfl

theorem wtCLM_lpEmb (hc1 : ∀ q, ‖c q‖ = 1) (l : P →₀ ℂ) :
    wtCLM c hc1 (lpEmb P 1 l) = wtPort c l := by
  classical
  rw [wtCLM_apply, wtPort_apply]
  have hz : ∀ q ∉ l.support, c q * ((lpEmb P 1 l : lp (fun _ : P => ℂ) 1) : P → ℂ) q = 0 := by
    intro q hq
    rw [lpEmb_apply_coord, Finsupp.notMem_support_iff.1 hq, mul_zero]
  rw [tsum_eq_sum hz]
  exact Finset.sum_congr rfl fun q _ => by rw [lpEmb_apply_coord, mul_comm]

theorem coeFn_trunc_one (x : lp (fun _ : P => ℂ) 1) (F : Finset P) (i : P) :
    ((∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q) : lp (fun _ : P => ℂ) 1) : P → ℂ) i
      = if i ∈ F then (x : P → ℂ) i else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  exact Finset.sum_pi_single i (fun q => (x : P → ℂ) q) F

theorem norm_sub_trunc_one (x : lp (fun _ : P => ℂ) 1) (F : Finset P) :
    ‖x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)‖
      = ∑' (q : {y : P // y ∉ F}), ‖(x : P → ℂ) q‖ := by
  classical
  rw [norm_eq_tsum_one]
  have hcoord : ∀ i : P,
      ‖((x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q) : lp (fun _ : P => ℂ) 1)
        : P → ℂ) i‖ = Set.indicator {y : P | y ∉ F} (fun q => ‖(x : P → ℂ) q‖) i := by
    intro i
    rw [lp.coeFn_sub]
    simp only [Pi.sub_apply, coeFn_trunc_one]
    by_cases hi : i ∈ F
    · rw [if_pos hi, sub_self, Set.indicator_of_notMem (by simpa using hi), norm_zero]
    · rw [if_neg hi, sub_zero, Set.indicator_of_mem (by simpa using hi)]
  rw [tsum_congr hcoord, ← tsum_subtype {y : P | y ∉ F} fun q => ‖(x : P → ℂ) q‖]
  rfl

/-- **Theorem 2, `(RC.7)`.**  In `ℓ¹` the closure of the constraint is the kernel of the extended
port. -/
theorem closure_image_wtIdeal_one [Nonempty P] (hc : ∀ q, c q ≠ 0) (hc1 : ∀ q, ‖c q‖ = 1) :
    closure ((lpEmb P 1) '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = {x : lp (fun _ : P => ℂ) 1 | wtCLM c hc1 x = 0} := by
  classical
  obtain ⟨q₀⟩ := ‹Nonempty P›
  apply le_antisymm
  · refine closure_minimal ?_ (IsClosed.preimage (wtCLM c hc1).continuous isClosed_singleton)
    rintro z ⟨m, hm, rfl⟩
    rw [Set.mem_setOf_eq, wtCLM_lpEmb]
    exact hm
  · intro x hx
    have hx0 : wtCLM c hc1 x = 0 := hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have htail : Filter.Tendsto
        (fun F : Finset P => ∑' (q : {y : P // y ∉ F}), ‖(x : P → ℂ) q‖) Filter.atTop (nhds 0) :=
      tendsto_tsum_compl_atTop_zero (fun q : P => ‖(x : P → ℂ) q‖)
    have hpart : Filter.Tendsto (fun F : Finset P => ∑ q ∈ F, c q * (x : P → ℂ) q) Filter.atTop
        (nhds 0) := by
      have h := (summable_wt_lp_one hc1 x).hasSum
      rw [← wtCLM_apply hc1 x, hx0] at h
      exact h
    have hev1 := (tendsto_order.1 htail).2 (ε / 2) (by linarith)
    have hev2 := hpart.eventually (Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0:ℝ) < ε / 2))
    obtain ⟨F, hF1, hF2⟩ := (hev1.and hev2).exists
    set lF : P →₀ ℂ := ∑ q ∈ F, Finsupp.single q ((x : P → ℂ) q) with hlF
    have hport : wtPort c lF = ∑ q ∈ F, c q * (x : P → ℂ) q := by
      rw [hlF, map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [wtPort_single, mul_comm]
    refine ⟨lpEmb P 1 (lF - Finsupp.single q₀ (wtPort c lF * (c q₀)⁻¹)), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_wtIdeal_iff, map_sub, wtPort_single, mul_assoc,
        inv_mul_cancel₀ (hc q₀), mul_one, sub_self]
    · have hemb : lpEmb P 1 lF = ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q) := by
        rw [hlF, map_sum]
        exact Finset.sum_congr rfl fun q _ => lpEmb_single q _
      rw [dist_eq_norm, map_sub, hemb, lpEmb_single]
      have hsplit : x - (∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)
            - (lp.single (1 : ENNReal) q₀ (wtPort c lF * (c q₀)⁻¹) : lp (fun _ : P => ℂ) 1))
          = (x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q))
            + (lp.single (1 : ENNReal) q₀ (wtPort c lF * (c q₀)⁻¹) : lp (fun _ : P => ℂ) 1) := by
        abel
      rw [hsplit]
      have htri := norm_add_le
        (x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q))
        (lp.single (1 : ENNReal) q₀ (wtPort c lF * (c q₀)⁻¹) : lp (fun _ : P => ℂ) 1)
      have hb1 : ‖x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)‖ < ε / 2 := by
        rw [norm_sub_trunc_one]
        exact hF1
      have hb2 : ‖(lp.single (1 : ENNReal) q₀ (wtPort c lF * (c q₀)⁻¹) :
          lp (fun _ : P => ℂ) 1)‖ < ε / 2 := by
        rw [lp.norm_single (by norm_num), norm_mul, norm_inv, hc1 q₀, inv_one, mul_one, hport]
        have hd := hF2
        rw [dist_zero_right] at hd
        exact hd
      linarith

/-- The augmentation as a continuous functional on `ℓ¹`. -/
noncomputable def augCLM : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ :=
  wtCLM (fun _ : P => (1 : ℂ)) (fun _ => norm_one)

theorem augCLM_lpEmb (l : P →₀ ℂ) : augCLM (lpEmb P 1 l) = augment l :=
  wtCLM_lpEmb (fun _ => norm_one) l

/-- **Theorem 2, `(RC.7)`, the augmentation form.** -/
theorem closure_image_augIdeal_one [Nonempty P] :
    closure ((lpEmb P 1) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = {x : lp (fun _ : P => ℂ) 1 | augCLM x = 0} :=
  closure_image_wtIdeal_one one_ne_zero_family (fun _ => norm_one)

theorem wtCLM_surjective [Nonempty P] (hc : ∀ q, c q ≠ 0) (hc1 : ∀ q, ‖c q‖ = 1) :
    Function.Surjective (wtCLM c hc1) := by
  obtain ⟨q₀⟩ := ‹Nonempty P›
  intro z
  refine ⟨lp.single (1 : ENNReal) q₀ (z * (c q₀)⁻¹), ?_⟩
  have h := wtCLM_lpEmb hc1 (Finsupp.single q₀ (z * (c q₀)⁻¹))
  rw [lpEmb_single] at h
  rw [h, wtPort_single, mul_assoc, inv_mul_cancel₀ (hc q₀), mul_one]

theorem augCLM_surjective [Nonempty P] :
    Function.Surjective (augCLM : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ) :=
  wtCLM_surjective one_ne_zero_family (fun _ => norm_one)

/-- The continuous annihilator of the closed constraint is the line of the extended port. -/
theorem eq_smul_wtCLM_of_vanishing [Nonempty P] (hc : ∀ q, c q ≠ 0) (hc1 : ∀ q, ‖c q‖ = 1)
    (q₀ : P) (g : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ)
    (hg : ∀ x : lp (fun _ : P => ℂ) 1, wtCLM c hc1 x = 0 → g x = 0) :
    ∀ x, g x = g (lp.single (1 : ENNReal) q₀ (c q₀)⁻¹) * wtCLM c hc1 x := by
  intro x
  have hv : wtCLM c hc1 (lp.single (1 : ENNReal) q₀ (c q₀)⁻¹) = 1 := by
    have h := wtCLM_lpEmb hc1 (Finsupp.single q₀ ((c q₀)⁻¹))
    rw [lpEmb_single] at h
    rw [h, wtPort_single, inv_mul_cancel₀ (hc q₀)]
  have hker : wtCLM c hc1 (x - wtCLM c hc1 x • lp.single (1 : ENNReal) q₀ (c q₀)⁻¹) = 0 := by
    rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  have hzero := hg _ hker
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul] at hzero
  rw [hzero]
  ring

theorem eq_smul_augCLM_of_vanishing [Nonempty P] (q₀ : P)
    (g : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ)
    (hg : ∀ x : lp (fun _ : P => ℂ) 1, augCLM x = 0 → g x = 0) :
    ∀ x, g x = g (lp.single (1 : ENNReal) q₀ (1 : ℂ)⁻¹) * augCLM x :=
  eq_smul_wtCLM_of_vanishing one_ne_zero_family (fun _ => norm_one) q₀ g hg

/-! ### The algebraic–continuous separation defect -/

/-- **Corollary 4, the `ℓ¹` phase `𝔎 = 0`.**  Completion is injective on the algebraic port, and
every algebraic annihilator of the constraint is the restriction of a continuous one. -/
theorem separation_defect_one [Nonempty P] (hc : ∀ q, c q ≠ 0) (hc1 : ∀ q, ‖c q‖ = 1) :
    (∀ l : P →₀ ℂ,
        lpEmb P 1 l ∈ closure ((lpEmb P 1) ''
          ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → wtPort c l = 0) ∧
    (∀ a : ℂ, ∃ g : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ,
        (∀ x : lp (fun _ : P => ℂ) 1,
          x ∈ closure ((lpEmb P 1) ''
            ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → g x = 0) ∧
        ∀ l : P →₀ ℂ, g (lpEmb P 1 l) = a * wtPort c l) := by
  constructor
  · intro l hl
    rw [closure_image_wtIdeal_one hc hc1] at hl
    rw [← wtCLM_lpEmb hc1 l]
    exact hl
  · intro a
    refine ⟨a • wtCLM c hc1, ?_, ?_⟩
    · intro x hx
      rw [closure_image_wtIdeal_one hc hc1] at hx
      simp only [smul_apply, smul_eq_mul]
      rw [hx, mul_zero]
    · intro l
      simp only [smul_apply, smul_eq_mul]
      rw [wtCLM_lpEmb]

omit [DecidableEq P] in
/-- **Corollary 4, the erasure phases `𝔎 ≅ ℍ(ℂ)`.**  In a chart with arbitrarily small vectors of
port value one, completion kills the whole algebraic port and no algebraic annihilator except zero
extends continuously. -/
theorem separation_defect_erasure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (c : P → ℂ) (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, wtPort c u = 1 ∧ ‖emb u‖ < ε) :
    (∀ l : P →₀ ℂ,
        emb l ∈ closure (emb '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))) ∧
    (∀ g : X →L[ℂ] ℂ,
        (∀ x, x ∈ closure (emb '' ((wtIdeal c : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → g x = 0) →
        ∀ l : P →₀ ℂ, g (emb l) = 0) :=
  ⟨fun l => mem_closure_image_wtIdeal c emb hsmall l,
    fun g hg l => eq_zero_on_range_of_vanishing_on_wtIdeal c emb hsmall g
      (fun m hm => hg _ (subset_closure ⟨m, hm, rfl⟩)) l⟩

end L1

end HTGeometry.ConstraintMotiveRelativity
