import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimeAugmentationSymplectic

/-!
# Completion phases of the prime augmentation port

The finitely supported prime coordinates embed in every `lp` chart.  Whether the augmentation
constraint survives the completion is decided by one quantity: whether the chart contains vectors
of augmentation one and arbitrarily small norm.

In `ℓ¹` it does not — the augmentation extends to a continuous functional of norm one, the closure
of the constraint is its kernel, closed of codimension one, and the annihilator of that kernel is
the line of the extended augmentation.  In `ℓ^p` for `1 < p < ∞`, and in the closure of the
finitely supported vectors inside `ℓ^∞` (that is, `c₀`), the spread vector
`N^{-1}(e_{q_1} + … + e_{q_N})` has augmentation one and norm `N^{1/p-1}` respectively `N^{-1}`, so
the constraint is dense, its continuous annihilator is zero, and Hausdorff reduction of the port
vanishes.
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
/-- **If the chart contains vectors of augmentation one and arbitrarily small norm, the
augmentation constraint is dense in the chart image.** -/
theorem mem_closure_image_augIdeal {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε) (l : P →₀ ℂ) :
    emb l ∈ closure (emb '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨u, hu1, hu2⟩ := hsmall (ε / (‖augment l‖ + 1))
    (by positivity)
  refine ⟨emb (l - augment l • u), ⟨l - augment l • u, ?_, rfl⟩, ?_⟩
  · rw [SetLike.mem_coe, mem_augIdeal_iff, map_sub, map_smul, hu1, smul_eq_mul, mul_one, sub_self]
  · rw [dist_eq_norm, map_sub, map_smul, sub_sub_cancel, norm_smul]
    have h1 : ‖augment l‖ * ‖emb u‖ ≤ ‖augment l‖ * (ε / (‖augment l‖ + 1)) := by
      by_cases h0 : ‖augment l‖ = 0
      · rw [h0]; simp
      · exact mul_le_mul_of_nonneg_left hu2.le (norm_nonneg _)
    have h2 : ‖augment l‖ * (ε / (‖augment l‖ + 1)) < ε := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg (augment l), hε]
    calc ‖(augment l : ℂ)‖ * ‖emb u‖ ≤ ‖augment l‖ * (ε / (‖augment l‖ + 1)) := h1
      _ < ε := h2

omit [DecidableEq P] in
/-- The spread vector `N⁻¹(e_{q₁} + ⋯ + e_{q_N})` has augmentation one. -/
theorem augment_spread {G : Finset P} (hG : G.Nonempty) :
    augment (∑ q ∈ G, Finsupp.single q ((G.card : ℂ)⁻¹)) = 1 := by
  rw [map_sum]
  have hcard : (G.card : ℂ) ≠ 0 := by
    have : 0 < G.card := Finset.card_pos.2 hG
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl fun q _ => augment_single q ((G.card : ℂ)⁻¹)]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem lpEmb_spread (G : Finset P) :
    lpEmb P p (∑ q ∈ G, Finsupp.single q ((G.card : ℂ)⁻¹))
      = ∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => lpEmb_single q _

/-! ### The erasure phases -/

/-- The spread vectors of an `ℓ^p` chart with `p > 1` have arbitrarily small norm. -/
theorem exists_small_spread_lp [Infinite P] (hp : 1 < p.toReal) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖lpEmb P p u‖ < ε := by
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
  refine ⟨∑ q ∈ G, Finsupp.single q ((G.card : ℂ)⁻¹), augment_spread hGne, ?_⟩
  rw [lpEmb_spread]
  have hns : ‖∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹)‖ ^ r = (N : ℝ) ^ (1 - r) := by
    have hbase := lp.norm_sum_single (E := fun _ : P => ℂ) (p := p) hr0
      (fun _ => ((G.card : ℂ)⁻¹)) G
    rw [hbase, Finset.sum_const, nsmul_eq_mul, norm_inv, Complex.norm_natCast, hcardR,
      Real.inv_rpow hNpos.le, Real.rpow_sub hNpos, Real.rpow_one, div_eq_mul_inv]
  have hlt : ‖∑ q ∈ G, lp.single p q ((G.card : ℂ)⁻¹)‖ ^ r < ε ^ r := by
    rw [hns]; exact hN.1
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hr0).1 hlt

/-- The spread vectors of the `ℓ^∞` chart have arbitrarily small norm. -/
theorem exists_small_spread_top [Infinite P] (ε : ℝ) (hε : 0 < ε) :
    ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖lpEmb P ⊤ u‖ < ε := by
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
  refine ⟨∑ q ∈ G, Finsupp.single q ((G.card : ℂ)⁻¹), augment_spread hGne, ?_⟩
  rw [lpEmb_spread]
  have hcoord : ∀ i : P,
      ‖((∑ q ∈ G, lp.single (⊤ : ENNReal) q ((G.card : ℂ)⁻¹) : lp (fun _ : P => ℂ) ⊤) : P → ℂ) i‖
        ≤ ((N : ℝ))⁻¹ := by
    intro i
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
    rw [Finset.sum_pi_single]
    by_cases hi : i ∈ G
    · rw [if_pos hi, norm_inv, Complex.norm_natCast, hGcard]
    · rw [if_neg hi]
      simp only [norm_zero]
      positivity
  have hle := lp.norm_le_of_forall_le (E := fun _ : P => ℂ) (by positivity) hcoord
  have hlt : ((N : ℝ))⁻¹ < ε := by
    rw [inv_lt_comm₀ hNpos hε]
    rw [one_div] at hN
    exact hN
  linarith

/-- **Theorem 3, `(RC.8)`.**  In `ℓ^p` with `p > 1` the augmentation constraint is dense in the
chart image. -/
theorem closure_image_augIdeal_lp [Infinite P] (hp : 1 < p.toReal) :
    closure ((lpEmb P p) ''
        ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P p)) := by
  apply le_antisymm
  · exact closure_mono (Set.image_subset_range _ _)
  · rw [← closure_closure (s := (lpEmb P p) '' _)]
    refine closure_mono ?_
    rintro x ⟨l, rfl⟩
    exact mem_closure_image_augIdeal _ (fun ε hε => exists_small_spread_lp hp ε hε) l

/-- **Theorem 3, `(RC.8)` for `c₀`.**  Inside `ℓ^∞` the augmentation constraint is dense in the
closure of the finitely supported vectors, which is `c₀`. -/
theorem closure_image_augIdeal_top [Infinite P] :
    closure ((lpEmb P ⊤) ''
        ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = closure (Set.range (lpEmb P ⊤)) := by
  apply le_antisymm
  · exact closure_mono (Set.image_subset_range _ _)
  · rw [← closure_closure (s := (lpEmb P ⊤) '' _)]
    refine closure_mono ?_
    rintro x ⟨l, rfl⟩
    exact mem_closure_image_augIdeal _ (fun ε hε => exists_small_spread_top ε hε) l

omit [DecidableEq P] in
/-- **Theorem 3, `(RC.8)`, the annihilator.**  A continuous functional vanishing on the
augmentation constraint vanishes on the whole chart image. -/
theorem eq_zero_on_range_of_vanishing_on_augIdeal {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε)
    (g : X →L[ℂ] ℂ) (hg : ∀ l ∈ (augIdeal : Submodule ℂ (P →₀ ℂ)), g (emb l) = 0) (l : P →₀ ℂ) :
    g (emb l) = 0 := by
  have hmem := mem_closure_image_augIdeal emb hsmall l
  have hzero : ∀ y ∈ closure ((emb) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))),
      g y = 0 := by
    intro y hy
    have hcl : closure ((emb) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
        ⊆ g ⁻¹' {0} := by
      refine closure_minimal ?_ (IsClosed.preimage g.continuous isClosed_singleton)
      rintro z ⟨m, hm, rfl⟩
      exact hg m hm
    exact hcl hy
  exact hzero _ hmem

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

/-- The augmentation as a linear functional on `ℓ¹`. -/
noncomputable def augLin : lp (fun _ : P => ℂ) 1 →ₗ[ℂ] ℂ where
  toFun := fun x => ∑' q, (x : P → ℂ) q
  map_add' := fun x y => by
    simp only [lp.coeFn_add, Pi.add_apply]
    exact (summable_lp_one x).tsum_add (summable_lp_one y)
  map_smul' := fun a x => by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [tsum_mul_left]

/-- **Theorem 2.**  The augmentation extends to a continuous functional of norm at most one on
`ℓ¹`. -/
noncomputable def augCLM : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ :=
  LinearMap.mkContinuous augLin 1 fun x => by
    rw [one_mul, norm_eq_tsum_one]
    exact norm_tsum_le_tsum_norm (summable_norm_lp_one x)

omit [DecidableEq P] in
@[simp] theorem augCLM_apply (x : lp (fun _ : P => ℂ) 1) : augCLM x = ∑' q, (x : P → ℂ) q := rfl

theorem augCLM_lpEmb (l : P →₀ ℂ) : augCLM (lpEmb P 1 l) = augment l := by
  classical
  rw [augCLM_apply, augment_apply]
  have hz : ∀ q ∉ l.support, ((lpEmb P 1 l : lp (fun _ : P => ℂ) 1) : P → ℂ) q = 0 := by
    intro q hq
    rw [lpEmb_apply_coord]
    exact Finsupp.notMem_support_iff.1 hq
  rw [tsum_eq_sum hz]
  exact Finset.sum_congr rfl fun q _ => lpEmb_apply_coord l q

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

/-- **Theorem 2, `(RC.7)`.**  In `ℓ¹` the closure of the augmentation constraint is the kernel of
the extended augmentation. -/
theorem closure_image_augIdeal_one [Nonempty P] :
    closure ((lpEmb P 1) '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))
      = {x : lp (fun _ : P => ℂ) 1 | augCLM x = 0} := by
  classical
  obtain ⟨q₀⟩ := ‹Nonempty P›
  apply le_antisymm
  · refine closure_minimal ?_ (IsClosed.preimage augCLM.continuous isClosed_singleton)
    rintro z ⟨m, hm, rfl⟩
    rw [Set.mem_setOf_eq, augCLM_lpEmb]
    exact hm
  · intro x hx
    have hx0 : augCLM x = 0 := hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have htail : Filter.Tendsto
        (fun F : Finset P => ∑' (q : {y : P // y ∉ F}), ‖(x : P → ℂ) q‖) Filter.atTop (nhds 0) :=
      tendsto_tsum_compl_atTop_zero (fun q : P => ‖(x : P → ℂ) q‖)
    have hpart : Filter.Tendsto (fun F : Finset P => ∑ q ∈ F, (x : P → ℂ) q) Filter.atTop
        (nhds 0) := by
      have := (summable_lp_one x).hasSum
      rw [← augCLM_apply x, hx0] at this
      exact this
    have hev1 := (tendsto_order.1 htail).2 (ε / 2) (by linarith)
    have hev2 := hpart.eventually (Metric.ball_mem_nhds (0 : ℂ) (by linarith : (0:ℝ) < ε / 2))
    obtain ⟨F, hF1, hF2⟩ := (hev1.and hev2).exists
    set lF : P →₀ ℂ := ∑ q ∈ F, Finsupp.single q ((x : P → ℂ) q) with hlF
    have haug : augment lF = ∑ q ∈ F, (x : P → ℂ) q := by
      rw [hlF, map_sum]
      exact Finset.sum_congr rfl fun q _ => augment_single q _
    refine ⟨lpEmb P 1 (lF - Finsupp.single q₀ (augment lF)), ⟨_, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, mem_augIdeal_iff, map_sub, augment_single, sub_self]
    · have hemb : lpEmb P 1 lF = ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q) := by
        rw [hlF, map_sum]
        exact Finset.sum_congr rfl fun q _ => lpEmb_single q _
      rw [dist_eq_norm, map_sub, hemb, lpEmb_single]
      have htri : ‖x - (∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)
            - (lp.single (1 : ENNReal) q₀ (augment lF) : lp (fun _ : P => ℂ) 1))‖
          ≤ ‖x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)‖
            + ‖(lp.single (1 : ENNReal) q₀ (augment lF) : lp (fun _ : P => ℂ) 1)‖ := by
        have : x - (∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)
              - (lp.single (1 : ENNReal) q₀ (augment lF) : lp (fun _ : P => ℂ) 1))
            = (x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q))
              + (lp.single (1 : ENNReal) q₀ (augment lF) : lp (fun _ : P => ℂ) 1) := by abel
        rw [this]
        exact norm_add_le _ _
      have hb1 : ‖x - ∑ q ∈ F, lp.single (1 : ENNReal) q ((x : P → ℂ) q)‖ < ε / 2 := by
        rw [norm_sub_trunc_one]
        exact hF1
      have hb2 : ‖(lp.single (1 : ENNReal) q₀ (augment lF) : lp (fun _ : P => ℂ) 1)‖ < ε / 2 := by
        rw [lp.norm_single (by norm_num), haug]
        have hd := hF2
        rw [dist_zero_right] at hd
        exact hd
      linarith

theorem augCLM_surjective [Nonempty P] :
    Function.Surjective (augCLM : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ) := by
  obtain ⟨q₀⟩ := ‹Nonempty P›
  intro z
  refine ⟨lp.single (1 : ENNReal) q₀ z, ?_⟩
  have := augCLM_lpEmb (P := P) (Finsupp.single q₀ z)
  rw [lpEmb_single] at this
  rw [this, augment_single]

/-- The continuous annihilator of the closed constraint is the line of the extended
augmentation. -/
theorem eq_smul_augCLM_of_vanishing [Nonempty P] (q₀ : P)
    (g : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ)
    (hg : ∀ x : lp (fun _ : P => ℂ) 1, augCLM x = 0 → g x = 0) :
    ∀ x, g x = g (lp.single (1 : ENNReal) q₀ 1) * augCLM x := by
  intro x
  have hv : augCLM (lp.single (1 : ENNReal) q₀ (1 : ℂ)) = 1 := by
    have := augCLM_lpEmb (P := P) (Finsupp.single q₀ (1 : ℂ))
    rw [lpEmb_single] at this
    rw [this, augment_single]
  have hker : augCLM (x - augCLM x • lp.single (1 : ENNReal) q₀ (1 : ℂ)) = 0 := by
    rw [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  have := hg _ hker
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul] at this
  rw [this]
  ring

/-! ### The algebraic–continuous separation defect -/

/-- **Corollary 4, the `ℓ¹` phase `𝔎 = 0`.**  Completion is injective on the algebraic port, and
every algebraic annihilator of the constraint is the restriction of a continuous one. -/
theorem separation_defect_one [Nonempty P] :
    (∀ l : P →₀ ℂ,
        lpEmb P 1 l ∈ closure ((lpEmb P 1) ''
          ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → augment l = 0) ∧
    (∀ a : ℂ, ∃ g : lp (fun _ : P => ℂ) 1 →L[ℂ] ℂ,
        (∀ x : lp (fun _ : P => ℂ) 1,
          x ∈ closure ((lpEmb P 1) ''
            ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → g x = 0) ∧
        ∀ l : P →₀ ℂ, g (lpEmb P 1 l) = a * augment l) := by
  constructor
  · intro l hl
    rw [closure_image_augIdeal_one] at hl
    rw [← augCLM_lpEmb l]
    exact hl
  · intro a
    refine ⟨a • augCLM, ?_, ?_⟩
    · intro x hx
      rw [closure_image_augIdeal_one] at hx
      simp only [smul_apply, smul_eq_mul]
      rw [hx, mul_zero]
    · intro l
      simp only [smul_apply, smul_eq_mul]
      rw [augCLM_lpEmb]

omit [DecidableEq P] in
/-- **Corollary 4, the erasure phases `𝔎 ≅ ℍ(ℂ)`.**  In a chart with arbitrarily small vectors of
augmentation one, completion kills the whole algebraic port and no algebraic annihilator except
zero extends continuously. -/
theorem separation_defect_erasure {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (emb : (P →₀ ℂ) →ₗ[ℂ] X)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ u : P →₀ ℂ, augment u = 1 ∧ ‖emb u‖ < ε) :
    (∀ l : P →₀ ℂ,
        emb l ∈ closure (emb '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ)))) ∧
    (∀ g : X →L[ℂ] ℂ,
        (∀ x, x ∈ closure (emb '' ((augIdeal : Submodule ℂ (P →₀ ℂ)) : Set (P →₀ ℂ))) → g x = 0) →
        ∀ l : P →₀ ℂ, g (emb l) = 0) :=
  ⟨fun l => mem_closure_image_augIdeal emb hsmall l,
    fun g hg l => eq_zero_on_range_of_vanishing_on_augIdeal emb hsmall g
      (fun m hm => hg _ (subset_closure ⟨m, hm, rfl⟩)) l⟩

end L1

end HTGeometry.ConstraintMotiveRelativity
