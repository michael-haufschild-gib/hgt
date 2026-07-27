import Mathlib

/-!
# The infinite occupation law

For an arbitrary index type `ι` and nonnegative one-particle weights `u : ι → ℝ≥0∞`, the total
weight of every finitely supported bosonic occupation is exactly the supremum of the finite Euler
products

`∑' ν : ι →₀ ℕ, ∏ a, u a ^ ν a = ⨆ S : Finset ι, ∏ a ∈ S, (1 - u a)⁻¹`.

When the weights are finite and strictly below one, the occupation mass is finite exactly when the
one-particle mass is summable.  No countability assumption is imposed: summability itself forces
the effective support to be countable.
-/

namespace HTGeometry

open scoped BigOperators ENNReal

/-- The elementary finite-dimensional geometric-series identity. -/
private theorem tsum_pi_geometric_fin :
    ∀ (n : ℕ) (u : Fin n → ℝ≥0∞),
      ∑' f : Fin n → ℕ, ∏ i, u i ^ f i =
        ∏ i, (1 - u i)⁻¹ := by
  intro n
  induction n with
  | zero =>
      intro u
      simp
  | succ n ih =>
      intro u
      rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).tsum_eq]
      simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
      rw [show
        (∑' c : ℕ × (Fin n → ℕ), u 0 ^ c.1 * ∏ x, u x.succ ^ c.2 x) =
          ∑' a : ℕ, ∑' b : Fin n → ℕ, u 0 ^ a * ∏ x, u x.succ ^ b x
        from ENNReal.tsum_prod
          (f := fun (a : ℕ) (b : Fin n → ℕ) =>
            u 0 ^ a * ∏ x : Fin n, u x.succ ^ b x)]
      simp_rw [ENNReal.tsum_mul_left]
      rw [ih]
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]

/-- The geometric-series identity for an arbitrary finite type. -/
private theorem tsum_pi_geometric {ι : Type*} [Fintype ι] (u : ι → ℝ≥0∞) :
    ∑' f : ι → ℕ, ∏ i, u i ^ f i =
      ∏ i, (1 - u i)⁻¹ := by
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  calc
    ∑' f : ι → ℕ, ∏ i, u i ^ f i =
        ∑' h : Fin (Fintype.card ι) → ℕ,
          ∏ j, u (e.symm j) ^ h j := by
            rw [← pe.tsum_eq]
            congr 1
            funext f
            exact Fintype.prod_equiv e (fun i => u i ^ f i)
              (fun j => u (e.symm j) ^ pe f j) (by simp [pe])
    _ = ∏ j, (1 - u (e.symm j))⁻¹ :=
      tsum_pi_geometric_fin _ _
    _ = ∏ i, (1 - u i)⁻¹ := by
      exact Fintype.prod_equiv e.symm
        (fun j => (1 - u (e.symm j))⁻¹)
        (fun i => (1 - u i)⁻¹) (by simp)

private def finsetSubtypeEmbedding {ι : Type*} (S : Finset ι) : S ↪ ι :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- A function on a finite set is the same as a finitely supported occupation whose support lies
in that set. -/
private noncomputable def supportedOccupationEquiv {ι : Type*} (S : Finset ι) :
    (S → ℕ) ≃ {ν : ι →₀ ℕ // ν.support ⊆ S} where
  toFun f :=
    ⟨Finsupp.embDomain (finsetSubtypeEmbedding S)
        (Finsupp.equivFunOnFinite.symm f), by
      classical
      intro a ha
      rw [Finsupp.support_embDomain] at ha
      rcases Finset.mem_map.1 ha with ⟨b, _, rfl⟩
      exact b.property⟩
  invFun ν := fun a => ν.1 a
  left_inv f := by
    funext a
    change
      (Finsupp.embDomain (finsetSubtypeEmbedding S)
        (Finsupp.equivFunOnFinite.symm f)) (finsetSubtypeEmbedding S a) = f a
    rw [Finsupp.embDomain_apply_self]
    rfl
  right_inv ν := by
    classical
    apply Subtype.ext
    ext a
    by_cases ha : a ∈ S
    · have : a = finsetSubtypeEmbedding S ⟨a, ha⟩ := rfl
      rw [this, Finsupp.embDomain_apply_self]
      rfl
    · rw [Finsupp.embDomain_notin_range]
      · exact (Finsupp.notMem_support_iff.mp (fun h => ha (ν.2 h))).symm
      · rintro ⟨b, hb⟩
        apply ha
        change (b : ι) = a at hb
        rw [← hb]
        exact b.property

/-- Multiplicative weight of a finitely supported occupation. -/
noncomputable def occupationWeight {ι : Type*}
    (u : ι → ℝ≥0∞) (ν : ι →₀ ℕ) : ℝ≥0∞ :=
  ν.prod fun a n => u a ^ n

private theorem occupationWeight_supportedOccupationEquiv {ι : Type*}
    (u : ι → ℝ≥0∞) (S : Finset ι) (f : S → ℕ) :
    occupationWeight u ((supportedOccupationEquiv S) f).1 =
      ∏ a : S, u a ^ f a := by
  classical
  rw [occupationWeight]
  change
    (Finsupp.embDomain (finsetSubtypeEmbedding S)
      (Finsupp.equivFunOnFinite.symm f)).prod (fun a n => u a ^ n) = _
  rw [Finsupp.prod_embDomain, Finsupp.prod_fintype]
  · rfl
  · intro
    simp

/-- Total weight of occupations supported in one prescribed finite set. -/
theorem tsum_supported_occupationWeight {ι : Type*}
    (u : ι → ℝ≥0∞) (S : Finset ι) :
    ∑' ν : {ν : ι →₀ ℕ // ν.support ⊆ S}, occupationWeight u ν.1 =
      ∏ a ∈ S, (1 - u a)⁻¹ := by
  rw [← (supportedOccupationEquiv S).tsum_eq]
  simp_rw [occupationWeight_supportedOccupationEquiv]
  rw [tsum_pi_geometric]
  exact (Finset.prod_subtype S (fun _ => by simp)
    (fun a => (1 - u a)⁻¹)).symm

/-- **Exact arbitrary-index occupation law.**  The total bosonic occupation mass is the directed
supremum of all finite Euler products. -/
theorem occupationMass_eq_iSup_finset {ι : Type*} (u : ι → ℝ≥0∞) :
    ∑' ν : ι →₀ ℕ, occupationWeight u ν =
      ⨆ S : Finset ι, ∏ a ∈ S, (1 - u a)⁻¹ := by
  classical
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro T
    let S : Finset ι := T.biUnion Finsupp.support
    calc
      ∑ ν ∈ T, occupationWeight u ν =
          ∑ ν ∈ T, Set.indicator
            {ν : ι →₀ ℕ | ν.support ⊆ S} (occupationWeight u) ν := by
              apply Finset.sum_congr rfl
              intro ν hν
              rw [Set.indicator_of_mem]
              exact Finset.subset_biUnion_of_mem Finsupp.support hν
      _ ≤ ∑' ν : ι →₀ ℕ, Set.indicator
            {ν : ι →₀ ℕ | ν.support ⊆ S} (occupationWeight u) ν :=
          ENNReal.sum_le_tsum T
      _ = ∑' ν : {ν : ι →₀ ℕ // ν.support ⊆ S},
            occupationWeight u ν.1 := (tsum_subtype _ _).symm
      _ = ∏ a ∈ S, (1 - u a)⁻¹ :=
        tsum_supported_occupationWeight u S
      _ ≤ ⨆ R : Finset ι, ∏ a ∈ R, (1 - u a)⁻¹ :=
        le_iSup (fun R : Finset ι => ∏ a ∈ R, (1 - u a)⁻¹) S
  · apply iSup_le
    intro S
    rw [← tsum_supported_occupationWeight u S]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (occupationWeight u)

@[simp] theorem occupationWeight_single {ι : Type*} (u : ι → ℝ≥0∞)
    (a : ι) :
    occupationWeight u (Finsupp.single a 1) = u a := by
  classical
  simp [occupationWeight]

/-- The one-particle sector embeds in the full occupation space. -/
theorem nome_tsum_le_occupationMass {ι : Type*} (u : ι → ℝ≥0∞) :
    ∑' a, u a ≤ ∑' ν : ι →₀ ℕ, occupationWeight u ν := by
  let e : ι ↪ (ι →₀ ℕ) :=
    ⟨fun a => Finsupp.single a 1, Finsupp.single_left_injective one_ne_zero⟩
  calc
    ∑' a, u a = ∑' a, occupationWeight u (e a) := by
      congr 1
      funext a
      exact (occupationWeight_single u a).symm
    _ ≤ ∑' ν : ι →₀ ℕ, occupationWeight u ν :=
      ENNReal.tsum_comp_le_tsum_of_injective e.injective _

/-- **Sharp summability threshold.**  If every one-particle weight is below one, the total weight
of all finite occupations is finite exactly when the one-particle weights are summable. -/
theorem occupationMass_ne_top_iff {ι : Type*} (u : ι → NNReal)
    (hu_lt : ∀ a, u a < 1) :
    (∑' ν : ι →₀ ℕ, occupationWeight (fun a => (u a : ℝ≥0∞)) ν) ≠ ∞ ↔
      Summable (fun a => (u a : ℝ)) := by
  classical
  constructor
  · intro hmass
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
    exact ne_top_of_le_ne_top hmass
      (nome_tsum_le_occupationMass (fun a => (u a : ℝ≥0∞)))
  · intro hu
    let v : ι → NNReal := fun a => u a / (1 - u a)
    have hv : Summable (fun a => (v a : ℝ)) := by
      apply (hu.mul_left 2).of_norm_bounded_eventually
      filter_upwards
        [hu.tendsto_cofinite_zero.eventually_le_const
          (show (0 : ℝ) < 1 / 2 by norm_num)] with a ha
      have hua0 : 0 ≤ (u a : ℝ) := (u a).property
      have hden : 0 < 1 - (u a : ℝ) := by
        exact sub_pos.mpr (mod_cast hu_lt a)
      simp only [v, NNReal.coe_div, NNReal.coe_sub (le_of_lt (hu_lt a))]
      change ‖(u a : ℝ) / (1 - (u a : ℝ))‖ ≤ 2 * (u a : ℝ)
      rw [Real.norm_of_nonneg (div_nonneg hua0 hden.le)]
      apply (div_le_iff₀ hden).2
      nlinarith
    have hfactor_nn : ∀ a, (1 - u a)⁻¹ = 1 + v a := by
      intro a
      apply NNReal.eq
      simp only [v, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one,
        NNReal.coe_div, NNReal.coe_sub (le_of_lt (hu_lt a))]
      have hne : 1 - (u a : ℝ) ≠ 0 :=
        ne_of_gt (sub_pos.mpr (mod_cast hu_lt a))
      field_simp
      ring
    have hfactor_en : ∀ a,
        (1 - (u a : ℝ≥0∞))⁻¹ = ((1 + v a : NNReal) : ℝ≥0∞) := by
      intro a
      calc
        (1 - (u a : ℝ≥0∞))⁻¹ =
            (((1 - u a : NNReal) : ℝ≥0∞))⁻¹ := by
              rw [ENNReal.coe_sub]
              simp
        _ = (((1 - u a : NNReal)⁻¹ : NNReal) : ℝ≥0∞) :=
          (ENNReal.coe_inv (ne_of_gt (tsub_pos_iff_lt.mpr (hu_lt a)))).symm
        _ = ((1 + v a : NNReal) : ℝ≥0∞) :=
          congrArg (fun q : NNReal => (q : ℝ≥0∞)) (hfactor_nn a)
    obtain ⟨r, hr, S₀, hS₀⟩ :=
      (Real.multipliable_one_add_of_summable hv).eventually_bounded_finsetProd
    have hbound : ∀ S : Finset ι,
        ∏ a ∈ S, (1 - (u a : ℝ≥0∞))⁻¹ ≤ ENNReal.ofReal r := by
      intro S
      have hprod :
          ∏ a ∈ S, (1 + (v a : ℝ)) ≤ r := by
        calc
          ∏ a ∈ S, (1 + (v a : ℝ)) ≤
              ∏ a ∈ S ∪ S₀, (1 + (v a : ℝ)) := by
                apply Finset.prod_le_prod_of_subset_of_one_le
                  Finset.subset_union_left
                · intro a _
                  positivity
                intro a _ _
                exact le_add_of_nonneg_right (v a).property
          _ ≤ r := hS₀ (S ∪ S₀) Finset.subset_union_right
      simp_rw [hfactor_en]
      rw [← ENNReal.coe_finsetProd]
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast hprod
    rw [occupationMass_eq_iSup_finset]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hbound)

end HTGeometry
