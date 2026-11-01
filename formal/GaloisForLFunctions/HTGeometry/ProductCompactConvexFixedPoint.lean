import GaloisForLFunctions.HTGeometry.SimplexFixedPoint

/-!
# Compact-convex fixed points in products

Finite coordinate distances turn compactness into finite simplex
approximations. A fixed point of each approximation has arbitrarily small
displacement in the chosen coordinates. Compactness then gives an exact
fixed point in the product topology.
-/

noncomputable section
open Set Finset

namespace GaloisForLFunctions.HTGeometry

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sum of coordinate distances over a finite set of coordinates. -/
def finiteCoordinateDist (s : Finset I) (x y : I → E) : ℝ :=
  ∑ i ∈ s, ‖x i - y i‖

omit [NormedSpace ℝ E] in
theorem continuous_finiteCoordinateDist (s : Finset I) :
    Continuous (fun p : (I → E) × (I → E) => finiteCoordinateDist s p.1 p.2) :=
  continuous_finsetSum s fun i _ =>
    (((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)).norm

omit [NormedSpace ℝ E] in
theorem finiteCoordinateDist_nonneg (s : Finset I) (x y : I → E) :
    0 ≤ finiteCoordinateDist s x y :=
  sum_nonneg fun _ _ => norm_nonneg _

/-- A finite-coordinate distance is convex in its second argument. -/
theorem finiteCoordinateDist_sum_le {J : Type*} [Fintype J]
    (s : Finset I) (x : I → E) (y : J → I → E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    finiteCoordinateDist s x (∑ j, w j • y j) ≤
      ∑ j, w j * finiteCoordinateDist s x (y j) := by
  have he (i : I) : x i - (∑ j, w j • y j) i = ∑ j, w j • (x i - y j i) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_sub, sum_sub_distrib,
      ← Finset.sum_smul, hsum, one_smul]
  calc
    finiteCoordinateDist s x (∑ j, w j • y j)
        = ∑ i ∈ s, ‖∑ j, w j • (x i - y j i)‖ := by
          simp only [finiteCoordinateDist, he]
    _ ≤ ∑ i ∈ s, ∑ j, w j * ‖x i - y j i‖ := by
      apply sum_le_sum
      intro i _
      calc
        ‖∑ j, w j • (x i - y j i)‖ ≤ ∑ j, ‖w j • (x i - y j i)‖ := norm_sum_le _ _
        _ = ∑ j, w j * ‖x i - y j i‖ := by
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _)]
    _ = ∑ j, w j * finiteCoordinateDist s x (y j) := by
      rw [sum_comm]
      simp only [finiteCoordinateDist, mul_sum]

/-- A convex combination of strictly close points remains strictly close. -/
theorem finiteCoordinateDist_sum_lt {J : Type*} [Fintype J]
    (s : Finset I) (x : I → E) (y : J → I → E) (w : stdSimplex ℝ J)
    {ε : ℝ} (hclose : ∀ j, w.val j ≠ 0 → finiteCoordinateDist s x (y j) < ε) :
    finiteCoordinateDist s x (∑ j, w.val j • y j) < ε := by
  have hpos : ∃ j, 0 < w.val j := by
    by_contra! h
    have hsum : ∑ j, w.val j ≤ 0 := sum_nonpos fun j _ => h j
    rw [w.property.2] at hsum
    exact (not_le_of_gt zero_lt_one) hsum
  obtain ⟨j₀, hj₀⟩ := hpos
  have hle (j : J) : w.val j * finiteCoordinateDist s x (y j) ≤ w.val j * ε := by
    by_cases hj : w.val j = 0
    · simp only [hj, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hclose j hj).le (w.property.1 j)
  calc
    finiteCoordinateDist s x (∑ j, w.val j • y j)
        ≤ ∑ j, w.val j * finiteCoordinateDist s x (y j) :=
      finiteCoordinateDist_sum_le s x y w.val w.property.1 w.property.2
    _ < ∑ j, w.val j * ε := sum_lt_sum (fun j _ => hle j)
      ⟨j₀, mem_univ _, mul_lt_mul_of_pos_left (hclose j₀ hj₀.ne') hj₀⟩
    _ = ε := by rw [← sum_mul, w.property.2, one_mul]

/-- Compactness and Brouwer give an approximate fixed point in any finite coordinates. -/
theorem exists_finiteCoordinate_approx_fixedPoint {K : Set (I → E)}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : K → K) (hf : Continuous f) (s : Finset I) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : K, finiteCoordinateDist s (f x).val x.val < ε := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hne.to_subtype
  let d : K → K → ℝ := fun x y => finiteCoordinateDist s (f x).val y.val
  have hd (y : K) : Continuous (fun x => d x y) :=
    (continuous_finiteCoordinateDist s).comp
      ((continuous_subtype_val.comp hf).prodMk continuous_const)
  let U : K → Set K := fun y => {x | d x y < ε}
  have hU (y : K) : IsOpen (U y) := isOpen_lt (hd y) continuous_const
  have hcover : (univ : Set K) ⊆ ⋃ y, U y := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨f x, ?_⟩
    simpa only [U, mem_setOf_eq, d, finiteCoordinateDist, sub_self, norm_zero, sum_const_zero]
      using hε
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  have htcover (x : K) : ∃ y ∈ t, d x y < ε := by
    simpa only [mem_iUnion, U, mem_setOf_eq, exists_prop] using ht (mem_univ x)
  have htne : t.Nonempty := by
    obtain ⟨y, hy, _⟩ := htcover (Classical.arbitrary K)
    exact ⟨y, hy⟩
  letI : Nonempty t := htne.to_subtype
  let a : K → t → ℝ := fun x j => max 0 (ε - d x j.val)
  have ha (j : t) : Continuous (fun x => a x j) :=
    continuous_const.max (continuous_const.sub (hd j.val))
  have hsum (x : K) : 0 < ∑ j : t, a x j := by
    obtain ⟨y, hy, hxy⟩ := htcover x
    exact sum_pos' (fun j _ => le_max_left _ _)
      ⟨⟨y, hy⟩, mem_univ _, lt_of_lt_of_le (sub_pos.mpr hxy) (le_max_right _ _)⟩
  let ρ : K → stdSimplex ℝ t := fun x =>
    ⟨fun j => a x j / ∑ l : t, a x l,
      fun j => div_nonneg (le_max_left _ _) (hsum x).le,
      by rw [← sum_div]; exact div_self (hsum x).ne'⟩
  have hρ : Continuous ρ := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (ha j).div (continuous_finsetSum univ fun l _ => ha l)
      (fun x => (hsum x).ne')
  let b : stdSimplex ℝ t → K := fun w =>
    ⟨∑ j : t, w.val j • j.val.val,
      hconv.sum_mem (fun j _ => w.property.1 j) w.property.2
        (fun j _ => j.val.property)⟩
  have hb : Continuous b := by
    apply Continuous.subtype_mk
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp continuous_subtype_val).smul continuous_const
  obtain ⟨w, hw⟩ := exists_fixedPoint_stdSimplex (ρ ∘ b) (hρ.comp hb)
  refine ⟨b w, ?_⟩
  have hclose (j : t) (hj : w.val j ≠ 0) : d (b w) j.val < ε := by
    have he : (ρ (b w)).val j = w.val j := congrArg (fun v : stdSimplex ℝ t => v.val j) hw
    have ha0 : a (b w) j ≠ 0 := by
      intro hz
      apply hj
      rw [← he]
      change a (b w) j / _ = 0
      rw [hz, zero_div]
    have hp : 0 < max 0 (ε - d (b w) j.val) :=
      lt_of_le_of_ne (le_max_left _ _) (Ne.symm ha0)
    have hh : 0 < ε - d (b w) j.val := (lt_max_iff.mp hp).resolve_left (lt_irrefl 0)
    exact sub_pos.mp hh
  exact finiteCoordinateDist_sum_lt s (f (b w)).val (fun j : t => j.val.val) w hclose

/-- Schauder's fixed-point theorem for compact convex subsets of a product of normed spaces. -/
theorem exists_fixedPoint_compact_convex_product {K : Set (I → E)}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : K → K) (hf : Continuous f) : ∃ x, f x = x := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : Nonempty K := hne.to_subtype
  by_contra! hfix
  let U : I → Set K := fun i => {x | 0 < ‖(f x).val i - x.val i‖}
  have hU (i : I) : IsOpen (U i) := isOpen_lt continuous_const
    ((((continuous_apply i).comp continuous_subtype_val).comp hf).sub
      ((continuous_apply i).comp continuous_subtype_val)).norm
  have hcover : (univ : Set K) ⊆ ⋃ i, U i := by
    intro x _
    have hneval : (f x).val ≠ x.val := fun h => hfix x (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hneval
    exact mem_iUnion.mpr ⟨i, norm_pos_iff.mpr (sub_ne_zero.mpr hi)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let d : K → ℝ := fun x => finiteCoordinateDist s (f x).val x.val
  have hd : Continuous d := (continuous_finiteCoordinateDist s).comp
    ((continuous_subtype_val.comp hf).prodMk continuous_subtype_val)
  have hdpos (x : K) : 0 < d x := by
    obtain ⟨i, hi, hix⟩ : ∃ i ∈ s, 0 < ‖(f x).val i - x.val i‖ := by
      simpa only [mem_iUnion, U, mem_setOf_eq, exists_prop] using hs (mem_univ x)
    exact sum_pos' (fun i _ => norm_nonneg _) ⟨i, hi, hix⟩
  obtain ⟨x₀, _, hmin⟩ := isCompact_univ.exists_isMinOn
    (Set.univ_nonempty : (univ : Set K).Nonempty) hd.continuousOn
  obtain ⟨x, hx⟩ := exists_finiteCoordinate_approx_fixedPoint hK hne hconv f hf s (hdpos x₀)
  exact (not_lt_of_ge (hmin (mem_univ x))) hx

/-- A separating continuous linear coordinate map transfers the compact-convex fixed-point law. -/
theorem exists_fixedPoint_compact_convex_of_linear_injection
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (L : V →ₗ[ℝ] (I → E)) (hL : Continuous L) (hinj : Function.Injective L)
    {K : Set V} (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (f : K → K) (hf : Continuous f) : ∃ x, f x = x := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let e : K ≃ L '' K := Equiv.Set.image L K hinj
  have he : Continuous e := (hL.comp continuous_subtype_val).subtype_mk _
  let h : K ≃ₜ L '' K := he.homeoOfEquivCompactToT2
  let g : L '' K → L '' K := fun x => h (f (h.symm x))
  have hg : Continuous g := h.continuous.comp (hf.comp h.symm.continuous)
  obtain ⟨x, hx⟩ := exists_fixedPoint_compact_convex_product
    (hK.image hL) (hne.image L) (hconv.linear_image L) g hg
  refine ⟨h.symm x, h.injective ?_⟩
  simpa only [Homeomorph.apply_symm_apply] using hx

end GaloisForLFunctions.HTGeometry
