import Mathlib

/-!
# Escape subgroups of a complex vector group

An *escape subgroup* of a complex topological vector group `E` is a closed additive subgroup `P`
whose identity component is a complex-linear subspace — so that `E ⧸ P` is a connected abelian
complex Lie group — and whose quotient `E ⧸ P` is noncompact.  These are the period groups that a
facet separation of a hypertranscendental relation complex must exhibit.

* `idComponentSet` — the identity component of an additive subgroup, read inside the ambient group;
* `IsEscapeSubgroup` — the three conditions above;
* `pencilSubgroup` — the periodic-pencil escape group `{z : ℓ z ∈ ℤ}` of a nonzero linear form, and
  `isEscapeSubgroup_pencilSubgroup`, which verifies all three conditions for it;
* **`exists_rat_relation_of_isEscapeSubgroup_dim_one`** — in complex dimension one an escape
  subgroup contains no two `ℚ`-independent elements: a full lattice would make the quotient
  compact, and an irrational ratio would make the subgroup contain a whole real line, forcing its
  identity component to be all of `E`.
-/

open Set Topology

namespace GaloisForLFunctions

/-! ## Preconnected sets of integers -/

/-- A preconnected set of complex numbers all of whose members are integers has at most one
element: its image under the real part is order-connected, and no interval with distinct integer
endpoints consists of integers. -/
theorem subsingleton_of_isPreconnected_subset_intCast {S : Set ℂ} (hS : IsPreconnected S)
    (hsub : S ⊆ Set.range ((↑) : ℤ → ℂ)) : S.Subsingleton := by
  intro a ha b hb
  obtain ⟨m, rfl⟩ := hsub ha
  obtain ⟨n, rfl⟩ := hsub hb
  by_contra hne
  have hmn : m ≠ n := by
    intro h; exact hne (by rw [h])
  -- the real part image is preconnected, hence order-connected, and consists of integers
  have himg : IsPreconnected (Complex.re '' S) :=
    hS.image _ Complex.continuous_re.continuousOn
  have hint : ∀ x ∈ Complex.re '' S, ∃ k : ℤ, (k : ℝ) = x := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, rfl⟩ := hsub hz
    exact ⟨k, by simp⟩
  have hma : ((m : ℝ)) ∈ Complex.re '' S := ⟨(m : ℂ), ha, by simp⟩
  have hnb : ((n : ℝ)) ∈ Complex.re '' S := ⟨(n : ℂ), hb, by simp⟩
  have hord := himg.ordConnected
  -- pick the midpoint between the smaller integer and its successor
  rcases lt_or_gt_of_ne (show (m : ℝ) ≠ (n : ℝ) by exact_mod_cast fun h => hmn (by exact_mod_cast h))
    with hlt | hlt
  · have hmem : ((m : ℝ) + 1 / 2) ∈ Complex.re '' S := by
      refine hord.out hma hnb ⟨by linarith, ?_⟩
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast hlt)
      linarith
    obtain ⟨k, hk⟩ := hint _ hmem
    have : ((2 * k : ℤ) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) := by push_cast; rw [hk]; ring
    have hz : (2 * k : ℤ) = 2 * m + 1 := by exact_mod_cast this
    omega
  · have hmem : ((n : ℝ) + 1 / 2) ∈ Complex.re '' S := by
      refine hord.out hnb hma ⟨by linarith, ?_⟩
      have : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr (by exact_mod_cast hlt)
      linarith
    obtain ⟨k, hk⟩ := hint _ hmem
    have : ((2 * k : ℤ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by push_cast; rw [hk]; ring
    have hz : (2 * k : ℤ) = 2 * n + 1 := by exact_mod_cast this
    omega

/-! ## Identity components and escape subgroups -/

/-- The identity component of an additive subgroup, read inside the ambient group. -/
def idComponentSet {E : Type*} [AddGroup E] [TopologicalSpace E] (P : AddSubgroup E) : Set E :=
  ((↑) : P → E) '' connectedComponent (0 : P)

theorem idComponentSet_subset {E : Type*} [AddGroup E] [TopologicalSpace E] (P : AddSubgroup E) :
    idComponentSet P ⊆ (P : Set E) := by
  rintro _ ⟨p, -, rfl⟩
  exact p.2

theorem zero_mem_idComponentSet {E : Type*} [AddGroup E] [TopologicalSpace E]
    (P : AddSubgroup E) : (0 : E) ∈ idComponentSet P :=
  ⟨(0 : P), mem_connectedComponent, rfl⟩

/-- A connected subset of `P` containing the origin lies in the identity component. -/
theorem subset_idComponentSet {E : Type*} [AddGroup E] [TopologicalSpace E] {P : AddSubgroup E}
    {ι : Type*} [TopologicalSpace ι] [PreconnectedSpace ι] (γ : ι → E)
    (hmem : ∀ t, γ t ∈ P) (hcont : Continuous γ) {t₀ : ι} (hzero : γ t₀ = 0) :
    Set.range γ ⊆ idComponentSet P := by
  set g : ι → P := fun t => ⟨γ t, hmem t⟩ with hg
  have hgcont : Continuous g := continuous_induced_rng.mpr hcont
  have hpre : IsPreconnected (Set.range g) := isPreconnected_range hgcont
  have hzero' : (0 : P) ∈ Set.range g := ⟨t₀, by simp [hg, Subtype.ext_iff, hzero]⟩
  have hsub : Set.range g ⊆ connectedComponent (0 : P) :=
    hpre.subset_connectedComponent hzero'
  rintro _ ⟨t, rfl⟩
  exact ⟨g t, hsub ⟨t, rfl⟩, rfl⟩

/-- **An escape subgroup.**  A closed additive subgroup of a complex topological vector group whose
identity component is a complex-linear subspace and whose quotient is noncompact. -/
structure IsEscapeSubgroup {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (P : AddSubgroup E) : Prop where
  isClosed : IsClosed (P : Set E)
  linearIdComponent : ∃ W : Submodule ℂ E, (W : Set E) = idComponentSet P
  noncompactQuotient : ¬ CompactSpace (E ⧸ P)

/-! ## The periodic-pencil escape subgroup -/

/-- The linear form attached to a pencil coefficient vector. -/
noncomputable def pencilForm {d : ℕ} (u : Fin d → ℂ) : (Fin d → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ i, u i * z i
  map_add' z w := by
    simp only [Pi.add_apply, mul_add]
    exact Finset.sum_add_distrib
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] theorem pencilForm_apply {d : ℕ} (u z : Fin d → ℂ) :
    pencilForm u z = ∑ i, u i * z i := rfl

theorem continuous_pencilForm {d : ℕ} (u : Fin d → ℂ) : Continuous (pencilForm u) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The periodic-pencil period group of a linear form: the vectors on which the form is an
integer. -/
noncomputable def pencilSubgroup {d : ℕ} (u : Fin d → ℂ) : AddSubgroup (Fin d → ℂ) :=
  (AddSubgroup.zmultiples (1 : ℂ)).comap (pencilForm u).toAddMonoidHom

theorem mem_pencilSubgroup {d : ℕ} (u z : Fin d → ℂ) :
    z ∈ pencilSubgroup u ↔ ∃ k : ℤ, pencilForm u z = (k : ℂ) := by
  simp only [pencilSubgroup, AddSubgroup.mem_comap, AddSubgroup.mem_zmultiples_iff,
    LinearMap.toAddMonoidHom_coe]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; simp⟩

theorem coe_zmultiples_one : ((AddSubgroup.zmultiples (1 : ℂ)) : Set ℂ)
    = Set.range ((↑) : ℤ → ℂ) := by
  ext z
  simp only [SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff, Set.mem_range]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩

theorem isClosed_pencilSubgroup {d : ℕ} (u : Fin d → ℂ) :
    IsClosed ((pencilSubgroup u : Set (Fin d → ℂ))) := by
  have : (pencilSubgroup u : Set (Fin d → ℂ))
      = (pencilForm u) ⁻¹' (Set.range ((↑) : ℤ → ℂ)) := by
    ext z
    simp only [SetLike.mem_coe, mem_pencilSubgroup, Set.mem_preimage, Set.mem_range]
    exact exists_congr fun _ => eq_comm
  rw [this]
  exact Complex.isClosed_range_intCast.preimage (continuous_pencilForm u)

/-- The identity component of a pencil period group is the kernel of its form. -/
theorem idComponentSet_pencilSubgroup {d : ℕ} (u : Fin d → ℂ) :
    idComponentSet (pencilSubgroup u) = ((LinearMap.ker (pencilForm u) : Submodule ℂ _) : Set _) := by
  apply Set.Subset.antisymm
  · -- the form is continuous and integer valued on `P`, so it is constant on the component
    rintro _ ⟨p, hp, rfl⟩
    have hpre : IsPreconnected (connectedComponent (0 : pencilSubgroup u)) :=
      isPreconnected_connectedComponent
    set f : (pencilSubgroup u) → ℂ := fun q => pencilForm u (q : Fin d → ℂ) with hf
    have hfcont : Continuous f :=
      (continuous_pencilForm u).comp continuous_subtype_val
    have himg : IsPreconnected (f '' connectedComponent (0 : pencilSubgroup u)) :=
      hpre.image _ hfcont.continuousOn
    have hsub : f '' connectedComponent (0 : pencilSubgroup u) ⊆ Set.range ((↑) : ℤ → ℂ) := by
      rintro _ ⟨q, -, rfl⟩
      obtain ⟨k, hk⟩ := (mem_pencilSubgroup u (q : Fin d → ℂ)).mp q.2
      exact ⟨k, hk.symm⟩
    have hzero : f 0 ∈ f '' connectedComponent (0 : pencilSubgroup u) :=
      ⟨0, mem_connectedComponent, rfl⟩
    have hfp : f p ∈ f '' connectedComponent (0 : pencilSubgroup u) := ⟨p, hp, rfl⟩
    have := subsingleton_of_isPreconnected_subset_intCast himg hsub hfp hzero
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    simpa [hf, map_zero] using this
  · -- every kernel vector is joined to the origin inside `P` by the real ray through it
    intro z hz
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hz
    have hray : ∀ t : ℝ, ((t : ℂ) • z) ∈ pencilSubgroup u := by
      intro t
      refine (mem_pencilSubgroup u _).mpr ⟨0, ?_⟩
      rw [map_smul, hz]
      simp
    have hcont : Continuous fun t : ℝ => ((t : ℂ) • z) :=
      (Complex.continuous_ofReal.smul continuous_const)
    have hzero : ((0 : ℝ) : ℂ) • z = 0 := by simp
    have hsub := subset_idComponentSet (P := pencilSubgroup u)
      (fun t : ℝ => ((t : ℂ) • z)) hray hcont hzero
    have : z ∈ Set.range fun t : ℝ => ((t : ℂ) • z) := ⟨1, by simp⟩
    exact hsub this

/-- A pencil form with a nonzero coefficient is surjective. -/
theorem pencilForm_surjective {d : ℕ} {u : Fin d → ℂ} (hu : u ≠ 0) :
    Function.Surjective (pencilForm u) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  have hu₀ : u i₀ ≠ 0 := by simpa using hi₀
  intro c
  refine ⟨fun i => if i = i₀ then c / u i₀ else 0, ?_⟩
  simp only [pencilForm_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i₀ (fun i => u i * (c / u i₀))]
  simp only [Finset.mem_univ, if_true]
  field_simp

/-- **A quotient admitting a continuous additive surjection onto the real line is noncompact.** -/
theorem not_compactSpace_quotient_of_realSurjection {E : Type*} [AddCommGroup E]
    [TopologicalSpace E] {P : AddSubgroup E} (g : E →+ ℝ) (hg : Continuous g)
    (hker : ∀ p ∈ P, g p = 0) (hsurj : Function.Surjective g) :
    ¬ CompactSpace (E ⧸ P) := by
  intro hcompact
  have hcompat : ∀ a b : E, (QuotientAddGroup.leftRel P) a b → g a = g b := by
    intro a b hab
    have hmem : -a + b ∈ P := QuotientAddGroup.leftRel_apply.mp hab
    have hzero := hker _ hmem
    rw [map_add, map_neg] at hzero
    linarith
  have hhcont : Continuous (Quotient.lift (g : E → ℝ) hcompat) := hg.quotient_lift hcompat
  have hqsurj : Function.Surjective (Quotient.lift (g : E → ℝ) hcompat) := by
    intro r
    obtain ⟨z, hz⟩ := hsurj r
    exact ⟨QuotientAddGroup.mk z, hz⟩
  have : IsCompact (Set.univ : Set ℝ) := by
    have := (hcompact.isCompact_univ).image hhcont
    rwa [Set.image_univ, hqsurj.range_eq] at this
  exact absurd this (noncompact_univ ℝ)

/-- The quotient by a pencil period group is noncompact: the imaginary part of the form descends to
a continuous surjection onto the real line. -/
theorem noncompact_quotient_pencilSubgroup {d : ℕ} {u : Fin d → ℂ} (hu : u ≠ 0) :
    ¬ CompactSpace ((Fin d → ℂ) ⧸ pencilSubgroup u) := by
  refine not_compactSpace_quotient_of_realSurjection
    (AddMonoidHom.mk' (fun z => (pencilForm u z).im) ?_) ?_ ?_ ?_
  · intro a b
    simp [map_add]
  · exact Complex.continuous_im.comp (continuous_pencilForm u)
  · intro p hp
    obtain ⟨k, hk⟩ := (mem_pencilSubgroup u p).mp hp
    show (pencilForm u p).im = 0
    rw [hk]
    simp
  · intro r
    obtain ⟨z, hz⟩ := pencilForm_surjective hu (r * Complex.I)
    refine ⟨z, ?_⟩
    show (pencilForm u z).im = r
    rw [hz]
    simp

/-- **The periodic pencil produces an escape subgroup.**  For a nonzero coefficient vector the
period group `{z : ℓ z ∈ ℤ}` is closed, has the kernel of `ℓ` as identity component, and has
noncompact quotient. -/
theorem isEscapeSubgroup_pencilSubgroup {d : ℕ} {u : Fin d → ℂ} (hu : u ≠ 0) :
    IsEscapeSubgroup (pencilSubgroup u) where
  isClosed := isClosed_pencilSubgroup u
  linearIdComponent := ⟨LinearMap.ker (pencilForm u), (idComponentSet_pencilSubgroup u).symm⟩
  noncompactQuotient := noncompact_quotient_pencilSubgroup hu

/-! ## Escape subgroups in complex dimension one -/

namespace DimOne

/-- Two vectors of `Fin 1 → ℂ` agreeing at the unique coordinate are equal. -/
theorem ext_of_apply {x y : Fin 1 → ℂ} (h : x 0 = y 0) : x = y := by
  funext i
  rw [Subsingleton.elim i 0]
  exact h

theorem apply_ne_zero_of_ne_zero {x : Fin 1 → ℂ} (hx : x ≠ 0) : x 0 ≠ 0 := by
  intro h
  exact hx (ext_of_apply (by simpa using h))

/-- Every vector is a complex multiple of a fixed nonzero vector. -/
theorem eq_smul (x : Fin 1 → ℂ) (hx : x 0 ≠ 0) (z : Fin 1 → ℂ) : z = (z 0 / x 0) • x := by
  refine ext_of_apply ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

theorem smul_apply_zero (w : ℂ) (x : Fin 1 → ℂ) : (w • x) 0 = w * x 0 := rfl

/-- A submodule containing a nonzero vector is everything. -/
theorem submodule_eq_top {W : Submodule ℂ (Fin 1 → ℂ)} {v : Fin 1 → ℂ} (hv : v ∈ W)
    (hv0 : v 0 ≠ 0) : W = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  rw [eq_smul v hv0 z]
  exact W.smul_mem _ hv

/-- A subgroup containing two `ℝ`-independent vectors has compact quotient: the unit box of the
two vectors is a compact fundamental set. -/
theorem compactSpace_quotient_of_lattice {P : AddSubgroup (Fin 1 → ℂ)} {x y : Fin 1 → ℂ}
    (hx : x ∈ P) (hy : y ∈ P) (hx0 : x 0 ≠ 0) (him : (y 0 / x 0).im ≠ 0) :
    CompactSpace ((Fin 1 → ℂ) ⧸ P) := by
  set c : ℂ := y 0 / x 0 with hc
  have hcx : c • x = y := ext_of_apply (by rw [smul_apply_zero, hc]; field_simp)
  set K : Set (Fin 1 → ℂ) :=
    (fun p : ℝ × ℝ => (p.1 : ℂ) • x + (p.2 : ℂ) • y) '' (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    with hK
  have hKcompact : IsCompact K := by
    refine (isCompact_Icc.prod isCompact_Icc).image ?_
    fun_prop
  have himg : (QuotientAddGroup.mk '' K) = (Set.univ : Set ((Fin 1 → ℂ) ⧸ P)) := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    set w : ℂ := z 0 / x 0 with hw
    set β : ℝ := w.im / c.im with hβ
    set α : ℝ := w.re - β * c.re with hα
    have hsum : ((α : ℂ) + (β : ℂ) * c) = w := by
      apply Complex.ext
      · simp [hα, Complex.add_re, Complex.mul_re]
      · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        rw [hβ]
        field_simp
        ring
    have hz : z = (α : ℂ) • x + (β : ℂ) • y := by
      have h1 : z = w • x := eq_smul x hx0 z
      rw [h1, ← hsum, add_smul, mul_smul, hcx]
    set m : ℤ := ⌊α⌋ with hm
    set n : ℤ := ⌊β⌋ with hn
    set g : Fin 1 → ℂ := (m : ℤ) • x + (n : ℤ) • y with hg
    have hgP : g ∈ P := P.add_mem (P.zsmul_mem hx m) (P.zsmul_mem hy n)
    have hmx : ((m : ℤ) • x) = ((m : ℝ) : ℂ) • x := by
      rw [← Int.cast_smul_eq_zsmul ℂ m x]; norm_cast
    have hny : ((n : ℤ) • y) = ((n : ℝ) : ℂ) • y := by
      rw [← Int.cast_smul_eq_zsmul ℂ n y]; norm_cast
    have hdiff : z - g = ((Int.fract α : ℝ) : ℂ) • x + ((Int.fract β : ℝ) : ℂ) • y := by
      rw [hz, hg, hmx, hny]
      have h1 : ((Int.fract α : ℝ) : ℂ) = (α : ℂ) - ((m : ℝ) : ℂ) := by
        rw [Int.fract]; push_cast [hm]; ring
      have h2 : ((Int.fract β : ℝ) : ℂ) = (β : ℂ) - ((n : ℝ) : ℂ) := by
        rw [Int.fract]; push_cast [hn]; ring
      rw [h1, h2, sub_smul, sub_smul]
      abel
    refine ⟨z - g, ⟨(Int.fract α, Int.fract β), ⟨⟨(Int.fract_nonneg α), (Int.fract_lt_one α).le⟩,
      ⟨(Int.fract_nonneg β), (Int.fract_lt_one β).le⟩⟩, hdiff.symm⟩, ?_⟩
    refine QuotientAddGroup.eq.mpr ?_
    have : -(z - g) + z = g := by abel
    rw [this]
    exact hgP
  refine ⟨?_⟩
  rw [← himg]
  exact hKcompact.image continuous_quot_mk

/-- **An escape subgroup in complex dimension one has `ℚ`-rank at most one.**  Two `ℝ`-independent
members would generate a full lattice and make the quotient compact; an irrational real ratio would
put a whole real line inside the closed subgroup, forcing the identity component — a complex
subspace — to be everything, and the quotient to be a point. -/
theorem exists_rat_relation_of_isEscapeSubgroup {P : AddSubgroup (Fin 1 → ℂ)}
    (hP : IsEscapeSubgroup P) {x y : Fin 1 → ℂ} (hx : x ∈ P) (hy : y ∈ P) :
    ∃ p q : ℚ, (p ≠ 0 ∨ q ≠ 0) ∧ p • x + q • y = 0 := by
  by_cases hx0 : x = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hx0]; simp⟩
  have hx0' : x 0 ≠ 0 := apply_ne_zero_of_ne_zero hx0
  set c : ℂ := y 0 / x 0 with hc
  have hcx : c • x = y := ext_of_apply (by rw [smul_apply_zero, hc]; field_simp)
  by_cases him : c.im = 0
  swap
  · exact absurd (compactSpace_quotient_of_lattice hx hy hx0' him) hP.noncompactQuotient
  have hcre : ((c.re : ℝ) : ℂ) = c := by
    apply Complex.ext <;> simp [him]
  by_cases hrat : ∃ t : ℚ, ((t : ℝ)) = c.re
  · obtain ⟨t, ht⟩ := hrat
    refine ⟨-t, 1, Or.inr one_ne_zero, ?_⟩
    have hct : ((t : ℚ) : ℂ) = c := by
      rw [← hcre, ← ht]; norm_cast
    refine ext_of_apply ?_
    simp only [Pi.add_apply, Pi.smul_apply, Rat.smul_def, Pi.zero_apply]
    rw [Rat.cast_neg, hct, Rat.cast_one, one_mul]
    have : y 0 = c * x 0 := by rw [← smul_apply_zero c x, hcx]
    rw [this]; ring
  have hrat' : ∀ t : ℚ, ((t : ℝ)) ≠ c.re := fun t ht => hrat ⟨t, ht⟩
  -- the ratio is irrational, so the real multiples of `x` in `P` form a dense closed subgroup
  refine absurd ?_ hP.noncompactQuotient
  set T : AddSubgroup ℝ :=
    { carrier := {t : ℝ | ((t : ℂ) • x) ∈ P}
      zero_mem' := by simp
      add_mem' := by
        intro s t hs ht
        have hst : (((s + t : ℝ)) : ℂ) • x = ((s : ℂ) • x) + ((t : ℂ) • x) := by
          push_cast; rw [add_smul]
        show (((s + t : ℝ)) : ℂ) • x ∈ P
        rw [hst]
        exact P.add_mem hs ht
      neg_mem' := by
        intro t ht
        have hnt : (((-t : ℝ)) : ℂ) • x = -((t : ℂ) • x) := by push_cast; rw [neg_smul]
        show (((-t : ℝ)) : ℂ) • x ∈ P
        rw [hnt]
        exact P.neg_mem ht } with hT
  have hTclosed : IsClosed ((T : Set ℝ)) := by
    have : (T : Set ℝ) = (fun t : ℝ => (t : ℂ) • x) ⁻¹' (P : Set (Fin 1 → ℂ)) := rfl
    rw [this]
    exact hP.isClosed.preimage (Complex.continuous_ofReal.smul continuous_const)
  have hone : (1 : ℝ) ∈ T := by
    show ((1 : ℝ) : ℂ) • x ∈ P
    simpa using hx
  have hcT : c.re ∈ T := by
    show ((c.re : ℝ) : ℂ) • x ∈ P
    rw [hcre, hcx]
    exact hy
  have hdense : Dense ((T : Set ℝ)) := by
    rcases AddSubgroup.dense_or_cyclic T with h | ⟨a, ha⟩
    · exact h
    · exfalso
      rw [ha] at hone hcT
      obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_singleton.mp hone
      obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hcT
      have ha0 : a ≠ 0 := by
        intro h; rw [h] at hm; simp at hm
      have hm0 : (m : ℝ) ≠ 0 := by
        intro h
        rw [zsmul_eq_mul, h, zero_mul] at hm
        exact one_ne_zero hm.symm
      have hmz : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
      refine hrat' ((n : ℚ) / (m : ℚ)) ?_
      rw [zsmul_eq_mul] at hm hn
      have : a = 1 / (m : ℝ) := by field_simp at hm ⊢; linarith [hm]
      rw [this] at hn
      rw [← hn]
      push_cast
      field_simp
  have hTtop : ∀ t : ℝ, ((t : ℂ) • x) ∈ P := by
    intro t
    have : (T : Set ℝ) = Set.univ := by
      rw [← hTclosed.closure_eq, hdense.closure_eq]
    have ht : t ∈ (T : Set ℝ) := by rw [this]; trivial
    exact ht
  have hray := subset_idComponentSet (P := P) (fun t : ℝ => ((t : ℂ) • x)) hTtop
    (Complex.continuous_ofReal.smul continuous_const) (t₀ := (0 : ℝ)) (by simp)
  obtain ⟨W, hW⟩ := hP.linearIdComponent
  have hxW : x ∈ W := by
    have : x ∈ idComponentSet P := hray ⟨1, by simp⟩
    rw [← hW] at this
    exact this
  have hWtop : W = ⊤ := submodule_eq_top hxW hx0'
  have hPtop : ∀ z : Fin 1 → ℂ, z ∈ P := by
    intro z
    have : z ∈ idComponentSet P := by
      rw [← hW, hWtop]; trivial
    exact idComponentSet_subset P this
  have hsub : (Set.univ : Set ((Fin 1 → ℂ) ⧸ P)).Subsingleton := by
    intro a _ b _
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective b
    exact QuotientAddGroup.eq.mpr (hPtop _)
  exact ⟨hsub.isCompact⟩

end DimOne

end GaloisForLFunctions
