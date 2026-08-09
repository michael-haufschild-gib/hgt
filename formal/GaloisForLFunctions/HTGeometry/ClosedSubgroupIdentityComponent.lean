import GaloisForLFunctions.HTGeometry.EscapeSubgroup

/-!
# The identity component of a closed subgroup of a finite-dimensional real vector space

A closed additive subgroup `P` of a finite-dimensional real normed space contains a largest real
subspace, namely the set of vectors all of whose real multiples lie in `P`, and that subspace is
exactly the identity component of `P`.

* `lineSubmodule P` — the vectors whose whole real line lies in `P`;
* **`exists_line_of_not_discrete`** — a closed subgroup with arbitrarily small nonzero elements
  contains a whole real line: normalize a null sequence to the unit sphere, take a convergent
  subsequence by compactness, and approximate an arbitrary real multiple by integer multiples;
* **`idComponentSet_eq_lineSubmodule`** — hence, splitting off a linear complement, the subgroup is
  discrete transverse to `lineSubmodule P`, so that subspace is clopen in `P` and is its identity
  component.
-/

open Set Topology Metric Filter

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The largest real subspace contained in an additive subgroup. -/
def lineSubmodule (P : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ P}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact P.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    simp
  smul_mem' := by
    intro c v hv t
    rw [smul_smul]
    exact hv (t * c)

theorem mem_lineSubmodule {P : AddSubgroup E} {v : E} :
    v ∈ lineSubmodule P ↔ ∀ t : ℝ, t • v ∈ P := Iff.rfl

theorem lineSubmodule_subset (P : AddSubgroup E) :
    ((lineSubmodule P : Submodule ℝ E) : Set E) ⊆ (P : Set E) := by
  intro v hv
  simpa using (mem_lineSubmodule.mp hv) 1

/-! ## A closed subgroup that is not discrete contains a line -/

variable [FiniteDimensional ℝ E]

/-- **A closed subgroup with arbitrarily small nonzero elements contains a real line.**  Normalize
a null sequence of nonzero members to the unit sphere; compactness gives a limiting direction, and
integer multiples of the small members approximate every real multiple of it. -/
theorem exists_line_of_not_discrete {P : AddSubgroup E} (hP : IsClosed (P : Set E))
    (h : ∀ ε : ℝ, 0 < ε → ∃ q ∈ P, q ≠ 0 ∧ ‖q‖ < ε) :
    ∃ u : E, u ≠ 0 ∧ ∀ t : ℝ, t • u ∈ P := by
  choose q hqP hq0 hqlt using fun n : ℕ => h (1 / (n + 1)) (by positivity)
  have hqnorm : ∀ n, 0 < ‖q n‖ := fun n => norm_pos_iff.mpr (hq0 n)
  set u : ℕ → E := fun n => ‖q n‖⁻¹ • q n with hu
  have husph : ∀ n, u n ∈ sphere (0 : E) 1 := by
    intro n
    simp only [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm]
    field_simp
    exact div_self (hqnorm n).ne'
  obtain ⟨a, ha, φ, hφ, htend⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq husph
  have hanorm : ‖a‖ = 1 := by simpa using ha
  refine ⟨a, fun h0 => by simp [h0] at hanorm, ?_⟩
  intro t
  -- the null sequence of scales
  have hqto : Tendsto (fun n => ‖q n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (hqnorm n).le) (fun n => (hqlt n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hqsub : Tendsto (fun n => ‖q (φ n)‖) atTop (𝓝 0) :=
    hqto.comp hφ.tendsto_atTop
  -- integer multiples of the small members
  set c : ℕ → ℝ := fun n => (⌊t / ‖q (φ n)‖⌋ : ℝ) * ‖q (φ n)‖ with hc
  have hcto : Tendsto c atTop (𝓝 t) := by
    have hbound : ∀ n, |c n - t| ≤ ‖q (φ n)‖ := by
      intro n
      have hpos := hqnorm (φ n)
      have hfl := Int.sub_one_lt_floor (t / ‖q (φ n)‖)
      have hfl' := Int.floor_le (t / ‖q (φ n)‖)
      rw [hc]
      rw [abs_le]
      constructor
      · have : (t / ‖q (φ n)‖ - 1) * ‖q (φ n)‖ ≤ (⌊t / ‖q (φ n)‖⌋ : ℝ) * ‖q (φ n)‖ :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
        have hid : (t / ‖q (φ n)‖ - 1) * ‖q (φ n)‖ = t - ‖q (φ n)‖ := by
          field_simp
        linarith [hid ▸ this]
      · have : (⌊t / ‖q (φ n)‖⌋ : ℝ) * ‖q (φ n)‖ ≤ (t / ‖q (φ n)‖) * ‖q (φ n)‖ :=
          mul_le_mul_of_nonneg_right hfl' hpos.le
        have hid : (t / ‖q (φ n)‖) * ‖q (φ n)‖ = t := by field_simp
        linarith [hid ▸ this]
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun n => ?_) hqsub
    simpa [Real.norm_eq_abs] using hbound n
  have hsmul : Tendsto (fun n => c n • u (φ n)) atTop (𝓝 (t • a)) := hcto.smul htend
  refine hP.mem_of_tendsto hsmul ?_
  filter_upwards with n
  have hpos := hqnorm (φ n)
  have hrw : c n • u (φ n) = (⌊t / ‖q (φ n)‖⌋ : ℤ) • q (φ n) := by
    rw [hc, hu]
    simp only [smul_smul]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    field_simp
  rw [hrw]
  exact P.zsmul_mem (hqP (φ n)) _

/-! ## The identity component -/

/-- **The identity component of a closed subgroup is its largest real subspace.** -/
theorem idComponentSet_eq_lineSubmodule {P : AddSubgroup E} (hP : IsClosed (P : Set E)) :
    idComponentSet P = ((lineSubmodule P : Submodule ℝ E) : Set E) := by
  classical
  set V : Submodule ℝ E := lineSubmodule P with hV
  obtain ⟨W, hcompl⟩ := V.exists_isCompl
  -- the projection onto the complement
  set e : E ≃ₗ[ℝ] (V × W) := (Submodule.prodEquivOfIsCompl V W hcompl).symm with he
  set π : E →ₗ[ℝ] E :=
    W.subtype ∘ₗ (LinearMap.snd ℝ V W) ∘ₗ (e : E →ₗ[ℝ] (V × W)) with hπ
  have hsplit : ∀ z : E, ((e z).1 : E) + ((e z).2 : E) = z := by
    intro z
    have := (Submodule.prodEquivOfIsCompl V W hcompl).apply_symm_apply z
    simpa [he, Submodule.coe_prodEquivOfIsCompl] using this
  have hπmem : ∀ z : E, π z ∈ W := by
    intro z
    exact ((e z).2).2
  have hπsub : ∀ z : E, z - π z ∈ V := by
    intro z
    have h := hsplit z
    have : z - π z = ((e z).1 : E) := by
      rw [hπ]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
        Submodule.subtype_apply]
      linear_combination (norm := module) -h
    rw [this]
    exact ((e z).1).2
  have hπV : ∀ z : E, z ∈ V → π z = 0 := by
    intro z hz
    have hzz : z - π z ∈ V := hπsub z
    have hπz : π z ∈ V := by
      have : π z = z - (z - π z) := by abel
      rw [this]
      exact V.sub_mem hz hzz
    have : π z ∈ V ⊓ W := ⟨hπz, hπmem z⟩
    rw [hcompl.inf_eq_bot] at this
    simpa using this
  have hπcont : Continuous π := LinearMap.continuous_of_finiteDimensional π
  -- the transverse part of `P` is discrete
  set PW : AddSubgroup E := P ⊓ W.toAddSubgroup with hPW
  have hPWclosed : IsClosed ((PW : Set E)) := by
    have hWclosed : IsClosed ((W : Set E)) := W.closed_of_finiteDimensional
    have : ((PW : Set E)) = (P : Set E) ∩ (W : Set E) := rfl
    rw [this]
    exact hP.inter hWclosed
  have hdisc : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ PW, ‖q‖ < ε → q = 0 := by
    by_contra hcon
    have hsmall : ∀ ε : ℝ, 0 < ε → ∃ q ∈ PW, q ≠ 0 ∧ ‖q‖ < ε := by
      intro ε hε
      by_contra hno
      exact hcon ⟨ε, hε, fun q hq hqn => by
        by_contra h0
        exact hno ⟨q, hq, h0, hqn⟩⟩
    obtain ⟨u, hu0, hline⟩ := exists_line_of_not_discrete hPWclosed hsmall
    have huV : u ∈ V := mem_lineSubmodule.mpr fun t => (hline t).1
    have huW : u ∈ W := by simpa using (hline 1).2
    have : u ∈ V ⊓ W := ⟨huV, huW⟩
    rw [hcompl.inf_eq_bot] at this
    exact hu0 (by simpa using this)
  obtain ⟨ε, hε, hεzero⟩ := hdisc
  -- the subspace is clopen inside the subgroup
  set S : Set P := {p | (p : E) ∈ V} with hS
  have hSopen : IsOpen S := by
    have hpre : S = (fun p : P => (p : E)) ⁻¹' {z : E | ‖π z‖ < ε} := by
      ext p
      simp only [hS, Set.mem_setOf_eq, Set.mem_preimage]
      constructor
      · intro hp
        rw [hπV _ hp]
        simpa using hε
      · intro hp
        have hmem : π (p : E) ∈ PW := by
          refine ⟨?_, hπmem _⟩
          have hd : π (p : E) = (p : E) - ((p : E) - π (p : E)) := by abel
          rw [hd]
          exact P.sub_mem p.2 (lineSubmodule_subset P (hπsub (p : E)))
        have hz := hεzero _ hmem hp
        have : (p : E) - π (p : E) ∈ V := hπsub (p : E)
        rw [hz, sub_zero] at this
        exact this
    rw [hpre]
    exact (isOpen_lt (by fun_prop) continuous_const).preimage continuous_subtype_val
  have hSclosed : IsClosed S := by
    have hVclosed : IsClosed ((V : Set E)) := V.closed_of_finiteDimensional
    exact hVclosed.preimage continuous_subtype_val
  have hSconn : IsPreconnected S := by
    have himg : (fun p : P => (p : E)) '' S = (V : Set E) := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp
      · intro hz
        exact ⟨⟨z, lineSubmodule_subset P hz⟩, hz, rfl⟩
    have hind : Topology.IsInducing (fun p : P => (p : E)) := ⟨rfl⟩
    refine (IsInducing.isPreconnected_image hind).mp ?_
    rw [himg]
    exact (V.convex).isPreconnected
  have hzeroS : (0 : P) ∈ S := by
    simp only [hS, Set.mem_setOf_eq]
    exact V.zero_mem
  have hcomp : connectedComponent (0 : P) = S := by
    refine Set.Subset.antisymm ?_ (hSconn.subset_connectedComponent hzeroS)
    exact IsClopen.connectedComponent_subset ⟨hSclosed, hSopen⟩ hzeroS
  rw [idComponentSet, hcomp]
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hz
    exact ⟨⟨z, lineSubmodule_subset P hz⟩, hz, rfl⟩

/-! ## Complex-linear identity components -/

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The largest real subspace inside a subgroup, promoted to a complex subspace when it is stable
under multiplication by `i`. -/
def complexLineSubmodule (P : AddSubgroup E)
    (hI : ∀ v ∈ lineSubmodule P, (Complex.I : ℂ) • v ∈ lineSubmodule P) : Submodule ℂ E where
  carrier := ((lineSubmodule P : Submodule ℝ E) : Set E)
  add_mem' := fun ha hb => (lineSubmodule P).add_mem ha hb
  zero_mem' := (lineSubmodule P).zero_mem
  smul_mem' := by
    intro c v hv
    have hre : ∀ (r : ℝ) (w : E), (r : ℝ) • w = ((r : ℂ)) • w := by
      intro r w
      rw [← IsScalarTower.algebraMap_smul ℂ r w, Complex.coe_algebraMap]
    have hsplit : c • v = ((c.re : ℝ) • v) + ((c.im : ℝ) • ((Complex.I : ℂ) • v)) := by
      rw [hre c.re v, hre c.im _, smul_smul, ← add_smul]
      congr 1
      exact (Complex.re_add_im c).symm
    rw [hsplit]
    exact (lineSubmodule P).add_mem ((lineSubmodule P).smul_mem _ hv)
      ((lineSubmodule P).smul_mem _ (hI v hv))

omit [FiniteDimensional ℂ E] in
@[simp] theorem coe_complexLineSubmodule (P : AddSubgroup E)
    (hI : ∀ v ∈ lineSubmodule P, (Complex.I : ℂ) • v ∈ lineSubmodule P) :
    ((complexLineSubmodule P hI : Submodule ℂ E) : Set E)
      = ((lineSubmodule P : Submodule ℝ E) : Set E) := rfl

/-- **Escape-subgroup criterion.**  A closed subgroup whose maximal real subspace is stable under
multiplication by `i` and whose quotient is noncompact is an escape subgroup. -/
theorem isEscapeSubgroup_of_isClosed {P : AddSubgroup E} (hP : IsClosed (P : Set E))
    (hI : ∀ v ∈ lineSubmodule P, (Complex.I : ℂ) • v ∈ lineSubmodule P)
    (hnc : ¬ CompactSpace (E ⧸ P)) : IsEscapeSubgroup P where
  isClosed := hP
  linearIdComponent :=
    ⟨complexLineSubmodule P hI, by
      rw [coe_complexLineSubmodule]
      exact (idComponentSet_eq_lineSubmodule hP).symm⟩
  noncompactQuotient := hnc

end Complex

end GaloisForLFunctions
