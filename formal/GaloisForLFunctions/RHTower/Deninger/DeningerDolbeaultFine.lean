import GaloisForLFunctions.RHTower.Deninger.DeningerDolbeaultSheaf

/-!
# The sheaves of smooth forms are fine

Multiplying a smooth form by a smooth real function gives a smooth form, so the sheaves of the
Dolbeault resolution are modules over the smooth functions on the domain.  The multipliers have to
be the smooth ones rather than all continuous ones — a smooth form times a continuous bump is not
smooth — which is why the fine structure is parametrized by a subgroup of the continuous functions.

* `RHTower.DeningerSmoothMult` : the smooth real functions on the domain.
* `RHTower.deningerFormFineAction` : the sheaf of smooth `(0,q)`-forms is fine over them.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat Complex HTGeometry

variable {n : ℕ}

section Multipliers

variable {Ω : Opens (Fin n → ℂ)}

open Classical in
/-- A real function on the domain, extended by zero to all of `ℂ^n`. -/
noncomputable def deningerExtendFun (ρ : ↥(deningerSpace Ω) → ℝ) : (Fin n → ℂ) → ℝ :=
  fun z => if h : z ∈ (Ω : Set (Fin n → ℂ)) then ρ ⟨z, h⟩ else 0

theorem deningerExtendFun_apply (ρ : ↥(deningerSpace Ω) → ℝ)
    (x : ↥(deningerSpace Ω)) : deningerExtendFun ρ (x.1 : Fin n → ℂ) = ρ x := by
  have hx : (x.1 : Fin n → ℂ) ∈ (Ω : Set (Fin n → ℂ)) := x.2
  simp only [deningerExtendFun, dif_pos hx]

theorem deningerExtendFun_add (ρ σ : ↥(deningerSpace Ω) → ℝ) (z : Fin n → ℂ) :
    deningerExtendFun (fun x => ρ x + σ x) z
      = deningerExtendFun ρ z + deningerExtendFun σ z := by
  by_cases h : z ∈ (Ω : Set (Fin n → ℂ))
  · simp only [deningerExtendFun, dif_pos h]
  · simp only [deningerExtendFun, dif_neg h, add_zero]

theorem deningerExtendFun_neg (ρ : ↥(deningerSpace Ω) → ℝ) (z : Fin n → ℂ) :
    deningerExtendFun (fun x => -ρ x) z = -deningerExtendFun ρ z := by
  by_cases h : z ∈ (Ω : Set (Fin n → ℂ))
  · simp only [deningerExtendFun, dif_pos h]
  · simp only [deningerExtendFun, dif_neg h, neg_zero]

/-- The smooth real functions on the domain: those whose extension by zero agrees, near every point
of the domain, with a globally smooth function on `ℂ^n`. -/
def DeningerSmoothMult (Ω : Opens (Fin n → ℂ)) : AddSubgroup C(deningerSpace Ω, ℝ) where
  carrier := {ρ | ∀ x : ↥(deningerSpace Ω), ∃ g : (Fin n → ℂ) → ℝ,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ᶠ z in nhds (x.1 : Fin n → ℂ), deningerExtendFun (fun y => ρ y) z = g z}
  zero_mem' := by
    intro x
    refine ⟨fun _ => 0, contDiff_const, ?_⟩
    filter_upwards with z
    show deningerExtendFun (fun y => (0 : C(deningerSpace Ω, ℝ)) y) z = 0
    by_cases h : z ∈ (Ω : Set (Fin n → ℂ))
    · simp only [deningerExtendFun, dif_pos h]
      rfl
    · simp only [deningerExtendFun, dif_neg h]
  add_mem' := by
    intro a b ha hb x
    obtain ⟨g, hg, hgeq⟩ := ha x
    obtain ⟨h, hh, hheq⟩ := hb x
    refine ⟨fun z => g z + h z, hg.add hh, ?_⟩
    filter_upwards [hgeq, hheq] with z hz1 hz2
    show deningerExtendFun (fun y => (a + b) y) z = _
    rw [show (fun y => (a + b) y) = (fun y => a y + b y) from rfl,
      deningerExtendFun_add (fun y => a y) (fun y => b y) z, hz1, hz2]
  neg_mem' := by
    intro a ha x
    obtain ⟨g, hg, hgeq⟩ := ha x
    refine ⟨fun z => -g z, hg.neg, ?_⟩
    filter_upwards [hgeq] with z hz
    show deningerExtendFun (fun y => (-a) y) z = _
    rw [show (fun y => (-a) y) = (fun y => -a y) from rfl,
      deningerExtendFun_neg (fun y => a y) z, hz]

theorem deningerSmoothMult_one_mem :
    (1 : C(deningerSpace Ω, ℝ)) ∈ DeningerSmoothMult Ω := by
  intro x
  refine ⟨fun _ => 1, contDiff_const, ?_⟩
  filter_upwards [Ω.2.mem_nhds x.2] with z hz
  have hz' : z ∈ (Ω : Set (Fin n → ℂ)) := hz
  show deningerExtendFun (fun y => (1 : C(deningerSpace Ω, ℝ)) y) z = 1
  simp only [deningerExtendFun, dif_pos hz']
  rfl

theorem deningerSmoothMult_mem_apply {ρ : ↥(DeningerSmoothMult Ω)}
    (x : ↥(deningerSpace Ω)) : ∃ g : (Fin n → ℂ) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ᶠ z in nhds (x.1 : Fin n → ℂ),
        deningerExtendFun (fun y => (ρ : C(deningerSpace Ω, ℝ)) y) z = g z := ρ.2 x

end Multipliers

section FineAction

variable {Ω : Opens (Fin n → ℂ)}

/-- Multiplication of a form by a smooth function. -/
noncomputable def deningerFormSmul (ρ : ↥(DeningerSmoothMult Ω))
    {U : Opens (deningerSpace Ω)} (f : ↥U → DeningerFormVal n) : ↥U → DeningerFormVal n :=
  fun y S => (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * f y S

theorem deningerFormSmul_pred {q : ℕ} (ρ : ↥(DeningerSmoothMult Ω))
    {U : Opens (deningerSpace Ω)} {f : ↥U → DeningerFormVal n} (hf : DeningerFormPred q f) :
    DeningerFormPred q (deningerFormSmul ρ f) := by
  refine ⟨fun y S hS => ?_, fun y => ?_⟩
  · show (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * f y S = 0
    rw [hf.1 y S hS, mul_zero]
  · obtain ⟨a, ha, had, haeq⟩ := hf.2 y
    obtain ⟨g, hg, hgeq⟩ := deningerSmoothMult_mem_apply (ρ := ρ) y.1
    refine ⟨fun S z => ((g z : ℝ) : ℂ) * a S z, ?_, ?_, ?_⟩
    · intro S
      exact (Complex.ofRealCLM.contDiff.comp hg).mul (ha S)
    · intro S hS z
      show ((g z : ℝ) : ℂ) * a S z = 0
      rw [had S hS z, mul_zero]
    · have hmem : (y.1.1 : Fin n → ℂ) ∈ deningerAmb U := deningerAmb_mem_of_mem y
      filter_upwards [haeq, hgeq, (deningerAmb U).2.mem_nhds hmem] with z hza hzg hzU
      intro S
      rw [deningerExtend_of_mem _ hzU]
      show (((ρ : C(deningerSpace Ω, ℝ)) (deningerPt hzU).1 : ℝ) : ℂ) * f (deningerPt hzU) S = _
      have hfz : f (deningerPt hzU) S = deningerExtend f z S :=
        (congrFun (deningerExtend_of_mem f hzU) S).symm
      have hρz : ((ρ : C(deningerSpace Ω, ℝ)) (deningerPt hzU).1 : ℝ)
          = deningerExtendFun (fun w => (ρ : C(deningerSpace Ω, ℝ)) w) z :=
        (deningerExtendFun_apply _ (deningerPt hzU).1).symm
      rw [hfz, hρz, hza S, hzg]

/-- **The sheaf of smooth `(0,q)`-forms is fine over the smooth functions.** -/
noncomputable def deningerFormFineAction (Ω : Opens (Fin n → ℂ)) (q : ℕ) :
    DeningerFineAction (deningerFormSheaf Ω q) (DeningerSmoothMult Ω) where
  one_mem := deningerSmoothMult_one_mem
  smul ρ U f := ⟨deningerFormSmul ρ f.1, deningerFormSmul_pred ρ f.2⟩
  smul_add ρ U s t := by
    refine Subtype.ext (funext fun y => funext fun S => ?_)
    show (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * (s.1 y S + t.1 y S)
      = (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * s.1 y S
        + (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * t.1 y S
    ring
  add_smul ρ σ U s := by
    refine Subtype.ext (funext fun y => funext fun S => ?_)
    show ((((ρ : C(deningerSpace Ω, ℝ)) y.1 + (σ : C(deningerSpace Ω, ℝ)) y.1 : ℝ)) : ℂ)
        * s.1 y S
      = (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * s.1 y S
        + (((σ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * s.1 y S
    push_cast
    ring
  one_smul U s := by
    refine Subtype.ext (funext fun y => funext fun S => ?_)
    show ((1 : ℝ) : ℂ) * s.1 y S = s.1 y S
    rw [Complex.ofReal_one, one_mul]
  smul_res := by
    intro ρ U V i s
    rfl
  smul_eq_zero ρ U s hρ := by
    refine Subtype.ext (funext fun y => funext fun S => ?_)
    show (((ρ : C(deningerSpace Ω, ℝ)) y.1 : ℝ) : ℂ) * s.1 y S = 0
    rw [hρ y.1 y.2, Complex.ofReal_zero, zero_mul]

end FineAction


section Partitions

variable {Ω : Opens (Fin n → ℂ)}

noncomputable instance : SigmaCompactSpace ↥(deningerSpace Ω) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-- Every open set of the domain contains a relatively compact open neighbourhood of each of its
points. -/
theorem deningerExists_relCompact {V : Opens ↥(deningerSpace Ω)} {x : ↥(deningerSpace Ω)}
    (hx : x ∈ V) : ∃ W : Opens ↥(deningerSpace Ω),
      x ∈ W ∧ W ≤ V ∧ IsCompact (closure (W : Set ↥(deningerSpace Ω))) := by
  obtain ⟨L, hLc, hxL, hLV⟩ :=
    exists_compact_between (isCompact_singleton (x := x)) V.2 (Set.singleton_subset_iff.2 hx)
  refine ⟨⟨interior L, isOpen_interior⟩, hxL rfl, fun z hz => hLV (interior_subset hz), ?_⟩
  refine hLc.of_isClosed_subset isClosed_closure ?_
  exact le_trans (closure_mono interior_subset) (le_of_eq hLc.isClosed.closure_eq)

/-- The extension by zero of a section of the domain, in the form used by the manifold library. -/
theorem deningerExtendFun_eq_extend (ρ : ↥(deningerSpace Ω) → ℝ) :
    deningerExtendFun ρ = Function.extend Subtype.val ρ 0 := by
  funext z
  by_cases h : z ∈ (Ω : Set (Fin n → ℂ))
  · have h1 : deningerExtendFun ρ z = ρ ⟨z, h⟩ := dif_pos h
    have h2 : Function.extend Subtype.val ρ 0 z = ρ ⟨z, h⟩ :=
      Subtype.val_injective.extend_apply ρ 0 ⟨z, h⟩
    rw [h1, h2]
  · have h1 : deningerExtendFun ρ z = 0 := dif_neg h
    have h2 : Function.extend Subtype.val ρ 0 z = 0 := by
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨y, rfl⟩
      exact h y.2
    rw [h1, h2]

/-- **The smooth functions on the domain admit partitions of unity.** -/
theorem deningerHasPartitions_smooth (Ω : Opens (Fin n → ℂ)) :
    DeningerHasPartitions (DeningerSmoothMult Ω) := by
  classical
  intro V hV
  choose W hxW hWV hWc using fun x : ↥(deningerSpace Ω) => deningerExists_relCompact (hV x)
  obtain ⟨f, hfsub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (I := modelWithCornersSelf ℝ (Fin n → ℂ)) (M := ↥(deningerSpace Ω))
    isClosed_univ (fun x => (W x : Set ↥(deningerSpace Ω))) (fun x => (W x).2)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxW y⟩)
  have hmem : ∀ i, (⟨f i, (f i).contMDiff.continuous⟩ : C(deningerSpace Ω, ℝ)) ∈ DeningerSmoothMult Ω := by
    intro i x
    have hcs : HasCompactSupport (f i) :=
      hWc i |>.of_isClosed_subset isClosed_closure (le_trans (hfsub i) subset_closure)
    have hsm : ContMDiff (modelWithCornersSelf ℝ (Fin n → ℂ)) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.extend Subtype.val (f i) 0) :=
      ContMDiff.extend_zero hcs (f i).contMDiff
    refine ⟨Function.extend Subtype.val (f i) 0, contMDiff_iff_contDiff.1 hsm, ?_⟩
    filter_upwards with z
    rw [deningerExtendFun_eq_extend]
    rfl
  refine ⟨fun i => ⟨⟨f i, (f i).contMDiff.continuous⟩, hmem i⟩, ?_, ?_, ?_⟩
  · intro i
    exact le_trans (hfsub i) (hWV i)
  · exact f.locallyFinite.closure
  · intro x
    exact f.sum_eq_one (Set.mem_univ x)

end Partitions


section GlobalPlane

/-- When the domain is the whole space, every ambient point lies in the ambient open set of `⊤`. -/
theorem deningerAmb_top_mem (z : Fin n → ℂ) :
    z ∈ deningerAmb (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ)))) :=
  ⟨⟨z, trivial⟩, trivial, rfl⟩

variable {q : ℕ}
  {h : ↥(⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ)))) → DeningerFormVal n}

/-- On the whole space a section is a globally smooth form. -/
theorem deningerFlip_smoothSetForm (hh : DeningerFormPred q h) :
    SmoothSetForm (deningerFlip (deningerExtend h)) := by
  intro S
  rw [contDiff_iff_contDiffAt]
  intro z
  obtain ⟨g, hg, hgd, hgeq⟩ := hh.2 (deningerPt (deningerAmb_top_mem z))
  refine ContDiffAt.congr_of_eventuallyEq (hg S).contDiffAt ?_
  filter_upwards [hgeq] with y hy
  exact hy S

/-- On the whole space a section of degree `q` gives a form of degree `q`. -/
theorem deningerFlip_setFormDeg (hh : DeningerFormPred q h) :
    SetFormDeg q (deningerFlip (deningerExtend h)) := by
  intro S hS z
  show deningerExtend h z S = 0
  rw [deningerExtend_of_mem h (deningerAmb_top_mem z)]
  exact hh.1 _ S hS

/-- **The Dolbeault differential is surjective on global sections over `ℂ^n`.** -/
theorem deningerFormDbar_globalSurjective (q : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      ((deningerFormDbar (⊤ : Opens (Fin n → ℂ)) q).1.app
        (op (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))))) := by
  intro hsec
  have hC : SmoothSetForm (deningerFlip (deningerExtend hsec.1)) :=
    deningerFlip_smoothSetForm hsec.2.1
  have hd : SetFormDeg (q + 1) (deningerFlip (deningerExtend hsec.1)) :=
    deningerFlip_setFormDeg hsec.2.1
  have hcl : ∀ (S : Finset (Fin n)) (z : Fin n → ℂ),
      setDbar (deningerFlip (deningerExtend hsec.1)) S z = 0 := by
    intro S z
    have := hsec.2.2 (deningerPt (deningerAmb_top_mem z)) S
    rwa [deningerPt_val (deningerAmb_top_mem z)] at this
  obtain ⟨u, hCu, hud, hu⟩ := setDbar_exact_global hC hd hcl
  refine ⟨⟨fun y => fun S => u S (y.1.1 : Fin n → ℂ),
    ⟨fun y S hS => hud S hS _, fun y => ⟨u, hCu, hud, ?_⟩⟩⟩, ?_⟩
  · filter_upwards [(deningerAmb
      (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))).2.mem_nhds
        (deningerAmb_mem_of_mem y)] with z hz
    intro S
    rw [deningerExtend_of_mem _ hz]
    rfl
  · refine Subtype.ext (funext fun y => funext fun S => ?_)
    have hmodel : ∀ᶠ z in nhds ((y.1.1 : Fin n → ℂ)), ∀ S,
        deningerExtend (fun w : ↥(⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ)))) =>
          fun S => u S (w.1.1 : Fin n → ℂ)) z S = u S z := by
      filter_upwards [(deningerAmb
        (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))).2.mem_nhds
          (deningerAmb_mem_of_mem y)] with z hz
      intro S
      rw [deningerExtend_of_mem _ hz]
      rfl
    show setDbar (deningerFlip (deningerExtend
      (fun w : ↥(⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ)))) =>
        fun S => u S (w.1.1 : Fin n → ℂ)))) S (y.1.1 : Fin n → ℂ) = _
    rw [deningerSetDbar_model hmodel S, hu S (y.1.1 : Fin n → ℂ)]
    show deningerExtend hsec.1 (y.1.1 : Fin n → ℂ) S = hsec.1 y S
    rw [deningerExtend_of_mem hsec.1 (deningerAmb_mem_of_mem y)]
    exact congrArg (fun w => hsec.1 w S) (deningerPt_eq y)

end GlobalPlane


section CartanB

open CategoryTheory.Abelian

universe w

variable [CategoryTheory.HasExt.{w}
  (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (⊤ : Opens (Fin n → ℂ))))]

/-- **Cartan's theorem B for `ℂ^n`.**  The sheaf of holomorphic functions — the closed smooth forms
of degree zero — has no higher cohomology.  The Dolbeault resolution is short exact, its terms are
fine hence acyclic, and its sections surject because the `∂̄` equation is globally solvable. -/
theorem deningerHolomorphic_ext_eq_zero (q : ℕ)
    (x : deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))
      (deningerClosedFormSheaf (⊤ : Opens (Fin n → ℂ)) 0) (q + 1)) : x = 0 :=
  deningerResolution_ext_eq_zero
    (K := fun i => deningerClosedFormSheaf (⊤ : Opens (Fin n → ℂ)) i)
    (A := fun i => deningerFormSheaf (⊤ : Opens (Fin n → ℂ)) i)
    (ι := fun i => deningerFormIncl (⊤ : Opens (Fin n → ℂ)) i)
    (π := fun i => deningerFormDbar (⊤ : Opens (Fin n → ℂ)) i)
    (hzero := fun i => deningerFormIncl_comp_dbar (⊤ : Opens (Fin n → ℂ)) i)
    (fun i => deningerFormStep_shortExact (⊤ : Opens (Fin n → ℂ)) i) ⊤
    (fun i => deningerFine_acyclicOn (deningerHasPartitions_smooth (⊤ : Opens (Fin n → ℂ)))
      (deningerFormFineAction (⊤ : Opens (Fin n → ℂ)) i))
    (fun i => deningerFormDbar_globalSurjective i) q 0 x

/-- **The higher cohomology of the structure sheaf of `ℂ^n` is a subsingleton.** -/
theorem deningerHolomorphic_subsingleton_cohomology (q : ℕ) :
    Subsingleton (deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (⊤ : Opens (Fin n → ℂ))))
      (deningerClosedFormSheaf (⊤ : Opens (Fin n → ℂ)) 0) (q + 1)) :=
  ⟨fun a b => by
    rw [deningerHolomorphic_ext_eq_zero q a, deningerHolomorphic_ext_eq_zero q b]⟩

end CartanB


section Punctured

/-- The punctured space as an open set of `ℂ^n`. -/
def deningerPunctured (n : ℕ) : Opens (Fin n → ℂ) :=
  ⟨puncturedSpace n, isOpen_puncturedSpace⟩

theorem deningerAmb_top_punctured {z : Fin n → ℂ} (hz : z ∈ puncturedSpace n) :
    z ∈ deningerAmb (⊤ : Opens (deningerSpace (deningerPunctured n))) :=
  ⟨⟨z, hz⟩, trivial, rfl⟩

theorem deningerAmb_top_punctured_subset {z : Fin n → ℂ}
    (hz : z ∈ deningerAmb (⊤ : Opens (deningerSpace (deningerPunctured n)))) :
    z ∈ puncturedSpace n := by
  obtain ⟨y, -, rfl⟩ := hz
  exact y.2

variable {q : ℕ}
  {h : ↥(⊤ : Opens (deningerSpace (deningerPunctured n))) → DeningerFormVal n}

theorem deningerFlip_smoothOn_punctured (hh : DeningerFormPred q h) :
    SmoothSetFormOn (deningerFlip (deningerExtend h)) (puncturedSpace n) := by
  intro S z hz
  obtain ⟨g, hg, hgd, hgeq⟩ := hh.2 (deningerPt (deningerAmb_top_punctured hz))
  refine ContDiffAt.congr_of_eventuallyEq (hg S).contDiffAt ?_
  filter_upwards [hgeq] with y hy
  exact hy S

theorem deningerFlip_setFormDeg_punctured (hh : DeningerFormPred q h) :
    SetFormDeg q (deningerFlip (deningerExtend h)) := by
  intro S hS z
  show deningerExtend h z S = 0
  by_cases hz : z ∈ deningerAmb (⊤ : Opens (deningerSpace (deningerPunctured n)))
  · rw [deningerExtend_of_mem h hz]
    exact hh.1 _ S hS
  · rw [deningerExtend, dif_neg hz]
    rfl

/-- **The Dolbeault differential is surjective on global sections over `(ℂ^×)^n`.** -/
theorem deningerFormDbar_globalSurjective_punctured (q : ℕ) :
    Function.Surjective (ConcreteCategory.hom
      ((deningerFormDbar (deningerPunctured n) q).1.app
        (op (⊤ : Opens (deningerSpace (deningerPunctured n)))))) := by
  intro hsec
  have hC : SmoothSetFormOn (deningerFlip (deningerExtend hsec.1)) (puncturedSpace n) :=
    deningerFlip_smoothOn_punctured hsec.2.1
  have hd : SetFormDeg (q + 1) (deningerFlip (deningerExtend hsec.1)) :=
    deningerFlip_setFormDeg_punctured hsec.2.1
  have hcl : ∀ (S : Finset (Fin n)), ∀ z ∈ puncturedSpace n,
      setDbar (deningerFlip (deningerExtend hsec.1)) S z = 0 := by
    intro S z hz
    have := hsec.2.2 (deningerPt (deningerAmb_top_punctured hz)) S
    rwa [deningerPt_val (deningerAmb_top_punctured hz)] at this
  obtain ⟨u, hCu, hud, hu⟩ := setDbar_exact_punctured hC hd hcl
  set sect : ↥(⊤ : Opens (deningerSpace (deningerPunctured n))) → DeningerFormVal n :=
    fun y => fun S => u S (y.1.1 : Fin n → ℂ) with hsect
  -- a global smooth model of the primitive near each point
  have hmodel : ∀ y : ↥(⊤ : Opens (deningerSpace (deningerPunctured n))),
      ∃ G : SetForm n, SmoothSetForm G ∧ SetFormDeg q G ∧
        ∃ V : Set (Fin n → ℂ), IsOpen V ∧ (y.1.1 : Fin n → ℂ) ∈ V ∧
          ∀ S, ∀ z ∈ V, G S z = u S z := by
    intro y
    have hy : (y.1.1 : Fin n → ℂ) ∈ puncturedSpace n := y.1.2
    obtain ⟨G, V, hVopen, hKV, hCG, hGeq, hGzero⟩ :=
      exists_contDiff_family_eqOn (h := u) (K := {(y.1.1 : Fin n → ℂ)})
        (W := puncturedSpace n) isCompact_singleton isOpen_puncturedSpace
        (Set.singleton_subset_iff.2 hy) hCu
    exact ⟨G, hCG, fun S hS z => hGzero S z (hud S hS z), V, hVopen, hKV rfl, hGeq⟩
  refine ⟨⟨sect, ⟨fun y S hS => hud S hS _, fun y => ?_⟩⟩, ?_⟩
  · obtain ⟨G, hCG, hGd, V, hVopen, hyV, hGeq⟩ := hmodel y
    refine ⟨G, hCG, hGd, ?_⟩
    filter_upwards [(hVopen.inter (deningerAmb
      (⊤ : Opens (deningerSpace (deningerPunctured n)))).2).mem_nhds
        ⟨hyV, deningerAmb_mem_of_mem y⟩] with z hz
    intro S
    rw [deningerExtend_of_mem _ hz.2, hGeq S z hz.1]
    rfl
  · refine Subtype.ext (funext fun y => funext fun S => ?_)
    obtain ⟨G, hCG, hGd, V, hVopen, hyV, hGeq⟩ := hmodel y
    have hmod : ∀ᶠ z in nhds ((y.1.1 : Fin n → ℂ)), ∀ S,
        deningerExtend sect z S = G S z := by
      filter_upwards [(hVopen.inter (deningerAmb
        (⊤ : Opens (deningerSpace (deningerPunctured n)))).2).mem_nhds
          ⟨hyV, deningerAmb_mem_of_mem y⟩] with z hz
      intro T
      rw [deningerExtend_of_mem _ hz.2, hGeq T z hz.1]
      rfl
    show setDbar (deningerFlip (deningerExtend sect)) S (y.1.1 : Fin n → ℂ) = _
    rw [deningerSetDbar_model hmod S]
    have hGu : setDbar G S (y.1.1 : Fin n → ℂ) = setDbar u S (y.1.1 : Fin n → ℂ) :=
      setDbar_congr_on_isOpen hVopen (fun T z hz => hGeq T z hz) hyV S
    rw [hGu, hu S (y.1.1 : Fin n → ℂ) y.1.2]
    show deningerExtend hsec.1 (y.1.1 : Fin n → ℂ) S = hsec.1 y S
    rw [deningerExtend_of_mem hsec.1 (deningerAmb_mem_of_mem y)]
    exact congrArg (fun w => hsec.1 w S) (deningerPt_eq y)

end Punctured

section CartanBPunctured

open CategoryTheory.Abelian

universe w

/-- **Cartan's theorem B for `(ℂ^×)^n`.**  The sheaf of holomorphic functions on the punctured
space has no higher cohomology. -/
theorem deningerHolomorphic_ext_eq_zero_punctured
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))] (q : ℕ)
    (x : deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (deningerPunctured n)))
      (deningerClosedFormSheaf (deningerPunctured n) 0) (q + 1)) : x = 0 :=
  deningerResolution_ext_eq_zero
    (K := fun i => deningerClosedFormSheaf (deningerPunctured n) i)
    (A := fun i => deningerFormSheaf (deningerPunctured n) i)
    (ι := fun i => deningerFormIncl (deningerPunctured n) i)
    (π := fun i => deningerFormDbar (deningerPunctured n) i)
    (hzero := fun i => deningerFormIncl_comp_dbar (deningerPunctured n) i)
    (fun i => deningerFormStep_shortExact (deningerPunctured n) i) ⊤
    (fun i => deningerFine_acyclicOn (deningerHasPartitions_smooth (deningerPunctured n))
      (deningerFormFineAction (deningerPunctured n) i))
    (fun i => deningerFormDbar_globalSurjective_punctured i) q 0 x

/-- **The higher cohomology of the structure sheaf of `(ℂ^×)^n` is a subsingleton.** -/
theorem deningerHolomorphic_subsingleton_cohomology_punctured
    [CategoryTheory.HasExt.{w}
      (TopCat.Sheaf AddCommGrpCat.{0} (deningerSpace (deningerPunctured n)))] (q : ℕ) :
    Subsingleton (deningerSheafCohomology.{w}
      (⊤ : Opens (deningerSpace (deningerPunctured n)))
      (deningerClosedFormSheaf (deningerPunctured n) 0) (q + 1)) :=
  ⟨fun a b => by
    rw [deningerHolomorphic_ext_eq_zero_punctured q a,
      deningerHolomorphic_ext_eq_zero_punctured q b]⟩

end CartanBPunctured

end RHTower
