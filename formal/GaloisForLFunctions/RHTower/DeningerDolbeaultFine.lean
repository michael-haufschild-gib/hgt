import GaloisForLFunctions.RHTower.DeningerDolbeaultSheaf

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
  exact congrArg ρ (Subtype.ext rfl)

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

end RHTower
