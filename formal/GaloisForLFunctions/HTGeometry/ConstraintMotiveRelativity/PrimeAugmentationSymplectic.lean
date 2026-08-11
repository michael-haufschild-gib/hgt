import Mathlib

/-!
# The algebraic prime augmentation port

On finitely supported prime coordinates `K₀ = P →₀ ℂ` the augmentation `ε x = ∑ x_p` has kernel
`I₀`.  In the algebraic cotangent double `K₀ ⊕ K₀*` with the canonical form
`ω((x,α),(y,β)) = α y - β x`, the subspace `I₀ ⊕ 0` is isotropic and its symplectic orthogonal is
`K₀ ⊕ ℂ ε`: a covector annihilates `I₀` exactly when it takes the same value on all coordinate
vectors, since every difference `e_p - e_q` lies in `I₀`.

The reduction `(x, a ε) ↦ (ε x, a)` therefore identifies the coisotropic quotient with `ℂ × ℂ`
carrying the hyperbolic form.  Algebraically the all-prime relation reduces regularly to one
hyperbolic port; no Witt-rank obstruction appears.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section AlgebraicPort

variable {P : Type*}

/-- The augmentation of finitely supported prime coordinates. -/
noncomputable def augment : (P →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ fun _ => (1 : ℂ)

@[simp] theorem augment_single (p : P) (a : ℂ) : augment (Finsupp.single p a) = a := by
  simp [augment]

theorem augment_apply (l : P →₀ ℂ) : augment l = ∑ p ∈ l.support, l p := by
  rw [augment, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun p _ => by simp

/-- The augmentation constraint `I₀`. -/
noncomputable def augIdeal : Submodule ℂ (P →₀ ℂ) := LinearMap.ker augment

theorem mem_augIdeal_iff {l : P →₀ ℂ} : l ∈ augIdeal ↔ augment l = 0 := Iff.rfl

theorem sub_single_mem_augIdeal (p q : P) :
    Finsupp.single p (1 : ℂ) - Finsupp.single q 1 ∈ augIdeal := by
  rw [mem_augIdeal_iff, map_sub, augment_single, augment_single, sub_self]

theorem augment_surjective [Nonempty P] : Function.Surjective (augment : (P →₀ ℂ) →ₗ[ℂ] ℂ) := by
  intro z
  obtain ⟨p⟩ := ‹Nonempty P›
  exact ⟨Finsupp.single p z, by simp⟩

/-- **Theorem 1, `(RC.3)`.**  A covector annihilates the augmentation constraint exactly when it is
a multiple of the augmentation. -/
theorem dualAnnihilator_augIdeal [Nonempty P] :
    (augIdeal : Submodule ℂ (P →₀ ℂ)).dualAnnihilator
      = Submodule.span ℂ {(augment : Module.Dual ℂ (P →₀ ℂ))} := by
  obtain ⟨p₀⟩ := ‹Nonempty P›
  apply le_antisymm
  · intro α hα
    rw [Submodule.mem_dualAnnihilator] at hα
    set a : ℂ := α (Finsupp.single p₀ (1 : ℂ)) with hadef
    have hcoord : ∀ p : P, α (Finsupp.single p (1 : ℂ)) = a := by
      intro p
      have h0 := hα _ (sub_single_mem_augIdeal p p₀)
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hα' : α = a • (augment : Module.Dual ℂ (P →₀ ℂ)) := by
      refine LinearMap.ext fun l => ?_
      have hl : l = ∑ p ∈ l.support, Finsupp.single p (l p) := (Finsupp.sum_single l).symm
      rw [hl, map_sum]
      simp only [LinearMap.smul_apply, smul_eq_mul, map_sum]
      have hterm : ∀ p ∈ l.support, α (Finsupp.single p (l p)) = l p * a := by
        intro p _
        have : Finsupp.single p (l p) = l p • Finsupp.single p (1 : ℂ) := by
          rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        rw [this, map_smul, hcoord p, smul_eq_mul]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      have hval : ∀ p ∈ l.support, a * augment (Finsupp.single p (l p)) = a * l p := by
        intro p _
        rw [augment_single]
      rw [Finset.sum_congr rfl hval, ← Finset.mul_sum]
      ring
    rw [hα']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (Submodule.mem_dualAnnihilator _).2 fun x hx => hx

/-- The algebraic cotangent double. -/
abbrev PortDouble (P : Type*) := (P →₀ ℂ) × Module.Dual ℂ (P →₀ ℂ)

/-- The canonical cotangent form `(RC.2)`. -/
noncomputable def portForm (u v : PortDouble P) : ℂ := u.2 v.1 - v.2 u.1

/-- The symplectic orthogonal of a subspace of the double. -/
noncomputable def portOrth (S : Submodule ℂ (PortDouble P)) : Submodule ℂ (PortDouble P) where
  carrier := {u | ∀ v ∈ S, portForm v u = 0}
  add_mem' := by
    intro x y hx hy v hv
    have h1 := hx v hv
    have h2 := hy v hv
    simp only [portForm, Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply] at *
    linear_combination h1 + h2
  zero_mem' := by
    intro v _
    simp [portForm]
  smul_mem' := by
    intro a x hx v hv
    have h1 := hx v hv
    simp only [portForm, Prod.smul_fst, Prod.smul_snd, map_smul, LinearMap.smul_apply,
      smul_eq_mul] at *
    linear_combination a * h1

theorem mem_portOrth {S : Submodule ℂ (PortDouble P)} {u : PortDouble P} :
    u ∈ portOrth S ↔ ∀ v ∈ S, portForm v u = 0 := Iff.rfl

/-- `I₀` as an isotropic subspace of the double. -/
noncomputable def augIsotropic : Submodule ℂ (PortDouble P) :=
  (augIdeal : Submodule ℂ (P →₀ ℂ)).prod ⊥

theorem augIsotropic_isotropic (u v : PortDouble P) (hu : u ∈ augIsotropic (P := P))
    (hv : v ∈ augIsotropic (P := P)) : portForm u v = 0 := by
  have h1 : u.2 = 0 := by simpa using hu.2
  have h2 : v.2 = 0 := by simpa using hv.2
  simp [portForm, h1, h2]

/-- **Theorem 1, `(RC.3)`.**  The symplectic orthogonal of the augmentation constraint is the whole
chart paired with the augmentation line. -/
theorem portOrth_augIsotropic [Nonempty P] :
    portOrth (augIsotropic (P := P))
      = (⊤ : Submodule ℂ (P →₀ ℂ)).prod
          (Submodule.span ℂ {(augment : Module.Dual ℂ (P →₀ ℂ))}) := by
  ext u
  rw [mem_portOrth, Submodule.mem_prod]
  constructor
  · intro hu
    refine ⟨Submodule.mem_top, ?_⟩
    rw [← dualAnnihilator_augIdeal]
    refine (Submodule.mem_dualAnnihilator _).2 fun x hx => ?_
    have := hu (x, 0) ⟨hx, by simp⟩
    simpa [portForm] using this
  · rintro ⟨-, hu2⟩
    rw [← dualAnnihilator_augIdeal, Submodule.mem_dualAnnihilator] at hu2
    rintro ⟨x, α⟩ ⟨hx, hα⟩
    have hα0 : α = 0 := by simpa using hα
    have := hu2 x hx
    simp [portForm, hα0, this]

/-- The reduction of the double to the hyperbolic plane: augmentation on the base, coefficient
along the augmentation on the fibre. -/
noncomputable def portRed (p₀ : P) : PortDouble P →ₗ[ℂ] ℂ × ℂ where
  toFun := fun u => (augment u.1, u.2 (Finsupp.single p₀ 1))
  map_add' := fun u v => by simp
  map_smul' := fun a u => by simp

@[simp] theorem portRed_apply (p₀ : P) (u : PortDouble P) :
    portRed p₀ u = (augment u.1, u.2 (Finsupp.single p₀ 1)) := rfl

/-- The hyperbolic form on `ℂ × ℂ`. -/
def hyperbolicForm (u v : ℂ × ℂ) : ℂ := u.2 * v.1 - v.2 * u.1

/-- **Theorem 1, `(RC.4)`, transport of the form.**  On the symplectic orthogonal the cotangent form
is the pullback of the hyperbolic form along the reduction. -/
theorem portForm_eq_hyperbolicForm [Nonempty P] (p₀ : P) {u v : PortDouble P}
    (hu : u ∈ portOrth (augIsotropic (P := P))) (hv : v ∈ portOrth (augIsotropic (P := P))) :
    portForm u v = hyperbolicForm (portRed p₀ u) (portRed p₀ v) := by
  rw [portOrth_augIsotropic, Submodule.mem_prod] at hu hv
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hu.2
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hv.2
  rw [portForm, hyperbolicForm, portRed_apply, portRed_apply, ← ha, ← hb]
  simp [smul_eq_mul]

/-- The reduction is surjective on the symplectic orthogonal. -/
theorem portRed_surjOn [Nonempty P] (p₀ : P) (z : ℂ × ℂ) :
    ∃ u ∈ portOrth (augIsotropic (P := P)), portRed p₀ u = z := by
  refine ⟨(Finsupp.single p₀ z.1, z.2 • (augment : Module.Dual ℂ (P →₀ ℂ))), ?_, ?_⟩
  · rw [portOrth_augIsotropic, Submodule.mem_prod]
    exact ⟨Submodule.mem_top, Submodule.mem_span_singleton.2 ⟨z.2, rfl⟩⟩
  · simp

/-- The kernel of the reduction inside the symplectic orthogonal is exactly the constraint. -/
theorem ker_portRed_inf [Nonempty P] (p₀ : P) :
    portOrth (augIsotropic (P := P)) ⊓ LinearMap.ker (portRed p₀) = augIsotropic := by
  apply le_antisymm
  · intro u humem
    rw [Submodule.mem_inf] at humem
    obtain ⟨hu, hker⟩ := humem
    rw [portOrth_augIsotropic, Submodule.mem_prod] at hu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hu.2
    have hk : augment u.1 = 0 ∧ u.2 (Finsupp.single p₀ 1) = 0 := by
      have := hker
      rw [LinearMap.mem_ker, portRed_apply, Prod.ext_iff] at this
      exact ⟨this.1, this.2⟩
    have ha0 : a = 0 := by
      have := hk.2
      rw [← ha] at this
      simpa using this
    refine ⟨hk.1, ?_⟩
    rw [← ha, ha0, zero_smul]
    exact Submodule.zero_mem _
  · intro u hu
    have h2 : u.2 = 0 := by simpa using hu.2
    rw [Submodule.mem_inf]
    constructor
    · rw [portOrth_augIsotropic, Submodule.mem_prod]
      exact ⟨Submodule.mem_top, by rw [h2]; exact Submodule.zero_mem _⟩
    · rw [LinearMap.mem_ker, portRed_apply, h2]
      simp only [LinearMap.zero_apply, Prod.mk_eq_zero]
      exact ⟨hu.1, trivial⟩

/-- The augmentation identifies `K₀/I₀` with `ℂ`. -/
theorem augIdeal_quotient_equiv [Nonempty P] :
    Nonempty ((((P →₀ ℂ) ⧸ (augIdeal : Submodule ℂ (P →₀ ℂ)))) ≃ₗ[ℂ] ℂ) :=
  ⟨LinearMap.quotKerEquivOfSurjective _ (augment_surjective (P := P))⟩

/-- **Theorem 1, `(RC.4)`.**  The reduction `(x, a ε) ↦ (ε x, a)` maps the symplectic orthogonal of
the augmentation constraint onto `ℂ × ℂ`, its kernel there is exactly the constraint, and it
carries the cotangent form to the hyperbolic form.  So the coisotropic quotient `I₀^ω/I₀` is the
hyperbolic plane `ℍ(ℂ)`. -/
theorem coisotropic_reduction [Nonempty P] (p₀ : P) :
    (∀ z : ℂ × ℂ, ∃ u ∈ portOrth (augIsotropic (P := P)), portRed p₀ u = z) ∧
    portOrth (augIsotropic (P := P)) ⊓ LinearMap.ker (portRed p₀) = augIsotropic ∧
    (∀ u ∈ portOrth (augIsotropic (P := P)), ∀ v ∈ portOrth (augIsotropic (P := P)),
      portForm u v = hyperbolicForm (portRed p₀ u) (portRed p₀ v)) :=
  ⟨portRed_surjOn p₀, ker_portRed_inf p₀,
    fun _ hu _ hv => portForm_eq_hyperbolicForm p₀ hu hv⟩

end AlgebraicPort

end HTGeometry.ConstraintMotiveRelativity
