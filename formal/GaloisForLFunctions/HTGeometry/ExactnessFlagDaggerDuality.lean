import GaloisForLFunctions.HTGeometry.ExactnessFlagProvenanceTopology
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dagger of an exactness flag

The algebraic dagger of an exactness flag `B ≤ Z` is the annihilator flag `Z° ≤ B°` in the dual
space.  It reverses the two provenance roles: the boundary space of the dagger is the annihilator of
the cycle space, and its cycle space is the annihilator of the boundary space.

The dagger is not a second spectrum.  Its spectral quotient is canonically the dual of the original
spectral quotient: restriction of a boundary-annihilating covector to the cycle space induces a
surjection onto the dual of `Z / B` whose kernel is exactly `Z°`, so

`B° / Z° ≅ (Z / B)ᵛ`.

On a finite-dimensional space the dagger is an involution up to the canonical double-dual
identification, and it is a bijection of flag spaces.
-/

namespace GaloisForLFunctions.HTGeometry

namespace ExFlag

open Set

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ## The dagger flag -/

/-- Algebraic dagger of an exactness flag: the opposite flag of annihilators. -/
def dagger (p : ExFlag K V) : ExFlag K (Module.Dual K V) :=
  ⟨p.cycle.dualAnnihilator, p.boundary.dualAnnihilator,
    Submodule.dualAnnihilator_anti p.boundary_le_cycle⟩

@[simp] theorem dagger_boundary (p : ExFlag K V) :
    (dagger p).boundary = p.cycle.dualAnnihilator := rfl

@[simp] theorem dagger_cycle (p : ExFlag K V) :
    (dagger p).cycle = p.boundary.dualAnnihilator := rfl

/-! ## The canonical pairing of the two spectral quotients -/

/-- Restriction to the cycle space carries a boundary-annihilating covector to a covector
annihilating the boundary part of the cycle space. -/
def daggerRestrict (p : ExFlag K V) :
    p.boundary.dualAnnihilator →ₗ[K]
      (Submodule.comap p.cycle.subtype p.boundary).dualAnnihilator :=
  LinearMap.codRestrict _
    ((Submodule.dualRestrict p.cycle).comp p.boundary.dualAnnihilator.subtype)
    (by
      intro φ
      rw [Submodule.mem_dualAnnihilator]
      rintro ⟨w, hw⟩ hmem
      exact (Submodule.mem_dualAnnihilator _).1 φ.2 w hmem)

/-- **The canonical pairing of a spectral quotient with its dagger.**  A boundary-annihilating
covector evaluates on classes of the spectral quotient. -/
def daggerEval (p : ExFlag K V) :
    p.boundary.dualAnnihilator →ₗ[K] Module.Dual K p.homology :=
  (Submodule.dualCopairing _).comp (daggerRestrict p)

@[simp] theorem daggerEval_homologyClass (p : ExFlag K V)
    (φ : p.boundary.dualAnnihilator) {v : V} (hv : v ∈ p.cycle) :
    daggerEval p φ (p.homologyClass hv) = (φ : Module.Dual K V) v := rfl

/-- **Every functional on the spectral quotient comes from a boundary-annihilating covector.**
A functional on `Z / B` lifts to `Z` and then extends to the whole space. -/
theorem surjective_daggerEval (p : ExFlag K V) : Function.Surjective (daggerEval p) := by
  intro ψ
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_extend (ψ.comp (Submodule.comap p.cycle.subtype p.boundary).mkQ)
  have hval : ∀ (v : V) (hv : v ∈ p.cycle),
      g v = ψ ((Submodule.comap p.cycle.subtype p.boundary).mkQ ⟨v, hv⟩) := by
    intro v hv
    have := congrArg (fun f : p.cycle →ₗ[K] K => f ⟨v, hv⟩) hg
    simpa using this
  have hgB : g ∈ p.boundary.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro b hb
    have hbZ : b ∈ p.cycle := p.boundary_le_cycle hb
    rw [hval b hbZ, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).2 (show (⟨b, hbZ⟩ : p.cycle) ∈
        Submodule.comap p.cycle.subtype p.boundary from hb), map_zero]
  refine ⟨⟨g, hgB⟩, ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show g (z : V) = ψ (Submodule.Quotient.mk z)
  exact hval (z : V) z.2

/-- **The pairing degenerates exactly on the annihilator of the cycle space.** -/
theorem ker_daggerEval (p : ExFlag K V) :
    LinearMap.ker (daggerEval p) =
      Submodule.comap p.boundary.dualAnnihilator.subtype p.cycle.dualAnnihilator := by
  ext φ
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.mem_dualAnnihilator]
  constructor
  · intro h v hv
    have := congrArg (fun f : Module.Dual K p.homology => f (p.homologyClass hv)) h
    simpa using this
  · intro h
    refine LinearMap.ext fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact h (z : V) z.2

/-- **The dagger spectral quotient is the dual of the spectral quotient.**  This is the perfect
pairing `(Z / B) × (B° / Z°) → K`. -/
noncomputable def daggerHomologyEquiv (p : ExFlag K V) :
    (dagger p).homology ≃ₗ[K] Module.Dual K p.homology :=
  (Submodule.quotEquivOfEq _ _ (ker_daggerEval p).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_daggerEval p))

/-- The pairing separates points of the spectral quotient. -/
theorem eq_zero_of_forall_daggerEval_eq_zero (p : ExFlag K V) {x : p.homology}
    (h : ∀ φ : p.boundary.dualAnnihilator, daggerEval p φ x = 0) : x = 0 := by
  refine (Module.forall_dual_apply_eq_zero_iff K x).1 fun ψ => ?_
  obtain ⟨φ, rfl⟩ := surjective_daggerEval p ψ
  exact h φ

/-! ## Involutivity -/

variable [FiniteDimensional K V]

/-- **The dagger is an involution.**  Applying it twice returns the flag transported along the
canonical evaluation isomorphism into the double dual. -/
theorem dagger_dagger (p : ExFlag K V) :
    dagger (dagger p) =
      pushforward (Module.Dual.eval K V) p := by
  refine ExFlag.ext ?_ ?_
  · show (p.boundary.dualAnnihilator).dualAnnihilator = Submodule.map (Module.Dual.eval K V) _
    rw [Subspace.dualAnnihilator_dualAnnihilator_eq, Module.mapEvalEquiv_apply]
  · show (p.cycle.dualAnnihilator).dualAnnihilator = Submodule.map (Module.Dual.eval K V) _
    rw [Subspace.dualAnnihilator_dualAnnihilator_eq, Module.mapEvalEquiv_apply]

/-- The inverse dagger, built from coannihilators. -/
def daggerSymm (q : ExFlag K (Module.Dual K V)) : ExFlag K V :=
  ⟨q.cycle.dualCoannihilator, q.boundary.dualCoannihilator,
    Submodule.dualCoannihilator_anti q.boundary_le_cycle⟩

omit [FiniteDimensional K V] in
@[simp] theorem daggerSymm_boundary (q : ExFlag K (Module.Dual K V)) :
    (daggerSymm q).boundary = q.cycle.dualCoannihilator := rfl

omit [FiniteDimensional K V] in
@[simp] theorem daggerSymm_cycle (q : ExFlag K (Module.Dual K V)) :
    (daggerSymm q).cycle = q.boundary.dualCoannihilator := rfl

omit [FiniteDimensional K V] in
theorem daggerSymm_dagger (p : ExFlag K V) : daggerSymm (dagger p) = p := by
  refine ExFlag.ext ?_ ?_
  · exact Subspace.dualAnnihilator_dualCoannihilator_eq
  · exact Subspace.dualAnnihilator_dualCoannihilator_eq

theorem dagger_daggerSymm (q : ExFlag K (Module.Dual K V)) : dagger (daggerSymm q) = q := by
  refine ExFlag.ext ?_ ?_
  · exact Subspace.dualCoannihilator_dualAnnihilator_eq
  · exact Subspace.dualCoannihilator_dualAnnihilator_eq

/-- **The dagger is a bijection of flag spaces.** -/
def daggerEquiv (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    ExFlag K V ≃ ExFlag K (Module.Dual K V) where
  toFun := dagger
  invFun := daggerSymm
  left_inv := daggerSymm_dagger
  right_inv := dagger_daggerSymm

@[simp] theorem daggerEquiv_apply (p : ExFlag K V) : daggerEquiv K V p = dagger p := rfl

@[simp] theorem daggerEquiv_symm_apply (q : ExFlag K (Module.Dual K V)) :
    (daggerEquiv K V).symm q = daggerSymm q := rfl

end ExFlag

end GaloisForLFunctions.HTGeometry
