import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearOperator
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The normed space attached to a seminorm, and nuclear locally convex spaces

A seminorm on a vector space becomes a genuine norm on the quotient by its kernel.  A comparison
of seminorms induces a bounded map between the corresponding normed spaces, and those comparison
maps are what nuclearity of a locally convex space is about: a space is nuclear when every defining
seminorm is dominated by one whose comparison map is a nuclear operator.

Two facts make the definition usable.  A linear map out of a finite-dimensional space is nuclear,
since it is the finite sum of the rank-one maps given by a basis; consequently every space whose
defining seminorms live on a finite-dimensional space is nuclear.

* `deningerSeminormKer`, `DeningerSeminormSpace` : the kernel and the quotient normed space.
* `deningerSeminormMk`, `_norm` : the canonical map, whose norm is the seminorm.
* `deningerSeminormComparison`, `_norm_le` : the comparison map of two seminorms.
* `deningerIsNuclear_of_finiteDimensional` : maps out of a finite-dimensional space are nuclear.
* `DeningerIsNuclearSpace`, `deningerIsNuclearSpace_of_finiteDimensional` : nuclear spaces.
-/

namespace RHTower

section Kernel

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **The kernel of a seminorm.** -/
def deningerSeminormKer (p : Seminorm 𝕜 E) : Submodule 𝕜 E where
  carrier := {x | p x = 0}
  add_mem' {x y} hx hy := by
    refine le_antisymm ?_ (apply_nonneg p _)
    have h := map_add_le_add p x y
    rw [hx, hy, add_zero] at h
    exact h
  zero_mem' := map_zero p
  smul_mem' c x hx := by
    show p (c • x) = 0
    rw [map_smul_eq_mul, hx, mul_zero]

@[simp]
theorem deningerSeminormKer_mem {p : Seminorm 𝕜 E} {x : E} :
    x ∈ deningerSeminormKer p ↔ p x = 0 := Iff.rfl

/-- A seminorm is constant on the cosets of its kernel. -/
theorem deningerSeminorm_eq_of_sub_mem {p : Seminorm 𝕜 E} {x y : E}
    (h : x - y ∈ deningerSeminormKer p) : p x = p y := by
  have hxy : p (x - y) = 0 := h
  have hyx : p (y - x) = 0 := by
    have : y - x = -(x - y) := by abel
    rw [this, map_neg_eq_map]
    exact hxy
  refine le_antisymm ?_ ?_
  · have h1 : p x ≤ p y + p (x - y) := by
      have : x = y + (x - y) := by abel
      calc p x = p (y + (x - y)) := by rw [← this]
        _ ≤ p y + p (x - y) := map_add_le_add p _ _
    rwa [hxy, add_zero] at h1
  · have h2 : p y ≤ p x + p (y - x) := by
      have : y = x + (y - x) := by abel
      calc p y = p (x + (y - x)) := by rw [← this]
        _ ≤ p x + p (y - x) := map_add_le_add p _ _
    rwa [hyx, add_zero] at h2

end Kernel

section Quotient

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **The normed space attached to a seminorm**: the quotient by its kernel. -/
def DeningerSeminormSpace (p : Seminorm 𝕜 E) : Type _ := E ⧸ deningerSeminormKer p

instance instAddCommGroupSeminormSpace (p : Seminorm 𝕜 E) :
    AddCommGroup (DeningerSeminormSpace p) :=
  inferInstanceAs (AddCommGroup (E ⧸ deningerSeminormKer p))

instance instModuleSeminormSpace (p : Seminorm 𝕜 E) : Module 𝕜 (DeningerSeminormSpace p) :=
  inferInstanceAs (Module 𝕜 (E ⧸ deningerSeminormKer p))

/-- The class of a vector in the seminorm quotient. -/
def deningerSeminormMk (p : Seminorm 𝕜 E) : E →ₗ[𝕜] DeningerSeminormSpace p :=
  (deningerSeminormKer p).mkQ

theorem deningerSeminormMk_surjective (p : Seminorm 𝕜 E) :
    Function.Surjective (deningerSeminormMk p) :=
  Submodule.mkQ_surjective _

/-- The norm of the seminorm quotient, as a group norm. -/
noncomputable def deningerSeminormGroupNorm (p : Seminorm 𝕜 E) :
    AddGroupNorm (DeningerSeminormSpace p) where
  toFun z := Quotient.liftOn' z (fun x => p x) fun a b hab =>
    deningerSeminorm_eq_of_sub_mem ((Submodule.quotientRel_def _).mp hab)
  map_zero' := map_zero p
  add_le' := by
    rintro ⟨a⟩ ⟨b⟩
    exact map_add_le_add p a b
  neg' := by
    rintro ⟨a⟩
    exact map_neg_eq_map p a
  eq_zero_of_map_eq_zero' := by
    rintro ⟨a⟩ h
    exact (Submodule.Quotient.mk_eq_zero _).mpr h

noncomputable instance instNormedAddCommGroupSeminormSpace (p : Seminorm 𝕜 E) :
    NormedAddCommGroup (DeningerSeminormSpace p) :=
  (deningerSeminormGroupNorm p).toNormedAddCommGroup

@[simp]
theorem deningerSeminormMk_norm (p : Seminorm 𝕜 E) (x : E) :
    ‖deningerSeminormMk p x‖ = p x := rfl

noncomputable instance instNormedSpaceSeminormSpace (p : Seminorm 𝕜 E) :
    NormedSpace 𝕜 (DeningerSeminormSpace p) where
  norm_smul_le c z := by
    induction z using Quotient.inductionOn' with
    | h a =>
        show p (c • a) ≤ ‖c‖ * p a
        exact le_of_eq (map_smul_eq_mul p c a)

end Quotient

section Comparison

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem deningerSeminormKer_le {p q : Seminorm 𝕜 E} {C : ℝ} (h : ∀ x, p x ≤ C * q x) :
    deningerSeminormKer q ≤ deningerSeminormKer p := by
  intro x hx
  have hqx : q x = 0 := hx
  refine le_antisymm ?_ (apply_nonneg p _)
  have := h x
  rwa [hqx, mul_zero] at this

/-- **The comparison map of two seminorms.**  A domination `p ≤ C q` induces a bounded map from
the normed space of `q` to that of `p`. -/
noncomputable def deningerSeminormComparison {p q : Seminorm 𝕜 E} {C : ℝ}
    (h : ∀ x, p x ≤ C * q x) :
    DeningerSeminormSpace q →L[𝕜] DeningerSeminormSpace p :=
  LinearMap.mkContinuous
    (Submodule.mapQ (deningerSeminormKer q) (deningerSeminormKer p) LinearMap.id
      (deningerSeminormKer_le h))
    C (by
      rintro ⟨a⟩
      show p a ≤ C * q a
      exact h a)

@[simp]
theorem deningerSeminormComparison_mk {p q : Seminorm 𝕜 E} {C : ℝ} (h : ∀ x, p x ≤ C * q x)
    (x : E) :
    deningerSeminormComparison h (deningerSeminormMk q x) = deningerSeminormMk p x := rfl

theorem deningerSeminormComparison_norm_le {p q : Seminorm 𝕜 E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, p x ≤ C * q x) : ‖deningerSeminormComparison h‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

end Comparison

section FiniteDimensional

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A map out of a finite-dimensional space is nuclear.**  Expanding in a basis writes it as a
finite sum of rank-one maps. -/
theorem deningerIsNuclear_of_finiteDimensional (T : X →L[𝕜] Y) : DeningerIsNuclear T := by
  classical
  set n := Module.finrank 𝕜 X with hn
  set b := Module.finBasis 𝕜 X with hb
  refine ⟨Fin n, fun i => LinearMap.toContinuousLinearMap (b.coord i),
    fun i => T (b i), ?_, ?_⟩
  · exact (hasSum_fintype
      fun i => ‖LinearMap.toContinuousLinearMap (b.coord i)‖ * ‖T (b i)‖).summable
  · intro x
    have hx : ∑ i, b.coord i x • b i = x := by
      simp [Module.Basis.coord_apply]
    have hsum : HasSum (fun i => b.coord i x • T (b i)) (∑ i, b.coord i x • T (b i)) :=
      hasSum_fintype _
    have hval : ∑ i, b.coord i x • T (b i) = T x := by
      have hstep : ∑ i, b.coord i x • T (b i) = T (∑ i, b.coord i x • b i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => (map_smul T _ _).symm
      rw [hstep, hx]
    rwa [hval] at hsum

end FiniteDimensional

section NuclearSpace

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A nuclear locally convex space**: every defining seminorm is dominated by one whose
comparison map is a nuclear operator. -/
def DeningerIsNuclearSpace {ι : Type*} (P : SeminormFamily 𝕜 E ι) : Prop :=
  ∀ i : ι, ∃ (j : ι) (C : ℝ) (h : ∀ x, P i x ≤ C * P j x),
    DeningerIsNuclear (deningerSeminormComparison h)

/-- **A space with finite-dimensional seminorm quotients is nuclear.**  Every comparison map out of
a finite-dimensional normed space is nuclear, so it suffices that each seminorm quotient is finite
dimensional; taking the dominating seminorm to be the seminorm itself, with constant one. -/
theorem deningerIsNuclearSpace_of_finiteDimensional [CompleteSpace 𝕜] {ι : Type*}
    (P : SeminormFamily 𝕜 E ι)
    (hfin : ∀ i, FiniteDimensional 𝕜 (DeningerSeminormSpace (P i))) :
    DeningerIsNuclearSpace P := by
  intro i
  refine ⟨i, 1, fun x => by rw [one_mul], ?_⟩
  haveI := hfin i
  exact deningerIsNuclear_of_finiteDimensional _

end NuclearSpace

end RHTower

