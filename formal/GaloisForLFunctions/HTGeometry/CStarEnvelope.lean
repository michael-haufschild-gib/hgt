import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Enveloping C⋆-algebras of `*`-algebras with a dominating norm

For a complex `*`-algebra `B` and a function `N : B → ℝ`, an `N`-bounded representation is a
`*`-homomorphism `π : B → B(H)` into the bounded operators of a Hilbert space with
`‖π(b)‖ ≤ N(b)`.  The **enveloping C⋆-algebra** `C⋆(B, N)` is the norm closure of the universal
representation `b ↦ (π(b))_π` in `ℓ^∞(B(H_π))`: a C⋆-algebra whose norm is the supremum over all
`N`-bounded representations, through which every such representation factors.

For a locally compact group acting on a C⋆-algebra `A` and `N` the `L¹(G, A)` norm on a dense core
of `L¹(G, A)` with its twisted convolution, this is the full crossed product `A ⋊ G`.
-/

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

universe u

variable (B : Type u) [NonUnitalRing B] [StarRing B] [Module ℂ B] (N : B → ℝ)

/-- An `N`-bounded `*`-representation of `B` on a Hilbert space. -/
structure BoundedRep where
  /-- The Hilbert space. -/
  H : Type u
  [normed : NormedAddCommGroup H]
  [inner : InnerProductSpace ℂ H]
  [complete : CompleteSpace H]
  /-- The representation. -/
  π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)
  bound : ∀ b, ‖π b‖ ≤ N b

attribute [instance] BoundedRep.normed BoundedRep.inner BoundedRep.complete

/-- Bounded families of operators indexed by all `N`-bounded representations. -/
def EnvFamily : Type (u + 1) := lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞

instance : NonUnitalCStarAlgebra (EnvFamily B N) :=
  inferInstanceAs (NonUnitalCStarAlgebra (lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞))

variable {B N}

namespace EnvFamily

/-- The `ρ`-component of a bounded family. -/
def apply (y : EnvFamily B N) (ρ : BoundedRep B N) : ρ.H →L[ℂ] ρ.H :=
  (show lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞ from y) ρ

/-- A bounded family from a uniformly bounded choice of operators. -/
def ofBounded (f : ∀ ρ : BoundedRep B N, ρ.H →L[ℂ] ρ.H) (C : ℝ) (hf : ∀ ρ, ‖f ρ‖ ≤ C) :
    EnvFamily B N :=
  (⟨f, memℓp_infty ⟨C, by rintro _ ⟨ρ, rfl⟩; exact hf ρ⟩⟩ :
    lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞)

@[simp] theorem apply_ofBounded (f : ∀ ρ : BoundedRep B N, ρ.H →L[ℂ] ρ.H) (C : ℝ)
    (hf : ∀ ρ, ‖f ρ‖ ≤ C) (ρ : BoundedRep B N) : (ofBounded f C hf).apply ρ = f ρ := rfl

theorem ext {y z : EnvFamily B N} (h : ∀ ρ, y.apply ρ = z.apply ρ) : y = z :=
  lp.ext (funext h)

@[simp] theorem apply_add (y z : EnvFamily B N) (ρ : BoundedRep B N) :
    (y + z).apply ρ = y.apply ρ + z.apply ρ := rfl
@[simp] theorem apply_zero (ρ : BoundedRep B N) : (0 : EnvFamily B N).apply ρ = 0 := rfl
@[simp] theorem apply_mul (y z : EnvFamily B N) (ρ : BoundedRep B N) :
    (y * z).apply ρ = y.apply ρ * z.apply ρ := rfl
@[simp] theorem apply_smul (c : ℂ) (y : EnvFamily B N) (ρ : BoundedRep B N) :
    (c • y).apply ρ = c • y.apply ρ := rfl
@[simp] theorem apply_star (y : EnvFamily B N) (ρ : BoundedRep B N) :
    (star y).apply ρ = star (y.apply ρ) := rfl
@[simp] theorem apply_sub (y z : EnvFamily B N) (ρ : BoundedRep B N) :
    (y - z).apply ρ = y.apply ρ - z.apply ρ := rfl

theorem norm_apply_le (y : EnvFamily B N) (ρ : BoundedRep B N) : ‖y.apply ρ‖ ≤ ‖y‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero
    (show lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞ from y) ρ

theorem norm_le_of_forall_le {y : EnvFamily B N} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ρ, ‖y.apply ρ‖ ≤ C) : ‖y‖ ≤ C :=
  lp.norm_le_of_forall_le (f := (show lp (fun ρ : BoundedRep B N => ρ.H →L[ℂ] ρ.H) ∞ from y)) hC h

end EnvFamily

variable (B N)

/-- The **universal representation** `b ↦ (π(b))_π`. -/
def envUniversal : B →⋆ₙₐ[ℂ] EnvFamily B N where
  toFun b := EnvFamily.ofBounded (fun ρ => ρ.π b) (N b) fun ρ => ρ.bound b
  map_smul' c b := EnvFamily.ext fun ρ => by simp
  map_zero' := EnvFamily.ext fun ρ => by simp
  map_add' b b' := EnvFamily.ext fun ρ => by simp
  map_mul' b b' := EnvFamily.ext fun ρ => by simp
  map_star' b := EnvFamily.ext fun ρ => by
    rw [EnvFamily.apply_star, EnvFamily.apply_ofBounded, EnvFamily.apply_ofBounded]
    exact map_star ρ.π b

@[simp] theorem envUniversal_apply (b : B) (ρ : BoundedRep B N) :
    (envUniversal B N b).apply ρ = ρ.π b := rfl

/-- The closure of the universal representation. -/
def envSub : NonUnitalStarSubalgebra ℂ (EnvFamily B N) :=
  (NonUnitalStarAlgHom.range (envUniversal B N)).topologicalClosure

instance : IsClosed (envSub B N : Set (EnvFamily B N)) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

theorem mem_envSub_iff {y : EnvFamily B N} :
    y ∈ envSub B N ↔ y ∈ closure (Set.range (envUniversal B N)) := by
  rw [← NonUnitalStarAlgHom.coe_range]
  rfl

/-- **The enveloping C⋆-algebra** of `B` with respect to `N`. -/
def CStarEnvelope : Type (u + 1) := envSub B N

noncomputable instance : NonUnitalCStarAlgebra (CStarEnvelope B N) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra (envSub B N)

variable {B N}

/-- The underlying family of an element of the envelope. -/
def CStarEnvelope.val (y : CStarEnvelope B N) : EnvFamily B N :=
  Subtype.val (p := (· ∈ envSub B N)) y

theorem CStarEnvelope.val_mem (y : CStarEnvelope B N) : y.val ∈ envSub B N :=
  Subtype.property (p := (· ∈ envSub B N)) y

/-- An element of the envelope from a family in the closure. -/
def CStarEnvelope.mk (y : EnvFamily B N) (hy : y ∈ envSub B N) : CStarEnvelope B N :=
  (⟨y, hy⟩ : envSub B N)

@[simp] theorem CStarEnvelope.val_mk (y : EnvFamily B N) (hy : y ∈ envSub B N) :
    (CStarEnvelope.mk y hy).val = y := rfl

theorem CStarEnvelope.val_injective : Function.Injective (CStarEnvelope.val (B := B) (N := N)) :=
  Subtype.val_injective (p := (· ∈ envSub B N))

theorem CStarEnvelope.ext {y z : CStarEnvelope B N} (h : y.val = z.val) : y = z :=
  CStarEnvelope.val_injective h

@[simp] theorem CStarEnvelope.val_add (y z : CStarEnvelope B N) : (y + z).val = y.val + z.val :=
  rfl
@[simp] theorem CStarEnvelope.val_zero : (0 : CStarEnvelope B N).val = 0 := rfl
@[simp] theorem CStarEnvelope.val_mul (y z : CStarEnvelope B N) : (y * z).val = y.val * z.val :=
  rfl
@[simp] theorem CStarEnvelope.val_smul (c : ℂ) (y : CStarEnvelope B N) :
    (c • y).val = c • y.val := rfl
@[simp] theorem CStarEnvelope.val_star (y : CStarEnvelope B N) : (star y).val = star y.val := rfl
@[simp] theorem CStarEnvelope.val_sub (y z : CStarEnvelope B N) : (y - z).val = y.val - z.val :=
  rfl
theorem CStarEnvelope.norm_val (y : CStarEnvelope B N) : ‖y.val‖ = ‖y‖ := rfl

theorem CStarEnvelope.isInducing_val : Topology.IsInducing (CStarEnvelope.val (B := B) (N := N)) :=
  Topology.IsInducing.subtypeVal

theorem CStarEnvelope.continuous_val : Continuous (CStarEnvelope.val (B := B) (N := N)) :=
  CStarEnvelope.isInducing_val.continuous

variable (B N)

theorem envUniversal_mem (b : B) : envUniversal B N b ∈ envSub B N :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨b, rfl⟩

/-- The canonical map of `B` into its enveloping C⋆-algebra. -/
def toEnvelope : B →⋆ₙₐ[ℂ] CStarEnvelope B N where
  toFun b := CStarEnvelope.mk (envUniversal B N b) (envUniversal_mem B N b)
  map_smul' c b := CStarEnvelope.ext (map_smul (envUniversal B N) c b)
  map_zero' := CStarEnvelope.ext (map_zero (envUniversal B N))
  map_add' b b' := CStarEnvelope.ext (map_add (envUniversal B N) b b')
  map_mul' b b' := CStarEnvelope.ext (map_mul (envUniversal B N) b b')
  map_star' b := CStarEnvelope.ext (map_star (envUniversal B N) b)

@[simp] theorem toEnvelope_val (b : B) : (toEnvelope B N b).val = envUniversal B N b := rfl

theorem toEnvelope_dense : DenseRange (toEnvelope B N) := by
  intro y
  rw [CStarEnvelope.isInducing_val.closure_eq_preimage_closure_image]
  have himg : CStarEnvelope.val '' Set.range (toEnvelope B N) = Set.range (envUniversal B N) := by
    ext z
    constructor
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, ⟨b, rfl⟩, rfl⟩
  rw [Set.mem_preimage, himg, ← mem_envSub_iff]
  exact y.val_mem

/-- The envelope norm is dominated by `N`. -/
theorem norm_toEnvelope_le (b : B) (hN : 0 ≤ N b) : ‖toEnvelope B N b‖ ≤ N b :=
  EnvFamily.norm_le_of_forall_le hN fun ρ => ρ.bound b

variable {B N}

/-- Every `N`-bounded representation is dominated by the envelope norm. -/
theorem BoundedRep.norm_le_envelope (ρ : BoundedRep B N) (b : B) :
    ‖ρ.π b‖ ≤ ‖toEnvelope B N b‖ :=
  (envUniversal B N b).norm_apply_le ρ

/-- **Universal property**: an `N`-bounded representation extends to the envelope. -/
def BoundedRep.extend (ρ : BoundedRep B N) : CStarEnvelope B N →⋆ₙₐ[ℂ] (ρ.H →L[ℂ] ρ.H) where
  toFun y := y.val.apply ρ
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

theorem BoundedRep.extend_toEnvelope (ρ : BoundedRep B N) (b : B) :
    ρ.extend (toEnvelope B N b) = ρ.π b := rfl

end GaloisForLFunctions.HTGeometry
