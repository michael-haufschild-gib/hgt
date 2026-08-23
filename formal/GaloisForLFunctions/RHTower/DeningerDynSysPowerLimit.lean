import GaloisForLFunctions.RHTower.DeningerDynSysCharacterColimit
import Mathlib.Topology.Algebra.Monoid

/-!
# The projective limit along the power maps, and the continuous character points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §3, the description
`(24rn)` of `X̌ (C)` and Definition 3.5 (`t36n`).

For a submonoid `N₀ ⊆ ℕ` ordered by divisibility, the projective limit

`lim_{N₀} M = { (x_ν)_{ν ∈ N₀} | x_{ν μ} ^ μ = x_ν }`

of a commutative monoid `M` along the power maps carries the projections `pr_ν`.  A point of
`X̌ (C)` is a pair `(x , P)` with `P : lim_{N₀} κ (x)ˣ → Cˣ` a character factoring through some
`pr_ν`; this is the map recorded here from the colimit built in
`DeningerDynSysCharacterColimit`.

Definition 3.5 replaces "factors through some `pr_ν`" by continuity for given topologies on the
groups `κ (x)ˣ` and the projective limit topology.  When the `κ (x)ˣ` are discrete, every
character factoring through a projection is continuous, which is the easy half of Corollary 3.7.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

/-! ## The projective limit along the power maps -/

/-- **Deninger, §3.**  The projective limit `lim_{N₀} M` of a commutative monoid along the power
maps, as a submonoid of the functions on `N₀`. -/
def deningerPowerLimitSubmonoid (M : Type*) [CommMonoid M] (N₀ : Submonoid ℕ) :
    Submonoid (N₀ → M) where
  carrier := {f | ∀ ν μ : N₀, f (ν * μ) ^ (μ : ℕ) = f ν}
  one_mem' := by intro ν μ; simp
  mul_mem' := by
    intro f g hf hg ν μ
    show (f (ν * μ) * g (ν * μ)) ^ (μ : ℕ) = f ν * g ν
    rw [mul_pow, hf ν μ, hg ν μ]

/-- The projective limit `lim_{N₀} M`. -/
abbrev DeningerPowerLimit (M : Type*) [CommMonoid M] (N₀ : Submonoid ℕ) : Type _ :=
  deningerPowerLimitSubmonoid M N₀

variable {M : Type*} [CommMonoid M] {N₀ : Submonoid ℕ}

/-- **Deninger, (23rn).**  The projection `pr_ν : lim_{N₀} M → M`. -/
def deningerPowerProj (ν : N₀) : DeningerPowerLimit M N₀ →* M where
  toFun f := f.1 ν
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem deningerPowerProj_apply (ν : N₀) (f : DeningerPowerLimit M N₀) :
    deningerPowerProj ν f = f.1 ν := rfl

/-- The projections are compatible with the power maps. -/
theorem deningerPowerProj_pow (ν μ : N₀) (f : DeningerPowerLimit M N₀) :
    deningerPowerProj (ν * μ) f ^ (μ : ℕ) = deningerPowerProj ν f := f.2 ν μ

/-- The projective limit topology. -/
instance deningerPowerLimitTopology [TopologicalSpace M] :
    TopologicalSpace (DeningerPowerLimit M N₀) :=
  TopologicalSpace.induced (fun f : DeningerPowerLimit M N₀ => f.1) inferInstance

theorem deningerPowerProj_continuous [TopologicalSpace M] (ν : N₀) :
    Continuous (deningerPowerProj (M := M) ν) :=
  (continuous_apply ν).comp continuous_induced_dom

/-! ## Characters factoring through a projection -/

variable {C : Type*} [CommMonoid C]

/-- A character of the projective limit factoring through the `ν`-th projection. -/
def deningerFactoredChar (ν : N₀) (ψ : M →* C) : DeningerPowerLimit M N₀ →* C :=
  ψ.comp (deningerPowerProj ν)

@[simp] theorem deningerFactoredChar_apply (ν : N₀) (ψ : M →* C)
    (f : DeningerPowerLimit M N₀) :
    deningerFactoredChar ν ψ f = ψ (f.1 ν) := rfl

/-- **Deninger, Corollary 3.7 (`t38n`), the elementary half.**  If `M` carries the discrete
topology, every character of the projective limit that factors through a projection is
continuous. -/
theorem deningerFactoredChar_continuous [TopologicalSpace M] [DiscreteTopology M]
    [TopologicalSpace C] (ν : N₀) (ψ : M →* C) :
    Continuous (deningerFactoredChar ν ψ) :=
  (continuous_of_discreteTopology (f := ψ)).comp (deningerPowerProj_continuous ν)

/-! ## Definition 3.5: the continuous character points -/

section Definition35

variable (X : Scheme.{u}) (C₀ : Type u) [Field C₀] [TopologicalSpace C₀]
  [∀ x : X, TopologicalSpace ((X.residueField x)ˣ)] (N : Submonoid ℕ)

/-- **Deninger, Definition 3.5 (`t36n`).**  The space `X̂̂ (C)` of pairs `(x , P)` where `P` is a
*continuous* character of the projective limit `lim_{N₀} κ (x)ˣ`. -/
def DeningerContinuousCharPoints : Type u :=
  Σ x : X, {χ : DeningerPowerLimit ((X.residueField x)ˣ) N →* C₀ˣ // Continuous χ}

variable {X C₀ N}

/-- The projection of a continuous character point to the underlying scheme point. -/
def deningerContinuousCharProj (P : DeningerContinuousCharPoints X C₀ N) : X := P.1

/-- **Deninger, §3, the description (24rn).**  A character point of `X̂ (C)` together with an index
`ν ∈ N₀` gives a continuous character point, provided the residue field unit groups are
discrete. -/
noncomputable def deningerContinuousCharOfFactored [∀ x : X, DiscreteTopology ((X.residueField x)ˣ)]
    (ν : N) (P : DeningerCharPoints X C₀) : DeningerContinuousCharPoints X C₀ N :=
  ⟨P.1, ⟨deningerFactoredChar ν P.2, deningerFactoredChar_continuous ν P.2⟩⟩

@[simp] theorem deningerContinuousCharOfFactored_fst
    [∀ x : X, DiscreteTopology ((X.residueField x)ˣ)]
    (ν : N) (P : DeningerCharPoints X C₀) :
    (deningerContinuousCharOfFactored ν P).1 = P.1 := rfl

end Definition35

end RHTower
