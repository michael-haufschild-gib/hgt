import Mathlib.AlgebraicGeometry.FunctionField
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittLocalSections
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysWittFatouCarrier

/-!
# `W_rat (𝒪_X)` on an integral scheme

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 2.1(b), (c).

On an integral scheme every nonempty open has a domain of sections which embeds in the function
field `K`.  Part (b) says that if `𝒪_X (U)` is a Fatou domain, then the sheaf `W_rat (𝒪_X)` has no
sections over `U` beyond `W_rat (𝒪_X (U))` itself.  Part (c) computes the sections of
`W_rat (𝒪_X)` over an arbitrary open of a scheme all of whose affine sections are Fatou:  they
are exactly the big Witt vectors over `𝒪_X (U)` whose image in `W (K)` is rational.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

variable (X : Scheme.{u})

/-- **Deninger, Proposition 2.1(c), hypothesis.**  A scheme is *Fatou* when the sections over
every nonempty affine open form a Fatou domain. -/
def DeningerFatouScheme (X : Scheme.{u}) : Prop :=
  ∀ V : X.Opens, IsAffineOpen V → ∀ (_ : Nonempty V) (inst : IsDomain Γ(X, V)),
    @DeningerFatouDomain Γ(X, V) _ inst

/-- Restriction is compatible with the maps to the function field. -/
theorem deningerGermToFunctionField_res [IsIntegral X] {U V : X.Opens} (h : V ≤ U)
    [Nonempty V] [Nonempty U] (s : Γ(X, U)) :
    algebraMap Γ(X, V) X.functionField ((X.presheaf.map (homOfLE h).op) s)
      = algebraMap Γ(X, U) X.functionField s := by
  show (X.germToFunctionField V) ((X.presheaf.map (homOfLE h).op) s)
    = (X.germToFunctionField U) s
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ s

/-- The big Witt map to `W (K)` factors through any restriction. -/
theorem deningerBigWittRing_functionField_res [IsIntegral X] {U V : X.Opens} (h : V ≤ U)
    [Nonempty V] [Nonempty U] (w : DeningerBigWittRing Γ(X, U)) :
    deningerBigWittRingMap (algebraMap Γ(X, V) X.functionField)
        (deningerBigWittRingMap (X.presheaf.map (homOfLE h).op).hom w)
      = deningerBigWittRingMap (algebraMap Γ(X, U) X.functionField) w := by
  have hcomp : (algebraMap Γ(X, V) X.functionField).comp
      (X.presheaf.map (homOfLE h).op).hom = algebraMap Γ(X, U) X.functionField :=
    RingHom.ext (deningerGermToFunctionField_res X h)
  rw [← deningerBigWittRingMap_comp, hcomp]

theorem deningerFunctionField_faithfulSMul [IsIntegral X] (U : X.Opens) [Nonempty U] :
    FaithfulSMul Γ(X, U) X.functionField :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 (X.germToFunctionField_injective U)

/-- **Deninger, Proposition 2.1(c), the easy inclusion.**  A section of `W_rat (𝒪_X)` over a
nonempty open is rational over the function field. -/
theorem deningerWittLocallyRational_functionField [IsIntegral X] {U : X.Opens} [hU : Nonempty U]
    {w : DeningerBigWittRing Γ(X, U)} (hw : DeningerWittLocallyRational X.presheaf U w) :
    ∃ v : DeningerCanonicalRationalWittRing X.functionField,
      deningerCanonicalRationalWittEmbedding v
        = deningerBigWittRingMap (algebraMap Γ(X, U) X.functionField) w := by
  have x : U := hU.some
  obtain ⟨V, h, hxV, v, hv⟩ := hw x.1 x.2
  haveI : Nonempty V := ⟨⟨x.1, hxV⟩⟩
  refine ⟨deningerCanonicalRationalWittMap (algebraMap Γ(X, V) X.functionField) v, ?_⟩
  rw [deningerCanonicalRationalWittEmbedding_map, hv,
    deningerBigWittRing_functionField_res]

/-- The Fatou property of `𝒪_X (V)` turns rationality over the function field into rationality
over `V`. -/
theorem deningerWittRationalRange_of_functionField [IsIntegral X] {V : X.Opens} [Nonempty V]
    (hV : DeningerFatouDomain Γ(X, V)) {w : DeningerBigWittRing Γ(X, V)}
    {v : DeningerCanonicalRationalWittRing X.functionField}
    (hv : deningerCanonicalRationalWittEmbedding v
      = deningerBigWittRingMap (algebraMap Γ(X, V) X.functionField) w) :
    w ∈ deningerWittRationalRange X.presheaf V := by
  haveI := deningerFunctionField_faithfulSMul X V
  obtain ⟨v₀, hv₀⟩ := (deningerRationalWittFatouIntersection_ring Γ(X, V) X.functionField
    hV v).2 ⟨w, hv.symm⟩
  refine ⟨v₀, ?_⟩
  refine deningerBigWittRingMap_injective (algebraMap Γ(X, V) X.functionField)
    (X.germToFunctionField_injective V) ?_
  rw [← deningerCanonicalRationalWittEmbedding_map, hv₀, hv]

/-- **Deninger, Proposition 2.1(b).**  If `X` is integral and `𝒪_X (U)` is a Fatou domain, then
`W_rat (𝒪_X (U)) = W_rat (𝒪_X) (U)`. -/
theorem deningerWittLocallyRational_iff_rational [IsIntegral X] {U : X.Opens} [Nonempty U]
    (hU : DeningerFatouDomain Γ(X, U)) (w : DeningerBigWittRing Γ(X, U)) :
    DeningerWittLocallyRational X.presheaf U w ↔ w ∈ deningerWittRationalRange X.presheaf U := by
  refine ⟨fun hw => ?_, deningerWittLocallyRational_of_range⟩
  obtain ⟨v, hv⟩ := deningerWittLocallyRational_functionField X hw
  exact deningerWittRationalRange_of_functionField X hU hv

/-- **Deninger, Proposition 2.1(c).**  For a Fatou scheme `X` with function field `K` and any
nonempty open `U`, the sections of `W_rat (𝒪_X)` over `U` are exactly
`W_rat (K) ∩ W (𝒪_X (U))` inside `W (K)`. -/
theorem deningerWittLocallyRational_iff_functionField [IsIntegral X] (hX : DeningerFatouScheme X)
    {U : X.Opens} [Nonempty U] (w : DeningerBigWittRing Γ(X, U)) :
    DeningerWittLocallyRational X.presheaf U w
      ↔ ∃ v : DeningerCanonicalRationalWittRing X.functionField,
          deningerCanonicalRationalWittEmbedding v
            = deningerBigWittRingMap (algebraMap Γ(X, U) X.functionField) w := by
  refine ⟨fun hw => deningerWittLocallyRational_functionField X hw, ?_⟩
  rintro ⟨v, hv⟩ x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hle : V ≤ U := hVU
  refine ⟨V, hle, hxV, ?_⟩
  refine deningerWittRationalRange_of_functionField X (v := v)
    (hX V hV inferInstance inferInstance) ?_
  rw [deningerBigWittRing_functionField_res, hv]

end RHTower
