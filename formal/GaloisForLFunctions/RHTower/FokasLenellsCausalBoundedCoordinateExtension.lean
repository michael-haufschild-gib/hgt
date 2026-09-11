import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedCoordinateDensity
import GaloisForLFunctions.RHTower.FokasLenellsCausalBoundedExponentialGroup
import GaloisForLFunctions.RHTower.FokasLenellsCausalCoisometry

/-! Bounded L2 extensions of actual bounded derivative-chain operators.
Every fixed derivative coordinate has dense range. This forces uniqueness of a
bounded extension and excludes backward real time using the genuine Cauchy kernel. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance causalCoordinateExtensionLowerComplete : CompleteSpace (hardyL2ᗮ) :=
  hardyL2.isClosed_orthogonal.completeSpace_coe
local instance causalCoordinateExtensionChainNormedGroup : NormedAddCommGroup causalBoundedChain :=
  causalBoundedChain.normedAddCommGroup
local instance causalCoordinateExtensionChainNormedSpace : NormedSpace ℂ causalBoundedChain :=
  causalBoundedChain.normedSpace

/-- Compatibility of a bounded chain operator with a bounded original L2 operator
through one genuine derivative coordinate. -/
def causalBoundedCoordinateExtension (j : ℕ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain)
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) : Prop :=
  T.comp (causalBoundedChainCoordinate j) = (causalBoundedChainCoordinate j).comp A

/-- Each genuine derivative coordinate permits at most one bounded L2 extension
of any prescribed bounded chain operator. -/
theorem causalBoundedCoordinateExtension_subsingleton (j : ℕ)
    (A : causalBoundedChain →L[ℂ] causalBoundedChain) :
    Set.Subsingleton {T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ | causalBoundedCoordinateExtension j A T} := by
  intro T hT U hU
  have he : (T : hardyL2ᗮ → hardyL2ᗮ) = U :=
    (causalBoundedChainCoordinate_denseRange j).equalizer T.continuous U.continuous (by
      funext u
      exact congrArg (fun Q : causalBoundedChain →L[ℂ] hardyL2ᗮ => Q u)
        (hT.trans hU.symm))
  exact ContinuousLinearMap.ext (fun x => congrFun he x)

private theorem evolution_extends (j : ℕ) (t : ℝ≥0) :
    causalBoundedCoordinateExtension j (causalBoundedChainExponential ((t : ℝ) : ℂ))
      (causalLowerCauchyEvolution t) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (causalBoundedEntireOrbit_eq_evolution j u t).symm

/-- The unique bounded L2 extension of forward chain evolution is exactly the
original causal Cauchy semigroup, at every derivative coordinate. -/
theorem causalBoundedCoordinateExtension_real_iff (j : ℕ) (t : ℝ≥0)
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ) :
    causalBoundedCoordinateExtension j (causalBoundedChainExponential ((t : ℝ) : ℂ)) T ↔
      T = causalLowerCauchyEvolution t := by
  constructor
  · intro hT
    exact causalBoundedCoordinateExtension_subsingleton j _ hT (evolution_extends j t)
  · rintro rfl
    exact evolution_extends j t

private theorem backward_extension_left_inverse (j : ℕ) (s : ℝ≥0)
    (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (hT : causalBoundedCoordinateExtension j
      (causalBoundedChainExponential (-((s : ℝ) : ℂ))) T) :
    T.comp (causalLowerCauchyEvolution s) = ContinuousLinearMap.id ℂ (hardyL2ᗮ) := by
  have hleft : causalBoundedCoordinateExtension j (ContinuousLinearMap.id ℂ causalBoundedChain)
      (T.comp (causalLowerCauchyEvolution s)) := by
    apply ContinuousLinearMap.ext
    intro u
    change T (causalLowerCauchyEvolution s (causalBoundedChainCoordinate j u)) =
      causalBoundedChainCoordinate j u
    calc
      T (causalLowerCauchyEvolution s (causalBoundedChainCoordinate j u)) =
          T (causalBoundedChainCoordinate j
            (causalBoundedChainExponential ((s : ℝ) : ℂ) u)) :=
        congrArg T (causalBoundedEntireOrbit_eq_evolution j u s).symm
      _ = causalBoundedChainCoordinate j (causalBoundedChainExponential (-((s : ℝ) : ℂ))
            (causalBoundedChainExponential ((s : ℝ) : ℂ) u)) :=
        congrArg (fun Q : causalBoundedChain →L[ℂ] hardyL2ᗮ =>
          Q (causalBoundedChainExponential ((s : ℝ) : ℂ) u)) hT
      _ = causalBoundedChainCoordinate j u :=
        congrArg (causalBoundedChainCoordinate j)
          (causalBoundedChainExponential_neg_apply ((s : ℝ) : ℂ) u)
  have hid : causalBoundedCoordinateExtension j (ContinuousLinearMap.id ℂ causalBoundedChain)
      (ContinuousLinearMap.id ℂ (hardyL2ᗮ)) := by
    apply ContinuousLinearMap.ext
    intro u
    rfl
  exact causalBoundedCoordinateExtension_subsingleton j _ hleft hid

/-- A real-time chain evolution has a bounded extension to original L2 data
exactly at nonnegative times, regardless of the derivative coordinate used. -/
theorem causalBoundedChainExponential_real_has_coordinateExtension_iff (j : ℕ) (t : ℝ) :
    (∃ T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ,
      causalBoundedCoordinateExtension j (causalBoundedChainExponential (t : ℂ)) T) ↔ 0 ≤ t := by
  constructor
  · rintro ⟨T, hT⟩
    by_contra hn
    have ht : t < 0 := lt_of_not_ge hn
    let s : ℝ≥0 := ⟨-t, le_of_lt (neg_pos.mpr ht)⟩
    have hs : (s : ℝ) = -t := rfl
    have hback : causalBoundedCoordinateExtension j
        (causalBoundedChainExponential (-((s : ℝ) : ℂ))) T := by
      simpa only [hs, Complex.ofReal_neg, neg_neg] using hT
    have heq := backward_extension_left_inverse j s T hback
    have hinj : Function.Injective (causalLowerCauchyEvolution s) := by
      intro x y hxy
      have hx := congrArg (fun Q : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => Q x) heq
      have hy := congrArg (fun Q : hardyL2ᗮ →L[ℂ] hardyL2ᗮ => Q y) heq
      exact hx.symm.trans ((congrArg T hxy).trans hy)
    have hz : s = 0 := (causalLowerCauchyEvolution_injective_iff s).mp hinj
    have hr := congrArg (fun a : ℝ≥0 => (a : ℝ)) hz
    change -t = 0 at hr
    linarith
  · intro ht
    exact ⟨causalLowerCauchyEvolution ⟨t, ht⟩, evolution_extends j ⟨t, ht⟩⟩

end
end RHTower.FokasLenells
