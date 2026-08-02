import GaloisForLFunctions.HTGeometry.PointedIncidenceConstancy
import GaloisForLFunctions.HTGeometry.RelativeTwoShiftGaugeCharacterization
import GaloisForLFunctions.HTGeometry.DifferentialIndependence

/-!
# The pointed two-shift incidence fibres

Fix two shifts together with the unit period, rationally independent, and a boundary datum for the
two shift differences.  A *pointed primitive* is an element of the meromorphic field with that
boundary, fixed by the unit period, and with a prescribed value under a constant-separating
evaluation.

Two pointed primitives differ by an element fixed by all three periods, hence by a constant, which
the pointing kills: the ambient pointed fibre has at most one member.  If moreover the given
primitive is hypertranscendental, the fibre inside the differentially algebraic sector is empty.

This is the incidence phase of the fracture: a nonzero relative obstruction on the thin side and a
single canonical point on the ambient side.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The embedded constants of the ambient meromorphic field. -/
def meroConstant (c : ℂ) : meroField (Set.univ : Set ℂ) :=
  algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) (constToAnalytic Set.univ c)

/-- A constant-separating evaluation of the ambient sector. -/
structure ConstantPointing where
  /-- The underlying additive evaluation. -/
  ev : meroField (Set.univ : Set ℂ) → ℂ
  /-- It is additive on differences. -/
  map_sub : ∀ x y, ev (x - y) = ev x - ev y
  /-- It inverts the constant embedding. -/
  eval_const : ∀ c : ℂ, ev (meroConstant c) = c

/-- The pointed primitives of a two-shift boundary inside a sector. -/
def shiftIncidence (S : Set (meroField (Set.univ : Set ℂ))) (sigma tau : ℂ)
    (bs bt : meroField (Set.univ : Set ℂ)) (P : ConstantPointing) (p : ℂ) :
    Set (meroField (Set.univ : Set ℂ)) :=
  {G | G ∈ S ∧ addTranslationMeroEquiv sigma G - G = bs
    ∧ addTranslationMeroEquiv tau G - G = bt
    ∧ addTranslationMeroEquiv 1 G - G = 0 ∧ P.ev G = p}

/-- The differentially algebraic sector of the ambient field. -/
def daSector : Set (meroField (Set.univ : Set ℂ)) :=
  {x | DifferentialAlgebraicOver (RatFunc ℂ) x}

/-- A sector fibre sits inside the ambient one. -/
theorem shiftIncidence_subset_univ {S : Set (meroField (Set.univ : Set ℂ))} {sigma tau : ℂ}
    {bs bt : meroField (Set.univ : Set ℂ)} {P : ConstantPointing} {p : ℂ} :
    shiftIncidence S sigma tau bs bt P p ⊆ shiftIncidence Set.univ sigma tau bs bt P p := by
  rintro G ⟨-, h1, h2, h3, h4⟩
  exact ⟨Set.mem_univ G, h1, h2, h3, h4⟩

/-- **The pointed ambient fibre has at most one member.** -/
theorem shiftIncidence_subsingleton {sigma tau : ℂ}
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    {S : Set (meroField (Set.univ : Set ℂ))} {bs bt : meroField (Set.univ : Set ℂ)}
    {P : ConstantPointing} {p : ℂ} {G H : meroField (Set.univ : Set ℂ)}
    (hG : G ∈ shiftIncidence S sigma tau bs bt P p)
    (hH : H ∈ shiftIncidence S sigma tau bs bt P p) : G = H := by
  obtain ⟨-, hGs, hGt, hG1, hGp⟩ := hG
  obtain ⟨-, hHs, hHt, hH1, hHp⟩ := hH
  refine eq_of_fixed_rankThree_of_sub_const hindep ?_ ?_
  · intro i
    have hshift : ∀ q : ℂ, addTranslationMeroEquiv q G - G = addTranslationMeroEquiv q H - H →
        addTranslationMeroEquiv q (G - H) = G - H := by
      intro q hq
      rw [map_sub]
      have hqq : addTranslationMeroEquiv q G - addTranslationMeroEquiv q H = G - H := by
        have := hq
        linear_combination this
      exact hqq
    fin_cases i
    · exact hshift 1 (by rw [hG1, hH1])
    · exact hshift sigma (by rw [hGs, hHs])
    · exact hshift tau (by rw [hGt, hHt])
  · intro c hc
    have hev : P.ev (G - H) = 0 := by
      rw [P.map_sub, hGp, hHp, sub_self]
    have hcev : P.ev (meroConstant c) = c := P.eval_const c
    rw [meroConstant] at hcev
    rw [hc] at hcev
    rw [hev] at hcev
    exact hcev.symm

/-- **The pointed ambient fibre of a primitive is exactly that primitive.** -/
theorem shiftIncidence_ambient_eq_singleton {sigma tau : ℂ}
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    {F : meroField (Set.univ : Set ℂ)} {P : ConstantPointing}
    (h1 : addTranslationMeroEquiv 1 F - F = 0) :
    shiftIncidence Set.univ sigma tau (addTranslationMeroEquiv sigma F - F)
      (addTranslationMeroEquiv tau F - F) P (P.ev F) = {F} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Set.mem_univ F, rfl, rfl, h1, rfl⟩, ?_⟩
  intro G hG
  exact shiftIncidence_subsingleton hindep hG ⟨Set.mem_univ F, rfl, rfl, h1, rfl⟩

/-- **The pointed differentially algebraic fibre of a hypertranscendental primitive is empty.** -/
theorem shiftIncidence_da_eq_empty {sigma tau : ℂ}
    (hindep : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    {F : meroField (Set.univ : Set ℂ)} {P : ConstantPointing}
    (h1 : addTranslationMeroEquiv 1 F - F = 0)
    (hHT : HypertranscendentalOver (RatFunc ℂ) F) :
    shiftIncidence daSector sigma tau (addTranslationMeroEquiv sigma F - F)
      (addTranslationMeroEquiv tau F - F) P (P.ev F) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun G hG => ?_
  have hGF : G = F :=
    shiftIncidence_subsingleton hindep (shiftIncidence_subset_univ hG)
      ⟨Set.mem_univ F, rfl, rfl, h1, rfl⟩
  have hDA : DifferentialAlgebraicOver (RatFunc ℂ) G := hG.1
  rw [hGF] at hDA
  exact hHT hDA

/-- **The pointing is inhabited**, so the incidence statements are not vacuous: the constants embed
as a rational subspace, and any rational left inverse of that embedding separates them. -/
theorem nonempty_constantPointing : Nonempty ConstantPointing := by
  classical
  have hmero_inj : Function.Injective meroConstant := by
    intro a b hab
    rw [meroConstant, meroConstant] at hab
    have hsub : constToAnalytic Set.univ a = constToAnalytic Set.univ b :=
      (IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ))
        (meroField Set.univ)) hab
    have hv := congrArg Subtype.val hsub
    change ((fun _ : ℂ => a : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
      = ((fun _ : ℂ => b : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) at hv
    rw [Germ.coe_eq] at hv
    exact eventually_principal.mp hv 0 (Set.mem_univ 0)
  let f : ℂ →+ meroField (Set.univ : Set ℂ) :=
    { toFun := meroConstant
      map_zero' := by
        rw [meroConstant, map_zero, map_zero]
      map_add' := by
        intro x y
        rw [meroConstant, meroConstant, meroConstant, map_add, map_add] }
  let e : ℂ →ₗ[ℚ] meroField (Set.univ : Set ℂ) := f.toRatLinearMap
  have hker : e.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hmero_inj
  obtain ⟨g, hg⟩ := e.exists_leftInverse_of_injective hker
  refine ⟨⟨fun x => g x, fun x y => by rw [map_sub], fun c => ?_⟩⟩
  have hc := congrArg (fun F : ℂ →ₗ[ℚ] ℂ => F c) hg
  exact hc

end

end GaloisForLFunctions.HTGeometry
