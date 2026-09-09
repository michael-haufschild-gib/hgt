import GaloisForLFunctions.RHTower.FokasLenellsCausalRationalGraphCore
import GaloisForLFunctions.RHTower.FokasLenellsCauchyCoreRange

/-! Actual finite inner multipliers on real-line L², for rational Cauchy pole cancellation.
Their norm and spectral-gap properties hold on the full data space. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- A finite composition of actual real-line inner multipliers at upper-half-plane poles. -/
def causalFiniteBlaschke : List {z : ℂ // 0 < z.im} → (SoninL2 →L[ℂ] SoninL2)
  | [] => ContinuousLinearMap.id ℂ SoninL2
  | w :: ws => (blaschkeMulInv w.val).comp (causalFiniteBlaschke ws)

/-- Every finite pole-cancelling multiplier preserves the actual L² norm. -/
theorem norm_causalFiniteBlaschke (ws : List {z : ℂ // 0 < z.im}) (u : SoninL2) :
    ‖causalFiniteBlaschke ws u‖ = ‖u‖ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ‖blaschkeMulInv w.val (causalFiniteBlaschke ws u)‖ = _
    rw [norm_blaschkeMulInv w.property.ne', ih]

/-- The actual finite operator is pointwise multiplication by the finite product of inner factors. -/
theorem causalFiniteBlaschke_ae (ws : List {z : ℂ // 0 < z.im}) (u : SoninL2) :
    (causalFiniteBlaschke ws u : ℝ → ℂ) =ᵐ[volume]
      fun x => (ws.map (fun w => blaschkeSymbolInv w.val x)).prod * (u : ℝ → ℂ) x := by
  induction ws with
  | nil =>
    change (u : ℝ → ℂ) =ᵐ[volume] fun x => (1 : ℂ) * (u : ℝ → ℂ) x
    simp only [one_mul]
    exact Filter.EventuallyEq.rfl
  | cons w ws ih =>
    filter_upwards [coeFn_blaschkeMulInv w.val (causalFiniteBlaschke ws u), ih] with x hx hi
    change (blaschkeMulInv w.val (causalFiniteBlaschke ws u) : ℝ → ℂ) x = _
    rw [hx, hi]
    simp only [List.map_cons, List.prod_cons, mul_assoc]

/-- Concatenation of the pole lists equals composition of the actual multipliers. -/
theorem causalFiniteBlaschke_append (ws vs : List {z : ℂ // 0 < z.im}) (u : SoninL2) :
    causalFiniteBlaschke (ws ++ vs) u = causalFiniteBlaschke ws (causalFiniteBlaschke vs u) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change blaschkeMulInv w.val (causalFiniteBlaschke (ws ++ vs) u) =
      blaschkeMulInv w.val (causalFiniteBlaschke ws (causalFiniteBlaschke vs u))
    rw [ih]

/-- Actual finite pole-cancelling multipliers commute on every real-line L² datum. -/
theorem causalFiniteBlaschke_commute (ws vs : List {z : ℂ // 0 < z.im}) (u : SoninL2) :
    causalFiniteBlaschke ws (causalFiniteBlaschke vs u) =
      causalFiniteBlaschke vs (causalFiniteBlaschke ws u) := by
  apply Lp.ext
  filter_upwards [causalFiniteBlaschke_ae ws (causalFiniteBlaschke vs u),
    causalFiniteBlaschke_ae vs u, causalFiniteBlaschke_ae vs (causalFiniteBlaschke ws u),
    causalFiniteBlaschke_ae ws u] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

private theorem finite_mem_hardy (ws : List {z : ℂ // 0 < z.im})
    (u : SoninL2) (hu : u ∈ hardyL2) : causalFiniteBlaschke ws u ∈ hardyL2 := by
  induction ws with
  | nil => exact hu
  | cons w ws ih => exact blaschkeMulInv_mem_hardyL2 w.property ih

/-- Every actual finite pole-cancelling product preserves the upper Hardy subspace. -/
theorem causalFiniteBlaschke_mem_hardy (ws : List {z : ℂ // 0 < z.im}) (u : UpperHardyL2) :
    causalFiniteBlaschke ws u.val ∈ hardyL2 := finite_mem_hardy ws u.val u.property

/-- Every entire-core datum retains an actual spectral zero gap after finite pole cancellation. -/
theorem causalFiniteBlaschke_core_zeroGap (ws : List {z : ℂ // 0 < z.im})
    (u : rawComplexEntireCore) :
    ∃ b : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), dist x 0 < Real.exp b →
      (causalFiniteBlaschke ws u.val : ℝ → ℂ) x = 0 := by
  obtain ⟨b, hb⟩ := rawComplexEntireCore_exists_zeroGap u
  refine ⟨b, ?_⟩
  filter_upwards [causalFiniteBlaschke_ae ws u.val, hb] with x hx hg
  intro hxb
  rw [hx, hg hxb, mul_zero]

end
end RHTower.FokasLenells
