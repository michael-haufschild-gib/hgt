import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount
import GaloisForLFunctions.SquareRootThreshold.WindowedWeilFormSliceTransfer
import Zeta23.WeilEF.ZeroSummabilityGen

/-!
# Critical projection preserves every ordinate count

Move each zero horizontally to the critical line and add multiplicities
at collisions. Every ordinate window keeps its exact count. Thus the
critical projection of the zeta divisor provides an unconditional
on-line background with zeta's density and tempered mass.
-/

open Set Finset
open Zeta23
noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open SquareRootThreshold

/-- Horizontal projection onto the critical line. -/
def criticalProjection (z : ℂ) : ℂ := ⟨1 / 2, z.im⟩

/-- The finite fibre of one ordinate, including its full horizontal multiplicity. -/
def ordinateFiber (Z : ZeroConfig) (t : ℝ) : Finset ℂ := by
  classical
  exact (Z.finite_window (t - 1) t).toFinset.filter (fun z => z.im = t)

theorem mem_ordinateFiber {Z : ZeroConfig} {z : ℂ} {t : ℝ} :
    z ∈ ordinateFiber Z t ↔ z ∈ Z.carrier ∧ z.im = t := by
  classical
  simp only [ordinateFiber, mem_filter, Set.Finite.mem_toFinset, mem_inter_iff, mem_setOf_eq]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hz, rfl⟩
    exact ⟨⟨hz, by linarith, le_rfl⟩, rfl⟩

theorem reflect_criticalProjection (z : ℂ) : reflect (criticalProjection z) = criticalProjection z := by
  apply Complex.ext <;> simp [reflect, criticalProjection]
  norm_num

/-- The configuration obtained by moving all zeros to the line and retaining multiplicity. -/
def criticalProjectionConfig (Z : ZeroConfig) : ZeroConfig where
  carrier := criticalProjection '' Z.carrier
  mult := fun z => ∑ ρ ∈ ordinateFiber Z z.im, Z.mult ρ
  one_le_mult := by
    rintro _ ⟨z, hz, rfl⟩
    exact (Z.one_le_mult z hz).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_ordinateFiber.mpr ⟨hz, rfl⟩))
  strip := by
    rintro _ ⟨z, _, rfl⟩
    norm_num [criticalProjection]
  reflect_mem := by
    rintro _ ⟨z, hz, rfl⟩
    rw [reflect_criticalProjection]
    exact ⟨z, hz, rfl⟩
  mult_reflect := by
    rintro _ ⟨z, _, rfl⟩
    rw [reflect_criticalProjection]
  finite_window := by
    intro T₁ T₂
    apply ((Z.finite_window T₁ T₂).image criticalProjection).subset
    rintro _ ⟨⟨z, hz, rfl⟩, hwin⟩
    exact ⟨z, ⟨hz, hwin⟩, rfl⟩

theorem criticalProjectionConfig_onLine (Z : ZeroConfig) :
    ∀ z ∈ (criticalProjectionConfig Z).carrier, z.re = 1 / 2 := by
  rintro _ ⟨z, _, rfl⟩
  rfl

theorem criticalProjectionConfig_window (Z : ZeroConfig) (T₁ T₂ : ℝ) :
    (criticalProjectionConfig Z).window T₁ T₂ = criticalProjection '' Z.window T₁ T₂ := by
  ext z
  constructor
  · rintro ⟨⟨ρ, hρ, rfl⟩, hwin⟩
    exact ⟨ρ, ⟨hρ, hwin⟩, rfl⟩
  · rintro ⟨ρ, ⟨hρ, hwin⟩, rfl⟩
    exact ⟨⟨ρ, hρ, rfl⟩, hwin⟩

/-- Horizontal projection preserves the full count on every ordinate window. -/
theorem criticalProjectionConfig_N (Z : ZeroConfig) (T₁ T₂ : ℝ) :
    (criticalProjectionConfig Z).N T₁ T₂ = Z.N T₁ T₂ := by
  classical
  let S := (Z.finite_window T₁ T₂).toFinset
  have hwin : (criticalProjectionConfig Z).window T₁ T₂ = ↑(S.image criticalProjection) := by
    rw [criticalProjectionConfig_window, Finset.coe_image, Set.Finite.coe_toFinset]
    rfl
  rw [ZeroConfig.N, hwin]
  simp only [Finset.mem_coe]
  rw [finsum_mem_finset_eq_sum, ZeroConfig.N, ZeroConfig.window,
    finsum_mem_eq_finite_toFinset_sum _ (Z.finite_window T₁ T₂)]
  change (∑ z ∈ S.image criticalProjection, ∑ ρ ∈ ordinateFiber Z z.im, Z.mult ρ) =
    ∑ ρ ∈ S, Z.mult ρ
  have hfiber : ∀ z ∈ S.image criticalProjection,
      ordinateFiber Z z.im = S.filter (fun ρ => criticalProjection ρ = z) := by
    rintro _ hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hw' := (Z.finite_window T₁ T₂).mem_toFinset.mp hw
    ext ρ
    simp only [mem_ordinateFiber, mem_filter]
    constructor
    · rintro ⟨hρ, him⟩
      have him' : ρ.im = w.im := him
      refine ⟨(Z.finite_window T₁ T₂).mem_toFinset.mpr ⟨hρ, ?_⟩, ?_⟩
      · simpa only [him'] using hw'.2
      · exact Complex.ext rfl him'
    · rintro ⟨hρ, he⟩
      exact ⟨((Z.finite_window T₁ T₂).mem_toFinset.mp hρ).1, congrArg Complex.im he⟩
  rw [Finset.sum_congr rfl (fun z hz => congrArg (fun F : Finset ℂ => ∑ ρ ∈ F, Z.mult ρ)
    (hfiber z hz))]
  exact Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image criticalProjection)
    (g := criticalProjection) (fun z hz => Finset.mem_image_of_mem criticalProjection hz) _

/-- A local logarithmic count remains a tempered critical configuration after projection. -/
theorem temperedConfig_criticalProjection_of_localCount (Z : ZeroConfig) {A : ℝ}
    (hA : 1 ≤ A) (hcount : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3)) :
    TemperedConfig (criticalProjectionConfig Z) := by
  apply WeilEF.zero_sum_inv_sq_gen _ hA
  intro t
  rw [criticalProjectionConfig_N]
  exact hcount t

/-- The critical projection of the actual zeta divisor is tempered unconditionally. -/
theorem temperedConfig_criticalProjection_zeta :
    TemperedConfig (criticalProjectionConfig zetaZeroConfig) := by
  obtain ⟨A, hA, hcount⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact temperedConfig_criticalProjection_of_localCount zetaZeroConfig hA hcount


end GaloisForLFunctions.ZeroConfigurationGeometry
