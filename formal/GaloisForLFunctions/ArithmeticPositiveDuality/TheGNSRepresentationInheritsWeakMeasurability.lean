import GaloisForLFunctions.ArithmeticPositiveDuality.TheHilbertSpaceOfAPositiveDefiniteFunction
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Topology.Sequences

/-!
# Weak measurability of GNS representations

Finite GNS coefficients are sums of translates of the defining positive-definite
function. Hilbert completion preserves their scalar measurability, without a
separability assumption on the completed space.
-/

open Complex MeasureTheory Filter Topology UniformSpace
open scoped InnerProductSpace

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositiveDuality


variable {G : Type*} [Group G] (Φ : PosDefFn G)

/-- A pre-GNS matrix coefficient is a finite sum of translates of the original function. -/
lemma inner_preGNS_gnsRep (g : G) (x y : PreGNS Φ) :
    ⟪(x : GNSHilbert Φ), gnsRep Φ g (y : GNSHilbert Φ)⟫_ℂ =
      (toF Φ x).sum fun i a => (toF Φ y).sum fun j b =>
        star a * Φ.toFun (i⁻¹ * (g * j)) * b := by
  rw [gnsRep_coe, Completion.inner_coe, inner_eq_gnsInner]
  unfold gnsInner
  rw [toF_gnsTranslate]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro j a b; ring)]

/-- Every Hilbert vector is the norm limit of finite pre-GNS vectors. -/
lemma exists_preGNS_seq_tendsto (x : GNSHilbert Φ) :
    ∃ u : ℕ → PreGNS Φ, Tendsto (fun n => (u n : GNSHilbert Φ)) atTop (𝓝 x) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (Completion.denseRange_coe x)
  choose v hv using hu
  exact ⟨v, by simpa only [hv] using hlim⟩

/-- Measurability of translated cyclic coefficients extends to all GNS matrix coefficients
by finite sums and norm approximation; no separability of the Hilbert space is required. -/
theorem measurable_inner_gnsRep {A : Type*} [MeasurableSpace A] (u : A → G)
    (hΦ : ∀ g h : G, Measurable fun a => Φ.toFun (g⁻¹ * (u a * h)))
    (x y : GNSHilbert Φ) : Measurable fun a => ⟪x, gnsRep Φ (u a) y⟫_ℂ := by
  have hpre (v w : PreGNS Φ) :
      Measurable fun a => ⟪(v : GNSHilbert Φ), gnsRep Φ (u a) (w : GNSHilbert Φ)⟫_ℂ := by
    simp_rw [inner_preGNS_gnsRep, Finsupp.sum]
    exact Finset.measurable_sum _ fun g _ => Finset.measurable_sum _ fun h _ =>
      (measurable_const.mul (hΦ g h)).mul measurable_const
  obtain ⟨v, hv⟩ := exists_preGNS_seq_tendsto Φ x
  obtain ⟨w, hw⟩ := exists_preGNS_seq_tendsto Φ y
  apply measurable_of_tendsto_metrizable (fun n => hpre (v n) (w n))
  apply tendsto_pi_nhds.mpr
  intro a
  exact hv.inner (((gnsRep Φ (u a)).continuous.tendsto y).comp hw)

/-- A Borel positive-definite function has Borel matrix coefficients throughout its GNS space. -/
theorem measurable_gnsRep_coefficient [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [ContinuousMul G] (hΦ : Measurable Φ.toFun) (x y : GNSHilbert Φ) :
    Measurable fun g => ⟪x, gnsRep Φ g y⟫_ℂ := by
  apply measurable_inner_gnsRep Φ id _ x y
  intro g h
  exact hΦ.comp ((continuous_const.mul (continuous_id.mul continuous_const)).measurable)

#print axioms measurable_inner_gnsRep
#print axioms measurable_gnsRep_coefficient
end GaloisForLFunctions.ArithmeticPositiveDuality
