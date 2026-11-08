import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanSmallSource
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanRegularity
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Poles of the small-height Mellin continuation

Subtracting the entire large-height tail preserves the full arithmetic pole multiplicities of the physical Mellin continuation.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual small-height continuation is meromorphic on the entire physical plane. -/
theorem meromorphic_narainMeanSmallMellin (Y Z : Height) :
    Meromorphic (narainMeanSmallMellin Y Z) := by
  intro s
  have hshift : MeromorphicAt
      (fun z : ℂ => narainMellinMeanRegularPart Y Z (z - 1 / 2)) s := by
    simpa only [sub_eq_add_neg] using (meromorphicAt_comp_add (a := s) (h := -(1 / 2 : ℂ))).mpr
      (meromorphic_narainMellinMeanRegularPart Y Z (s + -(1 / 2 : ℂ)))
  exact hshift.sub ((differentiable_narainMeanMellinTail Y Z).analyticAt s).meromorphicAt

/-- The cutoff continuation has no positive real singularity, including the removed main pole. -/
theorem analyticAt_narainMeanSmallMellin_of_real
    (Y Z : Height) {σ : ℝ} (hσ : 0 < σ) :
    AnalyticAt ℂ (narainMeanSmallMellin Y Z) (σ : ℂ) := by
  have hshift : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) (σ : ℂ) := by fun_prop
  have hreg := AnalyticAt.comp (g := narainMellinMeanRegularPart Y Z)
    (f := fun s : ℂ => s - 1 / 2) (x := (σ : ℂ))
    (analyticAt_narainMellinMeanRegularPart_of_real Y Z hσ) hshift
  exact hreg.sub ((differentiable_narainMeanMellinTail Y Z).analyticAt (σ : ℂ))

/-- Removing the actual large-height tail preserves every arithmetic pole and its full multiplicity. -/
theorem narainMeanSmallMellin_full_order (p : Resonance) (Y Z : Height) :
    meromorphicOrderAt (narainMeanSmallMellin Y Z) (p.val + 1 / 2) =
      -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  let Q : ℂ → ℂ := fun u => -narainMeanMellinTail Y Z (u + 1 / 2)
  have hQ : AnalyticAt ℂ Q p.val :=
    (AnalyticAt.comp (g := narainMeanMellinTail Y Z)
      (f := fun u : ℂ => u + 1 / 2) (x := p.val)
      ((differentiable_narainMeanMellinTail Y Z).analyticAt (p.val + 1 / 2))
      (by fun_prop)).neg
  have heq : (fun u : ℂ => narainMeanSmallMellin Y Z (u + 1 / 2)) =
      narainMellinMeanRegularPart Y Z + Q := by
    funext u
    simp only [narainMeanSmallMellin, add_sub_cancel_right, Pi.add_apply, Q, sub_eq_add_neg]
  have hord : meromorphicOrderAt (narainMellinMeanRegularPart Y Z) p.val =
      meromorphicOrderAt (narainMellinMean Y Z) p.val := by
    rw [narainMellinMeanRegularPart_full_order, narainMellinMean_full_order]
  have hneg : meromorphicOrderAt (narainMellinMeanRegularPart Y Z) p.val < 0 := by
    obtain ⟨n, hn⟩ := narainMellinMean_pole p Y Z
    rw [hord, hn]
    norm_cast
    omega
  rw [← GaloisForLFunctions.HTGeometry.meromorphicOrderAt_comp_add
    (narainMeanSmallMellin Y Z) p.val (1 / 2), heq,
    meromorphicOrderAt_add_eq_left_of_lt hQ.meromorphicAt
      (hneg.trans_le hQ.meromorphicOrderAt_nonneg), narainMellinMeanRegularPart_full_order]

#print axioms meromorphic_narainMeanSmallMellin
#print axioms analyticAt_narainMeanSmallMellin_of_real
#print axioms narainMeanSmallMellin_full_order
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
