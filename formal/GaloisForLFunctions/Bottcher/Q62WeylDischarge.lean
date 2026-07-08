/-
# q62 — the Brolin support route, with Weyl's lemma discharged

`weylOnBall_greenFunctionDyn` (Brolin/WeylLemma) proves `WeylOnBall (greenFunctionDyn c)`
unconditionally, so the `hWeyl` hypothesis threaded through the GAP-A support theorem and
its q62 consumers is now automatic.  This module supplies the `hWeyl`-free forms.

Two analytic inputs remain, of very different reach:

* `volume (filledJulia c) = 0` — Julia-set Lebesgue-nullity.  TRUE and hard only for
  **disconnected/hyperbolic-empty-interior** `c` (it is the Mañé/pressure contraction);
  **FALSE** for connected `c` in a hyperbolic component, where `K_c` has positive area —
  precisely the both-connected regime the q62 consumers (`Q62BrolinRootTower`) live in.
* `EquilibriumPotentialVanishesAe c a` — Frostman's equilibrium identity `Uᵘ = 0` a.e. on
  `K_c` (Robin constant `= -log cap K_c = 0`).  TRUE for **every** `c`, positive-area
  `K_c` included.  This is the correct general GAP-A input; it makes the smooth Riesz
  identity — hence the whole support route and `LimitingBrolinMeasureAtSupportsJulia` —
  unconditional across all three q62 regimes, with no Julia-nullity.

The null form is kept for the disconnected lane; the Frostman form is the general one.
-/
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
import GaloisForLFunctions.Bottcher.Q62BrolinSupportDischarge

open MeasureTheory Complex Filter Metric Set

namespace Bottcher

noncomputable section

/-! ## Julia-nullity form (disconnected lane) -/

/-- **The q62 Brolin support input from Julia-nullity alone.**  For every target `a`, the
Brolin measure charges every Julia-frontier ball — conditional only on `volume(filledJulia c)=0`
(Weyl's lemma is discharged internally).  Serves the disconnected lane only. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null (c a : ℂ)
    (hnull : volume (filledJulia c) = 0) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null_of_weyl c a hnull
    (weylOnBall_greenFunctionDyn c)

/-- `∀`-fixed-point form consumed by the q62 both-connected capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null
    (c : ℂ) (hnull : volume (filledJulia c) = 0) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a _ => limitingBrolinMeasureAtSupportsJulia_of_filledJulia_null c a hnull

/-- **Backward-orbit density from Julia-nullity alone**, targets chosen internally. -/
theorem exists_fixedPoint_backwardOrbitDense_of_filledJulia_null
    {c : ℂ} (hnull : volume (filledJulia c) = 0) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a :=
  exists_fixedPoint_backwardOrbitDense_of_filledJulia_null_of_weyl hnull
    (weylOnBall_greenFunctionDyn c)

/-! ## Frostman-equilibrium form (all regimes)

The Julia-null route above cannot serve the both-connected regime (`c ∈ M` with
positive-area `K_c`).  The route below does: it names the *true* potential-theoretic
fact and derives the whole support datum from it for every `c`. -/

/-- **Frostman's equilibrium identity (a.e. form).**  The logarithmic potential of the
Brolin (equilibrium) measure vanishes Lebesgue-a.e. on the filled Julia set: `Uᵘ = 0`
q.e. on `K_c` (Robin constant `= -log cap K_c = 0`, since `cap K_c = 1`), hence a.e.
This is TRUE for every `c` — hyperbolic-interior `c`, where `K_c` has positive area,
included — unlike `volume (filledJulia c) = 0`. -/
def EquilibriumPotentialVanishesAe (c a : ℂ) : Prop :=
  ∀ᵐ z ∂(volume : Measure ℂ), z ∈ filledJulia c →
    logPotential (limitingBrolinMeasureAt c a) z = 0

/-- The a.e. potential representation `G_c = −Uᵘ` on all of `ℂ`: the basin representation
(everywhere off `K_c`) glued to Frostman-vanishing (a.e. on `K_c`, where `G_c = 0`). -/
theorem green_eq_neg_logPotential_limitingBrolinMeasureAt_ae (c a : ℂ)
    (hfrost : EquilibriumPotentialVanishesAe c a) :
    (fun z => greenFunctionDyn c z)
      =ᵐ[volume] fun z => - logPotential (limitingBrolinMeasureAt c a) z := by
  filter_upwards [hfrost] with z hz
  by_cases hK : z ∈ filledJulia c
  · rw [(greenFunctionDyn_eq_zero_iff c z).mpr hK, hz hK, neg_zero]
  · exact green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin hK

/-- **Unconditional-modulo-Frostman Riesz identity.**  `limitingBrolinMeasureAt c a`
is the smooth-distributional `(2π)⁻¹ ΔG_c`, for every `c` — no Julia-nullity. -/
theorem isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_equilibriumVanishes (c a : ℂ)
    (hfrost : EquilibriumPotentialVanishesAe c a) :
    IsRieszMeasureOfSmooth (limitingBrolinMeasureAt c a) (greenFunctionDyn c) := by
  have hcarrier : limitingBrolinMeasureAt c a (Metric.closedBall 0 (max 2 ‖c‖))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
      (limitingBrolinMeasureAt_filledJulia_compl c a)
  exact isRieszMeasureOfSmooth_of_potentialRep_ae_carrier (limitingBrolinMeasureAt c a)
    hcarrier _ (green_eq_neg_logPotential_limitingBrolinMeasureAt_ae c a hfrost)

/-- **GAP-A support theorem, Frostman form** — valid for ALL `c` (Weyl discharged). -/
theorem frontier_filledJulia_subset_support_limitingBrolinMeasureAt_of_equilibriumVanishes
    (c a : ℂ) (hfrost : EquilibriumPotentialVanishesAe c a) :
    frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support :=
  frontier_filledJulia_subset_support_of_isRieszMeasureOfSmooth
    (isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_equilibriumVanishes c a hfrost)
    (weylOnBall_greenFunctionDyn c)

/-- **The q62 both-connected support input, Frostman form.**  `LimitingBrolinMeasureAtSupportsJulia`
for every `c`, conditional only on the true general equilibrium-potential vanishing —
the both-connected regime where `volume (filledJulia c) = 0` is false is now covered. -/
theorem limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes (c a : ℂ)
    (hfrost : EquilibriumPotentialVanishesAe c a) :
    LimitingBrolinMeasureAtSupportsJulia c a :=
  frontier_filledJulia_subset_support_limitingBrolinMeasureAt_of_equilibriumVanishes c a hfrost

/-- `∀`-fixed-point Frostman form consumed by the both-connected capstones. -/
theorem forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes
    (c : ℂ) (hfrost : ∀ a : ℂ, quadratic c a = a → EquilibriumPotentialVanishesAe c a) :
    ∀ a : ℂ, quadratic c a = a → LimitingBrolinMeasureAtSupportsJulia c a :=
  fun a ha => limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes c a (hfrost a ha)

/-- **Backward-orbit density, Frostman form**, targets chosen internally. -/
theorem exists_fixedPoint_backwardOrbitDense_of_equilibriumVanishes
    {c : ℂ}
    (hfrost : ∀ a : ℂ, quadratic c a = a → EquilibriumPotentialVanishesAe c a) :
    ∃ a : ℂ, quadratic c a = a ∧ BackwardOrbitDense c a :=
  exists_fixedPoint_backwardOrbitDense_of_limitingBrolinMeasureAtSupportsJulia_all
    (forall_fixedPoint_limitingBrolinMeasureAtSupportsJulia_of_equilibriumVanishes c hfrost)

end

end Bottcher
