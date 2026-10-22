import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularFlatReflectionCarrier

/-!
# Single-endpoint seam obstruction for Parikh--Wilczek reflection

The literal singular reflected-Gamma carrier is sourced by the first physical
endpoint winding `exp(-1/x)` at scale `epsilon = x/4`. Direct reciprocal
energy at the same endpoint instead forces `epsilon = x/2`. These scales are
incompatible, so a single literal endpoint event cannot simultaneously carry
the singular source contact and the reciprocal-energy reverse required by the
PW-B chain.

Proof-chain role:
`one literal Hawking endpoint -> singular reflected-Gamma contact + reciprocal
energy seam` is impossible. The remaining source seam must have genuinely
multi-event/nonlocal calibration before fixed-grade partner balance and Xi
occurrence can be attempted.
-/

namespace RHTower

noncomputable section

/-- A direct one-event endpoint seam asks one positive backreaction scale to
produce both reciprocal energy and the literal singular source contact. -/
def PWLiteralSingleEndpointSingularReciprocalSeam : Prop :=
  ∀ x : ℝ, 0 < x → ∃ epsilon : ℝ, 0 < epsilon ∧
    schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon = x⁻¹ ∧
    schwarzschildParikhWilczekWindingTerm 0 epsilon
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) =
        Real.exp (-x⁻¹)

/-- Reciprocal endpoint energy fixes the unique physical backreaction scale. -/
theorem schwarzschildParikhWilczek_endpointScale_eq_half_of_reciprocal
    {x epsilon : ℝ} (hx : 0 < x) (hepsilon : 0 < epsilon)
    (henergy : schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon = x⁻¹) :
    epsilon = x / 2 := by
  rw [schwarzschildParikhWilczekDimensionlessEnergyEndpoint] at henergy
  field_simp [hx.ne', hepsilon.ne'] at henergy
  linarith

/-- The literal first-endpoint contact of the singular reflected-Gamma carrier
fixes a different, unique physical backreaction scale. -/
theorem schwarzschildParikhWilczek_endpointScale_eq_quarter_of_singularContact
    {x epsilon : ℝ} (hx : 0 < x) (hepsilon : 0 < epsilon)
    (hcontact : schwarzschildParikhWilczekWindingTerm 0 epsilon
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint epsilon) =
        Real.exp (-x⁻¹)) : epsilon = x / 4 := by
  rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint 0 hepsilon.ne',
    schwarzschildParikhWilczekEndpointAction_zero] at hcontact
  have harg := Real.exp_injective hcontact
  field_simp [hx.ne', hepsilon.ne'] at harg
  linarith

/-- **Literal one-endpoint seam no-go.** A single physical endpoint cannot
simultaneously realize reciprocal energy and the singular contact required by
the source-native reflected-Gamma carrier. -/
theorem not_PWLiteralSingleEndpointSingularReciprocalSeam :
    ¬ PWLiteralSingleEndpointSingularReciprocalSeam := by
  intro h
  obtain ⟨epsilon, hepsilon, henergy, hcontact⟩ := h 1 (by norm_num)
  have hepsilon_eq : epsilon = 1 / 2 := by
    exact schwarzschildParikhWilczek_endpointScale_eq_half_of_reciprocal
      (by norm_num) hepsilon henergy
  have hepsilon_quarter : epsilon = 1 / 4 := by
    exact schwarzschildParikhWilczek_endpointScale_eq_quarter_of_singularContact
      (by norm_num) hepsilon hcontact
  linarith

end

end RHTower
