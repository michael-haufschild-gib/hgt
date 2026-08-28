# HB Peierls–Darboux orbit optical transgression (HC18, 2026-08-28)

Formalized and wired `ThetaCuspHawkingBMPeierlsDarbouxOrbitOpticalTransgression.lean`.

Exact local law: with `a=Re q`, `b=Im q`, reflected Darboux weights `c,d`, `y=12*horizonAmplitude^2*omega`, and `N=8n+5`,
`b^2(c^2+y^2)(d^2+y^2)*phaseMismatch*N = -16*y^2*a^2*(1-a)^2*Re(orbitTrace)`.

Define `hbXiPeierlsFESchwarzOrbitRadiationPower = -Re(orbitTrace)*‖radiation psi‖^2`. Then
`orbitRadiationPower = 4*(8n+5)*d4BMXiTransportedOrthogonalHelicityMixingFlux`.
It is nonnegative, strictly positive for every radiating tilted Xi copy, and zero iff the copy is critical.

Canonical full-Einstein unit-amplitude, zero-auxiliary-mixing reporter is premise-free:
- per-copy zero iff `Re q=1/2`;
- universal zero iff RH;
- universal zero exactly iff HC17 equal-positive-weight Ward identity.

Main theorems:
- `hbXiPeierlsFESchwarzOrbitDarbouxPhaseMismatch_optical_eq`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_eq_flux`
- `hbXiPeierlsFESchwarzOrbitRadiationPower_pos_of_tilt`
- `hbXiPeierlsFESchwarzOrbitDarbouxRadiation_optical_eq`
- `forall_hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rh`
- `hbXiPeierlsFESchwarzCanonicalOpticalWard_iff_positiveWard`

Verification: direct Lean passed; target build passed (11905 jobs); seven endpoint axiom reports only `[propext, Classical.choice, Quot.sound]`; forbidden/diff gates clean; global lint only unrelated umbrella reachability failures.

Cards:
- `docs/drafts/pipeline/3-formalized/hb-peierls-darboux-orbit-optical-transgression.md`
- `docs/drafts/pipeline/5-failed/hb-passive-darboux-optical-stationarity-no-go.md`

Positive survivor: derive a signed cross-sector action/current cancellation; passive channel powers are strictly positive off wall and cannot supply stationarity. Frontier map remains read-only.