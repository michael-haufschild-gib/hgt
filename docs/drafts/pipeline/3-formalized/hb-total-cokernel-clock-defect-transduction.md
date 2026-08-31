# HB total-cokernel/source-clock transduction

- **ID:** HB-COKERNEL-CLOCK-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB literal Einstein--Teukolsky source producer
- **Statement:** The complete target-independent third-order `++-` Peierls cokernel orbit is the negative of an explicit strictly positive susceptibility times the squared norm of the literal source-FE centered-QNM clock defect.

## Goal

Close the invariant bridge between two already independent RH chains:

1. literal total third-order Einstein--Teukolsky causal cokernel orbit;
2. one source-predeclared nonzero physical-clock FE covariance law.

For `K_n(q)` the canonical full-cokernel unit-carrier orbit cut, `D_n(q)` the reflected
source-FE centered-clock defect coefficient, `S_n(q)` the Peierls/optical susceptibility,
`W_n(q)` the canonical Ward-energy multiplier, and `kappa(q)` the nowhere-zero literal source
FE cocycle, prove unconditionally

`K_n(q) = -((Sigma_n(q) * Complex.normSq (D_n(q)) : Real) : Complex)`,

where

`Sigma_n(q) = 4 * S_n(q) * W_n(q) / Complex.normSq (kappa(q)) > 0`.

Then prove

`K_n(q)=0 <-> D_n(q)=0 <-> sourceFE (U_1 e_q)=U_1(sourceFE e_q)`

and its global form

`(forall q, K_n(q)=0) <-> HBXiPeierlsUnitSourceFEPhysicalClockStepCovariant 0 1 <-> RH`.

This is non-circular: equality and positivity use explicit source, cocycle, radiation, and total
cokernel formulas only. It does not assert the remaining dynamical sign. It reduces that burden to
one invariant statement: physical Einstein--Teukolsky passivity must give the orientation opposite
to the algebraically forced `K_n(q) <= 0`; simultaneous signs then force `K_n(q)=0` and RH.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Theorem and proof `[PROVED HERE]`

Corpus-derived identities:

- `K_n = -S_n * opticalPower_n` for the complete target-independent cokernel orbit;
- `opticalPower_n = W_n * wardCharge^2`;
- `wardCharge = 1 - 2 Re(q) = -2 (Re(q)-1/2)`;
- `D_n = I * (Re(q)-1/2) * kappa(q)`;
- `kappa(q) != 0`, `S_n(q)>0`, and `W_n(q)>0`.

Multiplicativity of `Complex.normSq` gives

`normSq(D_n)= (Re(q)-1/2)^2 * normSq(kappa(q))`.

Substitution yields the displayed factor `Sigma_n`. No division by the tilt occurs, so the formula
is regular on critical fibres. The result uses the total retarded-minus-advanced cokernel cut and is
therefore independent of the common direct Einstein third jet and of perturbative channel
coordinates.

More explicitly, put `t(q)=Re(q)-1/2`. The third and fourth corpus identities give

`wardCharge(q)^2 = (-2 t(q))^2 = 4 t(q)^2`

and

`normSq(D_n(q)) = t(q)^2 normSq(kappa(q))`.

Since `normSq(kappa(q))>0`, division by this factor is valid. Therefore

`K_n(q) = -S_n(q) W_n(q) 4 t(q)^2`

`         = -(4 S_n(q) W_n(q)/normSq(kappa(q))) normSq(D_n(q))`.

Positivity of `S_n`, `W_n`, and `normSq(kappa)` proves `Sigma_n(q)>0`. Hence
`K_n(q)=0` iff `normSq(D_n(q))=0` iff `D_n(q)=0`. Existing exact coefficient and
single-packet theorems identify the last equality with commutation of source FE and one unit
physical-clock step. Universal quantification over Xi fibres is the existing unit-clock covariance
endpoint, already equivalent to RH. No analytic assumption or physical sign is used in this proof.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTotalCokernelClockDefectTransduction`

Principal declarations:

- `hbXiPeierlsClockDefectToFullCokernelSusceptibility_pos`;
- `normSq_hbXiPeierlsSourceFECenteredQNMClockDefectCoefficient_eq`;
- `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_clockDefectEnergy`;
- `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_clockDefect`;
- `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_unitClockStep`;
- `forall_hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_zero_iff_unitClockStepCovariant`.

Audit, 2026-08-30:

- direct `lake env lean` check: PASS;
- targeted module `lake build`: PASS;
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- wired into `GaloisForLFunctions.RHTower` umbrella;
- corpus research index returns this declaration as exact total-cokernel/clock-energy bridge.

## RH proof burden after this theorem

Discharged premise: coefficient-exact complete-cokernel-to-finite-clock transduction inside the
canonical receiver. Subsequent one-sided causal-split no-go shows this canonical realization cannot
itself be treated as physical: its zero advanced response violates causal Schwarz exchange. The
surviving HB burden therefore has two inseparable parts: derive a genuinely two-sided reciprocal,
Schwarz-exchanged Einstein--Teukolsky jump from literal source data, then prove its complete cut has
the opposite nonnegative orientation and agrees with this receiver. Existing corpus classification
shows universal unit BM incidence for an arbitrary abstract pair in that class is already
RH-equivalent, so an abstract response choice is not a producer.

Hostile tests passed before proof:

- mixed `+-` monodromy cannot supply the cut: Peierls skewness makes it a self-pairing and kills it;
- a named AIME/cascade/direct channel is invalid because field redefinitions move those channels;
- critical fibres cause no `0/0`: only the nowhere-zero source cocycle is divided out;
- off wall, positive susceptibility forces strict negative causal orbit exactly when the clock
  defect is nonzero;
- current primary literature supplies second-order Teukolsky excitation, AIME, and conserved QNM
  bilinear forms, but no total third-order source-FE/Xi clock transduction (arXiv:2401.15516,
  arXiv:2112.11168, arXiv:2210.15935; audited 2026-08-30).

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** pending

## Log

- 2026-08-30 — created directly in 1-in-progress after corpus and primary-literature audits.
- 2026-08-30 — coefficient-exact proof completed, formalized, axiom-audited, targeted build passed,
  and card promoted to stage 3.
