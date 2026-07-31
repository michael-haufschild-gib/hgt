# Operational boundary--time capacity law

- **ID:** `operational-boundary-time-capacity-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / OPERATIONAL L-BIT CAPACITY LAW
- **Parent:** `lbit-boundary-temporal-dimension-budget-law`
- **Target paper:** `universal-quantum-recurrence-anatomy`
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NOVELTY AUDIT OPEN]`

## Scientific question

The exact l-bit boundary law proves that resolving one more site can create
\(D_r=2^r\) new rational temporal directions while their total coupling
mass is at most \(K/(2D_r)\).  Exact rational rank is an infinite-time
invariant.  The missing operational question is:

> How many of those directions can a finite-time observer resolve?

## Exact law

Let \(b_{r,S}\), \(S\subseteq F_r\), be the boundary-born coefficient packet,
let
\[
  g_r(x)=4\sum_{S\subseteq F_r}b_{r,S}\chi_S(x),
  \qquad x\in\{\pm1\}^{F_r},
\]
and define the demodulated boundary OTO phase response
\[
  R_{r,t}(x)=\exp\!\bigl(i t g_r(x)\bigr)-1.
\]
For \(A\subseteq F_r\), write
\[
  \widehat R_{r,t}(A)
  =D_r^{-1}\sum_x R_{r,t}(x)\chi_A(x)
\]
and define the resolution-\(\eta\) operational temporal dimension
\[
  N_\eta(r,t)
  =\#\{A:|\widehat R_{r,t}(A)|\ge\eta\}.
\]

The operational capacity law is
\[
  \boxed{
  \eta^2N_\eta(r,t)
  \le
  \left(\frac{2K|t|}{D_r}\right)^2 .
  }
  \tag{OTC}
\]
Consequently, if all \(D_r\) boundary directions are resolved at level
\(\eta>0\), then
\[
  \boxed{
  |t|\ge \frac{\eta}{2K}D_r^{3/2}.
  }
  \tag{FULL}
\]

This replaces the earlier unproved \(D_r^2\) guess by a theorem candidate
whose \(D_r^{3/2}\) exponent follows from exact Walsh--Parseval geometry.

## Proof mechanism

1. Walsh--Parseval gives
   \[
   \sum_A|\widehat R_{r,t}(A)|^2
   =D_r^{-1}\sum_x|R_{r,t}(x)|^2.
   \]
2. The unit-circle chord bound gives
   \[
   |R_{r,t}(x)|\le |t|\,|g_r(x)|
   \le4|t|\sum_S|b_{r,S}|.
   \]
3. The same-packet locality budget gives
   \[
   4\sum_S|b_{r,S}|\le 2K/D_r.
   \]
4. Every coefficient counted by \(N_\eta\) contributes at least
   \(\eta^2\) to Parseval.  Combining the four steps proves `(OTC)`;
   substituting \(N_\eta=D_r\) proves `(FULL)`.

## Why this is one law rather than a collage

The same packet \(b_{r,S}\):

- creates exactly \(D_r\) new completed-time directions;
- pays the quasi-local diameter budget;
- generates the finite-time OTO phase response;
- is constrained by the operational dimension bound.

Exact temporal dimension and observable temporal dimension are therefore
two limits of one boundary channel.  Locality does not remove the distant
directions; it postpones how many can become observable.

## Hostile boundaries

1. \(R_{r,t}\) is the demodulated four-phase/OTOC quotient, not an arbitrary
   laboratory readout.
2. The theorem is for the explicit quasi-local diagonal l-bit field and its
   finite boundary restriction, not a microscopic random-field spin chain.
3. `(OTC)` is an upper bound.  No matching lower construction is claimed.
4. Exact rank remains \(D_r\) for every \(r\); finite-time operational
   dimension depends on \(\eta,t\).
5. External priority must be checked against l-bit OTOC, operator-size and
   Boolean Fourier-spectrum literature.

## Gates

- [x] exact observable and normalization defined
- [x] dependency-closed paper proof identified
- [x] Walsh--Parseval infrastructure formalized
- [x] phase-response capacity theorem formalized
- [x] specialization to explicit infinite field formalized
- [x] axiom audit
- [ ] external priority audit
- [ ] hostile Nature significance review


## Formalization

Implemented in:

- `formal/GaloisForLFunctions/HTGeometry/FiniteWalshObservationCapacityLaw.lean`;
- `formal/GaloisForLFunctions/HTGeometry/LBitBoundaryOperationalCapacityLaw.lean`.

Capstones:

- `sum_norm_sq_inverseWalshCoefficient`;
- `sq_mul_walshThresholdCount_le_bound_sq`;
- `lbitBoundaryPacketEnergy_doubleFlip_eq_generator`;
- `lbitBoundaryResponse_dimension_time_capacity`;
- `lbitBoundaryResponse_fullVisibility_time_lower_sq`.

Direct foreground `lake env lean` checks passed for both modules.  The
capstone axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.
