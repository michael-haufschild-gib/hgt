# De Sitter ultrametric detailed-balance hypertranscendence

- **ID:** `de-sitter-ultrametric-detailed-balance-hypertranscendence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / OPERATIONAL COSMOLOGY BRIDGE
- **Scientific status:** `[PROVED] [PHYSICAL COSMOLOGY BRIDGE] [PARENT-DERIVED]`
  `[NOVELTY UNVERIFIED]`
- **Scope:** general hypertranscendence in an exact de Sitter detector observable; no RH or
  distinguished special-function input
- **Parents:** `ultrametric-thermal-mahler-hypertranscendence.md`; Conroy's de Sitter
  Unruh--DeWitt response theorem
- **Statement:** A stationary multilevel detector whose positive energy gaps and degeneracies are
  the source-derived ultrametric spectrum has a hypertranscendental trace of de Sitter
  detailed-balance ratios.  The induced Hubble-decimation equation does not select this response
  by itself: the physical Boltzmann coordinate and regularity at its zero boundary are
  load-bearing.

## Physical setup

Let (p\ge2) be prime and (\varepsilon>0).  Use the positive spectrum and multiplicities of the
Neumann-to-Dirichlet operator on the (p)-adic unit circle,

```text
E_n = epsilon p^n,                 n >= 0,
rho(0) = p-2,
rho(n) = (p-1)^2 p^(n-1),         n >= 1.                 (1)
```

Regard `(1)` as the energy-gap spectrum of an ideal stationary multilevel detector.  Resolve every
degenerate eigenspace by a tomographically complete family of Hermitian monopole couplings whose
selected transition matrix elements are nonzero.  The detector follows a comoving geodesic in
four-dimensional de Sitter spacetime with Hubble parameter (H>0) and is coupled to a massless,
conformally coupled scalar field in the conformal vacuum, equivalently the Bunch--Davies vacuum in
this model.

In the infinite detection-time limit, the de Sitter Unruh--DeWitt response is thermal at

```text
T_dS = H/(2 pi).                                           (2)
```

For a channel with positive gap (E), let (Gamma_up(E)) and (Gamma_down(E)) be its excitation and
de-excitation rates.  KMS detailed balance gives

```text
Gamma_up(E) / Gamma_down(E) = exp(-2 pi E/H).              (3)
```

For every addressed channel, the squared detector matrix element is common to the two
orientations and cancels in `(3)`.  The universal ratio is scalar on each energy eigenspace.
Summing it with spectral multiplicity therefore gives the basis-independent trace below; changing
basis may require changing the tomographic family of couplings, but cannot change the trace.

## Exact detailed-balance trace

Define the reduced trace of channelwise detailed-balance ratios by

```text
R_(p,epsilon)(H)
  = sum_(n>=0) rho(n) Gamma_up(E_n)/Gamma_down(E_n).        (4)
```

This is not the total excitation rate.  It is a spectroscopically reconstructible trace of rate
ratios.  Put

```text
a = 2 pi epsilon,
w_H = exp(-a/H).
```

Equations `(1)` and `(3)` give the exact identity

```text
R_(p,epsilon)(H)
  = (p-2) exp(-a/H)
    + (p-1)^2 sum_(n>=1) p^(n-1) exp(-a p^n/H)
  = K_p(w_H),                                               (5)
```

where (K_p) is the reduced ultrametric thermal trace.  The sum converges for every (H>0).
Therefore the response is not prescribed as an arbitrary detector form factor: its scale tower
and multiplicities come from the boundary spectrum, while its reporter coordinate comes from de
Sitter KMS thermality.

## Hypertranscendence in the physical coordinates

The parent theorem proves that (K_p(w)) is hypertranscendental over (\mathbb C(w)).  Hence `(5)`
is hypertranscendental in the canonical Boltzmann coordinate (w_H).

It is also hypertranscendental as a local function of (H).  Indeed,

```text
w(H) = exp(-a/H),                 H(w) = -a/log(w).         (6)
```

On any compatible simply connected local domain, both changes of variable in `(6)` are
differentially algebraic and are inverse to each other.  Differentially algebraic germs are
closed under composition.  If (R_(p,epsilon)(H)) were differentially algebraic over
(\mathbb C(H)), composition with (H(w)) would make (K_p(w)) differentially algebraic over
(\mathbb C(w)), contradicting the parent theorem.  Thus

```text
R_(p,epsilon) is hypertranscendental over C(H).             (7)
```

This conclusion concerns ordinary local differential algebra away from the singular boundary
(H=0); it does not assert a Taylor expansion in (H) at that boundary.

## Exact Hubble-scale constraint

The Mahler constraint on (K_p) and the identity

```text
w_(H/p) = w_H^p
```

give

```text
R(H) = (p-2) exp(-a/H) + exp(-a p/H) + p R(H/p).           (8)
```

Equation `(8)` is a static relation among detector experiments at Hubble scales (H) and (H/p),
not time evolution within one spacetime.

## Finite-resolution falsification law

Let (R_N(H)) retain the base shell and the first (N) positive shells of `(5)`.  Direct finite-sum
algebra gives

```text
R_N(H) - [(p-2)e^(-a/H) + e^(-ap/H) + p R_N(H/p)]
  = -(p-1)^2 p^N e^(-a p^(N+1)/H).                        (9)
```

Thus a finite detector does not have an unspecified truncation error in the scale law: its
residual is exactly the next omitted shell.  Measurements of (R_N) at (H) and (H/p) can falsify
the predicted next-shell multiplicity without resolving the rest of the tower.  Repeating `(9)`
at increasing (N) gives a cofinal finite-resolution protocol.

No fixed (N) proves that the tower is infinite or certifies hypertranscendence.  Every (R_N) is a
finite exponential sum and is differentially algebraic.  The formal proof of `(9)` is recorded in
`../../3-formalized/not_new_scientific_knowledge/ultrametric-thermal-finite-resolution-residual.md`.

## Hubble-decimation non-selection theorem

The homogeneous Hubble equation associated with `(8)` is

```text
Y(H) = p Y(H/p).                                          (10)
```

It has the nonzero differentially algebraic solution

```text
Y(H) = H.                                                 (11)
```

This solution even tends to zero as (H\downarrow0).  Therefore `(8)`, including a vanishing
boundary condition at (H=0), does **not** uniquely select the physical response and does not by
itself force hypertranscendence.

The rigidity theorem holds only after passing to the physical Boltzmann coordinate and requiring
a formal or holomorphic germ at (w=0).  Under `(6)`, the spurious solution `(11)` becomes
(-a/\log w), which is not a formal power series at (w=0).  Thus the exact selection mechanism is

```text
de Sitter KMS coordinate + ultrametric scale constraint
+ regularity at the zero-temperature Boltzmann boundary.  (12)
```

This is the main conceptual result of the bridge.  A scale equation written directly in a
cosmological parameter can forget the boundary category that made the constraint rigid.

## Operational and physical boundary

The quantity `(4)` is basis-independent and each summand is a measured rate ratio, but full
reconstruction requires resolving an ideal infinite detector tower.  The theorem uses the
stationary, infinite detection-time KMS limit.  It does not establish a finite-time exact identity
or an error bound for switching and transient effects.

The result is an operational de Sitter realization of a hypertranscendental response.  It is not
a primordial wavefunction coefficient, a late-time cosmological correlator, an interacting
gravitational model, or an observational forecast.  No claim is made that an ordinary material
detector realizes the ultrametric internal spectrum.

## Anti-theatre and novelty verdict

The de Sitter Unruh--DeWitt rate, KMS detailed balance, the ultrametric spectrum, and the Mahler
hypertranscendence theorem are parent results.  Exact searches for combinations of ultrametric or
(p)-adic detector spectra with de Sitter detailed balance found no direct match, but absence from
a finite search is not a novelty proof.  The theorem is therefore labelled a parent-derived
physical bridge, not new scientific knowledge.

It nevertheless kills two forms of theatre:

1. an arbitrary hypertranscendental detector response is unnecessary--the exact function follows
   from a source-derived spectrum and a universal KMS ratio;
2. Hubble self-similarity is not the cause of hypertranscendence--without the Boltzmann boundary
   category, the same homogeneous scale law admits the elementary solution `(11)`.

## Lean boundary

`formal/GaloisForLFunctions/HTGeometry/UltrametricThermalMahler.lean` already formalizes the
coefficient spectrum, the exact constraint in the (w)-coordinate, and uniqueness among formal
power series.  `FiniteKMSDetailedBalance.lean` already formalizes exact finite Gibbs detailed
balance for Hermitian transition amplitudes.

`UltrametricThermalTruncation.lean` formalizes the new reusable finite-resolution content: the
prefix constraint and the exact next-shell residual `(9)`.  By contrast,
`ExponentialObservationHypertranscendence.lean` concerns exponentiating an HT dependent variable,
and `GenericTimeChangeJetBirationality.lean` concerns generic finite jets under time change.
Neither is a theorem that an invertible differentially algebraic change of the independent
variable preserves HT.  A wrapper merely replacing (w) by (\exp(-a/H)) would therefore overstate
the current formal surface while hiding the scientifically important failure of uniqueness in
the (H)-coordinate.

The external analytic ingredients not presently formalized are the de Sitter detector response,
closure of local differential algebra under the inverse changes `(6)`, and the imported Mahler
hypertranscendence theorem.

## Exact open core

1. Derive a source-natural ultrametric tower inside an interacting cosmological field theory,
   rather than placing the spectrum in an ideal detector.
2. Prove a finite-switching-time stability theorem that controls the deviation from `(3)` across
   the whole tower.
3. Produce hypertranscendence in a primordial wavefunction or gauge-invariant in-in correlator and
   prove survival under cosmological observation.
4. Add noise, finite linewidth, and missed-channel error bounds to the exact finite-resolution
   residual `(9)`; the noiseless cofinal protocol is now proved.
5. Complete a systematic literature novelty audit across detector models, ultrametric quantum
   systems, and cosmological response theory.

## Primary sources

- A. Conroy, *Unruh-DeWitt detectors in cosmological spacetimes*,
  <https://arxiv.org/abs/2204.00359>.
- E. T. Akhmedov, K. V. Bazarov, D. V. Diakonov, U. Moschella, F. K. Popov, and C. Schubert,
  *Propagators and Gaussian effective actions in various patches of de Sitter space*,
  <https://arxiv.org/abs/2005.13952>.
- A. Huang and C. B. Jepsen, *A glimpse into the Ultrametric spectrum*,
  <https://arxiv.org/abs/2601.03738>.
- B. Adamczewski, T. Dreyfus, and C. Hardouin,
  *Hypertranscendence and linear difference equations*,
  <https://arxiv.org/abs/1910.01874>.
- R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia,
  *D-Algebraic Functions*, <https://arxiv.org/abs/2301.02512>.
