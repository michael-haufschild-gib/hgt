# Dyadic-prime passive impedance network to RH

- **ID:** `dyadic-prime-passive-impedance-network-rh`
- **Status:** `1-in-progress`
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [PROVED SOURCE TOMOGRAPHY END]`
- **Inputs:** `../3-formalized/dyadic-prime-source-divisor-tomography.md`,
  `CCMSharpPrimeWindowDivisorTomography.lean`, `CCMSharpPrimeWindowExcessEnergyGate.lean`,
  `CCMComplexMellinColligation.lean`, `PrimeDelayHerglotzNoGo.lean`,
  `SeamCollisionMechanism.lean`, `theta-prime-pointed-doubling-fock-carrier.md`

## Claim

Let `F(s)=dyadicSharpPrimeContinuedSource(s)`.  This is the canonical meromorphic continuation of
the explicit source Dirichlet series

`sum_(n>=1) S(n)n^(-s)`,

where

`S(n)=4(1-1/sqrt(2))*sqrt(n)-2*sum_(n/2<k<=n) Lambda(k)/sqrt(k)`.

The corpus now proves that the poles of `F` in `Re(s)>1` are exactly `rho+1/2` for right
off-critical Xi zeros `rho`, with exact multiplicity.  Introduce the impedance coordinate

`z=i(s-1)`, equivalently `s=1-i z`.                                  (1)

The half-plane `Re(s)>1` becomes `Im(z)>0`, while the critical boundary `Re(s)=1` becomes the real
axis.  Therefore a source construction proving that

`Z(z)=F(1-i z)`

is the driving-point impedance, Weyl function, or boundary response of one passive distributed
network on the upper half-plane would exclude all off-boundary poles and prove RH.

`[CONJECTURE]` The dyadic prime-window source has a canonical passive transmission-line or
electrical-network realization whose finite apertures use only positive local energies and whose
normal limit equals `Z` on the initial domain `Im(z)>1/2`.  Passivity then supplies a holomorphic
Nevanlinna response on all of `Im(z)>0`; uniqueness identifies it with the canonical continuation,
so the proven divisor tomography forces RH.

## Two-ended chain

```text
explicit dyadic von-Mangoldt window S(n)                     [PROVED SOURCE]
  -> ordinary Dirichlet series on Re(s)>3/2                  [PROVED LEAN]
  -> canonical meromorphic continuation F on Re(s)>1/2      [PROVED LEAN]
  -> exact pole tomography in Re(s)>1, with multiplicity     [PROVED LEAN]

explicit finite-aperture passive line/network N_R
  -> positive local conductances/energies and Schur response [OPEN CORE A]
  -> response Z_R holomorphic with Nevanlinna sign on C+     [PARENT THEORY]
  -> locally uniform passive limit Z on C+                   [OPEN CORE B]
  -> Z(z)=F(1-i z) on Im(z)>1/2 from source quadrature       [OPEN CORE C]
  -> equality on C+ by analytic uniqueness
  -> F holomorphic on Re(s)>1
  -> no right off-critical Xi pole by tomography
  -> RH.
```

Both ends are closed independently.  The source end contains no Xi zero data.  The consumer end is
the formal theorem

`RiemannHypothesis <-> AnalyticOn F {s | 1 < Re(s)}`

together with exact pole support and multiplicity.  The only missing work is the passive response
construction and its exhaustion theorem.

## Existing finite colligation floor

The finite network incidence is substantially closer than a blank synthesis problem.
`CCMComplexMellinColligation.lean` proves on every finite packet of complex right-half-plane nodes
that

```text
Cauchy Gram = resolved von-Mangoldt Gram
              - shifted polar Gram
              + critical Mellin-defect matrix.
```

The resolved prime Gram is positive semidefinite with its unsquared von-Mangoldt weights.  The same
module proves that diagonal-Fock passivity is exactly the source-resolved inequality for this
three-channel colligation.  Hence no finite algebraic incidence remains to be guessed: the open
orientation is the sign of the coupled critical defect for a distinguished finite Fock coupling,
followed by its cofinal closure.

The raw-delay shortcut is now closed in Lean.  For every positive frequency `lambda`,
`PrimeDelayHerglotzNoGo.lean` exhibits two points with `Im(z)=1` at which
`exp(i lambda z)` has imaginary parts `+exp(-lambda)` and `-exp(-lambda)`.  Thus a prime delay is
not itself a passive impedance.  The positive successor is a contractive scattering colligation
or Schur-complement response built from the already-positive prime Gram.

## Why a passive network is more than a Herglotz rename

A bare assumption that `Z` is Herglotz is only another RH-equivalent positivity statement.  The
route is live only if passivity is forced locally from the displayed prime-window source.  The
construction must provide:

1. explicit positive edge, string, or canonical-system energy at every finite aperture;
2. a boundary response obtained by Schur complement, not by inserting the poles of `F`;
3. compatibility under aperture enlargement;
4. local uniform normal-family control on the whole upper half-plane;
5. equality with the source Dirichlet/quadrature formula on the initial overlap.

Distributed delay lines are allowed and likely necessary: the frequencies `log n` make a finite
lumped rational network too small.  A canonical system, metric graph with delay lengths `log p`,
or de Branges string is an admissible network only when its coefficients are derived before the
source continuation is evaluated at its poles.

## Candidate constructions

1. **Dyadic ladder network.**  Use one cell for the interval `(n/2,n]`; the polar counterterm is the
   reference conductance and the von-Mangoldt window is the shunt load.  The exact sharp-window
   telescoping identities already formalized are the series/parallel conservation laws to match.
2. **Coupled Sonin response.**  Use the all-prime Sonin residual Gram operator as the internal
   positive energy and take a dyadic boundary Schur complement.  Cross-prime overlap stays inside
   the network instead of being discarded into scalar coefficient signs.
3. **Theta transmission line.**  Use the pointed doubling-Fock theta carrier for the archimedean
   termination and the bounded prime evaluations as line attachments.  The distinguished vector
   `one` gives the driving port, while theta inversion provides the reflected boundary condition.
4. **Boundary-jet network.**  Use the positive prime-support deformation
   `M_n(t)=n(1-t)^(n-1)` as a support-graded internal incidence network.  Its full boundary jets
   retain mixed-prime channels; the dyadic observable is taken only at the external port.
5. **Existing complex CCM colligation.**  Take the resolved von-Mangoldt Gram as the positive
   internal prime port, the shifted polar Gram as the boundary port, and the critical Mellin defect
   as the feedback channel.  The precise task is to construct the distinguished diagonal Fock
   coupling whose source-resolved inequality holds cofinally; the entrywise colligation and finite
   passivity equivalence are already formalized.

## Hard attacks and positive residues

1. **Naive positive-residue synthesis fails.**  The coefficients `S(n)` are sign-changing; treating
   each `S(n)` as an independent positive conductance or spectral mass cannot work.
   **Positive residue:** passivity must arise after internal coupling and Schur complementation.
   The corpus already isolates the negative part of `S(n)` as exactly twice the positive dyadic
   prime-window excess, so the passivity defect has an explicit source coordinate.
   Raw prime delays fail even before summation: each one takes both Herglotz signs on the same
   horizontal line, as proved by `primeDelayMode_not_upperHalfPlaneValued`.
2. **Finite rational network is too small.**  A finite RLC impedance has finitely many algebraic
   poles and cannot equal the logarithmic prime-frequency source.
   **Positive residue:** the correct finite objects are delay-line or finite-aperture distributed
   systems, followed by a controlled normal limit.
3. **Arbitrary network synthesis is circular.**  Synthesizing a network from the poles of `F`
   reads the Xi divisor already recovered by tomography.
   **Positive residue:** every cell must be written from `Lambda(k)`, the dyadic window, and theta
   termination only.
4. **Boundary values alone are insufficient.**  A real or nonnegative response on one vertical
   line need not extend as a passive function on the whole half-plane.
   **Positive residue:** prove a bulk energy identity or positive kernel
   `(Z(z)-conj(Z(w)))/(z-conj(w))`, not a pointwise boundary sign.
5. **Scalar positive coefficients are unnecessary.**  A passive multiport Schur response can have
   signed expansion coefficients even though its internal energy is positive.
   **Positive residue:** the sign changes in `S(n)` do not retire the coupled-network route; they
   retire only the parallel-atom shortcut.
6. **Generic de Branges realization is not a source proof.**  An abstract canonical system built
   after assuming the Nevanlinna property merely repackages it.
   **Positive residue:** the dyadic cells and theta termination provide a falsifiable source-first
   construction target.

## Exact open cores

- `[OPEN CORE A]` In the already-formalized complex CCM three-channel colligation, construct the
  distinguished finite-aperture diagonal Fock/scattering coupling and prove its source-resolved
  passivity inequality, including the critical Mellin defect and polar counterterm.
- `[OPEN CORE B]` Prove monotone/strong-resolvent or normal-family convergence of those responses on
  every compact subset of `Im(z)>0`, independent of aperture choices.
- `[OPEN CORE C]` Identify the limit with `F(1-i z)` on `Im(z)>1/2` using the existing Dirichlet and
  quadrature theorems, with no zero-fed spectral measure.
- `[OPEN CORE D]` If a lossless rather than dissipative network occurs, prove the reflected
  self-adjoint extension selected by theta termination still has a holomorphic upper-half-plane
  Weyl response.

## Kill conditions

Retire the route if a positive finite cell cannot reproduce the exact dyadic counterterm; if the
network uses the Xi poles or a divisor-selected measure; if only a formal continued fraction is
obtained without convergence; if the limit loses the Nevanlinna kernel sign; if aperture order
changes the response; or if equality with `F` is shown only on a discrete set rather than an open
overlap.

## Gates

- [x] explicit source statistic and initial Dirichlet series formalized
- [x] canonical continuation and exact off-critical divisor tomography formalized
- [x] passive half-plane coordinate and both-ended closure identified
- [x] parallel-atom and zero-fed network shortcuts closed with positive successors
- [x] finite complex prime--polar--defect colligation and positive prime Gram formalized
- [x] raw prime-delay Herglotz shortcut disproved in Lean
- [ ] distinguished finite Fock coupling and source-resolved passivity proved
- [ ] passive response exhaustion proved
- [ ] source overlap identity proved
- [ ] holomorphy capstone composed with divisor tomography to obtain RH
