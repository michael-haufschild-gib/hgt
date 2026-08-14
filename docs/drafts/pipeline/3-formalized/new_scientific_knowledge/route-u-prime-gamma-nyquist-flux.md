# Route U common-filter prime--Gamma Nyquist flux

- **ID:** `route-u-prime-gamma-nyquist-flux`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`; successor to
  `route-u-global-nyquist-current-exchange`
- **Statement:** Every finite Route-U dyadic even/odd packet admits coefficient-faithful real
  Chebyshev source polynomials whose native weighted difference-of-squares divisor current equals
  an exact difference of two literal completed prime--Gamma capitals under one common positive
  Laplace filter.  The canonically renormalized literal source flux tends to zero unconditionally.

## Status labels

`[LEAN-PROVED] [SOURCE BRIDGE] [NOVELTY UNVERIFIED]`

## Conjecture--failure--pivot loop

### U-PGN-RAW — subtract the two native source capitals

Conjecture: lift even and odd channel polynomials independently and subtract their existing
prime--Gamma capitals.

**Verdict:** `[FALSIFIED]`.  Minimal reciprocal lifts can have different degrees.  Their source
transmutations then carry different factors `(2d)!` and different positive kernels
`t^(2d) exp(-a^2 t)`.  Raw subtraction is not the Nyquist current and destroys common-filter
orientation before divisor aggregation.

### U-PGN-PAD — common-degree source gauge

Pad both reciprocal polynomials to

```text
D=max(deg R_E,deg R_O)
```

using exact coefficient vectors of length `D+1`.  Both literal source capitals now use the same
positive Laplace filter and the same factorial normalization.  This conjecture survives.

### U-PGN-ACTUAL — coefficient-faithful dyadic channels

The abstract common-degree identity is useful only if the actual lattice channels are represented
without target-fed interpolation.  Construct the fine even Chebyshev polynomial directly from
even lattice modes and define the odd polynomial as the exact residual of the full finite packet.
Lean proves their evaluations are exactly the Route-U even and odd samples at every Xi divisor
copy.  Therefore the common-degree source identity specializes to the actual Nyquist current.

**Verdict:** `[PAPER-PROVED] [LEAN-PROVED]`.

## Exact theorem

For positive hard-edge mass `a` and real polynomials `P,Q`, put

```text
R_P = xiHardEdgeReciprocalPolynomial a P,
R_Q = xiHardEdgeReciprocalPolynomial a Q,
D   = max(deg R_P,deg R_Q).
```

Let `c_P,c_Q : Fin(D+1)->R` be the zero-padded coefficient vectors and let
`C_P,C_Q` be their literal filtered completed prime--Gamma capitals.  Define the oriented divisor
term

```text
Phi_a(P,Q;q)
 = xiHardEdgeDivisorPacketTerm a P q
   - xiHardEdgeDivisorPacketTerm a Q q.
```

Then

```text
a^2 (C_P-C_Q)
 = pi (2D)! Re sum_q Phi_a(P,Q;q).                       (PGN.1)
```

For physical carrier `g`, compact cutoff `n`, and dyadic scale `k`, there are canonical finite
polynomials `P_E(k),P_O(k)` satisfying, for every `q`,

```text
P_E(k)(x_(2k+1,q)) = E_k(q),
P_O(k)(x_(2k+1,q)) = O_k(q).                              (PGN.2)
```

No interpolation at Xi nodes is used.  Consequently

```text
Phi_(2k+1)(P_E(k),P_O(k);q)
 = W_(2k+1)(q) (E_k(q)^2-O_k(q)^2).                       (PGN.3)
```

Define the renormalized literal source flux

```text
F_k = a_(2k+1)^2 (C_E(k)-C_O(k)) / (pi (2D_k)!).          (PGN.4)
```

The closed capstone is

```text
F_k = Re sum_q W_(2k+1)(q) J_k(q),
F_k -> 0.                                                  (PGN.5)
```

## Dependency-closed paper proof

Choose `D` as above.  Because `deg R_P,deg R_Q<=D`, polynomial `ofFn` applied to each length-`D+1`
coefficient vector recovers the corresponding reciprocal polynomial exactly.  The generic
trace-Hankel coefficient expansion at shift `a^2` therefore gives

```text
H_(a^2)(c_P)=Re TraceHankel_(a^2)(R_P),
H_(a^2)(c_Q)=Re TraceHankel_(a^2)(R_Q).                   (6)
```

The existing Cayley divisor lift converts (6) into

```text
a^2 H_(a^2)(c_P)=Re sum_q packet(a,P;q),
a^2 H_(a^2)(c_Q)=Re sum_q packet(a,Q;q).                  (7)
```

Both packet families are absolutely summable.  Subtracting (7) and using summability to commute
subtraction with `tsum` gives

```text
Re sum_q Phi_a(P,Q;q)=a^2(H(c_P)-H(c_Q)).                 (8)
```

Since `a>0`, the filtered prime--Gamma transmutation applies to both common-degree vectors with
the same kernel:

```text
C_P=pi(2D)!H(c_P),
C_Q=pi(2D)!H(c_Q).                                        (9)
```

Equations (8)--(9) prove (PGN.1).

For the actual dyadic packet, compact support supplies one finite cutoff.  Pair positive and
negative even fine-lattice indices.  The exact Cayley character identity converts every pair at
mode `2m` into `2 T_(2m)`; the zero mode supplies the constant coefficient.  This constructs
`P_E` and proves the first identity in (PGN.2).  The full finite Chebyshev packet already represents
`E+O`; defining `P_O=P_full-P_E` proves the second identity.  Substitution in the literal packet
definition gives (PGN.3) pointwise, before any divisor sum.

Specializing (PGN.1), dividing by the nonzero common factor `pi(2D_k)!`, and using (PGN.3) proves
the equality in (PGN.5).  The preceding global Nyquist-current theorem makes the complex complete
sum tend to zero; continuity of real part gives the final source-flux limit.  No RH assumption,
zero count, numerical computation, target-fed interpolation, or unproved exchange occurs.  QED.

## Hostile significance audit

This is the requested source identity before divisor aggregation: Gamma, polar, and von-Mangoldt
terms remain inside each literal completed balance, and both channel capitals share one filter.
It is not RH.  An indefinite quadratic form may have vanishing reconstruction/detail cross flux
while its reconstruction diagonal remains negative.  Therefore “source orthogonality implies
positivity” is false without an additional source-specific diagonal law.

The strongest positive survivor is exact asymptotic common-filter orthogonality:

```text
completed prime--Gamma reconstruction channel
  ⟂ completed prime--Gamma detail channel
```

after native mass/factorial normalization.  This turns the former vague source anomaly into a
specific diagonal obstruction.

## Novelty audit

- `[CORPUS]` Finite Cayley/Chebyshev packet representation, filtered prime--Gamma transmutation,
  exact hard-edge divisor lift, and global Nyquist-current decay existed separately.
- `[NEW COMPOSITION]` Common-degree zero padding, coefficient-faithful even/odd physical-channel
  lift, literal common-filter identity (PGN.1), and source-flux limit (PGN.5) were not found in the
  internal corpus.
- `[LITERATURE]` Classical polyphase/QMF theory treats even/odd decomposition and lossless
  reconstruction, for example Vaidyanathan's tutorial
  <https://authors.library.caltech.edu/records/x720m-mr760> and lossless polyphase matrices
  <https://authors.library.caltech.edu/records/pjekd-b0323>.  The audit found no Xi hard-edge
  Gamma--polar--von-Mangoldt common-filter flux theorem.

## Higher universal principle

Degree is source gauge, not physical charge.  Different minimal polynomial degrees place two
channels in different Laplace filters and manufacture a factorial mismatch.  Padding to one common
degree is the covariant comparison that preserves orientation.  Earlier source-flux failures were
shadows of comparing gauge-incompatible disintegrations.

## Exact open core

False RH still yields cofinal negative full-packet prime--Gamma capital.  The new theorem proves
that its reconstruction/detail mixed flux vanishes after normalization, so the obstruction is now
diagonal.  Next hard theorem must perform the common-filter polarization of the full source capital
and prove one of:

1. actual fixed-carrier even/detail diagonal capitals are nonnegative or have a strict lower bound;
2. any negative diagonal capital forces a labelled prime--Gamma anomaly incompatible with the
   degree-free Cauchy density;
3. a source-local boundary term survives common-degree polarization and is the true producer.

Generic positivity of all diagonal source capitals is RH itself and is retired.  The theorem must
use the one fixed cofinal polynomial--Gaussian carrier and its explicit hard-edge channels.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaNyquistFlux.lean`.

Key closed theorems:

- `routeUHardEdgePrimeGammaNyquistFlux_identity`
- `routeUDyadicFineEvenLatticeSample_eq_eval_evenChebyshevPacket`
- `routeUDyadicEvenSample_eq_eval_sourcePolynomial`
- `routeUDyadicOddSample_eq_eval_sourcePolynomial`
- `routeUDyadicPolynomialNyquistFluxTerm_eq_weightedCurrent`
- `routeUDyadicPrimeGammaNyquistFlux_identity`
- `routeUDyadicRenormalizedPrimeGammaNyquistFlux_eq`
- `tendsto_routeUDyadicRenormalizedPrimeGammaNyquistFlux_zero`

Scratch and checked-in source passed `lake env lean`; exact `.olean` was built directly.  Axiom
audit reports only `[propext, Classical.choice, Quot.sound]`.  Umbrella import is wired without an
umbrella/full build.  Forbidden computation and placeholder tokens are absent.

## Gates

- [x] 0 → 1: raw-capital conjecture killed; common-filter successor specified
- [x] 1 → 2: dependency-closed proof above
- [x] 2 → 3: checked-in Lean proof, exact `.olean`, axiom audit, umbrella wiring
- [ ] 3 → 4: independent novelty/significance audit and standalone exposition

## Log

- 2026-08-14 — Raw independent-degree source subtraction falsified by factorial/filter mismatch.
- 2026-08-14 — Common-degree covariant source gauge and actual even/odd Chebyshev lifts proved.
- 2026-08-14 — Literal prime--Gamma Nyquist flux identity and global cancellation Lean-proved.
