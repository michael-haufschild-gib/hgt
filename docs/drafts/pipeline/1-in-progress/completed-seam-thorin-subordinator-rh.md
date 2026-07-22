# Completed seam Thorin subordinator and RH

- **ID:** `completed-seam-thorin-subordinator-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [KNOWN RH EQUIVALENCE; SOURCE-ASSEMBLY TARGET]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`,
  `formal/GaloisForLFunctions/RHTower/XiRelativeResolventFlux.lean`,
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmMomentDeterminacy.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean`, and
  `formal/GaloisForLFunctions/RHTower/PrimeBoundaryDickmanWick.lean`
- **Statement:** `[CONJECTURE]` The reciprocal completed seam ratio is the Laplace transform of one
  source-defined generalized gamma convolution whose Thorin measure is constructed from the
  coupled theta--Euler--Gamma constraint without using the Xi divisor.  This representation forces
  the canonical seam-log derivative into the Stieltjes cone and therefore proves RH.

## Exact object and closed consumer end

Put

```text
Xi(w)=xi(1/2+w),
Phi(s)=Xi(sqrt(s)),
F_src(s)=Phi(0)/Phi(s),
L(s)=log(Phi(s)/Phi(0)).                                  (1)
```

The square root causes no branch ambiguity because `Xi` is even.  The corpus proves for the
canonical seam-log Markov germ

```text
G_src(-s)=2 L'(s)=-2 (log F_src)'(s),                     (2)
```

and proves on paper that `G_src` is a positive Markov transform on `R_+` if and only if RH.  Hence
the following source theorem closes the consumer end:

```text
F_src(s)=exp(-a s-integral log(1+s/t) dU(t)),              (3)
```

where `a>=0` and `U` is a positive Thorin measure on `(0,infinity)` satisfying the usual local
integrability conditions.  Differentiating `(3)` gives

```text
G_src(-s)=2a+2 integral 1/(s+t) dU(t).                    (4)
```

Under `y=1/t`, `(4)` is a Markov transform

```text
G_src(-s)=integral 1/(1+s y) dnu(y),                     (5)
```

with `nu=2a delta_0+2 push_(t->1/t)(t^(-1)U)`.  Therefore `(3)` implies the
all-order shifted Stieltjes square tests, and the existing seam-log theorem gives RH.

Conversely, under RH the Hadamard product gives

```text
F_src(s)=product_gamma (1+s/gamma^2)^(-m_gamma),          (6)
```

so `(3)` holds with the positive atomic Thorin measure

```text
U=sum_gamma m_gamma delta_(gamma^2).                      (7)
```

Thus GGC membership of this exact reciprocal seam ratio is an RH equivalence.  The equivalence is
parent theory; the only proof-bearing novelty can be a divisor-free construction of `U` from the
completed source.

## The large two-ended detour

```text
positive theta-cusp atom density and all raw even moments        [PROVED LEAN]
  + Euler prime-power logarithmic source on its convergence side [PROVED LEAN]
  + exact Gamma/polar completion and FE weld                      [PROVED LEAN]
  -> incomplete-Gamma / half-stable source packets
       [OPEN CORE A: positive packet measure]
  -> one compatible positive Thorin measure U
       [OPEN CORE B: completion-sensitive assembly]
  -> local shifted Markov identity at the genuine theta boundary
       [OPEN SOURCE CONSTRUCTION: now part of cores A--B]
  -> analytic transport from Euler-safe Cassini u=0 to centered u=1
       [CLOSED LEAN FOR COMPACT CARRIERS: CORE C]
  -> Stieltjes representation (4)--(5)                            [GENERAL GGC THEORY]
  -> all shifted seam Hankel square tests                         [MOMENT GRAM]
  -> RH                                                            [PROVED PAPER CONSUMER].
```

This is not a proposal to infer positivity from a finite coefficient prefix.  A single positive
measure `U` must generate every order simultaneously, and `(3)` must first be proved on an open
right-half-plane overlap where both the Euler--Gamma expression and the Laplace exponent converge.
Analytic uniqueness then identifies the canonical seam germ.

## Source forms to attack

A GGC Laplace transform has the equivalent Lévy form

```text
-log F_src(s)=a s+integral_0^infinity (1-exp(-s x)) k_src(x) dx/x,
k_src(x)=integral_0^infinity exp(-t x) dU(t).             (8)
```

Consequently the first genuinely source-side target is not the abstract phrase “`F_src` is GGC.”
It is an explicit theta--prime formula for `k_src(x)` followed by complete monotonicity of that
specific density:

```text
(-1)^n k_src^(n)(x)>=0  for all x>0 and all n>=0.         (9)
```

The corpus offers three nonidentical constructions to test.

1. **Incomplete-Gamma packets.**  Keep each positive Gaussian theta atom intact under the
   half-power substitution, express its incomplete-Gamma remainder as a truncated stable
   `1/2` packet, and couple the prime and polar corrections before testing positivity.
2. **Completed relative-resolvent flux.**  Invert the already-formalized identity between the
   continued prime--arch source trace and the Xi relative resolvent.  The desired `k_src` is the
   inverse-Laplace density of the divided completed trace, not of either singular source summand.
3. **Static heat-trace realization.**  Construct directly from theta--Euler--Gamma incidence a
   positive measure `U` whose Laplace trace is `k_src`.  This is a static spectral constraint; the
   measure is invalid if its atoms or support are read from Xi zeros.

## Hard attacks and positive residues

1. **The Xi characteristic function cannot be infinitely divisible.**  The normalized real-axis
   characteristic candidate `Xi(i t)/Xi(0)` has real zeros.  Every infinitely divisible
   characteristic function is an exponential of a Levy--Khintchine exponent and is therefore
   zero-free.
   **Positive residue:** the admissible probability object is the positive-seam reciprocal
   `F_src(s)=Phi(0)/Phi(s)`, not Xi itself.  Its real positive axis has no denominator zero, and its
   logarithmic derivative is exactly the RH-complete seam object.
2. **The universal prime Dickman field is too positive and too small.**  The corpus proves its
   characteristic function is strictly positive and its Levy exponent loses the divisor.
   **Positive residue:** retain the signed completion-sensitive prime defect and Gamma/theta weld
   inside `k_src`; never replace them by the universal `du/|u|` limit.
3. **Termwise prime positivity fails after seam division.**  The prime and archimedean divided
   log-derivatives have opposite poles that cancel only in the completed sum.  A positive Thorin
   law for each separate Euler delay is impossible and a raw prime delay is not Herglotz.
   **Positive residue:** positivity may be tested only after the exact completion coupling, using
   one joint measure or positive block compression.
4. **Generic complete monotonicity is too weak.**  Complete monotonicity of `G_src(-s)` alone does
   not imply the Stieltjes cone; `exp(-s)` is the corpus counterexample.
   **Positive residue:** complete monotonicity is imposed on the Levy density `k_src` in `(8)`
   together with the exact logarithmic Laplace identity.  By Bernstein, this produces the Thorin
   measure and hence the Stieltjes derivative, not merely a Laplace shadow.
5. **A zero-fed Thorin measure is circular.**  The atomic measure `(7)` is available only after RH
   has localized the divisor.
   **Positive residue:** acceptable approximants use theta integer atoms, von Mangoldt prime powers,
   incomplete Gamma kernels, and polar terms only.  Their weak limit must be shown positive before
   the identity with `F_src` is invoked.
6. **Finite GGC interpolation proves nothing.**  Any finite positive coefficient prefix can have a
   later non-Stieltjes continuation.
   **Positive residue:** require a compatible positive measure at every aperture, tightness, and
   convergence of the full Laplace exponents on an open domain.
7. **The literature equivalence is not the missing sign.**  Existing Thorin reformulations isolate
   positivity equivalent to RH and explicitly separate unconditional Gaussian/subordinator tiers
   from the nontrivial tier.
   **Positive residue:** the research target is precisely a new source assembly proving positivity
   of the coupled nontrivial tier; no equivalence, coordinate change, or numerical HCM test counts.
8. **Separated polar-factor tilting fails by a fixed quarter-gap.**  The April 2026 revision of
   Polson's Thorin programme claims to transport an Euler-safe auxiliary GGC to the critical center.
   At square aperture `r`, however, its separated polar factor is `Exp(r-1/4)`, while center
   transport requires exponential tilt by `r`.  The tilted density has exponent `x/4` and is not
   integrable, independent of `r`.  At the paper's `r=1`, its own Thorin atom `delta_(3/4)` makes
   `E exp(H_star)=infinity`, contradicting the asserted finite unit tilt.
   **Positive residue:** the polar factor and zeta-pole channel must be canceled as one completed
   block before positivity is imposed.  This is formalized by
   `ThorinPolarQuarterTiltBarrier.lean`; increasing the auxiliary aperture cannot close cores A--B.
9. **Critical-center comparison is not an independent compact-source wall.**  The genuine theta
   response is already exact near the Euler-safe Cassini boundary `u=0`, and the canonical source
   is unconditionally zero-free on the full segment to the center `u=1`.  If one compact positive
   measure with support radius below `1/2` matches the shifted Markov kernel locally at `u=0`, a
   zero-free convex-tube identity theorem transports the same measure to the centered seam germ.
   **Positive residue:** for the compact route, no second Frullani or critical-center source
   comparison is needed.  The only live construction is the local coupled theta--prime--Gamma
   positive measure and its cofinal limit.  This is formalized by
   `ThetaCuspCassiniMarkovBoundaryTransport.lean`.
10. **The Euler-boundary response has an unconditional positive moving carrier.**  For
    `0<t<1`, `ThetaCuspCassiniHyperbolicSourceLaw.lean` proves the exact normalized source identity
    `H(1-t^2)=E_t[x tanh(tx)/t]`, where
    `dP_t(x)` is proportional to `cosh(tx) thetaCuspFullSource(x) dx` on the positive half-line.
    **Positive residue:** source positivity and normalization are discharged.  The remaining
    Thorin/Markov theorem must remove the `t`-dependence coherently and produce one fixed compact
    measure; replacing `P_t` by a frozen carrier deletes its replicator covariance term and is
    invalid.

## Low-aperture falsification protocol

For a proposed finite source packet `k_N`, require before any limit:

1. an explicit positive representing measure `U_N`, or certified complete monotonicity of `k_N`;
2. exact equality of its Frullani exponent with the completed finite source packet, including the
   polar counterterm;
3. compatibility or tightness of `U_N` under aperture enlargement;
4. convergence of logarithmic derivatives to `L'(s)` on an open source domain;
5. no use of Xi zeros, Hankel determinants, or target Jacobi/Thorin parameters in defining `U_N`.

A negative derivative of some `k_N` retires only that packetization.  Its positive successor is the
minimal coupled block containing the offending prime, theta, and polar channels; the sign defect is
to be retained as an explicit completion-interaction coordinate.

## Exact open cores

- `[OPEN CORE A]` Derive an explicit all-aperture coupled theta--Euler--Gamma measure and prove its
  shifted Markov transform equals the genuine inward theta response on a one-sided neighborhood
  of the Euler-safe Cassini boundary.  Polar--zeta cancellation must occur before positivity: a
  raw positive polar atom cannot survive the critical tilt.
- `[OPEN CORE B]` Prove positivity and compact support survive the completed limit with one fixed
  support radius `B<1/2` (or extend the transport theorem to a controlled noncompact carrier).
- `[CLOSED LEAN FOR COMPACT CARRIERS: CORE C]`
  `ThetaCuspCassiniMarkovBoundaryTransport.lean` proves that the local boundary identity from A--B
  transports the same measure to the centered completed-seam Markov germ.  Global Frullani/source
  comparison at the critical center is therefore redundant in the compact route.
- `[CLOSED LEAN: CORE D]` `CompletedSeamCompactMarkovGermCapstone.lean` formalizes the bridge from
  a local compact Markov transform to the canonical normalized prime--arch moment representation
  and RH. `CompletedSeamCompactThorinExponentCapstone.lean` now also proves that the exact centered
  Cassini-source logarithmic exponent has derivative equal to the completed-seam moment germ and
  that any finite positive compact Thorin representation of that exponent supplies the Markov
  premise. Source construction and identification remain exactly cores A--C.

## Kill conditions

Retire a construction if it uses the Xi divisor to define `U`; if it proves only complete
monotonicity of `G_src(-s)` rather than the GGC Levy density; if prime and Gamma pieces are declared
positive separately despite their divided-pole cancellation; if the measures depend incompatibly
on aperture; if the exponent identity holds only at finitely many derivatives; or if positivity is
assumed under the names Thorin, HCM, Pick, Stieltjes, or GGC.

## Parent boundary

The GGC/RH equivalence and the atomic Thorin measure under RH are established parent theory,
including N. Polson's *Riemann Hypothesis: a GGC factorisation* and the later incomplete-Gamma/Thorin
programme.  This card claims no novelty for `(3)--(7)`.  Its purpose is to isolate a source-pure
assembly target that can consume the corpus's theta atoms, prime continuation, relative-resolvent
weld, and moment determinacy in one chain.

## Gates

- [x] exact reciprocal seam ratio and GGC-to-Markov derivative dictionary stated
- [x] both-ended closure to the existing RH-equivalent seam Hankel cone stated
- [x] direct infinitely-divisible Xi characteristic-function route retired with a positive
      reciprocal-seam successor
- [x] Dickman and separated prime-delay shortcuts retired with completion-sensitive successors
- [x] infinite-support representing-measure-to-RH capstone formalized in Lean
- [ ] explicit completed finite Levy density constructed
- [ ] finite packet positivity and exponent identity proved
- [ ] tight positive Thorin limit proved
- [x] abstract compact-Markov-to-seam-Hankel bridge formalized
- [x] Markov coefficient dictionary composed with the formal RH capstone
- [x] exact centered source-exponent-to-compact-Markov wrapper formalized
- [x] Euler-safe theta-boundary Markov identity transported to the centered RH germ in Lean
