# Xi unit--double fused response and physical-weight renormalization

- **ID:** `xi-unit-double-fused-response-physical-weight-renormalization`
- **Stage:** `3-formalized/needs-audit`
- **Type:** theorem / source-to-response renormalization / AC28 reduction
- **Scientific status:** `[PAPER-PROVED LOCAL CORE] [CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE]`
  `[EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Sources:** `XiAperturePoissonValuationClockShuttle.lean`,
  `XiMobiusContinuousApertureSzegoMetric.lean`,
  `PhysicalPrimeEndpointMeshCoercivity.lean`, and the finite-fusion HT tower
- **Open consumer:** `critical-multiplicative-compensated-cancellation-rh.md`, `(AC28)`

## Discovery

Let the completely valuation-fused Poisson half-density at prime `p` be

```text
F_a(p)=sum_(e>=0) a exp(-a(e+1)log p)=a/(p^a-1),       (UR1)
```

and let the unit--double response shuttle be

```text
sigma_p=F_2(p)-F_1(p).                                 (UR2)
```

Then the distinguished apertures `1` and `2` collapse exactly:

```text
sigma_p=2/(p^2-1)-1/(p-1)=-1/(p+1).                   (UR3)
```

This is not merely another negative-orientation inequality.  If `q=p^(-1)` and
`r_a=p^(-a)`, the critical Möbius forward-depth feature is

```text
g_(a,p,e)=q/(1+q) (1-r_a) r_a^e
           =-sigma_p (1-r_a) r_a^e.                   (UR4)
```

Consequently the true local aperture metric is the exact quadratic compression of the signed
unit--double response current:

```text
K_p(a,b)
 =sigma_p^2 (1-r_a)(1-r_b)/(1-r_a r_b)
 =sum_(e>=0) g_(a,p,e)g_(b,p,e).                      (UR5)
```

Thus the positive aperture Gram is not an unrelated source object that must somehow be converted
into an indefinite response.  It is obtained by forgetting the sign of an already canonical
response current and completing its valuation-depth wavelet.  The missing operation is a signed
lift before Gram compression, not a fixed congruence after it.

## Exact join to the physical ordinary-prime weight

Insert the source-forced prime clock and write

```text
j_p=log(p)sigma_p=-log(p)/(p+1),
w_p=log(p)/p.                                          (UR6)
```

Then

```text
w_p=-j_p+epsilon_p,
epsilon_p=log(p)/(p(p+1))>0.                           (UR7)
```

The correction is absolutely summable, whereas both `w_p` and `-j_p` have the same non-trace-class
prime-harmonic leading channel.  At the coefficient level, complete HT valuation fusion has
therefore produced the exact response renormalization of the physical endpoint weight.

For the physical packet `0<c=log(K/M)<A`, every active prime obeys

```text
M exp(-A)<p<K=exp(c)M.                                 (UR8)
```

Hence, without prime-distribution input,

```text
sum_(p active) epsilon_p
 <= exp(c+2A) log(exp(c)M)/M.                          (UR9)
```

Indeed there are at most `K` active integers, `log p<=log K`, and
`p(p+1)>M^2 exp(-2A)`.  Since every centered interval vector has norm bounded in terms of `A`,
the physical endpoint carrier and the response-current carrier differ by
`O_(A,c)(log M/M)` in Hilbert norm.  This is already inside the `(AC28)` budget.

Therefore the RH-equivalent upper bound for the physical carrier transfers, at the correct power,
to the carrier with weights `log(p)/(p+1)`, which is the negative clocked unit--double fused
response current.

## Hostile audit

1. Equations `(UR1)`--`(UR3)` are elementary geometric-series algebra.  Their scientific content
   is restricted to the exact identification of three independently constructed project objects:
   the infinitely fused HT valuation current, the critical Möbius damping, and the physical
   ordinary-prime endpoint weight.
2. `(UR7)` does not prove cancellation of the main current.  It proves that the difference between
   the AC28 carrier and a source-defined response carrier is already of the required order.
3. The scalar Euler completion is valid for aperture `a>1`; the unit endpoint is non-trace-class.
   A valid completion of `(UR6)` must retain the common physical interval feature and use a
   Hilbert--Carleman/off-diagonal prime--Gamma regularization.  Naively summing `j_p` is invalid.
4. Squaring `sigma_p` gives the true aperture metric and erases precisely the sign needed by the
   response refinement.  A proof that starts only from `(UR5)` has already discarded the new
   information.
5. The local algebra is not claimed as a new theorem in classical analysis.  Candidate novelty is
   the source-specific AC28 renormalization and the resulting proof-shape correction.  External
   specialist audit remains open.

## Lean target

`GaloisForLFunctions/RHTower/XiAperturePhysicalEndpointResponseRenormalization.lean` should prove
unconditionally:

1. the closed forms `F_1(p)=1/(p-1)` and `F_2(p)=2/(p^2-1)`;
2. `(UR3)` and its clocked form `(UR6)`;
3. the exact physical-weight decomposition `(UR7)`;
4. positivity and summability of `epsilon_p`;
5. `(UR4)` and the local metric factorization `(UR5)`.

The active-packet estimate `(UR9)` and the analytic identification with the actual `AC28` carrier
remain paper-level until the clipped endpoint packet is represented in Lean.

## Gates

- [x] exact theorem originated from the existing infinite-fusion Bose law
- [x] internal corpus collision search for `(UR3)`--`(UR7)`
- [x] paper proof of the active-packet `M^(-1) log M` correction
- [x] hostile check against scalar-completion and Gram-sign circularity
- [x] targeted Lean leaf and axiom audit
- [ ] external specialist novelty audit
- [ ] completed prime--Gamma signed lift at the unit endpoint
- [ ] identify the signed lift with the joined `(AC25)` response
- [ ] prove `(AC28)` / RH

## Log

- 2026-07-19 — derived `(UR3)` from complete valuation fusion, recognized `-sigma_p` as the exact
  critical Möbius damping, and obtained the trace-class physical-weight correction `(UR7)` with
  the active-packet bound `(UR9)`; installed the unconditional Lean leaf, wired its umbrella import,
  and confirmed all public theorems use only the standard Lean axioms.
