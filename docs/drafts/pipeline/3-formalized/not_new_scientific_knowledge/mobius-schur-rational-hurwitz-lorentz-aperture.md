# The Möbius Schur metric sees the critical strip, not the critical line

- **ID:** `mobius-schur-rational-hurwitz-lorentz-aperture`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / EXACT METRIC CLASSIFICATION / NO-GO WITH POSITIVE SUCCESSOR
- **Scientific status:** `[PROVED] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/XiMobiusSchurRationalHurwitzLorentzAperture.lean`
- **Parents:**
  - `../needs-audit/xi-mobius-schur-valuation-marking.md`
  - `xi-rational-hurwitz-dyadic-refinement-square-law.md`
  - `prime-seam-damping-aperture-law.md`
  - `uniform-positive-multiplier-summability-transfer.md`
  - `../../2-fully-proven/not_new_scientific_knowledge/rational-hurwitz-lorentz-boost-colligation.md`
- **Statement:** The diagonal mass of the canonical all-prime Möbius Schur RKHS, multiplied by the
  normalized rational-Hurwitz reflection energy, is summable exactly in the open critical strip
  (with the critical line included as the zero case).  Consequently it is summable on every Xi
  divisor fibre unconditionally.  The source-fixed positive metric therefore discharges Hilbert
  membership but cannot supply the missing RH selector; the irreducible interface is contractivity
  or a cofinal zero-loss estimate in that metric.

## Exact splice

For a prime `p`, put `q=p^(-1)`.  The Möbius Schur depth-difference kernel has diagonal mass

```text
K_M(p,p)=q^2 (1-q)/(1+q)^3.                              (1)
```

For `rho=sigma+i*t`, let `H_p(rho)` be the normalized rational-Hurwitz reflection energy.  The
finite-value reflection law and the common phase of the two reflected responses give

```text
H_p(rho)
 =p ||orbitwiseNatPrimeSeamCharge(p,rho)||^2/(4 log(p)^2)
 =p/4 (p^(-sigma)-p^(-(1-sigma)))^2.                    (2)
```

Write

```text
A_p(sigma)=p^(-sigma)-p^(-(1-sigma)),
r_p=(1-q)/(1+q)^3.                                      (3)
```

Multiplying `(1)` and `(2)` gives the exact source/value splice

```text
K_M(p,p) H_p(rho)=r_p/4 * p^(-1) A_p(sigma)^2.          (4)
```

Thus the actual Möbius source metric is the `theta=1` member of the prime-seam damping hierarchy,
up to the intrinsic local Schur factor `r_p/4`.

## Uniform equivalence of metrics

Every prime has `0<q<=1/2`, and

```text
4/27 <= r_p <= 1.                                       (5)
```

The upper bound is immediate.  For the lower bound,

```text
27(1-q)-4(1+q)^3
  =(1-2q)(2q^2+7q+23)>=0,                               (6)
```

and `(1+q)^3>0`.  Equations `(4)`--`(5)` therefore give

```text
1/27 * p^(-1) A_p(sigma)^2
  <= K_M(p,p) H_p(rho)
  <= 1/4 * p^(-1) A_p(sigma)^2.                         (7)
```

The two nonnegative prime series have exactly the same summability behavior.

## Exact aperture and unconditional Xi consequence

The formalized damping-aperture law at `theta=1` now yields

```text
sum_p K_M(p,p) H_p(rho)<infinity
  iff sigma=1/2 or |2sigma-1|<1
  iff sigma=1/2 or 0<sigma<1.                            (8)
```

Every Xi zero already lies in the open critical strip, independently of RH.  Hence

```text
for every rho,
  xi(rho)=0 -> sum_p K_M(p,p) H_p(rho)<infinity.         (9)
```

This is not a weak RH criterion.  It is an unconditional source theorem showing exactly what the
canonical Möbius RKHS damping retains: the completed critical strip and the horizontal Lorentz
rapidity as a finite vector.

## No-go and positive successor

The existence of one source-fixed positive Hilbert metric was an open clause of the retired
source-framed colligation route.  The Möbius Schur metric now supplies that metric, but `(9)` proves
that mere membership, finite norm, and finite-packet nondegeneracy remain compatible with every
off-line Xi orbit.

The failed shortcut is therefore:

```text
canonical all-prime positive metric
  + normalized rational-Hurwitz Lorentz seam is Hilbert
  -> RH.                                                 (10)  FALSE
```

The strongest positive successor is now family-wide:

```text
every fixed positive continuous Möbius aperture sees precisely the strip;
cofinal apertures theta->0 force RH;
only a non-uniform zero-aperture law can retain RH data.  (11)
```

This stronger classification is formalized in
`mobius-continuous-aperture-rational-hurwitz-no-go.md`.  Its comparison constant depends on the
source aperture and tends to zero at the germ boundary, so it closes fixed-aperture tuning without
assuming away the still-open renormalized tangent problem.

The remaining RH-bearing interface is not construction of another metric.  It is either:

1. a source-built contraction/passivity law for the Lorentz transfer in the fixed Möbius metric;
2. a family of source estimates whose effective damping aperture tends to zero; or
3. a relative trace cancellation equivalent to that zero-loss limit.

The unbounded inverse Gamma dressing already rules out obtaining this by channelwise whitening.

## Novelty and parent boundary

The prime-power comparison, logarithmic moment threshold, and equivalence of uniformly comparable
positive series are classical.  Prime-zeta convergence on `Re(s)>1` and Euler's divergence at the
harmonic boundary are the analytic parents; Fröberg's classical study is C.-E. Fröberg, *On the
prime zeta function*, BIT 8 (1968), 187--202.  The alignment of the project's Möbius Schur RKHS
with its rational-Hurwitz reflection energy is a project bridge and no new-science claim is made.

## Gates

- [x] exact finite-value/Lorentz energy identified with the real reflected amplitude
- [x] exact Möbius Schur diagonal inserted
- [x] uniform two-sided source-metric comparison proved
- [x] exact aperture classified
- [x] unconditional all-Xi-fibre summability deduced
- [x] false Hilbert-membership shortcut retired with a positive successor
- [x] formalize the exact splice, comparison, aperture, and unconditional Xi proposition
- [x] extend the no-go to every fixed positive continuous Möbius aperture
- [ ] derive contractivity, a zero-loss family, or the corresponding relative trace from source

## Log

- 2026-07-19 — extracted by connecting the completed Möbius Schur metric to the normalized
  rational-Hurwitz Lorentz energy after the general damping-aperture law was formalized.
- 2026-07-19 — formalized the exact source/value splice, the uniform `4/27` and `1` Schur-factor
  bounds, the two-sided summability comparison, the exact unit aperture, and the unconditional
  all-Xi-fibre Prop discharge.  The exact leaf source check and exact Lake target build pass.
  Representative `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-19 — strengthened by the formalized continuous-aperture family classification: no fixed
  positive Möbius aperture narrows the strip, while the lower comparison degenerates exactly at
  the still-open `a -> 0+` source germ.
