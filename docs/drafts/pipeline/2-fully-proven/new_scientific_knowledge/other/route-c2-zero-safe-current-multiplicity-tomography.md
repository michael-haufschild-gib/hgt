# Route C2 zero-safe current multiplicity tomography

- **ID:** `route-c2-zero-safe-current-multiplicity-tomography`
- **Stage:** 2-fully-proven
- **Type:** CANDIDATE / ROUTE-CLOSURE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `rh-current-frontier-map.md`, Route C2
- **Statement:** At a centered Xi zero `alpha` of multiplicity `m`, the Hedenmalm
  center-mixed current on the transverse line through `alpha` has an exact factorization by
  `(a + alpha.im)^(2m-1)` with a continuous strictly positive residual at the zero. Consequently
  every off-critical zero creates a local negative-current chamber on its critical-line side, and
  the zero-safe current germ recovers the analytic multiplicity as `(vanishing order + 1)/2`.

## Goal and non-theatre standard

Close Route C2 without claiming its RH-equivalent endpoint as progress. The existing complete
aperture-width phase law already identifies positivity above aperture `alpha` with the assertion
that every Xi zero has horizontal displacement at most `alpha`. Hence lowering the last aperture
to zero is exactly RH, not an independent source theorem.

The only admissible positive survivor must add divisor information not present in the global iff:
an exact local normal form at the zeros, a forced sign geometry, or a multiplicity invariant. A
renaming of horizontal modulus monotonicity, another shell decomposition, or a conditional
zero-free implication does not qualify.

## Frozen conjecture

Let `rho : XiDivisorSupport`,

```text
alpha = xiSpectralPointSupport rho,
m     = xiSupportMultiplicity rho >= 1,
Q     = xiThetaDividedChain alpha m,
d     = -alpha.im,
b0    = alpha.re,
x     = a-d = a+alpha.im,
z_a   = b0-a i = alpha-x i.
```

Write the zero-safe transverse Xi energy current

```text
C_Xi(a,b) = 2 Im(XiC'(b-a i) conjugate(XiC(b-a i))).
```

For every real `a`, the conjectured exact divisor normal form is

```text
C_Xi(a,b0)
  = x^(2m-1)
      [2m |Q(z_a)|^2
       + 2x Im(Q'(z_a) conjugate(Q(z_a)))].                 (C2.1)
```

The bracket is continuous in `a` and equals

```text
2m |Q(alpha)|^2 > 0                                       (C2.2)
```

at `a=d`. Therefore there is `epsilon>0` such that

```text
d-epsilon < a < d  -> C_Xi(a,b0) < 0,
d < a < d+epsilon  -> C_Xi(a,b0) > 0.                     (C2.3)
```

When `|a|<1`, `C_Xi(a,b)` is exactly
`thetaCuspCenterMixedFourierCurrent a ha b`; for a right-of-line xi zero,
`0<d<1/2`, so (C2.3) occurs inside the physical Route C2 aperture. Moreover

```text
C_Xi(a,b0) / (a-d)^(2m-1) -> 2m |Q(alpha)|^2 > 0,          (C2.4)
```

and the first nonzero transverse order is exactly `2m-1`. This recovers `m` without dividing by
`XiC`, so it remains meaningful at the divisor where the logarithmic derivative is singular.

## Heavy conjecture / hostile falsification loop

### H1 — infinite shell completion can hide an off-line zero

**Bold claim.** Although every fixed shell prefix has the wrong cusp asymptotic and all finite
endpoint orders cancel only after the cofinal product-fibre sum, the completed current might stay
nonnegative on both sides of an off-line zero.

**Attack.** Insert the exact analytic multiplicity factorization
`XiC(z)=(z-alpha)^m Q(z)` into the zero-safe energy derivative before any shell expansion.

**Expected verdict.** False if (C2.1) holds. Completion may redistribute shell mass, but cannot
alter the odd divisor factor or the positive coefficient (C2.2).

### H2 — a universal quantitative negative-lobe mass exists

**Bold claim.** Multiplicity `m` forces a lower bound, independent of the zero and cofactor, for
the width or integral mass of the negative-current lobe.

**Attack.** Rescale an arbitrary nonzero analytic cofactor and allow nearby zeros. The leading
coefficient is `2m|Q(alpha)|^2`, while the positivity radius depends on continuity of `Q,Q'` and
can shrink with nearby divisor geometry.

**Verdict.** Rejected. No source theorem currently normalizes the cofactor or supplies a uniform
zero-separation radius. Claim would import a new hard zero-spacing estimate.

### H3 — a fixed finite shell prefix detects multiplicity

**Bold claim.** Some source-independent finite shell cutoff has the same first nonzero transverse
order `2m-1` as the completed current at every divisor point.

**Attack.** Compare with the exact source-product-fibre seam spectrum: every finite-order
coefficient cancels only after summing all product fibres, and the ground fibre has the wrong
eventual sign.

**Verdict.** Rejected. Finite prefixes are not divisor-faithful; the survivor is intrinsically a
completed-current theorem.

### H4 — fixed finite Bochner/Hankel rank localizes every defect

**Bold claim.** There is a universal finite matrix size whose failure detects every negative C2
current caused by an off-line zero.

**Attack.** Existing complete-Hankel equivalence uses polynomial density to localize an arbitrary
pointwise negative region. No degree bound follows from continuity, and the lobe radius in H2 is
not uniform.

**Verdict.** Rejected. Any universal finite rank would require new quantitative control absent
from the route.

### H5 — current germ is a multiplicity-faithful divisor transducer

**Bold claim.** Equations (C2.1)--(C2.4) hold exactly and show that the completed current germ,
unlike the singular logarithmic derivative, records every zero with odd order `2m-1` and oriented
sign.

**Attack.** Check sign convention on the path `z_a=alpha-(a-d)i`; check complex conjugation,
natural-number exponents, repeated zeros, and the zero-safe/current identification at `XiC=0`.

**Status.** Surviving conjecture. Paper proof must establish the exact formula before any Lean
implementation.

### H6 — Route C2 remains an independent positivity route after tomography

**Bold claim.** More shell, Wigner, finite-minor, or endpoint-jet refinement can close the
remaining sign without a new zero-width-reducing input.

**Attack.** The complete phase law says, for every `tau>0` and `alpha>=0`,

```text
HedenmalmGaussianHankelTailCone tau alpha
  <-> XiZeroHalfPlaneBound alpha.
```

At `alpha=0` this is exactly RH. The local conjecture further predicts that every violating zero
forces a negative germ, so no cancellation estimate internal to the same completed current can
evade the divisor.

**Expected verdict.** False. If H5 is proved, Route C2 is saturated as an exact divisor detector
and must be retired as an independent mechanism.

## Internal-priority audit

- `HedenmalmGaussianHankelApertureWidthSpectrum.lean` proves the complete tail-cone/zero-width iff
  and its `alpha=0` RH endpoint, but only uses monotonicity against an isolated zero; it does not
  state a local current normal form, forced two-sided sign, or multiplicity recovery.
- `XiHedenmalmMultiplicityChain.lean` supplies the exact factorization and nonzero terminal
  cofactor, but does not connect it to the center-mixed current.
- `ThetaCuspCenterMixedOrientationRankUniversalityLaw.lean` proves the zero-safe energy/logarithmic
  derivative identity, but does not factor its germ at a divisor point.
- Shell, Wigner, product-fibre, central-band, exterior-aperture, three-node, rank-four, and
  incomplete-Gamma cards do not state (C2.1)--(C2.4).

The proposed theorem is therefore a genuine internal synthesis delta. Its ingredients are
existing, so scientific classification is conservatively `[BRIDGE]`, not a claimed primary
breakthrough.

## External primary-source audit

1. Sondow--Dumitrescu, *A monotonicity property of Riemann's xi function and a reformulation of
   the Riemann Hypothesis*, arXiv:1005.1104 / Period. Math. Hungar. 60 (2010), proves horizontal
   modulus monotonicity in zero-free half-planes and its RH reformulation. It does not give the
   zero-safe multiplicity germ.
2. Matiyasevich--Saidak--Zvengrowski, *Horizontal Monotonicity of the Modulus of the Riemann Zeta
   Function and Related Functions*, arXiv:1205.2773, treats horizontal modulus/logarithmic
   derivatives and related RH equivalences, not (C2.1).
3. Michel Planat, *A Theta-Kernel Reformulation of a Growth Theorem and the Riemann Hypothesis*,
   posted 2026-06-01, derives the theta-kernel double integral, unconditional `sigma>1`
   positivity, and the exact remaining global oscillatory positivity problem. This collides with
   Route C2's broad theta-kernel framing and makes that framing non-novel; it does not state a
   zero-safe divisor normal form or multiplicity tomography.
4. Parker Emmerson, *Slip Certificates for the Riemann Xi-Function via Poisson Forcing and
   Carleson Tents*, posted 2026-01-27, proves multiplicity-weighted local forcing for the singular
   logarithmic derivative and integrated positive-part slip. It is the closest collision. The
   proposed survivor instead uses the nonsingular norm-square current, gives an exact odd-order
   pointwise germ, and requires no division or numerical certificate.
5. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, supplies the
   theta-driven eigenproblem and self-adjoint-pair program, not the C2 current germ.

Searches over the exact phrases and formulas found no external statement of (C2.1)--(C2.4).
Absence from search is not a priority proof; external status remains `[NOVELTY UNVERIFIED]`.

## Paper-proof obligations

- [x] Prove a general zero-safe transverse current formula for analytic `f`.
- [x] Differentiate the exact Xi multiplicity factorization on the transverse line.
- [x] Prove (C2.1) with correct sign and exponent for every `m>=1`.
- [x] Prove bracket continuity and strict positivity at `a=d`.
- [x] Derive the two-sided physical-aperture sign chamber and normalized limit.
- [x] State exact route disposition and strongest positive survivor.
- [ ] Formalize the dependency-closed theorem unconditionally in Lean.

## Dependency-closed paper proof

### Lemma 1 — zero-safe transverse energy derivative

Let `f` be complex differentiable at `z_a=b-a i`. Along the real transverse path,

```text
g(a)=f(b-a i),             g'(a)=-i f'(z_a).
```

Writing `f=u+iv` and differentiating `|f|^2=u^2+v^2` gives

```text
d/da |f(b-a i)|^2
  = 2 Re((-i f'(z_a)) conjugate(f(z_a)))
  = 2 Im(f'(z_a) conjugate(f(z_a))).                     (P1)
```

No nonvanishing premise occurs. At a zero both sides are defined and vanish. Taking `f=XiC`
identifies the right side with `C_Xi(a,b)`. The exact Fourier/Krein identity already proved in the
repository identifies `C_Xi(a,b)` with the actual C2 current whenever `|a|<1`.

### Lemma 2 — exact energy factorization on a divisor transverse

The multiplicity-chain theorem gives, for every complex `z`,

```text
XiC(z)=(z-alpha)^m Q(z),             Q(alpha) != 0.        (P2)
```

At `z=z_a=b0-a i`, direct coordinate arithmetic gives

```text
z_a-alpha=-i(a+alpha.im)=-ix.
```

Since `|-ix|^2=x^2`, multiplicativity of squared norm in (P2) yields the global real identity

```text
|XiC(z_a)|^2=x^(2m)|Q(z_a)|^2.                           (P3)
```

This holds for every real `a`, including `a=d`.

### Lemma 3 — exact current normal form

Differentiate (P3). The polynomial factor has derivative
`2m x^(2m-1)`, because `dx/da=1`. Applying (P1) to `Q` gives

```text
d/da |Q(z_a)|^2=2 Im(Q'(z_a) conjugate(Q(z_a))).          (P4)
```

The product rule, followed by `x^(2m)=x^(2m-1)x` (valid because `m>=1`), proves exactly

```text
C_Xi(a,b0)
 = x^(2m-1)
    [2m|Q(z_a)|^2+2x Im(Q'(z_a) conjugate(Q(z_a)))].
```

This is (C2.1). It is an equality of ordinary real functions, not an asymptotic expansion, and
uses neither RH nor a zero-free neighborhood.

### Lemma 4 — positive residual and forced sign chamber

`Q` is entire because every member of the canonical divided chain is entire. Hence `Q'`, `Q`,
their conjugate product, and the residual bracket

```text
B(a)=2m|Q(z_a)|^2+2x Im(Q'(z_a) conjugate(Q(z_a)))
```

are continuous. At `a=d`, `x=0`, so

```text
B(d)=2m|Q(alpha)|^2>0
```

because `m>=1` and `Q(alpha)!=0`. Continuity supplies `epsilon_0>0` with `B(a)>0` whenever
`|a-d|<epsilon_0`. The exponent `2m-1` is odd, so `x^(2m-1)` has the sign of `x=a-d`.
Equation (C2.1) now proves (C2.3), as well as `C_Xi(d,b0)=0`.

### Lemma 5 — normalized limit and multiplicity tomography

For `a!=d`, divide (C2.1) by `(a-d)^(2m-1)` to obtain exactly `B(a)`. Continuity then gives

```text
lim_(a->d, a!=d) C_Xi(a,b0)/(a-d)^(2m-1)
  = B(d)=2m|Q(alpha)|^2>0.
```

Therefore the current germ has exact first nonzero transverse order `2m-1`: lower order would
contradict the finite normalized limit, and higher order would force that limit to zero. Solving
for `m` recovers the analytic multiplicity as `(order+1)/2`. Unlike `XiC'/XiC`, this observable is
defined at the zero itself.

### Lemma 6 — physical C2 chamber for every off-line zero

Suppose `rho.re>1/2`. Since `rho` is a xi divisor support point, `xi(rho)=0`; the classical
critical-strip bound gives `rho.re<1`. With `d=rho.re-1/2`, this says

```text
0<d<1/2.
```

Also `alpha=rho.im-d i`, so `b0=rho.im`. Choose

```text
epsilon < min(epsilon_0,d,1/2-d).
```

Then both intervals `(d-epsilon,d)` and `(d,d+epsilon)` lie inside the physical aperture
`0<a<1/2`, where Lemma 1 identifies `C_Xi` with
`thetaCuspCenterMixedFourierCurrent`. Thus every hypothetical right-of-line zero forces an open
negative C2 chamber immediately below its displacement and an open positive chamber immediately
above it. Left-of-line zeros give the reflected statement.

## Route disposition

Route C2 is **saturated and retired as an independent RH route** once the exact survivor is
formalized. Reasons are structural:

1. Complete C2 positivity above aperture `alpha` is already equivalent to the actual Xi divisor
   width bound `|Re rho-1/2|<=alpha`.
2. At `alpha=0`, the requested remaining sign is exactly RH.
3. The local theorem proves that any violating zero necessarily survives every infinite shell
   cancellation as a negative completed-current germ of exact odd order.
4. Fixed shell prefixes, fixed derivative orders, fixed matrix ranks, generic positivity, and
   generic log-concavity have already failed and cannot alter this divisor normal form.

**Strongest positive survivor:** the completed theta-cusp center-mixed current is an exact,
zero-safe divisor transducer. Its phase threshold recovers horizontal zero width; its local sign
recovers side/orientation; its odd germ order recovers analytic multiplicity. This is new internal
knowledge and a source-specific bridge, but not a proof of RH.

Any future progress must introduce a genuinely new theorem that shrinks actual Xi zero width from
source data. More C2 coordinates, shell cancellations, or finite positivity packets without such
an input are bookkeeping, not a new route.

## Gates

- [x] 0 -> 1: source object fixed; attack is exact factorization; internal/external collisions
  audited; no numerical evidence used
- [x] 1 -> 2: dependency-closed paper proof
- [ ] 2 -> 3: exact unconditional Lean theorem, umbrella wiring, axiom/lint/final-build audit
- [ ] 3 -> 4: independent priority and expert review

## Log

- 2026-08-01 — conjecture frozen after internal phase-law audit and current primary-source audit.
- 2026-08-01 — exact paper proof closed; Route C2 classified as saturated pending Lean survivor.
