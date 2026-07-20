# Gamma-sewn Xi-shift tangent Hilbert kernel

- **ID:** `gamma-sewn-xi-shift-tangent-hilbert-kernel`
- **Stage:** `3-formalized/needs-audit`
- **Type:** `[PAPER-PROVED CORE] [LEAN-PROVED CORE] [NO-GO + POSITIVE SURVIVOR]`
- **Scientific status:** `[CORPUS-NEW SOURCE IDENTIFICATION] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnXiShiftTangentHilbertKernel.lean`

## Frontier

The previous CEERT-4H statement had two unresolved defects.  It knew the exact tangent norm
`p^-4` only primewise, so the claimed cross-prime four-rate operator was not yet an object.  It
also asked a centered second compound to reproduce a full three-node determinant, despite their
different compound orders.

This card constructs the missing cross-prime object and proves the exact compound-order no-go.

## `[LEAN-PROVED]` Actual all-depth tangent feature

Put `a=p^-1`, let

```text
d_p(e)=(1-a^2)a^(2e),
h_p(e)=(1-a^2)a(e+1),
psi_p(e)=sqrt(d_p(e)) (h_p(e)-a).
```

The feature has the closed coordinate form

```text
psi_p(e)=sqrt(1-a^2) a^(e+1) ((1-a^2)e-a^2).          (TH1)
```

Lean proves coordinatewise that `psi_p(e)^2` is literally the actual doubled-aperture Xi-shift
depth probability times the squared centered endpoint-height lift.  Thus this is not an auxiliary
geometric distribution or a freely selected Hardy vector.

The exact generating transform is

```text
Psi_p(z)=sum_(e>=0) psi_p(e)z^e
        =a^2 sqrt(1-a^2) (z-a)/(1-az)^2.               (TH2)
```

In particular,

```text
Psi_p(a)=0,                                             (TH3)
```

so father removal is a source root before Gram formation.  The same rational function has a
double pole at `z=p`.  The root and pole are both forced by the ordinary-prime endpoint and the
completed `+2` Xi shift.

## `[LEAN-PROVED]` Cross-prime kernel and true tangent metric

Define

```text
H(p,q)=sum_(e>=0) psi_p(e)psi_q(e).
```

For `a=p^-1`, `b=q^-1`, Lean proves

```text
H(p,q)=a^2 b^2 sqrt((1-a^2)(1-b^2))
       * ((1+ab)^2-2(a^2+b^2))/(1-ab)^3.               (TH4)
```

It also proves

```text
H(p,p)=p^-4,
H(p,q)>0.                                               (TH5)
```

Normalize `u_p=p^2 psi_p` and `C(p,q)=<u_p,u_q>`.  Then

```text
C(p,p)=1,
0<C(p,q)<=1,
sum_e (u_p(e)-u_q(e))^2=2(1-C(p,q)).                   (TH6)
```

This is the missing source-derived cross-prime contraction.  It avoids the exact resolution
deficit because the father mean was removed first, and it avoids HT graph saturation because it
uses the actual shared valuation-depth coordinate without taking the differential-field closure.
It does not yet include causal first-crossing dressing or the two Gamma boundary rows.

## `[PAPER-PROVED; LEAN GENERATING LAW PROVED]` Finite prime rank

Every finite distinct-prime family `{psi_p}` is linearly independent.  Indeed, a vanishing finite
linear combination of the power series gives a vanishing rational function by `(TH2)`.  At the
double pole `z=p`, every summand except the `p`-summand is regular, while the `p`-summand has
nonzero principal coefficient because `p-p^-1 != 0`.  Its coefficient must therefore vanish;
repeat over the finite packet.

Consequently four distinct primes provide four genuine source directions before the canonical
two-boundary compression.  This passes the previously proved four-direction threshold at the
uncompressed height-tangent level.  The rational linear-independence corollary is not yet wired in
Lean; only the exact generating law from which it follows is compiled.

## `[LEAN-PROVED NO-GO]` Second compound is not the three-node determinant

For a common rooted diagonal `k0` and tangent edge values `x,y,z`, Lean proves

```text
det3(k0*J+T)
 =k0 [2(xy+xz+yz)-(x^2+y^2+z^2)] + 2xyz.              (TH7)
```

The theorem is specialized to the actual completed physical endpoint kernel.  Hence

```text
full three-prime determinant = rooted tangent second compound
iff x*y*z=0.                                            (TH8)
```

The old finite falsifier was therefore ill-typed: a second compound cannot reproduce the whole
three-node determinant on a generic packet.  The exact positive survivor is the split in `(TH7)`.
The second compound is the correct producer for the `2 x 2` central Hankel correlation term; the
pure tangent cubic is a separate third-compound remainder.

## Revised conjecture: CEERT-4H2

`[CONJECTURE] [SOURCE-DERIVED] [HEIGHT-LOCALIZED] [INFINITE] [NOT RH]`

Use the actual feature `psi_p`, not merely its diagonal norm.  Apply causal first-crossing dressing
to the calibrated Euler legs, retain the Gamma sewing bit in the same positive joint law, and then
perform the canonical two-boundary four-rate Cauchy compression.

The exact finite target is now:

1. rooted means reproduce the positive local-stiffness marginal;
2. the connected second compound of the dressed `psi_p` packet reproduces the positive
   cross-orbit slope-dispersion term in the `2 x 2` central Hankel identity;
3. the joined Gamma sewing response reproduces the invariant transverse charge before any Jordan
   norms are taken;
4. the pure cubic tangent remainder in `(TH7)` is either transported by a genuine third compound
   or proved negligible under the source-prescribed cofinal height localization.

Contractivity of the undressed shared-depth feature is no longer conjectural: it is `(TH6)`.
The open operator estimate is specifically stability of `(TH6)` under causal dressing,
two-boundary compression, and cofinal response identification.

## Anti-theatre / external audit

- Square-root-density Fisher geometry and its Hilbert-sphere realization are standard parent
  theory; they are not claimed as new.
- Szego kernels and first-derivative reproducing kernels with denominator `(1-az)^2` are standard
  Hardy-space parent theory; they are not claimed as new.
- The determinant expansion `(TH7)` is elementary rank-one/rooted algebra; novelty is not claimed
  for the polynomial identity itself.
- Exact searches found no collision for the forced conjunction `(TH1)`--`(TH6)`: actual completed
  Xi-shift innovations, the physical endpoint height, the inverse-prime root, the double prime
  pole, the explicit cross-prime kernel, and the norm-one contraction in one source object.  This
  is search noncollision, not a priority claim.
- The genuinely new RH-facing statement still to be proved is CEERT-4H2's dressed two-boundary
  response crossing.  Neither generic Fisher geometry nor a generic reproducing kernel answers it.

## Gates

- [x] exact cross-prime source feature constructed
- [x] actual Xi-shift square identity in Lean
- [x] rooted double-pole generating law in Lean
- [x] exact cross-prime Gram formula, positivity, diagonal, and norm-one contraction in Lean
- [x] full-three-node/second-compound conflation retired in Lean
- [x] strongest positive survivor stated as rooted second compound plus tangent third compound
- [x] finite distinct-prime independence proved on paper from the compiled pole law
- [ ] finite distinct-prime independence wired in Lean
- [ ] causal first-crossing dressing of `psi_p`
- [ ] canonical two-boundary four-rate compression of the dressed feature
- [ ] second-compound identification with cross-orbit slope dispersion
- [ ] joined Gamma-sewing identification with transverse charge
- [ ] third-compound transport or cofinal cubic-remainder bound
- [ ] locally uniform response limit / RH
