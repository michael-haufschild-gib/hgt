# EDQ complete flux: uniformly bounded reduced-denominator head

Stage: formalized in Lean.
This is a bound for an explicit part of the complete arithmetic flux, not RH.

For positive d,e write
`K(d,e)=sum_(j>=1)P_e(d*j)/(d*j)^2`, with the actual modular primitive.
Define the literal reduced-denominator head

```
J(N,B) = -sum_(1<=b<=min(B,N)) sum_(1<=r<=floor(N/b))
          sum_(a>floor(N/r), gcd(a,b)=1)
            mu(r*a)*mu(r*b)*K(r*a,r*b).
```

It retains every numerator a and every time j. The conditions are exactly
d=r*a>N, e=r*b<=N, gcd(a,b)=1 and reduced denominator b<=B. The complete
one-complement formula for reciprocalFlux therefore gives J(N,N)=R_N on
paper. That full identification is separate from the head bound below.

**Unconditional bound:** `|J(N,B)|<=B/2` for all natural N,B.

The primitive bound |P_e|<=e/8 and sum_(j>=1)j^(-2)<=2 give absolute
convergence and `|K(d,e)|<=e/(4*d^2)`. For a fixed admitted b,r, put
q=floor(N/r)>=1. The literal Möbius product and coprimality mask have
absolute value at most one, so their entire a channel has absolute mass

```
<= b/(4*r) *sum_(a>q)1/a^2
<= b/(4*r*q)
<= b/(2*N).
```

The last step uses N<=2*r*floor(N/r). There are floor(N/b) admissible r,
so each reduced denominator costs at most 1/2, uniformly in N. Sum over
b<=min(B,N); the N=0 or B=0 case is empty. Absolute summability is proved
before any infinite sum is used. No Möbius cancellation estimate, numerical
input, or RH assumption is required.

This permits a growing reduced-denominator head B of subpower size to be
removed at subpower cost. It leaves all reduced denominators b>B with their
actual signs. The finite experiments rejected both ratio-four localization
and domination of the distant bands by b=2,3. Those observations motivate
retaining the remainder, but are not used in this proof.

## Formal statement and scope

Module: `GaloisForLFunctions.RHTower.EulerDeletionReducedDenominatorHead`.
Namespace: `RHTower.DeletionFlux`.

`completeKernel`, `reducedTerm` and `reducedHead` define the literal kernel,
coprime numerator channel and head. `reducedHead_bound N B` proves
`|reducedHead N B| <= (B:Real)/2` without hypotheses, for every natural N,B.
Its private proofs establish summability of each kernel and admitted numerator
channel. The full identification `reducedHead N N = reciprocalFlux N` is a
paper identity here, not an additional Lean theorem. In particular this module
does not assert that the unbounded reduced-denominator remainder is small.

Scratch validation passed. The final single-module build passed in 2.5 seconds,
compiling only the new leaf and reusing dependency oleans. The leaf is wired into
RHTower without building the umbrella. The four new public declarations were
audited separately; each depends only on `propext`, `Classical.choice`, and
`Quot.sound`. No numerical computation or added axiom enters any proof.
Repository lint and the scoped whitespace check passed. Both owned scratch
files were removed; an exact process audit found no owned Lean process left.
