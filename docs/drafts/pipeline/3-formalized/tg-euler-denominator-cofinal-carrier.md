# TG C9.11h — exact moving carrier of the Euler denominator

- **Stage:** 3-formalized
- **Type:** PROVED exact finite carrier and common-core rigidity, with nonzero finite survivor
- **Route:** TG, cofinal source admission after denominator clearing.

## Hard target

C9.11g exposes a change of Sonin carrier under the actual finite Euler denominator.
Determine that carrier exactly, then decide whether a common nonzero fixed-carrier
core survives all finite prime stages. This attacks cofinal admission, not a bound.

Let A_p be the existing `evenPrimeLocalFactor`, A_S its full finite physical
product, Q_b the Sonin projection, and R_c the Fourier cutoff. Write
P_S=∏p∈S p. For f with any positive initial Fourier gap, conjecture the sharp law

`R_c(A_S f)=0 iff R_(P_S c) f=0` for c>0.

For f∈K_b this would classify simultaneous membership:

`A_S f∈K_b iff R_(P_S b) f=0`.

The physical gap is preserved by every inverse-dilation factor in A_S. Thus the
survivor is the anisotropic carrier with physical gap b and Fourier gap P_S b,
unitarily related by dilation to the ordinary Sonin carrier of aperture sqrt(P_S)b.
Every finite stage should remain nontrivial; the common fixed-carrier core over
all prime stages should be zero.

## Paper mechanism to audit

For one prime, cutoff covariance turns `R_d A_p f=0` together with `R_d f=0` into
`R_(pd) f=0`, since the scalar coefficient is nonzero and dilation is injective.
If `R_c A_p f=0` and f initially vanishes below some d>0, finitely iterate this
implication while d<c, using the smaller cutoff d at each step. Powers of p cross c;
one final step gives `R_(pc) f=0`. The converse follows immediately from covariance
and cutoff nesting. No numerical iteration or computed bound is required.

For a finite product, the other factors preserve some positive gap (possibly
smaller). Apply the one-factor inverse-gap theorem successively to recover the
exact product P_S. Physical-hole preservation follows from the existing inverse
dilation cutoff identity. Unbounded genuine primes and Fourier cutoff exhaustion
then force every vector in the common fixed-carrier core to vanish.

## Source evidence

- `SoninEulerCalkinPartialIsometry`: exact Fourier cutoff/dilation covariance,
  nesting, and `evenIndicatorCutoff_mul_inverseDilation_mul_soninProjection`.
- `HardyTitchmarshSourceTransport`: A_p is identity minus nonzero scalar inverse dilation.
- `SoninApertureFourierParityNoGo`: membership in K_b is exactly vanishing of both cutoffs.
- `SoninPrincipalRelativeApertureNoGo`: existing Euclid/Archimedean prime-crossing proof;
  its conclusion concerns aperture defects, not this common denominator carrier.
- C9.11g: full finite denominator and its adjoint are literal Mellin polynomial operators.

## Limits and positive survivor

Triviality of this fixed common core would rule out only an unchanged-carrier
construction. It would not rule out graded moving carriers, a relative mapping
cone, or RH. The exact finite anisotropic-carrier classification is the mandatory
positive survivor, and must be formalized before closing any fixed-carrier proposal.

## Log

- 2026-10-02: deep search for common Sonin preservation was partial with no useful
  hits; exact lexical search returned the cutoff covariance and inverse-dilation
  source lemmas. Direct source inspection grounds the new conjecture above.

## Verified outcome — 2026-10-02

`CCMEulerDenominatorCarrier` proves seven public theorems and defines the actual
finite scale P_S. For **any** positive initial Fourier gap d and any c>0,
`R_c A_S f=0 iff R_(P_S*c)f=0`. The one-factor inverse proof propagates
`min(c,p^n*d)` until it reaches c; the finite product induction retains every
factor and starts each intermediate vector with its proved positive gap.

For f∈K_b, b>0, the exact classification is
`A_S f∈K_b iff R_(P_S*b)f=0`.
The physical gap is preserved. Across all genuine primes, and equivalently
across all finite prime sets including the empty stage, the common fixed carrier
contains exactly zero. Fourier cutoff exhaustion and Euclid's theorem prove
this without any numerical experiment or Euler-inverse bound.

**Positive survivor is proved:** for every finite S and b>0, there exists f≠0
with both f and A_S f in K_b. A nonzero vector in
K_(max(b,P_S*b)) suffices. Nontriviality of that actual even Sonin carrier follows
from the existing noncompact dilation-corner theorem. Thus the common-core
obstruction is not caused by vacuous finite carriers.

Foreground final leaf audit passed using `lake --old env lean ... -o ...` at
default heartbeats. All eight public axiom queries return only `propext`,
`Classical.choice`, `Quot.sound`; umbrella wired. Full formal lint reports ten
unrelated unwired modules and no failure in these new leaves.

The earlier proposed unitary identification with K_(sqrt(P_S)*b) is **not yet
formalized**. Genuine eventual admission (discarding finitely many starting
stages, without assuming an initial Fourier gap) is the next sharper target in
`tg-euler-denominator-eventual-carrier`. Cofinal moving-domain admission,
matrix-complete cubic-index comparison, and the sub-unit law remain open.
