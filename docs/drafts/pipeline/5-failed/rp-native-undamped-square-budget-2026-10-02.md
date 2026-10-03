# RP: finite undamped native square budget is impossible

Status: obstruction and positive survivor formalized and audited.
Parent: rp-selberg-prejump-forcing-2026-10-02.md (RP-50).

Rejected assertion: the literal complete native profile

    h(t) = exp(-t) * mobiusDivisorFullHead(exp t)

has an integrable square on t>0. This is a zero-damping obstruction;
no positive-damping budget and no RH assertion is rejected.

## Strong positive survivor

For every real budget B and cutoff T, some U>=T satisfies

    integral_0^U h(t)^2 dt > B.

Every finite interval admits this square. The same escape holds for the
literal Route-P resolvent ray. The exact source identification
H_full(x)=criticalContinuousAbel(x) holds at every real x, retaining the
complete physical divisor cutoff.

## Dependency-closed paper proof

If the Route-P ray R were square integrable, its causal Laplace transform
L would be analytic for Re z>0. The reconstructed function
-s*((s+1/2)*L(s-1/2)+2/3)-1 agrees with the regularized-zeta logarithmic
derivative for Re s>1. The corpus analytic-rigidity theorem extends this
agreement to Re s>1/2, hence L equals the actual source continuation.
Cauchy-Schwarz gives |L(sigma+i tau)|^2 <= integral|R|^2/(2 sigma), so
sigma*L(sigma+i tau)->0. A literal positive-height Hardy zero supplies a
nonzero residue -m/(rho*(rho+1/2)) at z=rho-1/2. These limits contradict.
No RH premise is used, including internally for zero existence.

The full Möbius head and critical Abel primitive agree at integers by
finite Möbius inversion. On [n,n+1], a finite core containing all primes
through n+1 agrees with the full head and is affine in sqrt(x). Both
endpoint values agree with the critical Abel primitive, which has the
same interpolation. Both sources vanish below one. This proves all-real
agreement without taking a full-ray limit over prime cores.

The existing Route-P correction then gives

    R(t)^2 <= 8*h(t)^2 + 2*(20/3)^2*exp(-t), t>=0.

Thus an integrable native square would imply an integrable R square.
Local admission follows from the actual core-free head envelope and
measurability. A uniform bound for all late partial integrals would imply
global square integrability by exhaustion, proving the positive survivor.

## Lean and audit

- RoutePSourceCriticalSquareNonintegrability.lean: leaf audit69078 exit0.
- RoutePNativeCriticalSquareEnergy.lean: leaf audit87829 exit0.
- Both used foreground `lake --old env lean <leaf> -o <olean>`.
- Scratch audit64016 exit0: all seven public theorems use only propext,
  Classical.choice, Quot.sound. No added axiom or hypothesis closes a gap.
- Both leaves are wired into RHTower.lean; no umbrella/full build.
- Lint8491 exit1: fourteen unrelated unreachable modules; neither new
  leaf is reported. Global lint is not green.

## Remaining route obligation

RP-51 also rejects a finite zero-damping negative-part budget for the
complete native coprime cross work C(t)=exp(-t)*CC(nativeProfile,t).
Its positive survivor is cofinally unbounded partial mass of max(-C,0),
with literal CC negative arbitrarily late. A hypothetical finite negative
mass first admits each damped square by domination against the admitted
combined balance. Compact dominated convergence then bounds all
undamped partial square energies, contradicting the survivor above.
Local negative-part admission follows by removing the epsilon=1 weight
on each finite interval and subtracting the locally admitted square.

Dependency-closed proof and audited Lean status are recorded in
../3-formalized/rp-native-negative-coprime-work-2026-10-02.md.
RoutePNativeNegativeCoprimeWork.lean passed leaf audit51819 and scratch
axiom audit18596; all three public results use only the standard logical
axioms. Uniform cutoff bounds for each positive damping, high-LCM signed
control, both native history debts, and unconditional RH remain open.

## RP-52: full signed survivor

The complete undamped balance B=h^2+C is now proved absolutely
integrable with integral zero. The actual unit-head Lipschitz bound
gives inverse-square L1 costs for adjacent reciprocal-square profile
dilations. Exact finite Abel summation combines them against Mertens
partial sums; unconditional inverse-square Mertens summability admits
the full source. The zero Mobius harmonic mass fixes its integral.
Exponential change of variables retains every native coprime pair.

Stronger positive survivor: max(C,0) is integrable, and
integral_0^T C + integral_0^T h^2 tends to zero. The full signed work
integral tends to minus infinity. Thus even a finite lower budget for
undamped signed cross work is impossible; this is not just divergence
of its negative part. Positive-damping negative work remains unpaid.

Dependency-closed proof and six verified results:
../3-formalized/rp-native-undamped-signed-balance-2026-10-02.md.
Leaf audit2035 exit0; final API and axiom scratch37380 exit0 reports only
standard logical axioms for all six results. No RH proof or falsification follows.
