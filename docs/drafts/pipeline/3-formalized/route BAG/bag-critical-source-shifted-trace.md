# BAG distinguished critical source and complete shifted trace

- **Stage:** 3-formalized

Route: signed physical BAG cubic. Continuation01ac. Three linked exact
arithmetic results; the reduced-rational source match and weighted physical
near-cone estimate remain open. All three production leaves and all17
public-declaration axiom probes passed. Registry/API audits passed; final
global lint has35 unrelated unreachable modules and is not clean.

## Actual finite source at every integer frequency

Let Q be the primes retained in a finite natural-number set P, and I_d(n)
the indicator d divides n. The literal finite critical square-sieved atoms
have Fourier coefficient

    sum_(p in Q) log(p)*(I_p(|n|)-I_(p^2)(|n|))
      * product_(q in Q, q!=p) (1-I_q(|n|)).

This holds for every integer n, including zero and integers outside any
covered band. It has no analytic premise and does not take a prime-set limit.
I_d is precisely the multiplier of normalized full d-torsion averaging.
Thus the differentiated prime has U_p-U_(p^2), not the old delta-U_p factor.

Proof. A prime square divides gcd(rad(P)^2,n) exactly when that retained
prime square divides n. The existing square-sieve indicator is therefore
product_p(1-I_(p^2)(n)). Rewrite the finite incidence multiplier as
product_p(1-exp(-epsilon*log(p))*I_p(n)). At epsilon=0 each sieved factor
equals 1-I_p, since I_(p^2)=1 implies I_p=1. Its derivative is
log(p)*(I_p-I_(p^2)). The finite product rule gives the displayed sum.
Taking the right slope limit and using the already proved finite atom
limits identifies this derivative with the ACTUAL critical atom coefficient.
Every atom and square-sieve factor is retained.

## Complete shifted valuation trace

Use the corpus coefficient c_z(i)=1 for i>=0, -z/(1-z) for i=-1,
and zero below. For all integers a,b,c and 0<z<1,

    sum_(i,j in Z) c_z(i+a)*c_z(j+b)*c_z(i+j+c)*z^(i+j)
      = z^(-c)*c_z(a+b-c)/(1-z)^2.

This is an absolutely convergent full pair sum. Indeed c_z is bounded;
c_z(i)*z^i is a geometric sequence minus (1-z)^(-1) times the atom at -1.
Translation preserves summability, with a nonzero scalar z^(-a). The
product of the two translated weighted sequences dominates the pair
summand up to a fixed constant. Full Fubini is therefore valid.

Fix i and translate j to j+b. The inner sum is

    c_z(i+a)*z^(i-b)*sum_j c_z(j)*c_z(j+i+c-b)*z^j.

The corpus's complete dilation theorem kills every row except i=b-c.
That row has exactly the displayed value. No valuation sector is omitted.
The trace vanishes exactly when a+b-c < -1. In particular,

    sum_(i,j) z*c_z(i+1)*c_z(j)*c_z(i+j)*z^(i+j) = z/(1-z)^2,
    sum_(i,j) z*c_z(i)*c_z(j)*c_z(i+j+1)*z^(i+j) = -z/(1-z)^3.

The statements specialize unconditionally to every actual prime z=1/p,
and finite-product summation gives the full lattice (Z^2)^P for every
finite prime set and arbitrary shifts at each prime.

## What this resolves and what it does not

The unchanged unshifted orthogonality law cannot be applied after replacing
one slot by its distinguished-prime shift: the exact trace can be nonzero,
with its sign determined above. The positive survivor is the complete
all-shift trace and exact zero classification, not merely a failed zero
conjecture. No BAG route is retired.

The normalized local coefficient predicted by U_p-U_(p^2) is z*c_z(i+1),
supported down to valuation -2. The equality of the FULL finite rational
node weights to these normalized shifted coefficients is still to prove;
the all-integer Fourier identity above is not claimed as that node-weight
theorem. Neither result identifies all physical near-cone lifts or permits
removing the r/Mellin-dependent profile. Signed o(N/log(N)^2) cancellation,
growing moments, moving cofactors, common-height self-return and RH remain open.

Production ChiRamanujanShiftedCubicTrace audit15708 and
ChiRamanujanCriticalDistinguishedPrime audit23006 both exited0 with empty
logs, using lake --old env lean with leaf output. Eight plus five public
declarations. Both imports wired once; no umbrella or full build.
Axiom87231 exited0, all13 names use only propext, Classical.choice, Quot.sound.
Index63528 passed, all13 API entries and single imports checked. Lint7342
exited1 with35 unrelated unreachable modules; no new-leaf/proof-debt error.

## Full complex weighted third-slot correction

For the existing complex coefficient c_z and h=z/(1-z), the exact full
weighted sum of c_z(i)c_z(j)c_z(i+j+1)x^i y^j, for ||x||,||y||<1, is

    weightedEuler(z,x,y) - h^3*x^(-1)*y^(-1)
      - h*(1+h)*(x^(-1)+y^(-1)).

The change from the old summand is supported on precisely the three possible
pairs (-1,-1), (-1,0), (0,-1). Their coefficients are -h^3 and
-h*(1+h) in the respective weighted slots. Proof by the actual coefficient
support gives the pointwise identity on EVERY integer pair. The existing
complete weighted HasSum minus those finite atomic HasSums proves absolute
summability and the displayed full signed value. No numerical calculation
or removal of a tail is used. Keeping 1+h makes the formula valid even at
z=1; using (1-z)^(-1) in its place would require z!=1.

The theorem specializes without hypotheses to every actual prime p and all
real tau,upsilon, with z=p^(-1), x=p^(-1-i*tau), y=p^(-1-i*upsilon).
The corpus's norm_cubicPrimeBase proves ||x||=||y||=1/p<1. Thus the complex
Mellin weights remain. This extends the unweighted negative third-slot
value; it still does not identify the full physical profile with this sum.

Scratch86201 and ChiRamanujanWeightedThirdShift production37262 passed;
production log empty. All four public declarations passed axiom88278 with
standard axioms only. Final index48316 passed; all25 public entries across
the four01ac leaves and exactly one import each verified. Final lint98092
exited1 with35 unrelated unreachable modules and no new-leaf/proof-debt error.
The other shifted slots and simultaneous shifts
still need their full weighted corrections, together with the literal
reduced rational node grouping and justified physical action transfer.

All owned processes terminal; completed scratch sources removed, logs and
search JSON retained. No added axioms, resource-limit changes, numerical
experiments, subagents, full/umbrella builds or commits. RH goal remains active.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ChiRamanujanCriticalDistinguishedPrime`, `GaloisForLFunctions.RHTower.ChiRamanujanShiftedCubicTrace`, `GaloisForLFunctions.RHTower.ChiRamanujanWeightedThirdShift`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
`GaloisForLFunctions.RHTower.ChiRamanujanCriticalDistinguishedPrime`, `GaloisForLFunctions.RHTower.ChiRamanujanShiftedCubicTrace`, `GaloisForLFunctions.RHTower.ChiRamanujanWeightedThirdShift`.

| Claim | Declaration |
|-|-|
| finite critical source at every integer: `Σ_p log p(I_p − I_{p²})Π_{q≠p}(1−I_q)`; square sieve `= Π(1−I_{p²})`; derivative limit | `ramanujanTorsionIndicator`, `ramanujanSquareSieveWeight_eq_primeProduct`, `ramanujanDistinguishedPrimeMultiplier`, `tendsto_ramanujanPrimeOnlyMultiplier_distinguished`, `sum_ramanujanCriticalPrimeAtomWeight_fourier_distinguished` |
| complete shifted trace `= z^{−c}c_z(a+b−c)/(1−z)²` for all integers `a,b,c`, `0 < z < 1`; zero iff `a+b−c < −1` | `shiftedLocalTriple`, `shiftedLocalTriple_summable`, `shiftedLocalTriple_hasSum`, `shiftedLocalTriple_tsum_eq_zero_iff` |
| tagged values `z/(1−z)²`, `−z/(1−z)³`; every prime; finite-prime lattice | `firstTaggedLocalTriple_hasSum`, `thirdTaggedLocalTriple_hasSum`, `primeShiftedLocalTriple_hasSum`, `finitePrimeShiftedCubic_hasSum` |
| weighted third-slot correction (pointwise and full HasSum, `‖x‖,‖y‖ < 1`), actual primes and Mellin weights | `weightedThirdShift`, `weightedThirdShift_decomposition`, `weightedThirdShift_hasSum`, `primeWeightedThirdShift_hasSum` |

The reduced-rational node weights, physical transfer and RH are not claimed.

The earlier Lean certificate of this lane is `../bag-critical-source-shifted-trace.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
