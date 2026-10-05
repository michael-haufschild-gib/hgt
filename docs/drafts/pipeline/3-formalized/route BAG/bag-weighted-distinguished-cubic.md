# BAG complete weighted distinguished placements and literal labels

- **Stage:** 3-formalized

Route: signed physical BAG cubic. Continuation01ad. Paper proofs and both
production Lean audits and all21 public-declaration axiom probes pass. Registry
audits pass; global lint has33 unrelated unreachable modules. No growing
cubic cancellation estimate.

## All weighted distinguished placements

Write c_z for the actual complex local coefficient, h=z/(1-z), and
W_k=sum_(i,j in Z) c_z(i)c_z(j)c_z(i+j+k)x^i y^j. The previous full
weighted trace supplies W_0, and the audited third-shift leaf supplies W_1.

For any integer k, the diagonal i+j=k contributes the FINITE sum

    D_k = sum_(i=-1 to k+1) c_z(i)c_z(k-i)x^i y^(k-i).

Proof of full HasSum: express this as a finite sum of pair atoms at (i,k-i).
Outside the indicated interval one of the actual coefficient factors is
zero. No conditional double-sum interchange is needed. In particular,

    D_-1 = -h*(x^(-1)+y^(-1)),
    D_0 = 1-h*(y/x+x/y),
    D_1 = x+y-h*(y^2/x+x^2/y).

The exact coefficient predecessor identity, valid even at z=1, is

    c_z(t-1)=c_z(t)+h*1_(t=-1)-(1+h)*1_(t=0).

Consequently each full weighted offset satisfies
W_(k-1)=W_k+h*D_(-k-1)-(1+h)*D_(-k). Using k=0,-1 proves

    W_-1 = W_0-h^2*(x^(-1)+y^(-1))-(1+h)*D_0,
    W_-2 = W_-1+h*D_0-(1+h)*D_1.

Each equality is a full HasSum for ||x||,||y||<1, since the correction is a
finite signed atom sum added to an already absolutely convergent sum.

For nonzero x,y, translating i->i+a,j->j+b gives the complete three-slot
shifted sum as x^(-a)*y^(-b)*W_(c-a-b). Actual distinguished placements have
a,b,c in {0,1}, so -2<=c-a-b<=1, including all coincident prime labels.
The four proved offsets therefore cover EVERY placement. Specialize to
z=p^(-1), x=p^(-1-i*tau), y=p^(-1-i*upsilon): the corpus proves their
nonvanishing and ||x||=||y||=1/p<1 for every prime p and real tau,upsilon.
Finite-product HasSum assembles the entire (Z^2)^P lattice, retaining both
Mellin frequencies. These final prime/finite-prime statements have no
analytic premise. They do not pass to an infinite prime net or to a physical
Mellin integral without a further proof.

## Individual distinguished labels equal physical primes

The already audited actual-source factorization has summands

    E_P(p,n)=log(p)*(I_(p divides n)-I_(p^2 divides n))
                * product_(q in P prime, q!=p) (1-I_(q divides n)).

Each E_P(p,n) is nonnegative for prime p. The square indicator is at most the
prime indicator; all other factors lie in {0,1}. Take P={0,...,M}. The
actual critical atom theorem gives sum_p E_P(p,n)=log(n) for prime n and
zero otherwise, for EVERY 1<n<=M. If n is composite, nonnegativity and
the zero sum force each individual entry to vanish. If n is prime, a
different prime p does not divide n, while E_P(n,n)=log(n). Hence

    E_P(p,n)=log(p)*1_(n=p)

for every retained prime label and every covered coordinate. Finite subtypes
encode those domains; no analytic premise is assumed.

Multiply the existing literal noncontracting projector on a triple Fourier
character (a,b,c) by E_P(p,a)E_P(q,b)E_P(r,c). This product vanishes unless
(a,b,c)=(p,q,r). When nonzero, the exact physical exclusions a=c or b=c
are precisely p=r or q=r. Thus BOTH literal contraction projectors, with
their intersection restored, can be moved to distinguished-label equality.
This is a theorem about the actual projector, not an identification with
the old valuation-vector axes.

## Remaining frontier

Still prove the actual reduced rational node weights and their normalization,
then transfer the complete weighted trace through the full physical profile,
all integer lifts, near-cone tails and coupled growing scale. The finite-prime
trace alone gives no signed o(N/log(N)^2) estimate. Growing moments, moving
cofactors, common-height self-return and RH remain open.

Production audits: ChiRamanujanDistinguishedPrimeLabels87443 and
ChiRamanujanWeightedDistinguishedCubic77712, both exit0 with empty logs,
using lake --old env lean with leaf output. Six plus15 public declarations.
Index30505 passes; all21 API entries and single imports verified. No full
or umbrella build. Axiom25745 exits0: all21 declarations use only propext,
Classical.choice and Quot.sound. Lint75464 exits1 with33 unrelated unreachable
modules; no new-leaf/proof-debt error. Global lint is not clean.

All owned processes terminal. Completed scratch sources removed; logs/search
JSON retained. No added axioms, resource-limit changes, numerical experiments,
subagents, full/umbrella builds or commits. RH goal remains active.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.ChiRamanujanDistinguishedPrimeLabels`, `GaloisForLFunctions.RHTower.ChiRamanujanWeightedDistinguishedCubic`, `GaloisForLFunctions.RHTower.ChiRamanujanDistinguishedLocalValues`, `GaloisForLFunctions.RHTower.ChiRamanujanWeightedThirdShift`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean`/`lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the RHTower umbrella; statements re-verified claim by claim against this paper card):
`GaloisForLFunctions.RHTower.ChiRamanujanDistinguishedPrimeLabels`, `GaloisForLFunctions.RHTower.ChiRamanujanWeightedDistinguishedCubic`, new `GaloisForLFunctions.RHTower.ChiRamanujanDistinguishedLocalValues` (explicit `D_k`, predecessor identity); base `GaloisForLFunctions.RHTower.ChiRamanujanWeightedThirdShift`.

| Claim | Declaration |
|-|-|
| `D_k` finite HasSum; `D_{−1}`, `D_0`, `D_1` explicit | `weightedValuationDiagonal`, `weightedValuationDiagonal_hasSum`, `weightedValuationDiagonal_neg_one_hasSum`, `weightedValuationDiagonal_zero_hasSum`, `weightedValuationDiagonal_one_hasSum` |
| predecessor identity `c_z(t−1) = c_z(t) + h1_{t=−1} − (1+h)1_{t=0}`; `W_{k−1} = W_k + hD_{−k−1} − (1+h)D_{−k}` | `complexCoefficient_pred`, `weightedConeOffset`, `weightedConeOffset_pred` |
| `W_{−1}`, `W_{−2}` full HasSum; all offsets `−2 ≤ k ≤ 1` | `weightedConeEulerMinusOne`, `weightedConeEulerMinusTwo`, `weightedConeOffset_neg_one_hasSum`, `weightedConeOffset_neg_two_hasSum`, `weightedConeEuler`, `weightedConeOffset_hasSum` |
| translation; every distinguished placement; actual primes; finite-prime lattice | `weightedShiftedLocal`, `weightedShiftedLocal_translate`, `weightedShiftedLocal_hasSum`, `primeWeightedShiftedLocal_hasSum`, `finitePrimeWeightedShiftedCubic_hasSum` |
| `E_P(p,n) ≥ 0`; `E_P(p,n) = log p·1_{n=p}` on the band | `ramanujanDistinguishedPrimeEntry`, `ramanujanDistinguishedPrimeEntry_nonneg`, `ramanujanDistinguishedPrimeEntry_band` |
| both contraction projectors move to label equality | `ramanujanDistinguishedPrimeEntry_projector` |

The physical transfer, signed estimate and RH are not claimed.

The earlier Lean certificate of this lane is `../bag-weighted-distinguished-cubic.md` (stage 3, flat folder).

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
