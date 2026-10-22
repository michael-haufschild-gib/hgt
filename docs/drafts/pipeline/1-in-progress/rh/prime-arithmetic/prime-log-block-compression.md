# Prime logarithmic block compression

Status: complete arithmetic comparison bound, holomorphic correction, and nonzero limit of literal finite Euler quotients are Lean-closed. The resulting zero-preservation argument is proved below on paper; no Lean RH endpoint or zero-free producer is claimed. RH remains open. This is a derived `[BRIDGE]`, not a primary conjecture or a claimed new theorem in the literature.

## Target and source

For each integer `k >= 2`, let `P_k` be the ordinary primes in `[k^4,(k+1)^4)`, let `m_k=|P_k|`, and let `c_k` be their mean logarithm (zero for an empty block). Replace these primes by `m_k` copies of `exp(c_k)`, retaining primes below 16 exactly. The proposed complete Euler product retains two literal arithmetic statistics per block: its prime count and sum of prime logarithms.

Target rigidity: its continuation and ordinary zeta have exactly the same zeros, with multiplicities, in `Re(s)>1/2`. No RH or prime-distribution estimate enters the proposed comparison. This would simplify the source; proving zero-freeness of the compressed source remains the hard problem.

## Proof attack

Write `D_k(s)=sum_(p in P_k) exp(-s log p)-m_k exp(-s c_k)`.
The centered logarithms sum to zero, and each has magnitude at most `4/k`. The block contains at most `15 k^3` integers. The exponential Taylor remainder therefore gives, for `sigma=Re(s)>=0`,

`|D_k(s)| <= 240 |s|^2 exp(2|s|) k^(1-4 sigma)`.

For `E(x,s)=-log(1-exp(-sx))`, the full discrepancy is

`A_k(s)=sum_(p in P_k) E(log p,s)-m_k E(c_k,s)`.

The higher-power remainder satisfies `|E(x,s)-exp(-sx)| <= exp(-2 sigma x)` whenever the exponential has modulus at most `1/2`. At `k>=2`, `sigma>=1/2`, this gives

`|A_k(s)-D_k(s)| <= 30 k^(3-8 sigma)`

and hence the Lean-closed full bound

`|A_k(s)| <= (240 |s|^2 exp(2|s|)+30) k^(1-4 sigma)`.

On every compact subset of `Re(s)>1/2`, bound `|s|` above and `Re(s)` below strictly above `1/2`. The resulting power series majorant is summable. Each summand is holomorphic because `1-exp(-sx)` lies in the right half-plane. Thus `A=sum_k A_k` is holomorphic there and `U=exp(-A)` is nonzero. Lean also identifies the literal finite quotient

`prod_(2<=k<K) [prod_(p in P_k)(1-p^(-s)) / (1-exp(-s c_k))^m_k]`

with `exp(-sum_(2<=k<K)A_k(s))` and proves its convergence to `U(s)`.

### Paper continuation argument and precise scope

For `sigma>1`, both original and compressed Euler products converge absolutely. For the compressed one, `m_k<=15 k^3`, `c_k>=4 log k`, and `sum k^(3-4 sigma)` converges. Empty blocks contribute one; primes below 16 are retained identically. Exhausting the quartic blocks exhausts all remaining ordinary primes. The finite quotient identity therefore gives `Z_compressed(s)=zeta(s) U(s)` in this Euler region. The right side defines its meromorphic continuation to `Re(s)>1/2`. Since `U` is holomorphic and nonzero, multiplication by it preserves every zero and its multiplicity there, as well as the pole at 1. This continuation/zero comparison is a paper deduction; the Lean leaf proves the complete source bound and the quotient limit, not an identification of a separately defined infinite compressed Euler product.

This argument does not extend the Euler products themselves into the strip by ordinary convergence. It does not preserve the functional equation or the fixed archimedean component of a Weil form. In particular it makes no claim that changing prime positions preserves an unchanged prime-side positivity test.

## Novelty and rejected shortcuts

The starting corpus obstruction is fixed-prime density fracture (`PrimeSquareMobiusDensityFracture`) and the fact that the signed cofactor observable is a weighted Liouville sum (`LiouvillePrimeErrorDivisorAudit`). Finite-prefix fidelity and a coordinate change supply no estimate.

Bounded single-prime displacement was independently considered and rejected as a novelty claim: [Grosswald–Schnitzer, *A class of modified zeta and L-functions* (1978)](https://msp.org/pjm/1978/74-2/pjm-v74-n2-p09-s.pdf), Theorem 1, already preserves zeros under interlacing prime displacements. Whole quartic blocks contain a growing number of primes; their centroid replacement does not satisfy that interlacing condition. The present argument uses grouped first-moment cancellation, but a general literature priority claim has not been established.

No numerical experiment is needed to check a consequence already forced by the Taylor bound. Before experimenting on the compressed source, a new risky source claim must be stated; convergence of the quotient alone is not that claim.

## Exact gain and remaining hardest problem

The literal prime source may be replaced, for off-line zero detection in the right half-strip, by one location and one integer multiplicity per quartic interval. The locations depend only on each block's count and total logarithm. The error from removing the remaining within-block geometry has an unconditional bound at every scale and an admissible complete arithmetic limit. This is an actual source simplification, unlike a rearrangement of the same weighted Liouville observable.

It supplies no estimate excluding zeros of the compressed source. Replacing the retained counts or centers by their continuous prime-density predictions would introduce a new error whose required cancellation has not been proved. The uniform constants above grow with height and the summed power majorant deteriorates as `sigma` approaches `1/2`. Neither this theorem nor finite numerical data supplies the missing all-scale cancellation. No primary zero-free conjecture beyond the original RH target has survived a discrimination test in this investigation.

## Formal scope

Module: `formal/GaloisForLFunctions/RHTower/PrimeLogBlockCompression.lean`, imported by `RHTower.lean`.

Fifteen public theorems, including `quarticPrimeFirstDiscrepancy_bound`, `quarticPrimeEulerDiscrepancy_bound`, `summable_quarticPrimeEulerDiscrepancy`, `differentiableOn_quarticPrimeEulerDiscrepancySum`, `quarticPrimeCompressionFinite_eq_exp`, and `tendsto_quarticPrimeCompressionFinite`. Scratch and source checks use `lake env lean`; named leaf build passes. Numerical results are not proof inputs. Axiom and repository lint results are recorded in the formal card.

## Discrimination of retained-source mechanisms

[Prime-block feedback experiments](../../prime-block-feedback.md) leave the missing source estimate open. Eight-lag count/centroid prediction and uniform contraction at each dyadic merge fail their frozen tests. Whole-block mean-square suppression survives initial prescribed boundary shifts and held-out ranges, while individual blocks expand by as much as 3.77018 times their mean fine-cell square. Its fixed average margin also fails the final larger-scale test. These finite numerical obstructions rule out treating the observed average as pointwise contraction or the tested fixed margin as uniform; they are not Lean no-gos or a rejection of source compression.
