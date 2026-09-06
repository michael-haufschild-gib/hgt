# Signed prime recursion and changing arithmetic alignment

**Status:** two empirical hunches falsified; exact signed cofactor transport and a divisor information audit formalized. No new all-scale cancellation bound and no RH proof. Numerical results are exploratory, despite this folder's pipeline location.

Positivity is suspended as the proposed producer in this investigation. This is a research constraint, not a theorem that all positive or spectral methods fail. Corpus starting points, frozen predictions, controls, and adaptive decisions are in [PROTOCOL.md](PROTOCOL.md).

## What the algebraic audit establishes

The actual observable is exactly

`R(N)=-sum(n<=N) lambda(n) w(n) - N sum(n<=N) lambda(n)/n`,

where `w(n)=sum(p prime dividing n) log p` counts each distinct prime divisor once. Expanding theta and reindexing the finite product region proves this: complete multiplicativity and the prime value -1 give `lambda(m)=-lambda(pm)`.

`LiouvillePrimeErrorDivisorAudit.lean` proves both the theta-pairing collapse and the full error identity, unconditionally and without computational premises. Scratch/direct checks and the named leaf build pass; both axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The alignment observable therefore re-expresses weighted Liouville cancellation; it does not supply a second independent arithmetic constraint. A representation may still expose a useful estimate, but that estimate has not been found.

The cyclic-shift controls break complete multiplicativity. Their ranks discriminate from the chosen coarse-data controls, but cannot establish a mechanism beyond the multiplicative identity they destroy. The generic signed dilation theorem also holds for every ratio kernel, so that theorem alone does not distinguish the literal counting-error kernel. **Further alignment scans are paused.** A new experimental target must state a source-specific property or estimate, distinguish it from these identities, and specify controls that retain the properties it claims to use.

## What changed our understanding

The literal arithmetic does not consistently make the measured prime-counting error smaller. Relative to interventions preserving every dyadic cofactor block's sign count and signed sum, it can strongly suppress or strongly amplify the same error pairing. The reversal involves many cofactor scales and survives removing the smallest cofactors. An apparent doubling law mostly extends to other primes, but has decisive failures.

These observations reject a fixed direction of improvement for this observable. They do not yet identify a replacement asymptotic law. The exact residue specifies what a signed dilation argument must control instead of assuming reversal.

## Experiment 1: keep both discarded remainders

For a completely multiplicative sign function f and S(N)=sum(n<=N) f(n), the corpus's exact log recursion gives

`S(N) log N = P(N) + Elog(N) + Epp(N)`,

where P is the signed prime sum, Elog is the log-weight replacement error, and Epp is the complete contribution from higher prime powers. The existing general bounds on the two errors are O(N), inadequate for an RH producer.

At all **37** literal Liouville cutoffs from 4096 through 2097152, Elog and Epp have the same sign. At the last cutoff their values divided by sqrt(N) are approximately **-1.34944** and **-2.75630**. Their addition provides no saving. Four of seven random completely multiplicative controls also reinforce at every tested cutoff; the other three sometimes cancel. Thus the two discarded errors do not exhibit a distinctive hidden cancellation in this sample. See `results.json`.

## Experiment 2: reverse prime and cofactor summation

Let theta be the actual Chebyshev prime sum and define

`R(N)=sum(m<=N) lambda(m)(theta(N/m)-N/m)`.

The exact reversed prime sum is `P(N)=-N sum(m<=N) lambda(m)/m - R(N)`. Keep theta fixed and cyclically shift the cofactor signs independently within each dyadic block, preserving each block's charge and sign count. Cofactors 1,2,3 stay fixed. These interventions destroy multiplicativity: they are alignment controls, not alternative zeta functions.

In the discovery batch, the literal R(N) has signed ranks **0,2,62,64,64** among 64 controls at N=2^15,2^17,2^19,2^21,2^23. Small literal error is therefore not a stable explanation. The last two cutoffs motivated H1: literal amplification above the 95th percentile at five specified new cutoffs with 128 new controls.

H1 failed at **four of five** withheld cutoffs:

| N | R(N)/sqrt(N) | Controls below literal / 128 |
|---:|---:|---:|
| 1,572,864 | 5.89199 | 83 |
| 3,145,728 | 6.98704 | 115 |
| 5,242,880 | 13.12915 | 128 |
| 7,340,032 | 7.35780 | 97 |
| 16,777,216 | 1.83435 | 0 |

At non-dyadic cutoffs the final partial block is shifted only within its visible prefix, preserving its charge too. See `reverse-results.json`, `holdout-results.json`, and [signed-reversal.png](signed-reversal.png).

## Attribution and hostile dilation test

For each visible dyadic block B, subtract the exact charge-only contribution:

`C_B(N)=sum(m in B) lambda(m)e(N/m) - mean_B(lambda) sum(m in B)e(N/m)`, with `e(x)=theta(x)-x`.

This is a signed decomposition, not a positive energy. At dyadic endpoints, summing these terms is exactly the literal excess above the expectation of uniform independent block rotations. That expectation is calculated directly, not estimated by Monte Carlo.

| N | sum C_B(N)/sqrt(N) | Contribution from m>=64 |
|---:|---:|---:|
| 2^21 | 5.93133 | 4.57860 |
| 2^22 | -5.51131 | -4.18844 |
| 2^23 | 4.28934 | 3.57922 |
| 2^24 | -3.99934 | -3.12344 |

The uncentered R itself is negative at 2^22, approximately `-0.399596 sqrt(N)`. Neither its observed sign nor the centered excess is fixed across these cutoffs.

The corpus's exact coefficient law lambda(pn)=-lambda(n) suggested H2: the centered excess reverses under each p in {2,3,5,7}, for N in {2^19,2^20,2^21}. **10 of 12** comparisons reverse, but H2 is false: at N=2^19 the normalized centered excess is **1.69135**, while at 3N and 7N it remains positive, **0.563684** and **1.01793**. Do not retain H2 by removing those primes. See `dilation-results.json` and `analysis.json`.

## Exact surviving theorem and missing mathematics

For the actual, uncentered R, Lean proves for every prime p and every N:

`R(pN)+R(N)=sum(n<=pN, p does not divide n) lambda(n)(theta(pN/n)-pN/n)`.

The divisible cofactors cancel exactly. The right side is retained; setting it to zero or bounding it by coarse sign counts would invent the missing producer. More generally, every positive integer a gives `R(aN)-lambda(a)R(N)` equal to the nondivisible cofactor sum. The proof works for every real-ratio kernel and is then specialized to the literal theta counting error.

`LiouvilleSignedCofactorDilation.lean` contains four unconditional finite-sum theorems. This is a derived bridge, not a claimed novel universal law or an RH equivalence. No numerical result enters its proofs. Scratch and direct source checks pass, as does the named-module final build; the module is wired into `RHTower.lean`. No umbrella build was run. Scratch axiom audits report only `propext`, `Classical.choice`, and `Quot.sound` for all four theorems. Current repository `scripts/formal_tools.py lint` reports the separately added `ChronologicalHeatMellin` module as unreachable from its umbrella. The signed-cofactor and divisor-audit leaves are wired; neither is the reported wiring error. [Formal statement and proof scope](../../../3-formalized/liouville-signed-cofactor-dilation.md).

The intended chain remains exact arithmetic → deterministic signed cancellation at all scales → all strict half-power Möbius bounds → the corpus's closed Mertens criterion → RH. The new cancellation law and its propagation are missing. The experiments do not settle whether this route can supply them; renaming the retained remainder would not count as progress on those obligations.

## Reproduction and limits

All numerical batches ran on the authorized Runpod in `/root/rh-signed-recursion-20260906`, with up to eight processes and one BLAS/OMP thread per worker. Python 3.8.10, NumPy 1.24.4; plotting uses the existing private matplotlib 3.7.5 directory `/root/rh-route-surprise-20260906/plotlib`. Every numerical command had a 120-second cap; the longest new experimental batch completed in **5.28 seconds**. Data, scripts, analysis, and figures are downloaded here.

Run `experiment.py`, then `reverse.py` with its default arguments. The H1 command is `reverse.py --power 24 --cutoffs 1572864 3145728 5242880 7340032 16777216 --seed 86100 --count 128 --output holdout-results.json`. Attribution uses `--power 24 --cutoffs 2097152 4194304 8388608 16777216 --seed 97500 --count 1 --output attribution-results.json`. H2 uses `--power 24 --cutoffs 524288 1048576 1572864 2621440 3670016 2097152 3145728 5242880 7340032 4194304 6291456 10485760 14680064 --seed 98500 --count 1 --output dilation-results.json`. The single controls in attribution/H2 have no statistical interpretation; only the directly computed centered quantities are used. Run `analyze.py` last with the private plotting directory in PYTHONPATH.

Signs are independently reconstructed from smallest prime factors on a short prefix. The exact weighted and reversed identities are checked numerically; maximum absolute residuals are about `5.9e-7` and `5.3e-7`, respectively, across sums much larger than the reported normalized sign margins. This is ordinary floating-point validation, not interval certification. Finite ranks and sign patterns do not prove asymptotic bounds or locate any zeta zero.
