# Transverse energy when advancing the retained prime front

Numerical diagnostic, not a Lean proof or an RH conclusion. The
[frozen protocol](../../../5-failed/ccm-fu-transverse-front-renewal.md)
precedes execution. No numerical result enters a Lean proof.

Let Q(M,P) be complete retained energy, F_R its signed fibre, and
T(M,P)=Q(M,P)−F_empty²−F_{2}². Test whether inserting the smallest remaining
prime other than two necessarily decreases T, when the fixed child core
{3,5,7,11,13} has been processed and all primes above M/15 remain available.
Prime 17 is retained in every tested state.

## Results

| Cutoff M | States | Positive gains | Fixed-core gain / original diagonal |
| --- | ---: | ---: | ---: |
| 512 | 64 | 0 | −0.01032433 |
| 2048 | 64 | 43 | 0.05810025 |
| 8192 | 64 | 29 | 0.08232163 |
| 32768 | 64 | 9 | 0.08999379 |

The fixed-core column always uses P={3,5,7,11,13}, without additional
processed primes. It suggests testing the existing fixed-core correlation
limit directly; these four values do not prove its sign or an asymptotic
lower bound.

The first flagged state is M=2048, P={3,5,7,11,13}. Independent original
time-sum reconstruction at 80 decimal digits gives

    T(P)       = 2175.281118171437933967342136343880338179...
    T(P+17)    = 2463.545537963806082780860587392427454390...
    difference =  288.264419792368148813518451048547116211...

The difference is approximately 5.8100 percent of the original diagonal.
Both receiving coordinates are already small: F_empty≈−4.107856 and
F_{2}≈3.509041, compared with sqrt(2048)>45. The sign failure is not
explained by a large receiving head.

The complete signed formula used by the primary screen is

    Delta_17 T = 2 sum_{R != empty,{2}; 17 not in R} F_R F_{R union {17}}
                 − F_{17}² − F_{2,17}².

Several positive products outside the receiving pair pay more than the
negative absorbed squares. Examples include paired labels71/1207,
67/1139,47/799 and74/1258; the last pair has both fibres negative. All
terms are retained in audit.json. The primary formula was also checked
against independently merging the grouped field and subtracting the two
transverse energies in every state.

The negative sign claim is numerically falsified. Its finite counterexample
has not been converted into symbolic interval inequalities or a Lean
counterexample. The independent audit is high-precision floating-point
arithmetic, not rigorous interval arithmetic. It reconstructs the source
from the original time sum and a separately factored squarefree support;
the primary screen uses the quotient-block sum and a prime-factor sieve.
Their witness gains differ by approximately 1.48e−11, far below the
frozen threshold 1e−10*max(1,Q_empty).

This does not refute bounded cumulative transverse cost, existence of
another prime choice, a complete bounded-energy order, or a sign law
restricted to a different cofinal cutoff family. No follow-up range scan
or tuning was performed.

## Positive mathematical result

The [source reserve commutation theorem](../../../3-formalized/ccm-fu-transverse-reserve-commutation.md)
is proved symbolically in Lean. Every child-inactive two-coordinate helper
block subtracts its own copied-square reserve from T, independently of
its displacement. For any other available prime q≠2, the T cost of
inserting q is exactly unchanged after that block. The same equality
holds for any additional finite prime core avoiding two and the helpers.
Thus head balancing cannot change a positive transverse gain into a
nonpositive one; the cumulative transverse gains still need a budget.
This identity uses no experiment output.

## Execution and provenance

- Supplied RunPod host 157.157.221.29:27094.
- Four independent cutoff workers; numerical-library threads set to one.
- Primary screen elapsed 0.4996054694 seconds; independent witness audit
  elapsed 1.3129573166 seconds.
- Each run had an internal 90-second deadline and external 100-second limit
  with a five-second kill grace. Primary worker cleanup uses terminating
  signal handlers.
- All four source/result file hashes match their downloaded copies.
- The owned remote directory and its four files were removed. A final
  /proc working-directory inspection found no owned processes.

## SHA-256

| File | Hash |
| --- | --- |
| screen.py | 77bcc9058e05d01f20fdbe49536ab800b5a046512324cb2e5e2605cde2313427 |
| audit.py | f960143957577259404cd4e0058cd48acab1011f22906ac5391a30cb205ee9cb |
| summary.json | 9c4bf339732196c85a002435114c73e30aeab4c62977c2e71d74db1b34dd6822 |
| audit.json | 9f42113307f42a3da80747a1c61f6dce5fb5150fff8d0fa7dcc3ea24892fcb25 |
