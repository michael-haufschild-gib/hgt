# Boundary of the observed zero chain

All 208 prescribed paths completed at 50 digits. The target loop is w(u)=1−exp(2πiu), with u from 0 to 1. It carried every tested positive zero numbered 65–128 and 257–320 to its predecessor, extending the earlier observation on zeros 2–64.

The same loop acts differently on the trivial zeros:

| Starting zeros | Observed action |
|---|---|
| −2 | Fixed |
| −4 | Sent to the conjugate of the first positive nontrivial zero |
| −6 and −8 | Exchanged |
| −10 and −12 | Exchanged |
| −14 and −16 | Exchanged |
| −18, −20, …, −32 | Fixed individually |

Reversing the loop sent −4 to the first positive nontrivial zero. Flattening or stretching its imaginary coordinate by factors 0.5 and 1.5 preserved the tested trivial-zero map. The smaller loop 0.35(1−exp(2πiu)) additionally exchanged −2 and −4; it retained the other three exchanges and fixed −18 through −32.

These observations reject a single-chain description covering every zero under this particular loop. Their positive residue is more specific: a long predecessor pattern for the sampled nontrivial zeros, together with distinct moving and fixed components among the trivial zeros. Enlarging a loop can remove an exchange, so its radius alone does not determine the permutation of zeros.

For RH, this is information about how different value fibres connect. It does not show that all nontrivial zeros belong to one component, nor that the zero fibre must lie on Re(s)=1/2. A proof using this geometry would need additional arithmetic rigidity and control of all relevant critical and asymptotic values.

Seven selected boundary and height paths have a separate 100/160-digit, smaller-step, independent Euler–Maclaurin challenge. The full 208-path census remains a finite 50-digit observation; selective validation is not a global certificate. Next discriminating tests concern the critical values responsible for the component differences and whether analogous L-functions share the structure.

Reproduce with `python guard.py experiment.py`. The whole family finished in 107.7 seconds. Code, zero cache, domain restrictions, raw paths, environment and original checksums are retained. No Lean builds or RH proof claim.
