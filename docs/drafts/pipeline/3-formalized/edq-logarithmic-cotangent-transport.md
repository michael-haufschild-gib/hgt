# EDQ: exact logarithmic cotangent transport

- **Stage:** 3-formalized
- **Date:** 2026-09-06
- **Scope:** finite source identities and unweighted orientation; no RH proof or falsification
- **Source card:** [weighted-head comparison](../1-in-progress/edq-logarithmic-cotangent-orientation.md)
- **Lean:** `RHTower/ArithmeticCotangentPhaseTransport.lean`, `RHTower/ArithmeticLogarithmicCotangent.lean`

## Exact theorem and paper proof

Write `E_j=exp(2*pi*i*phi_j)`, `delta_j=phi_(j+1)-phi_j`, `q_j=cot(pi*delta_j)`, with `phi_0=0`. Lean cutoff M includes samples 0 through M. Define

`D_M(w)=sum_(j=0..M) w_j*sin(2*pi*phi_j)`

`       +w_M*sin(2*pi*phi_(M+1))/2`

`       -w_M*q_M*(1-cos(2*pi*phi_(M+1)))/2`.

For every real phase sequence and every real weight sequence,

`D_M(w)=sum_(j=0..M-1) [(w_(j+1)-w_j)*sin(2*pi*phi_(j+1))/2`

`       -(w_(j+1)*q_(j+1)-w_j*q_j)*(1-cos(2*pi*phi_(j+1)))/2]`

`       +sum_(j=0..M, sin(pi*delta_j)=0) w_j*sin(2*pi*phi_j)`.

Proof: the corpus coefficient is `c_j=-1/2-i*q_j/2`. Outside resonance it satisfies `c_j*(E_(j+1)-E_j)=E_j`. At resonance the chord is zero, so the original sample is retained separately. Finite summation by parts and taking imaginary parts give the displayed equality. No infinite limit or zero assumption is used.

When weights are one, nonresonant increments lie in `(0,1)`, and increments decrease, cotangents increase. Every remaining `1-cos` factor is nonnegative, so `D_M<=0`. For strict decrease and M>0, the first interior phase lies strictly between zero and one and supplies a strictly positive cost: `D_M<0`.

For `phi_j=t/(2*pi)*log((n+j)/n)`, n>=1 and t>0, the exact increments are

`delta_j=t/(2*pi)*log(1+1/(n+j))`.

They are positive, strictly decreasing, and strictly below `t/[2*pi*(n+j)]`. Thus `0<t<2*pi*n` gives strict orientation for every M>0. When the terminal logarithmic angle is an integer multiple of `2*pi`, the endpoint correction vanishes and the literal finite sine sum is strictly negative.

At arbitrary positive height, once `t<2*pi*(n+J)`, each later new increment is nonresonant and each cotangent difference is positive. Subtracting consecutive identities gives `D_(M+1)<=D_M`, hence `D_M<=D_J` for every M>=J. The original finite head value remains on the right side.

## Literal source identification

`rotated_power_eq` proves the exact complex-power identity with anchor rotation and weight `w_j=(n+j)^(-sigma)`. At n=1, `rawPrefix_im_eq` identifies the sine sum with the actual Dirichlet prefix at `s=sigma-it`. `sourcePhaseDefect_eq` then rewrites the entire defect using the actual power-sum remainder, zeta value, power normalization, and endpoint kernel. All are retained, including at t=0 or a resonant increment. The universal identity is valid for every real sigma and t.

The principal declarations are:

| Declaration | Content |
| --- | --- |
| `PhaseCotangent.weightedPhaseDefect_eq` | Universal weighted/resonant equality |
| `PhaseCotangent.phaseDefect_nonpos`, `phaseDefect_neg` | Finite unweighted orientation |
| `LogarithmicCotangent.logarithmicPhase_increment_lt` | Explicit all-height increment bound |
| `LogarithmicCotangent.logarithmicPhase_defect_neg` | Every first-band finite cutoff |
| `LogarithmicCotangent.logarithmicPhase_defect_le_head` | All later cutoffs bounded by actual finite head |
| `LogarithmicCotangent.logarithmicPhase_closed_prefix_neg` | Exact closing-phase sine-sum sign |
| `LogarithmicCotangent.sourcePhaseDefect_eq` | Literal weighted remainder identity, all heights |

All namespaces above have the prefix `RHTower`.

## Audit boundary

The construction is classical finite summation by parts using the existing Kuzmin–Landau coefficient. Corpus searches found no prior signed logarithmic specialization; this is not a literature novelty claim. Every resonant sample, endpoint, and weight drift survives. The unweighted sign is not asserted for the actual weighted remainder. No computation, numerical certificate, new axiom, or zeta-zero premise supplies the sign.

The weighted sine drift, product-cotangent drift, and initial head still need a joint arithmetic comparison. These results do not prove R's linear normalized-remainder threshold, B2, C, or RH.

## Lean validation

Both proofs passed `lake env lean` scratch checks. The two serialized final leaf audits passed with `lake build --old` and one foreground Lean process at a time. Both modules are wired into `RHTower.lean`; no umbrella was built. Only the 39 new declarations (31 theorems and 8 definitions) were checked with `#print axioms`; their only dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The existing corpus was not re-audited.

The corpus index was refreshed once. `scripts/formal_tools.py lint` passed with existing large-file warnings.
