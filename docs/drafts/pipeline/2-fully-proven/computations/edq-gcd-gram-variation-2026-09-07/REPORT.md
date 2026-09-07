# Actual weighted Gram: exact-gcd total variation

Numerical research guidance. No result is a Lean premise or an RH proof.
Protocol frozen before execution; computation and numerical analysis ran on
the authorized RunPod. All seven downloaded/source files match its SHA256 manifest.

## Outcome

All eight cases satisfy the frozen finite discriminator `V < 4D`, including
the analytic allowance for the complete omitted infinite tails. V is the sum
of absolute exact-gcd contributions; D is the actual full Gram diagonal.
This supports attacking separate complete-gcd estimates. It establishes no
uniform bound at untested cutoffs.

| M | Source | Diagonal D | Signed norm range | Total variation range | V/D range |
|---:|:---|---:|:---|:---|:---|
| 64 | raw | 2.042703 | 0.920770–0.943035 | 4.737701–4.787460 | 2.319329–2.343689 |
| 64 | averaged | 1.422202 | 1.012258–1.034289 | 1.454314–1.504284 | 1.022580–1.057715 |
| 128 | raw | 2.557874 | 1.044052–1.065707 | 4.894435–4.944432 | 1.913478–1.933024 |
| 128 | averaged | 1.899390 | 1.025349–1.047021 | 3.238998–3.288986 | 1.705284–1.731602 |
| 256 | raw | 3.083247 | 0.992417–1.013834 | 5.147108–5.197106 | 1.669379–1.685595 |
| 256 | averaged | 2.395836 | 1.017581–1.039189 | 4.498410–4.548355 | 1.877595–1.898442 |
| 512 | raw | 3.608556 | 1.101003–1.122300 | 5.239787–5.289787 | 1.452045–1.465901 |
| 512 | averaged | 2.907855 | 1.023306–1.044792 | 4.492785–4.542782 | 1.545051–1.562245 |

Averaged coefficients have X=M/4 and exactly the corpus's logarithmic taper.
The signed norm is the modular-source norm, not the target-error norm.
Every case has both positive and negative gcd groups. The largest observed
`r*|C_r|` moves from r=2 to r=6; its raw M=512 upper value is 7.661071.
Positive-only or prime-only group models would discard observed terms.
Arithmetic grouping and temporal-band deletion are different partitions;
the previous experiment's temporal failure does not predict this outcome.

## Full-source quantities and compression

Put `F(k)=sum_(d<=M)a(d)*(k mod d)/d` and `w(k)=1/[k(k+1)]`.
Define `E_q=sum_(k>=1)(sum_(q|d,d<=M)a(d)*(k mod d)/d)^2*w(k)`.
Finite divisor inversion gives `C_r=sum_(l<=M/r)mu(l)*E_(rl)` and
`sum_r C_r=E_1`. Thus C_r retains every pair whose exact gcd is r.

For k=qt+i, 0<=i<q, the multiples channel is `A_q(t)+(i/q)*H_q`,
where `A_q(t)=sum_j a(qj)*(t mod j)/j` and `H_q=sum_j a(qj)/j`.
A divisor sieve forms A_q. Direct block moments handle t<16. For t>=16,
a geometric expansion through order 19 computes the three weight moments
of 1, i/q, and (i/q)^2. The diagonal uses the same moments and convergent
Hurwitz-zeta tails. No large coordinate-by-divisor matrix is built.

Let m_q=sum_j |a(qj)|, excluding the identically zero unit residue.
After B_q complete blocks the E_q tail is at most `m_q^2/(q B_q)`.
The frozen allocation sets `a_q=tau(q)*m_q^2/q`, `L=sum_q sqrt(a_q)`,
and `B_q=ceil(L*sqrt(a_q)/0.05)`, at least 17 for active channels.
Hence `sum_q tau(q)*tail_q <= 0.05`. Propagate those bounds through
Möbius inversion with their actual signs before taking absolute values.
Individual E_q prefixes end at different coordinates, but all bounds refer
to their complete infinite E_q, so they describe the same full C_r.

## Validation and numerical limits

Eight independent Python workers; native thread pools limited to one.
Python 3.8.10, NumPy 1.24.4, 63-bit long-double mantissa.
Wall time 4.048205 seconds under a 180-second limit. No fitted threshold or
follow-up sweep ran. All controls passed:

- Compressed moments versus direct sums: relative discrepancy below 1.21e-19.
- Compressed versus direct finite channel energy: absolute discrepancy below 1.09e-19.
- Modulus-two diagonal versus log(2)/4: discrepancy below 3.12e-19.
- Independent spot checks of accumulated divisor sums: discrepancy below 8.38e-13.
- Signed divisor-inversion reconstruction: discrepancy below 6.51e-19.

The analytic geometric-series remainder is below 1.64e-20 for each total
variation and 8.76e-25 for each diagonal, separately from the infinite-tail
allowance. Variation ranges include a further 1e-7 numerical sensitivity
margin. Floating-point rounding was checked by independent formulas, not
certified by interval arithmetic. These are not formal numerical certificates.

## Consequence for the proof attempt

The candidate is a bound on complete exact-gcd groups, with compensation and
later coordinates retained. The data do not license a sign assumption on
individual groups or on the quadratic head coefficient. The working card
records a rational obstruction to the latter and a derived subpower estimate
after the exact initial quadratic term is removed. Cancellation against the
complete later tail remains the hard target.

Artifacts: `PROTOCOL.md`, `experiment.py`, `INPUT_SHA256SUMS`, `results.json`,
`run.log`, `analysis.py`, `analysis.txt`, and `SHA256SUMS`.
