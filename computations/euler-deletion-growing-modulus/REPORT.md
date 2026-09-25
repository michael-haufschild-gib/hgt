# Growing-modulus mixed arithmetic sums

These are exploratory computations, not proof certificates. No numerical result was used in Lean. All numerical work ran on the specified Runpod, under `/root/hgt-rh-growing-modulus-20260906`; scripts and results are retained here.

## Question and method

For `S_N(s)=sum_(n=1..N)n^(-s)`, `c_p=p^(1-s)`, and `Z=zeta(s)`, compute

`T_p(N)=sum_(k=0..N-1)[S_k-c_p S_floor(k/p)-(1-c_p)Z](k+1)^(-conj(s))`.

The conjecture was that its leading modulus growth is `Kp^(2-2 sigma)`, with `K=zeta(2 sigma-1)/(1-conj(s))`, followed by `|Z|²p^(1-s)`. A further conjecture proposed a bounded remaining term at zeros. This tests actual source weights, not a fitted replacement sequence.

`scan.py` uses four process workers, NumPy vectorization, chunked partial sums, and one BLAS/OpenMP thread per worker. It scans moduli `16,32,...,8192` and ordinary cutoffs `N=128p,512p,2048p`, reaching `16,777,216`. The nine points are the first three critical-line zero approximations; horizontal shifts to real parts `0.65` and `0.85` at the first two heights; `1/2+17i`; and real `0.65`. Scalar heights and zeta values use 65-digit mpmath; the main sums use complex128.

Both raw results and estimates subtracting the previously conjectured cutoff correction `(p²-1)/(12N^(2 sigma))` are saved. That subtraction is a convergence aid, not a rigorous tail enclosure. `analyze.py` retains cutoff drift, modulus increments, and fitted coefficients; its amplitude/constant/log fit is diagnostic rather than a complete asymptotic model.

## Results

The bounded-remainder conjecture failed in the critical-line tests. At the first zero, after subtracting `Kp`, the real remainder at `p=1024,2048,4096,8192` is approximately

`-3.46580281, -3.81234290, -4.15889969, -4.50546478`.

The last logarithmic increment slope is `-0.49998774`. The other two tested zeros and the nonzero critical-line control, after its `|Z|²c_p` term is removed, show the same `-1/2` slope. This suggested a universal `-(1/2)log p` term, not zero-specific cancellation.

At fixed real part `0.65` or `0.85`, subtracting `|Z|²c_p` leaves a real remainder whose height dependence is exactly consistent with the additional constant `-|Z|²/2`. Its remaining modulus dependence suggested the real power-sum term

`B_sigma(p)=(1/2)zeta(2 sigma)(p^(1-2 sigma)-1)`.

The imaginary error after these subtractions suggested the next term

`-conj(s) zeta(2 sigma+1)/(12p^(2 sigma))`.

The last two corrected ordinary cutoffs differ by at most about `5.21e-5` in the critical-line zero scans and `3.80e-7` in the shifted scans. Such drift measures do not certify an error bound.

## Independent representation check

Define the exact power-sum remainder

`R_s(n)=S_n-zeta(s)-n^(1-s)/(1-s)-(1/2)n^(-s)`,

`W_p=p^(1-s)sum_(n>=1)n^(-s)R_conj(s)(pn)`.

`verify.py` evaluates the remainder independently through the Hurwitz tail at 65 digits. For `W_1` it evaluates 128 head terms directly and compares Euler–Maclaurin tail orders 8 and 12. For the other checked moduli it uses eight direct head terms and tail order 12. This remains an asymptotic-tail computation, without rigorous interval bounds.

It checks the newly derived identity

`T_p=|Z|²(c_p-1)+K(p^(2-2 sigma)-1)+B_sigma(p)+W_p-W_1`,

where `B_(1/2)(p)=-(1/2)log p`, at moduli `16,32,1024,8192` for all nine points. For example, the first-zero discrepancies against the independently computed cutoff estimates are approximately `1.40e-7`, `1.40e-7`, `1.35e-7`, and `2.67e-7`. The largest discrepancy among the first three zero checks is approximately `8.25e-7`, compatible with their finite-cutoff diagnostics.

The real identity `Re W_1=-|Z|²/2-Re K` has numerical residual below `6.49e-39` at all nine points. The largest order-8 versus order-12 tail drift is below `1.33e-27`. Those numbers support the derived formula; they are not mathematical proofs of it.

## Consequences and limits

The conjecture loop produced a complete arithmetic decomposition, not a term that vanishes merely because `Z=0`. The leading coefficient is universal, the oscillatory growing coefficient is `|Z|²`, and the real power/logarithmic term survives at zeros. In the strict-right strip, the paper derivation makes boundedness of the fixed-dilation, growing-source correction equivalent to `Z=0`; it does not exclude such zeros or make its limiting constant vanish.

[Paper derivation and precise formal scope](../../../1-in-progress/euler-deletion-growing-modulus-decomposition.md) give the arithmetic argument. Three exact finite identities are checked in Lean. The infinite decomposition and its analytic estimates are not yet Lean theorems. This experiment proves neither RH nor impossibility of the missing arithmetic identity, and makes no novelty claim.

Files: `scan.py`, `analyze.py`, `verify.py`, `results.json`, `analysis.json`, `verification.json`. The JSON records parameters, raw and corrected sums, software versions, precision, and comparison results.
