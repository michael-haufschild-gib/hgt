# EDQ complete-column coherence: frozen diagnostic outcome

Both proposed simplifications failed the frozen finite tests. The complete
signed finite-head estimate remains open; no numerical result is a Lean premise.

## All frozen cases

V is the sum of absolute complete row contributions; R is the full flux.
D is the absolute residual after subtracting the parameter-free Bernoulli
mean profile. Displayed ranges are abbreviated decimal readings of the
saved analytic enclosures; floating-point rounding is not certified.

| N | V/R | D/V | A: V<=4R | B: D<=V/4 |
|---:|:---|:---|:---|:---|
| 32 | 2.9801–2.9816 | 0.6444–0.6447 | survives | reversed |
| 48 | 1.4638–1.4650 | 0.8926–0.8933 | survives | reversed |
| 64 | 1.5117–1.5132 | 0.8249–0.8256 | survives | reversed |
| 96 | 6.0063–6.0140 | 0.4379–0.4383 | reversed | reversed |
| 128 | 1.5019–1.5044 | 0.9904–0.9918 | survives | reversed |
| 192 | 3.9319–3.9405 | 0.5660–0.5668 | survives | reversed |
| 256 | 2.1529–2.1599 | 0.8854–0.8874 | survives | reversed |
| 384 | 2.4862–2.4964 | 0.9925–0.9950 | survives | reversed |
| 512 | 3.3601–3.3806 | 0.9763–0.9792 | survives | reversed |

At N=96 the full flux is enclosed between 0.026768207480418877824 and
0.026797254887105390539, while its absolute row variation is more than six
times that flux. Outer signed cancellation is material at this cutoff.
This falsifies the fixed factor-four comparison, not a subpower bound on V.
Eight other cutoffs satisfy A; none is unresolved.

The zero-frequency Bernoulli profile fails B at all nine cutoffs. Its signed
total is negative at eight cutoffs although the full flux is positive;
its sole positive total, at N=384, is approximately 0.00000484865 against a
full flux near 0.0397. At N=384 the residual retains over 99% of the actual
row variation. Keeping only this mean would discard the dominant source in
that case. The conclusion concerns the stated profile and fixed tests;
no asymptotic power law or alternative fitted model is inferred.

## Execution and controls

The unchanged protocol and script ran on the authorized RunPod with eight
workers, one native numerical thread per worker, in 0.082191 seconds under
the fixed 120-second timeout. Python 3.8.10, NumPy 1.24.4, and 63-bit
longdouble mantissas were recorded. All mathematical analysis ran remotely.
Previously archived full kernel enclosures were reused; no kernel rebuild
or larger scan was run.

All nine full row sums overlap the independently archived full flux.
Every unit-modulus and zero-Möbius row vanishes before the margin, and every
modulus-two row agrees with its independent inverse-square formula.
All input and downloaded output hashes match their frozen manifests.
`results.json` retains every row, both signed masses, all source totals,
both classifications, and the controls. `run.log` is the original output.
The extra 1e-8 per-row sensitivity margin is not a proved rounding bound.

## Surviving mathematical target

The complete finite-head subtraction, all nonzero Fourier modes, and the
actual outer Möbius signs remain in the target. Completion gives an exact
representation and a proved subpower Euler error; neither failed diagnostic
controls the retained signed head. The data do not exclude a subpower total
row-variation bound, nor do they prove one. No RH conclusion follows.

Remote cleanup was checked after the interrupted turn: no process remained
in the experiment directory. Only the eight owned files and that directory
were removed after verifying the downloaded hashes. This task made no
frontier-map edit.
