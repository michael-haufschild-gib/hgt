# Damped exact flux: incompatible Fourier signs

**Outcome:** all four preregistered damping choices have a robust numerical conflict between
two centers. No RH sign theorem, Lean theorem, or all-parameter exclusion follows from this run.
The earlier single-flux transition experiment remains unrun.

The [protocol](PROTOCOL.md) and [script](probe.py) were uploaded before execution. Runpod used
12 processes on its 32-core host, with one BLAS/OpenMP thread per process. Versions were
NumPy 1.24.4, SciPy 1.10.1, and mpmath 1.3.0. The foreground command had a 180-second cap;
it completed normally in **4.690 seconds**, including both high-precision checks. No larger scan
or adaptive rank expansion was run. Raw output: [results](results.json), [grid selection](grid.json),
[log](run.log), and [checksums](SHA256SUMS).

## Observed conflict

At aperture `a=1/4`, let `W±` be the normalized native Fourier kernels at centers `x±`,
and let `h+>0>h-` be the damped correction coefficients. The necessary compatibility margin is
`M=(h+ W- - h- W+)/(h+ - h-)`.

| Damping λ | Frequency b | x+ | x- | High-precision M |
|---|---|---|---|---|
| 7/4 | 14.75 | 0.225 | 0.2375 | −2.02665203456422 × 10⁻⁶ |
| 2 | 14.75 | 0.225 | 0.2375 | −2.44102695436160 × 10⁻⁶ |
| 3 | 14.25 | 0.2 | 0.2125 | −4.76492684731409 × 10⁻⁶ |
| 5 | 13.5 | 0.175 | 0.1875 | −1.18729961334081 × 10⁻⁵ |

Both native Fourier values are negative in every selected pair. Therefore the issue is stronger
than a small mismatch of bounds: at `x+`, `W+ + h+ c≥0` requires `c>0`; at `x-`,
`W- + h- c≥0` requires `c<0`. One correction value cannot satisfy both. This elementary
implication is exact; the signs of these particular literal-source values are numerical findings.
The conflict does not depend on the additional normalization `C(0)=0`.

The maximum discrepancy between the two double-precision quadrature grids was
`6.41016 × 10⁻¹⁴`; the frozen provisional threshold was `6.41016 × 10⁻¹²`. Independent
60-digit/10-atom and 90-digit/18-atom integrations agree in the displayed signs and digits.
Atom counts varied as specified in the protocol; the displacement cutoff remained 4.
This is a numerical consistency check, not a certified error bound for the complete integral.

## Analytic follow-through

Damping repairs the divergent normalized tail coefficient, but creates a center at which its
entire correction vanishes. There is an independent reason that taking arbitrarily large damping
cannot solve that problem. Fix `0<a<1/2` and write

```
Λ_a(x) = 1/x + a coth(2ax) + ℓ'(x),  x>0,
h_(a,λ)(x) = 2x exp(-2λx)[Λ_a(x)-λ].
```

As `x→0+`, smooth evenness gives `ℓ'(x)→0`, and `Λ_a(x)→+∞`.
The existing Lean theorem
`RHTower.exists_thetaCuspNativeOddHankelThreeDet_neg_near_zero`
supplies `δ>0` on which the native odd rank-three determinant is strictly negative.
Choose `0<ε<δ`. For every `λ>Λ_a(ε)`, continuity supplies a center `0<x<ε`
with `Λ_a(x)=λ`. At that center the whole correction vanishes, including all displacement
derivatives, so the corrected kernel retains the negative native block for every smooth profile
`C`. In particular this applies to every Schwartz profile, the regularity class considered here.
Thus sufficiently fast damping fails independently of the numerical table. This is a paper
deduction from the formal source theorem; the deduction itself has not been formalized.

For completeness, the slow-damping tail observation in the protocol uses the first-atom
asymptotic of the complete source. With `t=exp(-x)u`,

```
p_x(exp(-x)u) → exp(-4πu²),
W(x,b) ~ exp(-x)/2                      (fixed b),
h_(a,λ)(x) ~ -4πx exp(-2(λ-1)x).
```

The Gaussian limit follows by expanding `cosh(2t)-1` in the reflected first-atom product;
higher atoms have exponentially smaller relative tails. A fixed small displacement window has
a Gaussian bound after this rescaling; logarithmic concavity and the source envelope control
its complement. Consequently `W/(-h)→0` for `λ≤3/2`. Compatibility then requires
`c(b)≤0` at every frequency. Under the proposed zero-mass condition `C(0)=0`, the correction
is zero. Allowing a nonzero value at displacement zero does not rescue this slow-damping
case either: the formal negative native determinant at center zero implies `W(0,b)<0` at
some frequency. Indeed, if its Schwartz Fourier transform were everywhere nonnegative,
the Fourier moment identity would make every native Hankel quadratic form nonnegative.
At that frequency, `h(0)=3` and `c(b)≤0` only worsen the negative value.
These asymptotic arguments are paper analysis for Schwartz profiles, not numerical premises
or new Lean results.

Together these arguments leave only a bounded range of scalar damping as an undecided
possibility. The sampled conflicts do not cover that range. No claim that every scalar damping,
every correction, or CLG/TTF itself is impossible is made.

## What the more general correction still has to prove

Allowing center and frequency to interact removes the two-center scalar restriction. It does
not automatically supply the missing sign. Set

```
ρ_a(x) = 4x sinh(2ax) Φ(x)²,
q_a(x,b) = ρ_a(x) W(x,b).
```

A flux `H_a(x,b)` that vanishes at both center boundaries changes this density to
`q_a+∂_x H_a` without changing its integral. If the corrected density is nonnegative, necessarily

```
∫ max(-q_a(x,b),0) dx ≤ ∫ max(q_a(x,b),0) dx,  for every b.  (2)
```

The exact source/Fourier incidence in the corpus identifies this complete signed comparison
with the required Fourier-current sign. Defining a flux from its antiderivative merely moves
(2) into the terminal boundary condition. No independent source estimate proving (2) was
obtained. In particular, the experiment supplies no justification for dropping negative centers,
assuming a terminal flux vanishes, or invoking an unproved positive reserve.

The next mathematical work must establish that full comparison, or give a source-specific
positive representation that establishes it. Another damping scan or finite-rank correction would
not establish it. The frontier map was read only; no Lean process or build was started for this run.
