# Constrained restricted Weil form across the prime-2 entry: rigorous certificate

Companion computations of the card
`docs/drafts/pipeline/1-in-progress/weil-polar-bombieri-yoshida-prime-two-entry.md`
(programme P2) and of the Lean modules `RHTower/SuzukiWeilConstrainedKernelForm.lean`
(exact kernel form) and `RHTower/ConstrainedWeilTaylorLocalization.lean` (Taylor localisation).

## Object

`a = S/2`, `V₀ = {f ∈ L²[-a,a] : ∫ e^{±x/2} f = 0}` (polar-constrained subspace).  On `V₀` the
restricted Weil form is the Fourier multiplier (Lean: `suzukiRestrictedWeilForm_eq_constrainedKernelForm`
gives the `h`-side identity; the `ξ`-side is Plancherel for the autocorrelation)

```
Q(f) = (1/2π) ∫ |f̂(ξ)|² m_S(ξ) dξ,
m_S(ξ) = A(S) + Λ_S(ξ) − Σ_{n ≥ 2, log n < S} (2Λ(n)/√n) cos(ξ log n),
Λ_S(ξ) = ∫_0^S K₊(u)(1 − cos uξ) du,  K₊(u) = e^{u/2}/sinh u = 2 e^{-u/2}/(1 − e^{-2u}),
A(S) = −γ − log π − log(1 − e^{-2S}) − J(S),  J(S) = ∫_0^S (e^{u/2} − e^{-u})/sinh u du.
```

## Scripts

* `constrained_multiplier.py` — first (double precision) exploration: `A(S)`, `Λ_S`, the negative band,
  Legendre Gram of the multiplier, constrained ground energy, prolate concentration.
* `certificate_staircase.py` — first staircase certificate (double precision, width 0.5 bands).
* `certificate_rigorous.py` — the certificate with explicit error control (mpmath, 25 digits):
  * `J(S)`: series `2 Σ_m [(1−e^{−α_m S})/α_m − (1−e^{−β_m S})/β_m]`, `α_m = 2m+½`, `β_m = 2m+2`, head
    of 300 terms, exact tail `(ψ(M+1) − ψ(M+¼))/2` and an `e^{−α_M S}` remainder bound;
  * `Λ_S(ξ) ≥ 2 Σ_{m<M} T_m(ξ)` (every `T_m ≥ 0`; loss `≤ ξ²/(2(2M−3/2)²)`, `M = 400`);
  * Lipschitz constant `sup|m'| ≤ ∫_0^S u K₊ + Σ (2Λ(n)/√n) log n`;
  * band minima on width-`w` bands by a grid of spacing `w/10` minus `L·w/20`;
  * last band `[Ξ, ∞)`, `Ξ = 24`: grid on `[Ξ, 80]` and, for `ξ ≥ 80`, the elementary monotone bound
    `m_S(ξ) ≥ A + γ + log(Sξ) − 2/(Sξ) + S/2 − 1/(2ξ) − S²/4 − S/(2ξ) − 1/ξ² − Σ 2Λ(n)/√n`
    (from `1/(1−e^{−2u}) ≥ 1/(2u) + ½`, `e^{−u/2} ≥ 1 − u/2`, `|Ci(x)| ≤ 2/x`);
  * band Grams of the normalised Legendre basis by 48-node Gauss–Legendre rules per band
    (cross-checked against 96 nodes: agreement to `10⁻²⁷`);
  * finite block: penalised eigenvalue `λ_min(M_stair + t CᵀC)`, a rigorous lower bound of the
    constrained minimum for every `t ≥ 0`;
  * assembly `Q(f) ≥ [x y] Ω [x y]ᵀ` (see the docstring) with the Taylor localisation
    `M_low = 2a^{2N+1}Ξ^{2N+1}/(π (N!)² (2N+1)²)` (the Lean constant carries an extra factor 4,
    irrelevant at `10⁻¹²`), `N = ⌈3.3 a Ξ⌉ + 1`, and the `ε_N`-closeness of the Legendre projection to
    `V₀`.

Environment variable `WIDTH` sets the band width (grid spacing is `WIDTH/10`).

## Results (`certified_ground_energy` = rigorous lower bound of the constrained ground energy)

| S | λ = e^{S/2} | primes | N | width | certified | finite block, exact multiplier |
|---|---|---|---|---|---|---|
| log 2 | 1.4142 | — | 29 | 0.05 | 0.5177 | 0.5223 |
| 0.72 | 1.4333 | 2 | 30 | 0.05 | 0.2505 | 0.2606 |
| 0.80 | 1.4918 | 2 | 33 | 0.05 | 0.1100 | 0.1244 |
| 0.90 | 1.5683 | 2 | 37 | 0.05 | 0.0173 | 0.0341 |
| 0.95 | 1.6080 | 2 | 39 | 0.02 | 0.0059 | 0.0127 |
| 0.98 | 1.6323 | 2 | 40 | 0.01 | 0.0024 | 0.0059 |
| 1.00 | 1.6487 | 2 | 41 | 0.005 | **0.0014** | 0.0031 |
| 1.02 | 1.6701 | 2 | 42 | 0.005 | −0.0003 | 0.0014 |
| 1.05 | 1.6905 | 2 | 43 | 0.05 | −0.0166 | 0.00007 |

Certified positivity: `S ≤ 1`, i.e. `λ ≤ √e = 1.6487`, against the Connes–Consani aperture
`√2 = 1.414`.  **The last column is not an upper bound of the ground energy**: it replaces the
multiplier beyond `Ξ = 24` by the constant `c_last ≤ m`, so it is a lower bound of the Rayleigh
quotient of one test function; an earlier version of this README wrongly read a "threshold
`S* ≈ 1.05`" off it.  Rigorous upper bounds come from `certificate_upper.py` (test function in `V₀`
vanishing at both endpoints, `|f̂| ≤ W/ξ²`, exact multiplier to `Ξ₂ = 200` with the upper series
tail, analytic tail beyond); its log is `certificate_upper.log`.

Logs: `certificate_rigorous.log` (width 0.25, first far-tail bound — superseded),
`certificate_rigorous_w005.log` (width 0.05; the `S ≥ log 3` rows there omit the prime terms and are
superseded), `certificate_rigorous_w002.log` (width 0.02), `certificate_rigorous_w001.log` (width 0.01),
`certificate_rigorous_primes.log` (all visible prime powers, width 0.05, `S ≥ 0.95`).
