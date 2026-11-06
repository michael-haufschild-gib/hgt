# Arithmetic Auxiliary Dynamics programme

- **ID:** AAD
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.8
- **Statement:** how the rational integers force zeros of ζ by construction and transport, with no sign.

## Goal
Develop the field: objects, tools, answers to the five questions of §2.8.
Lean folder: `formal/GaloisForLFunctions/ArithmeticAuxiliaryDynamics/`, umbrella `ArithmeticAuxiliaryDynamics.lean`.

## Working mathematics (paper targets; each is formalized before it counts)

For a balanced stencil `c` with `g = stepWeight c ≥ 0`, `g ≥ m` on `[1,B)`:

- W1 Increment and Möbius rigidity: `h = c*1`, `c = μ*h`; constant windows force `c = mμ`.
- W2 Reflection: on a common period `L`, `g(L−1−j) + g(j) = w`, `w = −Σc(k) = sup g`, mean `w/2`.
- W3 Forced jumps: `h(r) = c(1)` when `gcd(r,L) = 1`, so `g(r) ≥ m` at rough `r`.
- W4 Floor: `T := slope − m(1−1/B) ≥ m Σ_{r>1 rough} 1/(r(r+1))`, hence `A(K)−1 ≥ c/(K log K)`.
- W5 Coefficient bound: `|h(d)| ≤ slope·d(d+1)`, `|c(k)| ≲ slope·k²`, so `C_ε` of the producer is polynomial in `K`.
- W6 Mellin: `D_c(s)ζ(s) = Σ g(r)(r^{−s} − (r+1)^{−s})`, `Re s > 0`.
- W7 Mollifier on `Re s = 1`: `|D_cζ(1+iτ)/m − (1−B^{−1−iτ})| ≤ |1+iτ| T/m`.
- W8 Uncertainty: at a zero `ρ`, `m|1−B^{−ρ}|/|ρ| ≤ (1+1/β) w^{1−β} T^{β}`.
- W9 Reading: `ε(K) ≤ K^{−a}` gives `Θ < 1`; `ε(K) ≤ exp(−(log K)^α)` gives a zero-free region of exponent `(1−α)/α`.
- W10 Parity: `1_{λ=−1} = (1−λ)/2` moves the factor 2 of a nonnegative `h` to `Σ c(k)λ(k)L(x/k)`.
- W11 `h ≥ 0` is never balanced: the sieve cone and the producer cone meet trivially.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Log
- 2026-11-06 — created; first README draft written.
