# Half-polar twisted-arc null family (PTMP_half)

- **ID:** ptmp-half
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** rh-goal-loop-opus-2026-09-29.md rows 1280–1281; even-window-pole-weight-uniqueness.md
- **Statement:** There is a probability measure ν on the closed bottom arc such that the `Ξ`-divisible
  positive-definite density `D(τ) = Ξ(τ)² q(τ) R_ν(τ)`, `q(τ) = τ²(τ² + ¼)`, is prime-blind:
  `∫ D(τ) cos(τ log n) dτ = 0` for every `n ≥ 2`. Here `R_ν(s) = 4√2 ∫ ρ(u) P_{s−1}(u)/P_{s−1}(0) dν(u)`
  is the arc multiplier of the twisted-arc family.

## Goal
One family closes three sector uniqueness problems at once:
- C892 (even positivity at a pole weight β > 1);
- even pole-free uniqueness;
- DPHP (polar uniqueness).

In the sector representation `K_lam = μ̂_R + ∫cosh(ax) dσ(a) + 2a₀ cosh(x/2) + 2b x sinh(x/2)`,
residues plus blindness give the null identity
`∫ D dμ_R + ∫ D(ia) dσ(a) + 2a₀ E_a + 2b E_b = 0`, with `E_a = D(i/2)` and `E_b = i D'(i/2)`.
- `q(i/2) = 0`, so `E_a = 0`.
- `q(iy)` changes sign from − to + at `y = ½`, so `E_b = R_ν(1)/256 > 0`.
- `q(ia) = a²(a² − ¼) > 0` for `a > ½`, and `R_ν(ia) > 0` for `a ≤ 3/2`, so super-pole mass on
  `(½, 3/2]` is seen positively.

Every sector fake has `b ≥ 0`, `σ ≥ 0` on `(½, 1]` and `μ_R ≥ 0`. All terms are then
nonnegative and sum to zero, so `σ = 0`, `b = 0` and `μ_R` sits on the critical zeros. The exposed
point / Hamburger step then gives `lam = Λ`.

Odd sector (Q*): the `r = 0` atom has `q(0) = 0`, so it stays invisible. Q* is not closed by this family.

## Known obstructions [P]
- A nonnegative arc measure gives `R_ν(1) = 4√2 ∫ρ dν > 0`. So the unmodified twisted-arc family
  sees `(a₀, b)` with fixed signs and cannot separate fakes (row 1280).
- In frequency/stream language, `q` is the dilation polynomial `P(E) = E(E+1)(E + ½)²` with
  `E = k∂_k = r∂_r` (`𝒟 = −∂_x x²∂_x` has Mellin multiplier `s(1−s)` and commutes with Fourier).
  - `P(r∂_r)` preserves the Stokes equation `ψ_xx + ψ_yy − ψ_y/y = 0`, which is homogeneous of
    degree −2.
  - It does not preserve the wall condition at `x = ½`. The wall data are `Q(y∂_y)Ψ₁(y)` with
    `Ψ₁(y) = Σ a_i (−1)^{n_i} k_i y K₁(k_i y)`.
  - So the stream-function minimum principle of the TMP proof does not transfer verbatim.
- Integer dilations `h ↦ h(·/N)` preserve witness blindness but are one-sided in `s`. Any
  `s ↔ 1−s` symmetric multiplier built from them needs dilations by `1/N`, which break blindness.

## Approach
- Legendre transfer. On the arc, `𝓛 = ∂_u(1 − u²)∂_u` has eigenvalue `s(1 − s)` on
  `P_{s−1}(u)`, so `N_n = ρ (𝓛 − ¼)𝓛 (B_n/ρ)`.
- With `ρν = (−𝓛)^{−1}(¼ − 𝓛)^{−1}(ρμ)` (Dirichlet conditions at `u = ±½`, positivity
  preserving) and `μ` a TMP annihilator, Green's identity gives
  `∫ N_n dν = −(3/2)[f_n (g₂' + g'/4) − (𝓛 f_n) g'](½)` with `f_n = B_n/ρ`.
- So PTMP_half reduces to a corner condition at the elliptic point `ρ = e^{iπ/3}`. One needs a
  universal relation between the corner values `f_n(½)`, `𝓛f_n(½)`, `𝓛²f_n(½)`, possibly
  absorbed by corner atoms of ν.
- Next: extract the corner behaviour of the moment functions from the TMP proof (the corner
  step `∂_y∂_x ψ(ρ) = √3(G'(½) − 2G(½))`, the arc flux `G`, the Legendre identity of
  `TwistedArcStreamMoment`).

## Log
- 2026-10-15 — created (row 1281).
- 2026-10-15 (row 1282) — Dirichlet–Green transfer plus corner atoms ruled out (Carlson's theorem on corner values `K₀, K₁(πm√3)`). The semicircle version needs `∫ρμ = 0`. The remaining route is a signed Mehler–Fock-positive annihilator; by Farkas this is dual to DPHP.
