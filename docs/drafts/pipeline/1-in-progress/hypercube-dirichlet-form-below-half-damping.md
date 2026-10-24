# The hypercube Dirichlet form below half damping (Fable 2410, opening B)

- **ID:** hdf-below-half
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** docs/reports/review-2410/fable.md §2.3 B · BVI README §7.2, §7.5 · THIM §7.8.4
- **Statement:** For every modulus `r > 1` and every damping `0 ≤ ε < 1/2` the hypercube dilation
  Dirichlet form `D_{r,ε}(P) = Σ_{d₁,d₂ | P} μ(d₁)μ(d₂)(d₁d₂)^{-1/2-ε} Φ_r(d₁/d₂)` is unbounded over
  squarefree `P` coprime to `r`; along prime blocks `P_y = ∏_{y < p ≤ y + ⌊y/2r⌋} p` it grows at
  least like `c_r y^{1-2ε}/log² y`. The same holds for the parity twin (`|μ|` weights).

## Goal
Opening B names, as its concrete finite problem and first rung, a uniform-in-`P` bound for
`D_{r,ε}(P)` at one fixed `ε < 1/2` ("quasi-RH strength"). Decide it.

## Paper proof
1. *Physical form.* With `F_r(x) = C_r(⌊x⌋)/x` (`C_r` the Ramanujan primitive) and unitary
   dilations, `D_{r,ε}(P) = ‖Σ_{d|P} μ(d)d^{-1/2-ε} D_{1/d}F_r‖²`, and
   `Σ_{d|P} μ(d)d^{-1/2-ε}(D_{1/d}F_r)(x) = Ψ_P(⌊x⌋)/x` with
   `Ψ_P(n) = Σ_{d|P} μ(d)d^{-ε} C_r(⌊n/d⌋)`. Hence `D_{r,ε}(P) = Σ_{n≥1} Ψ_P(n)²/(n(n+1))`.
2. *Depth-one plateau.* Let `y ≥ r`, `h = ⌊y/2r⌋`, `S` the primes in `(y, y+h]`, `P = ∏_S p`. For
   `(r-1)(y+h) ≤ n < ry`: `⌊n/p⌋ = r-1` for every `p ∈ S`, and every divisor of `P` with two
   prime factors exceeds `y² ≥ ry > n`. Since `C_r(r-1) = C_r(r) - c_r(r) = -φ(r)`,
   `Ψ_P(n) = C_r(n) + φ(r)·M`, `M = Σ_{p∈S} p^{-ε}`.
3. *Count.* The plateau has length `≥ y/2`, so its pronic mass is `≥ 1/(2r²y)`, and
   `D ≥ (φ(r)M - B_r)²/(2r²y)`. The PNT gives `|S| ≥ y/(16 r log 2y)` for large `y`, so
   `M ≥ c y^{1-ε}/log y` and `D ≥ c' y^{1-2ε}/log² y → ∞` for `ε < 1/2`.
4. *Twin.* Replacing `μ(d)` by `1` changes `+φ(r)M` to `-φ(r)M`; the bound is identical.

`[PROVED HERE]` — elementary given the corpus PNT.

## Consequences for opening B
- The first rung as stated is false: no bound at any fixed `ε < 1/2` exists for this form,
  unconditionally. The form is not "the finite form of `ζ(1+ε)ζ(1+ε)^{-1} = 1` the receiver needs".
- Threshold: bounded for `ε > 1/2` (`hypercubeDilationDirichletForm_le_tsum_sq_of_half_lt`),
  unbounded for `0 ≤ ε < 1/2`, for `μ` and for `|μ|` alike: the threshold is sign-blind (Class II).
- Mechanism: divisor (Euler-product) truncation keeps a whole block of equal-sign primes on one
  floor plateau; in Mellin terms partial Euler products of `1/ζ` diverge left of `Re s = 1`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: complete paper proof above
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** depth-one plateau of a prime block (step 2).
- **Strongest positive survivor:** sharp sign-blind threshold law (bounded iff `ε > 1/2` on
  `[0,∞) \ {1/2}`, identical for `μ` and `|μ|`); exact physical form of the hypercube form.
- **New insight:** cross-depth cancellation of the receiver cannot be organised by prime support;
  it must be organised by size.
- **Status:** paper proof complete; Lean pending.

## Log
- 2026-10-24 — created in 1-in-progress
