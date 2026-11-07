# Prime torus theory

- **ID:** ptt
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-0611/obstacles-summary.md §2.8b
- **Statement:** The pair `(t, ω_t)` at finite time: alignment, near-diagonal energy, Bohr sets as approximate groups, kernel-valued certificates, the hull.

## Goal
Answer the six questions of §2.8b and build its five tools, in `formal/GaloisForLFunctions/PrimeTorusTheory/`. A macroscopic non-alignment theorem on the critical line is quasi-RH strength, so the honest targets are sharp brackets, exact identities, no-gos with their positive survivors, and small unconditional savings.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Paper proofs (status column is the only thing to update)

| # | Statement | Status |
|---|---|---|
| P1 | `√D_a` subadditive; `D_a(nt) ≤ n²D_a(t)`; `|P_a(t) − P_a(s)|² ≤ 2S_a D_a(t−s)`; `D₊(2t) ≤ 4D₋(t)` | paper |
| P2 | Halász–Montgomery: `P_a(t_i) ≥ θS` for `i<N` ⇒ `Σ_{i,j} P_a(t_i−t_j) ≥ θ²N²S` | paper |
| P3 | Finite-time Bohr: Fejér product on `P` = `|R|²/|A|`, `R` unimodular on divisors of `D=Πp^m`; window `L ≫ |A|²|P|·max p·D` ⇒ every direction entered at level `(m/(m+1))S` | paper |
| P4 | Pigeonhole non-alignment: `C(d+k,k) ≥ k t log y + 1` ⇒ `max_p ‖t log p‖ ≥ t/(2k y^k)`; half-space saving `S − sup P ≥ S·T^{−2/(2K−1)−o(1)}` | paper |
| P5 | Energy = Fejér moment; diagonal through `k₀`; Cauchy lower bound; start of orbit is the mixing term; returns add | paper |
| P6 | Rounded orbit: `ℓ̃_p ∈ (2π/T)ℤ`, `|ℓ̃_p−log p| ≤ π/T`: exact return at `T`, agrees to `cT`, diagonal through `k₀` preserved | paper |
| P7 | Agler wall, two-point inequality: `|S₁−S₂| ≤ |G₁|√((1−|S₁|²)/(1−|G₁|²)) + |G₂|/√(1−|G₂|²) + √(Σ|δ_k|²/(1−r_k²)²)`; along returns with `S,G→0`: `|S| ≤ |G|` | paper |
| P8 | Fejér positivity: `∫₀^T(1−t/T)P_a(t)dt = Σ a_i(1−cos Tℓ_i)/(Tℓ_i²) ≥ 0`, sign flips on the twin | paper |
| P9 | Hull table: finite modification, Liouville fibre `ζ(2s)/ζ(s)`, identity fibre pole, typical fibre zero-free | paper |
| P10 | Pole payment: `Σ_p p^{−σ}cos(u log p) ≤ log|ζ(σ+iu)| + c`, separated large values | paper |
| P11 | SOS: column outer factor `b−c_p = |(u−vω)/(1−rω)|²`; allocation ⇔ size; frozen coefficient ⇒ torus positive ⇒ size; graph lift tautological | paper |
| P12 | Critical coupling: both `½` are one pole | open |

## Approach
Module list follows the paper proofs; umbrella `PrimeTorusTheory.lean`, wired into `MainTheorems.lean`.

## Log
- 2026-11-07 — created
