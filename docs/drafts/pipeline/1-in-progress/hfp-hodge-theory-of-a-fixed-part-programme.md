# Hodge theory of a fixed part (HFP)

- **ID:** hfp-programme
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), programme card
- **Source:** `docs/reports/review-1011/obstacles-summary.md` §2.9
- **Statement:** Positivity and index theorems for the pairing of the degree points of the
  arithmetic square: contacts, jets, comb counterterm; effective classes; defects.

## Goal

Develop the field of §2.9: answer Q1–Q5, build tools T1–T6, decide criteria K1–K7, prove
milestones M2–M4. Folder `formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/`, umbrella
`HodgeTheoryOfAFixedPart.lean`, README in the folder.

## Normal form

Coordinates `c_n = f_n/√n` (packet `f` sampled at scale `N`, `f_n = f(log(n/N))`).

- `jet m n = ½(1/|m−n| + 1/(m+n))` (= AGZ `jetKernel`).
- contact `Λ(n/m)` for `m ∣ n`, `m < n`.
- counterterm `log(n/2π)`.
- `D·D = Σ_{m≠n} c_m c_n jet + 2 Σ_{m∣n,m<n} Λ(n/m) c_m c_n − Σ c_n² log(n/2π)`.
- degrees `d₁ = Σ c_n/n`, `d₂ = Σ c_n`; pole `2 d₁ d₂ = Σ c_m c_n (1/m + 1/n)`.
- AGZ: `degreeForm f L N + 2·degreeContact f L N` is `D·D` of the sampled packet on the window
  `Ioc N (N + L·N)`.

## Theorems (paper proofs)

**H1 (Lévy–Khintchine / Zariski on a comb).** For a symmetric kernel `k ≥ 0` off the diagonal on
a finite set `S`: `Σ_{m≠n} c_m c_n k = Σ_n c_n² row(n) − ½ Σ_{m≠n} k (c_m − c_n)²`. Hence
`D·D ≤ Σ c_n² (row_jets(n) + row_contacts(n) − log(n/2π))`.

**H2 (finite-scale Hodge index on short windows).** For `S ⊂ Ioc N (N+M)` with `M ≤ N/6`,
`N ≥ ...`, every real `c`: `D·D ≤ 2 d₁ d₂`. Proof: no contacts in a window of ratio `< 2`.
Row of the jets at `n`: `Σ_{m∈S, m≠n} ½/|m−n| ≤ H_{⌈(M−1)/2⌉}`-type bound `≤ 1 + log(M/2)`...,
`Σ ½/(m+n) ≤ M/(4N)`. Pole: `2 d₁ d₂ ≥ −(L³/2) Σ c_n²` on a window of ratio `1 + L`
(`d₁ = d₂/N − Σ c_n (n−N)/(nN)`). Counterterm `≥ log(N/2π)`.

**H3 (flat tail).** `Σ_{m ≤ A} ψ(B/m) = log ⌊B⌋!` for `A ≤ B < 2(A+1)`; contact energy of the
first `N` degree points is `log N!` (gluing index). Comb form of the flat tail `[1, N]`:
`2N·H_N − (N+½)H_{2N} + (5/4)H_N + N − log N! − N log 2π`, positive for every `N`, `/N → 2λ₁ =
2 + γ − log 4π`. In the limit the flat tail is `e^{u/2}` on `u ≤ 0`, `f̂(γ) = 1/ρ`,
`Z = Σ 1/(ρ(1−ρ)) = 2λ₁`.

**H4 (carry cocycle).** `E(N) = log N!` contact energy; `E(M+N) − E(M) − E(N) = log C(M+N, M)`
`= Σ_k Λ(k)·[carry]` (AGZ `log_choose_eq_sum_carry`). Counterterm of the block `(M, M+N]` =
counterterm of `[1, N]` + carry cocycle. Cross contacts of tail `[1,N]` with octave `(N, 2N]`:
`log((2N)!/N!)`; the single graph `Γ_1` contributes the window count, the others the carries.

**H5 (Riemann–Roch on the tower).** Sections of level `M`, `b` digits in `[0, A]`: count
`(A+1)^{bτ(M)}` (AGZ `card_image_orbitLatticeMap` for `[−A, A]`). Values on `Γ_1..Γ_K` lie in
the gluing lattice; with `|x_n| ≤ B_n` at most `Π_{n≤K}(2B_n/n + 1)` value vectors (necklace
coordinates are triangular with diagonal `n`). Pigeonhole: a nonzero section with digits in
`[−A, A]` vanishing on `Γ_1..Γ_K` exists once `(A+1)^{bτ} > Π (2B_n/n+1)`. The gluing index
`K!` is the quadratic term. Bézout: a section vanishing on all `Γ_d`, `d ∣ m`, `d < m`, has
`m ∣ x_m`.

**H6 (second axiom).** Reverse Cauchy–Schwarz on an open cone ⇔ index ≤ 1; Brunn–Minkowski for
`√vol` ⇒ reverse Cauchy–Schwarz. The count form of the tower at level `M` is a sum of `τ(M)`
hyperbolic planes: index `τ(M)`. Zero divisors `e_p(e_p − p) = 0`.

## Lean status

| Module | Content | Status |
|---|---|---|

## Open

Q1 (canonical comb), Q3 at finite scale beyond short windows, K1–K7 readings, M2–M4.

## Log
- 2026-11-10 — created; README first draft.
