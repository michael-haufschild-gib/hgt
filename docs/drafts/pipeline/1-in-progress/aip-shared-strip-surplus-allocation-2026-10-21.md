# AIP: shared strip surplus, allocated across nested prime strips without double counting

- **ID:** aip-shared-surplus-2026-10-21
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for the survivors; CONJECTURE/NO-GO for the global form
- **Source:** frontier map (AIP open/hard obstacle: "Allocate shared strip surplus without double
  counting"); review-2110 hard-obstacles AIP (b); AIP README mechanisms 28–35.
- **Statement:** For odd `F` on `[−r, r]` the strips `S_n = [log n − r, r]` of the entered prime powers are
  nested with common right end `r`. Allocate the one archimedean surplus
  `T(S) = ∫∫_{S×S} k(x, y)(F x − F y)²` among all of them so that every atom
  `2Λ(n)/√n ∫ F F(· + log n)` is paid and no pair is counted twice.

## Goal
Mechanisms 30/35 pay each atom from the surplus of its own strip `S_n × S_n`. The strips are nested, so
summing those inequalities counts the inner pairs once per strip. The task: a simultaneous allocation
(one copy of the surplus pays a family of atoms), its exact domain of validity, and the obstruction
outside it.

## Mathematics (paper)
1. **Union allocation.** `0 ≤ k` on same-side pairs and `S_{n'} ⊂ S_n` for `n < n'` give
   `T(S_{n'}) ≤ T(S_n)`; weights `θ_n ≥ 0`, `Σ θ_n ≤ 1`, `(1 + t_n) 2Λ_n ≤ θ_n λ_n` pay the family from
   `T(S_{n₀})`. For `ζ` this fails already for the thin pair `{23, 25}`: `(1.3076 + 0.6438)/1.86 > 1`.
2. **Shell micro-fold (corner-free).** Let `S = [p, r]`, `m = (p + r)/2`, `S' = [p', r]` with
   `c = p' − m > 0` (the inner strip lies right of the centre). A quadruple `x, L − x, y, L − y` of `S`
   has a pair in `S' × S'` only through its right–right pair, and only when `u, v > c`
   (`u = |x − m|`, `v = |y − m|`). Dropping exactly those quadruples (their three other pairs are
   `≥ 0`) leaves the sharp quadruple bound on the rest, and the folded weight is bounded on the
   corner by `W(u, v) ≤ (2 + η/2)/c + 1` (`k(u, v)(u − v) ≤ ½ + (u − v)/4`, `4ω(u + v) ≤ 1/c + 1`). So
   `T(S) − T(S') ≥ (λ₀ − (η − c)((2 + η/2)/c + 1)) ∫_S α²`, `η − c = r − p'`.
3. **Telescoping chain.** For `n₀ < n₁ < … < n_k`, strip `j` pays from the shell `T(S_j) − T(S_{j+1})`
   and the last from `T(S_k)`; the shells are disjoint and telescope to `T(S_{n₀})`: one copy, no pair
   counted twice. Hierarchically separated strips (`η_{j+1} ≪ η_j`) each keep almost the full
   constant `λ ≈ 1.9`.
4. **ζ instance.** `{23, 25}` for `½ log 25 < r ≤ ½ log 25 + 1/250`: union fails, shell works
   (`λ_sh ≥ 1.40 > 2Λ(23)/√23 = 1.3076`), and the atom of `25` is a net gain (`t = 1`).
5. **Capacity law (heuristic, to be audited).** The surplus is a logarithmic (`H^{1/2}`) energy: a
   bump of width `ε` at the common edge costs `≍ ε log(η/ε)` while every strip wider than `ε` charges
   `½ ∫ f²`. Capacity is logarithmic in strip width; atom mass in a width layer `[η, 2η]` is
   `≍ η e^r`. Hence simultaneous payment by the surplus is possible exactly in the light cone
   `η_n ≲ e^{−r}` (`n ≳ N − c√N`, `N = e^{2r}`), and impossible for the full thin band once `e^r` is
   large.

## Conjecture loop
- C1 shell micro-fold — attack (Lean).
- C2 telescoping chain allocation — attack (Lean).
- C3 union allocation for a finite family — attack (Lean).
- C4 `{23, 25}` shared strip — attack (Lean).
- C5 light cone at every scale: all atoms with `2r − 2δ(r) ≤ log n < 2r` paid jointly — attack.
- C6 sharing no-go: the odd-part charging cannot be global — paper audit, Lean if dependency-closed.

## Gates
- [x] 0 → 1 well-posed, corpus searched (`research "shared strip surplus allocation prime shifts"`:
  only per-strip theorems `two_mul_primePowerShift_le_stripSurplus*`; BiScale collar allocation is a
  different object).
- [ ] 1 → 2 paper proofs of C1–C5
- [ ] 2 → 3 Lean

## Log
- 2026-10-21 — created; mathematics 1–5 drafted.
