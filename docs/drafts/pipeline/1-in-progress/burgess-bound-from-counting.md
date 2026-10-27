# Burgess's bound for quadratic character sums, from counting on curves

- **ID:** aet-burgess
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** AET README §6 Q3, §9 topic 5 (uniform square-root cancellation from counting),
  `TheCompletionLaw` (Pólya–Vinogradov); Weil bound `RHTower.Hyperelliptic.abs_sum_quadraticChar_multiset_le`
- **Statement:** `p` odd prime, `χ` the quadratic character, `r ≥ 2`. There is `K_r` with
  `|Σ_{k<N} χ(M + k)| ≤ K_r N^{1−1/r} p^{(r+1)/(4r²)} (1 + log p)` for all `M ∈ ℤ`, `N ∈ ℕ`.

## Paper proof
Notation `S(M, N) = Σ_{k<N} χ(M + k)`, `T(x) = Σ_{b<B} χ(x + b)`, `L = 1 + log p`.

1. *Moment (counting on curves of genus `< r`).* For `B ≤ p`:
   `Σ_x T(x)^{2r} ≤ r^{2r} B^r p + 6r B^{2r} √p`. Expand: `Σ_{f : Fin 2r → [0,B)} Σ_x χ(Π_i (x + f_i))`.
   If some value of `f` has odd multiplicity, the Weil bound with multiplicities gives `≤ 6r√p`;
   otherwise `f` takes `≤ r` values, and there are `≤ C(B, r) r^{2r} ≤ r^{2r} B^r` such `f`.
2. *Energy.* For `1 ≤ A`, `2AN ≤ p`: `Q = #{a_i ≤ A, m_i < N : a₂(M + m₁) ≡ a₁(M + m₂)} ≤
   A² + 4AN(1 + log A)`. Fix `(a₁, a₂)`; the solutions form a lattice coset meeting a box of side
   `N`, so (difference trick) at most `#{|u|,|v| < N : a₂u ≡ a₁v}`; `|a₂u − a₁v| < 2AN ≤ p` forces
   `a₂u = a₁v`, so `u` is a multiple of `a₁/g` and `v` is determined: `≤ 1 + 2Ng/max(a₁, a₂)`.
   `Σ_{a₁,a₂ ≤ A} gcd/max ≤ 2Σ_{a≤A} τ(a) ≤ 2A(1 + log A)`.
3. *Hölder.* With `ν(x) = #{a ≤ A, m < N : ā(M + m) = x}`: `Σν = AN`, `Σν² = Q`, and
   `(Σ ν|T|)^{2r} ≤ (Σν)^{2r−2} (Σν²) (Σ T^{2r})`.
4. *Shift.* `χ(M + m + ab) = χ(a) χ(ā(M + m) + b)` (`a < p`), so
   `|Σ_{a≤A, b<B} S(M + ab, N)| ≤ Σ_x ν(x)|T(x)|`; and `S(M, N) − S(M + h, N) = S(M, h) − S(M + N, h)`.
5. *Induction on `N`.* `B = ⌊p^{1/(2r)}⌋` (`B^r ≤ √p`, moment `≤ (r^{2r} + 6r) B^r p`),
   `A = ⌊N/(κB)⌋`, `κ = 16`. Main term `≤ C κ^{1/(2r)} N^{1−1/r} p^{(r+1)/(4r²)} L`; error
   `≤ 2 max_{h ≤ AB} |S(·, h)| ≤ 2K (N/κ)^{1−1/r} p^{(r+1)/(4r²)} L ≤ (K/2) N^{1−1/r} …`. Ranges:
   `N < 2κB` trivial (`N ≤ (2κ)^{1/r} N^{1−1/r} p^{1/(2r²)}`); `2AN > p` forces
   `N ≥ p^{1/2+1/(4r)}`·const, where Pólya–Vinogradov `√p L ≤ N^{1−1/r} p^{(r+1)/(4r²)} L` suffices.

## Log
- 2026-10-27 — created; Weil input formalized (`RHTower/HyperellipticCharacterSums.lean`).
