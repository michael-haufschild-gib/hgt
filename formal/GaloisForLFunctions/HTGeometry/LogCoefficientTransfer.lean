import Mathlib

/-!
# Exponential-formula transfer of coefficient bounds

If a formal power series `A` with `A 0 = 1` is the exponential of a series whose coefficients are
recorded by `B` — equivalently, if `A` and `B` satisfy the Newton recursion coming from
`A' = (log A)' · A`, in the reindexed form

`n · A n = ∑_{j < n} (n − j) · B (n − j) · A j`,

then geometric bounds transfer from `A` to `B`: `‖A n‖ ≤ C R^n` forces `‖B n‖ ≤ (4CR)^n`.

For a Dirichlet series with an Euler product, `A k` is the local coefficient at `p^k` and `B k` is
`k` times the coefficient of `p^{-ks}` in the logarithm.  The Ramanujan bound `‖A k‖ ≤ C_ε p^{kε}`
(so `R = p^ε`) then yields `|b(p^k)| ≪ (4C_ε)^k p^{kε}`, which is what makes the `k ≥ 2` part of a
quadratic prime sum converge to the right of `1/2` rather than only to the right of `2θ + 1/2`.

The proof is a strong induction: isolate the `j = 0` term, bound the rest by `M^{n-j}R^j =
M^{n-1}R(R/M)^{j-1}` with `M = 4CR`, and sum the geometric series `R/M = 1/(4C) ≤ 1/2`.
-/

open Finset

namespace HTGeometry

open Finset

private lemma geom_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1/2) :
    ∀ m : ℕ, ∑ j ∈ Finset.range m, r ^ j ≤ 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [geom_sum_succ]
      nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range m) => pow_nonneg hr0 j)]

theorem log_coeff_bound {A B : ℕ → ℂ} {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R)
    (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n : ℂ) * A n = ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j)
    (hAb : ∀ n : ℕ, ‖A n‖ ≤ C * R ^ n) :
    ∀ n : ℕ, 1 ≤ n → ‖B n‖ ≤ (4 * C * R) ^ n := by
  set M : ℝ := 4 * C * R with hM
  have hM4 : (4:ℝ) ≤ M := by rw [hM]; nlinarith
  have hMpos : (0:ℝ) < M := by linarith
  have hRM : R / M ≤ 1/2 := by
    rw [div_le_iff₀ hMpos]; rw [hM]; nlinarith
  have hRM0 : (0:ℝ) ≤ R / M := by positivity
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h0 : (0:ℕ) ∈ Finset.range n := by simp; omega
    have hsplit : ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j
        = (n : ℂ) * B n * A 0 + ∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j := by
      rw [← Finset.add_sum_erase _ _ h0]
      have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
        ext j
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [herase]
      simp
    have hkey : (n : ℂ) * B n
        = (n : ℂ) * A n - ∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j := by
      have := hrec n hn
      rw [hsplit, hA0, mul_one] at this
      linear_combination -this
    have hterm : ∀ j ∈ Finset.Ico 1 n,
        ‖((n - j : ℕ) : ℂ) * B (n - j) * A j‖ ≤ (n : ℝ) * C * (M ^ (n-1) * R) * (R / M) ^ (j - 1) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      obtain ⟨hj1, hj2⟩ := hj
      have hnj : 1 ≤ n - j := by omega
      have hnjn : n - j < n := by omega
      have hB : ‖B (n - j)‖ ≤ M ^ (n - j) := ih _ hnjn hnj
      have hA : ‖A j‖ ≤ C * R ^ j := hAb j
      have e1 : (n - j) + (j - 1) = n - 1 := by omega
      have e2 : (j - 1) + 1 = j := by omega
      have hmul : M ^ (n - j) * R ^ j * M ^ (j - 1) = M ^ (n - 1) * R * R ^ (j - 1) := by
        calc M ^ (n - j) * R ^ j * M ^ (j - 1)
            = (M ^ (n - j) * M ^ (j - 1)) * R ^ j := by ring
          _ = M ^ (n - 1) * R ^ j := by rw [← pow_add, e1]
          _ = M ^ (n - 1) * (R ^ (j - 1) * R) := by rw [← pow_succ, e2]
          _ = M ^ (n - 1) * R * R ^ (j - 1) := by ring
      have hpow : M ^ (n - j) * R ^ j = M ^ (n-1) * R * (R / M) ^ (j - 1) := by
        rw [div_pow, ← mul_div_assoc, eq_div_iff (ne_of_gt (pow_pos hMpos _))]
        exact hmul
      calc ‖((n - j : ℕ) : ℂ) * B (n - j) * A j‖
          = ((n - j : ℕ) : ℝ) * ‖B (n - j)‖ * ‖A j‖ := by simp
        _ ≤ (n : ℝ) * M ^ (n - j) * (C * R ^ j) := by
            have h1 : ((n - j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n j
            gcongr
        _ = (n : ℝ) * C * (M ^ (n - j) * R ^ j) := by ring
        _ = (n : ℝ) * C * (M ^ (n-1) * R * (R / M) ^ (j - 1)) := by rw [hpow]
        _ = (n : ℝ) * C * (M ^ (n-1) * R) * (R / M) ^ (j - 1) := by ring
    have hgeo : ∑ j ∈ Finset.Ico 1 n, (R / M) ^ (j - 1) ≤ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simpa using geom_le_two hRM0 hRM (n - 1)
    have hnR : (0:ℝ) ≤ (n:ℝ) := by positivity
    have hsum : ‖∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j‖
        ≤ (n : ℝ) * C * (M ^ (n-1) * R) * 2 := by
      calc ‖∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j‖
          ≤ ∑ j ∈ Finset.Ico 1 n, ‖((n - j : ℕ) : ℂ) * B (n - j) * A j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Ico 1 n, (n : ℝ) * C * (M ^ (n-1) * R) * (R / M) ^ (j - 1) :=
            Finset.sum_le_sum hterm
        _ = (n : ℝ) * C * (M ^ (n-1) * R) * ∑ j ∈ Finset.Ico 1 n, (R / M) ^ (j - 1) := by
            rw [Finset.mul_sum]
        _ ≤ (n : ℝ) * C * (M ^ (n-1) * R) * 2 := by
            have : (0:ℝ) ≤ (n : ℝ) * C * (M ^ (n-1) * R) := by positivity
            nlinarith
    have hnB : (n : ℝ) * ‖B n‖ ≤ (n : ℝ) * (C * R ^ n) + (n : ℝ) * C * (M ^ (n-1) * R) * 2 := by
      have h1 : ‖(n:ℂ) * B n‖ = (n : ℝ) * ‖B n‖ := by simp
      have h2 : ‖(n:ℂ) * A n‖ = (n : ℝ) * ‖A n‖ := by simp
      rw [← h1, hkey]
      refine (norm_sub_le _ _).trans ?_
      rw [h2]
      have h3 : (n : ℝ) * ‖A n‖ ≤ (n : ℝ) * (C * R ^ n) := by
        have := hAb n; nlinarith
      linarith [hsum]
    have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hfin : ‖B n‖ ≤ C * R ^ n + 2 * (C * (M ^ (n-1) * R)) := by
      have : (n:ℝ) * ‖B n‖ ≤ (n:ℝ) * (C * R ^ n + 2 * (C * (M ^ (n-1) * R))) := by nlinarith
      exact le_of_mul_le_mul_left this hnpos
    have hRMpow : R ^ (n-1) ≤ M ^ (n-1) := by
      apply pow_le_pow_left₀ (by linarith) (by rw [hM]; nlinarith)
    have hRn : C * R ^ n = C * R * R ^ (n-1) := by
      have h : R ^ n = R ^ (n - 1) * R := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]
      rw [h]; ring
    have hMn : M ^ n = M * M ^ (n-1) := by
      have h : M ^ n = M ^ (n - 1) * M := by
        conv_lhs => rw [show n = (n - 1) + 1 from by omega]
        rw [pow_succ]
      rw [h]; ring
    have hCR0 : (0:ℝ) < C * R := by nlinarith
    calc ‖B n‖ ≤ C * R ^ n + 2 * (C * (M ^ (n-1) * R)) := hfin
      _ = C * R * R ^ (n-1) + 2 * (C * R * M ^ (n-1)) := by rw [hRn]; ring
      _ ≤ C * R * M ^ (n-1) + 2 * (C * R * M ^ (n-1)) := by nlinarith
      _ = 3 * (C * R) * M ^ (n-1) := by ring
      _ ≤ 4 * (C * R) * M ^ (n-1) := by nlinarith [pow_nonneg (le_of_lt hMpos) (n-1)]
      _ = M ^ n := by rw [hMn, hM]; ring

/-- **Summability of the higher log-coefficients.**  If `‖B n‖ ≤ M ^ n` for `n ≥ 1` and `M x < 1`,
then the tail from index `2` onwards is bounded by `(M x)² / (1 - M x)`, uniformly in the number of
terms.

Applied to the local factor of a Dirichlet series at a prime `p`, with `x = p^{-σ}` and `M` the
geometric constant supplied by the transfer bound, this is what makes the prime-power part of an
Euler product converge: the tail at each prime is `O(p^{-2σ+})`, and `∑_p p^{-2σ}` converges for
`σ > 1/2`. -/
theorem tail_geometric_bound {B : ℕ → ℂ} {M x : ℝ} (hM : 0 ≤ M) (hx : 0 ≤ x)
    (hMx : M * x < 1) (hB : ∀ n, 1 ≤ n → ‖B n‖ ≤ M ^ n) (N : ℕ) :
    ∑ k ∈ Finset.Ico 2 N, ‖B k‖ * x ^ k ≤ (M * x) ^ (2 : ℕ) / (1 - M * x) := by
  have hMx0 : 0 ≤ M * x := mul_nonneg hM hx
  have hden : 0 < 1 - M * x := by linarith
  have hne : M * x - 1 ≠ 0 := by intro h; linarith
  have hterm : ∀ k ∈ Finset.Ico 2 N, ‖B k‖ * x ^ k ≤ (M * x) ^ k := by
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Ico.1 hk).1
    have h1 : ‖B k‖ ≤ M ^ k := hB k (by omega)
    calc ‖B k‖ * x ^ k ≤ M ^ k * x ^ k := mul_le_mul_of_nonneg_right h1 (pow_nonneg hx k)
      _ = (M * x) ^ k := by rw [mul_pow]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_Ico_eq_sum_range]
  have hexp : ∀ i ∈ Finset.range (N - 2), (M * x) ^ (2 + i) = (M * x) ^ (2 : ℕ) * (M * x) ^ i :=
    fun i _ => by rw [pow_add]
  rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum]
  have hgeom : ∑ i ∈ Finset.range (N - 2), (M * x) ^ i ≤ 1 / (1 - M * x) := by
    rw [geom_sum_eq (by intro h; rw [h] at hMx; linarith)]
    have he : ((M * x) ^ (N - 2) - 1) / (M * x - 1)
        = (1 - (M * x) ^ (N - 2)) / (1 - M * x) := by
      rw [div_eq_div_iff hne (by linarith)]
      ring
    rw [he]
    have hnum : 1 - (M * x) ^ (N - 2) ≤ 1 := by
      nlinarith [pow_nonneg hMx0 (N - 2)]
    gcongr
  calc (M * x) ^ (2 : ℕ) * ∑ i ∈ Finset.range (N - 2), (M * x) ^ i
      ≤ (M * x) ^ (2 : ℕ) * (1 / (1 - M * x)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (M * x) ^ (2 : ℕ) / (1 - M * x) := by ring

/-- **Newton's second identity in exponential form.**  If `A 0 = 1` and the coefficients satisfy the
logarithmic-derivative recursion `n·Aₙ = ∑_{j<n}(n−j)·B_{n−j}·A_j`, then

```text
A 1 ^ (2 : ℕ) = 2 * A 2 - 2 * B 2 .
```

For an Euler factor `F_p(X) = ∑ₖ a_F(p^k) X^k` with `log F_p(X) = ∑ₖ b_F(p^k) X^k` this reads
`a_F(p)² = 2 a_F(p²) − 2 b_F(p²)`: the **square** of the prime coefficient is a `ℤ`-linear
combination of coefficients at the prime **square**, one of each kind.  Both are supplied directly by
the Dirichlet series and its logarithm, so a quadratic expression in the prime coefficients is
converted into a linear expression in prime-square data.

Checked against `ζ` (`a = 1`, `a(p²) = 1`, `b(p²) = 1/2`: `2 − 1 = 1`) and against a `GL₂` newform of
trivial nebentypus (`a(p²) = a² − 1`, `b(p²) = (a² − 2)/2`: `2(a²−1) − (a²−2) = a²`). -/
theorem newton_sq_identity {A B : ℕ → ℂ} (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n : ℂ) * A n = ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j) :
    A 1 ^ (2 : ℕ) = 2 * A 2 - 2 * B 2 := by
  have h1 := hrec 1 (le_refl 1)
  simp [hA0] at h1
  have h2 := hrec 2 (by norm_num)
  rw [show Finset.range 2 = {0, 1} from rfl] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  norm_num [hA0] at h2
  rw [h1] at h2 ⊢
  linear_combination -h2

end HTGeometry
