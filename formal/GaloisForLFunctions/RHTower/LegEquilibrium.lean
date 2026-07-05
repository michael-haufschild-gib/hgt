/-
# LegEquilibrium — the equilibrium constraint discharges the window hypothesis

Setting as in `LegWindow`: charges on two arithmetic progressions with step `h = δ/2` — ahead
points `a_k = (θ + k)h`, `k < M`, and behind points `b_k = (1 − θ + k)h`, `k < N ≥ M`, with
`θ ∈ (0, 1/2)`. An *equilibrium* is a root of the total field: writing
`g(ϑ) = Σ_{k<N} coth(b_k(ϑ)) − Σ_{k<M} coth(a_k(ϑ))`, the equilibrium condition is
`g(θ) = −(N + M)`.

Main point: the equilibrium condition itself forces the localization that the comparison
theorems need — no window hypothesis on `θ` survives as an assumption.

* `lattice_constraint_hasDerivAt` — `g'(ϑ) = (δ/2)·[Σ_{k<N} csch²(b_k) + Σ_{k<M} csch²(a_k)]`,
  positive: `g` is strictly increasing in `ϑ`.
* `equilibrium_theta_gap` — at an equilibrium with `θ ≥ 1/8`:  `Nδ/78 ≤ 1/2 − θ`.
  Proof: MVT for `g` on `[θ, 1/2]`. At `ϑ = 1/2` the two progressions coincide, so
  `g(1/2) = Σ_{k∈[M,N)} coth((1/2+k)h) ≥ N − M` (each `coth > 1`); hence
  `g(1/2) − g(θ) ≥ (N − M) + (N + M) = 2N`. On `(θ, 1/2)` the derivative is at most
  `156/δ`: termwise `csch²(s) ≤ 1/s²`, and the two inverse-square sums are at most
  `4 + 2 = 6` (behind, offset `1/2`) and `64 + 8 = 72` (ahead, offset `1/8`) by the
  telescoping bound `Σ_{k≥1} (a+k)⁻² ≤ 1/a`.
* `dW_dtheta_neg_at_equilibrium` — at every equilibrium with `δ ≤ 1` and `Nδ > 30`, the
  ahead sum wins: `Σ_{k<N} φ(b_k) < Σ_{k<M} φ(a_k)`. Indeed `θ ≥ 1/8` is impossible there
  (`equilibrium_theta_gap` would give `Nδ ≤ 78·(3/8) < 30`), and for `θ < 1/8` the
  small-step comparison `dW_dtheta_neg_small_delta` applies. The localization hypothesis is
  produced by the constraint, not assumed.
-/
import GaloisForLFunctions.RHTower.LegWindow

noncomputable section

namespace RHTower

open Finset

/-- Derivative of the lattice field in the offset variable:
`g'(ϑ) = (δ/2)·[Σ_{k<N} csch²((1−ϑ+k)δ/2) + Σ_{k<M} csch²((ϑ+k)δ/2)]` for `ϑ ∈ (0, 1)`.
Both trains contribute with the SAME sign: moving the equilibrium toward the behind train
increases every behind coth and increases every (negated) ahead coth. -/
theorem lattice_constraint_hasDerivAt {δ : ℝ} (hδ0 : 0 < δ) (M N : ℕ) {ϑ : ℝ}
    (hϑ0 : 0 < ϑ) (hϑ1 : ϑ < 1) :
    HasDerivAt (fun y => (∑ k ∈ range N, rcoth ((1 - y + k) * (δ / 2)))
        - ∑ k ∈ range M, rcoth ((y + k) * (δ / 2)))
      ((δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - ϑ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range M, (rcsch ((ϑ + k) * (δ / 2))) ^ 2)) ϑ := by
  have hb : ∀ k ∈ range N, HasDerivAt (fun y => rcoth ((1 - y + (k : ℝ)) * (δ / 2)))
      ((δ / 2) * (rcsch ((1 - ϑ + (k : ℝ)) * (δ / 2))) ^ 2) ϑ := by
    intro k _
    have harg : 0 < (1 - ϑ + (k : ℝ)) * (δ / 2) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith
    have hin : HasDerivAt (fun y : ℝ => (1 - y + (k : ℝ)) * (δ / 2)) ((0 - 1) * (δ / 2)) ϑ :=
      (((hasDerivAt_const ϑ (1 : ℝ)).sub (hasDerivAt_id ϑ)).add_const (k : ℝ)).mul_const (δ / 2)
    have hcomp := (rcoth_hasDerivAt harg.ne').comp ϑ hin
    convert hcomp using 1
    ring
  have ha : ∀ k ∈ range M, HasDerivAt (fun y => rcoth ((y + (k : ℝ)) * (δ / 2)))
      (-((δ / 2) * (rcsch ((ϑ + (k : ℝ)) * (δ / 2))) ^ 2)) ϑ := by
    intro k _
    have harg : 0 < (ϑ + (k : ℝ)) * (δ / 2) := by positivity
    have hin : HasDerivAt (fun y : ℝ => (y + (k : ℝ)) * (δ / 2)) (1 * (δ / 2)) ϑ :=
      ((hasDerivAt_id ϑ).add_const (k : ℝ)).mul_const (δ / 2)
    have hcomp := (rcoth_hasDerivAt harg.ne').comp ϑ hin
    convert hcomp using 1
    ring
  have hbsum := HasDerivAt.fun_sum (fun k hk => hb k hk)
  have hasum := HasDerivAt.fun_sum (fun k hk => ha k hk)
  have h := hbsum.sub hasum
  convert h using 1
  rw [Finset.sum_neg_distrib, sub_neg_eq_add, mul_add, Finset.mul_sum, Finset.mul_sum]

/-- **The equilibrium forces localization**: if `θ ∈ [1/8, 1/2)` satisfies the equilibrium
condition `g(θ) = −(N + M)`, then `Nδ/78 ≤ 1/2 − θ`. A long behind train is incompatible
with an equilibrium near the midpoint. -/
theorem equilibrium_theta_gap {θ δ : ℝ} {M N : ℕ} (hM1 : 1 ≤ M) (hMN : M ≤ N)
    (hθ8 : 1 / 8 ≤ θ) (hθhalf : θ < 1 / 2) (hδ0 : 0 < δ)
    (hEq : (∑ k ∈ range N, rcoth ((1 - θ + k) * (δ / 2)))
        - (∑ k ∈ range M, rcoth ((θ + k) * (δ / 2))) = -((N : ℝ) + M)) :
    (N : ℝ) * δ / 78 ≤ 1 / 2 - θ := by
  have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le (by norm_num) hθ8
  have h1N : 1 ≤ N := le_trans hM1 hMN
  set g : ℝ → ℝ := fun y => (∑ k ∈ range N, rcoth ((1 - y + k) * (δ / 2)))
      - ∑ k ∈ range M, rcoth ((y + k) * (δ / 2)) with hg
  -- MVT for g on [θ, 1/2]
  have hcont : ContinuousOn g (Set.Icc θ (1 / 2)) := by
    intro y hy
    have h1 : 0 < y := lt_of_lt_of_le hθ0 hy.1
    have h2 : y < 1 := lt_of_le_of_lt hy.2 (by norm_num)
    exact (lattice_constraint_hasDerivAt hδ0 M N h1 h2).continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Set.Ioo θ (1 / 2),
      HasDerivAt g ((fun y => (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range M, (rcsch ((y + k) * (δ / 2))) ^ 2)) y) y := by
    intro y hy
    exact lattice_constraint_hasDerivAt hδ0 M N (lt_trans hθ0 hy.1)
      (lt_trans hy.2 (by norm_num))
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g
    (fun y => (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - y + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range M, (rcsch ((y + k) * (δ / 2))) ^ 2)) hθhalf hcont hderiv
  have hgap : (0 : ℝ) < 1 / 2 - θ := by linarith
  rw [eq_div_iff hgap.ne'] at hslope
  -- the value at the midpoint: the two trains coincide, only the unpaired tail remains
  have hg12 : g (1 / 2) = ∑ k ∈ Ico M N, rcoth ((1 / 2 + (k : ℝ)) * (δ / 2)) := by
    have hcongr : ∀ S : Finset ℕ, ∑ k ∈ S, rcoth ((1 - (1 : ℝ) / 2 + (k : ℝ)) * (δ / 2))
        = ∑ k ∈ S, rcoth ((1 / 2 + (k : ℝ)) * (δ / 2)) := by
      intro S
      exact Finset.sum_congr rfl (fun k _ => by norm_num)
    simp only [hg, hcongr]
    rw [← Finset.sum_range_add_sum_Ico (fun k => rcoth ((1 / 2 + (k : ℝ)) * (δ / 2))) hMN]
    ring
  -- each unpaired coth exceeds 1
  have hg12lb : ((N : ℝ) - M) ≤ g (1 / 2) := by
    rw [hg12]
    have hone : ∀ k ∈ Ico M N, (1 : ℝ) ≤ rcoth ((1 / 2 + (k : ℝ)) * (δ / 2)) := by
      intro k _
      exact (one_lt_rcoth_of_pos (by positivity)).le
    have hcard := Finset.card_nsmul_le_sum (Ico M N)
      (fun k => rcoth ((1 / 2 + (k : ℝ)) * (δ / 2))) 1 hone
    rw [Nat.card_Ico, nsmul_eq_mul, mul_one] at hcard
    calc ((N : ℝ) - M) = ((N - M : ℕ) : ℝ) := by
          rw [Nat.cast_sub hMN]
      _ ≤ _ := hcard
  -- the slope beats 2N
  have h2N : 2 * (N : ℝ) ≤ (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - ξ + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range M, (rcsch ((ξ + k) * (δ / 2))) ^ 2) * (1 / 2 - θ) := by
    have hgθ : g θ = -((N : ℝ) + M) := hEq
    linarith [hslope, hg12lb, hgθ]
  -- the derivative is at most 156/δ on (θ, 1/2), via csch² ≤ 1/s² and the telescopes
  have hξ0 : (1 : ℝ) / 8 < ξ := lt_of_le_of_lt hθ8 hξ.1
  have hξhalf : ξ < 1 / 2 := hξ.2
  have hbterm : ∀ k ∈ range N, (rcsch ((1 - ξ + (k : ℝ)) * (δ / 2))) ^ 2
      ≤ (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) := by
    intro k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hpos2 : 0 < (1 / 2 + (k : ℝ)) * (δ / 2) := by positivity
    have hle : (1 / 2 + (k : ℝ)) * (δ / 2) ≤ (1 - ξ + (k : ℝ)) * (δ / 2) := by nlinarith
    have hmono : (rcsch ((1 - ξ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (rcsch ((1 / 2 + (k : ℝ)) * (δ / 2))) ^ 2 := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [← h]
      · have h1 : rcsch ((1 - ξ + (k : ℝ)) * (δ / 2)) ≤ rcsch ((1 / 2 + (k : ℝ)) * (δ / 2)) :=
          (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hpos2)
            (Set.mem_Ioi.mpr (lt_of_lt_of_le hpos2 hle)) h).le
        exact pow_le_pow_left₀
          (rcsch_pos_of_pos (lt_of_lt_of_le hpos2 hle)).le h1 2
    have hinv := rcsch_sq_le_inv_sq hpos2
    have heq : 1 / ((1 / 2 + (k : ℝ)) * (δ / 2)) ^ 2
        = (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) := by
      rw [mul_pow]
      have hknz : ((1 : ℝ) / 2 + (k : ℝ)) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    linarith [hmono, hinv, heq.ge]
  have haterm : ∀ k ∈ range M, (rcsch ((ξ + (k : ℝ)) * (δ / 2))) ^ 2
      ≤ (4 / δ ^ 2) * (1 / (1 / 8 + (k : ℝ)) ^ 2) := by
    intro k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hpos2 : 0 < (1 / 8 + (k : ℝ)) * (δ / 2) := by positivity
    have hle : (1 / 8 + (k : ℝ)) * (δ / 2) ≤ (ξ + (k : ℝ)) * (δ / 2) := by nlinarith
    have hmono : (rcsch ((ξ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ (rcsch ((1 / 8 + (k : ℝ)) * (δ / 2))) ^ 2 := by
      rcases eq_or_lt_of_le hle with h | h
      · rw [← h]
      · have h1 : rcsch ((ξ + (k : ℝ)) * (δ / 2)) ≤ rcsch ((1 / 8 + (k : ℝ)) * (δ / 2)) :=
          (rcsch_strictAntiOn_pos (Set.mem_Ioi.mpr hpos2)
            (Set.mem_Ioi.mpr (lt_of_lt_of_le hpos2 hle)) h).le
        exact pow_le_pow_left₀
          (rcsch_pos_of_pos (lt_of_lt_of_le hpos2 hle)).le h1 2
    have hinv := rcsch_sq_le_inv_sq hpos2
    have heq : 1 / ((1 / 8 + (k : ℝ)) * (δ / 2)) ^ 2
        = (4 / δ ^ 2) * (1 / (1 / 8 + (k : ℝ)) ^ 2) := by
      rw [mul_pow]
      have hknz : ((1 : ℝ) / 8 + (k : ℝ)) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    linarith [hmono, hinv, heq.ge]
  -- behind inverse-square sum ≤ 4 + 2 = 6
  have hsum6 : ∑ k ∈ range N, 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2 ≤ 6 := by
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2) h1N
    have htel := inv_sq_telescope (a := 1 / 2) (M := 1) (N := N) h1N
      (by norm_num : (0 : ℝ) < 1 / 2 + (1 : ℕ) - 1)
    have h0 : ∑ k ∈ range 1, 1 / ((1 : ℝ) / 2 + (k : ℝ)) ^ 2 = 4 := by
      rw [Finset.sum_range_one]
      norm_num
    have htelval : (1 : ℝ) / (1 / 2 + (1 : ℕ) - 1) = 2 := by norm_num
    rw [htelval] at htel
    linarith [hsplit, htel, h0]
  -- ahead inverse-square sum ≤ 64 + 8 = 72
  have hsum72 : ∑ k ∈ range M, 1 / ((1 : ℝ) / 8 + (k : ℝ)) ^ 2 ≤ 72 := by
    have hsplit := Finset.sum_range_add_sum_Ico
      (fun k => 1 / ((1 : ℝ) / 8 + (k : ℝ)) ^ 2) hM1
    have htel := inv_sq_telescope (a := 1 / 8) (M := 1) (N := M) hM1
      (by norm_num : (0 : ℝ) < 1 / 8 + (1 : ℕ) - 1)
    have h0 : ∑ k ∈ range 1, 1 / ((1 : ℝ) / 8 + (k : ℝ)) ^ 2 = 64 := by
      rw [Finset.sum_range_one]
      norm_num
    have htelval : (1 : ℝ) / (1 / 8 + (1 : ℕ) - 1) = 8 := by norm_num
    rw [htelval] at htel
    linarith [hsplit, htel, h0]
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hbsum : ∑ k ∈ range N, (rcsch ((1 - ξ + (k : ℝ)) * (δ / 2))) ^ 2 ≤ 24 / δ ^ 2 := by
    calc ∑ k ∈ range N, (rcsch ((1 - ξ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ ∑ k ∈ range N, (4 / δ ^ 2) * (1 / (1 / 2 + (k : ℝ)) ^ 2) :=
          Finset.sum_le_sum hbterm
      _ = (4 / δ ^ 2) * ∑ k ∈ range N, 1 / (1 / 2 + (k : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (4 / δ ^ 2) * 6 := by
          apply mul_le_mul_of_nonneg_left hsum6 (by positivity)
      _ = 24 / δ ^ 2 := by ring
  have hasum : ∑ k ∈ range M, (rcsch ((ξ + (k : ℝ)) * (δ / 2))) ^ 2 ≤ 288 / δ ^ 2 := by
    calc ∑ k ∈ range M, (rcsch ((ξ + (k : ℝ)) * (δ / 2))) ^ 2
        ≤ ∑ k ∈ range M, (4 / δ ^ 2) * (1 / (1 / 8 + (k : ℝ)) ^ 2) :=
          Finset.sum_le_sum haterm
      _ = (4 / δ ^ 2) * ∑ k ∈ range M, 1 / (1 / 8 + (k : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (4 / δ ^ 2) * 72 := by
          apply mul_le_mul_of_nonneg_left hsum72 (by positivity)
      _ = 288 / δ ^ 2 := by ring
  -- assemble: 2N ≤ (156/δ)(1/2 − θ)
  have hDbound : (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - ξ + k) * (δ / 2))) ^ 2)
      + ∑ k ∈ range M, (rcsch ((ξ + k) * (δ / 2))) ^ 2) ≤ 156 / δ := by
    have hsum312 : (∑ k ∈ range N, (rcsch ((1 - ξ + (k : ℝ)) * (δ / 2))) ^ 2)
        + ∑ k ∈ range M, (rcsch ((ξ + (k : ℝ)) * (δ / 2))) ^ 2 ≤ 312 / δ ^ 2 := by
      have h312 : (24 : ℝ) / δ ^ 2 + 288 / δ ^ 2 = 312 / δ ^ 2 := by ring
      linarith [hbsum, hasum, h312]
    have hfin : (δ / 2) * (312 / δ ^ 2) = 156 / δ := by
      field_simp
      ring
    calc (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - ξ + k) * (δ / 2))) ^ 2)
        + ∑ k ∈ range M, (rcsch ((ξ + k) * (δ / 2))) ^ 2)
        ≤ (δ / 2) * (312 / δ ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsum312 (by positivity)
      _ = 156 / δ := hfin
  -- conclude: Nδ/78 ≤ 1/2 − θ
  have hchain : 2 * (N : ℝ) ≤ (156 / δ) * (1 / 2 - θ) := by
    calc 2 * (N : ℝ)
        ≤ (δ / 2) * ((∑ k ∈ range N, (rcsch ((1 - ξ + k) * (δ / 2))) ^ 2)
          + ∑ k ∈ range M, (rcsch ((ξ + k) * (δ / 2))) ^ 2) * (1 / 2 - θ) := h2N
      _ ≤ (156 / δ) * (1 / 2 - θ) := by
          apply mul_le_mul_of_nonneg_right hDbound hgap.le
  have hmul := mul_le_mul_of_nonneg_right hchain hδ0.le
  have heval : (156 / δ) * (1 / 2 - θ) * δ = 156 * (1 / 2 - θ) := by
    field_simp
  rw [heval] at hmul
  linarith [hmul]

/-- **The comparison holds at every equilibrium with a long behind train** — no hypothesis
on `θ` beyond the equilibrium condition itself. If `δ ≤ 1`, `Nδ > 30`, and `θ ∈ (0, 1/2)`
satisfies `g(θ) = −(N + M)`, then `Σ_{k<N} φ((1−θ+k)δ/2) < Σ_{k<M} φ((θ+k)δ/2)`.
Either `θ ≤ 1/8` and the small-step comparison applies directly, or `θ > 1/8` — impossible,
since `equilibrium_theta_gap` would force `Nδ ≤ 78·(1/2 − 1/8) < 30`. -/
theorem dW_dtheta_neg_at_equilibrium {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθhalf : θ < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hNδ : 30 < (N : ℝ) * δ)
    (hEq : (∑ k ∈ range N, rcoth ((1 - θ + k) * (δ / 2)))
        - (∑ k ∈ range M, rcoth ((θ + k) * (δ / 2))) = -((N : ℝ) + M)) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  by_cases hθ8 : θ ≤ 1 / 8
  · exact dW_dtheta_neg_small_delta hMN hM1 hθ0 hθ8 hδ0 hδ1
  · have hθ8' : (1 : ℝ) / 8 < θ := not_le.mp hθ8
    have hbound := equilibrium_theta_gap hM1 hMN hθ8'.le hθhalf hδ0 hEq
    exact absurd hNδ (by linarith)

end RHTower
