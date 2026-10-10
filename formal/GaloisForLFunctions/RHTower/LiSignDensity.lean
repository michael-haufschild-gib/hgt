import GaloisForLFunctions.RHTower.LiSignOscillation

/-!
# Off the critical line both signs of the Li coefficients have positive density

Write `2λ_n = Σ_ρ m_ρ (2 − w_ρⁿ − w_ρ⁻ⁿ)` for the paired Li coefficients. If the Riemann hypothesis
fails, then for some `c > 0` and all large `N` the indices `n < N` with `Re 2λ_n < 0` number at
least `cN`, and so do those with `Re 2λ_n > 0`
(`exists_density_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis`). Consequently the Riemann
hypothesis holds as soon as the negative indices have lower density zero
(`riemannHypothesis_of_liminf_density_re_xiLiPaired_neg_zero`): Li's criterion cannot fail on a
sparse set.

**Mechanism.**
* *Dominant part.* Among the finitely many Cayley roots `v_ρ` (normalised to modulus `≥ 1`) of
  modulus above a threshold, those of maximal modulus `R > 1` form a set `D`. Writing
  `v_ρ = R u_ρ`, `‖u_ρ‖ = 1`, one has `Re 2λ_n = −Rⁿ f(n) + o(Rⁿ)` with
  `f(n) = Σ_{ρ ∈ D} m_ρ Re(u_ρⁿ)` (`abs_re_tsum_liTerm_add_dominant_le`).
* *Mean values.* The `u_ρ` are non-real, so `u_ρ² ≠ 1`. Geometric sums give `|Σ_{n<N} f(n)| ≤ B₁`
  and `Σ_{n<N} f(n)² ≥ (N/2) Σ m_ρ² − B₂`. With `|f| ≤ F = Σ m_ρ` this forces
  `#{n < N : f(n) > ε} ≥ cN − K` and `#{n < N : f(n) < −ε} ≥ cN − K` for `ε = σ²/(4F)`,
  `c = σ²/(4F²)`, `σ² = ½Σ m_ρ²` (`exists_card_filter_gt_and_lt`).
-/

open Complex Filter

noncomputable section

namespace RHTower

/-! ## Finite unimodular cosine sums -/

/-- `‖Σ_{n<N} wⁿ‖ ≤ 2/‖w − 1‖` for `‖w‖ = 1`, `w ≠ 1`. -/
theorem norm_geom_sum_le_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ 2 / ‖w - 1‖ := by
  rw [geom_sum_eq hw1 N, norm_div]
  have h1 : ‖w ^ N - 1‖ ≤ 2 := by
    calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num
  exact div_le_div_of_nonneg_right h1 (norm_nonneg _)

/-- The bound `b(w) = 2/‖w − 1‖` for `w ≠ 1` and `0` at `w = 1`. -/
def unimodularGeomBound (w : ℂ) : ℝ := if w = 1 then 0 else 2 / ‖w - 1‖

theorem unimodularGeomBound_nonneg (w : ℂ) : 0 ≤ unimodularGeomBound w := by
  unfold unimodularGeomBound; split_ifs <;> positivity

/-- `Re(a)Re(b) = (Re(ab) + Re(a b̄))/2`. -/
theorem re_mul_re_eq_half_sum (a b : ℂ) : a.re * b.re = ((a * b).re + (a * (starRingEnd ℂ) b).re) / 2 := by
  simp [Complex.mul_re]

/-- Shifted geometric sums: `Re Σ_{n<N} w^{M+n} ≥ −b(w)` for every unimodular `w`, uniformly in
`M`. -/
theorem neg_unimodularGeomBound_le_re_sum_shift {w : ℂ} (hw : ‖w‖ = 1) (M N : ℕ) :
    -unimodularGeomBound w ≤ (∑ n ∈ Finset.range N, w ^ (M + n)).re := by
  unfold unimodularGeomBound
  split_ifs with h1
  · subst h1; simp
  · have h := norm_geom_sum_le_of_norm_eq_one hw h1 N
    have he : ∑ n ∈ Finset.range N, w ^ (M + n) = w ^ M * ∑ n ∈ Finset.range N, w ^ n := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => pow_add w M n
    have h2 : ‖∑ n ∈ Finset.range N, w ^ (M + n)‖ ≤ 2 / ‖w - 1‖ := by
      rw [he, norm_mul, norm_pow, hw, one_pow, one_mul]; exact h
    have := Complex.abs_re_le_norm (∑ n ∈ Finset.range N, w ^ (M + n))
    have := neg_abs_le (∑ n ∈ Finset.range N, w ^ (M + n)).re
    linarith

/-- Shifted pair sums, uniformly in `M`. -/
theorem sum_re_pow_mul_re_pow_ge_shift {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (M N : ℕ) :
    (if x * (starRingEnd ℂ) y = 1 then (N : ℝ) / 2 else 0)
        - (unimodularGeomBound (x * y) + unimodularGeomBound (x * (starRingEnd ℂ) y)) / 2
      ≤ ∑ n ∈ Finset.range N, (x ^ (M + n)).re * (y ^ (M + n)).re := by
  have hxy : ‖x * y‖ = 1 := by rw [norm_mul, hx, hy, one_mul]
  have hxy' : ‖x * (starRingEnd ℂ) y‖ = 1 := by rw [norm_mul, Complex.norm_conj, hx, hy, one_mul]
  have hsplit : ∑ n ∈ Finset.range N, (x ^ (M + n)).re * (y ^ (M + n)).re
      = ((∑ n ∈ Finset.range N, (x * y) ^ (M + n)).re
        + (∑ n ∈ Finset.range N, (x * (starRingEnd ℂ) y) ^ (M + n)).re) / 2 := by
    rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [re_mul_re_eq_half_sum, mul_pow, mul_pow, map_pow]
  rw [hsplit]
  have h1 := neg_unimodularGeomBound_le_re_sum_shift hxy M N
  have h2 := neg_unimodularGeomBound_le_re_sum_shift hxy' M N
  split_ifs with hc
  · have : (∑ n ∈ Finset.range N, (x * (starRingEnd ℂ) y) ^ (M + n)).re = N := by
      rw [hc]; simp
    have hb : unimodularGeomBound (x * (starRingEnd ℂ) y) = 0 := by
      unfold unimodularGeomBound; rw [if_pos hc]
    rw [this, hb]
    linarith
  · have := unimodularGeomBound_nonneg (x * (starRingEnd ℂ) y)
    linarith

/-- **Both signs in every window.** The constants of `exists_card_filter_gt_and_lt` are uniform in
the starting point: for every `M`, `f(M + n) = Σ m_i Re(u_i^{M+n})` exceeds `ε` and falls below
`−ε` on at least `cN − K` of the `n < N`. -/
theorem exists_card_filter_gt_and_lt_shift {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℂ)
    (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hu2 : ∀ i, u i ^ 2 ≠ 1) (hm : ∀ i, 0 < m i) :
    ∃ ε c K : ℝ, 0 < ε ∧ 0 < c ∧ ∀ M N : ℕ,
      c * N - K ≤ (((Finset.range N).filter
        (fun n => ε < ∑ i, m i * (u i ^ (M + n)).re)).card : ℝ) ∧
      c * N - K ≤ (((Finset.range N).filter
        (fun n => ∑ i, m i * (u i ^ (M + n)).re < -ε)).card : ℝ) := by
  classical
  set F : ℝ := ∑ i, m i with hF
  have hF0 : 0 < F := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hre1 : ∀ i n, |(u i ^ n).re| ≤ 1 := fun i n => by
    calc |(u i ^ n).re| ≤ ‖u i ^ n‖ := Complex.abs_re_le_norm _
      _ = 1 := by rw [norm_pow, hu i, one_pow]
  set σ2 : ℝ := (∑ i, m i ^ 2) / 2 with hσ2
  have hσ0 : 0 < σ2 := by
    have := Finset.sum_pos (fun i _ => pow_pos (hm i) 2) (Finset.univ_nonempty (α := ι))
    rw [hσ2]; linarith
  have hu1 : ∀ i, u i ≠ 1 := fun i h => hu2 i (by rw [h]; norm_num)
  set B₁ : ℝ := ∑ i, m i * unimodularGeomBound (u i) with hB₁
  set B₂ : ℝ := ∑ i, ∑ j, m i * m j * ((unimodularGeomBound (u i * u j)
      + unimodularGeomBound (u i * (starRingEnd ℂ) (u j))) / 2) with hB₂
  set ε : ℝ := σ2 / (4 * F) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hB₁0 : 0 ≤ B₁ := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hm i).le (unimodularGeomBound_nonneg _)
  refine ⟨ε, σ2 / (4 * F ^ 2), (B₂ + F * B₁) / (2 * F ^ 2), hε0, by positivity,
    fun M N => ?_⟩
  set f : ℕ → ℝ := fun n => ∑ i, m i * (u i ^ (M + n)).re with hf
  have hfabs : ∀ n, |f n| ≤ F := by
    intro n
    calc |f n| ≤ ∑ i, |m i * (u i ^ (M + n)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, m i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_pos (hm i)]
          nlinarith [hre1 i (M + n), hm i]
  have hsum1 : |∑ n ∈ Finset.range N, f n| ≤ B₁ := by
    have he : ∑ n ∈ Finset.range N, f n
        = ∑ i, m i * (∑ n ∈ Finset.range N, u i ^ (M + n)).re := by
      rw [hf]; simp only
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum, Complex.re_sum]
    rw [he]
    calc |∑ i, m i * (∑ n ∈ Finset.range N, u i ^ (M + n)).re|
        ≤ ∑ i, |m i * (∑ n ∈ Finset.range N, u i ^ (M + n)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, m i * unimodularGeomBound (u i) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_pos (hm i)]
          refine mul_le_mul_of_nonneg_left ?_ (hm i).le
          have he2 : ∑ n ∈ Finset.range N, u i ^ (M + n)
              = u i ^ M * ∑ n ∈ Finset.range N, u i ^ n := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => pow_add (u i) M n
          unfold unimodularGeomBound
          rw [if_neg (hu1 i)]
          calc |(∑ n ∈ Finset.range N, u i ^ (M + n)).re|
              ≤ ‖∑ n ∈ Finset.range N, u i ^ (M + n)‖ := Complex.abs_re_le_norm _
            _ = ‖∑ n ∈ Finset.range N, u i ^ n‖ := by
                rw [he2, norm_mul, norm_pow, hu i, one_pow, one_mul]
            _ ≤ 2 / ‖u i - 1‖ := norm_geom_sum_le_of_norm_eq_one (hu i) (hu1 i) N
  have hsum2 : σ2 * N - B₂ ≤ ∑ n ∈ Finset.range N, f n ^ 2 := by
    have he : ∑ n ∈ Finset.range N, f n ^ 2
        = ∑ i, ∑ j, m i * m j * ∑ n ∈ Finset.range N, (u i ^ (M + n)).re * (u j ^ (M + n)).re := by
      rw [hf]; simp only
      have : ∀ n, (∑ i, m i * (u i ^ (M + n)).re) ^ 2
          = ∑ i, ∑ j, m i * m j * ((u i ^ (M + n)).re * (u j ^ (M + n)).re) := by
        intro n
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      simp_rw [this]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
    rw [he]
    have hpair : ∀ i j, m i * m j * ((if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0)
          - (unimodularGeomBound (u i * u j)
            + unimodularGeomBound (u i * (starRingEnd ℂ) (u j))) / 2)
        ≤ m i * m j * ∑ n ∈ Finset.range N, (u i ^ (M + n)).re * (u j ^ (M + n)).re :=
      fun i j => mul_le_mul_of_nonneg_left (sum_re_pow_mul_re_pow_ge_shift (hu i) (hu j) M N)
        (mul_nonneg (hm i).le (hm j).le)
    have hdiag : ∀ i, m i * m i * (if u i * (starRingEnd ℂ) (u i) = 1 then (N : ℝ) / 2 else 0)
        = m i ^ 2 * N / 2 := by
      intro i
      have h1 : u i * (starRingEnd ℂ) (u i) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu i]; norm_num
      rw [if_pos h1]; ring
    have hind : ∀ i, m i ^ 2 * N / 2 ≤ ∑ j, m i * m j *
        (if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0) := by
      intro i
      rw [← hdiag i]
      exact Finset.single_le_sum (f := fun j => m i * m j *
        (if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0))
        (fun j _ => mul_nonneg (mul_nonneg (hm i).le (hm j).le) (by split_ifs <;> positivity))
        (Finset.mem_univ i)
    have hlow : σ2 * N ≤ ∑ i, ∑ j, m i * m j *
        (if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0) := by
      rw [hσ2, div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => hind i
    have hexp : ∑ i, ∑ j, m i * m j * ((if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0)
          - (unimodularGeomBound (u i * u j)
            + unimodularGeomBound (u i * (starRingEnd ℂ) (u j))) / 2)
        = ∑ i, ∑ j, m i * m j * (if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0)
          - B₂ := by
      rw [hB₂, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    calc σ2 * N - B₂ ≤ _ := by linarith
      _ = ∑ i, ∑ j, m i * m j * ((if u i * (starRingEnd ℂ) (u j) = 1 then (N : ℝ) / 2 else 0)
          - (unimodularGeomBound (u i * u j)
            + unimodularGeomBound (u i * (starRingEnd ℂ) (u j))) / 2) := hexp.symm
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
  have hsq : ∀ n, f n ^ 2 ≤ F * |f n| := fun n => by
    rw [← sq_abs]; nlinarith [hfabs n, abs_nonneg (f n)]
  constructor
  · set A := ((Finset.range N).filter (fun n => ε < f n)).card with hA
    have hpt : ∀ n, f n ^ 2 ≤ F * (2 * (if ε < f n then F else ε) - f n) := by
      intro n
      have h1 := hsq n
      have h2 : |f n| ≤ 2 * (if ε < f n then F else ε) - f n := by
        split_ifs with h
        · have h3 := (abs_le.mp (hfabs n)).2
          rw [abs_of_pos (by linarith)]; linarith
        · push Not at h; cases abs_cases (f n) <;> linarith
      nlinarith
    have hsumite : ∑ n ∈ Finset.range N, (if ε < f n then F else ε) ≤ F * A + ε * N := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hcard : (((Finset.range N).filter (fun n => ¬ ε < f n)).card : ℝ) ≤ N := by
        have := Finset.card_filter_le (Finset.range N) (fun n => ¬ ε < f n)
        rw [Finset.card_range] at this; exact_mod_cast this
      rw [← hA]
      nlinarith
    have htot : ∑ n ∈ Finset.range N, f n ^ 2 ≤ F * (2 * (F * A + ε * N) + B₁) := by
      calc ∑ n ∈ Finset.range N, f n ^ 2
          ≤ ∑ n ∈ Finset.range N, F * (2 * (if ε < f n then F else ε) - f n) :=
            Finset.sum_le_sum fun n _ => hpt n
        _ = F * (2 * ∑ n ∈ Finset.range N, (if ε < f n then F else ε)
            - ∑ n ∈ Finset.range N, f n) := by
            rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.mul_sum]
        _ ≤ F * (2 * (F * A + ε * N) + B₁) := by
            have := (abs_le.mp hsum1).1
            nlinarith
    have hεF : 2 * F * ε = σ2 / 2 := by rw [hε]; field_simp; ring
    have he : σ2 / (4 * F ^ 2) * N - (B₂ + F * B₁) / (2 * F ^ 2)
        = (σ2 * N - 2 * (B₂ + F * B₁)) / (4 * F ^ 2) := by field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith
  · set A := ((Finset.range N).filter (fun n => f n < -ε)).card with hA
    have hpt : ∀ n, f n ^ 2 ≤ F * (2 * (if f n < -ε then F else ε) + f n) := by
      intro n
      have h1 := hsq n
      have h2 : |f n| ≤ 2 * (if f n < -ε then F else ε) + f n := by
        split_ifs with h
        · cases abs_cases (f n) <;> linarith [(abs_le.mp (hfabs n)).1]
        · push Not at h; cases abs_cases (f n) <;> linarith
      nlinarith
    have hsumite : ∑ n ∈ Finset.range N, (if f n < -ε then F else ε) ≤ F * A + ε * N := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hcard : (((Finset.range N).filter (fun n => ¬ f n < -ε)).card : ℝ) ≤ N := by
        have := Finset.card_filter_le (Finset.range N) (fun n => ¬ f n < -ε)
        rw [Finset.card_range] at this; exact_mod_cast this
      rw [← hA]
      nlinarith
    have htot : ∑ n ∈ Finset.range N, f n ^ 2 ≤ F * (2 * (F * A + ε * N) + B₁) := by
      calc ∑ n ∈ Finset.range N, f n ^ 2
          ≤ ∑ n ∈ Finset.range N, F * (2 * (if f n < -ε then F else ε) + f n) :=
            Finset.sum_le_sum fun n _ => hpt n
        _ = F * (2 * ∑ n ∈ Finset.range N, (if f n < -ε then F else ε)
            + ∑ n ∈ Finset.range N, f n) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ F * (2 * (F * A + ε * N) + B₁) := by
            have := (abs_le.mp hsum1).2
            nlinarith
    have hεF : 2 * F * ε = σ2 / 2 := by rw [hε]; field_simp; ring
    have he : σ2 / (4 * F ^ 2) * N - (B₂ + F * B₁) / (2 * F ^ 2)
        = (σ2 * N - 2 * (B₂ + F * B₁)) / (4 * F ^ 2) := by field_simp; ring
    rw [he, div_le_iff₀ (by positivity)]
    nlinarith

/-- **Both signs on a positive proportion.** For a finite nonempty family of unimodular `u_i` with
`u_i² ≠ 1` and weights `m_i > 0`, the cosine sum `f(n) = Σ m_i Re(u_iⁿ)` exceeds `ε` and falls
below `−ε` on at least `cN − K` of the indices `n < N`. -/
theorem exists_card_filter_gt_and_lt {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℂ)
    (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hu2 : ∀ i, u i ^ 2 ≠ 1) (hm : ∀ i, 0 < m i) :
    ∃ ε c K : ℝ, 0 < ε ∧ 0 < c ∧ ∀ N : ℕ,
      c * N - K ≤ (((Finset.range N).filter (fun n => ε < ∑ i, m i * (u i ^ n).re)).card : ℝ) ∧
      c * N - K ≤ (((Finset.range N).filter (fun n => ∑ i, m i * (u i ^ n).re < -ε)).card : ℝ) := by
  obtain ⟨ε, c, K, hε, hc, h⟩ := exists_card_filter_gt_and_lt_shift u m hu hu2 hm
  exact ⟨ε, c, K, hε, hc, fun N => by simpa using h 0 N⟩

/-! ## The dominant part of the paired Li sums -/

theorem re_inv_pow_le_one {v : ℂ} (hv : 1 ≤ ‖v‖) (n : ℕ) : |(v⁻¹ ^ n).re| ≤ 1 := by
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv
  calc |(v⁻¹ ^ n).re| ≤ ‖v⁻¹ ^ n‖ := Complex.abs_re_le_norm _
    _ ≤ 1 := by
        rw [norm_pow, norm_inv]
        exact pow_le_one₀ (by positivity) ((inv_le_one₀ hvpos).mpr hv)

/-- `Re liTerm(v, n) + Re(vⁿ) = 2 − Re(v⁻ⁿ)` lies in `[1, 3]`. -/
theorem abs_re_liTerm_add_re_pow_le {v : ℂ} (hv : 1 ≤ ‖v‖) (n : ℕ) :
    |(liTerm v n).re + (v ^ n).re| ≤ 3 := by
  have h := re_inv_pow_le_one hv n
  have hl : (liTerm v n).re = 2 - (v ^ n).re - (v⁻¹ ^ n).re := by rw [liTerm]; simp
  rw [hl, abs_le]
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- `|Re liTerm(v, n)| ≤ 3 + ‖v‖ⁿ`. -/
theorem abs_re_liTerm_le_three_add {v : ℂ} (hv : 1 ≤ ‖v‖) (n : ℕ) :
    |(liTerm v n).re| ≤ 3 + ‖v‖ ^ n := by
  have h := abs_re_liTerm_add_re_pow_le hv n
  have h2 : |(v ^ n).re| ≤ ‖v‖ ^ n := by rw [← norm_pow]; exact Complex.abs_re_le_norm _
  calc |(liTerm v n).re| = |((liTerm v n).re + (v ^ n).re) - (v ^ n).re| := by ring_nf
    _ ≤ |(liTerm v n).re + (v ^ n).re| + |(v ^ n).re| := abs_sub _ _
    _ ≤ 3 + ‖v‖ ^ n := add_le_add h h2

/-- For `1 ≤ ‖v‖ ≤ q`: `|Re liTerm(v, n)| ≤ n² qⁿ ‖v − 1‖²`. -/
theorem abs_re_liTerm_le_tail {v : ℂ} {q : ℝ} (hv : 1 ≤ ‖v‖) (hq : ‖v‖ ≤ q) (n : ℕ) :
    |(liTerm v n).re| ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v - 1‖ ^ (2 : ℕ) := by
  have hvpos : 0 < ‖v‖ := lt_of_lt_of_le zero_lt_one hv
  have hvne : v ≠ 0 := norm_pos_iff.mp hvpos
  have hmax : max ‖v‖ ‖v‖⁻¹ = ‖v‖ := by
    refine max_eq_left ?_
    rw [inv_le_iff_one_le_mul₀ hvpos]; nlinarith
  have hbase := norm_liTerm_le hvne n
  rw [hmax] at hbase
  have hpow : ‖v‖ ^ n ≤ q ^ n := pow_le_pow_left₀ (norm_nonneg _) hq n
  calc |(liTerm v n).re| ≤ ‖liTerm v n‖ := Complex.abs_re_le_norm _
    _ ≤ (n : ℝ) ^ (2 : ℕ) * ‖v‖ ^ n * ‖v - 1‖ ^ (2 : ℕ) := hbase
    _ ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v - 1‖ ^ (2 : ℕ) := by gcongr

variable {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}

/-- **The dominant part.** If some Cayley root has modulus `> 1`, there are a finite nonempty set
`D` of indices of maximal modulus `R > 1` such that for every `η > 0`, eventually
`|Σ' m Re liTerm(v, n) + Rⁿ Σ_{i∈D} m_i Re((v_i/R)ⁿ)| ≤ η Rⁿ`. -/
theorem abs_re_tsum_liTerm_add_dominant_le
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ (D : Finset ι) (R : ℝ), D.Nonempty ∧ 1 < R ∧ (∀ i ∈ D, ‖v i‖ = R) ∧
      ∀ η : ℝ, 0 < η → ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n →
        |∑' i, m i * (liTerm (v i) n).re + R ^ n * ∑ i ∈ D, m i * ((v i / R) ^ n).re|
          ≤ η * R ^ n := by
  classical
  have hm0 : ∀ i, (0 : ℝ) ≤ m i := fun i => by linarith [hm i]
  set W : ℝ := ‖v i₀‖ with hWdef
  set q : ℝ := (1 + W) / 2 with hqdef
  clear_value W q
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hqW : q < W := by rw [hqdef]; linarith
  have hFfin : {i | q ≤ ‖v i‖}.Finite := finite_far_set hm hs hq1
  set S : Finset ι := hFfin.toFinset with hSdef
  have hmemS : ∀ i, i ∈ S ↔ q ≤ ‖v i‖ := by
    intro i; rw [hSdef, Set.Finite.mem_toFinset]; rfl
  have hi₀S : i₀ ∈ S := (hmemS i₀).mpr (by rw [hWdef] at hqW; exact hqW.le)
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  set R : ℝ := S.sup' hSne (fun i => ‖v i‖) with hRdef
  have hRle : ∀ i ∈ S, ‖v i‖ ≤ R := fun i hi => Finset.le_sup' (fun i => ‖v i‖) hi
  have hWR : W ≤ R := by rw [hWdef]; exact hRle i₀ hi₀S
  have hqR : q < R := lt_of_lt_of_le hqW hWR
  have hR0 : (0 : ℝ) < R := by linarith
  have hR1 : (1 : ℝ) < R := by linarith
  set D : Finset ι := S.filter (fun i => ‖v i‖ = R) with hDdef
  set E : Finset ι := S.filter (fun i => ¬ ‖v i‖ = R) with hEdef
  have hDne : D.Nonempty := by
    obtain ⟨j, hjS, hj⟩ := Finset.exists_mem_eq_sup' hSne (fun i => ‖v i‖)
    exact ⟨j, Finset.mem_filter.mpr ⟨hjS, hj.symm⟩⟩
  have hDnorm : ∀ i ∈ D, ‖v i‖ = R := fun i hi => (Finset.mem_filter.mp hi).2
  have hElt : ∀ i ∈ E, ‖v i‖ < R := fun i hi =>
    lt_of_le_of_ne (hRle i (Finset.mem_filter.mp hi).1) (Finset.mem_filter.mp hi).2
  refine ⟨D, R, hDne, hR1, hDnorm, fun η hη => ?_⟩
  set C : ℝ := ∑' i, m i * ‖v i - 1‖ ^ (2 : ℕ) with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg fun i => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
  set mS : ℝ := ∑ i ∈ S, m i with hmS
  -- the error, normalised by `Rⁿ`, tends to zero
  have hlim : Tendsto (fun n : ℕ => 3 * mS * (1 / R) ^ n + ∑ i ∈ E, m i * (‖v i‖ / R) ^ n
      + C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => 3 * mS * (1 / R) ^ n) atTop (nhds 0) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / R)
        ((div_lt_one hR0).mpr hR1)
      simpa using this.const_mul (3 * mS)
    have h2 : Tendsto (fun n : ℕ => ∑ i ∈ E, m i * (‖v i‖ / R) ^ n) atTop (nhds 0) := by
      have h0 : (0 : ℝ) = ∑ i ∈ E, m i * 0 := by simp
      rw [h0]
      refine tendsto_finsetSum _ fun i hi => ?_
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        ((div_lt_one hR0).mpr (hElt i hi))).const_mul _
    have h3 : Tendsto (fun n : ℕ => C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n)) atTop (nhds 0) := by
      have hr0 : 0 ≤ q / R := by positivity
      have hr1 : q / R < 1 := (div_lt_one hR0).mpr hqR
      have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (2 : ℕ) * (q / R) ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one 2 (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
      simpa using hsum.tendsto_atTop_zero.const_mul C
    simpa using (h1.add h2).add h3
  obtain ⟨N₁, hN₁⟩ := (hlim.eventually (gt_mem_nhds hη)).exists_forall_of_atTop
  refine ⟨N₁, fun n hn => ?_⟩
  have hsmall := (hN₁ n hn).le
  have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
  -- split the sum
  have hsummable := summable_re_liTerm_of_one_le hm0 hv hM hs n
  have hsplit := hsummable.sum_add_tsum_compl (s := S)
  have hSDE : ∑ i ∈ S, m i * (liTerm (v i) n).re
      = ∑ i ∈ D, m i * (liTerm (v i) n).re + ∑ i ∈ E, m i * (liTerm (v i) n).re := by
    rw [hDdef, hEdef]; exact (Finset.sum_filter_add_sum_filter_not S _ _).symm
  -- the dominant part
  have hD : |∑ i ∈ D, m i * (liTerm (v i) n).re + R ^ n * ∑ i ∈ D, m i * ((v i / R) ^ n).re|
      ≤ 3 * ∑ i ∈ D, m i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hvn : R ^ n * ((v i / R) ^ n).re = (v i ^ n).re := by
      rw [div_pow, ← Complex.ofReal_pow, Complex.div_ofReal_re, mul_div_cancel₀ _ hRn.ne']
    have h3 := abs_re_liTerm_add_re_pow_le (hv i) n
    calc |m i * (liTerm (v i) n).re + R ^ n * (m i * ((v i / R) ^ n).re)|
        = m i * |(liTerm (v i) n).re + (v i ^ n).re| := by
          rw [← hvn, show m i * (liTerm (v i) n).re + R ^ n * (m i * ((v i / R) ^ n).re)
            = m i * ((liTerm (v i) n).re + R ^ n * ((v i / R) ^ n).re) by ring, abs_mul,
            abs_of_nonneg (hm0 i)]
      _ ≤ m i * 3 := mul_le_mul_of_nonneg_left h3 (hm0 i)
      _ = 3 * m i := by ring
  -- the middle part
  have hE : |∑ i ∈ E, m i * (liTerm (v i) n).re| ≤ 3 * ∑ i ∈ E, m i + ∑ i ∈ E, m i * ‖v i‖ ^ n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_nonneg (hm0 i)]
    have := abs_re_liTerm_le_three_add (hv i) n
    nlinarith [hm0 i]
  -- the tail
  have htailC : (∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) ≤ C := by
    have hsp := hs.sum_add_tsum_compl (s := S)
    have hSnn : (0 : ℝ) ≤ ∑ i ∈ S, m i * ‖v i - 1‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg fun i _ => by nlinarith [hm0 i, sq_nonneg ‖v i - 1‖]
    rw [hCdef, ← hsp]; linarith
  have hBsum : Summable fun i : {x // x ∈ (↑S : Set ι)ᶜ} =>
      (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) :=
    (hs.subtype _).mul_left _
  have hpt : ∀ i : {x // x ∈ (↑S : Set ι)ᶜ},
      |m (i : ι) * (liTerm (v (i : ι)) n).re|
        ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) := by
    rintro ⟨i, hi⟩
    have hiS : ¬ (q ≤ ‖v i‖) := by
      intro h; simp only [Set.mem_compl_iff, Finset.mem_coe] at hi; exact hi ((hmemS i).mpr h)
    have := abs_re_liTerm_le_tail (hv i) (le_of_lt (lt_of_not_ge hiS)) n
    rw [abs_mul, abs_of_nonneg (hm0 i)]
    calc m i * |(liTerm (v i) n).re| ≤ m i * ((n : ℝ) ^ (2 : ℕ) * q ^ n * ‖v i - 1‖ ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left this (hm0 i)
      _ = _ := by ring
  have htail : |∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re|
      ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * C := by
    have habs : Summable fun i : {x // x ∈ (↑S : Set ι)ᶜ} => |m (i : ι) * (liTerm (v (i : ι)) n).re| :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hpt hBsum
    calc |∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re|
        ≤ ∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, |m (i : ι) * (liTerm (v (i : ι)) n).re| := by
          have := norm_tsum_le_tsum_norm (f := fun i : {x // x ∈ (↑S : Set ι)ᶜ} =>
            m (i : ι) * (liTerm (v (i : ι)) n).re) (by simpa [Real.norm_eq_abs] using habs)
          simpa [Real.norm_eq_abs] using this
      _ ≤ ∑' i : {x // x ∈ (↑S : Set ι)ᶜ},
            (n : ℝ) ^ (2 : ℕ) * q ^ n * (m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ)) :=
          habs.tsum_le_tsum hpt hBsum
      _ = (n : ℝ) ^ (2 : ℕ) * q ^ n * ∑' i : {x // x ∈ (↑S : Set ι)ᶜ},
            m (i : ι) * ‖v (i : ι) - 1‖ ^ (2 : ℕ) := tsum_mul_left
      _ ≤ (n : ℝ) ^ (2 : ℕ) * q ^ n * C := mul_le_mul_of_nonneg_left htailC (by positivity)
  -- assemble
  have hmS : ∑ i ∈ D, m i + ∑ i ∈ E, m i = mS := by
    rw [hmS, hDdef, hEdef]; exact Finset.sum_filter_add_sum_filter_not S _ _
  have hEpow : ∑ i ∈ E, m i * ‖v i‖ ^ n = R ^ n * ∑ i ∈ E, m i * (‖v i‖ / R) ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]; field_simp
  have hqpow : (n : ℝ) ^ (2 : ℕ) * q ^ n * C = R ^ n * (C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n)) := by
    rw [div_pow]; field_simp
  have hmSpow : 3 * mS = R ^ n * (3 * mS * (1 / R) ^ n) := by
    rw [one_div, inv_pow]; field_simp
  rw [← hsplit, hSDE]
  have hbound : |∑ i ∈ D, m i * (liTerm (v i) n).re + ∑ i ∈ E, m i * (liTerm (v i) n).re
      + ∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re
      + R ^ n * ∑ i ∈ D, m i * ((v i / R) ^ n).re|
      ≤ 3 * mS + ∑ i ∈ E, m i * ‖v i‖ ^ n + (n : ℝ) ^ (2 : ℕ) * q ^ n * C := by
    have e : ∑ i ∈ D, m i * (liTerm (v i) n).re + ∑ i ∈ E, m i * (liTerm (v i) n).re
        + ∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re
        + R ^ n * ∑ i ∈ D, m i * ((v i / R) ^ n).re
        = (∑ i ∈ D, m i * (liTerm (v i) n).re + R ^ n * ∑ i ∈ D, m i * ((v i / R) ^ n).re)
          + ∑ i ∈ E, m i * (liTerm (v i) n).re
          + ∑' i : {x // x ∈ (↑S : Set ι)ᶜ}, m (i : ι) * (liTerm (v (i : ι)) n).re := by ring
    rw [e]
    refine (abs_add_three _ _ _).trans ?_
    linarith
  calc _ ≤ 3 * mS + ∑ i ∈ E, m i * ‖v i‖ ^ n + (n : ℝ) ^ (2 : ℕ) * q ^ n * C := hbound
    _ = R ^ n * (3 * mS * (1 / R) ^ n + ∑ i ∈ E, m i * (‖v i‖ / R) ^ n
          + C * ((n : ℝ) ^ (2 : ℕ) * (q / R) ^ n)) := by
        rw [hEpow, hqpow, mul_add, mul_add, ← hmSpow]
    _ ≤ R ^ n * η := mul_le_mul_of_nonneg_left hsmall hRn.le
    _ = η * R ^ n := by ring

/-! ## Both signs with positive density -/

theorem card_filter_le_card_filter_add {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    {N₁ : ℕ} (h : ∀ n, N₁ ≤ n → P n → Q n) (N : ℕ) :
    ((Finset.range N).filter P).card ≤ ((Finset.range N).filter Q).card + N₁ := by
  classical
  have hsub : (Finset.range N).filter P ⊆ (Finset.range N).filter Q ∪ Finset.range N₁ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rcases lt_or_ge n N₁ with hlt | hge
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr hlt)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn.1, h n hge hn.2⟩)
  calc ((Finset.range N).filter P).card ≤ ((Finset.range N).filter Q ∪ Finset.range N₁).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range N).filter Q).card + (Finset.range N₁).card := Finset.card_union_le _ _
    _ = _ := by rw [Finset.card_range]

/-- **Both signs with positive density, abstract form.** If one member of a non-real family lies
strictly outside the unit circle, the paired Li sums are negative on at least `cN − K` and positive
on at least `cN − K` of the indices `n < N`. -/
theorem exists_density_re_tsum_liTerm_neg_and_pos
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) (hnr : ∀ i, (v i).im ≠ 0)
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ c K : ℝ, 0 < c ∧ ∀ N : ℕ,
      c * N - K ≤ (((Finset.range N).filter
        (fun n => ∑' i, m i * (liTerm (v i) n).re < 0)).card : ℝ) ∧
      c * N - K ≤ (((Finset.range N).filter
        (fun n => 0 < ∑' i, m i * (liTerm (v i) n).re)).card : ℝ) := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, hDnorm i i.2,
      div_self hR0.ne']
  have hu2 : ∀ i, u i ^ 2 ≠ 1 := by
    intro i h
    have him : (u i).im ≠ 0 := by
      rw [hudef]; simp only
      rw [Complex.div_ofReal_im]
      exact div_ne_zero (hnr i) hR0.ne'
    have : u i = 1 ∨ u i = -1 := by
      have h' : (u i - 1) * (u i + 1) = 0 := by ring_nf; rw [h]; ring
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases this with h1 | h1 <;> rw [h1] at him <;> simp at him
  obtain ⟨ε, c, K, hε, hc, hcount⟩ :=
    exists_card_filter_gt_and_lt u (fun i => m i) hunit hu2 (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re := by
    intro n
    exact Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  refine ⟨c, K + N₁, hc, fun N => ?_⟩
  obtain ⟨hpos, hneg⟩ := hcount N
  constructor
  · have hle := card_filter_le_card_filter_add
      (P := fun n => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ n).re)
      (Q := fun n => ∑' i, m i * (liTerm (v i) n).re < 0) (N₁ := N₁) (fun n hn hP => by
        have hd := hN₁ n hn
        rw [hf] at hP
        have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
        have := (abs_le.mp hd).2
        nlinarith) N
    have : (((Finset.range N).filter (fun n => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ n).re)).card : ℝ)
        ≤ (((Finset.range N).filter (fun n => ∑' i, m i * (liTerm (v i) n).re < 0)).card : ℝ) + N₁ := by
      exact_mod_cast hle
    linarith
  · have hle := card_filter_le_card_filter_add
      (P := fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε)
      (Q := fun n => 0 < ∑' i, m i * (liTerm (v i) n).re) (N₁ := N₁) (fun n hn hP => by
        have hd := hN₁ n hn
        rw [hf] at hP
        have hRn : (0 : ℝ) < R ^ n := pow_pos hR0 n
        have := (abs_le.mp hd).1
        nlinarith) N
    have : (((Finset.range N).filter (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ n).re < -ε)).card : ℝ)
        ≤ (((Finset.range N).filter (fun n => 0 < ∑' i, m i * (liTerm (v i) n).re)).card : ℝ) + N₁ := by
      exact_mod_cast hle
    linarith

/-- **Both signs in every long window, abstract form.** If one member of a non-real family lies
strictly outside the unit circle, there are `L` and `N₁` such that every window `[M, M + L)` with
`M ≥ N₁` contains an index where the paired Li sum is negative and one where it is positive. -/
theorem exists_window_re_tsum_liTerm_neg_and_pos
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ)) (hnr : ∀ i, (v i).im ≠ 0)
    {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ L N₁ : ℕ, ∀ a : ℕ, N₁ ≤ a →
      (∃ n, a ≤ n ∧ n < a + L ∧ ∑' i, m i * (liTerm (v i) n).re < 0) ∧
      (∃ n, a ≤ n ∧ n < a + L ∧ 0 < ∑' i, m i * (liTerm (v i) n).re) := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, hDnorm i i.2,
      div_self hR0.ne']
  have hu2 : ∀ i, u i ^ 2 ≠ 1 := by
    intro i h
    have him : (u i).im ≠ 0 := by
      rw [hudef]; simp only
      rw [Complex.div_ofReal_im]
      exact div_ne_zero (hnr i) hR0.ne'
    have : u i = 1 ∨ u i = -1 := by
      have h' : (u i - 1) * (u i + 1) = 0 := by ring_nf; rw [h]; ring
      rcases mul_eq_zero.mp h' with h1 | h1
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h1)
    rcases this with h1 | h1 <;> rw [h1] at him <;> simp at him
  obtain ⟨ε, c, K, hε, hc, hcount⟩ :=
    exists_card_filter_gt_and_lt_shift u (fun i => m i) hunit hu2 (fun i => by linarith [hm i])
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  obtain ⟨L, hL⟩ := exists_nat_gt (K / c)
  have hcL : 0 < c * L - K := by
    rw [div_lt_iff₀ hc] at hL; linarith
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re := by
    intro n
    exact Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  refine ⟨L, N₁, fun a ha => ⟨?_, ?_⟩⟩
  · have hpos := (hcount a L).1
    have hne : ((Finset.range L).filter
        (fun n => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (a + n)).re)).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < (((Finset.range L).filter
          (fun n => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (a + n)).re)).card : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨n, hn⟩ := hne
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨a + n, by omega, by omega, ?_⟩
    have hd := hN₁ (a + n) (by omega)
    have hP := hn.2
    rw [hf] at hP
    have hRn : (0 : ℝ) < R ^ (a + n) := pow_pos hR0 _
    have := (abs_le.mp hd).2
    nlinarith
  · have hneg := (hcount a L).2
    have hne : ((Finset.range L).filter
        (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ (a + n)).re < -ε)).Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < (((Finset.range L).filter
          (fun n => ∑ i : {x // x ∈ D}, m i * (u i ^ (a + n)).re < -ε)).card : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨n, hn⟩ := hne
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨a + n, by omega, by omega, ?_⟩
    have hd := hN₁ (a + n) (by omega)
    have hP := hn.2
    rw [hf] at hP
    have hRn : (0 : ℝ) < R ^ (a + n) := pow_pos hR0 _
    have := (abs_le.mp hd).1
    nlinarith

/-! ## The Xi divisor -/

/-- The Xi Cayley family satisfies the hypotheses of the abstract theorems, and off the critical
line one of its roots lies strictly outside the unit circle. -/
theorem xiLi_family_facts :
    ∃ M : ℝ, (∀ ρ : XiDivisorSupport, (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)) ∧
      (∀ ρ : XiDivisorSupport, 1 ≤ ‖xiRootV (ρ : ℂ)‖) ∧
      (∀ ρ : XiDivisorSupport, ‖xiRootV (ρ : ℂ)‖ ≤ M) ∧
      (Summable fun ρ : XiDivisorSupport =>
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)) ∧
      (∀ ρ : XiDivisorSupport, (xiRootV (ρ : ℂ)).im ≠ 0) ∧
      (¬ RiemannHypothesis → ∃ ρ₀ : XiDivisorSupport, 1 < ‖xiRootV (ρ₀ : ℂ)‖) := by
  obtain ⟨M, hM1, hMb⟩ := exists_bound_xiRootW
  have hne0 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 0 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hne1 : ∀ ρ : XiDivisorSupport, (ρ : ℂ) ≠ 1 := by
    intro ρ h
    have him := xi_divisor_support_im_ne_zero ρ
    rw [h] at him
    simp at him
  have hmult : ∀ ρ : XiDivisorSupport,
      (1 : ℝ) ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
    intro ρ
    have := xi_divisor_pos_on_support ρ
    exact_mod_cast this
  refine ⟨M, hmult, fun ρ => one_le_norm_xiRootV (hne0 ρ) (hne1 ρ), fun ρ => ?_, ?_, ?_, ?_⟩
  · rw [norm_xiRootV (hne0 ρ) (hne1 ρ)]
    exact hMb ρ
  · refine Summable.of_nonneg_of_le
      (fun ρ => by nlinarith [hmult ρ, sq_nonneg ‖xiRootV (ρ : ℂ) - 1‖])
      (fun ρ => ?_) (xi_zero_multiplicity_inv_sq_summable.mul_left (M ^ (2 : ℕ)))
    have hb := norm_xiRootV_sub_one_le (hne0 ρ) (hne1 ρ) hM1 (hMb ρ)
    have hw1 : ‖xiRootW (ρ : ℂ) - 1‖ = 1 / ‖(ρ : ℂ)‖ := norm_xiRootW_sub_one _
    rw [hw1] at hb
    have hnn : (0 : ℝ) ≤ ‖xiRootV (ρ : ℂ) - 1‖ := norm_nonneg _
    have hsq : ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
      have hM0 : (0 : ℝ) ≤ M := by linarith
      have hmul : (M * (1 / ‖(ρ : ℂ)‖)) ^ (2 : ℕ) = M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by
        rw [mul_pow, div_pow, one_pow]
      rw [← hmul]
      nlinarith [mul_nonneg hM0 (by positivity : (0 : ℝ) ≤ 1 / ‖(ρ : ℂ)‖)]
    calc ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * ‖xiRootV (ρ : ℂ) - 1‖ ^ (2 : ℕ)
        ≤ ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)
            * (M ^ (2 : ℕ) * (1 / ‖(ρ : ℂ)‖ ^ (2 : ℕ))) := by
          have := hmult ρ
          nlinarith
      _ = M ^ (2 : ℕ) * (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ)
            / ‖(ρ : ℂ)‖ ^ (2 : ℕ)) := by ring
  · intro ρ h
    have hw : (xiRootW (ρ : ℂ)).im ≠ 0 := by
      intro hw
      exact xi_divisor_support_im_ne_zero ρ (im_eq_zero_of_xiRootW_im_eq_zero (hne0 ρ) hw)
    apply hw
    unfold xiRootV at h
    split_ifs at h with hcase
    · exact h
    · rw [Complex.inv_im] at h
      have hn0 : Complex.normSq (xiRootW (ρ : ℂ)) ≠ 0 := by
        rw [Ne, Complex.normSq_eq_zero]
        exact xiRootW_ne_zero (hne0 ρ) (hne1 ρ)
      rcases div_eq_zero_iff.mp h with h1 | h1
      · exact neg_eq_zero.mp h1
      · exact absurd h1 hn0
  · intro hRH
    rw [riemannHypothesis_iff_xi_zero_re_eq_half] at hRH
    push Not at hRH
    obtain ⟨ρ₁, hρ₁zero, hρ₁re⟩ := hRH
    set ρ₀ : XiDivisorSupport := ⟨ρ₁, mem_xi_divisor_support_of_eq_zero hρ₁zero⟩ with hρ₀def
    refine ⟨ρ₀, ?_⟩
    have hnorm : ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ ≠ 1 := by
      intro hEq
      exact hρ₁re ((norm_xiRootW_eq_one_iff (hne0 ρ₀)).mp hEq)
    have hposw : 0 < ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ :=
      norm_pos_iff.mpr (xiRootW_ne_zero (hne0 ρ₀) (hne1 ρ₀))
    rw [norm_xiRootV (hne0 ρ₀) (hne1 ρ₀)]
    rcases lt_trichotomy ‖xiRootW ((ρ₀ : XiDivisorSupport) : ℂ)‖ 1 with hlt | heq | hgt
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      rw [one_lt_inv₀ hposw]
      exact hlt
    · exact absurd heq hnorm
    · exact lt_of_lt_of_le hgt (le_max_left _ _)

theorem re_xiLiPaired_eq_tsum_mult (n : ℕ) : (xiLiPaired n).re = ∑' ρ : XiDivisorSupport,
    ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) * (liTerm (xiRootV (ρ : ℂ)) n).re := by
  rw [xiLiPaired, Complex.re_tsum (summable_xiLiPairedTerm n)]
  refine tsum_congr fun ρ => ?_
  rw [xiLiPairedTerm, Complex.re_ofReal_mul, liTerm_xiRootV]

/-- **Off the critical line both signs of the paired Li coefficients have positive density.** If
the Riemann hypothesis fails, there are `c > 0` and `K` with at least `cN − K` indices `n < N` of
each sign of `Re 2λ_n`. -/
theorem exists_density_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ c K : ℝ, 0 < c ∧ ∀ N : ℕ,
      c * N - K ≤ (((Finset.range N).filter (fun n => (xiLiPaired n).re < 0)).card : ℝ) ∧
      c * N - K ≤ (((Finset.range N).filter (fun n => 0 < (xiLiPaired n).re)).card : ℝ) := by
  classical
  obtain ⟨M, hmult, hvnorm, hvM, hsum, hnr, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨c, K, hc, hcount⟩ :=
    exists_density_re_tsum_liTerm_neg_and_pos hmult hvnorm hvM hsum hnr hρ₀
  refine ⟨c, K, hc, fun N => ?_⟩
  simp_rw [re_xiLiPaired_eq_tsum_mult]
  exact hcount N

/-- **Off the critical line the negative Li indices have bounded gaps.** If the Riemann hypothesis
fails, there are `L` and `N₁` such that every window `[a, a + L)` with `a ≥ N₁` contains indices
with `Re 2λ_n < 0` and with `Re 2λ_n > 0`. -/
theorem exists_window_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ L N₁ : ℕ, ∀ a : ℕ, N₁ ≤ a →
      (∃ n, a ≤ n ∧ n < a + L ∧ (xiLiPaired n).re < 0) ∧
      (∃ n, a ≤ n ∧ n < a + L ∧ 0 < (xiLiPaired n).re) := by
  obtain ⟨M, hmult, hvnorm, hvM, hsum, hnr, hbad⟩ := xiLi_family_facts
  obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
  obtain ⟨L, N₁, hwin⟩ := exists_window_re_tsum_liTerm_neg_and_pos hmult hvnorm hvM hsum hnr hρ₀
  refine ⟨L, N₁, fun a ha => ?_⟩
  simp_rw [re_xiLiPaired_eq_tsum_mult]
  exact hwin a ha

/-- **Long runs criterion.** The Riemann hypothesis holds iff for every length `L` there are
arbitrarily late runs `[a, a + L)` of nonnegative paired Li coefficients. -/
theorem riemannHypothesis_iff_arbitrarily_late_nonneg_runs :
    RiemannHypothesis ↔ ∀ L a₀ : ℕ, ∃ a : ℕ, a₀ ≤ a ∧
      ∀ n, a ≤ n → n < a + L → 0 ≤ (xiLiPaired n).re := by
  constructor
  · intro hRH L a₀
    exact ⟨a₀, le_rfl, fun n _ _ => re_xiLiPaired_nonneg_of_rh hRH n⟩
  · intro h
    by_contra hRH
    obtain ⟨L, N₁, hwin⟩ := exists_window_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis hRH
    obtain ⟨a, ha, hrun⟩ := h L N₁
    obtain ⟨n, hn1, hn2, hneg⟩ := (hwin a ha).1
    exact absurd (hrun n hn1 hn2) (not_le.mpr hneg)

/-- **Li's criterion cannot fail on a sparse set.** If the negative indices
`{n < N : Re 2λ_n < 0}` have lower density zero, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_liminf_density_re_xiLiPaired_neg_zero
    (h : ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      (((Finset.range N).filter (fun n => (xiLiPaired n).re < 0)).card : ℝ) < ε * N) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨c, K, hc, hcount⟩ := exists_density_re_xiLiPaired_neg_and_pos_of_not_riemannHypothesis hRH
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * K / c)
  obtain ⟨N, hN, hlt⟩ := h (c / 2) (by linarith) N₀
  have h1 := (hcount N).1
  have hN' : 2 * K / c < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  have hNK : 2 * K < c * N := by
    rw [div_lt_iff₀ hc] at hN'; linarith
  linarith

/-- **Density form of Li's criterion.** The Riemann hypothesis holds iff the indices with
`Re 2λ_n < 0` have lower density zero; under RH the set is empty. -/
theorem riemannHypothesis_iff_liminf_density_re_xiLiPaired_neg_zero :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      (((Finset.range N).filter (fun n => (xiLiPaired n).re < 0)).card : ℝ) < ε * N := by
  refine ⟨fun hRH ε hε N₀ => ⟨N₀ + 1, by omega, ?_⟩,
    riemannHypothesis_of_liminf_density_re_xiLiPaired_neg_zero⟩
  have hempty : (Finset.range (N₀ + 1)).filter (fun n => (xiLiPaired n).re < 0) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro n _
    exact not_lt.mpr (re_xiLiPaired_nonneg_of_rh hRH n)
  rw [hempty, Finset.card_empty, Nat.cast_zero]
  positivity

end RHTower
