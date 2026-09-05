/-
# Small values of a Dirichlet polynomial on the critical line

For a unit-head bounded Dirichlet polynomial `Ψ = edPoly b s`, the corpus zero-free cofactor
factorization on a ball centred at `8 + it` (`exists_zero_free_cofactor_bounds`) and the
minimum-modulus lemma for zero-free functions (`norm_lower_bound_of_anchor`) give the interior
lower bound

  `log ‖Ψ(1/2+it)‖ ≥ −C + ∑_{zeros u near} m_u log ‖(1/2+it) − u‖`,

with `C` and the total multiplicity bounded by constants depending only on `b, s`. Squaring and
integrating over `t` (the zeros of the strip are `≪ T` in number) gives

  `∫_{T₁}^{T₂} (log⁻ ‖Ψ(1/2+it)‖)² dt ≤ C₁ (T₂ − T₁) + C₂`,

the uniform integrability of `log ‖Ψ‖` on the line that the lower torus law needs.
-/
import GaloisForLFunctions.HTGeometry.PolynomialMinimumModulus
import GaloisForLFunctions.RHTower.MinimumModulus
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

open Metric Complex Finset Set Filter Topology
open scoped Classical

namespace RHTower

noncomputable section

/-- Mass constant controlling `‖Ψ‖` on `Re z ≥ −19`. -/
def leftMass (b : ℕ → ℂ) (s : Finset ℕ) : ℝ := ∑ n ∈ s, ‖b n‖ * ((n : ℝ) ^ (19 : ℕ))

theorem norm_edPoly_le_leftMass (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) {z : ℂ}
    (hz : -19 ≤ z.re) : ‖edPoly b s z‖ ≤ leftMass b s := by
  unfold edPoly leftMass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos (hs n hn)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hs n hn
  have hre : (-z).re ≤ ((19 : ℕ) : ℝ) := by
    rw [Complex.neg_re]; push_cast; linarith
  have := Real.rpow_le_rpow_of_exponent_le hn1 hre
  rw [Real.rpow_natCast] at this
  exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

theorem one_le_leftMass (b : ℕ → ℂ) {s : Finset ℕ} (h1 : 1 ∈ s) (hb1 : b 1 = 1) :
    1 ≤ leftMass b s := by
  unfold leftMass
  have : ‖b 1‖ * ((1 : ℕ) : ℝ) ^ (19 : ℕ) = 1 := by rw [hb1]; simp
  rw [← this]
  exact Finset.single_le_sum (f := fun n : ℕ => ‖b n‖ * ((n : ℝ) ^ (19 : ℕ)))
    (fun n _ => by positivity) h1

/-- Zero data of an entire function on the ball `closedBall c₀ R`, translated to the origin:
the zeros with multiplicities, and a zero-free cofactor with explicit bounds. -/
structure BallZeroData (D : ℂ → ℂ) (c₀ : ℂ) (R R' Mf : ℝ) where
  T : Finset ℂ
  m : ℂ → ℕ
  g : ℂ → ℂ
  hg : AnalyticOnNhd ℂ g Set.univ
  hT : ∀ a ∈ T, ‖a‖ ≤ R ∧ 1 ≤ m a ∧ D (c₀ + a) = 0
  hg0 : ∀ z : ℂ, ‖z‖ ≤ R → g z ≠ 0
  hgb : ∀ z : ℂ, ‖z‖ ≤ R' → ‖g z‖ ≤ Mf / (R' - R) ^ (∑ a ∈ T, m a)
  hfac : ∀ z : ℂ, D (c₀ + z) = (∏ a ∈ T, (z - a) ^ m a) * g z

/-- An entire function that is not identically zero is nowhere locally zero. -/
theorem not_eventually_zero_of_entire {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D Set.univ)
    (hne : ∃ z : ℂ, D z ≠ 0) (a : ℂ) : ¬ ∀ᶠ z in 𝓝 a, D z = 0 := by
  intro h
  obtain ⟨z, hz⟩ := hne
  have := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a)
    (by simpa [Filter.EventuallyEq] using h) (Set.mem_univ z)
  exact hz this

/-- The corpus factorization, repackaged with the zeros filtered to positive multiplicity. -/
theorem exists_ballZeroData {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D Set.univ) (hne : ∃ z : ℂ, D z ≠ 0)
    (c₀ : ℂ) {R R' Mf : ℝ} (hR : 0 < R) (hRR' : R < R')
    (hMf : ∀ z : ℂ, ‖z - c₀‖ = R' → ‖D z‖ ≤ Mf) :
    Nonempty (BallZeroData D c₀ R R' Mf) := by
  set f : ℂ → ℂ := fun z => D (c₀ + z) with hf
  have hfan : AnalyticOnNhd ℂ f Set.univ := by
    intro z _
    have h1 : AnalyticAt ℂ D (c₀ + z) := hD _ (Set.mem_univ _)
    exact h1.comp_of_eq (analyticAt_const.add analyticAt_id) rfl
  have hfne : ∃ z : ℂ, f z ≠ 0 := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z - c₀, by simp [hf, hz]⟩
  have hnz : ∀ a ∈ (Set.univ : Set ℂ), ¬ ∀ᶠ z in 𝓝 a, f z = 0 :=
    fun a _ => not_eventually_zero_of_entire hfan hfne a
  have hMf' : ∀ z : ℂ, ‖z‖ = R' → ‖f z‖ ≤ Mf := by
    intro z hz
    apply hMf
    simpa using hz
  obtain ⟨T, m, g, hg, hTR, hg0, hgb, hfac⟩ :=
    GaloisForLFunctions.HTGeometry.exists_zero_free_cofactor_bounds (U := Set.univ) isOpen_univ hR hRR' (Set.subset_univ _)
      hfan hnz hMf'
  set T' : Finset ℂ := T.filter (fun a => m a ≠ 0) with hT'
  have hprod : ∀ z : ℂ, (∏ a ∈ T, (z - a) ^ m a) = ∏ a ∈ T', (z - a) ^ m a := by
    intro z
    rw [hT']
    symm
    apply Finset.prod_filter_of_ne
    intro a _ h
    intro h0
    apply h
    rw [h0, pow_zero]
  have hsum : (∑ a ∈ T, m a) = ∑ a ∈ T', m a := by
    rw [hT']
    symm
    apply Finset.sum_filter_of_ne
    intro a _ h h0
    exact h h0
  refine ⟨⟨T', m, g, hg, ?_, ?_, ?_, ?_⟩⟩
  · intro a ha0
    have ha : a ∈ T ∧ m a ≠ 0 := by
      have := ha0
      rw [hT', Finset.mem_filter] at this
      exact this
    refine ⟨hTR a ha.1, Nat.one_le_iff_ne_zero.mpr ha.2, ?_⟩
    have h := hfac a (Set.mem_univ a)
    rw [hf] at h
    simp only at h
    rw [h, hprod]
    have hz : (a - a) ^ m a = 0 := by rw [sub_self, zero_pow ha.2]
    rw [Finset.prod_eq_zero ha0 hz, zero_mul]
  · intro z hz
    exact hg0 z (Metric.mem_closedBall.mpr (by simpa using hz))
  · intro z hz
    rw [← hsum]
    exact hgb z hz
  · intro z
    have h := hfac z (Set.mem_univ z)
    rw [hf] at h
    simp only at h
    rw [h, hprod]

namespace BallZeroData

variable {D : ℂ → ℂ} {c₀ : ℂ} {R R' Mf : ℝ}

/-- Total multiplicity. -/
def N (Z : BallZeroData D c₀ R R' Mf) : ℕ := ∑ a ∈ Z.T, Z.m a

theorem card_le_N (Z : BallZeroData D c₀ R R' Mf) : Z.T.card ≤ Z.N := by
  unfold N
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun a ha => (Z.hT a ha).2.1

/-- The anchor: `‖g 0‖ ≥ ‖D c₀‖ / R^N`. -/
theorem anchor (Z : BallZeroData D c₀ R R' Mf) (hR : 0 < R) :
    ‖D c₀‖ ≤ R ^ Z.N * ‖Z.g 0‖ := by
  have h := Z.hfac 0
  rw [add_zero] at h
  rw [h, norm_mul, norm_prod]
  have hle : (∏ a ∈ Z.T, ‖((0 : ℂ) - a) ^ Z.m a‖) ≤ R ^ Z.N := by
    unfold N
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_le_prod (fun a _ => norm_nonneg _)
    intro a ha
    rw [norm_pow, zero_sub, norm_neg]
    exact pow_le_pow_left₀ (norm_nonneg _) (Z.hT a ha).1 _
  exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

/-- Multiplicity bound: `N log((R'−R)/R) ≤ log (Mf / ‖D c₀‖)`. -/
theorem N_mul_log_le (Z : BallZeroData D c₀ R R' Mf) (hR : 0 < R) (hRR' : R < R')
    (hanc : 0 < ‖D c₀‖) :
    (Z.N : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖D c₀‖) := by
  have hgap : 0 < R' - R := by linarith
  have h1 := Z.anchor hR
  have h2 := Z.hgb 0 (by simp; linarith)
  have hMf : 0 < Mf := by
    have : 0 < ‖Z.g 0‖ := norm_pos_iff.mpr (Z.hg0 0 (by simp; linarith))
    have h3 : 0 < R ^ Z.N * ‖Z.g 0‖ := by positivity
    have h4 : ‖Z.g 0‖ ≤ Mf / (R' - R) ^ (∑ a ∈ Z.T, Z.m a) := h2
    have : 0 < Mf / (R' - R) ^ (∑ a ∈ Z.T, Z.m a) := lt_of_lt_of_le this h4
    exact (div_pos_iff_of_pos_right (by positivity)).mp this
  have hN : (∑ a ∈ Z.T, Z.m a) = Z.N := rfl
  rw [hN] at h2
  -- ‖D c₀‖ ≤ R^N · Mf / (R'−R)^N
  have h3 : ‖D c₀‖ ≤ R ^ Z.N * (Mf / (R' - R) ^ Z.N) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have h4 : ((R' - R) / R) ^ Z.N ≤ Mf / ‖D c₀‖ := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hanc]
    have : R ^ Z.N * (Mf / (R' - R) ^ Z.N) * (R' - R) ^ Z.N = R ^ Z.N * Mf := by
      field_simp
    nlinarith [h3, this, pow_pos hgap Z.N, pow_pos hR Z.N]
  have h5 := Real.log_le_log (by positivity) h4
  rw [Real.log_pow] at h5
  exact h5

end BallZeroData

/-- **Interior lower bound.**  If `‖D c₀‖ ≥ 1/2` and `‖D‖ ≤ Mf` on `‖z − c₀‖ = 27`, then at every
`w` with `‖w − c₀‖ ≤ 15/2` and `D w ≠ 0`,
`−log ‖D w‖ ≤ C(Mf) + ∑_{a} m_a · max 0 (−log ‖(w − c₀) − a‖)` with `∑ m_a ≤ log(2 Mf)/log 2`. -/
theorem exists_interior_log_lower_bound {D : ℂ → ℂ} (hD : AnalyticOnNhd ℂ D Set.univ)
    (hne : ∃ z : ℂ, D z ≠ 0) (c₀ : ℂ) {Mf : ℝ} (hMf1 : 1 ≤ Mf)
    (hMf : ∀ z : ℂ, ‖z - c₀‖ = 27 → ‖D z‖ ≤ Mf) (hanc : 1 / 2 ≤ ‖D c₀‖) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ),
      (∀ a ∈ T, ‖a‖ ≤ 9 ∧ 1 ≤ m a ∧ D (c₀ + a) = 0) ∧
      (∀ u : ℂ, ‖u - c₀‖ ≤ 9 → D u = 0 → u - c₀ ∈ T) ∧
      (∑ a ∈ T, (m a : ℝ)) ≤ Real.log (2 * Mf) / Real.log 2 ∧
      ∀ w : ℂ, ‖w - c₀‖ ≤ 15 / 2 → D w ≠ 0 →
        -Real.log ‖D w‖ ≤ Real.log 2 + (Real.log (2 * Mf) / Real.log 2) * Real.log 9
            + 10 * Real.log (4 * Mf)
          + ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖(w - c₀) - a‖) := by
  obtain ⟨Z⟩ := exists_ballZeroData hD hne c₀ (R := 9) (R' := 27) (Mf := Mf) (by norm_num)
    (by norm_num) hMf
  have hanc0 : 0 < ‖D c₀‖ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogMf : 0 ≤ Real.log (2 * Mf) := Real.log_nonneg (by linarith)
  -- multiplicity bound
  have hN : (Z.N : ℝ) ≤ Real.log (2 * Mf) / Real.log 2 := by
    have h := Z.N_mul_log_le (by norm_num) (by norm_num) hanc0
    have h2 : Real.log ((27 - 9) / 9 : ℝ) = Real.log 2 := by norm_num
    rw [h2] at h
    have h3 : Real.log (Mf / ‖D c₀‖) ≤ Real.log (2 * Mf) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ hanc0]
      nlinarith
    rw [le_div_iff₀ hlog2]
    linarith
  have hNnat : (Z.N : ℝ) = ∑ a ∈ Z.T, (Z.m a : ℝ) := by
    unfold BallZeroData.N; push_cast; rfl
  have hzeros : ∀ u : ℂ, ‖u - c₀‖ ≤ 9 → D u = 0 → u - c₀ ∈ Z.T := by
    intro u hu hDu
    have h := Z.hfac (u - c₀)
    rw [show c₀ + (u - c₀) = u by ring, hDu] at h
    have hg := Z.hg0 (u - c₀) hu
    have hprod : (∏ a ∈ Z.T, (u - c₀ - a) ^ Z.m a) = 0 := by
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact h1
      · exact absurd h1 hg
    obtain ⟨a, ha, hfa⟩ := Finset.prod_eq_zero_iff.mp hprod
    have : u - c₀ - a = 0 := pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp (Z.hT a ha).2.1) |>.mp hfa
    rw [sub_eq_zero] at this
    rw [this]; exact ha
  refine ⟨Z.T, Z.m, Z.hT, hzeros, by rw [← hNnat]; exact hN, ?_⟩
  intro w hw hDw
  set z := w - c₀ with hz
  have hwz : w = c₀ + z := by rw [hz]; ring
  -- minimum modulus of the cofactor on the ball of radius 9 at radius 15/2
  set M : ℝ := 2 * Mf / 18 ^ Z.N with hM
  set m₀ : ℝ := (1 / 2) / 9 ^ Z.N with hm₀
  have hMpos : 0 < M := by rw [hM]; positivity
  have hm₀pos : 0 < m₀ := by rw [hm₀]; positivity
  have hsup : ∀ y ∈ ball (0 : ℂ) 9, ‖Z.g y‖ ≤ M := by
    intro y hy
    have h := Z.hgb y (by
      have := mem_ball_zero_iff.mp hy
      linarith)
    have hN' : (∑ a ∈ Z.T, Z.m a) = Z.N := rfl
    rw [hN'] at h
    rw [hM]
    calc ‖Z.g y‖ ≤ Mf / (27 - 9) ^ Z.N := h
      _ ≤ 2 * Mf / 18 ^ Z.N := by
          norm_num
          gcongr
          linarith
  have hanchor : m₀ ≤ ‖Z.g 0‖ := by
    have h := Z.anchor (by norm_num)
    rw [hm₀, div_le_iff₀ (by positivity)]
    linarith
  have hmM : m₀ < M := by
    rw [hm₀, hM]
    have h18 : (18 : ℝ) ^ Z.N = 2 ^ Z.N * 9 ^ Z.N := by rw [← mul_pow]; norm_num
    rw [h18, div_lt_div_iff₀ (by positivity) (by positivity)]
    -- (1/2) · 2^N · 9^N < 2 Mf · 9^N  ⟸  2^N ≤ 2 Mf
    have h2N : (2 : ℝ) ^ Z.N ≤ 2 * Mf := by
      have h := hN
      rw [le_div_iff₀ hlog2] at h
      have := Real.exp_le_exp.mpr h
      rw [Real.exp_log (by linarith)] at this
      have h3 : Real.exp ((Z.N : ℝ) * Real.log 2) = 2 ^ Z.N := by
        rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
      rw [h3] at this
      exact this
    have h9 : (0 : ℝ) < 9 ^ Z.N := by positivity
    nlinarith [h2N, h9, hMf1]
  have hg0' : ∀ y ∈ ball (0 : ℂ) 9, Z.g y ≠ 0 := fun y hy =>
    Z.hg0 y (by have := mem_ball_zero_iff.mp hy; linarith)
  have hgan : AnalyticOnNhd ℂ Z.g (ball (0 : ℂ) 9) := fun y _ => Z.hg y (Set.mem_univ y)
  have hlow := norm_lower_bound_of_anchor (c := (0 : ℂ)) (R := 9) (r := 15 / 2) (M := M)
    (m := m₀) (by norm_num) (by norm_num) hgan hg0' hsup hm₀pos hmM hanchor z
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hw)
  -- log ‖g z‖ ≥ log m₀ − 10 log(M/m₀)
  have hexp : (15 / 2 : ℝ) / (9 - 15 / 2) = 5 := by norm_num
  have hlow' : Real.log m₀ - 10 * Real.log (M / m₀) ≤ Real.log ‖Z.g z‖ := by
    have hgz : 0 < ‖Z.g z‖ := norm_pos_iff.mpr (Z.hg0 z (by rw [hz]; linarith))
    have h1 := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul hm₀pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 : -(2 * Real.log (M / m₀) * (15 / 2) / (9 - 15 / 2)) = -10 * Real.log (M / m₀) := by
      norm_num; ring
    rw [h2] at h1
    linarith
  have hMm : Real.log (M / m₀) ≤ Real.log (4 * Mf) := by
    apply Real.log_le_log (by positivity)
    have h18 : (18 : ℝ) ^ Z.N = 2 ^ Z.N * 9 ^ Z.N := by rw [← mul_pow]; norm_num
    have hratio : M / m₀ = 4 * Mf / 2 ^ Z.N := by
      rw [hM, hm₀, h18]
      field_simp
      ring
    rw [hratio]
    have h2 : (1 : ℝ) ≤ 2 ^ Z.N := one_le_pow₀ (by norm_num)
    exact div_le_self (by positivity) h2
  have hlogm₀ : Real.log m₀ = -Real.log 2 - (Z.N : ℝ) * Real.log 9 := by
    rw [hm₀, Real.log_div (by norm_num) (by positivity), Real.log_pow]
    have : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [this]
  -- decompose log ‖D w‖
  have hfac := Z.hfac z
  rw [← hwz] at hfac
  have hprod_ne : (∏ a ∈ Z.T, (z - a) ^ Z.m a) ≠ 0 := by
    intro h0
    apply hDw
    rw [hfac, h0, zero_mul]
  have hgz_ne : Z.g z ≠ 0 := Z.hg0 z (by rw [hz]; linarith)
  have hlogD : Real.log ‖D w‖ =
      (∑ a ∈ Z.T, (Z.m a : ℝ) * Real.log ‖z - a‖) + Real.log ‖Z.g z‖ := by
    rw [hfac, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hprod_ne) (norm_ne_zero_iff.mpr hgz_ne),
      norm_prod, Real.log_prod (fun a ha => ?_)]
    · congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [norm_pow, Real.log_pow]
    · rw [norm_ne_zero_iff]
      exact Finset.prod_ne_zero_iff.mp hprod_ne a ha
  have hterm : ∀ a ∈ Z.T, -((Z.m a : ℝ) * Real.log ‖z - a‖) ≤
      (Z.m a : ℝ) * max 0 (-Real.log ‖z - a‖) := by
    intro a _
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
  have hsumterm : -(∑ a ∈ Z.T, (Z.m a : ℝ) * Real.log ‖z - a‖) ≤
      ∑ a ∈ Z.T, (Z.m a : ℝ) * max 0 (-Real.log ‖z - a‖) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum hterm
  have hN9 : (Z.N : ℝ) * Real.log 9 ≤ (Real.log (2 * Mf) / Real.log 2) * Real.log 9 :=
    mul_le_mul_of_nonneg_right hN (Real.log_nonneg (by norm_num))
  rw [hlogD]
  linarith [hlow', hMm, hlogm₀, hsumterm, hN9]


/-! ## Exponential type and the strip zero count -/

/-- `‖Ψ z‖ ≤ (∑ ‖b n‖) · exp(log N · ‖z‖)` for `s ⊆ Icc 1 N`. -/
theorem norm_edPoly_le_expType (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) {N : ℕ}
    (hsN : ∀ n ∈ s, n ≤ N) (z : ℂ) :
    ‖edPoly b s z‖ ≤ (∑ n ∈ s, ‖b n‖) * Real.exp (Real.log N * ‖z‖) := by
  unfold edPoly
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul, Complex.ofReal_natCast, Complex.norm_natCast_cpow_of_pos (hs n hn)]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hs n hn
  have hnN : (n : ℝ) ≤ N := by exact_mod_cast hsN n hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hre : (-z).re ≤ ‖z‖ := by
    rw [Complex.neg_re]
    have := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  have h1 : (n : ℝ) ^ (-z).re ≤ (n : ℝ) ^ ‖z‖ := Real.rpow_le_rpow_of_exponent_le hn1 hre
  have h2 : (n : ℝ) ^ ‖z‖ = Real.exp (Real.log n * ‖z‖) := by
    rw [Real.rpow_def_of_pos (by linarith)]
  have h3 : Real.exp (Real.log n * ‖z‖) ≤ Real.exp (Real.log N * ‖z‖) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hlogN (norm_nonneg _)
  calc ‖b n‖ * (n : ℝ) ^ (-z).re ≤ ‖b n‖ * Real.exp (Real.log N * ‖z‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [← h2] at h3
        exact h1.trans h3

/-- The window strip `[-1, 17] × [T₁ - 9, T₂ + 9]`. -/
def windowStrip (T₁ T₂ : ℝ) : Set ℂ :=
  Set.uIcc ((((-1 : ℝ) : ℂ) + ((T₁ - 9 : ℝ) : ℂ) * I)).re
      ((((17 : ℝ) : ℂ) + ((T₂ + 9 : ℝ) : ℂ) * I)).re ×ℂ
    Set.uIcc ((((-1 : ℝ) : ℂ) + ((T₁ - 9 : ℝ) : ℂ) * I)).im
      ((((17 : ℝ) : ℂ) + ((T₂ + 9 : ℝ) : ℂ) * I)).im

theorem mem_windowStrip {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) {u : ℂ} :
    u ∈ windowStrip T₁ T₂ ↔ (-1 ≤ u.re ∧ u.re ≤ 17) ∧ (T₁ - 9 ≤ u.im ∧ u.im ≤ T₂ + 9) := by
  unfold windowStrip
  rw [Complex.mem_reProdIm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_mul,
    zero_add]
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 17), Set.uIcc_of_le (by linarith : T₁ - 9 ≤ T₂ + 9)]
  simp only [Set.mem_Icc]

/-- The finite set of zeros of `Ψ` in the window strip. -/
def windowStripZeros (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly b s z ≠ 0) (T₁ T₂ : ℝ) : Finset ℂ :=
  (entire_zeros_closedRectangle_finite (analyticOnNhd_edPoly b hs) hne
    (((-1 : ℝ) : ℂ) + ((T₁ - 9 : ℝ) : ℂ) * I) (((17 : ℝ) : ℂ) + ((T₂ + 9 : ℝ) : ℂ) * I)).toFinset

theorem mem_windowStripZeros (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly b s z ≠ 0) {T₁ T₂ : ℝ} {u : ℂ} :
    u ∈ windowStripZeros b hs hne T₁ T₂ ↔ u ∈ windowStrip T₁ T₂ ∧ edPoly b s u = 0 := by
  unfold windowStripZeros windowStrip
  rw [Set.Finite.mem_toFinset]
  rfl

/-- **Linear strip zero count**: `#windowStripZeros ≤ K (1 + 27 + |T₁| + |T₂|)`. -/
theorem exists_windowStripZeros_card_le (b : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (hne : ∃ z : ℂ, edPoly b (Finset.Icc 1 N) z ≠ 0) (T₁ T₂ : ℝ), T₁ ≤ T₂ →
      ((windowStripZeros b (fun n hn => (Finset.mem_Icc.mp hn).1) hne T₁ T₂).card : ℝ)
        ≤ K * (1 + (27 + |T₁| + |T₂|)) := by
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsN : ∀ n ∈ s, n ≤ N := fun n hn => (Finset.mem_Icc.mp hn).2
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hdiff : Differentiable ℂ (edPoly b s) := differentiable_edPoly b hs
  have hanc : edPoly b s (8 : ℂ) ≠ 0 := by
    intro h0
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (8 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  have hC1 : 1 ≤ ∑ n ∈ s, ‖b n‖ := by
    have : ‖b 1‖ = 1 := by rw [hb1]; simp
    rw [← this]
    exact Finset.single_le_sum (f := fun n => ‖b n‖) (fun n _ => norm_nonneg _) h1
  have hA : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  obtain ⟨K, hK, hbound⟩ := exponentialType_zeroCount_linear hdiff hanc hA hC1
    (norm_edPoly_le_expType b hs hsN)
  refine ⟨K, hK, ?_⟩
  intro hne T₁ T₂ hT
  set Z := windowStripZeros b hs hne T₁ T₂ with hZ
  set r : ℝ := 27 + |T₁| + |T₂| with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith [abs_nonneg T₁, abs_nonneg T₂]
  have hball : ∀ u ∈ Z, u ∈ closedBall (8 : ℂ) r := by
    intro u hu
    rw [hZ, mem_windowStripZeros b hs hne, mem_windowStrip hT] at hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hre : |(u - 8).re| ≤ 9 := by
      simp only [Complex.sub_re]
      norm_num
      rw [abs_le]; constructor <;> linarith [hu.1.1.1, hu.1.1.2]
    have him : |(u - 8).im| ≤ 9 + |T₁| + |T₂| := by
      simp only [Complex.sub_im]
      norm_num
      rw [abs_le]
      constructor <;> linarith [hu.1.2.1, hu.1.2.2, le_abs_self T₁, neg_abs_le T₁,
        le_abs_self T₂, neg_abs_le T₂]
    calc ‖u - 8‖ ≤ |(u - 8).re| + |(u - 8).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 9 + (9 + |T₁| + |T₂|) := add_le_add hre him
      _ ≤ r := by rw [hr]; linarith
  have hzero : ∀ u ∈ Z, edPoly b s u = 0 := by
    intro u hu
    rw [hZ, mem_windowStripZeros b hs hne] at hu
    exact hu.2
  have hcard := card_le_sum_divisor_of_finite_zeros hdiff hanc Z id
    (fun x _ y _ h => h) hball hzero
  have hlin := hbound r hr1
  have hcardR : (Z.card : ℝ) ≤ ((∑ᶠ u, (MeromorphicOn.divisor (edPoly b s) (closedBall 8 r)) u : ℤ) : ℝ) := by
    exact_mod_cast hcard
  linarith


/-! ## The pointwise square bound on a window -/

/-- Total multiplicity bound of the zeros in the ball of radius `9` around `8 + it`. -/
def mollNmax (b : ℕ → ℂ) (s : Finset ℕ) : ℝ := Real.log (2 * leftMass b s) / Real.log 2

/-- The interior constant. -/
def mollC₀ (b : ℕ → ℂ) (s : Finset ℕ) : ℝ :=
  Real.log 2 + mollNmax b s * Real.log 9 + 10 * Real.log (4 * leftMass b s)

theorem mollNmax_nonneg (b : ℕ → ℂ) {s : Finset ℕ} (h1 : 1 ∈ s) (hb1 : b 1 = 1) :
    0 ≤ mollNmax b s := by
  unfold mollNmax
  have := one_le_leftMass b h1 hb1
  exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))

theorem mollC₀_nonneg (b : ℕ → ℂ) {s : Finset ℕ} (h1 : 1 ∈ s) (hb1 : b 1 = 1) :
    0 ≤ mollC₀ b s := by
  unfold mollC₀
  have := one_le_leftMass b h1 hb1
  have h2 := mollNmax_nonneg b h1 hb1
  have h9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log (4 * leftMass b s) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- The negative log-modulus at height `t`. -/
def lineLogNeg (b : ℕ → ℂ) (s : Finset ℕ) (t : ℝ) : ℝ :=
  max 0 (-Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)

/-- The zero contribution at height `t` from a zero `u`. -/
def zeroLogNeg (u : ℂ) (t : ℝ) : ℝ := max 0 (-Real.log ‖(((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) - u‖)

theorem zeroLogNeg_nonneg (u : ℂ) (t : ℝ) : 0 ≤ zeroLogNeg u t := le_max_left _ _

/-- **Pointwise square bound on the window.** -/
theorem lineLogNeg_sq_le (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (h1 : 1 ∈ s)
    (hb1 : b 1 = 1) (hbn : ∀ n ∈ s, ‖b n‖ ≤ 1) (hne : ∃ z : ℂ, edPoly b s z ≠ 0)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) {t : ℝ} (ht : t ∈ Set.Icc T₁ T₂) :
    lineLogNeg b s t ^ 2 ≤ 2 * mollC₀ b s ^ 2 + 2 * mollNmax b s ^ 3 *
      ∑ u ∈ windowStripZeros b hs hne T₁ T₂, zeroLogNeg u t ^ 2 := by
  set Ψ := edPoly b s with hΨ
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hw
  set c₀ : ℂ := (8 : ℂ) + (t : ℂ) * I with hc₀
  set Z := windowStripZeros b hs hne T₁ T₂ with hZ
  have hMf1 := one_le_leftMass b h1 hb1
  have hNmax0 := mollNmax_nonneg b h1 hb1
  have hC₀0 := mollC₀_nonneg b h1 hb1
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hMf : ∀ z : ℂ, ‖z - c₀‖ = 27 → ‖Ψ z‖ ≤ leftMass b s := by
    intro z hz
    apply norm_edPoly_le_leftMass b hs
    have hre : |(z - c₀).re| ≤ 27 := by
      rw [← hz]; exact Complex.abs_re_le_norm _
    have hc₀re : c₀.re = 8 := by rw [hc₀]; simp
    rw [Complex.sub_re, hc₀re, abs_le] at hre
    linarith [hre.1]
  have hanc : 1 / 2 ≤ ‖Ψ c₀‖ := by
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := c₀)
      (by rw [hc₀]; simp; norm_num)
    have := norm_sub_norm_le (1 : ℂ) (Ψ c₀)
    rw [norm_one, norm_sub_rev] at this
    linarith
  obtain ⟨T, m, hTa, hzeros, hsum, hbound⟩ :=
    exists_interior_log_lower_bound hΨan hne c₀ hMf1 hMf hanc
  have hwc : w - c₀ = ((-15 / 2 : ℝ) : ℂ) := by
    rw [hw, hc₀]; push_cast; ring
  have hwc_norm : ‖w - c₀‖ = 15 / 2 := by
    rw [hwc, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hNmax_eq : Real.log (2 * leftMass b s) / Real.log 2 = mollNmax b s := rfl
  rw [hNmax_eq] at hsum hbound
  -- the zero sum
  set S : ℝ := ∑ u ∈ Z, zeroLogNeg u t with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun u _ => zeroLogNeg_nonneg u t
  have hTcard : (T.card : ℝ) ≤ mollNmax b s := by
    calc (T.card : ℝ) = ∑ a ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ a ∈ T, (m a : ℝ) := Finset.sum_le_sum fun a ha => by exact_mod_cast (hTa a ha).2.1
      _ ≤ mollNmax b s := hsum
  -- image of T in the strip
  have himage : T.image (fun a => c₀ + a) ⊆ Z := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    rw [hZ, mem_windowStripZeros b hs hne, mem_windowStrip hT]
    obtain ⟨ha9, _, hzero⟩ := hTa a ha
    have hre : |a.re| ≤ 9 := (Complex.abs_re_le_norm a).trans ha9
    have him : |a.im| ≤ 9 := (Complex.abs_im_le_norm a).trans ha9
    rw [abs_le] at hre him
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hzero⟩
    · rw [Complex.add_re, hc₀]; simp; linarith [hre.1]
    · rw [Complex.add_re, hc₀]; simp; linarith [hre.2]
    · rw [Complex.add_im, hc₀]; simp; linarith [him.1, ht.1]
    · rw [Complex.add_im, hc₀]; simp; linarith [him.2, ht.2]
  have hinj : Set.InjOn (fun a : ℂ => c₀ + a) (T : Set ℂ) := fun x _ y _ h => by
    simpa using h
  -- Claim 1: lineLogNeg ≤ C₀ + Nmax · S
  have hclaim1 : lineLogNeg b s t ≤ mollC₀ b s + mollNmax b s * S := by
    unfold lineLogNeg
    rw [← hw, ← hΨ]
    apply max_le (by positivity)
    by_cases hΨw : Ψ w = 0
    · rw [hΨw, norm_zero, Real.log_zero, neg_zero]; positivity
    · have h := hbound w (by rw [hwc_norm]) hΨw
      have hterm : ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖(w - c₀) - a‖)
          ≤ mollNmax b s * ∑ a ∈ T, zeroLogNeg (c₀ + a) t := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro a ha
        have hma : (m a : ℝ) ≤ mollNmax b s := by
          calc (m a : ℝ) ≤ ∑ a' ∈ T, (m a' : ℝ) :=
                Finset.single_le_sum (f := fun a' => (m a' : ℝ)) (fun _ _ => by positivity) ha
            _ ≤ mollNmax b s := hsum
        have heq : ‖(w - c₀) - a‖ = ‖w - (c₀ + a)‖ := by ring_nf
        unfold zeroLogNeg
        rw [← hw, heq]
        exact mul_le_mul_of_nonneg_right hma (le_max_left _ _)
      have himg : ∑ a ∈ T, zeroLogNeg (c₀ + a) t ≤ S := by
        have hre : ∑ a ∈ T, zeroLogNeg (c₀ + a) t
            = ∑ u ∈ T.image (fun a => c₀ + a), zeroLogNeg u t :=
          (Finset.sum_image (f := fun u => zeroLogNeg u t) (g := fun a => c₀ + a) hinj).symm
        rw [hS, hre]
        exact Finset.sum_le_sum_of_subset_of_nonneg himage (fun u _ _ => zeroLogNeg_nonneg u t)
      have hC₀ : Real.log 2 + mollNmax b s * Real.log 9 + 10 * Real.log (4 * leftMass b s)
          = mollC₀ b s := rfl
      rw [hC₀] at h
      calc -Real.log ‖Ψ w‖ ≤ mollC₀ b s + ∑ a ∈ T, (m a : ℝ) * max 0 (-Real.log ‖(w - c₀) - a‖) := h
        _ ≤ mollC₀ b s + mollNmax b s * ∑ a ∈ T, zeroLogNeg (c₀ + a) t := by linarith
        _ ≤ mollC₀ b s + mollNmax b s * S := by
            have := mul_le_mul_of_nonneg_left himg hNmax0
            linarith
  -- Claim 2: S² ≤ Nmax · ∑ zeroLogNeg²
  have hclaim2 : S ^ 2 ≤ mollNmax b s * ∑ u ∈ Z, zeroLogNeg u t ^ 2 := by
    set F := Z.filter (fun u => zeroLogNeg u t ≠ 0) with hF
    have hSF : S = ∑ u ∈ F, zeroLogNeg u t := by
      rw [hS, hF, Finset.sum_filter_ne_zero]
    have hFsub : ∀ u ∈ F, u - c₀ ∈ T := by
      intro u hu
      rw [hF, Finset.mem_filter] at hu
      obtain ⟨huZ, hune⟩ := hu
      rw [hZ, mem_windowStripZeros b hs hne] at huZ
      have hlt : ‖w - u‖ < 1 := by
        unfold zeroLogNeg at hune
        rw [← hw] at hune
        by_contra hge
        push_neg at hge
        apply hune
        have : 0 ≤ Real.log ‖w - u‖ := Real.log_nonneg hge
        rw [max_eq_left (by linarith)]
      apply hzeros u _ huZ.2
      calc ‖u - c₀‖ = ‖(u - w) + (w - c₀)‖ := by ring_nf
        _ ≤ ‖u - w‖ + ‖w - c₀‖ := norm_add_le _ _
        _ ≤ 9 := by rw [norm_sub_rev, hwc_norm]; linarith
    have hFcard : (F.card : ℝ) ≤ mollNmax b s := by
      have hinj' : Set.InjOn (fun u : ℂ => u - c₀) (F : Set ℂ) := fun x _ y _ h => by
        simpa using h
      have : F.card = (F.image (fun u => u - c₀)).card := (Finset.card_image_of_injOn hinj').symm
      rw [this]
      have hsub : F.image (fun u => u - c₀) ⊆ T := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        exact hFsub u hu
      calc ((F.image (fun u => u - c₀)).card : ℝ) ≤ (T.card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ mollNmax b s := hTcard
    have hcs := sq_sum_le_card_mul_sum_sq (s := F) (f := fun u => zeroLogNeg u t)
    rw [hSF]
    calc (∑ u ∈ F, zeroLogNeg u t) ^ 2 ≤ F.card * ∑ u ∈ F, zeroLogNeg u t ^ 2 := hcs
      _ ≤ mollNmax b s * ∑ u ∈ Z, zeroLogNeg u t ^ 2 := by
          apply mul_le_mul hFcard ?_ (by positivity) hNmax0
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro u _ _
          positivity
  -- combine
  have hA0 : 0 ≤ lineLogNeg b s t := le_max_left _ _
  calc lineLogNeg b s t ^ 2 ≤ (mollC₀ b s + mollNmax b s * S) ^ 2 :=
        pow_le_pow_left₀ hA0 hclaim1 2
    _ ≤ 2 * mollC₀ b s ^ 2 + 2 * (mollNmax b s * S) ^ 2 := by nlinarith [sq_nonneg (mollC₀ b s - mollNmax b s * S)]
    _ = 2 * mollC₀ b s ^ 2 + 2 * mollNmax b s ^ 2 * S ^ 2 := by ring
    _ ≤ 2 * mollC₀ b s ^ 2 + 2 * mollNmax b s ^ 2 * (mollNmax b s * ∑ u ∈ Z, zeroLogNeg u t ^ 2) := by
        gcongr
    _ = 2 * mollC₀ b s ^ 2 + 2 * mollNmax b s ^ 3 * ∑ u ∈ Z, zeroLogNeg u t ^ 2 := by ring


/-! ## The `rpow` majorant of a zero term -/

theorem rpow_neg_half_nonneg (x : ℝ) : 0 ≤ x ^ (-(1 / 2 : ℝ)) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.rpow_def_of_neg hx]
    have : Real.cos (-(1 / 2 : ℝ) * Real.pi) = 0 := by
      rw [show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
    rw [this, mul_zero]
  · rw [hx, Real.zero_rpow (by norm_num)]
  · exact Real.rpow_nonneg hx.le _

/-- The integrable majorant `16 · 1_{|t−c|<1} · (|t−c|^{-1/2})`, written with two one-sided `rpow`s. -/
def rpowMajorant (c t : ℝ) : ℝ :=
  Set.indicator (Set.Ioo (c - 1) (c + 1))
    (fun t => 16 * ((t - c) ^ (-(1 / 2 : ℝ)) + (c - t) ^ (-(1 / 2 : ℝ)))) t

theorem rpowMajorant_nonneg (c t : ℝ) : 0 ≤ rpowMajorant c t := by
  unfold rpowMajorant
  apply Set.indicator_nonneg
  intro t _
  have := rpow_neg_half_nonneg (t - c)
  have := rpow_neg_half_nonneg (c - t)
  positivity

/-- Squared log-distance bound: `(log(1/x))² ≤ 16 x^{-1/2}` for `0 < x`. -/
theorem sq_log_inv_le (x : ℝ) (hx : 0 < x) :
    (max 0 (-Real.log x)) ^ 2 ≤ 16 * x ^ (-(1 / 2 : ℝ)) := by
  have hinv : 0 ≤ x⁻¹ := by positivity
  have h1 : -Real.log x = Real.log x⁻¹ := by rw [Real.log_inv]
  have h2 : Real.log x⁻¹ ≤ (x⁻¹) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div hinv (by norm_num)
  have h3 : (x⁻¹) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (x⁻¹) ^ (1 / 4 : ℝ) := by ring
  have hpos : 0 ≤ 4 * (x⁻¹) ^ (1 / 4 : ℝ) := by positivity
  have hmax : max 0 (-Real.log x) ≤ 4 * (x⁻¹) ^ (1 / 4 : ℝ) := by
    apply max_le hpos
    rw [h1]; linarith
  have hsq : (4 * (x⁻¹) ^ (1 / 4 : ℝ)) ^ 2 = 16 * x ^ (-(1 / 2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast ((x⁻¹) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hinv,
      Real.inv_rpow hx.le, ← Real.rpow_neg hx.le]
    norm_num
  rw [← hsq]
  exact pow_le_pow_left₀ (le_max_left _ _) hmax 2

/-- Off the height of the zero, the squared zero term is dominated by the majorant. -/
theorem zeroLogNeg_sq_le_rpowMajorant (u : ℂ) {t : ℝ} (ht : t ≠ u.im) :
    zeroLogNeg u t ^ 2 ≤ rpowMajorant u.im t := by
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I with hw
  have him : |t - u.im| ≤ ‖w - u‖ := by
    have : (w - u).im = t - u.im := by rw [hw]; simp
    rw [← this]
    exact Complex.abs_im_le_norm _
  have hx : 0 < |t - u.im| := abs_pos.mpr (sub_ne_zero.mpr ht)
  by_cases hlt : |t - u.im| < 1
  · have hmem : t ∈ Set.Ioo (u.im - 1) (u.im + 1) := by
      rw [abs_lt] at hlt; constructor <;> linarith [hlt.1, hlt.2]
    unfold rpowMajorant
    rw [Set.indicator_of_mem hmem]
    -- one of the one-sided rpow's is |t − c|^{-1/2}
    have hone : |t - u.im| ^ (-(1 / 2 : ℝ)) ≤
        (t - u.im) ^ (-(1 / 2 : ℝ)) + (u.im - t) ^ (-(1 / 2 : ℝ)) := by
      rcases lt_or_gt_of_ne ht with h | h
      · rw [abs_of_neg (by linarith), show -(t - u.im) = u.im - t by ring]
        linarith [rpow_neg_half_nonneg (t - u.im)]
      · rw [abs_of_pos (by linarith)]
        linarith [rpow_neg_half_nonneg (u.im - t)]
    have hmono : zeroLogNeg u t ≤ max 0 (-Real.log |t - u.im|) := by
      unfold zeroLogNeg
      rw [← hw]
      apply max_le_max le_rfl
      have := Real.log_le_log hx him
      linarith
    have h0 : 0 ≤ zeroLogNeg u t := zeroLogNeg_nonneg u t
    calc zeroLogNeg u t ^ 2 ≤ (max 0 (-Real.log |t - u.im|)) ^ 2 := pow_le_pow_left₀ h0 hmono 2
      _ ≤ 16 * |t - u.im| ^ (-(1 / 2 : ℝ)) := sq_log_inv_le _ hx
      _ ≤ 16 * ((t - u.im) ^ (-(1 / 2 : ℝ)) + (u.im - t) ^ (-(1 / 2 : ℝ))) := by gcongr
  · push_neg at hlt
    have hz : zeroLogNeg u t = 0 := by
      unfold zeroLogNeg
      rw [← hw]
      have : 0 ≤ Real.log ‖w - u‖ := Real.log_nonneg (hlt.trans him)
      rw [max_eq_left (by linarith)]
    rw [hz]
    simpa using rpowMajorant_nonneg u.im t

theorem intervalIntegrable_sub_rpow (c : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t - c) ^ (-(1 / 2 : ℝ))) MeasureTheory.volume (c - 1) (c + 1) := by
  have := (intervalIntegral.intervalIntegrable_rpow' (a := -1) (b := 1)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_right c
  rw [show (-1 : ℝ) + c = c - 1 by ring, show (1 : ℝ) + c = c + 1 by ring] at this
  exact this

theorem intervalIntegrable_rsub_rpow (c : ℝ) :
    IntervalIntegrable (fun t : ℝ => (c - t) ^ (-(1 / 2 : ℝ))) MeasureTheory.volume (c - 1) (c + 1) := by
  have := ((intervalIntegral.intervalIntegrable_rpow' (a := -1) (b := 1)
    (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left c).symm
  rw [show c - (-1 : ℝ) = c + 1 by ring] at this
  exact this

theorem intervalIntegrable_rpowMajorant (c a b : ℝ) :
    IntervalIntegrable (rpowMajorant c) MeasureTheory.volume a b := by
  have h1 := intervalIntegrable_sub_rpow c
  have h2 := intervalIntegrable_rsub_rpow c
  have hg : IntervalIntegrable
      (fun t : ℝ => 16 * ((t - c) ^ (-(1 / 2 : ℝ)) + (c - t) ^ (-(1 / 2 : ℝ))))
      MeasureTheory.volume (c - 1) (c + 1) := (h1.add h2).const_mul 16
  have hIoo : MeasureTheory.IntegrableOn
      (fun t : ℝ => 16 * ((t - c) ^ (-(1 / 2 : ℝ)) + (c - t) ^ (-(1 / 2 : ℝ))))
      (Set.Ioo (c - 1) (c + 1)) := by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : c - 1 ≤ c + 1)).mp hg
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hind : MeasureTheory.Integrable (rpowMajorant c) := by
    unfold rpowMajorant
    exact hIoo.integrable_indicator measurableSet_Ioo
  exact hind.intervalIntegrable

theorem integral_rpow_neg_half_symm : ∫ x in (-1 : ℝ)..1, x ^ (-(1 / 2 : ℝ)) = 2 := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have hneg : (-1 : ℝ) ^ (-(1 / 2 : ℝ) + 1) = 0 := by
    rw [Real.rpow_def_of_neg (by norm_num)]
    have : Real.cos ((-(1 / 2 : ℝ) + 1) * Real.pi) = 0 := by
      rw [show (-(1 / 2 : ℝ) + 1) * Real.pi = Real.pi / 2 by ring, Real.cos_pi_div_two]
    rw [this, mul_zero]
  rw [hneg, Real.one_rpow]
  norm_num

theorem integral_rpowMajorant_le (c a b : ℝ) (hab : a ≤ b) :
    ∫ t in a..b, rpowMajorant c t ≤ 64 := by
  have hint : MeasureTheory.Integrable (rpowMajorant c) := by
    have := intervalIntegrable_rpowMajorant c (c - 1) (c + 1)
    -- integrability on ℝ: the majorant is an indicator of an integrable-on-Ioo function
    have h1 := intervalIntegrable_sub_rpow c
    have h2 := intervalIntegrable_rsub_rpow c
    have hg := (h1.add h2).const_mul 16
    have hIoo := ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by linarith : c - 1 ≤ c + 1)).mp hg).mono_set Set.Ioo_subset_Ioc_self
    unfold rpowMajorant
    exact hIoo.integrable_indicator measurableSet_Ioo
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ t in Set.Ioc a b, rpowMajorant c t
      ≤ ∫ t, rpowMajorant c t := by
        apply MeasureTheory.setIntegral_le_integral hint
        filter_upwards with t
        exact rpowMajorant_nonneg c t
    _ = ∫ t in Set.Ioo (c - 1) (c + 1),
          16 * ((t - c) ^ (-(1 / 2 : ℝ)) + (c - t) ^ (-(1 / 2 : ℝ))) := by
        unfold rpowMajorant
        rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    _ = ∫ t in (c - 1)..(c + 1),
          16 * ((t - c) ^ (-(1 / 2 : ℝ)) + (c - t) ^ (-(1 / 2 : ℝ))) := by
        rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = 64 := by
        have h1 := intervalIntegrable_sub_rpow c
        have h2 := intervalIntegrable_rsub_rpow c
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2]
        have e1 : ∫ t in (c - 1)..(c + 1), (t - c) ^ (-(1 / 2 : ℝ)) = 2 := by
          rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) c]
          simp only [sub_sub_cancel_left, add_sub_cancel_left]
          exact integral_rpow_neg_half_symm
        have e2 : ∫ t in (c - 1)..(c + 1), (c - t) ^ (-(1 / 2 : ℝ)) = 2 := by
          rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) c]
          simp only [sub_add_cancel_left, sub_sub_cancel]
          exact integral_rpow_neg_half_symm
        rw [e1, e2]
        norm_num


/-! ## Uniform integrability of `log ‖Ψ‖` on the line -/

/-- **Small values of a mollifier on the critical line.**  For every `ε ∈ (0,1)`,
`∫_{T₁}^{T₂} max(log ε − log ‖Ψ(1/2+it)‖, 0) dt ≤ (C₁ (T₂−T₁) + C₂ (1+|T₁|+|T₂|)) / log(1/ε)`. -/
theorem exists_line_smallValues_bound (b : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) (hb1 : b 1 = 1)
    (hbn : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ T₁ T₂ : ℝ, T₁ ≤ T₂ → ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ t in T₁..T₂, max (Real.log ε -
          Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) 0)
        ≤ (C₁ * (T₂ - T₁) + C₂ * (1 + |T₁| + |T₂|)) / Real.log (1 / ε) := by
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hΨan : AnalyticOnNhd ℂ (edPoly b s) Set.univ := analyticOnNhd_edPoly b hs
  have hne : ∃ z : ℂ, edPoly b s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  obtain ⟨K, hK, hcard⟩ := exists_windowStripZeros_card_le b hN hb1 hbn
  set C₀ := mollC₀ b s with hC₀
  set Nm := mollNmax b s with hNm
  have hC₀0 : 0 ≤ C₀ := mollC₀_nonneg b h1 hb1
  have hNm0 : 0 ≤ Nm := mollNmax_nonneg b h1 hb1
  refine ⟨2 * C₀ ^ 2, 2 * Nm ^ 3 * 64 * 28 * K, by positivity, by positivity, ?_⟩
  intro T₁ T₂ hT ε hε hε1
  set lam : ℝ := Real.log (1 / ε) with hlam
  have hlampos : 0 < lam := Real.log_pos (by rw [lt_div_iff₀ hε]; linarith)
  have hlogε : Real.log ε = -lam := by rw [hlam, one_div, Real.log_inv, neg_neg]
  set Z := windowStripZeros b hs hne T₁ T₂ with hZ
  set E : Finset ℝ := Z.image Complex.im with hE
  set G : ℝ → ℝ := fun t => 2 * C₀ ^ 2 + 2 * Nm ^ 3 * ∑ u ∈ Z, rpowMajorant u.im t with hG
  set φ : ℝ → ℝ := fun t => max (Real.log ε -
    Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) 0 with hφ
  -- integrability
  have hφint : IntervalIntegrable φ MeasureTheory.volume T₁ T₂ := by
    have hf : IntervalIntegrable (fun t : ℝ => Real.log ε -
        Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) MeasureTheory.volume T₁ T₂ :=
      intervalIntegrable_const.sub (intervalIntegrable_log_norm_vertical_of_entire hΨan (1 / 2) T₁ T₂)
    rw [intervalIntegrable_iff] at hf ⊢
    exact hf.pos_part
  have hGint : IntervalIntegrable G MeasureTheory.volume T₁ T₂ := by
    have hsum : IntervalIntegrable (fun t => ∑ u ∈ Z, rpowMajorant u.im t) MeasureTheory.volume T₁ T₂ := by
      have := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := T₁) (b := T₂) Z
        (f := fun u => fun t => rpowMajorant u.im t)
        (fun u _ => intervalIntegrable_rpowMajorant u.im T₁ T₂)
      rw [Finset.sum_fn] at this
      exact this
    exact intervalIntegrable_const.add (hsum.const_mul _)
  have hG0 : ∀ t, 0 ≤ G t := by
    intro t
    have : 0 ≤ ∑ u ∈ Z, rpowMajorant u.im t := Finset.sum_nonneg fun u _ => rpowMajorant_nonneg _ _
    rw [hG]; positivity
  -- a.e. pointwise bound
  have hEnull : ∀ᵐ t ∂MeasureTheory.volume, t ∉ (E : Set ℝ) := by
    rw [← MeasureTheory.measure_eq_zero_iff_ae_notMem]
    exact (E : Set ℝ).toFinite.measure_zero _
  have hae : φ ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc T₁ T₂)] fun t => lam⁻¹ * G t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
    filter_upwards [hEnull] with t htE ht
    have hA := lineLogNeg_sq_le b hs h1 hb1 hbn hne hT ht
    have hmaj : ∑ u ∈ Z, zeroLogNeg u t ^ 2 ≤ ∑ u ∈ Z, rpowMajorant u.im t := by
      apply Finset.sum_le_sum
      intro u hu
      apply zeroLogNeg_sq_le_rpowMajorant
      intro h
      apply htE
      rw [hE, Finset.coe_image]
      exact ⟨u, hu, h.symm⟩
    have hAG : lineLogNeg b s t ^ 2 ≤ G t := by
      rw [hG]
      calc lineLogNeg b s t ^ 2 ≤ 2 * C₀ ^ 2 + 2 * Nm ^ 3 * ∑ u ∈ Z, zeroLogNeg u t ^ 2 := hA
        _ ≤ 2 * C₀ ^ 2 + 2 * Nm ^ 3 * ∑ u ∈ Z, rpowMajorant u.im t := by gcongr
    set L := Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ with hL
    have hφt : φ t = max (Real.log ε - L) 0 := rfl
    have hAt : lineLogNeg b s t = max 0 (-L) := rfl
    show φ t ≤ lam⁻¹ * G t
    rw [hφt]
    by_cases hcase : Real.log ε - L ≤ 0
    · rw [max_eq_right hcase]
      exact mul_nonneg (inv_nonneg.mpr hlampos.le) (hG0 t)
    · push_neg at hcase
      rw [max_eq_left hcase.le]
      have hAge : lineLogNeg b s t ≥ (Real.log ε - L) + lam := by
        rw [hAt, hlogε]
        have : -L ≥ (-lam - L) + lam := by linarith
        exact le_trans this (le_max_right _ _)
      have hA0 : 0 ≤ lineLogNeg b s t := le_max_left _ _
      have hkey : lam * (Real.log ε - L) ≤ lineLogNeg b s t ^ 2 := by
        nlinarith [hAge, hA0, hlampos, hcase]
      rw [inv_mul_eq_div, le_div_iff₀ hlampos]
      linarith [hAG]
  -- integrate
  have hint := intervalIntegral.integral_mono_ae_restrict hT hφint (hGint.const_mul _) hae
  have hGeval : (∫ t in T₁..T₂, lam⁻¹ * G t) =
      lam⁻¹ * (2 * C₀ ^ 2 * (T₂ - T₁) + 2 * Nm ^ 3 * ∑ u ∈ Z, ∫ t in T₁..T₂, rpowMajorant u.im t) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hsum : IntervalIntegrable (fun t => ∑ u ∈ Z, rpowMajorant u.im t) MeasureTheory.volume T₁ T₂ := by
      have := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := T₁) (b := T₂) Z
        (f := fun u => fun t => rpowMajorant u.im t)
        (fun u _ => intervalIntegrable_rpowMajorant u.im T₁ T₂)
      rw [Finset.sum_fn] at this
      exact this
    rw [hG]
    simp only
    rw [intervalIntegral.integral_add intervalIntegrable_const (hsum.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finset_sum (fun u _ => intervalIntegrable_rpowMajorant u.im T₁ T₂)]
    simp only [smul_eq_mul]
    ring
  have hZsum : ∑ u ∈ Z, ∫ t in T₁..T₂, rpowMajorant u.im t ≤ 64 * (Z.card : ℝ) := by
    calc ∑ u ∈ Z, ∫ t in T₁..T₂, rpowMajorant u.im t ≤ ∑ u ∈ Z, (64 : ℝ) :=
          Finset.sum_le_sum fun u _ => integral_rpowMajorant_le u.im T₁ T₂ hT
      _ = 64 * (Z.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hZcard : (Z.card : ℝ) ≤ K * (28 * (1 + |T₁| + |T₂|)) := by
    have h := hcard hne T₁ T₂ hT
    have : (1 + (27 + |T₁| + |T₂|) : ℝ) ≤ 28 * (1 + |T₁| + |T₂|) := by
      linarith [abs_nonneg T₁, abs_nonneg T₂]
    calc (Z.card : ℝ) ≤ K * (1 + (27 + |T₁| + |T₂|)) := h
      _ ≤ K * (28 * (1 + |T₁| + |T₂|)) := mul_le_mul_of_nonneg_left this hK.le
  have hfinal : lam⁻¹ * (2 * C₀ ^ 2 * (T₂ - T₁) + 2 * Nm ^ 3 * ∑ u ∈ Z, ∫ t in T₁..T₂, rpowMajorant u.im t)
      ≤ (2 * C₀ ^ 2 * (T₂ - T₁) + 2 * Nm ^ 3 * 64 * 28 * K * (1 + |T₁| + |T₂|)) / lam := by
    rw [div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlampos.le)
    have h1 : 2 * Nm ^ 3 * ∑ u ∈ Z, ∫ t in T₁..T₂, rpowMajorant u.im t
        ≤ 2 * Nm ^ 3 * (64 * (K * (28 * (1 + |T₁| + |T₂|)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hZsum.trans (mul_le_mul_of_nonneg_left hZcard (by norm_num))
    nlinarith [h1]
  calc (∫ t in T₁..T₂, φ t) ≤ ∫ t in T₁..T₂, lam⁻¹ * G t := hint
    _ = _ := hGeval
    _ ≤ _ := hfinal

end

end RHTower
