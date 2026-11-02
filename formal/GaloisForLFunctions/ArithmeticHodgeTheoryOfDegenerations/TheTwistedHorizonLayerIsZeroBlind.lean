import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCountLawOverEveryFiniteRing
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndex

/-!
# The twisted horizon layer is zero-blind

Which directions of the complete Weil family see an individual point of the zero configuration at
second order? A fixed conductor packet sees it only through the pole coefficient, with positive
weight (`tendsto_bulkLedger`); an untwisted horizon window sees Weil's summand of the synthesized
test (`tendsto_horizonLedger`). This file settles the remaining directions of the horizon layer:
windows twisted by an `m`-periodic weight of mean zero — a Ramanujan sum `c_m(n)`, `m ≥ 2`, or a
nonprincipal character — see **no** point of the strip.

* **Twisted Riemann sums vanish** (`norm_twistedRiemannSum_le`): the twist has a bounded periodic
  primitive, and summation by parts against the Lipschitz profile `F_s` gives
  `|N⁻¹ Σ_{r ≤ N} F_s(r/N) χ(r)| ≤ 2 (Σ_{j<m} |χ(j)|) (L_h + |s − 1| B_h) e^{2A}/N`.
* **Twisted ledger** (`tendsto_twistedLedger`): the contribution of every point `ρ` of the
  critical strip to the normalized complete form of a twisted horizon window is `o(c_N)`.

Among the directions of the complete family only the untwisted horizon windows read an individual
zero at second order; the twisted horizon windows are zero-blind, like the count.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri

variable {h : ℝ → ℝ} {A : ℝ}

/-- The weights of a twisted horizon window, `x_n = χ(n) h(log(n/N))/√n`. -/
def twistedWeights (h : ℝ → ℝ) (χ : ℕ → ℝ) (N n : ℕ) : ℝ := horizonWeights h N n * χ n

/-- An `m`-periodic twist of mean zero. -/
structure MeanZeroTwist (χ : ℕ → ℝ) (m : ℕ) : Prop where
  pos : 0 < m
  periodic : ∀ n, χ (n + m) = χ n
  mean_zero : ∑ j ∈ range m, χ j = 0

/-! ### The periodic primitive is bounded -/

theorem sum_range_shift {χ : ℕ → ℝ} {m : ℕ} (hper : ∀ n, χ (n + m) = χ n) (a : ℕ) :
    ∑ j ∈ range m, χ (a + j) = ∑ j ∈ range m, χ j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 := Finset.sum_range_succ' (fun j => χ (a + j)) m
    have h2 := Finset.sum_range_succ (fun j => χ (a + j)) m
    simp only [add_zero] at h1
    rw [hper a] at h2
    have e : ∀ j, χ (a + (j + 1)) = χ (a + 1 + j) := fun j => by rw [add_assoc, add_comm 1 j]
    simp_rw [e] at h1
    linarith

theorem sum_range_mul_add {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) (q r : ℕ) :
    ∑ j ∈ range (q * m + r), χ j = ∑ j ∈ range r, χ j := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * m + r = (q * m + r) + m by ring, Finset.sum_range_add, ih,
      sum_range_shift hχ.periodic, hχ.mean_zero, add_zero]

/-- The partial sums of a mean-zero periodic twist are bounded by `Σ_{j<m} |χ(j)|`. -/
theorem abs_sum_range_le {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) (n : ℕ) :
    |∑ j ∈ range n, χ j| ≤ ∑ j ∈ range m, |χ j| := by
  rw [← Nat.div_add_mod n m, mul_comm, sum_range_mul_add hχ]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.mod_lt _ hχ.pos).le) fun _ _ _ => abs_nonneg _

/-! ### Summation by parts against a complex profile -/

theorem norm_sum_mul_real_le (f : ℕ → ℂ) (g : ℕ → ℝ) (M : ℕ) {B : ℝ}
    (hB : ∀ k ≤ M, |∑ i ∈ range (k + 1), g i| ≤ B) :
    ‖∑ i ∈ range (M + 1), f i * (g i : ℂ)‖ ≤
      B * (‖f M‖ + ∑ i ∈ range M, ‖f (i + 1) - f i‖) := by
  have hBnn : 0 ≤ B := (abs_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hG : ∀ k ≤ M, ‖∑ i ∈ range (k + 1), (g i : ℂ)‖ ≤ B := fun k hk => by
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]; exact hB k hk
  have h := Finset.sum_range_by_parts f (fun i => (g i : ℂ)) (M + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  rw [mul_add]
  refine add_le_add ?_ ?_
  · rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hG M le_rfl) (norm_nonneg _)
  · rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hG i (by simp at hi; omega)) (norm_nonneg _)

/-! ### Twisted Riemann sums -/

/-- The Dirichlet polynomial of a twisted window is a twisted Riemann sum. -/
theorem twistedRiemannSum_eq (h : ℝ → ℝ) (χ : ℕ → ℝ) (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    ((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (twistedWeights h χ N) (gammaOf s) =
      ((N : ℝ) : ℂ)⁻¹ * ∑ r ∈ Icc 1 N, horizonProfile h s (r / N) * (χ r : ℂ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [dirichletPoly_gammaOf, mul_sum, mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hq : (0 : ℝ) < r / N := div_pos hr0 hN0
  have e1 : horizonProfile h s (r / N) = (h (Real.log r - Real.log N) : ℂ) *
      Complex.exp (((Real.log r - Real.log N : ℝ) : ℂ) * (s - 1)) := by
    rw [horizonProfile, if_pos hq, RHTower.cpow_ofReal_eq_exp hq, Real.log_div hr0.ne' hN0.ne']
  have e2 : ((twistedWeights h χ N r : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * (Real.log r : ℂ)) =
      (h (Real.log r - Real.log N) : ℂ) * Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1)) *
        (χ r : ℂ) := by
    rw [twistedWeights, horizonWeights, Complex.ofReal_mul, Complex.ofReal_div, div_eq_mul_inv]
    rw [show (h (Real.log ↑r - Real.log ↑N) : ℂ) * ((Real.sqrt r : ℝ) : ℂ)⁻¹ * (χ r : ℂ) *
        Complex.exp ((s - 1 / 2) * (Real.log r : ℂ)) = (h (Real.log ↑r - Real.log ↑N) : ℂ) *
          (((Real.sqrt r : ℝ) : ℂ)⁻¹ * Complex.exp ((s - 1 / 2) * (Real.log r : ℂ))) * (χ r : ℂ)
      by ring, inv_sqrt_mul_exp hr1, RHTower.cpow_ofReal_eq_exp hr0]
  have e3 : ((N : ℝ) : ℂ)⁻¹ = Complex.exp (-((Real.log N : ℝ) : ℂ)) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hN0]
  rw [e1, e3, RHTower.cpow_ofReal_eq_exp hN0, e2]
  have key : Complex.exp (-((Real.log N : ℝ) : ℂ)) *
      Complex.exp (((Real.log r - Real.log N : ℝ) : ℂ) * (s - 1)) =
      Complex.exp (((Real.log N : ℝ) : ℂ) * -s) * Complex.exp (((Real.log r : ℝ) : ℂ) * (s - 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (-(h (Real.log r - Real.log N) : ℂ)) * (χ r : ℂ) * key

/-- **Twisted Riemann sums vanish**: `|N^{−s} D_x(γ_s)| ≤ 2 (Σ_{j<m}|χ(j)|) K_s/N`,
`K_s = (L_h + |s − 1| B_h) e^{2A}`, for `0 ≤ Re s ≤ 2`. -/
theorem norm_twistedRiemannSum_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh)
    {Lh : NNReal} (hLh : LipschitzWith Lh h) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m)
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) {N : ℕ} (hN : 1 ≤ N) :
    ‖((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (twistedWeights h χ N) (gammaOf s)‖ ≤
      2 * (∑ j ∈ range m, |χ j|) * (((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A)) / N := by
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨K, hK⟩ : ∃ K, K = ((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  rw [← hK]
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ j ∈ range m, |χ j| := ⟨_, rfl⟩
  rw [← hS]
  have hlip := lipschitzWith_horizonProfile hh hsupp hA hB hLh hs0 hs2
  rw [← hK] at hlip
  have hg0 : h 0 = 0 := horizon_zero_at_zero hsupp fun u v => by
    simpa [Real.dist_eq] using hLh.dist_le_mul u v
  have hF1 : horizonProfile h s 1 = 0 := by simp [horizonProfile, hg0]
  rw [twistedRiemannSum_eq h χ s hN, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hN0.le]
  -- reindex `r = i + 1`
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hre : ∑ r ∈ Icc 1 (M + 1), horizonProfile h s (r / ((M + 1 : ℕ) : ℝ)) * (χ r : ℂ) =
      ∑ i ∈ range (M + 1), horizonProfile h s (((i + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) *
        (χ (i + 1) : ℂ) := by
    rw [show Icc 1 (M + 1) = Finset.Ico 1 (M + 2) by ext; simp; omega, Finset.sum_Ico_eq_sum_range,
      show M + 2 - 1 = M + 1 by omega]
    exact sum_congr rfl fun i _ => by rw [add_comm 1 i]
  rw [hre]
  have hpart : ∀ k ≤ M, |∑ i ∈ range (k + 1), χ (i + 1)| ≤ 2 * S := by
    intro k _
    have e := Finset.sum_range_succ' χ (k + 1)
    have h1 := hS ▸ abs_sum_range_le hχ (k + 2)
    have h2 := hS ▸ abs_sum_range_le hχ 1
    rw [Finset.sum_range_one] at h2
    rw [show k + 2 = k + 1 + 1 by ring, e] at h1
    calc |∑ i ∈ range (k + 1), χ (i + 1)| = |(∑ i ∈ range (k + 1), χ (i + 1) + χ 0) - χ 0| := by
          ring_nf
      _ ≤ |∑ i ∈ range (k + 1), χ (i + 1) + χ 0| + |χ 0| := abs_sub _ _
      _ ≤ S + S := add_le_add h1 h2
      _ = 2 * S := by ring
  have hab := norm_sum_mul_real_le (fun i => horizonProfile h s (((i + 1 : ℕ) : ℝ) /
    ((M + 1 : ℕ) : ℝ))) (fun i => χ (i + 1)) M hpart
  have hlast : ‖horizonProfile h s (((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))‖ = 0 := by
    rw [div_self (by positivity), hF1, norm_zero]
  have hvar : ∑ i ∈ range M, ‖horizonProfile h s (((i + 1 + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) -
      horizonProfile h s (((i + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))‖ ≤ K := by
    have hcell : ∀ i ∈ range M, ‖horizonProfile h s (((i + 1 + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ)) -
        horizonProfile h s (((i + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))‖ ≤ K / ((M + 1 : ℕ) : ℝ) := by
      intro i _
      have := hlip.dist_le_mul (((i + 1 + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))
        (((i + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ))
      rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ hK0] at this
      refine this.trans (le_of_eq ?_)
      rw [← sub_div]
      push_cast
      rw [show (i : ℝ) + 1 + 1 - (i + 1) = 1 by ring, abs_of_pos (by positivity)]
      ring
    refine (Finset.sum_le_sum hcell).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  rw [hlast, zero_add] at hab
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ((M + 1 : ℕ) : ℝ)⁻¹ * ‖∑ i ∈ range (M + 1), horizonProfile h s (((i + 1 : ℕ) : ℝ) /
        ((M + 1 : ℕ) : ℝ)) * (χ (i + 1) : ℂ)‖
      ≤ ((M + 1 : ℕ) : ℝ)⁻¹ * (2 * S * K) := by
        refine mul_le_mul_of_nonneg_left (hab.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hvar (by positivity)
    _ = 2 * S * K / ((M + 1 : ℕ) : ℝ) := by ring

/-- Twisted Riemann sums tend to `0` on the critical strip. -/
theorem tendsto_twistedRiemannSum (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m)
    {s : ℂ} (hs0 : 0 ≤ s.re) (hs2 : s.re ≤ 2) :
    Tendsto (fun N : ℕ => ((N : ℝ) : ℂ) ^ (-s) * dirichletPoly N (twistedWeights h χ N)
      (gammaOf s)) atTop (𝓝 0) := by
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  set C := 2 * (∑ j ∈ range m, |χ j|) * (((Lh : ℝ) + ‖s - 1‖ * Bh) * Real.exp (2 * A))
  have hlim : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact norm_twistedRiemannSum_le hh hA hsupp hB hLh hχ hs0 hs2 hN

/-! ### The twisted ledger -/

/-- The contribution of `ρ` to the normalized complete form of a twisted horizon window. -/
def twistedLedger (Z : ZeroConfig) (φ h : ℝ → ℝ) (χ : ℕ → ℝ) (c : ℝ) (N : ℕ) (ρ : ℂ) : ℂ :=
  Z.Wsummand (cx (atomicTest N (twistedWeights h χ N) (atomDilate φ (c / N))))
      (cx (atomicTest N (twistedWeights h χ N) (atomDilate φ (c / N)))) ρ /
    ((∫ u, atomDilate φ (c / N) u ^ 2 : ℝ) : ℂ)

theorem inv_mul_twistedLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (h : ℝ → ℝ) (χ : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (ρ : ℂ) :
    ((c⁻¹ : ℝ) : ℂ) * twistedLedger Z φ h χ c N ρ =
      (Z.mult ρ : ℂ) * (paperFT (cx φ) (((c / N : ℝ) : ℂ) * gammaOf ρ) *
        conj (paperFT (cx φ) (((c / N : ℝ) : ℂ) * conj (gammaOf ρ)))) /
        ((∫ u, φ u ^ 2 : ℝ) : ℂ) *
      ((((N : ℝ) : ℂ) ^ (-ρ) * dirichletPoly N (twistedWeights h χ N) (gammaOf ρ)) *
        (((N : ℝ) : ℂ) ^ (-(1 - ρ)) * dirichletPoly N (twistedWeights h χ N) (gammaOf (1 - ρ)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hg : Continuous (atomDilate φ (c / N)) := by unfold atomDilate; fun_prop
  have hgc : HasCompactSupport (atomDilate φ (c / N)) := hasCompactSupport_atomDilate hw.ne' hφc
  have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hpow : ((N : ℝ) : ℂ) ^ (-ρ) * ((N : ℝ) : ℂ) ^ (-(1 - ρ)) = ((N : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hNc, show -ρ + -(1 - ρ) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  unfold twistedLedger
  rw [Wsummand_atomicTest Z hg hgc, paperFT_atomDilate hw, paperFT_atomDilate hw,
    conj_dirichletPoly_conj_gammaOf, integral_atomDilate_sq φ hw]
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hI : ((∫ u, φ u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hφ2.ne'
  rw [show ((N : ℝ) : ℂ) ^ (-ρ) * dirichletPoly N (twistedWeights h χ N) (gammaOf ρ) *
      (((N : ℝ) : ℂ) ^ (-(1 - ρ)) * dirichletPoly N (twistedWeights h χ N) (gammaOf (1 - ρ))) =
      (((N : ℝ) : ℂ) ^ (-ρ) * ((N : ℝ) : ℂ) ^ (-(1 - ρ))) *
        (dirichletPoly N (twistedWeights h χ N) (gammaOf ρ) *
          dirichletPoly N (twistedWeights h χ N) (gammaOf (1 - ρ))) by ring, hpow]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

/-- **The twisted horizon layer is zero-blind.** For a mean-zero periodic twist and every point
`ρ` of the critical strip, `c_N⁻¹` times the contribution of `ρ` to the normalized complete form
of the twisted window tends to `0` along every schedule with `c_N/N → 0`. -/
theorem tendsto_twistedLedger (Z : ZeroConfig) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (hφ2 : 0 < ∫ u, φ u ^ 2) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m)
    {ρ : ℂ} (hρ0 : 0 ≤ ρ.re) (hρ1 : ρ.re ≤ 1) {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    (hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ((c N)⁻¹ : ℂ) * twistedLedger Z φ h χ (c N) N ρ) atTop (𝓝 0) := by
  have hF : Continuous (paperFT (cx φ)) :=
    (RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hφ)
      (hφc.comp_left Complex.ofReal_zero)).continuous
  have hw : Tendsto (fun N : ℕ => ((c N / N : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa using hcN.ofReal
  have h1 : Tendsto (fun N : ℕ => paperFT (cx φ) (((c N / N : ℝ) : ℂ) * gammaOf ρ)) atTop
      (𝓝 (paperFT (cx φ) 0)) := by
    have := hw.mul_const (gammaOf ρ)
    rw [zero_mul] at this
    exact (hF.tendsto 0).comp this
  have h2 : Tendsto (fun N : ℕ => conj (paperFT (cx φ) (((c N / N : ℝ) : ℂ) * conj (gammaOf ρ))))
      atTop (𝓝 (conj (paperFT (cx φ) 0))) := by
    have := hw.mul_const (conj (gammaOf ρ))
    rw [zero_mul] at this
    exact (Complex.continuous_conj.tendsto _).comp ((hF.tendsto 0).comp this)
  have hs1 : 0 ≤ (1 - ρ).re := by simp; linarith
  have hs2 : (1 - ρ).re ≤ 2 := by simp; linarith
  have hlim := (((h1.mul h2).const_mul (Z.mult ρ : ℂ)).div_const ((∫ u, φ u ^ 2 : ℝ) : ℂ)).mul
    ((tendsto_twistedRiemannSum hh hA hsupp hχ hρ0 (by linarith)).mul
      (tendsto_twistedRiemannSum hh hA hsupp hχ hs1 hs2))
  rw [zero_mul, mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← inv_mul_twistedLedger Z hφ hφc hφ2 h χ (hc N) hN ρ]
  push_cast
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
