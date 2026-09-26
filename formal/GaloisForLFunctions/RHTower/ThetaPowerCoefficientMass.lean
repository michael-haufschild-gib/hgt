import GaloisForLFunctions.RHTower.ThetaPowerFourierExpansion
import GaloisForLFunctions.RHTower.ThetaPowerHorocycleMass
import GaloisForLFunctions.RHTower.AbsoluteTrigSeriesParseval

/-!
# Coefficient mass of the theta-power family

With `F_a(τ) = Σ b_n e^{πi(n+α)τ}`, `α = a/4`, Parseval on `Im τ = y` gives
`∫₀² |F_a(x+iy)|² dx = 2 M(y)`, `M(y) = Σ |b_n|² e^{-2π(n+α)y}`.  For `0 < a < 1/2`:

* the Hecke bound gives `M(y) ≤ C_H² y^{-1/2}`, hence `|b_n| ≤ C_H e^π (n+α)^{1/4}`;
* the horocycle mass gives `M(y) ≥ c y^{-1/2}` for `y ≤ 1`, hence `Σ |b_n|²(n+α)^{-1/2} = ∞`
  (dominated convergence as `y → 0`), hence `Σ |b_n|(n+α)^{-1/4} = ∞`;
* consequently for every `A` and `δ > 0` some `σ ∈ (1/4, 1/4+δ)` and `N` have `Σ_{n<N} |b_n|(n+α)^{-σ} ≥ A`.
-/

open Complex Real Filter Topology

namespace RHTower

noncomputable section

open Bottcher

variable {a : ℝ}

/-- The horizontal mass `M(y) = Σ |b_n|² e^{-2π(n+a/4)y}`. -/
def thetaPowerMass (a y : ℝ) : ℝ :=
  ∑' n : ℕ, ‖thetaPowerCoeff a n‖ ^ 2 * Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y))

theorem summable_norm_coeff_exp (ha : 0 ≤ a) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ * Real.exp (-(π * n * y)) := by
  have hr1 : Real.exp (-(π * y)) < 1 := by
    rw [Real.exp_lt_one_iff]; have := Real.pi_pos; nlinarith
  refine (summable_norm_thetaPowerCoeff_mul_pow ha (Real.exp_pos _).le hr1).congr (fun n => ?_)
  rw [← Real.exp_nat_mul]; congr 2; ring

theorem summable_thetaPowerMass (ha : 0 ≤ a) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ ^ 2 * Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y)) := by
  have hs := summable_norm_coeff_exp ha hy
  set A := ∑' n : ℕ, ‖thetaPowerCoeff a n‖ * Real.exp (-(π * n * y))
  have hsq : Summable fun n : ℕ => (‖thetaPowerCoeff a n‖ * Real.exp (-(π * n * y))) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) (hs.mul_left A)
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hs.le_tsum n (fun m _ => by positivity)) (by positivity)
  refine (hsq.mul_left (Real.exp (-(2 * π * (a / 4) * y)))).congr (fun n => ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  have : Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y)) =
      Real.exp (-(2 * π * (a / 4) * y)) * Real.exp (((2 : ℕ) : ℝ) * -(π * n * y)) := by
    rw [← Real.exp_add]; congr 1; push_cast; ring
  rw [this]; ring

/-- **Horizontal Parseval.** -/
theorem integral_norm_sq_thetaPowerForm (ha : 0 ≤ a) {y : ℝ} (hy : 0 < y) :
    ∫ x in (0 : ℝ)..2, ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2 = 2 * thetaPowerMass a y := by
  set c : ℕ → ℂ := fun n => thetaPowerCoeff a n * ((Real.exp (-(π * n * y)) : ℝ) : ℂ) with hc
  have hcn : ∀ n, ‖c n‖ = ‖thetaPowerCoeff a n‖ * Real.exp (-(π * n * y)) := by
    intro n; rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hcs : Summable fun n => ‖c n‖ := by simp_rw [hcn]; exact summable_norm_coeff_exp ha hy
  have hF : ∀ x : ℝ, thetaPowerForm a ((x : ℂ) + y * Complex.I) =
      Complex.exp (π * Complex.I * ((a / 4 : ℝ) : ℂ) * ((x : ℂ) + y * Complex.I)) *
        ∑' n, c n * Complex.exp (π * Complex.I * n * x) := by
    intro x
    have hτ : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
    have hs := hasSum_thetaPowerForm ha hτ
    rw [← hs.tsum_eq, ← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hc]; push_cast
    have hA : Complex.exp (π * Complex.I * ((n : ℂ) + (a : ℂ) / 4) * ((x : ℂ) + y * Complex.I)) =
        Complex.exp (π * Complex.I * ((a : ℂ) / 4) * ((x : ℂ) + y * Complex.I)) *
          Complex.exp (-(π * n * y)) * Complex.exp (π * Complex.I * n * x) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring_nf; rw [Complex.I_sq]; ring
    rw [hA]; ring
  have hnorm : ∀ x : ℝ, ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2 =
      Real.exp (-(2 * π * (a / 4) * y)) * ‖∑' n, c n * Complex.exp (π * Complex.I * n * x)‖ ^ 2 := by
    intro x
    rw [hF, norm_mul, mul_pow, Complex.norm_exp]
    congr 1
    rw [← Real.exp_nat_mul]; congr 1
    simp; ring
  simp_rw [hnorm]
  rw [intervalIntegral.integral_const_mul, integral_norm_sq_trig_tsum c hcs]
  have hM : thetaPowerMass a y = Real.exp (-(2 * π * (a / 4) * y)) * ∑' n, ‖c n‖ ^ 2 := by
    unfold thetaPowerMass
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    rw [hcn, mul_pow, ← Real.exp_nat_mul]
    have : Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y)) =
        Real.exp (-(2 * π * (a / 4) * y)) * Real.exp (((2 : ℕ) : ℝ) * -(π * n * y)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [hM]; ring

theorem thetaPowerMass_nonneg (a y : ℝ) : 0 ≤ thetaPowerMass a y :=
  tsum_nonneg fun n => by positivity

/-- **Upper mass bound** from the Hecke bound. -/
theorem thetaPowerMass_le (ha0 : 0 < a) (ha1 : a < 1 / 2) {y : ℝ} (hy : 0 < y) :
    thetaPowerMass a y ≤ thetaPowerHeckeConstant a ^ 2 * y ^ (-(1 / 2 : ℝ)) := by
  have hint := integral_norm_sq_thetaPowerForm ha0.le hy
  have hpt : ∀ x ∈ Set.Icc (0 : ℝ) 2, ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2 ≤
      thetaPowerHeckeConstant a ^ 2 * y ^ (-(1 / 2 : ℝ)) := by
    intro x _
    have hτ : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
    have h := norm_thetaPowerForm_le_hecke ha0 ha1 hτ
    have him : ((x : ℂ) + y * Complex.I).im = y := by simp
    rw [him] at h
    have hC : 0 ≤ thetaPowerHeckeConstant a * y ^ (-(1 / 4 : ℝ)) := le_trans (norm_nonneg _) h
    calc ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2
        ≤ (thetaPowerHeckeConstant a * y ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = thetaPowerHeckeConstant a ^ 2 * y ^ (-(1 / 2 : ℝ)) := by
          rw [mul_pow, ← Real.rpow_natCast (y ^ _), ← Real.rpow_mul hy.le]; norm_num
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num)
    (Continuous.intervalIntegrable ((continuous_thetaPowerForm_horizontal a y hy).norm.pow 2 :
      Continuous fun x : ℝ => ‖thetaPowerForm a ((x : ℂ) + y * Complex.I)‖ ^ 2) _ _)
    (Continuous.intervalIntegrable continuous_const _ _) hpt
  simp only [Pi.pow_apply] at hmono
  rw [hint, intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith

/-- The lower mass constant. -/
def thetaPowerMassLower : ℝ := thetaPowerLowerConstant 16 ^ 2 * (2 - 6 / 16) / 2

theorem thetaPowerMassLower_pos : 0 < thetaPowerMassLower := by
  unfold thetaPowerMassLower; have := thetaPowerLowerConstant_pos 16; positivity

/-- **Lower mass bound** from the horocycle mass. -/
theorem thetaPowerMassLower_le (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) :
    thetaPowerMassLower * y ^ (-(1 / 2 : ℝ)) ≤ thetaPowerMass a y := by
  have h := thetaPowerHorocycleMass ha0 ha1 (K := 16) (by norm_num) hy0 hy1
  rw [integral_norm_sq_thetaPowerForm ha0 hy0] at h
  unfold thetaPowerMassLower
  linarith

theorem thetaPowerHeckeConstant_pos (ha0 : 0 < a) (ha1 : a < 1 / 2) : 0 < thetaPowerHeckeConstant a := by
  unfold thetaPowerHeckeConstant
  have hmin : 0 < min a (1 - 2 * a) := lt_min ha0 (by linarith)
  have hb : 0 < π * min a (1 - 2 * a) / 4 := by positivity
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hb _)

/-- The coefficient constant `C_H e^π`. -/
def thetaPowerCoeffConstant (a : ℝ) : ℝ := thetaPowerHeckeConstant a * Real.exp π

/-- **Coefficient bound** `|b_n| ≤ C_H e^π (n+a/4)^{1/4}`. -/
theorem norm_thetaPowerCoeff_le (ha0 : 0 < a) (ha1 : a < 1 / 2) (n : ℕ) :
    ‖thetaPowerCoeff a n‖ ≤ thetaPowerCoeffConstant a * ((n : ℝ) + a / 4) ^ (1 / 4 : ℝ) := by
  set lam : ℝ := (n : ℝ) + a / 4 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  set y : ℝ := 1 / lam with hy
  have hy0 : 0 < y := by rw [hy]; positivity
  have hterm : ‖thetaPowerCoeff a n‖ ^ 2 * Real.exp (-(2 * π * lam * y)) ≤ thetaPowerMass a y :=
    (summable_thetaPowerMass ha0.le hy0).le_tsum n (fun m _ => by positivity)
  have hmass := thetaPowerMass_le ha0 ha1 hy0
  have hexp : Real.exp (-(2 * π * lam * y)) = Real.exp (-(2 * π)) := by
    congr 1; rw [hy]; field_simp
  rw [hexp] at hterm
  have hyrpow : y ^ (-(1 / 2 : ℝ)) = lam ^ (1 / 2 : ℝ) := by
    rw [hy, one_div, Real.inv_rpow hlam0.le, ← Real.rpow_neg hlam0.le, neg_neg]
  have hsq : ‖thetaPowerCoeff a n‖ ^ 2 ≤
      (thetaPowerHeckeConstant a * Real.exp π) ^ 2 * lam ^ (1 / 2 : ℝ) := by
    have h1 := hterm.trans hmass
    rw [hyrpow] at h1
    have he : Real.exp (-(2 * π)) * Real.exp π ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; simp
    have hE : 0 < Real.exp π ^ 2 := by positivity
    calc ‖thetaPowerCoeff a n‖ ^ 2 = ‖thetaPowerCoeff a n‖ ^ 2 * Real.exp (-(2 * π)) * Real.exp π ^ 2 := by
          rw [mul_assoc, he, mul_one]
      _ ≤ thetaPowerHeckeConstant a ^ 2 * lam ^ (1 / 2 : ℝ) * Real.exp π ^ 2 := by gcongr
      _ = (thetaPowerHeckeConstant a * Real.exp π) ^ 2 * lam ^ (1 / 2 : ℝ) := by ring
  have hC : 0 ≤ thetaPowerHeckeConstant a * Real.exp π :=
    (mul_pos (thetaPowerHeckeConstant_pos ha0 ha1) (Real.exp_pos _)).le
  unfold thetaPowerCoeffConstant
  have hq : (lam ^ (1 / 4 : ℝ)) ^ 2 = lam ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]; norm_num
  have hrhs : 0 ≤ thetaPowerHeckeConstant a * Real.exp π * lam ^ (1 / 4 : ℝ) :=
    mul_nonneg hC (Real.rpow_nonneg hlam0.le _)
  rw [← hq, ← mul_pow] at hsq
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs (by norm_num)).mp hsq

/-- `u^{1/2} e^{-2πu} ≤ 1` for `u ≥ 0`. -/
theorem sqrt_mul_exp_neg_le_one {u : ℝ} (hu : 0 ≤ u) : u ^ (1 / 2 : ℝ) * Real.exp (-(2 * π * u)) ≤ 1 := by
  have h1 : u ^ (1 / 2 : ℝ) ≤ Real.exp u := by
    rcases le_total u 1 with h | h
    · exact (Real.rpow_le_one hu h (by norm_num)).trans (Real.one_le_exp hu)
    · calc u ^ (1 / 2 : ℝ) ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
        _ = u := Real.rpow_one u
        _ ≤ u + 1 := by linarith
        _ ≤ Real.exp u := Real.add_one_le_exp u
  have h2 : Real.exp u * Real.exp (-(2 * π * u)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]; have := Real.pi_gt_three; nlinarith
  calc u ^ (1 / 2 : ℝ) * Real.exp (-(2 * π * u)) ≤ Real.exp u * Real.exp (-(2 * π * u)) := by gcongr
    _ ≤ 1 := h2

/-- **Divergence at the critical exponent.** `Σ |b_n|² (n+a/4)^{-1/2} = ∞`. -/
theorem not_summable_thetaPowerCoeff_sq (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    ¬ Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) := by
  intro hsum
  have hlam : ∀ n : ℕ, 0 < (n : ℝ) + a / 4 := fun n => by positivity
  set f : ℝ → ℕ → ℝ := fun y n => ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) *
    ((((n : ℝ) + a / 4) * y) ^ (1 / 2 : ℝ) * Real.exp (-(2 * π * (((n : ℝ) + a / 4) * y))))
  have hid : ∀ y, 0 < y → y ^ (1 / 2 : ℝ) * thetaPowerMass a y = ∑' n, f y n := by
    intro y hy
    unfold thetaPowerMass
    rw [← tsum_mul_left]
    refine tsum_congr (fun n => ?_)
    simp only [f]
    rw [Real.mul_rpow (hlam n).le hy.le]
    have hp : ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) + a / 4) ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add (hlam n)]; norm_num
    have he : Real.exp (-(2 * π * (((n : ℝ) + a / 4) * y))) = Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y)) := by
      congr 1; ring
    rw [he]
    calc y ^ (1 / 2 : ℝ) * (‖thetaPowerCoeff a n‖ ^ 2 * Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y)))
        = ‖thetaPowerCoeff a n‖ ^ 2 * (((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) + a / 4) ^ (1 / 2 : ℝ)) *
            (y ^ (1 / 2 : ℝ) * Real.exp (-(2 * π * ((n : ℝ) + a / 4) * y))) := by rw [hp]; ring
      _ = _ := by ring
  have hlim : Tendsto (fun y => ∑' n, f y n) (𝓝[>] 0) (𝓝 (∑' n : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun n => ?_) ?_
    · have hc : ContinuousAt (fun y : ℝ => f y n) 0 := by
        simp only [f]
        refine continuousAt_const.mul ((ContinuousAt.rpow_const (by fun_prop) (Or.inr (by norm_num))).mul
          (by fun_prop))
      have h0 : f 0 n = 0 := by simp [f]
      have ht := hc.tendsto
      rw [h0] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy n
      have hy0 : (0 : ℝ) < y := hy
      simp only [f, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have hb := sqrt_mul_exp_neg_le_one (mul_pos (hlam n) hy0).le
      calc ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) *
            ((((n : ℝ) + a / 4) * y) ^ (1 / 2 : ℝ) * Real.exp (-(2 * π * (((n : ℝ) + a / 4) * y))))
          ≤ ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
        _ = _ := mul_one _
  rw [tsum_zero] at hlim
  have hlow : ∀ᶠ y in 𝓝[>] (0 : ℝ), thetaPowerMassLower ≤ ∑' n, f y n := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with y hy
    rw [← hid y hy.1]
    have h := thetaPowerMassLower_le ha0.le ha1.le hy.1 hy.2.le
    have hyp : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy.1 _
    have hyy : y ^ (1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hy.1]; norm_num
    calc thetaPowerMassLower = y ^ (1 / 2 : ℝ) * (thetaPowerMassLower * y ^ (-(1 / 2 : ℝ))) := by
          rw [mul_left_comm, hyy, mul_one]
      _ ≤ y ^ (1 / 2 : ℝ) * thetaPowerMass a y := by gcongr
  have := ge_of_tendsto hlim hlow
  linarith [thetaPowerMassLower_pos]

/-- **Divergence of the absolute series at `σ = 1/4`.** -/
theorem not_summable_thetaPowerCoeff_quarter (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    ¬ Summable fun n : ℕ => ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ)) := by
  intro hs
  apply not_summable_thetaPowerCoeff_sq ha0 ha1
  have hC : 0 < thetaPowerCoeffConstant a :=
    mul_pos (thetaPowerHeckeConstant_pos ha0 ha1) (Real.exp_pos _)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left (thetaPowerCoeffConstant a))
  have hlam : 0 < (n : ℝ) + a / 4 := by positivity
  have hb := norm_thetaPowerCoeff_le ha0 ha1 n
  calc ‖thetaPowerCoeff a n‖ ^ 2 * ((n : ℝ) + a / 4) ^ (-(1 / 2 : ℝ))
      = ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ)) *
          (‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ))) := by
        rw [sq, show (-(1 / 2 : ℝ)) = -(1 / 4) + -(1 / 4) by norm_num, Real.rpow_add hlam]; ring
    _ ≤ thetaPowerCoeffConstant a * (‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ))) := by
        gcongr
        calc ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ))
            ≤ thetaPowerCoeffConstant a * ((n : ℝ) + a / 4) ^ (1 / 4 : ℝ) *
                ((n : ℝ) + a / 4) ^ (-(1 / 4 : ℝ)) := by gcongr
          _ = thetaPowerCoeffConstant a := by
              rw [mul_assoc, ← Real.rpow_add hlam]; norm_num

/-- **Polygon mass.** For every `A` and `δ > 0` there are `σ ∈ (1/4, 1/4 + δ)` and `N` with
`Σ_{n<N} |b_n| (n+a/4)^{-σ} ≥ A`. -/
theorem exists_sigma_partial_mass_ge (ha0 : 0 < a) (ha1 : a < 1 / 2) (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 1 / 4 < σ ∧ σ < 1 / 4 + δ ∧ ∃ N : ℕ,
      A ≤ ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-σ) := by
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by positivity)).mp
    (not_summable_thetaPowerCoeff_quarter ha0 ha1)
  obtain ⟨N, hN⟩ := (hdiv.eventually (Filter.eventually_gt_atTop (A + 1))).exists
  have hlam : ∀ n : ℕ, 0 < (n : ℝ) + a / 4 := fun n => by positivity
  have hcont : Continuous fun σ : ℝ =>
      ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-σ) := by
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    exact (Real.continuous_const_rpow (hlam n).ne').comp continuous_neg
  have hopen : ∀ᶠ σ in 𝓝 (1 / 4 : ℝ),
      A < ∑ n ∈ Finset.range N, ‖thetaPowerCoeff a n‖ * ((n : ℝ) + a / 4) ^ (-σ) :=
    hcont.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hopen
  refine ⟨1 / 4 + min δ ε / 2, by have := lt_min hδ hε; linarith, by
    have := min_le_left δ ε; have := lt_min hδ hε; linarith, N, ?_⟩
  refine (hball ?_).le
  rw [Real.dist_eq, abs_of_nonneg (by have := lt_min hδ hε; linarith)]
  have := min_le_right δ ε; have := lt_min hδ hε; linarith

end

end RHTower
