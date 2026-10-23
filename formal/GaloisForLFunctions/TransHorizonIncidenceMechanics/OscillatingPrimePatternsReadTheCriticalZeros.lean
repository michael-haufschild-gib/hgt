import GaloisForLFunctions.TransHorizonIncidenceMechanics.SubgroupFlipsArePaidAtHalfDamping

/-!
# Oscillating prime patterns read the critical zeros

For `a ∈ [−1, 1]` and `t₀ ∈ ℝ` let `f_{a,t₀}` be the completely multiplicative pattern with
`f(p) = a cos(t₀ log p)` (`oscPattern`), and `c(d) = f(d) d^{-1/2}` its half-damped weight
(`oscWeight`). Since `f(p) p^{-w} = (a/2)(p^{-(w − it₀)} + p^{-(w + it₀)})`, the Euler products give

`|log|F(w)| − (a/2)(log|ζ(w − it₀)| + log|ζ(w + it₀)|)| ≤ 2 Σ_p p^{-2}`  on `Re w > 1`

(`abs_log_norm_oscSeries_sub_le`): the series sees `ζ` at the two heights `±t₀` with exponent `a/2`
each. Through the boundary-energy form of the receiver this decides the weight:

* `a ≤ 0`, every `t₀`: paid (`receiverBounded_oscWeight_nonpos`), by `1/ζ` bounds right of `Re = 1`;
* `0 < a < 1`, `t₀ ≠ 0`: paid (`receiverBounded_oscWeight_of_lt_one`): the singularity
  `|C(1/2 + u + it)|² ≲ |t − t₀|^{-a}` is integrable.

The real-axis prime mean of `f_{a,t₀}` is `0` for `t₀ ≠ 0`, yet the threshold of the amplitude is `1`,
not `1/2`: the quarter law applies height by height.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Completely multiplicative patterns from prime values -/

/-- The completely multiplicative function with prescribed values `g(p)` at the primes. -/
def primeValueHom (g : ℕ → ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else (n.primeFactorsList.map g).prod
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [mul_ne_zero hm hn, hm, hn, if_false]
    rw [((Nat.perm_primeFactorsList_mul hm hn).map g).prod_eq, List.map_append, List.prod_append]

theorem primeValueHom_prime (g : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : primeValueHom g p = g p := by
  simp [primeValueHom, hp.ne_zero, Nat.primeFactorsList_prime hp]

/-- The oscillating prime pattern `f(p) = a cos(t₀ log p)`. -/
def oscPattern (a t₀ : ℝ) : ℕ →*₀ ℝ := primeValueHom fun p => a * Real.cos (t₀ * Real.log p)

theorem oscPattern_prime (a t₀ : ℝ) {p : ℕ} (hp : p.Prime) :
    oscPattern a t₀ p = a * Real.cos (t₀ * Real.log p) :=
  primeValueHom_prime _ hp

theorem abs_oscPattern_le {a : ℝ} (ha : |a| ≤ 1) (t₀ : ℝ) (n : ℕ) : |oscPattern a t₀ n| ≤ 1 :=
  abs_patternHom_le_one _ (fun p hp => by
    rw [oscPattern_prime a t₀ hp, abs_mul]
    exact mul_le_one₀ ha (abs_nonneg _) (Real.abs_cos_le_one _)) n

/-- The pattern is even in the frequency. -/
theorem oscPattern_neg (a t₀ : ℝ) : oscPattern a (-t₀) = oscPattern a t₀ := by
  unfold oscPattern
  congr 1
  funext p
  rw [neg_mul, Real.cos_neg]

/-- At frequency `0` the pattern is the constant-sign model `a^{Ω}`. -/
theorem oscPattern_zero (a : ℝ) : oscPattern a 0 = constantSignHom a := by
  ext n
  induction n using Nat.recOnMul with
  | zero => simp
  | one => simp
  | prime p hp => rw [oscPattern_prime a 0 hp, constantSignHom_prime a hp]; simp
  | mul m n hm hn => rw [map_mul, map_mul, hm, hn]

/-- The half-damped oscillating weight `f_{a,t₀}(d) d^{-1/2}`. -/
def oscWeight (a t₀ : ℝ) (d : ℕ) : ℝ := oscPattern a t₀ d * (d : ℝ) ^ (-(1 / 2 : ℝ))

theorem oscWeight_neg (a t₀ : ℝ) : oscWeight a (-t₀) = oscWeight a t₀ := by
  funext d; simp only [oscWeight, oscPattern_neg]

theorem oscWeight_zero (a : ℝ) : oscWeight a 0 = constantSignWeight a := by
  funext d; simp only [oscWeight, constantSignWeight, oscPattern_zero]

theorem dampedClass_oscWeight {a : ℝ} (ha : |a| ≤ 1) (t₀ : ℝ) :
    DampedClass 1 (1 / 2) (oscWeight a t₀) := fun d => by
  rw [oscWeight, one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (abs_oscPattern_le ha t₀ d)

theorem weightDirichletSeries_oscWeight (a t₀ : ℝ) (s : ℂ) :
    weightDirichletSeries (oscWeight a t₀) s =
      ∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1 / 2)) :=
  weightDirichletSeries_pattern (oscPattern a t₀) s

/-! ### The Euler comparison with `ζ` at the heights `±t₀` -/

/-- `cos(t₀ log p) p^{-w} = (p^{-(w − it₀)} + p^{-(w + it₀)})/2`. -/
theorem cos_mul_cpow_eq {p : ℕ} (hp : 0 < p) (t₀ : ℝ) (w : ℂ) :
    ((Real.cos (t₀ * Real.log p) : ℝ) : ℂ) * (p : ℂ) ^ (-w) =
      ((p : ℂ) ^ (-(w - t₀ * I)) + (p : ℂ) ^ (-(w + t₀ * I))) / 2 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0,
    Complex.cpow_def_of_ne_zero hp0, hlog, Complex.ofReal_cos, Complex.cos, ← Complex.exp_add,
    ← Complex.exp_add]
  push_cast
  ring_nf

/-- The two-sided Euler log of `ζ`: `|log|ζ(v)| − Re Σ_p p^{-v}| ≤ S` on `Re v > 1`. -/
theorem abs_log_norm_riemannZeta_sub_re_le {v : ℂ} (hv : 1 < v.re) :
    |Real.log ‖riemannZeta v‖ - (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-v)).re| ≤
      primeSquareMass := by
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-v)
  have hys : Summable y := summable_prime_cpow_neg hv
  have hL : Summable (fun p : Nat.Primes => -Complex.log (1 - y p)) := hys.clog_one_sub.neg
  have hlog : Real.log ‖riemannZeta v‖ = ∑' p : Nat.Primes, (-Complex.log (1 - y p)).re := by
    rw [← riemannZeta_eulerProduct_exp_log hv, Complex.norm_exp, Complex.re_tsum hL, Real.log_exp]
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - y p)).re) :=
    Complex.reCLM.summable hL
  have hre2 : Summable (fun p : Nat.Primes => (y p).re) := Complex.reCLM.summable hys
  have hterm : ∀ p : Nat.Primes, ‖(-Complex.log (1 - y p)).re - (y p).re‖ ≤
      ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    rw [Real.norm_eq_abs]
    exact (abs_re_neg_log_one_sub_sub_re_le (norm_prime_cpow_neg_le hv p).1).trans
      (norm_prime_cpow_neg_le hv p).2
  have hdiff := hre1.sub hre2
  rw [hlog, Complex.re_tsum hys, ← hre1.tsum_sub hre2, ← Real.norm_eq_abs, primeSquareMass]
  exact (norm_tsum_le_tsum_norm hdiff.norm).trans
    (Summable.tsum_le_tsum hterm hdiff.norm summable_primeSquare)

/-- **The Euler comparison.** On `Re w > 1`, for `|a| ≤ 1`,
`|log|F(w)| − (a/2)(log|ζ(w − it₀)| + log|ζ(w + it₀)|)| ≤ 2S`. -/
theorem abs_log_norm_oscSeries_sub_le {a : ℝ} (ha : |a| ≤ 1) (t₀ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    |Real.log ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ -
      a / 2 * (Real.log ‖riemannZeta (w - t₀ * I)‖ + Real.log ‖riemannZeta (w + t₀ * I)‖)| ≤
        2 * primeSquareMass := by
  have hwm : 1 < (w - t₀ * I).re := by simpa using hw
  have hwp : 1 < (w + t₀ * I).re := by simpa using hw
  have hF := abs_log_norm_tsum_sub_re_le (cweightedPatternHom (oscPattern a t₀) w) hw fun n => by
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_natCast]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_oscPattern_le ha t₀ n)
  have hFn : ∑' n, cweightedPatternHom (oscPattern a t₀) w n =
      ∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := tsum_congr fun n => rfl
  have hsm := summable_prime_cpow_neg hwm
  have hsp := summable_prime_cpow_neg hwp
  have hFp : ∑' p : Nat.Primes, cweightedPatternHom (oscPattern a t₀) w p =
      ((a / 2 : ℝ) : ℂ) * (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w - t₀ * I)) +
        ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w + t₀ * I))) := by
    rw [← hsm.tsum_add hsp, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast, oscPattern_prime a t₀ p.2]
    rw [Complex.ofReal_mul, mul_assoc, cos_mul_cpow_eq p.2.pos]
    push_cast
    ring
  rw [hFn, hFp, Complex.re_ofReal_mul, Complex.add_re] at hF
  have hζm := abs_log_norm_riemannZeta_sub_re_le hwm
  have hζp := abs_log_norm_riemannZeta_sub_re_le hwp
  have hS : ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) = primeSquareMass := rfl
  rw [hS] at hF
  have ha2 : |a / 2| ≤ 1 / 2 := by rw [abs_div, abs_two]; linarith
  set L := Real.log ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
  set Zm := Real.log ‖riemannZeta (w - t₀ * I)‖
  set Zp := Real.log ‖riemannZeta (w + t₀ * I)‖
  set Rm := (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w - t₀ * I))).re
  set Rp := (∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(w + t₀ * I))).re
  have key : L - a / 2 * (Zm + Zp) = (L - a / 2 * (Rm + Rp)) - a / 2 * ((Zm - Rm) + (Zp - Rp)) := by
    ring
  rw [key]
  have h2 : |a / 2 * ((Zm - Rm) + (Zp - Rp))| ≤ 1 / 2 * (primeSquareMass + primeSquareMass) := by
    rw [abs_mul]
    exact mul_le_mul ha2 ((abs_add_le _ _).trans (add_le_add hζm hζp)) (abs_nonneg _)
      (by norm_num)
  have h3 := abs_add_le (L - a / 2 * (Rm + Rp)) (-(a / 2 * ((Zm - Rm) + (Zp - Rp))))
  rw [abs_neg, ← sub_eq_add_neg] at h3
  linarith

/-- The oscillating series does not vanish on `Re w > 1` (an Euler product). -/
theorem oscSeries_ne_zero {a : ℝ} (ha : |a| ≤ 1) (t₀ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) ≠ 0 := by
  set g := cweightedPatternHom (oscPattern a t₀) w
  have hsum : Summable (fun n => ‖g n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    simp only [g, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -w.re ≠ 0 by intro h; linarith)]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (abs_oscPattern_le ha t₀ n)
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  have hFn : ∑' n, g n = ∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) :=
    tsum_congr fun n => rfl
  rw [← hFn, ← hE]
  exact Complex.exp_ne_zero _

/-- **The Euler bounds**: `e^{-2S} Z^{a/2} ≤ |F(w)| ≤ e^{2S} Z^{a/2}`, `Z = |ζ(w − it₀)| |ζ(w + it₀)|`. -/
theorem norm_oscSeries_le_ge {a : ℝ} (ha : |a| ≤ 1) (t₀ : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        Real.exp (2 * primeSquareMass) *
          (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) ∧
      Real.exp (-(2 * primeSquareMass)) *
          (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) ≤
        ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ := by
  have hwm : 1 ≤ (w - t₀ * I).re := by simp; linarith
  have hwp : 1 ≤ (w + t₀ * I).re := by simp; linarith
  have hm := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwm)
  have hp := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwp)
  have hpos := norm_pos_iff.mpr (oscSeries_ne_zero ha t₀ hw)
  have h := abs_le.mp (abs_log_norm_oscSeries_sub_le ha t₀ hw)
  rw [← Real.exp_log hpos, Real.rpow_def_of_pos (mul_pos hm hp), ← Real.exp_add, ← Real.exp_add,
    Real.log_mul hm.ne' hp.ne']
  exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

/-! ### Bounds on `ζ` -/

/-- `|ζ(w)| |w − 1| ≤ K₀` for `1 < Re w ≤ 2`, `|Im w| ≤ 2`. -/
theorem exists_norm_zeta_mul_sub_one_le :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → |w.im| ≤ 2 →
      ‖riemannZeta w‖ * ‖w - 1‖ ≤ K₀ := by
  obtain ⟨C, hC, hbound⟩ := RHTower.exists_norm_zetaPoleCleared_le
  refine ⟨12 * C, by positivity, fun w hw hw2 ht => ?_⟩
  have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hζ : riemannZeta w = RHTower.zetaPoleCleared w * w / (w - 1) := by
    rw [RHTower.zetaPoleCleared_eq hw1]; field_simp
  have hwn : ‖w‖ ≤ 4 := by
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ ≤ 2 + 2 := by rw [abs_of_pos (by linarith)]; linarith
      _ = 4 := by norm_num
  have hpc := hbound w (by linarith) (by linarith)
  have hpc' : ‖RHTower.zetaPoleCleared w‖ ≤ 3 * C := by
    calc _ ≤ C * (1 + |w.im|) := hpc
      _ ≤ C * 3 := by nlinarith
      _ = 3 * C := by ring
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hsub
  rw [hζ, norm_div, norm_mul, div_mul_cancel₀ _ hpos.ne']
  calc ‖RHTower.zetaPoleCleared w‖ * ‖w‖ ≤ (3 * C) * 4 :=
        mul_le_mul hpc' hwn (norm_nonneg _) (by positivity)
    _ = 12 * C := by ring

/-- `1/|ζ(v)| ≤ K (1 + |Im v|)^{1/4}` on `1 < Re v ≤ 2`. -/
theorem exists_inv_norm_zeta_le_uniform :
    ∃ K : ℝ, 0 < K ∧ ∀ v : ℂ, 1 < v.re → v.re ≤ 2 →
      ‖riemannZeta v‖⁻¹ ≤ K * (1 + |v.im|) ^ (1 / 4 : ℝ) := by
  obtain ⟨K₁, hK₁, hlarge⟩ := exists_inv_norm_zeta_le_rpow_large
  obtain ⟨K₂, hK₂, hbox⟩ := exists_inv_norm_zeta_le_box
  refine ⟨K₁ + K₂, by positivity, fun v hv hv2 => ?_⟩
  have h1 : 1 ≤ (1 + |v.im|) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg v.im]) (by norm_num)
  rcases le_total |v.im| 9 with h9 | h9
  · calc ‖riemannZeta v‖⁻¹ ≤ K₂ := hbox v hv hv2 h9
      _ ≤ (K₁ + K₂) * 1 := by linarith
      _ ≤ (K₁ + K₂) * (1 + |v.im|) ^ (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
  · calc ‖riemannZeta v‖⁻¹ ≤ K₁ * |v.im| ^ (1 / 4 : ℝ) := hlarge v hv hv2 h9
      _ ≤ (K₁ + K₂) * (1 + |v.im|) ^ (1 / 4 : ℝ) :=
          mul_le_mul (by linarith) (Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num))
            (by positivity) (by positivity)

/-- `ζ` is bounded on the box `1/2 ≤ σ ≤ 3/4`, `|t| ≤ T`. -/
theorem exists_norm_zeta_le_on_tall_box (T : ℝ) :
    ∃ Z₀ : ℝ, 0 ≤ Z₀ ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → |t| ≤ T →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Z₀ := by
  set K : Set ℂ := (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (-T) T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn riemannZeta K := fun z hz => by
    have hre := (Complex.mem_reProdIm.mp hz).1
    have hz1 : z ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
    exact (differentiableAt_riemannZeta hz1).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ t hσ hσ' ht => ?_⟩
  have hmem : (σ : ℂ) + t * I ∈ K := by
    rw [Complex.mem_reProdIm]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    exact ⟨⟨hσ, hσ'⟩, abs_le.mp ht⟩
  exact (hC _ hmem).trans (le_max_left _ _)

/-- `X^b ≤ 1 + X^{1/2}` for `X ≥ 0`, `0 ≤ b ≤ 1/2`. -/
theorem rpow_le_one_add_rpow_half {X b : ℝ} (hX : 0 ≤ X) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) :
    X ^ b ≤ 1 + X ^ (1 / 2 : ℝ) := by
  rcases le_total X 1 with h | h
  · have h1 := Real.rpow_le_one hX h hb0
    have h2 := Real.rpow_nonneg hX (1 / 2 : ℝ)
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h hb
    linarith

/-- `|t − t₀|^r` is interval integrable for `r > −1`. -/
theorem intervalIntegrable_abs_sub_rpow {r : ℝ} (hr : -1 < r) (t₀ a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => |t - t₀| ^ r) volume a b := by
  have h0 : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc).mp
      (intervalIntegral.intervalIntegrable_rpow' hr)).congr_fun
        (fun x hx => by simp only [abs_of_pos hx.1]) measurableSet_Ioc
  have habs : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => |x| ^ r) volume 0 c := by
    intro c
    rcases le_total 0 c with hc | hc
    · exact h0 c hc
    · have h := (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => |x| ^ r)).mp
        (h0 (-c) (by linarith)).symm
      simpa only [abs_neg, neg_neg, neg_zero] using h.symm
  have hall : IntervalIntegrable (fun x : ℝ => |x| ^ r) volume (a - t₀) (b - t₀) :=
    (habs (a - t₀)).symm.trans (habs (b - t₀))
  simpa only [sub_add_cancel] using hall.comp_sub_right t₀

/-! ### A line-energy criterion with a local majorant -/

/-- **An integrable local majorant pays the line energy.** If on `1/2 < σ < 3/4` the line integrand
is dominated on `(0, T]`, off one height `t₁`, by a fixed `g` integrable there, and
`|C(s) − P| ≤ B₁ t^{1/4}` for `t > T ≥ 2`, the line energies are uniformly bounded. -/
theorem exists_lineEnergy_le_of_majorant {c : ℕ → ℝ} {P T B₁ t₁ : ℝ} {g : ℝ → ℝ}
    (hT : 2 ≤ T) (hg : IntegrableOn g (Ioc 0 T))
    (hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ≠ t₁ →
      lineIntegrand c P σ t ≤ g t)
    (hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₁ * t ^ (1 / 4 : ℝ)) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t : ℝ, lineIntegrand c P σ t ≤ M := by
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set Λ : ℝ := B₁ ^ 2
  have hΛ : 0 ≤ Λ := sq_nonneg _
  refine ⟨2 * (∫ t in Ioc 0 T, g t + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand c P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 / ‖(σ : ℂ) + t * I‖ ^ 2 :=
    fun t => by simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  -- beyond `T`
  have hlarge' : ∀ u : ℝ, T < u →
      Φ u ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hsn : u ≤ ‖(σ : ℂ) + u * I‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + u * I)
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add] at this
      rwa [abs_of_pos hu0] at this
    rw [hΦform u, div_le_iff₀ (pow_pos (lt_of_lt_of_le hu0 hsn) 2)]
    have hX := pow_le_pow_left₀ (norm_nonneg _) (hlarge σ u hσ hσ' hu) 2
    have hq2 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    have hpow : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
    have hs2 : u ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 := pow_le_pow_left₀ hu0.le hsn 2
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * (Λ * u ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hX.trans (le_of_eq ?_)) (sq_nonneg _)
          rw [mul_pow, hq2]
      _ = Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) * u ^ 2 := by
          rw [← hpow]; ring
      _ ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) *
            ‖(σ : ℂ) + u * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
  -- the majorant on the half-line
  set G : ℝ → ℝ := fun u => if u ≤ T then g u
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  have hint2T : IntegrableOn
      (fun u : ℝ => ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) (Ioi T) :=
    hint2.mono_set (Ioi_subset_Ioi hT)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 T ∪ Ioi T := (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  have hGint : IntegrableOn G (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · exact hg.congr_fun (fun u hu => by simp only [G, if_pos hu.2]) measurableSet_Ioc
    · refine IntegrableOn.congr_fun (hint2T.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ T := not_le.mpr hu
      simp only [G, if_neg this]
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t₁ := compl_mem_ae_iff.mpr (measure_singleton t₁)
  have hΦle : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), Φ u ≤ G u := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (hne.mono fun u hu hpos => ?_)
    by_cases h2 : u ≤ T
    · simp only [G, if_pos h2]; exact hsmall σ u hσ hσ' hpos h2 hu
    · simp only [G, if_neg h2]; exact hlarge' u (not_le.mp h2)
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), G u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hGint hΦle
  have hGval : ∫ u in Ioi (0 : ℝ), G u = ∫ u in Ioc 0 T, g u +
      Λ * ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hGint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hGint.mono_set (by rw [hsplit]; exact subset_union_right))]
    congr 1
    · exact setIntegral_congr_fun measurableSet_Ioc (fun u hu => by simp only [G, if_pos hu.2])
    · rw [setIntegral_congr_fun
          (g := fun u : ℝ => Λ * (‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))))
          measurableSet_Ioi (fun u hu => by
            have : ¬ u ≤ T := not_le.mpr hu
            simp only [G, if_neg this]), integral_const_mul]
  have htail : ∫ u in Ioi T, ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) ≤ M₂ := by
    refine le_trans (setIntegral_mono_set hint2 ?_ (Ioi_subset_Ioi hT).eventuallyLE) hbound2
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [mem_Ioi.mp hu]) _)
  have heven : ∫ t : ℝ, Φ t = 2 * ∫ u in Ioi (0 : ℝ), Φ u := by
    rw [← integral_comp_abs]
    congr 1
    funext t
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hΦ, lineIntegrand_neg]
  rw [heven]
  have := mul_le_mul_of_nonneg_left htail hΛ
  linarith

/-! ### The paid range -/

theorem rpow_quarter_sixteen : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
  have h : (16 : ℝ) = 2 ^ ((4 : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_num
  rw [h, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `(1 + x)^{1/4} ≤ 2` for `0 ≤ x ≤ 15`. -/
theorem one_add_rpow_quarter_le_two {x : ℝ} (hx : 0 ≤ x) (hx15 : x ≤ 15) :
    (1 + x) ^ (1 / 4 : ℝ) ≤ 2 := by
  rw [← rpow_quarter_sixteen]; exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)

/-- `(1 + x)^{1/4} ≤ 2 x^{1/4}` for `x ≥ 1`. -/
theorem one_add_rpow_quarter_le {x : ℝ} (hx : 1 ≤ x) :
    (1 + x) ^ (1 / 4 : ℝ) ≤ 2 * x ^ (1 / 4 : ℝ) := by
  rw [← rpow_quarter_sixteen, ← Real.mul_rpow (by norm_num) (by linarith)]
  exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)

/-- **Nonpositive amplitudes are paid at every frequency**: for `−1 ≤ a ≤ 0` the half-damped
oscillating weight has bounded receiver. -/
theorem receiverBounded_oscWeight_nonpos {a : ℝ} (ha : -1 ≤ a) (ha0 : a ≤ 0) (t₀ : ℝ) :
    ReceiverBounded (oscWeight a t₀) := by
  have haa : |a| ≤ 1 := abs_le.mpr ⟨ha, by linarith⟩
  obtain ⟨K, hK, hinv⟩ := exists_inv_norm_zeta_le_uniform
  set P : ℝ := ∑' d : ℕ, oscWeight a t₀ d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  have hE2 : 0 < E2 := Real.exp_pos _
  have hK'0 : 0 < K * (1 + |t₀|) ^ (1 / 4 : ℝ) := by positivity
  set K' : ℝ := K * (1 + |t₀|) ^ (1 / 4 : ℝ)
  -- `|F(w)| ≤ E2 (1 + K' (1 + |Im w|)^{1/4})`: `F = e^{O(1)} Z^{a/2}`, `Z^{a/2} ≤ 1 + (1/Z)^{1/2}`
  have hF : ∀ w : ℂ, 1 < w.re → w.re ≤ 2 →
      ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        E2 * (1 + K' * (1 + |w.im|) ^ (1 / 4 : ℝ)) := by
    intro w hw hw2
    have hwm : 1 < (w - t₀ * I).re := by simpa using hw
    have hwp : 1 < (w + t₀ * I).re := by simpa using hw
    have hm := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwm.le)
    have hp := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hwp.le)
    have hY1 : 1 ≤ (1 + |t₀|) * (1 + |w.im|) := one_le_mul_of_one_le_of_one_le
      (by linarith [abs_nonneg t₀]) (by linarith [abs_nonneg w.im])
    set Y : ℝ := (1 + |t₀|) * (1 + |w.im|)
    have hY0 : 0 ≤ Y := by linarith
    have hshift : ∀ v : ℂ, v.re = w.re → |v.im| ≤ |w.im| + |t₀| →
        ‖riemannZeta v‖⁻¹ ≤ K * Y ^ (1 / 4 : ℝ) := by
      intro v hvre hvim
      refine (hinv v (by rw [hvre]; exact hw) (by rw [hvre]; exact hw2)).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ?_ (by norm_num)) hK.le
      have : 1 + |w.im| + |t₀| ≤ Y := by
        simp only [Y]; nlinarith [abs_nonneg t₀, abs_nonneg w.im]
      linarith
    have hm' := hshift (w - t₀ * I) (by simp) (by
      have him : (w - t₀ * I).im = w.im - t₀ := by simp
      rw [him, abs_le]
      constructor <;> linarith [neg_abs_le w.im, le_abs_self w.im, neg_abs_le t₀, le_abs_self t₀])
    have hp' := hshift (w + t₀ * I) (by simp) (by
      have him : (w + t₀ * I).im = w.im + t₀ := by simp
      rw [him, abs_le]
      constructor <;> linarith [neg_abs_le w.im, le_abs_self w.im, neg_abs_le t₀, le_abs_self t₀])
    set Zm := ‖riemannZeta (w - t₀ * I)‖
    set Zp := ‖riemannZeta (w + t₀ * I)‖
    have hX : (Zm * Zp)⁻¹ ≤ K ^ 2 * Y ^ (1 / 2 : ℝ) := by
      rw [mul_inv]
      calc Zm⁻¹ * Zp⁻¹ ≤ (K * Y ^ (1 / 4 : ℝ)) * (K * Y ^ (1 / 4 : ℝ)) :=
            mul_le_mul hm' hp' (inv_nonneg.mpr hp.le) (by positivity)
        _ = K ^ 2 * Y ^ (1 / 2 : ℝ) := by
            rw [show (1 / 2 : ℝ) = 1 / 4 + 1 / 4 by norm_num, Real.rpow_add (by linarith)]; ring
    have hXh : ((Zm * Zp)⁻¹) ^ (1 / 2 : ℝ) ≤ K * Y ^ (1 / 4 : ℝ) := by
      calc ((Zm * Zp)⁻¹) ^ (1 / 2 : ℝ) ≤ (K ^ 2 * Y ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hX (by norm_num)
        _ = K * Y ^ (1 / 4 : ℝ) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
              ← Real.rpow_mul hK.le, ← Real.rpow_mul hY0]
            norm_num
    have hpowX : (Zm * Zp) ^ (a / 2) = ((Zm * Zp)⁻¹) ^ (-(a / 2)) := by
      rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
    have hb := rpow_le_one_add_rpow_half (X := (Zm * Zp)⁻¹) (by positivity) (b := -(a / 2))
      (by linarith) (by linarith)
    have hYsplit : K * Y ^ (1 / 4 : ℝ) = K' * (1 + |w.im|) ^ (1 / 4 : ℝ) := by
      simp only [Y, K']; rw [Real.mul_rpow (by positivity) (by positivity)]; ring
    calc ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
        ≤ E2 * (Zm * Zp) ^ (a / 2) := (norm_oscSeries_le_ge haa t₀ hw).1
      _ ≤ E2 * (1 + K' * (1 + |w.im|) ^ (1 / 4 : ℝ)) := by
          rw [hpowX]
          refine mul_le_mul_of_nonneg_left ?_ hE2.le
          rw [← hYsplit]
          linarith
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hC : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      ‖weightDirichletSeries (oscWeight a t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        E2 * (1 + K' * (1 + |t|) ^ (1 / 4 : ℝ)) + |P| := by
    intro σ t hσ hσ'
    rw [weightDirichletSeries_oscWeight]
    refine (norm_sub_le _ _).trans (add_le_add ?_ (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have h := hF ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
    rwa [hwim] at h
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_bounds (c := oscWeight a t₀) (P := P)
    (B₀ := E2 * (1 + 2 * K') + |P|) (B₁ := E2 * (1 + 2 * K') + |P|)
    (fun σ t hσ hσ' ht => (hC σ t hσ hσ').trans (by
      have h2 := one_add_rpow_quarter_le_two (abs_nonneg t) (by linarith)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ E2 * K')
      nlinarith))
    (fun σ t hσ hσ' ht => (hC σ t hσ hσ').trans (by
      have h1 : 1 ≤ |t| ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have h2 := one_add_rpow_quarter_le (show 1 ≤ |t| by linarith)
      have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ E2 * K')
      have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ E2 + |P|)
      nlinarith))
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_oscWeight haa t₀) hM⟩

/-- **The small-height bound** (`0 ≤ a ≤ 1`, `t₀ > 0`): on `1 < Re w ≤ 2`, `0 < Im w ≤ 2t₀ + 2`,
`|F(w)| ≤ B |w − it₀ − 1|^{-a/2}`, from `|ζ(w − it₀)| ≲ 1/|w − it₀ − 1|` and `|ζ(w + it₀)| ≲ 1`. -/
theorem exists_norm_oscSeries_le_small {a t₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht₀ : 0 < t₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 0 < w.im → w.im ≤ 2 * t₀ + 2 →
      ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
        B * ‖w - t₀ * I - 1‖ ^ (-(a / 2)) := by
  have haa : |a| ≤ 1 := abs_le.mpr ⟨by linarith, ha1⟩
  obtain ⟨K₀, hK₀, hpole⟩ := exists_norm_zeta_mul_sub_one_le
  set T : ℝ := 2 * t₀ + 2
  have hT2 : 2 ≤ T := by simp only [T]; linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogTt : 0 ≤ Real.log (T + t₀) := Real.log_nonneg (by linarith)
  have hKz : 0 < K₀ + (1 + T) * (Real.log T + 5) := by positivity
  have hKp : 0 < K₀ / t₀ + Real.log (T + t₀) + 5 := by positivity
  set Kz : ℝ := K₀ + (1 + T) * (Real.log T + 5)
  set Kp : ℝ := K₀ / t₀ + Real.log (T + t₀) + 5
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  refine ⟨E2 * (Kz * Kp) ^ (a / 2), by positivity, fun w hw hw2 ht htT => ?_⟩
  have hwmre : (w - t₀ * I).re = w.re := by simp
  have hwmim : (w - t₀ * I).im = w.im - t₀ := by simp
  have hwpre : (w + t₀ * I).re = w.re := by simp
  have hwpim : (w + t₀ * I).im = w.im + t₀ := by simp
  have hd : 0 < ‖w - t₀ * I - 1‖ := by
    refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm (w - t₀ * I - 1))
    rw [Complex.sub_re, hwmre, Complex.one_re, abs_of_pos (by linarith)]; linarith
  -- `|ζ(w − it₀)| ≤ Kz/|w − it₀ − 1|`
  have hZm : ‖riemannZeta (w - t₀ * I)‖ ≤ Kz / ‖w - t₀ * I - 1‖ := by
    rw [le_div_iff₀ hd]
    rcases le_total |(w - t₀ * I).im| 2 with h2 | h2
    · have := hpole (w - t₀ * I) (by rw [hwmre]; exact hw) (by rw [hwmre]; exact hw2) h2
      have : 0 ≤ (1 + T) * (Real.log T + 5) := by positivity
      linarith
    · have hlog := RHTower.norm_riemannZeta_le_log_add (s := w - t₀ * I) (by rw [hwmre]; linarith)
        (by rw [hwmre]; exact hw2) h2
      have hτT : |(w - t₀ * I).im| ≤ T := by
        rw [hwmim, abs_le]; constructor <;> linarith
      have hlt : Real.log |(w - t₀ * I).im| ≤ Real.log T := Real.log_le_log (by linarith) hτT
      have hdn : ‖w - t₀ * I - 1‖ ≤ 1 + T := by
        calc ‖w - t₀ * I - 1‖ ≤ |(w - t₀ * I - 1).re| + |(w - t₀ * I - 1).im| :=
              Complex.norm_le_abs_re_add_abs_im _
          _ ≤ 1 + T := by
            rw [Complex.sub_re, Complex.sub_im, hwmre, Complex.one_re, Complex.one_im, sub_zero,
              abs_of_pos (by linarith)]
            linarith
      calc ‖riemannZeta (w - t₀ * I)‖ * ‖w - t₀ * I - 1‖ ≤ (Real.log T + 5) * (1 + T) :=
            mul_le_mul (by linarith) hdn (norm_nonneg _) (by linarith)
        _ ≤ Kz := by simp only [Kz]; linarith
  -- `|ζ(w + it₀)| ≤ Kp`
  have hZp : ‖riemannZeta (w + t₀ * I)‖ ≤ Kp := by
    rcases le_total (w + t₀ * I).im 2 with h2 | h2
    · have hpos : 0 < (w + t₀ * I).im := by rw [hwpim]; linarith
      have hb := hpole (w + t₀ * I) (by rw [hwpre]; exact hw) (by rw [hwpre]; exact hw2)
        (by rw [abs_of_pos hpos]; exact h2)
      have hge : t₀ ≤ ‖w + t₀ * I - 1‖ := by
        have := Complex.abs_im_le_norm (w + t₀ * I - 1)
        rw [Complex.sub_im, Complex.one_im, sub_zero, hwpim, abs_of_pos (by linarith)] at this
        linarith
      have h3 : ‖riemannZeta (w + t₀ * I)‖ ≤ K₀ / t₀ := by
        rw [le_div_iff₀ ht₀]
        calc ‖riemannZeta (w + t₀ * I)‖ * t₀ ≤ ‖riemannZeta (w + t₀ * I)‖ * ‖w + t₀ * I - 1‖ :=
              mul_le_mul_of_nonneg_left hge (norm_nonneg _)
          _ ≤ K₀ := hb
      simp only [Kp]; linarith
    · have hlog := RHTower.norm_riemannZeta_le_log_add (s := w + t₀ * I) (by rw [hwpre]; linarith)
        (by rw [hwpre]; exact hw2) (by rw [abs_of_pos (by linarith)]; exact h2)
      rw [abs_of_pos (by linarith)] at hlog
      have hlt : Real.log (w + t₀ * I).im ≤ Real.log (T + t₀) :=
        Real.log_le_log (by linarith) (by rw [hwpim]; linarith)
      have : 0 ≤ K₀ / t₀ := by positivity
      simp only [Kp]; linarith
  have hprod : ‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖ ≤
      Kz * Kp / ‖w - t₀ * I - 1‖ := by
    calc _ ≤ Kz / ‖w - t₀ * I - 1‖ * Kp := mul_le_mul hZm hZp (norm_nonneg _) (by positivity)
      _ = Kz * Kp / ‖w - t₀ * I - 1‖ := by ring
  calc ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ E2 * (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) :=
        (norm_oscSeries_le_ge haa t₀ hw).1
    _ ≤ E2 * (Kz * Kp / ‖w - t₀ * I - 1‖) ^ (a / 2) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hprod (by linarith))
          (Real.exp_pos _).le
    _ = E2 * (Kz * Kp) ^ (a / 2) * ‖w - t₀ * I - 1‖ ^ (-(a / 2)) := by
        rw [Real.div_rpow (by positivity) hd.le, Real.rpow_neg hd.le]; ring

/-- **The large-height bound** (`0 ≤ a ≤ 1`, `t₀ > 0`): for `Im w > 2t₀ + 2`,
`|F(w)| ≤ 10 e^{2S} (Im w)^{1/4}`. -/
theorem norm_oscSeries_le_large {a t₀ : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht₀ : 0 < t₀) {w : ℂ}
    (hw : 1 < w.re) (hw2 : w.re ≤ 2) (ht : 2 * t₀ + 2 < w.im) :
    ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      10 * Real.exp (2 * primeSquareMass) * w.im ^ (1 / 4 : ℝ) := by
  have haa : |a| ≤ 1 := abs_le.mpr ⟨by linarith, ha1⟩
  have ht0 : 0 < w.im := by linarith
  have hwmre : (w - t₀ * I).re = w.re := by simp
  have hwmim : (w - t₀ * I).im = w.im - t₀ := by simp
  have hwpre : (w + t₀ * I).re = w.re := by simp
  have hwpim : (w + t₀ * I).im = w.im + t₀ := by simp
  have hm : ‖riemannZeta (w - t₀ * I)‖ ≤ Real.log w.im + 6 := by
    have h := RHTower.norm_riemannZeta_le_log_add (s := w - t₀ * I) (by rw [hwmre]; linarith)
      (by rw [hwmre]; exact hw2) (by rw [hwmim, abs_of_pos (by linarith)]; linarith)
    rw [hwmim, abs_of_pos (by linarith)] at h
    have := Real.log_le_log (by linarith) (show w.im - t₀ ≤ w.im by linarith)
    linarith
  have hp : ‖riemannZeta (w + t₀ * I)‖ ≤ Real.log w.im + 6 := by
    have h := RHTower.norm_riemannZeta_le_log_add (s := w + t₀ * I) (by rw [hwpre]; linarith)
      (by rw [hwpre]; exact hw2) (by rw [hwpim, abs_of_pos (by linarith)]; linarith)
    rw [hwpim, abs_of_pos (by linarith)] at h
    have h2 : Real.log (w.im + t₀) ≤ Real.log (2 * w.im) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) ht0.ne'] at h2
    have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hL1 : 1 ≤ Real.log w.im + 6 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ w.im by linarith); linarith
  have hprod : (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) ≤
      Real.log w.im + 6 := by
    calc _ ≤ ((Real.log w.im + 6) * (Real.log w.im + 6)) ^ (a / 2) :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul hm hp (norm_nonneg _) (by linarith))
            (by linarith)
      _ = (Real.log w.im + 6) ^ a := by
          rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1; push_cast; ring
      _ ≤ (Real.log w.im + 6) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 ha1
      _ = Real.log w.im + 6 := Real.rpow_one _
  have hlog : Real.log w.im + 6 ≤ 10 * w.im ^ (1 / 4 : ℝ) := by
    have h1 : 1 ≤ w.im ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have h2 : Real.log w.im ≤ 4 * w.im ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div ht0.le (show (0 : ℝ) < 1 / 4 by norm_num); linarith
    linarith
  calc ‖∑' n : ℕ, (oscPattern a t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
      ≤ Real.exp (2 * primeSquareMass) *
          (‖riemannZeta (w - t₀ * I)‖ * ‖riemannZeta (w + t₀ * I)‖) ^ (a / 2) :=
        (norm_oscSeries_le_ge haa t₀ hw).1
    _ ≤ Real.exp (2 * primeSquareMass) * (10 * w.im ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hprod.trans hlog) (Real.exp_pos _).le
    _ = 10 * Real.exp (2 * primeSquareMass) * w.im ^ (1 / 4 : ℝ) := by ring

/-- **Amplitudes in `(0, 1)` are paid at positive frequency**: the singularity
`|C(1/2 + u + it)|² ≲ |t − t₀|^{-a}` at the height `t₀` is integrable. -/
theorem receiverBounded_oscWeight_pos_of_lt_one {a t₀ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht₀ : 0 < t₀) : ReceiverBounded (oscWeight a t₀) := by
  have haa : |a| ≤ 1 := abs_le.mpr ⟨by linarith, ha1.le⟩
  obtain ⟨B, hB0, hBs⟩ := exists_norm_oscSeries_le_small ha0.le ha1.le ht₀
  set T : ℝ := 2 * t₀ + 2
  have hT : 2 ≤ T := by simp only [T]; linarith
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set P : ℝ := ∑' d : ℕ, oscWeight a t₀ d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  have hE2 : 0 < E2 := Real.exp_pos _
  have hA0 : 0 ≤ 8 * Z₀ ^ 2 * (B ^ 2 + P ^ 2) := by positivity
  set A : ℝ := 8 * Z₀ ^ 2 * (B ^ 2 + P ^ 2)
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  have hg : IntegrableOn (fun t : ℝ => A * (|t - t₀| ^ (-a) + 1)) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      (((intervalIntegrable_abs_sub_rpow (by linarith) t₀ 0 T).add
        intervalIntegrable_const).const_mul A)
  have hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < t → t ≤ T → t ≠ t₀ →
      lineIntegrand (oscWeight a t₀) P σ t ≤ A * (|t - t₀| ^ (-a) + 1) := by
    intro σ t hσ hσ' ht htT hne
    have hF := hBs ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
      (by rw [hwim]; exact ht) (by rw [hwim]; exact htT)
    have hτ : |t - t₀| ≤ ‖(σ : ℂ) + t * I + 1 / 2 - t₀ * I - 1‖ := by
      have := Complex.abs_im_le_norm ((σ : ℂ) + t * I + 1 / 2 - t₀ * I - 1)
      have him : ((σ : ℂ) + t * I + 1 / 2 - t₀ * I - 1).im = t - t₀ := by simp
      rwa [him] at this
    have hτ0 : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hpow : ‖(σ : ℂ) + t * I + 1 / 2 - t₀ * I - 1‖ ^ (-(a / 2)) ≤ |t - t₀| ^ (-(a / 2)) :=
      Real.rpow_le_rpow_of_nonpos hτ0 hτ (by linarith)
    have hC : ‖weightDirichletSeries (oscWeight a t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        B * |t - t₀| ^ (-(a / 2)) + |P| := by
      rw [weightDirichletSeries_oscWeight]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (by rw [Complex.norm_real, Real.norm_eq_abs]))
      exact hF.trans (mul_le_mul_of_nonneg_left hpow hB0)
    have hζs := hZ σ t hσ.le hσ'.le (by rw [abs_of_pos ht]; exact htT)
    have hsn : σ ≤ ‖(σ : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + t * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + t * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + t * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    have hpw : (|t - t₀| ^ (-(a / 2))) ^ 2 = |t - t₀| ^ (-a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; congr 1; push_cast; ring
    have hsq : ‖weightDirichletSeries (oscWeight a t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 ≤
        2 * (B ^ 2 * |t - t₀| ^ (-a)) + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hC 2
      have hab : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
        nlinarith [sq_nonneg (x - y)]
      refine h.trans ((hab _ _).trans (le_of_eq ?_))
      rw [mul_pow, hpw, sq_abs]
    have hzsq : ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζs 2
    have hX0 : 0 ≤ |t - t₀| ^ (-a) := Real.rpow_nonneg (abs_nonneg _) _
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    have key : A * (|t - t₀| ^ (-a) + 1) * (1 / 2) ^ 2 -
        Z₀ ^ 2 * (2 * (B ^ 2 * |t - t₀| ^ (-a)) + 2 * P ^ 2) =
          2 * Z₀ ^ 2 * B ^ 2 + 2 * Z₀ ^ 2 * P ^ 2 * |t - t₀| ^ (-a) := by
      simp only [A]; ring
    have hkey0 : 0 ≤ 2 * Z₀ ^ 2 * B ^ 2 + 2 * Z₀ ^ 2 * P ^ 2 * |t - t₀| ^ (-a) := by positivity
    calc ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
          ‖weightDirichletSeries (oscWeight a t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * (2 * (B ^ 2 * |t - t₀| ^ (-a)) + 2 * P ^ 2) :=
          mul_le_mul hzsq hsq (sq_nonneg _) (sq_nonneg _)
      _ ≤ A * (|t - t₀| ^ (-a) + 1) * (1 / 2) ^ 2 := by linarith
      _ ≤ A * (|t - t₀| ^ (-a) + 1) * ‖(σ : ℂ) + t * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (mul_nonneg hA0 (by positivity))
  have hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < t →
      ‖weightDirichletSeries (oscWeight a t₀) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        (10 * E2 + |P|) * t ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    rw [weightDirichletSeries_oscWeight]
    refine (norm_sub_le _ _).trans ?_
    have h := norm_oscSeries_le_large ha0.le ha1.le ht₀ (w := (σ : ℂ) + t * I + 1 / 2)
      (by rw [hwre]; linarith) (by rw [hwre]; linarith) (by rw [hwim]; exact ht)
    rw [hwim] at h
    have h1 : 1 ≤ t ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs]
    nlinarith [abs_nonneg P]
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant hT hg hsmall hlarge
  exact ⟨3 * M / (4 * Real.pi),
    weightPronicEnergy_le_of_lineEnergy_le (dampedClass_oscWeight haa t₀) hM⟩

/-- **Every amplitude below one is paid off the real frequency**: for `−1 ≤ a < 1` and `t₀ ≠ 0`
the half-damped oscillating weight has bounded receiver. -/
theorem receiverBounded_oscWeight_of_lt_one {a t₀ : ℝ} (ha : -1 ≤ a) (ha1 : a < 1)
    (ht₀ : t₀ ≠ 0) : ReceiverBounded (oscWeight a t₀) := by
  rcases le_or_lt a 0 with ha0 | ha0
  · exact receiverBounded_oscWeight_nonpos ha ha0 t₀
  rcases lt_or_gt_of_ne ht₀ with hneg | hpos
  · rw [← oscWeight_neg a t₀]
    exact receiverBounded_oscWeight_pos_of_lt_one ha0 ha1 (by linarith)
  · exact receiverBounded_oscWeight_pos_of_lt_one ha0 ha1 hpos

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
