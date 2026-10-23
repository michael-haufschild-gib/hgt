import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticWeightedZeta
import GaloisForLFunctions.RHTower.ZetaVerticalLineBound

/-!
# The quarter law for the constant-sign model

Let `f_z(n) = z^{Ω(n)}` — the completely multiplicative pattern taking the value `z ∈ [0, 1]` at
every prime, the mean-field model of a sign pattern whose flipped primes have density
`δ = (1 − z)/2`. Its Dirichlet series behaves like `ζ^z` near `s = 1`. The half-damped weight
`c_z(d) = f_z(d) d^{-1/2}` is paid **if and only if** `z < 1/2`, that is `δ > 1/4`:

* `receiverBounded_constantSign` (`0 ≤ z < 1/2`): by the boundary-energy identity the receiver is
  the line energy of `ζ(s)(F_z(s + 1/2) − m)/s`; the Euler product gives
  `|F_z(w)| ≤ e^{2S}|ζ(w)|^z` on `Re w > 1`; near `w = 1` this is `O(|Im w|^{-z})`, square integrable
  exactly because `2z < 1`, and at height `|t| ≥ 2` it is `O(log |t|)`, paid by the dyadic mean
  square of `ζ` on the strip.
* `not_receiverBounded_constantSign` (`1/2 < z ≤ 1`): `F_z(w) ≥ e^{-S}(w − 1)^{-z}` on real `w > 1`
  against the general pole law's cap `O((σ − 1/2)^{-1/2})`.
* `not_receiverBounded_constantSign_half` (`z = 1/2`, where the real-axis pole law is saturated):
  `|F_{1/2}(w)|² ≥ e^{-4S}|ζ(w)| ≥ e^{-4S}/(2|w − 1|)` off the axis, so the line energy at
  `σ = 1/2 + u` exceeds `κ log(1/u) − O(1)`, while a paid receiver caps it by `4πE`.

The threshold is the square integrability of `|w − 1|^{-z}` on the line `Re w = 1`: the receiver
reads the order of the weight's singularity at `s = 1`, and the parity barrier's critical density
`1/4` is the order `1/2`.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The model and its Euler product -/

/-- The constant-sign model `n ↦ z^{Ω(n)}` (and `0` at `0`). -/
def constantSignHom (z : ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else z ^ ArithmeticFunction.cardFactors n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [mul_ne_zero hm hn, hm, hn, if_false, ArithmeticFunction.cardFactors_mul hm hn,
      pow_add]

theorem constantSignHom_prime (z : ℝ) {p : ℕ} (hp : p.Prime) : constantSignHom z p = z := by
  simp [constantSignHom, hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp]

/-- The complex weighted pattern `n ↦ f(n) n^{-w}`. -/
def cweightedPatternHom (f : ℕ →*₀ ℝ) (w : ℂ) : ℕ →*₀ ℂ where
  toFun n := (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)
  map_zero' := by
    simp only [map_zero, Complex.ofReal_zero, zero_mul]
  map_one' := by simp
  map_mul' m n := by
    rw [map_mul, Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring

/-- One Euler factor: `|Re(−log(1 − zy)) − z Re(−log(1 − y))| ≤ 2|y|²` for `|y| ≤ 1/2`, from
`log(1 − v) = −v + O(|v|²)` at `v = zy` and `v = y`. -/
theorem abs_re_neg_log_one_sub_mul_sub_le {z : ℝ} (hz : |z| ≤ 1) {y : ℂ}
    (hy : ‖y‖ ≤ 1 / 2) :
    |(-Complex.log (1 - z * y)).re - z * (-Complex.log (1 - y)).re| ≤ 2 * ‖y‖ ^ 2 := by
  have hzy : ‖-((z : ℂ) * y)‖ ≤ ‖y‖ := by
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) hz
  have hy1 : ‖-y‖ < 1 := by rw [norm_neg]; linarith
  have hzy1 : ‖-((z : ℂ) * y)‖ < 1 := by linarith
  have h1 := Complex.norm_log_one_add_sub_self_le hzy1
  have h2 := Complex.norm_log_one_add_sub_self_le hy1
  have hb : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 ≤ ‖u‖ ^ 2 := by
    intro u hu
    have hpos : 0 < 1 - ‖u‖ := by linarith
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hinv : (1 - ‖u‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    nlinarith [sq_nonneg ‖u‖]
  have h1' : ‖Complex.log (1 - z * y) + z * y‖ ≤ ‖y‖ ^ 2 := by
    have := h1.trans (hb _ (hzy.trans hy))
    rw [← sub_eq_add_neg, sub_neg_eq_add] at this
    exact this.trans (pow_le_pow_left₀ (norm_nonneg _) hzy 2)
  have h2' : ‖Complex.log (1 - y) + y‖ ≤ ‖y‖ ^ 2 := by
    have := h2.trans (hb _ (by rw [norm_neg]; exact hy))
    rw [← sub_eq_add_neg, sub_neg_eq_add, norm_neg] at this
    exact this
  have r1 := (Complex.abs_re_le_norm (Complex.log (1 - z * y) + z * y)).trans h1'
  have r2 := (Complex.abs_re_le_norm (Complex.log (1 - y) + y)).trans h2'
  have hre : ((z : ℂ) * y).re = z * y.re := by simp
  simp only [Complex.add_re] at r1 r2
  rw [hre] at r1
  simp only [Complex.neg_re]
  -- `−a + z b = −(a + z Y) + z (b + Y)` with both brackets `O(|y|²)`
  have hz2 : |z * ((Complex.log (1 - y)).re + y.re)| ≤ ‖y‖ ^ 2 := by
    rw [abs_mul]
    exact (mul_le_mul hz r2 (abs_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
  calc |-(Complex.log (1 - z * y)).re - z * -(Complex.log (1 - y)).re|
      = |-((Complex.log (1 - z * y)).re + z * y.re) + z * ((Complex.log (1 - y)).re + y.re)| := by
        congr 1; ring
    _ ≤ |-((Complex.log (1 - z * y)).re + z * y.re)| + |z * ((Complex.log (1 - y)).re + y.re)| :=
        abs_add_le _ _
    _ ≤ 2 * ‖y‖ ^ 2 := by rw [abs_neg]; linarith

/-- The prime constant `S = Σ_p p^{-2}`. -/
def primeSquareMass : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)

theorem summable_primeSquare : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
  Nat.Primes.summable_rpow.mpr (by norm_num)

/-- **The Euler exponents of the constant-sign model.** On `Re w > 1`,
`|F_z(w)| = e^L` and `|ζ(w)| = e^Z` with `|L − zZ| ≤ 2S`, `S = Σ_p p^{-2}`. -/
theorem exists_constantSignSeries_exponents {z : ℝ} (hz : |z| ≤ 1) {w : ℂ}
    (hw : 1 < w.re) :
    ∃ L Z : ℝ, ‖∑' n : ℕ, (constantSignHom z n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ = Real.exp L ∧
      ‖riemannZeta w‖ = Real.exp Z ∧ |L - z * Z| ≤ 2 * primeSquareMass := by
  set g := cweightedPatternHom (constantSignHom z) w
  have habs : ∀ n, |constantSignHom z n| ≤ 1 := by
    intro n
    simp only [constantSignHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
    split_ifs
    · simp
    · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg z) hz
  have hsum : Summable (fun n => ‖g n‖) := by
    refine (Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)).of_nonneg_of_le
      (fun _ => norm_nonneg _) fun n => ?_
    simp only [g, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -w.re ≠ 0 by intro h; linarith)]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _) (habs n)
  have hE := EulerProduct.exp_tsum_primes_log_eq_tsum hsum
  have hZ := riemannZeta_eulerProduct_exp_log hw
  set y : Nat.Primes → ℂ := fun p => ((p : ℕ) : ℂ) ^ (-w)
  have hgy : ∀ p : Nat.Primes, g p = (z : ℂ) * y p := fun p => by
    simp only [g, y, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      constantSignHom_prime z p.2, Complex.ofReal_natCast]
  have hnorm_y : ∀ p : Nat.Primes, ‖y p‖ = ((p : ℕ) : ℝ) ^ (-w.re) := fun p => by
    simp only [y]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (by exact_mod_cast p.2.pos), Complex.neg_re]
  have hyhalf : ∀ p : Nat.Primes, ‖y p‖ ≤ 1 / 2 := fun p => by
    rw [hnorm_y]
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    calc ((p : ℕ) : ℝ) ^ (-w.re) ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hys : Summable y := by
    refine (Nat.Primes.summable_rpow.mpr (show -w.re < -1 by linarith)).of_norm_bounded fun p => ?_
    rw [hnorm_y]
  have hgs : Summable (fun p : Nat.Primes => g p) := by
    simp_rw [hgy]; exact hys.mul_left _
  have hL1 : Summable (fun p : Nat.Primes => -Complex.log (1 - g p)) := hgs.clog_one_sub.neg
  have hL2 : Summable (fun p : Nat.Primes => -Complex.log (1 - y p)) := hys.clog_one_sub.neg
  have hF : ‖∑' n, g n‖ = Real.exp (∑' p : Nat.Primes, (-Complex.log (1 - g p)).re) := by
    rw [← hE, Complex.norm_exp, Complex.re_tsum hL1]
  have hζ : ‖riemannZeta w‖ = Real.exp (∑' p : Nat.Primes, (-Complex.log (1 - y p)).re) := by
    rw [← hZ, Complex.norm_exp, Complex.re_tsum hL2]
  have hsq : Summable (fun p : Nat.Primes => ‖y p‖ ^ 2) :=
    summable_primeSquare.of_nonneg_of_le (fun _ => sq_nonneg _) fun p => by
      rw [hnorm_y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)
  have hsqS : ∑' p : Nat.Primes, ‖y p‖ ^ 2 ≤ primeSquareMass :=
    Summable.tsum_le_tsum (fun p => by
      rw [hnorm_y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
      exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)) hsq summable_primeSquare
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - g p)).re) :=
    Complex.reCLM.summable hL1
  have hre2 : Summable (fun p : Nat.Primes => (-Complex.log (1 - y p)).re) :=
    Complex.reCLM.summable hL2
  refine ⟨_, _, hF, hζ, ?_⟩
  have hterm : ∀ p : Nat.Primes,
      ‖(-Complex.log (1 - g p)).re - z * (-Complex.log (1 - y p)).re‖ ≤ 2 * ‖y p‖ ^ 2 :=
    fun p => by
      rw [Real.norm_eq_abs, hgy]; exact abs_re_neg_log_one_sub_mul_sub_le hz (hyhalf p)
  have hdiff := hre1.sub (hre2.mul_left z)
  rw [← tsum_mul_left, ← hre1.tsum_sub (hre2.mul_left z), ← Real.norm_eq_abs]
  calc ‖∑' p : Nat.Primes, ((-Complex.log (1 - g p)).re - z * (-Complex.log (1 - y p)).re)‖
      ≤ ∑' p : Nat.Primes, ‖(-Complex.log (1 - g p)).re - z * (-Complex.log (1 - y p)).re‖ :=
        norm_tsum_le_tsum_norm hdiff.norm
    _ ≤ ∑' p : Nat.Primes, 2 * ‖y p‖ ^ 2 :=
        Summable.tsum_le_tsum hterm hdiff.norm (hsq.mul_left 2)
    _ ≤ 2 * primeSquareMass := by rw [tsum_mul_left]; linarith

/-- **The Euler bound of the constant-sign model**: `|F_z(w)| ≤ e^{2S} |ζ(w)|^z` on `Re w > 1`. -/
theorem norm_constantSignSeries_le {z : ℝ} (hz : |z| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    ‖∑' n : ℕ, (constantSignHom z n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      Real.exp (2 * primeSquareMass) * ‖riemannZeta w‖ ^ z := by
  obtain ⟨L, Z, hL, hZ, hLZ⟩ := exists_constantSignSeries_exponents hz hw
  rw [hL, hZ, ← Real.exp_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hLZ).2])

/-- **The reverse Euler bound**: `|F_z(w)| ≥ e^{-2S} |ζ(w)|^z` on `Re w > 1`. -/
theorem norm_constantSignSeries_ge {z : ℝ} (hz : |z| ≤ 1) {w : ℂ} (hw : 1 < w.re) :
    Real.exp (-(2 * primeSquareMass)) * ‖riemannZeta w‖ ^ z ≤
      ‖∑' n : ℕ, (constantSignHom z n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ := by
  obtain ⟨L, Z, hL, hZ, hLZ⟩ := exists_constantSignSeries_exponents hz hw
  rw [hL, hZ, ← Real.exp_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp hLZ).1])

/-! ### The model's half-damped weight -/

theorem abs_constantSignHom_le {z : ℝ} (hz : |z| ≤ 1) (n : ℕ) :
    |constantSignHom z n| ≤ 1 := by
  simp only [constantSignHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  split_ifs
  · simp
  · rw [abs_pow]; exact pow_le_one₀ (abs_nonneg z) hz

/-- The half-damped weight `f_z(d) d^{-1/2}` of the constant-sign model. -/
def constantSignWeight (z : ℝ) (d : ℕ) : ℝ := constantSignHom z d * (d : ℝ) ^ (-(1 / 2 : ℝ))

theorem dampedClass_constantSignWeight {z : ℝ} (hz : |z| ≤ 1) :
    DampedClass 1 (1 / 2) (constantSignWeight z) := fun d => by
  rw [constantSignWeight, one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (abs_constantSignHom_le hz d)

/-- The weight's Dirichlet series is the model's series at `s + 1/2`. -/
theorem weightDirichletSeries_constantSignWeight (z : ℝ) (s : ℂ) :
    weightDirichletSeries (constantSignWeight z) s =
      ∑' n : ℕ, (constantSignHom z n : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [constantSignWeight]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [constantSignWeight, Complex.ofReal_mul, Complex.ofReal_cpow hd0.le, mul_assoc,
    ← Complex.cpow_add _ _ hdC]
  congr 2
  push_cast
  ring

/-! ### Bounds on `ζ` near `Re s = 1` and on the critical box -/

/-- `|ζ(w)| · |Im w| ≤ K₀` for `1 < Re w ≤ 2`, `|Im w| ≤ 2`. -/
theorem exists_norm_zeta_mul_im_le :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → |w.im| ≤ 2 →
      ‖riemannZeta w‖ * |w.im| ≤ K₀ := by
  obtain ⟨C, hC, hbound⟩ := RHTower.exists_norm_zetaPoleCleared_le
  refine ⟨12 * C, by positivity, fun w hw hw2 ht => ?_⟩
  have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have hζ : riemannZeta w = RHTower.zetaPoleCleared w * w / (w - 1) := by
    rw [RHTower.zetaPoleCleared_eq hw1]; field_simp
  have him : |w.im| ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1); simpa using this
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
  rw [hζ, norm_div, norm_mul]
  calc ‖RHTower.zetaPoleCleared w‖ * ‖w‖ / ‖w - 1‖ * |w.im|
      ≤ ‖RHTower.zetaPoleCleared w‖ * ‖w‖ / ‖w - 1‖ * ‖w - 1‖ :=
        mul_le_mul_of_nonneg_left him (by positivity)
    _ = ‖RHTower.zetaPoleCleared w‖ * ‖w‖ := by field_simp
    _ ≤ (3 * C) * 4 := mul_le_mul hpc' hwn (norm_nonneg _) (by positivity)
    _ = 12 * C := by ring

/-- `ζ` is bounded on the box `1/2 ≤ σ ≤ 3/4`, `|t| ≤ 2`. -/
theorem exists_norm_zeta_le_on_box :
    ∃ Z₀ : ℝ, 0 ≤ Z₀ ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 4 → |t| ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ Z₀ := by
  set K : Set ℂ := (Icc (1 / 2 : ℝ) (3 / 4)) ×ℂ (Icc (-2 : ℝ) 2)
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

/-! ### The uniform dyadic bound -/

/-- `∫_{t > 2} |ζ(σ + it)|² t^{-3/2} dt` is bounded uniformly in `1/2 ≤ σ ≤ 3`. -/
theorem exists_integral_zeta_sq_rpow_le :
    ∃ M₂ : ℝ, ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      IntegrableOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 * t ^ (-(3 / 2 : ℝ))) (Ioi 2) ∧
      ∫ t in Ioi (2 : ℝ), ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 * t ^ (-(3 / 2 : ℝ)) ≤ M₂ := by
  obtain ⟨C, hC, hmoment⟩ := RHTower.exists_integral_normSq_zeta_vertical_le
  set q : ℝ := 2 ^ (-(1 / 2 : ℝ))
  have hq0 : 0 ≤ q := by positivity
  have hq1 : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeom : Summable (fun k : ℕ => 8 * C * ((k + 1 : ℕ) : ℝ) ^ 3 * q ^ (k + 1)) := by
    have h := ((summable_nat_add_iff 1).mpr
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 3 hq1)).mul_left (8 * C)
    simpa only [mul_assoc] using h
  refine ⟨∑' k : ℕ, 8 * C * ((k + 1 : ℕ) : ℝ) ^ 3 * q ^ (k + 1), fun σ hσ hσ3 => ?_⟩
  set F : ℝ → ℝ := fun t => ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2
  have hFc : ContinuousOn F (Ici 2) :=
    (RHTower.WeilSingularArithmetic.continuousOn_norm_zeta_positive_line σ).pow 2
  have hint : IntegrableOn (fun t : ℝ => F t * t ^ (-1 - 1 / 2 : ℝ)) (Ici 2) :=
    RHTower.WeilSingularArithmetic.integrableOn_mul_rpow_of_dyadic_logCube hFc
      (fun _ => sq_nonneg _) hC.le (by norm_num) fun T hT => hmoment T hT σ hσ hσ3
  have hexp : (-1 - 1 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [hexp] at hint
  have hintI : IntegrableOn (fun t : ℝ => F t * t ^ (-(3 / 2 : ℝ))) (Ioi 2) :=
    hint.mono_set Ioi_subset_Ici_self
  refine ⟨hintI, ?_⟩
  -- the blocks `[2^{k+1}, 2^{k+2}]`
  set a : ℕ → ℝ := fun k => (2 : ℝ) ^ (k + 1)
  have ha2 : ∀ k, (2 : ℝ) ≤ a k := fun k => by
    simp only [a]; exact le_self_pow₀ (by norm_num) (by omega)
  have hblockI : ∀ k, IntervalIntegrable (fun t : ℝ => F t * t ^ (-(3 / 2 : ℝ))) volume (a k) (a (k + 1)) :=
    fun k => by
      have hle : a k ≤ a (k + 1) := by simp only [a]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mpr (hintI.mono_set ?_)
      exact fun t ht => lt_of_le_of_lt (ha2 k) ht.1
  have hblock : ∀ k, ∫ t in a k..a (k + 1), F t * t ^ (-(3 / 2 : ℝ)) ≤
      8 * C * ((k + 1 : ℕ) : ℝ) ^ 3 * q ^ (k + 1) := by
    intro k
    set T := a k
    have hT2 : 2 ≤ T := ha2 k
    have hT0 : 0 < T := by linarith
    have haT : a (k + 1) = 2 * T := by simp only [a, T]; ring
    rw [haT]
    have hFint : IntervalIntegrable F volume T (2 * T) :=
      (hFc.mono fun t ht => by
        rw [uIcc_of_le (by linarith)] at ht; exact hT2.trans ht.1).intervalIntegrable
    have hle : ∫ t in T..(2 * T), F t * t ^ (-(3 / 2 : ℝ)) ≤
        ∫ t in T..(2 * T), F t * T ^ (-(3 / 2 : ℝ)) := by
      refine intervalIntegral.integral_mono_on (by linarith) (by simpa [haT] using hblockI k)
        (hFint.mul_const _) fun t ht => ?_
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hT0 ht.1 (by norm_num))
        (sq_nonneg _)
    rw [intervalIntegral.integral_mul_const] at hle
    have hm := hmoment T hT2 σ hσ hσ3
    have hpow : T * T ^ (-(3 / 2 : ℝ)) = q ^ (k + 1) := by
      have h1 : T * T ^ (-(3 / 2 : ℝ)) = T ^ (-(1 / 2 : ℝ)) := by
        nth_rw 1 [← Real.rpow_one T]; rw [← Real.rpow_add hT0]; norm_num
      rw [h1]
      simp only [T, a, q]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      ring_nf
    have hlog : (1 + Real.log T) ^ 3 ≤ (2 * ((k + 1 : ℕ) : ℝ)) ^ 3 := by
      apply pow_le_pow_left₀
      · have := Real.log_nonneg (show 1 ≤ T by linarith); linarith
      · simp only [T, a]
        rw [Real.log_pow]
        have hl2 : Real.log 2 < 1 := by
          have := Real.log_two_lt_d9; linarith
        have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
        push_cast at hk ⊢
        nlinarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num)]
    calc ∫ t in T..(2 * T), F t * t ^ (-(3 / 2 : ℝ))
        ≤ (∫ t in T..(2 * T), F t) * T ^ (-(3 / 2 : ℝ)) := hle
      _ ≤ (C * T * (1 + Real.log T) ^ 3) * T ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
      _ = C * (1 + Real.log T) ^ 3 * (T * T ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ C * (2 * ((k + 1 : ℕ) : ℝ)) ^ 3 * q ^ (k + 1) := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC.le) (by positivity)
      _ = 8 * C * ((k + 1 : ℕ) : ℝ) ^ 3 * q ^ (k + 1) := by ring
  -- telescoping and the limit
  have hb : Tendsto (fun N : ℕ => a N) atTop atTop := by
    simp only [a]
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_add_atTop_nat 1)
  have hlim := intervalIntegral_tendsto_integral_Ioi 2 hintI hb
  refine le_of_tendsto hlim (Eventually.of_forall fun N => ?_)
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t : ℝ => F t * t ^ (-(3 / 2 : ℝ))) (μ := volume) (a := a) (n := N)
    fun k _ => hblockI k
  have ha0 : a 0 = 2 := by simp [a]
  rw [ha0] at hsplit
  rw [← hsplit]
  exact (Finset.sum_le_sum fun k _ => hblock k).trans
    (Summable.sum_le_tsum _ (fun k _ => by positivity) hgeom)

/-! ### The line energy of the model -/

theorem weightDirichletSeries_conj (c : ℕ → ℝ) (s : ℂ) :
    weightDirichletSeries c (starRingEnd ℂ s) = starRingEnd ℂ (weightDirichletSeries c s) := by
  rw [weightDirichletSeries, weightDirichletSeries, Complex.conj_tsum]
  refine tsum_congr fun d => ?_
  have harg : (((d : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg d)]; exact Real.pi_ne_zero.symm
  rw [map_mul, Complex.conj_ofReal, ← map_neg, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- The line integrand `|ζ(s)(C(s) − m)/s|²` at `s = σ + it`. -/
def lineIntegrand (c : ℕ → ℝ) (m σ t : ℝ) : ℝ :=
  ‖riemannZeta ((σ : ℂ) + t * I) * (weightDirichletSeries c ((σ : ℂ) + t * I) - (m : ℂ)) /
    ((σ : ℂ) + t * I)‖ ^ 2

/-- The line integrand is even in the height. -/
theorem lineIntegrand_neg (c : ℕ → ℝ) (m σ t : ℝ) :
    lineIntegrand c m σ (-t) = lineIntegrand c m σ t := by
  have hs : ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) = starRingEnd ℂ ((σ : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  simp only [lineIntegrand]
  rw [hs, riemannZeta_conj, weightDirichletSeries_conj]
  have hm : (m : ℂ) = starRingEnd ℂ (m : ℂ) := (Complex.conj_ofReal m).symm
  conv_lhs => rw [hm]
  rw [← map_sub, ← map_mul, ← map_div₀, Complex.norm_conj]

/-- **The line energy of the constant-sign weight is uniformly bounded** for `0 ≤ z < 1/2`. -/
theorem exists_lineEnergy_constantSign_le {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1 / 2) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      ∫ t : ℝ, ‖riemannZeta ((σ : ℂ) + t * I) *
        (weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + t * I) -
          ((∑' d : ℕ, constantSignWeight z d / d : ℝ) : ℂ)) / ((σ : ℂ) + t * I)‖ ^ 2 ≤ M := by
  have hz1 : z ≤ 1 := by linarith
  obtain ⟨K₀, hK₀, hK⟩ := exists_norm_zeta_mul_im_le
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_box
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set P : ℝ := ∑' d : ℕ, constantSignWeight z d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  have hE2 : 0 < E2 := Real.exp_pos _
  set A₁ : ℝ := 8 * Z₀ ^ 2 * (E2 ^ 2 * K₀ ^ (2 * z) + P ^ 2)
  have hA₁ : 0 ≤ A₁ := by positivity
  set Λ : ℝ := (9 * E2 + |P|) ^ 2
  refine ⟨2 * (A₁ * (2 ^ (1 - 2 * z) / (1 - 2 * z) + 2) + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand (constantSignWeight z) P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  -- the series bound at `w = s + 1/2`
  have hC : ∀ t : ℝ, ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
      E2 * ‖riemannZeta ((σ : ℂ) + t * I + 1 / 2)‖ ^ z + |P| := by
    intro t
    rw [weightDirichletSeries_constantSignWeight]
    have hre : 1 < ((σ : ℂ) + t * I + 1 / 2).re := by simp; linarith
    refine (norm_sub_le _ _).trans (add_le_add ?_ (by rw [Complex.norm_real, Real.norm_eq_abs]))
    exact norm_constantSignSeries_le (abs_le.mpr ⟨by linarith, hz1⟩) hre
  have hwre : ∀ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun t => by simp
  have hwim : ∀ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun t => by simp
  have hsnorm : ∀ t : ℝ, σ ≤ ‖(σ : ℂ) + t * I‖ ∧ |t| ≤ ‖(σ : ℂ) + t * I‖ := fun t => by
    constructor
    · have := Complex.abs_re_le_norm ((σ : ℂ) + t * I); simp at this; linarith [le_abs_self σ]
    · have := Complex.abs_im_le_norm ((σ : ℂ) + t * I); simpa using this
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 /
        ‖(σ : ℂ) + t * I‖ ^ 2 := fun t => by
    simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  -- small heights
  have hsmall : ∀ u : ℝ, 0 < u → u ≤ 2 → Φ u ≤ A₁ * (u ^ (-(2 * z)) + 1) := by
    intro u hu0 hu2
    have hζs := hZ σ u hσ.le hσ'.le (by rw [abs_of_pos hu0]; exact hu2)
    have hζw : ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ * u ≤ K₀ := by
      have := hK ((σ : ℂ) + u * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
        (by rw [hwim, abs_of_pos hu0]; exact hu2)
      rwa [hwim, abs_of_pos hu0] at this
    have hζw' : ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ ^ z ≤ K₀ ^ z * u ^ (-z) := by
      have h1 : ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ ≤ K₀ / u := by rw [le_div_iff₀ hu0]; exact hζw
      calc _ ≤ (K₀ / u) ^ z := Real.rpow_le_rpow (norm_nonneg _) h1 hz0
        _ = K₀ ^ z * u ^ (-z) := by
            rw [Real.div_rpow hK₀.le hu0.le, Real.rpow_neg hu0.le, div_eq_mul_inv]
    have hCu := (hC u).trans (add_le_add (mul_le_mul_of_nonneg_left hζw' hE2.le) le_rfl)
    have hsn := (hsnorm u).1
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    rw [hΦform u]
    have hX : 0 ≤ ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + u * I) - (P : ℂ)‖ :=
      norm_nonneg _
    have hupow : (u ^ (-z)) ^ 2 = u ^ (-(2 * z)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; ring_nf
    have hKpow : (K₀ ^ z) ^ 2 = K₀ ^ (2 * z) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK₀.le]; ring_nf
    have hsq : ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2 ≤
        2 * (E2 ^ 2 * K₀ ^ (2 * z) * u ^ (-(2 * z))) + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ hX hCu 2
      have hab : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := fun a b => by
        nlinarith [sq_nonneg (a - b)]
      refine h.trans ((hab _ _).trans ?_)
      rw [mul_pow, mul_pow, hKpow, hupow, sq_abs]
      nlinarith
    have hzsq : ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hζs 2
    have hden : 0 < ‖(σ : ℂ) + u * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    rw [div_le_iff₀ hden]
    have hupos : 0 ≤ u ^ (-(2 * z)) := Real.rpow_nonneg hu0.le _
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * (2 * (E2 ^ 2 * K₀ ^ (2 * z) * u ^ (-(2 * z))) + 2 * P ^ 2) :=
          mul_le_mul hzsq hsq (sq_nonneg _) (sq_nonneg _)
      _ ≤ A₁ * (u ^ (-(2 * z)) + 1) * (1 / 2) ^ 2 := by
          have h1 := mul_nonneg (sq_nonneg Z₀) (by positivity : (0 : ℝ) ≤ E2 ^ 2 * K₀ ^ (2 * z))
          have h2 := mul_nonneg (mul_nonneg (sq_nonneg Z₀) (sq_nonneg P)) hupos
          have key : Z₀ ^ 2 * (2 * (E2 ^ 2 * K₀ ^ (2 * z) * u ^ (-(2 * z))) + 2 * P ^ 2) +
              (2 * (Z₀ ^ 2 * (E2 ^ 2 * K₀ ^ (2 * z))) + 2 * (Z₀ ^ 2 * P ^ 2 * u ^ (-(2 * z)))) =
              A₁ * (u ^ (-(2 * z)) + 1) * (1 / 2) ^ 2 := by
            simp only [A₁]; ring
          linarith
      _ ≤ A₁ * (u ^ (-(2 * z)) + 1) * ‖(σ : ℂ) + u * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
  -- large heights
  have hlarge : ∀ u : ℝ, 2 < u →
      Φ u ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hζw : ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ ≤ Real.log u + 5 := by
      have := RHTower.norm_riemannZeta_le_log_add (s := (σ : ℂ) + u * I + 1 / 2)
        (by rw [hwre]; linarith) (by rw [hwre]; linarith) (by rw [hwim, abs_of_pos hu0]; linarith)
      rwa [hwim, abs_of_pos hu0] at this
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hζw' : ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ ^ z ≤ Real.log u + 5 :=
      (Real.rpow_le_rpow (norm_nonneg _) hζw hz0).trans (by
        calc (Real.log u + 5) ^ z ≤ (Real.log u + 5) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hz1
          _ = Real.log u + 5 := Real.rpow_one _)
    have hq : 1 ≤ u ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hlogq : Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
      have := Real.log_le_rpow_div hu0.le (show (0 : ℝ) < 1 / 4 by norm_num); linarith
    have hCu : ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + u * I) - (P : ℂ)‖ ≤
        (9 * E2 + |P|) * u ^ (1 / 4 : ℝ) := by
      refine (hC u).trans ?_
      have h1 : E2 * ‖riemannZeta ((σ : ℂ) + u * I + 1 / 2)‖ ^ z ≤ E2 * (9 * u ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (hζw'.trans (by linarith)) hE2.le
      nlinarith [abs_nonneg P]
    have hsn := (hsnorm u).2
    rw [abs_of_pos hu0] at hsn
    rw [hΦform u, div_le_iff₀ (pow_pos (lt_of_lt_of_le hu0 hsn) 2)]
    have hX := pow_le_pow_left₀ (norm_nonneg _) hCu 2
    have hq2 : (u ^ (1 / 4 : ℝ)) ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
    have hpow : u ^ (-(3 / 2 : ℝ)) * u ^ 2 = u ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0]; norm_num
    have hs2 : u ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 := pow_le_pow_left₀ hu0.le hsn 2
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * (Λ * u ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (hX.trans (le_of_eq ?_)) (sq_nonneg _)
          rw [mul_pow, hq2]
      _ = Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) * u ^ 2 := by
          rw [← hpow]; ring
      _ ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) *
            ‖(σ : ℂ) + u * I‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
  -- the majorant on the half-line
  set g : ℝ → ℝ := fun u => if u ≤ 2 then A₁ * (u ^ (-(2 * z)) + 1)
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hgsmall : IntegrableOn (fun u : ℝ => A₁ * (u ^ (-(2 * z)) + 1)) (Ioc 0 2) := by
    have h : IntervalIntegrable (fun u : ℝ => A₁ * (u ^ (-(2 * z)) + 1)) volume 0 2 :=
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 2)
        (show -1 < -(2 * z) by linarith)).add (intervalIntegrable_const (c := (1 : ℝ)))).const_mul A₁
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
  have hgint : IntegrableOn g (Ioi 0) := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · refine hgsmall.congr_fun (fun u hu => ?_) measurableSet_Ioc
      simp only [g, if_pos hu.2]
    · refine IntegrableOn.congr_fun (hint2.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ 2 := not_le.mpr hu
      simp only [g, if_neg this]
  have hΦle : ∀ u ∈ Ioi (0 : ℝ), Φ u ≤ g u := by
    intro u hu
    by_cases h2 : u ≤ 2
    · simp only [g, if_pos h2]; exact hsmall u hu h2
    · simp only [g, if_neg h2]; exact hlarge u (not_le.mp h2)
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), g u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hgint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hΦle))
  have hgval : ∫ u in Ioi (0 : ℝ), g u =
      A₁ * (2 ^ (1 - 2 * z) / (1 - 2 * z) + 2) +
        Λ * ∫ u in Ioi (2 : ℝ), ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hgint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hgint.mono_set (by rw [hsplit]; exact subset_union_right))]
    congr 1
    · rw [setIntegral_congr_fun (g := fun u => A₁ * (u ^ (-(2 * z)) + 1)) measurableSet_Ioc
          (fun u hu => by simp only [g, if_pos hu.2]),
        ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_rpow'
          (show -1 < -(2 * z) by linarith)) intervalIntegrable_const,
        integral_rpow (Or.inl (by linarith))]
      have h0 : (0 : ℝ) ^ (-(2 * z) + 1) = 0 := Real.zero_rpow (by intro h; linarith)
      rw [h0, show -(2 * z) + 1 = 1 - 2 * z by ring]
      simp
    · rw [setIntegral_congr_fun
          (g := fun u : ℝ => Λ * (‖riemannZeta ((σ : ℂ) + (u : ℂ) * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))))
          measurableSet_Ioi (fun u hu => by
            have : ¬ u ≤ 2 := not_le.mpr hu
            simp only [g, if_neg this]), integral_const_mul]
  have heven : ∫ t : ℝ, Φ t = 2 * ∫ u in Ioi (0 : ℝ), Φ u := by
    rw [← integral_comp_abs]
    congr 1
    funext t
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, hΦ, lineIntegrand_neg]
  rw [heven]
  have hM2' := mul_le_mul_of_nonneg_left hbound2 (show (0 : ℝ) ≤ Λ by positivity)
  linarith [hhalf, hgval]

/-! ### The sharp law -/

/-- **The constant-sign model is paid below the quarter threshold**: for `0 ≤ z < 1/2` the
half-damped weight `z^{Ω(d)} d^{-1/2}` has bounded receiver. -/
theorem receiverBounded_constantSign {z : ℝ} (hz0 : 0 ≤ z) (hz : z < 1 / 2) :
    ReceiverBounded (constantSignWeight z) := by
  obtain ⟨M, hM⟩ := exists_lineEnergy_constantSign_le hz0 hz
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le
    (dampedClass_constantSignWeight (abs_le.mpr ⟨by linarith, by linarith⟩)) hM⟩

/-- **The constant-sign model is unpaid above the quarter threshold**: for `1/2 < z ≤ 1`,
`Σ z^{Ω(n)} n^{-w} ≥ e^{-2S}(w − 1)^{-z}` and the pole law forbids a bounded receiver. -/
theorem not_receiverBounded_constantSign {z : ℝ} (hz : 1 / 2 < z) (hz1 : z ≤ 1) :
    ¬ ReceiverBounded (constantSignWeight z) := by
  have hz0 : 0 ≤ z := by linarith
  have hf1 : ∀ p : ℕ, p.Prime → |constantSignHom z p| ≤ 1 := fun p hp => by
    rw [constantSignHom_prime z hp, abs_of_nonneg hz0]; exact hz1
  refine not_receiverBounded_of_pattern_ge (constantSignHom z) hf1
    (κ := Real.exp (-2 * primeSquareMass)) (Real.exp_pos _) hz fun w hw hw2 => ?_
  rw [tsum_pattern_eq_exp (constantSignHom z) hf1 hw]
  set x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-w)
  have hx0 : ∀ p, 0 ≤ x p := fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hxhalf : ∀ p : Nat.Primes, x p ≤ 1 / 2 := by
    intro p
    have hp2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
    calc x p ≤ ((p : ℕ) : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ 2 ^ (-1 : ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  have hxs : Summable x := Nat.Primes.summable_rpow.mpr (by linarith)
  have hx2 : ∀ p : Nat.Primes, x p ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    simp only [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)
  -- `−log(1 − zx) ≥ zx` and `−log(1 − x) ≤ x + 2x²`
  have hlo : ∀ p : Nat.Primes, z * x p ≤ -Real.log (1 - constantSignHom z p * x p) := fun p => by
    rw [constantSignHom_prime z p.2]
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 - z * x p by nlinarith [hx0 p, hxhalf p])
    linarith
  have hhi : ∀ p : Nat.Primes, -Real.log (1 - x p) ≤ x p + 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    have h2 : 1 - (1 - x p)⁻¹ ≤ Real.log (1 - x p) :=
      Real.one_sub_inv_le_log_of_pos (by linarith [hxhalf p])
    have h3 : (1 - x p)⁻¹ ≤ 1 + x p + 2 * x p ^ 2 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith [hxhalf p])]; nlinarith [hx0 p, hxhalf p]
    linarith [hx2 p]
  have hL1s : Summable (fun p : Nat.Primes => -Real.log (1 - x p)) :=
    ((hxs.add (summable_primeSquare.mul_left 2))).of_nonneg_of_le
      (fun p => by
        have := Real.log_nonpos (x := 1 - x p) (by linarith [hxhalf p]) (by linarith [hx0 p])
        linarith) hhi
  have hLzs : Summable (fun p : Nat.Primes => -Real.log (1 - constantSignHom z p * x p)) := by
    refine (hxs.mul_left 2).of_norm_bounded fun p => ?_
    rw [constantSignHom_prime z p.2, Real.norm_eq_abs, abs_neg]
    have hzx : 0 ≤ z * x p := mul_nonneg hz0 (hx0 p)
    have hzx2 : z * x p ≤ 1 / 2 := by nlinarith [hx0 p, hxhalf p]
    have h2 : 1 - (1 - z * x p)⁻¹ ≤ Real.log (1 - z * x p) :=
      Real.one_sub_inv_le_log_of_pos (by linarith)
    have h3 : (1 - z * x p)⁻¹ ≤ 1 + 2 * (z * x p) := by
      rw [inv_le_iff_one_le_mul₀ (by linarith)]; nlinarith
    have h4 : Real.log (1 - z * x p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    rw [abs_le]; constructor <;> nlinarith [hx0 p]
  -- assemble: `Σ −log(1 − zx) ≥ z Σ x ≥ z (log(1/(w−1)) − 2S)`
  have hones := one_div_sub_one_le_exp_primes hw
  have hsumx : Real.log (1 / (w - 1)) - 2 * primeSquareMass ≤ ∑' p, x p := by
    have h1 : Real.log (1 / (w - 1)) ≤ ∑' p : Nat.Primes, -Real.log (1 - x p) := by
      rw [← Real.log_exp (∑' p : Nat.Primes, -Real.log (1 - x p))]
      exact Real.log_le_log (one_div_pos.mpr (by linarith)) hones
    have h2 : ∑' p : Nat.Primes, -Real.log (1 - x p) ≤ ∑' p, x p + 2 * primeSquareMass := by
      rw [primeSquareMass, ← tsum_mul_left, ← hxs.tsum_add (summable_primeSquare.mul_left 2)]
      exact Summable.tsum_le_tsum hhi hL1s (hxs.add (summable_primeSquare.mul_left 2))
    linarith
  have hsumz : z * ∑' p, x p ≤ ∑' p : Nat.Primes, -Real.log (1 - constantSignHom z p * x p) := by
    rw [← tsum_mul_left]; exact Summable.tsum_le_tsum hlo (hxs.mul_left z) hLzs
  have hw1 : 0 < w - 1 := by linarith
  have hrpow : (w - 1) ^ (-z) = Real.exp (z * Real.log (1 / (w - 1))) := by
    rw [Real.rpow_def_of_pos hw1, one_div, Real.log_inv]; ring_nf
  have hS0 : 0 ≤ primeSquareMass := tsum_nonneg fun p => by positivity
  rw [hrpow, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_le_mul_of_nonneg_left hsumx hz0]

/-! ### The threshold `z = 1/2` is unpaid

At `z = 1/2` the real-axis pole law is saturated: `F_{1/2}(w) ≍ (w − 1)^{-1/2}`. The boundary
energy sees more: off the axis `|C(s)|² ≥ κ'/|s − 1/2|` near `s = 1/2`, whose integral over a
segment `|t| ≤ r` of the line `Re s = 1/2 + u` grows like `log(1/u)`, while a paid receiver caps every
line energy by `4πE`. -/

/-- `|ζ(w)| ≥ 1/(2|w − 1|)` near the pole (`(w − 1)ζ(w) → 1`). -/
theorem exists_norm_zeta_ge_near_one :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, w ≠ 1 → ‖w - 1‖ < ρ → 1 / (2 * ‖w - 1‖) ≤ ‖riemannZeta w‖ := by
  have h2 : ∀ᶠ w in 𝓝[≠] (1 : ℂ), 1 / 2 < ‖(w - 1) * riemannZeta w‖ :=
    ((continuous_norm.tendsto _).comp riemannZeta_residue_one).eventually
      (lt_mem_nhds (by norm_num))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, hball⟩ := h2
  refine ⟨ρ, hρ, fun w hw1 hwρ => ?_⟩
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
  have h := hball (by rwa [dist_eq_norm]) hw1
  rw [norm_mul] at h
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- `|ζ(s)| > 1/2` near `s = 1/2`, since `|ζ(1/2)| ≥ 1`. -/
theorem exists_norm_zeta_gt_near_half :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ‖s - 1 / 2‖ < r → 1 / 2 < ‖riemannZeta s‖ := by
  have h1 : (1 : ℝ) ≤ ‖riemannZeta (1 / 2 : ℂ)‖ := by
    have h := div_le_norm_riemannZeta (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    have e : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by push_cast; ring
    rw [e] at h
    norm_num at h
    exact h
  have hc : ContinuousAt riemannZeta (1 / 2 : ℂ) :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Tendsto.eventually hc.norm (lt_mem_nhds (show (1 / 2 : ℝ) < ‖riemannZeta (1 / 2)‖ by
      linarith)))
  exact ⟨r, hr, fun s hs => hball (by rwa [dist_eq_norm])⟩

/-- **Off-axis lower bound at the threshold.** There are `r, κ > 0` such that for `0 < u ≤ r` and
`0 ≤ t ≤ r` the line integrand of `c_{1/2}` at `s = 1/2 + u + it` is at least `κ/(u + t) − m²/4`. -/
theorem exists_lineIntegrand_constantSign_half_ge :
    ∃ r κ : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 < κ ∧ ∀ u t : ℝ, 0 < u → u ≤ r → 0 ≤ t → t ≤ r →
      κ / (u + t) - (∑' d : ℕ, constantSignWeight (1 / 2) d / d) ^ 2 / 4 ≤
        lineIntegrand (constantSignWeight (1 / 2)) (∑' d : ℕ, constantSignWeight (1 / 2) d / d)
          (1 / 2 + u) t := by
  obtain ⟨ρ, hρ, hζ1⟩ := exists_norm_zeta_ge_near_one
  obtain ⟨r₁, hr₁, hζh⟩ := exists_norm_zeta_gt_near_half
  set m : ℝ := ∑' d : ℕ, constantSignWeight (1 / 2) d / d
  set r : ℝ := min (min ρ r₁ / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hrρ : 2 * r < ρ := by
    have := min_le_left (min ρ r₁ / 4) (1 / 4)
    have := min_le_left ρ r₁
    linarith
  have hr1 : 2 * r < r₁ := by
    have := min_le_left (min ρ r₁ / 4) (1 / 4)
    have := min_le_right ρ r₁
    linarith
  set S := primeSquareMass
  refine ⟨r, Real.exp (-(4 * S)) / 16, hr, hr4, by positivity, fun u t hu hur ht htr => ?_⟩
  set s : ℂ := (((1 / 2 + u : ℝ)) : ℂ) + t * I
  -- the two displacements
  have hs2 : s - 1 / 2 = (u : ℂ) + t * I := by simp only [s]; push_cast; ring
  have hnorm_ut : ‖(u : ℂ) + t * I‖ ≤ u + t := by
    have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + t * I)
    simpa [abs_of_pos hu, abs_of_nonneg ht] using this
  have hnorm_ut0 : u ≤ ‖(u : ℂ) + t * I‖ := by
    have := Complex.abs_re_le_norm ((u : ℂ) + t * I)
    simpa [abs_of_pos hu] using this
  -- `|ζ(s)| > 1/2`
  have hζs : 1 / 2 < ‖riemannZeta s‖ := hζh s (by rw [hs2]; linarith)
  -- `|s| ≤ 1`
  have hs1 : ‖s‖ ≤ 1 := by
    have := Complex.norm_le_abs_re_add_abs_im s
    have hre : s.re = 1 / 2 + u := by simp [s]
    have him : s.im = t := by simp [s]
    rw [hre, him, abs_of_pos (by linarith), abs_of_nonneg ht] at this
    linarith
  have hs0 : 0 < ‖s‖ := by
    have := Complex.abs_re_le_norm s
    have hre : s.re = 1 / 2 + u := by simp [s]
    rw [hre, abs_of_pos (by linarith)] at this
    linarith
  -- the Dirichlet series at `w = s + 1/2`
  set w : ℂ := s + 1 / 2
  have hw1 : w - 1 = (u : ℂ) + t * I := by rw [← hs2]; simp only [w]; ring
  have hwre : 1 < w.re := by
    have := congrArg Complex.re hw1
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
      sub_zero] at this
    linarith
  have hwne : w ≠ 1 := by
    intro h
    have : ‖w - 1‖ = 0 := by rw [h, sub_self, norm_zero]
    rw [hw1] at this
    linarith
  have hζw : 1 / (2 * (u + t)) ≤ ‖riemannZeta w‖ := by
    have h := hζ1 w hwne (by rw [hw1]; linarith)
    rw [hw1] at h
    refine le_trans ?_ h
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  set P := ‖∑' n : ℕ, (constantSignHom (1 / 2) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
  have hP : Real.exp (-(2 * S)) * Real.sqrt (1 / (2 * (u + t))) ≤ P := by
    refine le_trans ?_ (norm_constantSignSeries_ge (z := 1 / 2) (by norm_num [abs_of_pos]) hwre)
    rw [← Real.sqrt_eq_rpow]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hζw) (Real.exp_pos _).le
  have hP2 : Real.exp (-(4 * S)) * (1 / (2 * (u + t))) ≤ P ^ 2 := by
    have h0 : 0 ≤ Real.exp (-(2 * S)) * Real.sqrt (1 / (2 * (u + t))) := by positivity
    have h := pow_le_pow_left₀ h0 hP 2
    rwa [mul_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * -(2 * S) = -(4 * S) by push_cast; ring] at h
  -- assemble the integrand
  have hC : weightDirichletSeries (constantSignWeight (1 / 2)) s =
      ∑' n : ℕ, (constantSignHom (1 / 2) n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) :=
    weightDirichletSeries_constantSignWeight (1 / 2) s
  set Y := ‖weightDirichletSeries (constantSignWeight (1 / 2)) s - (m : ℂ)‖
  have hPY : P ≤ Y + |m| := by
    have h := norm_sub_norm_le (weightDirichletSeries (constantSignWeight (1 / 2)) s) (m : ℂ)
    have hW : ‖weightDirichletSeries (constantSignWeight (1 / 2)) s‖ = P := by rw [hC]
    rw [hW, Complex.norm_real, Real.norm_eq_abs] at h
    exact (by linarith : P ≤ ‖weightDirichletSeries (constantSignWeight (1 / 2)) s - (m : ℂ)‖ + |m|)
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hP0 : 0 ≤ P := norm_nonneg _
  have hYP : P ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
    have h := pow_le_pow_left₀ hP0 hPY 2
    nlinarith [sq_nonneg (Y - |m|), sq_abs m]
  have hint : lineIntegrand (constantSignWeight (1 / 2)) m (1 / 2 + u) t =
      (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
    simp only [lineIntegrand, norm_div, norm_mul]
    rfl
  rw [hint]
  have hXY : ‖riemannZeta s‖ * Y ≤ ‖riemannZeta s‖ * Y / ‖s‖ :=
    le_div_self (by positivity) hs0 hs1
  have hsq := pow_le_pow_left₀ (by positivity) hXY 2
  have hX2 : Y ^ 2 / 4 ≤ (‖riemannZeta s‖ * Y) ^ 2 := by
    rw [mul_pow]
    have : (1 / 2 : ℝ) ^ 2 ≤ ‖riemannZeta s‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hζs.le 2
    nlinarith [sq_nonneg Y]
  have hκ : Real.exp (-(4 * S)) / 16 / (u + t) =
      Real.exp (-(4 * S)) * (1 / (2 * (u + t))) / 8 := by
    have : 0 < u + t := by linarith
    field_simp
    ring
  rw [hκ]
  linarith

/-- **The threshold is unpaid**: the half-damped weight `2^{-Ω(d)} d^{-1/2}` has unbounded
receiver. Its boundary line energy at `σ = 1/2 + u` exceeds `κ log(1/u) − O(1)`, while a bounded
receiver caps it by `4πE`. -/
theorem not_receiverBounded_constantSign_half :
    ¬ ReceiverBounded (constantSignWeight (1 / 2)) := by
  rintro ⟨E, hE⟩
  set c := constantSignWeight (1 / 2)
  have hc : DampedClass 1 (1 / 2) c := dampedClass_constantSignWeight (by norm_num [abs_of_pos])
  set m : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨r, κ, hr, hr4, hκ, hpt⟩ := exists_lineIntegrand_constantSign_half_ge
  have hE0 : 0 ≤ E := by simpa [weightPronicEnergy] using hE 0
  -- a paid receiver caps every line energy by `4πE`
  have hup : ∀ u : ℝ, 0 < u → u ≤ r → ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * Real.pi * E := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hid := sum_sq_mul_mellinCell_eq_lineEnergy hc hσ hσ1
    have hcap := tsum_sq_mul_mellinCell_le_of_energy (weightCenteredPrefix_zero c m) hσ.le hE
    have h : (1 / 2 + u) / Real.pi * ∫ t, lineIntegrand c m (1 / 2 + u) t ≤ 4 * (1 / 2 + u) * E :=
      hid.symm.le.trans hcap
    have hpi := Real.pi_pos
    rw [div_mul_eq_mul_div, div_le_iff₀ hpi] at h
    nlinarith
  -- and the segment `0 ≤ t ≤ r` alone carries `κ log((u + r)/u) − m² r/4`
  have hlow : ∀ u : ℝ, 0 < u → u ≤ r →
      κ * Real.log ((u + r) / u) - m ^ 2 / 4 * r ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := by
    intro u hu hur
    have hσ : 1 / 2 < 1 / 2 + u := by linarith
    have hσ1 : 1 / 2 + u < 1 := by linarith
    have hfi : Integrable (lineIntegrand c m (1 / 2 + u)) := integrable_lineEnergy hc hσ hσ1
    have hf0 : 0 ≤ᵐ[volume] lineIntegrand c m (1 / 2 + u) :=
      Eventually.of_forall fun t => by simp only [Pi.zero_apply, lineIntegrand]; positivity
    have hinv : IntervalIntegrable (fun t : ℝ => (u + t)⁻¹) volume 0 r := by
      refine ContinuousOn.intervalIntegrable ((continuousOn_const.add continuousOn_id).inv₀ ?_)
      intro t ht
      rw [uIcc_of_le hr.le] at ht
      have : 0 < u + t := by linarith [ht.1]
      exact this.ne'
    have hg : IntervalIntegrable (fun t : ℝ => κ * (u + t)⁻¹ - m ^ 2 / 4) volume 0 r :=
      (hinv.const_mul κ).sub intervalIntegrable_const
    have hval : ∫ t in (0 : ℝ)..r, (κ * (u + t)⁻¹ - m ^ 2 / 4) =
        κ * Real.log ((u + r) / u) - m ^ 2 / 4 * r := by
      rw [intervalIntegral.integral_sub (hinv.const_mul κ) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left (fun x => x⁻¹),
        add_zero, integral_inv_of_pos hu (by linarith), intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc κ * Real.log ((u + r) / u) - m ^ 2 / 4 * r
        = ∫ t in (0 : ℝ)..r, (κ * (u + t)⁻¹ - m ^ 2 / 4) := hval.symm
      _ ≤ ∫ t in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_mono_on hr.le hg hfi.intervalIntegrable fun t ht => by
            have := hpt u t hu hur ht.1 ht.2
            rwa [div_eq_mul_inv] at this
      _ = ∫ t in Ioc (0 : ℝ) r, lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le hr.le
      _ ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  -- choose `u = r e^{-X}` with `κ X > 4πE + m² r/4`
  set X : ℝ := (4 * Real.pi * E + m ^ 2 / 4 * r + 1) / κ
  have hX : 0 < X := by
    have := Real.pi_pos
    positivity
  set u : ℝ := r * Real.exp (-X)
  have hu : 0 < u := by positivity
  have hur : u ≤ r := mul_le_of_le_one_right hr.le (Real.exp_le_one_iff.mpr (by linarith))
  have hlog : X ≤ Real.log ((u + r) / u) := by
    have hru : r / u = Real.exp X := by
      simp only [u]
      rw [div_mul_eq_div_div, div_self hr.ne', one_div, ← Real.exp_neg, neg_neg]
    calc X = Real.log (r / u) := by rw [hru, Real.log_exp]
      _ ≤ Real.log ((u + r) / u) :=
          Real.log_le_log (div_pos hr hu) (div_le_div_of_nonneg_right (by linarith) hu.le)
  have h1 := hlow u hu hur
  have h2 := hup u hu hur
  have hκX : κ * X = 4 * Real.pi * E + m ^ 2 / 4 * r + 1 := by
    simp only [X]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ.le]

/-- **The sharp law of the constant-sign model**: for `0 ≤ z ≤ 1`, the half-damped weight
`z^{Ω(d)} d^{-1/2}` is paid exactly when `z < 1/2`. -/
theorem receiverBounded_constantSign_iff {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ReceiverBounded (constantSignWeight z) ↔ z < 1 / 2 := by
  refine ⟨fun h => ?_, receiverBounded_constantSign hz0⟩
  by_contra hz
  rcases (not_lt.mp hz).eq_or_lt with h2 | h2
  · rw [← h2] at h; exact not_receiverBounded_constantSign_half h
  · exact not_receiverBounded_constantSign h2 hz1 h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
