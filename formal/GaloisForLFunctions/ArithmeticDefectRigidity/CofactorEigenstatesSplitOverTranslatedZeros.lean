import GaloisForLFunctions.ArithmeticDefectRigidity.PowerLogEigenstatesOfTheCofactorCountZetaMultiplicity

/-!
# Cofactor eigenstates split over the translated zeros

Let `F` be a finite set of exponents with `1/2 ≤ Re s < 1 − ε` and `u = Σ_{s∈F} Σ_{k≤K} c_{s,k}
log^k n · n^s`. The real and imaginary parts of `u` both satisfy the renormalized inversion law iff
`c_{s,k} = 0` whenever `k ≥ ord_{s+ε} ζ` (`powerLogRows_global_renormalizedInversion_iff_order`).
The power-log eigenspace of `D̃` over `F` is the direct sum of the blocks at the translated zeros
`ρ − ε ∈ F`, of total complex dimension `Σ_{s∈F} ord_{s+ε} ζ`: the index of the renormalized
cofactor on any finite exponent window counts translated zeros with multiplicity.

Mechanism: exponents are separated by dilations. `D_p f(n) = f(⌊n/p⌋)` preserves admitted rows,
acts on the block of exponent `s` by `p^{-s}` times a unipotent triangular matrix, so
`(D_p − p^{-s})^{K+1}` annihilates that block while `D_p − p^{-s'}` is injective on every block with
`p^{-s'} ≠ p^{-s}`; for `s ≠ s'` one of `p = 2, 3` separates, since `2^a ≠ 3^b`.
-/

open Finset Filter Topology Complex
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Complex admission -/

/-- The complex pronic energy `Σ_{n≤T} |f(n)|²/(n(n+1))`. -/
def cEnergy (T : ℕ) (f : ℕ → ℂ) : ℝ := ∑ n ∈ Icc 1 T, ‖f n‖ ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

/-- A complex row is admitted when it vanishes at the origin and has bounded pronic energy. -/
def CAdmitted (f : ℕ → ℂ) : Prop := f 0 = 0 ∧ ∃ B : ℝ, ∀ T : ℕ, cEnergy T f ≤ B

theorem cEnergy_nonneg (T : ℕ) (f : ℕ → ℂ) : 0 ≤ cEnergy T f :=
  sum_nonneg fun n _ => by positivity

theorem cEnergy_eq_pronicNorm_sq (T : ℕ) (f : ℕ → ℂ) :
    cEnergy T f = pronicNorm T (fun n => ‖f n‖) ^ 2 := by
  rw [pronicNorm_sq]; rfl

theorem cEnergy_eq_re_add_im (T : ℕ) (f : ℕ → ℂ) :
    cEnergy T f = pronicNorm T (fun n => (f n).re) ^ 2 + pronicNorm T (fun n => (f n).im) ^ 2 := by
  rw [pronicNorm_sq, pronicNorm_sq, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  rw [← add_div, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

theorem CAdmitted.zero : CAdmitted (fun _ => 0) :=
  ⟨rfl, 0, fun T => by simp [cEnergy]⟩

theorem CAdmitted.add {f g : ℕ → ℂ} (hf : CAdmitted f) (hg : CAdmitted g) :
    CAdmitted (fun n => f n + g n) := by
  obtain ⟨hf0, Bf, hBf⟩ := hf
  obtain ⟨hg0, Bg, hBg⟩ := hg
  refine ⟨by simp [hf0, hg0], 2 * Bf + 2 * Bg, fun T => ?_⟩
  have h : cEnergy T (fun n => f n + g n) ≤ 2 * cEnergy T f + 2 * cEnergy T g := by
    rw [cEnergy, cEnergy, cEnergy, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun n _ => ?_
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h1 := norm_add_le (f n) (g n)
    nlinarith [norm_nonneg (f n + g n), norm_nonneg (f n), norm_nonneg (g n),
      sq_nonneg (‖f n‖ - ‖g n‖)]
  linarith [hBf T, hBg T]

theorem CAdmitted.const_mul (c : ℂ) {f : ℕ → ℂ} (hf : CAdmitted f) :
    CAdmitted (fun n => c * f n) := by
  obtain ⟨hf0, B, hB⟩ := hf
  refine ⟨by simp [hf0], ‖c‖ ^ 2 * B, fun T => ?_⟩
  have h : cEnergy T (fun n => c * f n) = ‖c‖ ^ 2 * cEnergy T f := by
    rw [cEnergy, cEnergy, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [norm_mul, mul_pow, mul_div_assoc]
  rw [h]
  exact mul_le_mul_of_nonneg_left (hB T) (by positivity)

theorem CAdmitted.sub {f g : ℕ → ℂ} (hf : CAdmitted f) (hg : CAdmitted g) :
    CAdmitted (fun n => f n - g n) := by
  have h := hf.add (hg.const_mul (-1))
  simpa [sub_eq_add_neg] using h

theorem CAdmitted.congr {f g : ℕ → ℂ} (hf : CAdmitted f) (h : ∀ n, f n = g n) : CAdmitted g := by
  have : f = g := funext h
  rwa [← this]

theorem CAdmitted.sum {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℂ)
    (h : ∀ i ∈ S, CAdmitted (f i)) : CAdmitted (fun n => ∑ i ∈ S, f i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using CAdmitted.zero
  | insert i S hi ih =>
    have h1 := h i (mem_insert_self i S)
    have h2 := ih fun j hj => h j (mem_insert_of_mem hj)
    exact (h1.add h2).congr fun n => by rw [sum_insert hi]

/-- Rows of size `C (√n)^θ` with `θ < 1` and vanishing origin are admitted. -/
theorem cAdmitted_of_norm_le {f : ℕ → ℂ} (h0 : f 0 = 0) {C θ : ℝ} (hθ : θ < 1)
    (h : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ C * Real.sqrt n ^ θ) : CAdmitted f := by
  refine ⟨h0, C ^ 2 * (1 + 1 / (1 - θ)), fun T => ?_⟩
  have h' := TransHorizonIncidenceMechanics.sum_sq_le_of_abs_le_sqrt_rpow (ε := 1 - θ)
    (by linarith) (f := fun n => ‖f n‖) (K := C)
    (fun n hn => by rw [abs_of_nonneg (norm_nonneg _), show 1 - (1 - θ) = θ by ring]; exact h n hn) T
  exact h'

/-! ### Dilations -/

/-- The floor dilation `D_p f(n) = f(⌊n/p⌋)`. -/
def dil (p : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ := f (n / p)

theorem CAdmitted.dil {p : ℕ} (hp : 1 ≤ p) {f : ℕ → ℂ} (hf : CAdmitted f) :
    CAdmitted (dil p f) := by
  obtain ⟨hf0, B, hB⟩ := hf
  refine ⟨by simp [ArithmeticDefectRigidity.dil, hf0], 2 * B, fun T => ?_⟩
  have h := ArithmeticContinuationAndCriticalEnergy.pronicNorm_rowDilate_le hp T
    (fun n => ‖f n‖) (by simp [hf0])
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : 2 / (p : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hp0]; have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  rw [cEnergy_eq_pronicNorm_sq]
  have hrow : (fun n => ‖ArithmeticDefectRigidity.dil p f n‖) =
      ArithmeticContinuationAndCriticalEnergy.rowDilate p (fun n => ‖f n‖) := rfl
  rw [hrow]
  have hsq := pow_le_pow_left₀ (pronicNorm_nonneg _ _) h 2
  rw [mul_pow, Real.sq_sqrt (by positivity), ← cEnergy_eq_pronicNorm_sq] at hsq
  calc _ ≤ 2 / (p : ℝ) * cEnergy T f := hsq
    _ ≤ 2 * B := mul_le_mul h2 (hB T) (cEnergy_nonneg _ _) (by norm_num)

/-! ### Dilation of a power-log block -/

/-- The coefficients of the dilated block: `D_p(log^d n · n^s) = p^{-s}(log n − log p)^d n^s`. -/
def dilCoeff (p : ℕ) (s : ℂ) (K : ℕ) (b : ℕ → ℂ) (i : ℕ) : ℂ :=
  (p : ℂ) ^ (-s) * ∑ d ∈ Icc i K, b d * ((d.choose i : ℂ) * (-(Real.log p : ℂ)) ^ (d - i))

/-- The exact dilated block `Σ_d b_d log^d(n/p) (n/p)^s` has the dilated coefficients. -/
theorem powerLogRow_dilCoeff {p : ℕ} (hp : 1 ≤ p) (s : ℂ) (K : ℕ) (b : ℕ → ℂ) {n : ℕ}
    (hn : 1 ≤ n) :
    powerLogRow s K (dilCoeff p s K b) n = ∑ d ∈ range (K + 1), b d *
      ((Real.log ((n : ℝ) / p) : ℂ) ^ d * (((n : ℝ) / p : ℝ) : ℂ) ^ s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hlog : (Real.log ((n : ℝ) / p) : ℂ) = (Real.log n : ℂ) + (-(Real.log p : ℂ)) := by
    rw [Real.log_div hn0.ne' hp0.ne']; push_cast; ring
  have hpow : (((n : ℝ) / p : ℝ) : ℂ) ^ s = (p : ℂ) ^ (-s) * (((n : ℝ)) : ℂ) ^ s := by
    rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hp0]
    push_cast; ring
  have hR : ∀ d, b d * ((Real.log ((n : ℝ) / p) : ℂ) ^ d * (((n : ℝ) / p : ℝ) : ℂ) ^ s) =
      ∑ i ∈ range (d + 1), b d * (((d.choose i : ℂ) * (-(Real.log p : ℂ)) ^ (d - i)) *
        ((p : ℂ) ^ (-s) * ((Real.log n : ℂ) ^ i * (((n : ℝ)) : ℂ) ^ s))) := by
    intro d
    rw [hlog, hpow, add_pow, sum_mul, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  rw [sum_congr rfl fun d _ => hR d, powerLogRow]
  rw [sum_comm' (s' := fun i => Icc i K) (t' := range (K + 1)) (fun d i => by
    simp only [mem_range, mem_Icc]; omega)]
  refine sum_congr rfl fun i _ => ?_
  rw [dilCoeff, mul_sum, sum_mul]
  exact sum_congr rfl fun d _ => by ring

theorem hasDerivAt_logPowCpow (k : ℕ) (s : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => (Real.log x : ℂ) ^ k * ((x : ℝ) : ℂ) ^ s)
      ((k : ℂ) * (Real.log y : ℂ) ^ (k - 1) * ((y⁻¹ : ℝ) : ℂ) * ((y : ℝ) : ℂ) ^ s +
        (Real.log y : ℂ) ^ k * (s * ((y : ℝ) : ℂ) ^ (s - 1))) y := by
  have h1 : HasDerivAt (fun x : ℝ => (Real.log x : ℂ)) ((y⁻¹ : ℝ) : ℂ) y :=
    (Real.hasDerivAt_log hy.ne').ofReal_comp
  exact (h1.pow k).mul (hasDerivAt_ofReal_cpow' s hy)

/-- Rounding the argument of `log^k x · x^s` costs at most `(k + ‖s‖)(1 + log x)^k` on `[1, ∞)`. -/
theorem norm_logPowCpow_floor_sub_le (k : ℕ) {s : ℂ} (hs1 : s.re ≤ 1) {a x : ℝ}
    (ha : 1 ≤ a) (hax : a ≤ x) (hx : x ≤ a + 1) :
    ‖(Real.log a : ℂ) ^ k * ((a : ℝ) : ℂ) ^ s - (Real.log x : ℂ) ^ k * ((x : ℝ) : ℂ) ^ s‖ ≤
      (k + ‖s‖) * (1 + Real.log x) ^ k := by
  have ha0 : 0 < a := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [norm_sub_rev]
  have hbound : ∀ y ∈ Set.Ico a x, ‖(k : ℂ) * (Real.log y : ℂ) ^ (k - 1) * ((y⁻¹ : ℝ) : ℂ) *
      ((y : ℝ) : ℂ) ^ s + (Real.log y : ℂ) ^ k * (s * ((y : ℝ) : ℂ) ^ (s - 1))‖ ≤
      (k + ‖s‖) * (1 + Real.log x) ^ k := by
    intro y hy
    have hy1 : 1 ≤ y := ha.trans hy.1
    have hy0 : 0 < y := by linarith
    have hly : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hlyx : Real.log y ≤ Real.log x := Real.log_le_log hy0 hy.2.le
    have hpow1 : ‖((y : ℝ) : ℂ) ^ s‖ * y⁻¹ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0, ← Real.rpow_neg_one,
        ← Real.rpow_add hy0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
    have hpow2 : ‖((y : ℝ) : ℂ) ^ (s - 1)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hy0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by simp; linarith)
    have hL1 : Real.log y ^ (k - 1) ≤ (1 + Real.log x) ^ k := by
      calc Real.log y ^ (k - 1) ≤ (1 + Real.log x) ^ (k - 1) :=
            pow_le_pow_left₀ hly (by linarith) _
        _ ≤ (1 + Real.log x) ^ k := pow_le_pow_right₀ (by linarith) (Nat.sub_le k 1)
    have hL2 : Real.log y ^ k ≤ (1 + Real.log x) ^ k := pow_le_pow_left₀ hly (by linarith) _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hly, abs_of_pos (inv_pos.mpr hy0)]
    have e1 : (k : ℝ) * Real.log y ^ (k - 1) * y⁻¹ * ‖((y : ℝ) : ℂ) ^ s‖ =
        (k : ℝ) * Real.log y ^ (k - 1) * (‖((y : ℝ) : ℂ) ^ s‖ * y⁻¹) := by ring
    rw [e1, add_mul]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA : (k : ℝ) * Real.log y ^ (k - 1) * (‖((y : ℝ) : ℂ) ^ s‖ * y⁻¹) ≤
        (k : ℝ) * (1 + Real.log x) ^ k := by
      calc _ ≤ (k : ℝ) * Real.log y ^ (k - 1) * 1 :=
            mul_le_mul_of_nonneg_left hpow1 (mul_nonneg hk0 (pow_nonneg hly _))
        _ ≤ (k : ℝ) * (1 + Real.log x) ^ k := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hL1 hk0
    have hB : Real.log y ^ k * (‖s‖ * ‖((y : ℝ) : ℂ) ^ (s - 1)‖) ≤ ‖s‖ * (1 + Real.log x) ^ k := by
      calc _ ≤ (1 + Real.log x) ^ k * (‖s‖ * 1) :=
            mul_le_mul hL2 (mul_le_mul_of_nonneg_left hpow2 (norm_nonneg _))
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        _ = ‖s‖ * (1 + Real.log x) ^ k := by ring
    linarith
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => (Real.log y : ℂ) ^ k * ((y : ℝ) : ℂ) ^ s)
    (fun y hy => (hasDerivAt_logPowCpow k s (by linarith [ha.trans hy.1])).hasDerivWithinAt)
    hbound x ⟨hax, le_rfl⟩
  calc _ ≤ (k + ‖s‖) * (1 + Real.log x) ^ k * (x - a) := hmv
    _ ≤ (k + ‖s‖) * (1 + Real.log x) ^ k * 1 := by gcongr; linarith
    _ = _ := mul_one _

/-- `(1 + log n)^k ≤ C_k n^{1/4}`. -/
theorem one_add_log_pow_le (k : ℕ) {n : ℝ} (hn : 1 ≤ n) :
    (1 + Real.log n) ^ k ≤ (1 + 4 * (k + 1)) ^ k * Real.sqrt n ^ (1 / 2 : ℝ) := by
  have hn0 : 0 < n := by linarith
  have ha : (0 : ℝ) < 1 / (4 * (k + 1)) := by positivity
  have hlog := Real.log_le_rpow_div hn0.le ha
  have hna : 1 ≤ n ^ (1 / (4 * (k + 1) : ℝ)) := Real.one_le_rpow hn (by positivity)
  have h1 : 1 + Real.log n ≤ (1 + 4 * (k + 1)) * n ^ (1 / (4 * (k + 1) : ℝ)) := by
    rw [div_div_eq_mul_div, div_one] at hlog
    calc 1 + Real.log n ≤ n ^ (1 / (4 * (k + 1) : ℝ)) +
          n ^ (1 / (4 * (k + 1) : ℝ)) * (4 * (k + 1)) := by linarith
      _ = (1 + 4 * (k + 1)) * n ^ (1 / (4 * (k + 1) : ℝ)) := by ring
  have hsq : Real.sqrt n ^ (1 / 2 : ℝ) = n ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; norm_num
  rw [hsq]
  calc (1 + Real.log n) ^ k ≤ ((1 + 4 * (k + 1)) * n ^ (1 / (4 * (k + 1) : ℝ))) ^ k :=
        pow_le_pow_left₀ (by linarith [Real.log_nonneg hn]) h1 k
    _ = (1 + 4 * (k + 1)) ^ k * n ^ (1 / (4 * (k + 1) : ℝ) * k) := by
        rw [mul_pow, ← Real.rpow_natCast (n ^ _), ← Real.rpow_mul hn0.le]
    _ ≤ (1 + 4 * (k + 1)) ^ k * n ^ (1 / 4 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn ?_) (by positivity)
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

/-- **Dilation of a block.** `D_p` maps the power-log block with coefficients `b` to the block with
coefficients `dilCoeff p s K b`, modulo an admitted row. -/
theorem cAdmitted_dil_powerLogRow_sub {p : ℕ} (hp : 1 ≤ p) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re ≤ 1) (K : ℕ) (b : ℕ → ℂ) :
    CAdmitted (fun n => dil p (powerLogRow s K b) n - powerLogRow s K (dilCoeff p s K b) n) := by
  have hs : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  set Cb := ∑ d ∈ range (K + 1), ‖b d‖ * ((d + ‖s‖) + Real.log p ^ d) *
    (1 + 4 * (d + 1)) ^ d with hCb
  refine cAdmitted_of_norm_le (by simp [dil, powerLogRow_zero hs, Nat.zero_div])
    (C := Cb) (θ := 1 / 2) (by norm_num) fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [powerLogRow_dilCoeff hp s K b hn, dil, powerLogRow, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [hCb, sum_mul]
  refine sum_le_sum fun d _ => ?_
  rw [← mul_sub, norm_mul]
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hpow := one_add_log_pow_le d hnR
  -- the rounded block term
  have hterm : ‖(Real.log ((n / p : ℕ) : ℝ) : ℂ) ^ d * ((((n / p : ℕ) : ℝ)) : ℂ) ^ s -
      (Real.log ((n : ℝ) / p) : ℂ) ^ d * (((n : ℝ) / p : ℝ) : ℂ) ^ s‖ ≤
      ((d + ‖s‖) + Real.log p ^ d) * (1 + Real.log n) ^ d := by
    rcases Nat.lt_or_ge n p with hnp | hnp
    · -- `⌊n/p⌋ = 0`: only the unrounded term remains
      have hdiv : n / p = 0 := Nat.div_eq_of_lt hnp
      have hx0 : (0 : ℝ) < (n : ℝ) / p := by positivity
      have hx1 : (n : ℝ) / p ≤ 1 := by
        rw [div_le_one hp0]; exact_mod_cast hnp.le
      rw [hdiv, Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow hs, mul_zero, zero_sub,
        norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hlogabs : |Real.log ((n : ℝ) / p)| ≤ Real.log p := by
        rw [abs_of_nonpos (Real.log_nonpos hx0.le hx1), Real.log_div hn0.ne' hp0.ne']
        linarith
      have hxs : ((n : ℝ) / p) ^ s.re ≤ 1 := Real.rpow_le_one hx0.le hx1 hs0.le
      have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
      have h1 : |Real.log ((n : ℝ) / p)| ^ d * ((n : ℝ) / p) ^ s.re ≤ Real.log p ^ d :=
        calc _ ≤ Real.log p ^ d * 1 :=
              mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hlogabs d) hxs (by positivity)
                (pow_nonneg hlp d)
          _ = _ := mul_one _
      have h2 : 1 ≤ (1 + Real.log n) ^ d := one_le_pow₀ (by linarith)
      have h3 : 0 ≤ (d : ℝ) + ‖s‖ := by positivity
      nlinarith [pow_nonneg hlp d]
    · -- `n ≥ p`: rounding inside `[⌊n/p⌋, n/p]`
      have hq1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hp).mpr (by omega)
      have hle : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := Nat.cast_div_le
      have hlt : (n : ℝ) / p ≤ ((n / p : ℕ) : ℝ) + 1 := by
        have := (abs_le.mp (RHTower.Sieve.abs_natDiv_sub_div_le (N := n) hp)).1
        linarith
      have h := norm_logPowCpow_floor_sub_le d hs1 (by exact_mod_cast hq1) hle hlt
      have hlogx : Real.log ((n : ℝ) / p) ≤ Real.log n := by
        rw [Real.log_div hn0.ne' hp0.ne']
        linarith [Real.log_nonneg (by exact_mod_cast hp : (1 : ℝ) ≤ p)]
      have hlogx0 : 0 ≤ Real.log ((n : ℝ) / p) :=
        Real.log_nonneg ((le_div_iff₀ hp0).mpr (by rw [one_mul]; exact_mod_cast hnp))
      refine h.trans ?_
      calc ((d : ℝ) + ‖s‖) * (1 + Real.log ((n : ℝ) / p)) ^ d
          ≤ ((d : ℝ) + ‖s‖) * (1 + Real.log n) ^ d :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) d)
              (by positivity)
        _ ≤ ((d + ‖s‖) + Real.log p ^ d) * (1 + Real.log n) ^ d := by
            have := pow_nonneg (Real.log_nonneg (by exact_mod_cast hp : (1 : ℝ) ≤ p)) d
            nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log n) d]
  calc _ ≤ ((d + ‖s‖) + Real.log p ^ d) * (1 + Real.log n) ^ d := hterm
    _ ≤ ((d + ‖s‖) + Real.log p ^ d) * ((1 + 4 * (d + 1)) ^ d * Real.sqrt n ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-! ### Elimination on coefficient vectors -/

/-- One elimination step `b ↦ dilCoeff b − μ b` on coefficient vectors. -/
def elimStep (p : ℕ) (s : ℂ) (K : ℕ) (μ : ℂ) (b : ℕ → ℂ) (i : ℕ) : ℂ :=
  dilCoeff p s K b i - μ * b i

theorem elimStep_eq (p : ℕ) (s : ℂ) (K : ℕ) (μ : ℂ) (b : ℕ → ℂ) {i : ℕ} (hi : i ≤ K) :
    elimStep p s K μ b i = ((p : ℂ) ^ (-s) - μ) * b i + (p : ℂ) ^ (-s) *
      ∑ d ∈ Ioc i K, b d * ((d.choose i : ℂ) * (-(Real.log p : ℂ)) ^ (d - i)) := by
  have hsplit : Icc i K = insert i (Ioc i K) := by
    ext d; simp only [mem_insert, mem_Icc, mem_Ioc]; omega
  rw [elimStep, dilCoeff, hsplit, sum_insert (by simp)]
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, mul_one]
  ring

/-- Elimination only reads the coefficients `0, …, K`. -/
theorem elimStep_congr (p : ℕ) (s : ℂ) (K : ℕ) (μ : ℂ) {b b' : ℕ → ℂ}
    (h : ∀ d ≤ K, b d = b' d) : ∀ i ≤ K, elimStep p s K μ b i = elimStep p s K μ b' i := by
  intro i hi
  rw [elimStep, elimStep, dilCoeff, dilCoeff, h i hi]
  congr 2
  refine sum_congr rfl fun d hd => ?_
  rw [h d (mem_Icc.mp hd).2]

/-- **The killing step.** With `μ = p^{-s}`, elimination lowers the top degree. -/
theorem elimStep_kill (p : ℕ) (s : ℂ) (K : ℕ) {b : ℕ → ℂ} {j : ℕ}
    (hb : ∀ d, j ≤ d → d ≤ K → b d = 0) :
    ∀ i, j ≤ i + 1 → i ≤ K → elimStep p s K ((p : ℂ) ^ (-s)) b i = 0 := by
  intro i hij hiK
  rw [elimStep_eq p s K _ b hiK, sub_self, zero_mul, zero_add]
  rw [sum_eq_zero fun d hd => by
    simp only [mem_Ioc] at hd
    rw [hb d (by omega) hd.2, zero_mul], mul_zero]

/-- `K+1` killing steps annihilate every block of degree `≤ K`. -/
theorem iterate_elimStep_kill (p : ℕ) (s : ℂ) (K : ℕ) (b : ℕ → ℂ) :
    ∀ i ≤ K, (elimStep p s K ((p : ℂ) ^ (-s)))^[K + 1] b i = 0 := by
  have key : ∀ t, ∀ i, K + 1 ≤ i + t → i ≤ K →
      (elimStep p s K ((p : ℂ) ^ (-s)))^[t] b i = 0 := by
    intro t
    induction t with
    | zero => intro i hi hiK; omega
    | succ t ih =>
      intro i hi hiK
      rw [Function.iterate_succ_apply']
      exact elimStep_kill p s K (j := K + 1 - t) (fun d hd hdK => ih d (by omega) hdK) i
        (by omega) hiK
  intro i hi
  exact key (K + 1) i (by omega) hi

/-- **The injective step.** If `μ ≠ p^{-s}`, an elimination step that vanishes on `0, …, K` comes
from a vector vanishing on `0, …, K`. -/
theorem eq_zero_of_elimStep_eq_zero (p : ℕ) (s : ℂ) (K : ℕ) {μ : ℂ} (hμ : (p : ℂ) ^ (-s) ≠ μ)
    {b : ℕ → ℂ} (h : ∀ i ≤ K, elimStep p s K μ b i = 0) : ∀ i ≤ K, b i = 0 := by
  have key : ∀ t, ∀ i, K - t ≤ i → i ≤ K → b i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hi hiK
      have hiK' : i = K := by omega
      subst hiK'
      have h0 := h i le_rfl
      rw [elimStep_eq p s i μ b le_rfl] at h0
      have hIoc : Ioc i i = ∅ := Finset.Ioc_self i
      rw [hIoc, sum_empty, mul_zero, add_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
    | succ t ih =>
      intro i hi hiK
      by_cases hit : K - t ≤ i
      · exact ih i hit hiK
      have h0 := h i hiK
      rw [elimStep_eq p s K μ b hiK] at h0
      rw [sum_eq_zero fun d hd => by
        simp only [mem_Ioc] at hd
        rw [ih d (by omega) hd.2, zero_mul], mul_zero, add_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  intro i hi
  exact key K i (by omega) hi

/-! ### Elimination lists -/

/-- Rows: apply the steps `f ↦ D_p f − μ f` of a list, last entry first. -/
def rowElim : List (ℕ × ℂ) → (ℕ → ℂ) → (ℕ → ℂ)
  | [], f => f
  | q :: L, f => fun n => dil q.1 (rowElim L f) n - q.2 * rowElim L f n

/-- Coefficients: the same steps on a block of exponent `s`. -/
def coeffElim (s : ℂ) (K : ℕ) : List (ℕ × ℂ) → (ℕ → ℂ) → (ℕ → ℂ)
  | [], b => b
  | q :: L, b => elimStep q.1 s K q.2 (coeffElim s K L b)

theorem rowElim_sum (L : List (ℕ × ℂ)) {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℂ) (n : ℕ) :
    rowElim L (fun m => ∑ i ∈ S, f i m) n = ∑ i ∈ S, rowElim L (f i) n := by
  induction L generalizing n with
  | nil => rfl
  | cons q L ih =>
    simp only [rowElim, dil, ih, mul_sum, ← sum_sub_distrib]

theorem rowElim_sub (L : List (ℕ × ℂ)) (f g : ℕ → ℂ) (n : ℕ) :
    rowElim L (fun m => f m - g m) n = rowElim L f n - rowElim L g n := by
  induction L generalizing n with
  | nil => rfl
  | cons q L ih =>
    simp only [rowElim, dil, ih]; ring

theorem CAdmitted.rowElim {L : List (ℕ × ℂ)} (hL : ∀ q ∈ L, 1 ≤ q.1) {f : ℕ → ℂ}
    (hf : CAdmitted f) : CAdmitted (rowElim L f) := by
  induction L with
  | nil => exact hf
  | cons q L ih =>
    have hL' : ∀ q' ∈ L, 1 ≤ q'.1 := fun q' hq' => hL q' (List.mem_cons_of_mem q hq')
    exact ((ih hL').dil (hL q List.mem_cons_self)).sub ((ih hL').const_mul q.2)

/-- The block elimination is linear in the coefficients. -/
theorem powerLogRow_elimStep (p : ℕ) (s : ℂ) (K : ℕ) (μ : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    powerLogRow s K (elimStep p s K μ b) n =
      powerLogRow s K (dilCoeff p s K b) n - μ * powerLogRow s K b n := by
  simp only [powerLogRow, elimStep, sub_mul, sum_sub_distrib, mul_sum, mul_assoc]

/-- **Rows follow coefficients.** Eliminating a block row gives the block with eliminated
coefficients, modulo an admitted row. -/
theorem cAdmitted_rowElim_powerLogRow_sub {L : List (ℕ × ℂ)} (hL : ∀ q ∈ L, 1 ≤ q.1) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (K : ℕ) (b : ℕ → ℂ) :
    CAdmitted (fun n => rowElim L (powerLogRow s K b) n -
      powerLogRow s K (coeffElim s K L b) n) := by
  induction L with
  | nil => exact CAdmitted.zero.congr fun n => by simp [rowElim, coeffElim]
  | cons q L ih =>
    have hL' : ∀ q' ∈ L, 1 ≤ q'.1 := fun q' hq' => hL q' (List.mem_cons_of_mem q hq')
    have hq := hL q List.mem_cons_self
    have h1 := (ih hL').dil hq
    have h2 := cAdmitted_dil_powerLogRow_sub hq hs0 hs1 K (coeffElim s K L b)
    have h3 := (ih hL').const_mul q.2
    refine ((h1.add h2).sub h3).congr fun n => ?_
    simp only [rowElim, coeffElim, powerLogRow_elimStep, dil]
    ring

/-- Elimination of a vector vanishing on `0, …, K` stays zero there. -/
theorem coeffElim_zero (s : ℂ) (K : ℕ) (L : List (ℕ × ℂ)) {b : ℕ → ℂ} (hb : ∀ d ≤ K, b d = 0) :
    ∀ i ≤ K, coeffElim s K L b i = 0 := by
  induction L with
  | nil => exact hb
  | cons q L ih =>
    intro i hi
    rw [coeffElim, elimStep_congr q.1 s K q.2 (b' := fun _ => 0) ih i hi]
    simp [elimStep, dilCoeff]

theorem coeffElim_append (s : ℂ) (K : ℕ) (L₁ L₂ : List (ℕ × ℂ)) (b : ℕ → ℂ) :
    coeffElim s K (L₁ ++ L₂) b = coeffElim s K L₁ (coeffElim s K L₂ b) := by
  induction L₁ with
  | nil => rfl
  | cons q L ih => simp only [List.cons_append, coeffElim, ih]

theorem coeffElim_replicate (p : ℕ) (s : ℂ) (K : ℕ) (μ : ℂ) (t : ℕ) (b : ℕ → ℂ) :
    coeffElim s K (List.replicate t (p, μ)) b = (elimStep p s K μ)^[t] b := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.replicate_succ, coeffElim, ih, Function.iterate_succ_apply']

/-- A list containing `K+1` consecutive killing steps for `s` annihilates the block of `s`. -/
theorem coeffElim_kill (s : ℂ) (K : ℕ) (p : ℕ) (L₁ L₂ : List (ℕ × ℂ)) (b : ℕ → ℂ) :
    ∀ i ≤ K, coeffElim s K (L₁ ++ List.replicate (K + 1) (p, (p : ℂ) ^ (-s)) ++ L₂) b i = 0 := by
  rw [coeffElim_append, coeffElim_append, coeffElim_replicate]
  exact coeffElim_zero s K L₁ (iterate_elimStep_kill p s K _)

/-- Elimination by steps that never kill `s₀` is injective on the block of `s₀`. -/
theorem coeffElim_injective (s₀ : ℂ) (K : ℕ) {L : List (ℕ × ℂ)}
    (hL : ∀ q ∈ L, ((q.1 : ℕ) : ℂ) ^ (-s₀) ≠ q.2) {b : ℕ → ℂ}
    (h : ∀ i ≤ K, coeffElim s₀ K L b i = 0) : ∀ i ≤ K, b i = 0 := by
  induction L with
  | nil => exact h
  | cons q L ih =>
    have hL' : ∀ q' ∈ L, ((q'.1 : ℕ) : ℂ) ^ (-s₀) ≠ q'.2 := fun q' hq' =>
      hL q' (List.mem_cons_of_mem q hq')
    exact ih hL' (eq_zero_of_elimStep_eq_zero q.1 s₀ K (hL q List.mem_cons_self) h)

/-! ### Separating exponents by the primes 2 and 3 -/

/-- `2^a = 3^b` with integers forces `a = b = 0`. -/
theorem int_eq_zero_of_two_zpow_eq_three_zpow {a b : ℤ}
    (h : (a : ℝ) * Real.log 2 = (b : ℝ) * Real.log 3) : a = 0 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hpow : ((2 : ℝ) ^ a) = (3 : ℝ) ^ b := by
    have h1 : Real.log ((2 : ℝ) ^ a) = Real.log ((3 : ℝ) ^ b) := by
      rw [Real.log_zpow, Real.log_zpow, h]
    exact Real.log_injOn_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) a)
      (zpow_pos (by norm_num : (0 : ℝ) < 3) b) h1
  by_contra ha
  -- `a` and `b` have the same sign
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hb : b < 0 := by
      by_contra hb; push Not at hb
      have : (a : ℝ) * Real.log 2 < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast ha) hl2
      have : 0 ≤ (b : ℝ) * Real.log 3 := mul_nonneg (by exact_mod_cast hb) hl3.le
      linarith
    have h' : (2 : ℝ) ^ (-a) = (3 : ℝ) ^ (-b) := by rw [zpow_neg, zpow_neg, hpow]
    obtain ⟨A, hA⟩ : ∃ A : ℕ, -a = A := ⟨(-a).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨B, hB⟩ : ∃ B : ℕ, -b = B := ⟨(-b).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hA, hB, zpow_natCast, zpow_natCast] at h'
    have hN : (2 : ℕ) ^ A = 3 ^ B := by exact_mod_cast h'
    have hA0 : 0 < A := by omega
    have h2 : 2 ∣ 3 ^ B := hN ▸ dvd_pow_self 2 hA0.ne'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    omega
  · have hb : 0 < b := by
      by_contra hb; push Not at hb
      have : 0 < (a : ℝ) * Real.log 2 := mul_pos (by exact_mod_cast ha) hl2
      have : (b : ℝ) * Real.log 3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hb) hl3.le
      linarith
    obtain ⟨A, hA⟩ : ∃ A : ℕ, a = A := ⟨a.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    obtain ⟨B, hB⟩ : ∃ B : ℕ, b = B := ⟨b.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    rw [hA, hB, zpow_natCast, zpow_natCast] at hpow
    have hN : (2 : ℕ) ^ A = 3 ^ B := by exact_mod_cast hpow
    have hA0 : 0 < A := by omega
    have h2 : 2 ∣ 3 ^ B := hN ▸ dvd_pow_self 2 hA0.ne'
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    omega

/-- **One of the dilations by 2 and 3 separates any two distinct exponents.** -/
theorem exists_separating_prime {s s₀ : ℂ} (hne : s ≠ s₀) :
    ∃ p ∈ ({2, 3} : Finset ℕ), ((p : ℕ) : ℂ) ^ (-s₀) ≠ ((p : ℕ) : ℂ) ^ (-s) := by
  by_contra hall
  push Not at hall
  have h2 := hall 2 (by simp)
  have h3 := hall 3 (by simp)
  -- `p^{s − s₀} = 1` for `p = 2, 3`
  have hexp : ∀ p : ℕ, 1 < p → ((p : ℕ) : ℂ) ^ (-s₀) = ((p : ℕ) : ℂ) ^ (-s) →
      ∃ n : ℤ, (s - s₀) * (Real.log p : ℂ) = n * (2 * Real.pi * I) := by
    intro p hp hpe
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans zero_lt_one hp)
    have hpC : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
    have h1 : ((p : ℕ) : ℂ) ^ (s - s₀) = 1 := by
      rw [show s - s₀ = -s₀ - -s by ring, Complex.cpow_sub _ _ hpC, hpe, div_self]
      rw [Complex.cpow_def_of_ne_zero hpC]; exact Complex.exp_ne_zero _
    rw [Complex.cpow_def_of_ne_zero hpC, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    rw [← hn, show ((p : ℕ) : ℂ) = ((p : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log hp0.le]
    ring
  obtain ⟨a, ha⟩ := hexp 2 (by norm_num) h2
  obtain ⟨b, hb⟩ := hexp 3 (by norm_num) h3
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  -- `a log 3 = b log 2`
  have hrel : ((a : ℝ) * Real.log 3 : ℂ) = ((b : ℝ) * Real.log 2 : ℂ) := by
    have e1 : (s - s₀) * (Real.log 2 : ℂ) * (Real.log 3 : ℂ) = (s - s₀) * (Real.log 3 : ℂ) *
        (Real.log 2 : ℂ) := by ring
    rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at ha
    rw [show ((3 : ℕ) : ℝ) = 3 by norm_num] at hb
    rw [ha, hb] at e1
    have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have e2 : ((a : ℂ) * (Real.log 3 : ℂ)) * (2 * Real.pi * I) =
        ((b : ℂ) * (Real.log 2 : ℂ)) * (2 * Real.pi * I) := by linear_combination e1
    have e3 := mul_right_cancel₀ hπ e2
    push_cast
    exact e3
  have hrel' : (b : ℝ) * Real.log 2 = (a : ℝ) * Real.log 3 := by exact_mod_cast hrel.symm
  have hb0 : b = 0 := int_eq_zero_of_two_zpow_eq_three_zpow hrel'
  rw [hb0] at hb
  simp only [Int.cast_zero, zero_mul] at hb
  have : s - s₀ = 0 := by
    have hl : (Real.log ((3 : ℕ) : ℝ) : ℂ) ≠ 0 := by
      rw [show ((3 : ℕ) : ℝ) = 3 by norm_num]; exact_mod_cast hl3.ne'
    exact (mul_eq_zero.mp hb).resolve_right hl
  exact hne (sub_eq_zero.mp this)

/-! ### Exponent independence of admitted block sums -/

/-- Real and imaginary bounds from complex admission. -/
theorem CAdmitted.re_im_bounded {f : ℕ → ℂ} (hf : CAdmitted f) :
    ∃ B : ℝ, (∀ T, pronicNorm T (fun n => (f n).re) ≤ B) ∧
      ∀ T, pronicNorm T (fun n => (f n).im) ≤ B := by
  obtain ⟨-, B, hB⟩ := hf
  refine ⟨Real.sqrt B, fun T => ?_, fun T => ?_⟩
  · have h := hB T
    rw [cEnergy_eq_re_add_im] at h
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (pronicNorm T fun n => (f n).im)])
  · have h := hB T
    rw [cEnergy_eq_re_add_im] at h
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (pronicNorm T fun n => (f n).re)])

/-- **Exponent independence.** If a finite sum of power-log blocks with exponents
`1/2 ≤ Re s ≤ 1` is admitted, every block coefficient vanishes. -/
theorem coeff_eq_zero_of_cAdmitted_sum {F : Finset ℂ} (hF : ∀ s ∈ F, 1 / 2 ≤ s.re ∧ s.re ≤ 1)
    (K : ℕ) (b : ℂ → ℕ → ℂ) (h : CAdmitted (fun n => ∑ s ∈ F, powerLogRow s K (b s) n)) :
    ∀ s₀ ∈ F, ∀ d ≤ K, b s₀ d = 0 := by
  classical
  intro s₀ hs₀
  -- a separating prime for every other exponent
  have hsep : ∀ s ∈ F.erase s₀, ∃ p ∈ ({2, 3} : Finset ℕ),
      ((p : ℕ) : ℂ) ^ (-s₀) ≠ ((p : ℕ) : ℂ) ^ (-s) := fun s hs =>
    exists_separating_prime (ne_of_mem_erase hs)
  choose! P hP hPs using hsep
  set L : List (ℕ × ℂ) := (F.erase s₀).toList.flatMap
    (fun s => List.replicate (K + 1) (P s, ((P s : ℕ) : ℂ) ^ (-s))) with hLdef
  have hP1 : ∀ s ∈ F.erase s₀, 1 ≤ P s := fun s hs => by
    have := hP s hs; simp only [mem_insert, mem_singleton] at this; omega
  have hL1 : ∀ q ∈ L, 1 ≤ q.1 := by
    intro q hq
    rw [hLdef, List.mem_flatMap] at hq
    obtain ⟨s, hs, hq⟩ := hq
    rw [List.eq_of_mem_replicate hq]
    exact hP1 s (mem_toList.mp hs)
  have hLinj : ∀ q ∈ L, ((q.1 : ℕ) : ℂ) ^ (-s₀) ≠ q.2 := by
    intro q hq
    rw [hLdef, List.mem_flatMap] at hq
    obtain ⟨s, hs, hq⟩ := hq
    rw [List.eq_of_mem_replicate hq]
    exact hPs s (mem_toList.mp hs)
  -- eliminate the full sum
  have hsum := h.rowElim hL1
  -- every other block is killed
  have hother : ∀ s ∈ F.erase s₀, CAdmitted (rowElim L (powerLogRow s K (b s))) := by
    intro s hs
    have hsre := hF s (mem_of_mem_erase hs)
    have hrow := cAdmitted_rowElim_powerLogRow_sub hL1 (by linarith [hsre.1]) hsre.2 K (b s)
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem (mem_toList.mpr hs)
    have hLsplit : L = (l₁.flatMap fun s => List.replicate (K + 1) (P s, ((P s : ℕ) : ℂ) ^ (-s))) ++
        List.replicate (K + 1) (P s, ((P s : ℕ) : ℂ) ^ (-s)) ++
        (l₂.flatMap fun s => List.replicate (K + 1) (P s, ((P s : ℕ) : ℂ) ^ (-s))) := by
      rw [hLdef, hl, List.flatMap_append, List.flatMap_cons, List.append_assoc]
    have hzero : ∀ n, powerLogRow s K (coeffElim s K L (b s)) n = 0 := by
      intro n
      refine sum_eq_zero fun d hd => ?_
      rw [hLsplit, coeffElim_kill s K (P s) _ _ (b s) d (Nat.lt_succ_iff.mp (mem_range.mp hd)),
        zero_mul]
    exact hrow.congr fun n => by rw [hzero, sub_zero]
  have hrest := CAdmitted.sum (F.erase s₀) _ hother
  have hblock : CAdmitted (rowElim L (powerLogRow s₀ K (b s₀))) := by
    refine (hsum.sub hrest).congr fun n => ?_
    rw [rowElim_sum, ← Finset.add_sum_erase F _ hs₀]
    ring
  have hs₀re := hF s₀ hs₀
  have hrow₀ := cAdmitted_rowElim_powerLogRow_sub hL1 (by linarith [hs₀re.1]) hs₀re.2 K (b s₀)
  have hfinal : CAdmitted (fun n => powerLogRow s₀ K (coeffElim s₀ K L (b s₀)) n) :=
    (hblock.sub hrow₀).congr fun n => by ring
  obtain ⟨B, hre, him⟩ := hfinal.re_im_bounded
  have hc := powerLogRow_coeff_eq_zero_of_bounded hs₀re.1 K _ hre him
  exact coeffElim_injective s₀ K hLinj hc

/-! ### The global eigenstate classification -/

/-- The real row of a finite sum of power-log blocks, as a vector of the trace domain. -/
def globalPowerLogTraceVector (ε : SubcriticalDamping) (F : Finset ℂ)
    (hF : ∀ s ∈ F, 0 < s.re ∧ s.re < 1 - ε) (K : ℕ) (c : ℂ → ℕ → ℂ) : poleTraceDomain ε :=
  ∑ s ∈ F.attach, powerLogTraceVector ε (hF s.1 s.2).1 (hF s.1 s.2).2 K (c s.1)

theorem globalPowerLogTraceVector_apply (ε : SubcriticalDamping) (F : Finset ℂ)
    (hF : ∀ s ∈ F, 0 < s.re ∧ s.re < 1 - ε) (K : ℕ) (c : ℂ → ℕ → ℂ) (n : ℕ) :
    (globalPowerLogTraceVector ε F hF K c : ℕ → ℝ) n = (∑ s ∈ F, powerLogRow s K (c s) n).re := by
  rw [globalPowerLogTraceVector, Submodule.coe_sum, Finset.sum_apply, Complex.re_sum]
  exact sum_attach F (fun s => (powerLogRow s K (c s) n).re)

/-- Finite sums of rows of bounded pronic norm have bounded pronic norm. -/
theorem exists_pronicNorm_sum_le {ι : Type*} (S : Finset ι) (f : ι → ℕ → ℝ)
    (h : ∀ i ∈ S, ∃ B : ℝ, ∀ T, pronicNorm T (f i) ≤ B) :
    ∃ B : ℝ, ∀ T, pronicNorm T (fun n => ∑ i ∈ S, f i n) ≤ B := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, fun T => by simp [BezoutValuationIncidence.pronicNorm]⟩
  | insert i S hi ih =>
    obtain ⟨B₁, hB₁⟩ := h i (mem_insert_self i S)
    obtain ⟨B₂, hB₂⟩ := ih fun j hj => h j (mem_insert_of_mem hj)
    refine ⟨B₁ + B₂, fun T => ?_⟩
    have := BezoutValuationIncidence.pronicNorm_add_le T (f i) (fun n => ∑ j ∈ S, f j n)
    simp only [sum_insert hi]
    linarith [hB₁ T, hB₂ T]

/-- **The global symbol law.** Modulo bounded energy, `(I + D̃)` maps the real row of
`Σ_s Σ_k c_{s,k} log^k n · n^s` to the real part of `Σ_s` (Leibniz block of `s`). -/
theorem exists_pronicNorm_global_symbol_le (ε : SubcriticalDamping) (F : Finset ℂ)
    (hF : ∀ s ∈ F, 0 < s.re ∧ s.re < 1 - ε) (K : ℕ) (c : ℂ → ℕ → ℂ) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n => (globalPowerLogTraceVector ε F hF K c : ℕ → ℝ) n +
      renormalizedCofactorOperator ε (globalPowerLogTraceVector ε F hF K c) n -
        (∑ s ∈ F, powerLogRow s K (leibnizCoeff ε s K (c s)) n).re) ≤ B := by
  obtain ⟨B, hB⟩ := exists_pronicNorm_sum_le F.attach (fun s n =>
      powerLogReRow s.1 K (c s.1) n + renormalizedCofactorOperator ε
        (powerLogTraceVector ε (hF s.1 s.2).1 (hF s.1 s.2).2 K (c s.1)) n -
        (∑ k ∈ range (K + 1), c s.1 k * zetaLeibnizRow ε s.1 k n).re)
    (fun s _ => exists_pronicNorm_powerLogRow_symbol_le ε (hF s.1 s.2).1 (hF s.1 s.2).2 K (c s.1))
  refine ⟨B, fun T => (le_of_eq ?_).trans (hB T)⟩
  congr 1
  funext n
  rw [globalPowerLogTraceVector_apply, globalPowerLogTraceVector, map_sum, Finset.sum_apply,
    sum_sub_distrib, sum_add_distrib]
  simp only [sum_mul_zetaLeibnizRow, powerLogReRow]
  rw [Complex.re_sum, Complex.re_sum, sum_attach F (fun s => (powerLogRow s K (c s) n).re),
    sum_attach F (fun s => (powerLogRow s K (leibnizCoeff ε s K (c s)) n).re)]

/-- **Global index theorem.** For a finite set `F` of exponents with `1/2 ≤ Re s < 1 − ε`, the real
and imaginary parts of `Σ_{s∈F} Σ_{k≤K} c_{s,k} log^k n · n^s` both satisfy the renormalized
inversion law iff `c_{s,k} = 0` whenever `k ≥ ord_{s+ε} ζ`. The power-log eigenspace of `D̃` over
`F` is the direct sum of the zero blocks, of dimension `Σ_{s∈F} ord_{s+ε} ζ`. -/
theorem powerLogRows_global_renormalizedInversion_iff_order (ε : SubcriticalDamping)
    (F : Finset ℂ) (hF : ∀ s ∈ F, 1 / 2 ≤ s.re ∧ s.re < 1 - ε) (K : ℕ) (c : ℂ → ℕ → ℂ) :
    ((∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n =>
        (globalPowerLogTraceVector ε F (fun s hs => ⟨by linarith [(hF s hs).1], (hF s hs).2⟩) K c :
          ℕ → ℝ) n + renormalizedCofactorOperator ε
          (globalPowerLogTraceVector ε F (fun s hs => ⟨by linarith [(hF s hs).1], (hF s hs).2⟩) K c)
            n) ≤ B) ∧
      (∃ B : ℝ, ∀ T : ℕ, pronicNorm T (fun n =>
        (globalPowerLogTraceVector ε F (fun s hs => ⟨by linarith [(hF s hs).1], (hF s hs).2⟩) K
          (fun s k => -I * c s k) : ℕ → ℝ) n + renormalizedCofactorOperator ε
          (globalPowerLogTraceVector ε F (fun s hs => ⟨by linarith [(hF s hs).1], (hF s hs).2⟩) K
            (fun s k => -I * c s k)) n) ≤ B)) ↔
      ∀ s ∈ F, ∀ k ≤ K, (analyticOrderAt riemannZeta (s + (ε : ℝ))).toNat ≤ k → c s k = 0 := by
  set hF' : ∀ s ∈ F, 0 < s.re ∧ s.re < 1 - ε :=
    fun s hs => ⟨by linarith [(hF s hs).1], (hF s hs).2⟩ with hF'def
  obtain ⟨B₁, hB₁⟩ := exists_pronicNorm_global_symbol_le ε F hF' K c
  obtain ⟨B₂, hB₂⟩ := exists_pronicNorm_global_symbol_le ε F hF' K (fun s k => -I * c s k)
  -- Leibniz coefficients of `−I c` are `−I` times those of `c`
  have hleibI : ∀ s n, powerLogRow s K (leibnizCoeff ε s K (fun k => -I * c s k)) n =
      -I * powerLogRow s K (leibnizCoeff ε s K (c s)) n := by
    intro s n
    simp only [powerLogRow, leibnizCoeff, mul_sum, sum_mul, mul_assoc]
  have himZ : ∀ n, (∑ s ∈ F, powerLogRow s K (leibnizCoeff ε s K (fun k => -I * c s k)) n).re =
      (∑ s ∈ F, powerLogRow s K (leibnizCoeff ε s K (c s)) n).im := by
    intro n
    simp only [hleibI]
    rw [← mul_sum]; simp [Complex.mul_re]
  -- the order data at each exponent
  have horder : ∀ s ∈ F, (∀ i < (analyticOrderAt riemannZeta (s + (ε : ℝ))).toNat,
      iteratedDeriv i riemannZeta (s + (ε : ℝ)) = 0) ∧
      iteratedDeriv (analyticOrderAt riemannZeta (s + (ε : ℝ))).toNat riemannZeta
        (s + (ε : ℝ)) ≠ 0 := by
    intro s hs
    have hz0 : 0 < (s + (ε : ℝ)).re := by simp; linarith [(hF s hs).1, ε.property.1]
    have hz1 : (s + (ε : ℝ)).re < 1 := by simp; linarith [(hF s hs).2]
    have hne1 : s + (ε : ℝ) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [(hF s hs).2]
    have hd : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    have han : AnalyticAt ℂ riemannZeta (s + (ε : ℝ)) := hd.analyticAt (isOpen_ne.mem_nhds hne1)
    exact (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero han).mp
      (ENat.coe_toNat (analyticOrderAt_riemannZeta_ne_top_of_strip hz0 hz1)).symm
  have hdiff : ∀ (f g : ℕ → ℝ) (Bf Bg : ℝ), (∀ T, pronicNorm T f ≤ Bf) →
      (∀ T, pronicNorm T (fun n => f n - g n) ≤ Bg) → ∀ T, pronicNorm T g ≤ Bf + Bg := by
    intro f g Bf Bg hf hfg T
    have h := BezoutValuationIncidence.pronicNorm_add_le T f (fun n => -(f n - g n))
    have hneg : pronicNorm T (fun n => -(f n - g n)) = pronicNorm T (fun n => f n - g n) := by
      simp only [BezoutValuationIncidence.pronicNorm, neg_sq]
    have heq : (fun n => f n + -(f n - g n)) = g := by funext n; ring
    rw [heq, hneg] at h
    linarith [hf T, hfg T]
  constructor
  · rintro ⟨⟨B, hB⟩, ⟨B', hB'⟩⟩
    have hre := hdiff _ _ B B₁ hB hB₁
    have him := hdiff _ _ B' B₂ hB' hB₂
    simp only [himZ] at him
    -- the Leibniz sum is complex-admitted
    have hZ : CAdmitted (fun n => ∑ s ∈ F, powerLogRow s K (leibnizCoeff ε s K (c s)) n) := by
      refine ⟨?_, (B + B₁) ^ 2 + (B' + B₂) ^ 2, fun T => ?_⟩
      · refine sum_eq_zero fun s hs => ?_
        exact powerLogRow_zero (fun h => by have := (hF s hs).1; rw [h, Complex.zero_re] at this
                                            linarith) K _
      · rw [cEnergy_eq_re_add_im]
        have h1 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hre T) 2
        have h2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) (him T) 2
        linarith
    have hcoeff := coeff_eq_zero_of_cAdmitted_sum (F := F)
      (fun s hs => ⟨(hF s hs).1, by linarith [(hF s hs).2, ε.property.1]⟩) K
      (fun s => leibnizCoeff ε s K (c s)) hZ
    intro s hs
    exact (leibnizCoeff_eq_zero_iff (horder s hs).1 (horder s hs).2 K (c s)).mp
      (hcoeff s hs)
  · intro hc
    have hzero : ∀ n, ∑ s ∈ F, powerLogRow s K (leibnizCoeff ε s K (c s)) n = 0 := by
      intro n
      refine sum_eq_zero fun s hs => sum_eq_zero fun d hd => ?_
      rw [(leibnizCoeff_eq_zero_iff (horder s hs).1 (horder s hs).2 K (c s)).mpr (hc s hs) d
        (Nat.lt_succ_iff.mp (mem_range.mp hd)), zero_mul]
    refine ⟨⟨B₁, fun T => ?_⟩, ⟨B₂, fun T => ?_⟩⟩
    · have h := hB₁ T
      simp only [hzero, Complex.zero_re, sub_zero] at h
      exact h
    · have h := hB₂ T
      simp only [himZ, hzero, Complex.zero_im, sub_zero] at h
      exact h

end GaloisForLFunctions.ArithmeticDefectRigidity
