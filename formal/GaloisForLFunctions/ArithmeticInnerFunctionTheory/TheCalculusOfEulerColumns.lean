import GaloisForLFunctions.ArithmeticInnerFunctionTheory.EchoTrainsOnIndependentReflectors
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# The calculus of signed Euler columns, and the Gamma base

An Euler column is `log p · Re(x/(1 − x))`, `x = p^{−½−a−ib}`, the local term of `−ζ′/ζ(½ + a + ib)`. With `r = p^{−½−a}` and `c = cos(b log p)` it is `log p · (rc − r²)/(1 − 2rc + r²)` (`colShape`, `re_div_one_sub`), increasing in `c`, with
maximum `r/(1 − r)` and minimum `−r/(1 + r)`.

* **Signed columns add** (`le_signedColumns_iff`). For distinct primes and any signs `s_p`, the infimum over `b` of `Σ_p s_p log p · colShape` is the sum of the column minima.
* **Products of columns are rigid** (`prod_nonneg_iff`). If each column is positive somewhere, the product of columns is nonnegative at all locked phases iff every column is nonnegative. So a sign cannot be moved between independent columns by multiplication.
* **The Sato–Tate pairing** (`integral_torusSum_mul_torusSum`, `tsum_mul_nonneg_of_torusPositive`). `∫ S_a S_b = Σ_k a_k b_k`, so two torus-positive amplitudes pair nonnegatively: the cone of torus-positive amplitudes lies in its own dual.

**The Gamma base.** Against the base `½ log(b/2π)` the current of a prime set `S` is `½ log(b/2π) − Σ_{p∈S} column_p(b)`.

* **The base pays by size** (`columnCurrent_pos_of_mass_lt`). If `Σ_{p∈S} log p/(p^{½+a} − 1) < ½ log(b/2π)`, the current is positive. For primes up to `P` this holds at every height with `log(b/2π) > 14√P log P` (`columnMass_le`).
* **Alignment has a height** (`exists_height_aligned`, `exists_columnCurrent_neg`). In every range `[B, BQ^{|S|}]` the phases of `S` align to within `2π/Q`. So if the aligned mass exceeds `½ log(BQ^{|S|}/2π)`, the current is negative at some height of that range.

Together these bracket the largest torus-positive prime set between the size of the mass and the height of alignment: columns near alignment are paid by the base as soon as `|S| log Q` passes twice the mass.
-/

open Finset Filter Topology MeasureTheory Set
open scoped Real

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

noncomputable section

/-! ### The shape of a column -/

/-- `Re(x/(1 − x))` for `|x| = r` and `cos(arg x) = c`. -/
def colShape (r c : ℝ) : ℝ := (r * c - r ^ 2) / (1 - 2 * r * c + r ^ 2)

variable {r c c' : ℝ}

theorem colShape_den_pos (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : c ≤ 1) : 0 < 1 - 2 * r * c + r ^ 2 := by
  nlinarith [mul_le_mul_of_nonneg_left hc hr0, sq_pos_of_pos (by linarith : 0 < 1 - r)]

/-- A column is increasing in the cosine of its phase. -/
theorem colShape_mono (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : c ≤ c') (hc' : c' ≤ 1) : colShape r c ≤ colShape r c' := by
  have h1 := colShape_den_pos hr0 hr1 (hc.trans hc')
  have h2 := colShape_den_pos hr0 hr1 hc'
  rw [colShape, colShape, div_le_div_iff₀ h1 h2]
  have h3 : 0 ≤ r * (1 - r ^ 2) * (c' - c) := by
    have : 0 ≤ 1 - r ^ 2 := by nlinarith
    exact mul_nonneg (mul_nonneg hr0 this) (by linarith)
  nlinarith

theorem colShape_one (hr1 : r < 1) : colShape r 1 = r / (1 - r) := by
  have h : 1 - r ≠ 0 := (sub_pos.mpr hr1).ne'
  have h2 : 1 - 2 * r * 1 + r ^ 2 = (1 - r) ^ 2 := by ring
  rw [colShape, h2, div_eq_div_iff (pow_ne_zero 2 h) h]
  ring

theorem colShape_neg_one (hr0 : 0 ≤ r) : colShape r (-1) = -(r / (1 + r)) := by
  have h : 1 + r ≠ 0 := by positivity
  have h2 : 1 - 2 * r * (-1) + r ^ 2 = (1 + r) ^ 2 := by ring
  rw [colShape, h2, ← neg_div, div_eq_div_iff (pow_ne_zero 2 h) h]
  ring

/-- The column is the real part of `x/(1 − x)`. -/
theorem re_div_one_sub (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    (((r : ℂ) * Complex.exp (θ * Complex.I)) / (1 - (r : ℂ) * Complex.exp (θ * Complex.I))).re =
      colShape r (Real.cos θ) := by
  set x : ℂ := (r : ℂ) * Complex.exp (θ * Complex.I) with hx
  have hxre : x.re = r * Real.cos θ := by
    rw [hx, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hxim : x.im = r * Real.sin θ := by
    rw [hx, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hsc := Real.sin_sq_add_cos_sq θ
  have hden : Complex.normSq (1 - x) = 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hxre, hxim]
    nlinarith
  have hne := colShape_den_pos hr0 hr1 (Real.cos_le_one θ)
  rw [Complex.div_re, hden, colShape]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hxre, hxim]
  rw [← add_div]
  congr 1
  linear_combination (-r ^ 2) * hsc

/-! ### Signed columns -/

/-- The radius of the column of `p` at abscissa `½ + a`. -/
def colRadius (a : ℝ) (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / 2 + a))

theorem colRadius_nonneg (a : ℝ) (p : ℕ) : 0 ≤ colRadius a p := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem colRadius_lt_one {a : ℝ} (ha : 0 ≤ a) {p : ℕ} (hp : 2 ≤ p) : colRadius a p < 1 := by
  have h : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg h (by linarith)

/-- The minimum of a signed column. -/
def signedMin (s r : ℝ) : ℝ := if 0 ≤ s then s * colShape r (-1) else s * colShape r 1

variable {n : ℕ}

/-- The re-parametrization of a signed column on the circle. -/
def signedColumn (w s r : ℝ) (z : Circle) : ℝ := s * w * colShape r ((z : ℂ).re)

theorem re_circle_mem (z : Circle) : (-1 : ℝ) ≤ (z : ℂ).re ∧ (z : ℂ).re ≤ 1 := by
  have h := Complex.abs_re_le_norm (z : ℂ)
  rw [Circle.norm_coe] at h
  exact abs_le.mp h

/-- The minimal value and its phase. -/
theorem signedColumn_min (hw : 0 ≤ w) (hr0 : 0 ≤ r) (hr1 : r < 1) (s : ℝ) (z : Circle) :
    w * signedMin s r ≤ signedColumn w s r z := by
  obtain ⟨h1, h2⟩ := re_circle_mem z
  have hm1 := colShape_mono hr0 hr1 h1 h2
  have hm2 := colShape_mono hr0 hr1 h2 le_rfl
  rw [signedMin, signedColumn]
  split_ifs with hs
  · have := mul_le_mul_of_nonneg_left hm1 (mul_nonneg hs hw)
    linarith
  · have := mul_le_mul_of_nonpos_left hm2 (mul_nonpos_of_nonpos_of_nonneg (not_le.mp hs).le hw)
    linarith

theorem continuous_signedColumn (hr0 : 0 ≤ r) (hr1 : r < 1) (w s : ℝ) : Continuous (signedColumn w s r) := by
  have hre : Continuous fun z : Circle => (z : ℂ).re :=
    Complex.continuous_re.comp continuous_subtype_val
  have hden : ∀ z : Circle, 1 - 2 * r * (z : ℂ).re + r ^ 2 ≠ 0 := fun z =>
    (colShape_den_pos hr0 hr1 (re_circle_mem z).2).ne'
  have e : signedColumn w s r = fun z : Circle =>
      s * w * ((r * (z : ℂ).re - r ^ 2) / (1 - 2 * r * (z : ℂ).re + r ^ 2)) := rfl
  rw [e]
  exact continuous_const.mul (((continuous_const.mul hre).sub continuous_const).div
    ((continuous_const.sub (continuous_const.mul hre)).add continuous_const) hden)

/-- **Signed columns add.** For distinct primes and any signs, the infimum over `b` of the signed sum of columns is the sum of the signed column minima. -/
theorem le_signedColumns_iff {a : ℝ} (ha : 0 ≤ a) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (s : Fin n → ℝ) (A : ℝ) :
    (∀ b : ℝ, A ≤ ∑ i, s i * Real.log (p i) * colShape (colRadius a (p i)) (Real.cos (b * Real.log (p i)))) ↔
      A ≤ ∑ i, Real.log (p i) * signedMin (s i) (colRadius a (p i)) := by
  have hr0 : ∀ i, 0 ≤ colRadius a (p i) := fun i => colRadius_nonneg a _
  have hr1 : ∀ i, colRadius a (p i) < 1 := fun i => colRadius_lt_one ha (hp i).two_le
  have hw : ∀ i, 0 ≤ Real.log (p i) := fun i => Real.log_natCast_nonneg _
  set g : Fin n → Circle → ℝ := fun i => signedColumn (Real.log (p i)) (s i) (colRadius a (p i)) with hg
  have hgc : ∀ i, Continuous (g i) := fun i => continuous_signedColumn (hr0 i) (hr1 i) _ _
  have hK := isKroneckerFamily_log_primes p hp hinj
  have hL := le_columnSum_iff hgc hK A
  have e : ∀ b : ℝ, columnSum g (fun i => Real.log (p i)) b =
      ∑ i, s i * Real.log (p i) * colShape (colRadius a (p i)) (Real.cos (b * Real.log (p i))) := fun b => by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, signedColumn, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  simp only [e] at hL
  rw [hL]
  constructor
  · intro h
    -- the torus point of the minima
    have hz := h fun i => if 0 ≤ s i then Circle.exp π else Circle.exp 0
    refine hz.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hg, signedColumn, signedMin]
    split_ifs with hs
    · simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_pi]
      ring
    · simp only [Circle.coe_exp, Complex.exp_ofReal_mul_I_re, Real.cos_zero]
      ring
  · intro h z
    exact h.trans (Finset.sum_le_sum fun i _ => signedColumn_min (hw i) (hr0 i) (hr1 i) _ _)

/-! ### Products of columns -/

/-- **Products of columns are rigid.** -/
theorem prod_nonneg_iff {g : Fin n → Circle → ℝ} (hg : ∀ i, Continuous (g i)) {ℓ : Fin n → ℝ}
    (hℓ : IsKroneckerFamily ℓ) (hp : ∀ i, ∃ w, 0 < g i w) :
    (∀ b : ℝ, 0 ≤ ∏ i, g i (Circle.exp (b * ℓ i))) ↔ ∀ i z, 0 ≤ g i z := by
  classical
  refine ⟨fun h i z => ?_, fun h b => Finset.prod_nonneg fun i _ => h i _⟩
  choose w hw using hp
  have hc : Continuous fun z : Fin n → Circle => ∏ i, g i (z i) :=
    continuous_finsetProd _ fun i _ => (hg i).comp (continuous_apply i)
  have hclosed : IsClosed {z : Fin n → Circle | 0 ≤ ∏ i, g i (z i)} := isClosed_le continuous_const hc
  have hall : ∀ y : Fin n → Circle, 0 ≤ ∏ i, g i (y i) := fun y => by
    refine closure_minimal ?_ hclosed (mem_closure_locked hℓ y)
    rintro _ ⟨b, rfl⟩
    exact h b
  have hu := hall (Function.update w i z)
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self] at hu
  have hrest : 0 < ∏ j ∈ Finset.univ.erase i, g j (Function.update w i z j) :=
    Finset.prod_pos fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      exact hw j
  exact nonneg_of_mul_nonneg_left hu hrest

/-! ### The Sato–Tate pairing -/

variable {a b : (Fin n → ℕ) → ℝ}

/-- **The Sato–Tate pairing of two torus sums.** -/
theorem integral_torusSum_mul_torusSum (ha : TraceSummable a) (hb : TraceSummable b) :
    ∫ θ, torusSum a θ * torusSum b θ ∂(torusMeasure n) = ∑' k, a k * b k := by
  set M := ∑' k, |a k| * chiSize k with hM
  have hMb : ∀ θ, |torusSum a θ| ≤ M := fun θ => abs_torusSum_le ha θ
  have hF : ∀ k, Integrable (fun θ => torusSum a θ * (b k * chiProd θ k)) (torusMeasure n) := fun k =>
    integrable_of_bounded_continuous (C := M * (|b k| * chiSize k))
      ((continuous_torusSum ha).mul (continuous_const.mul (continuous_chiProd k))) fun θ => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hMb θ) (mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans (hMb 0))
  have hsum : Summable fun k => ∫ θ, ‖torusSum a θ * (b k * chiProd θ k)‖ ∂(torusMeasure n) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _)
      (fun k => ?_) (hb.mul_left M)
    have hbd : ∀ θ, ‖torusSum a θ * (b k * chiProd θ k)‖ ≤ M * (|b k| * chiSize k) := fun θ => by
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hMb θ) (mul_le_mul_of_nonneg_left (abs_chiProd_le θ k) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans (hMb 0))
    calc ∫ θ, ‖torusSum a θ * (b k * chiProd θ k)‖ ∂(torusMeasure n)
        ≤ ∫ _ : Fin n → ℝ, M * (|b k| * chiSize k) ∂(torusMeasure n) :=
          integral_mono (hF k).norm (integrable_const _) hbd
      _ = _ := by simp
  have hs := hasSum_integral_of_summable_integral_norm hF hsum
  have e1 : ∀ θ, ∑' k, torusSum a θ * (b k * chiProd θ k) = torusSum a θ * torusSum b θ := fun θ => by
    rw [torusSum, tsum_mul_left]
    rfl
  simp_rw [e1] at hs
  have e2 : ∀ k, ∫ θ, torusSum a θ * (b k * chiProd θ k) ∂(torusMeasure n) = a k * b k := fun k => by
    have : (fun θ => torusSum a θ * (b k * chiProd θ k)) = fun θ => b k * (torusSum a θ * chiProd θ k) := by
      funext θ
      ring
    rw [this, integral_const_mul, integral_torusSum_mul_chiProd ha]
    ring
  simp_rw [e2] at hs
  exact hs.tsum_eq.symm

/-- **The cone lies in its own dual.** Two torus-positive amplitudes pair nonnegatively. -/
theorem tsum_mul_nonneg_of_torusPositive (ha : TraceSummable a) (hb : TraceSummable b)
    (hpa : ∀ θ, 0 ≤ torusSum a θ) (hpb : ∀ θ, 0 ≤ torusSum b θ) : 0 ≤ ∑' k, a k * b k := by
  rw [← integral_torusSum_mul_torusSum ha hb]
  exact integral_nonneg fun θ => mul_nonneg (hpa θ) (hpb θ)

/-! ### The Gamma base -/

/-- The mass of a prime set at abscissa `½ + a`: `Σ log p · r/(1 − r) = Σ log p/(p^{½+a} − 1)`. -/
def columnMass (a : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, Real.log p * (colRadius a p / (1 - colRadius a p))

/-- The sum of the columns of `S` at height `b`. -/
def columnsAt (a : ℝ) (S : Finset ℕ) (b : ℝ) : ℝ :=
  ∑ p ∈ S, Real.log p * colShape (colRadius a p) (Real.cos (b * Real.log p))

/-- The current of `S` against the Gamma base. -/
def columnCurrent (a : ℝ) (S : Finset ℕ) (b : ℝ) : ℝ := Real.log (b / (2 * π)) / 2 - columnsAt a S b

/-- Columns are at most their mass. -/
theorem columnsAt_le_mass {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) (b : ℝ) :
    columnsAt a S b ≤ columnMass a S := by
  refine Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)
  have hr := colRadius_lt_one ha (hS p hp)
  rw [← colShape_one hr]
  exact colShape_mono (colRadius_nonneg a p) hr (Real.cos_le_one _) le_rfl

/-- **The base pays by size.** -/
theorem columnCurrent_pos_of_mass_lt {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {b : ℝ}
    (hb : columnMass a S < Real.log (b / (2 * π)) / 2) : 0 < columnCurrent a S b := by
  have := columnsAt_le_mass ha hS b
  rw [columnCurrent]
  linarith

/-- `Σ_{n=1}^N 1/√n ≤ 2√N`. -/
theorem sum_inv_sqrt_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (Real.sqrt n)⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    have h1 : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ 2 = (N : ℝ) + 1 := by
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      ring
    have h2 : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg _)
    have hkey : (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤ 2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ)) := by
      rw [inv_le_iff_one_le_mul₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt (N : ℝ))]
    linarith

/-- **The mass of primes up to `P`.** `Σ_{p∈S} log p/(p^{½+a} − 1) ≤ 7√P log P` for `S ⊆ [2, P]`. -/
theorem columnMass_le {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} {P : ℕ}
    (hS : ∀ p ∈ S, 2 ≤ p ∧ p ≤ P) : columnMass a S ≤ 7 * Real.sqrt P * Real.log P := by
  have hLP : 0 ≤ Real.log P := Real.log_natCast_nonneg P
  have hterm : ∀ p ∈ S, Real.log p * (colRadius a p / (1 - colRadius a p)) ≤
      (7 / 2) * Real.log P * (Real.sqrt p)⁻¹ := fun p hp => by
    obtain ⟨h2, hle⟩ := hS p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h2
    have hlog : Real.log p ≤ Real.log P := Real.log_le_log hp0 (by exact_mod_cast hle)
    have hlog0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
    have hr : colRadius a p ≤ (Real.sqrt p)⁻¹ := by
      have e : (Real.sqrt p)⁻¹ = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hp0.le, Real.sqrt_eq_rpow]
      rw [e, colRadius]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hs2 : (7 / 5 : ℝ) ≤ Real.sqrt p := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
      linarith
    have hinv : (Real.sqrt p)⁻¹ ≤ 5 / 7 := by
      rw [inv_le_comm₀ hs (by norm_num)]
      norm_num
      linarith
    have hr0 := colRadius_nonneg a p
    have hden : (2 / 7 : ℝ) ≤ 1 - colRadius a p := by linarith
    have hq : colRadius a p / (1 - colRadius a p) ≤ (7 / 2) * (Real.sqrt p)⁻¹ := by
      rw [div_le_iff₀ (by linarith)]
      have h3 : 0 ≤ (Real.sqrt p)⁻¹ := by positivity
      nlinarith
    calc Real.log p * (colRadius a p / (1 - colRadius a p))
        ≤ Real.log P * ((7 / 2) * (Real.sqrt p)⁻¹) :=
          mul_le_mul hlog hq (div_nonneg hr0 (by linarith)) hLP
      _ = _ := by ring
  have hsub : S ⊆ Finset.Icc 1 P := fun p hp => by
    obtain ⟨h2, hle⟩ := hS p hp
    exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
  calc columnMass a S ≤ ∑ p ∈ S, (7 / 2) * Real.log P * (Real.sqrt p)⁻¹ := Finset.sum_le_sum hterm
    _ = (7 / 2) * Real.log P * ∑ p ∈ S, (Real.sqrt p)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (7 / 2) * Real.log P * ∑ n ∈ Finset.Icc 1 P, (Real.sqrt n)⁻¹ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
          (by positivity)
    _ ≤ (7 / 2) * Real.log P * (2 * Real.sqrt P) :=
        mul_le_mul_of_nonneg_left (sum_inv_sqrt_le P) (by positivity)
    _ = _ := by ring

/-- **Alignment has a height.** In `[B, BQ^{|S|}]` some height aligns all phases of `S` to within `2π/Q`. -/
theorem exists_height_aligned (S : Finset ℕ) {B : ℝ} (hB : 0 < B) {Q : ℕ} (hQ : 0 < Q) :
    ∃ b : ℝ, B ≤ b ∧ b ≤ B * (Q : ℝ) ^ S.card ∧
      ∀ p ∈ S, 1 - 2 * π ^ 2 / (Q : ℝ) ^ 2 ≤ Real.cos (b * Real.log p) := by
  classical
  let e := S.equivFin
  let β : Fin S.card → ℝ := fun j => B * Real.log ((e.symm j : ℕ)) / (2 * π)
  obtain ⟨q, hq1, hq2, hclose⟩ := HTGeometry.exists_simultaneous_dirichlet β hQ
  have hπ := Real.pi_pos
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  refine ⟨q * B, ?_, ?_, fun p hp => ?_⟩
  · have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith
  · have : (q : ℝ) ≤ (Q : ℝ) ^ S.card := by exact_mod_cast hq2
    nlinarith
  · obtain ⟨k, hk⟩ := hclose (e ⟨p, hp⟩)
    have hβ : β (e ⟨p, hp⟩) = B * Real.log p / (2 * π) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ] at hk
    set y : ℝ := (q : ℝ) * (B * Real.log p / (2 * π)) - k with hy
    have hx : (q : ℝ) * B * Real.log p = 2 * π * y + k * (2 * π) := by
      rw [hy]
      field_simp
      ring
    rw [hx, Real.cos_add_int_mul_two_pi]
    have hc := Real.one_sub_sq_div_two_le_cos (x := 2 * π * y)
    have hy2 : y ^ 2 ≤ (1 / (Q : ℝ)) ^ 2 := by
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg _) hk.le 2
    have e2 : 2 * π ^ 2 / (Q : ℝ) ^ 2 = (2 * π) ^ 2 * (1 / (Q : ℝ)) ^ 2 / 2 := by
      field_simp
    have e3 : (2 * π * y) ^ 2 / 2 = (2 * π) ^ 2 * y ^ 2 / 2 := by ring
    have h4 : (2 * π) ^ 2 * y ^ 2 / 2 ≤ (2 * π) ^ 2 * (1 / (Q : ℝ)) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left hy2 (sq_nonneg (2 * π))
      linarith
    rw [e2]
    linarith

/-- The aligned mass at resolution `Q`. -/
def alignedMass (a : ℝ) (S : Finset ℕ) (Q : ℕ) : ℝ :=
  ∑ p ∈ S, Real.log p * colShape (colRadius a p) (1 - 2 * π ^ 2 / (Q : ℝ) ^ 2)

/-- **Columns reach their aligned mass in a range of heights.** -/
theorem exists_columnsAt_ge {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {B : ℝ}
    (hB : 0 < B) {Q : ℕ} (hQ : 0 < Q) :
    ∃ b : ℝ, B ≤ b ∧ b ≤ B * (Q : ℝ) ^ S.card ∧ alignedMass a S Q ≤ columnsAt a S b := by
  obtain ⟨b, h1, h2, h3⟩ := exists_height_aligned S hB hQ
  refine ⟨b, h1, h2, Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg p)⟩
  exact colShape_mono (colRadius_nonneg a p) (colRadius_lt_one ha (hS p hp)) (h3 p hp) (Real.cos_le_one _)

/-- **Alignment below the base fails the current.** -/
theorem exists_columnCurrent_neg {a : ℝ} (ha : 0 ≤ a) {S : Finset ℕ} (hS : ∀ p ∈ S, 2 ≤ p) {B : ℝ}
    (hB : 0 < B) {Q : ℕ} (hQ : 0 < Q)
    (hlt : Real.log (B * (Q : ℝ) ^ S.card / (2 * π)) / 2 < alignedMass a S Q) :
    ∃ b : ℝ, B ≤ b ∧ b ≤ B * (Q : ℝ) ^ S.card ∧ columnCurrent a S b < 0 := by
  obtain ⟨b, h1, h2, h3⟩ := exists_columnsAt_ge ha hS hB hQ
  refine ⟨b, h1, h2, ?_⟩
  have hπ := Real.pi_pos
  have hb : 0 < b := lt_of_lt_of_le hB h1
  have hlog : Real.log (b / (2 * π)) ≤ Real.log (B * (Q : ℝ) ^ S.card / (2 * π)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right h2 (by positivity))
  rw [columnCurrent]
  linarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
