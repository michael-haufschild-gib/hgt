import GaloisForLFunctions.TransHorizonIncidenceMechanics.ResidueClassFlipsAndThePrimeDensityLaws
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfTheConstantSignPattern
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The quarter boundary of residue-class flips

A residue-class flip `f_{q,S}` (`residueFlip`) whose flipped unit classes have density
`ρ = #(S ∩ (ZMod q)ˣ)/φ(q)` at most `1/4` — the boundary `ρ = 1/4` included — has an unpaid
half-damped receiver (`not_receiverBounded_residueFlip_half_of_le`). The strict case `ρ < 1/4` is a
real-axis pole law; the boundary needs the off-axis size of the Dirichlet series near `w = 1`.

* **Complex class density** (`exists_abs_re_LSeries_classIndC_sub_le`): on the box
  `1 < Re s < 2`, `|Im s| < 1`, `Re Σ_{p ≡ a} p^{-s} = φ(q)^{-1} log(1/|s − 1|) + O(1)` for a unit
  class `a`. With `G(s) = Σ_{p ≡ a} p^{-s} + φ(q)^{-1} log(s − 1)`, the derivative is
  `−Aux_a(s) + (prime powers)`, bounded on the box by Mathlib's continuation of the residue-class
  L-function (`continuousOn_LFunctionResidueClassAux`), and the mean value theorem bounds `G`.
* **Euler lower bound** (`log_norm_patternSeries_ge`): for a `±1` pattern,
  `log|F(w)| ≥ log|ζ(w)| − 2 Σ_{f(p) = −1} Re p^{-w} − 2 Σ_p p^{-2}`.
* With `|ζ(w)| ≥ 1/(2|w − 1|)` near the pole this gives `|F(w)|² ≥ κ/|w − 1|` when `ρ ≤ 1/4`, and
  a local singularity `|C(s)|² ≥ κ/|s − 1/2|` of the shifted series makes the boundary line energy
  grow like `log(1/u)` (`not_receiverBounded_of_sq_norm_dirichletSeries_ge`), while a paid receiver
  caps it.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The complex density of one unit class -/

section classDensity

open ArithmeticFunction ArithmeticFunction.vonMangoldt LSeries

variable {q : ℕ} [NeZero q]

/-- The prime indicator of a residue class as a complex sequence. -/
def classIndC (a : ZMod q) (n : ℕ) : ℂ := ((primeResidueInd a n : ℝ) : ℂ)

theorem norm_classIndC_le (a : ZMod q) (n : ℕ) : ‖classIndC a n‖ ≤ 1 := by
  rw [classIndC, Complex.norm_real, Real.norm_eq_abs]
  unfold primeResidueInd; split_ifs <;> norm_num

theorem abscissaOfAbsConv_classIndC_le (a : ZMod q) : abscissaOfAbsConv (classIndC a) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_classIndC_le a n⟩

/-- The non-prime part of `Λ_a` as a complex sequence. -/
def classNonPrimeC (a : ZMod q) (n : ℕ) : ℂ := (((if n.Prime then 0 else residueClass a n) : ℝ) : ℂ)

/-- `Λ_a = log · [prime, ≡ a] + (non-prime part)`. -/
theorem residueClass_eq_logMul_add (a : ZMod q) :
    (fun n => ((residueClass a n : ℝ) : ℂ)) = logMul (classIndC a) + classNonPrimeC a := by
  funext n
  simp only [Pi.add_apply, logMul, classIndC, classNonPrimeC]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), ← Complex.ofReal_mul,
    ← Complex.ofReal_add, mul_comm, ← primeResidueLog_eq]
  unfold primeResidueLog
  split_ifs <;> simp

theorem norm_classNonPrimeC_le (a : ZMod q) (n : ℕ) :
    ‖classNonPrimeC a n‖ ≤ ‖((vonMangoldt n : ℝ) : ℂ)‖ := by
  rw [classNonPrimeC, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]
  split_ifs
  · simp [vonMangoldt_nonneg]
  · rw [abs_of_nonneg (residueClass_nonneg a n)]; exact residueClass_le a n

theorem LSeriesSummable_classNonPrimeC (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (classNonPrimeC a) s := by
  have h := (LSeriesSummable_vonMangoldt hs).norm
  refine Summable.of_norm_bounded h fun n => ?_
  rw [norm_term_eq, norm_term_eq]
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (norm_classNonPrimeC_le a n) (by positivity)

/-- The non-prime part is bounded on `Re s > 1` by its value at `1`. -/
theorem norm_LSeries_classNonPrimeC_le (a : ZMod q) {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (classNonPrimeC a) s‖ ≤ ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n := by
  have hsum := (LSeriesSummable_classNonPrimeC a hs).norm
  refine (norm_tsum_le_tsum_norm hsum).trans
    (Summable.tsum_le_tsum (fun n => ?_) hsum (summable_residueClass_non_primes_div a))
  rw [norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [if_neg hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ s.re := Real.rpow_le_rpow_of_exponent_le hn1 hs.le
  by_cases hp : n.Prime
  · simp [classNonPrimeC, hp]
  · simp only [classNonPrimeC, hp, if_false, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (residueClass_nonneg a n)]
    exact div_le_div_of_nonneg_left (residueClass_nonneg a n) (by linarith) hpow

/-- The box `1 < Re s < 2`, `|Im s| < 1`. -/
def nearOneBox : Set ℂ := {s | 1 < s.re} ∩ {s | s.re < 2} ∩ {s | -1 < s.im} ∩ {s | s.im < 1}

theorem convex_nearOneBox : Convex ℝ nearOneBox :=
  ((convex_halfSpace_re_gt 1).inter (convex_halfSpace_re_lt 2)).inter
    (convex_halfSpace_im_gt (-1)) |>.inter (convex_halfSpace_im_lt 1)

/-- **The complex logarithmic density of one unit class.** On the box `1 < Re s < 2`, `|Im s| < 1`:
`|Re Σ_{p ≡ a} p^{-s} − φ(q)^{-1} log(1/|s − 1|)| ≤ B`. -/
theorem exists_abs_re_LSeries_classIndC_sub_le {a : ZMod q} (ha : IsUnit a) :
    ∃ B : ℝ, ∀ s ∈ nearOneBox,
      |(LSeries (classIndC a) s).re - (q.totient : ℝ)⁻¹ * Real.log (1 / ‖s - 1‖)| ≤ B := by
  set φ : ℂ := (((q.totient : ℝ)⁻¹ : ℝ) : ℂ)
  -- the auxiliary function is bounded on the closed box
  set K : Set ℂ := (Icc (1 : ℝ) 2) ×ℂ (Icc (-1 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨MA, hMA⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_LFunctionResidueClassAux a).mono fun s hs => by
      have := (Complex.mem_reProdIm.mp hs).1; exact this.1)
  set C₀ := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n
  set G : ℂ → ℂ := fun s => LSeries (classIndC a) s + φ * Complex.log (s - 1)
  set G' : ℂ → ℂ := fun s => -LSeries (logMul (classIndC a)) s + φ * (1 / (s - 1))
  have hderiv : ∀ s ∈ nearOneBox, HasDerivWithinAt G (G' s) nearOneBox s := by
    intro s hs
    have hs1 : 1 < s.re := hs.1.1.1
    have habs : abscissaOfAbsConv (classIndC a) < s.re :=
      (abscissaOfAbsConv_classIndC_le a).trans_lt (by exact_mod_cast hs1)
    have hslit : s - 1 ∈ slitPlane := Or.inl (by simp; linarith)
    have hlog := (((hasDerivAt_id s).sub_const 1).clog hslit).const_mul φ
    have hL := LSeries_hasDerivAt habs
    refine (hL.add hlog).hasDerivWithinAt.congr_deriv ?_
    simp only [G', id]
  -- `G' = −Aux + (non-prime part)` on the box
  have hG' : ∀ s ∈ nearOneBox, ‖G' s‖ ≤ MA + C₀ := by
    intro s hs
    have hs1 : 1 < s.re := hs.1.1.1
    have hAux := eqOn_LFunctionResidueClassAux ha (show s ∈ {s : ℂ | 1 < s.re} from hs1)
    have hsplit : LSeries (fun n => ((residueClass a n : ℝ) : ℂ)) s =
        LSeries (logMul (classIndC a)) s + LSeries (classNonPrimeC a) s := by
      rw [residueClass_eq_logMul_add a, LSeries_add
        (LSeriesSummable_logMul_of_lt_re ((abscissaOfAbsConv_classIndC_le a).trans_lt
          (by exact_mod_cast hs1))) (LSeriesSummable_classNonPrimeC a hs1)]
    have hform : G' s = -LFunctionResidueClassAux a s + LSeries (classNonPrimeC a) s := by
      simp only [G', φ]
      beta_reduce at hAux
      rw [hAux, hsplit]
      push_cast
      ring
    rw [hform]
    have hmem : s ∈ K := Complex.mem_reProdIm.mpr
      ⟨⟨hs.1.1.1.le, hs.1.1.2.le⟩, ⟨hs.1.2.le, hs.2.le⟩⟩
    calc ‖-LFunctionResidueClassAux a s + LSeries (classNonPrimeC a) s‖
        ≤ ‖LFunctionResidueClassAux a s‖ + ‖LSeries (classNonPrimeC a) s‖ := by
          rw [← norm_neg (LFunctionResidueClassAux a s)]; exact norm_add_le _ _
      _ ≤ MA + C₀ := add_le_add (hMA s hmem) (norm_LSeries_classNonPrimeC_le a hs1)
  have h32 : (3 / 2 : ℂ) ∈ nearOneBox := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> norm_num
  refine ⟨‖G (3 / 2)‖ + (MA + C₀) * 2, fun s hs => ?_⟩
  have hmv := convex_nearOneBox.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hG' h32 hs
  have hdist : ‖s - 3 / 2‖ ≤ 2 := by
    obtain ⟨⟨⟨hr1, hr2⟩, hi1⟩, hi2⟩ := hs
    simp only [Set.mem_setOf_eq] at hr1 hr2 hi1 hi2
    have := Complex.norm_le_abs_re_add_abs_im (s - 3 / 2)
    have h1 : |(s - 3 / 2).re| ≤ 1 := by
      rw [abs_le]; simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.re_ofNat]
      constructor <;> linarith
    have h2 : |(s - 3 / 2).im| ≤ 1 := by
      rw [abs_le]; simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.im_ofNat]
      constructor <;> linarith
    linarith
  have hC : 0 ≤ MA + C₀ := le_trans (norm_nonneg _) (hG' _ h32)
  have hGs : ‖G s‖ ≤ ‖G (3 / 2)‖ + (MA + C₀) * 2 := by
    have := norm_le_insert' (G s) (G (3 / 2))
    nlinarith [mul_le_mul_of_nonneg_left hdist hC]
  -- `Re G(s) = Re L(s) − φ log(1/|s − 1|)`
  have hre : (G s).re = (LSeries (classIndC a) s).re -
      (q.totient : ℝ)⁻¹ * Real.log (1 / ‖s - 1‖) := by
    simp only [G, φ, Complex.add_re, Complex.re_ofReal_mul, Complex.log_re, one_div,
      Real.log_inv]
    ring
  rw [← hre]
  exact (Complex.abs_re_le_norm _).trans hGs


end classDensity

/-! ### The Euler lower bound of a `±1` pattern -/

/-- `‖log(1 + v) − v‖ ≤ ‖v‖²` for `‖v‖ ≤ 1/2`. -/
theorem norm_log_one_add_sub_self_le_sq {v : ℂ} (hv : ‖v‖ ≤ 1 / 2) :
    ‖Complex.log (1 + v) - v‖ ≤ ‖v‖ ^ 2 := by
  have h := Complex.norm_log_one_add_sub_self_le (show ‖v‖ < 1 by linarith)
  have hpos : 0 < 1 - ‖v‖ := by linarith
  have hinv : (1 - ‖v‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos (by norm_num)]; linarith
  refine h.trans ?_
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg ‖v‖]

/-- One flipped Euler factor: `Re(−log(1 + y)) ≥ Re(−log(1 − y)) − 2 Re y − 2|y|²` for `|y| ≤ 1/2`. -/
theorem re_neg_log_one_add_ge {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    (-Complex.log (1 - y)).re - 2 * y.re - 2 * ‖y‖ ^ 2 ≤ (-Complex.log (1 + y)).re := by
  have h1 := (Complex.abs_re_le_norm _).trans (norm_log_one_add_sub_self_le_sq hy)
  have h2 := (Complex.abs_re_le_norm _).trans
    (norm_log_one_add_sub_self_le_sq (v := -y) (by rw [norm_neg]; exact hy))
  rw [norm_neg, ← sub_eq_add_neg] at h2
  simp only [Complex.sub_re, Complex.neg_re] at h1 h2 ⊢
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.2]

/-- **The Euler lower bound of a `±1` pattern.** For completely multiplicative `f` with
`f(p) = ±1` and `Re w > 1`:
`log|F(w)| ≥ log|ζ(w)| − 2 Σ_{f(p) = −1} Re p^{-w} − 2 Σ_p p^{-2}`. -/
theorem log_norm_patternSeries_ge (f : ℕ →*₀ ℝ) (hf : ∀ p : ℕ, p.Prime → f p = 1 ∨ f p = -1)
    {w : ℂ} (hw : 1 < w.re) :
    0 < ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ∧
    Real.log ‖riemannZeta w‖ -
        2 * ∑' p : Nat.Primes, (if f p = -1 then (((p : ℕ) : ℂ) ^ (-w)).re else 0) -
        2 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤
      Real.log ‖∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ := by
  set g := cweightedPatternHom f w
  have habs : ∀ n, |f n| ≤ 1 := by
    intro n
    induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime p hp => rcases hf p hp with h | h <;> simp [h]
    | mul a b ha hb => rw [map_mul, abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb
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
  have hgy : ∀ p : Nat.Primes, g p = (f p : ℂ) * y p := fun p => by
    simp only [g, y, cweightedPatternHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
      Complex.ofReal_natCast]
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
  have hgs : Summable (fun p : Nat.Primes => g p) :=
    hys.norm.of_norm_bounded fun p => by
      rw [hgy, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (habs p)
  have hL1 : Summable (fun p : Nat.Primes => -Complex.log (1 - g p)) := hgs.clog_one_sub.neg
  have hL2 : Summable (fun p : Nat.Primes => -Complex.log (1 - y p)) := hys.clog_one_sub.neg
  have hre1 : Summable (fun p : Nat.Primes => (-Complex.log (1 - g p)).re) :=
    Complex.reCLM.summable hL1
  have hre2 : Summable (fun p : Nat.Primes => (-Complex.log (1 - y p)).re) :=
    Complex.reCLM.summable hL2
  have hF : Real.log ‖∑' n, g n‖ = ∑' p : Nat.Primes, (-Complex.log (1 - g p)).re := by
    rw [← hE, Complex.norm_exp, Complex.re_tsum hL1, Real.log_exp]
  have hζ : Real.log ‖riemannZeta w‖ = ∑' p : Nat.Primes, (-Complex.log (1 - y p)).re := by
    rw [← hZ, Complex.norm_exp, Complex.re_tsum hL2, Real.log_exp]
  have hsq2 : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have hysq : ∀ p : Nat.Primes, ‖y p‖ ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := fun p => by
    rw [hnorm_y, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.one_lt.le
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by push_cast; linarith)
  set I : Nat.Primes → ℝ := fun p => if f p = -1 then (y p).re else 0
  have hIs : Summable I := hys.norm.of_norm_bounded fun p => by
    simp only [I]; split_ifs
    · exact Complex.abs_re_le_norm _
    · simp
  have hterm : ∀ p : Nat.Primes, (-Complex.log (1 - y p)).re - 2 * I p -
      2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) ≤ (-Complex.log (1 - g p)).re := by
    intro p
    have hq := hysq p
    simp only [I]
    rcases hf p p.2 with h | h
    · have hne : f p ≠ -1 := by rw [h]; norm_num
      rw [if_neg hne, hgy, h]
      simp only [Complex.ofReal_one, one_mul]
      have : 0 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    · rw [if_pos h, hgy, h]
      have hflip := re_neg_log_one_add_ge (hyhalf p)
      simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, sub_neg_eq_add]
      linarith
  have hsumle := Summable.tsum_le_tsum hterm
    ((hre2.sub (hIs.mul_left 2)).sub (hsq2.mul_left 2)) hre1
  rw [(hre2.sub (hIs.mul_left 2)).tsum_sub (hsq2.mul_left 2), hre2.tsum_sub (hIs.mul_left 2),
    tsum_mul_left, tsum_mul_left] at hsumle
  have hseries : ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) = ∑' n, g n := rfl
  refine ⟨?_, ?_⟩
  · rw [hseries, ← hE]; exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  rw [hseries, hF, hζ]
  exact hsumle


/-! ### The flipped prime sum as a sum of class series -/

section flipSum

open LSeries

variable {q : ℕ} [NeZero q]

/-- `Re Σ_{p mod q ∈ S} p^{-w} = Σ_{a ∈ S} Re Σ_{p ≡ a} p^{-w}` on `Re w > 1`. -/
theorem tsum_residueFlip_re_eq (S : Finset (ZMod q)) {w : ℂ} (hw : 1 < w.re) :
    ∑' p : Nat.Primes, (if residueFlip q S p = -1 then (((p : ℕ) : ℂ) ^ (-w)).re else 0) =
      ∑ a ∈ S, (LSeries (classIndC a) w).re := by
  have hsumm : ∀ a : ZMod q, LSeriesSummable (classIndC a) w := fun a =>
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_classIndC_le a).trans_lt (by exact_mod_cast hw))
  set h : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) ∈ S then (((n : ℂ)) ^ (-w)).re else 0
  have hprimes : ∑' p : Nat.Primes,
      (if residueFlip q S p = -1 then (((p : ℕ) : ℂ) ^ (-w)).re else 0) = ∑' n, h n := by
    have hsupp : Function.support h ⊆ {n : ℕ | n.Prime} := fun n hn => by
      simp only [h, Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
      exact hn.1.1
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun p => ?_
    have hp : ((p : {n : ℕ | n.Prime}) : ℕ).Prime := p.2
    simp only [h, residueFlip_prime_eq_neg_one_iff q S hp, hp, true_and]
  have hterm : ∀ n, h n = ∑ a ∈ S, (term (classIndC a) w n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h, Nat.not_prime_zero]
    simp only [h, term, hn, if_false, classIndC, primeResidueInd]
    by_cases hp : n.Prime
    · simp only [hp, true_and]
      have hdiv : ∀ a : ZMod q, (((if (n : ZMod q) = a then (1 : ℝ) else 0 : ℝ) : ℂ) / (n : ℂ) ^ w).re =
          if (n : ZMod q) = a then ((n : ℂ) ^ (-w)).re else 0 := fun a => by
        split_ifs
        · rw [Complex.ofReal_one, one_div, Complex.cpow_neg]
        · simp
      simp_rw [hdiv]
      rw [Finset.sum_ite_eq]
    · simp [hp]
  rw [hprimes, tsum_congr hterm, Summable.tsum_finsetSum fun a _ =>
    Complex.reCLM.summable (hsumm a)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LSeries, Complex.re_tsum (hsumm a)]

/-- A class of non-units: `|Re Σ_{p ≡ a} p^{-w}| ≤ q + 1` on `Re w > 1`. -/
theorem abs_re_LSeries_classIndC_le_of_not_isUnit {a : ZMod q} (ha : ¬ IsUnit a) {w : ℂ}
    (hw : 1 < w.re) : |(LSeries (classIndC a) w).re| ≤ q + 1 := by
  have hsumm : LSeriesSummable (classIndC a) w :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      ((abscissaOfAbsConv_classIndC_le a).trans_lt (by exact_mod_cast hw))
  have hnorm : ∀ n, ‖term (classIndC a) w n‖ = primeResidueInd a n / (n : ℝ) ^ w.re := by
    intro n
    rw [norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [primeResidueInd, Nat.not_prime_zero]
    rw [if_neg hn, classIndC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    unfold primeResidueInd; split_ifs <;> norm_num
  refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm hsumm.norm).trans ?_)
  rw [tsum_congr hnorm]
  exact (tsum_primeResidueInd_mem_of_not_isUnit ha hw).2

end flipSum

/-! ### A local singularity of order `1/2` at `s = 1/2` is never paid -/

/-- The shifted Dirichlet series of a pattern weight `f(d) d^{-1/2}`. -/
theorem weightDirichletSeries_pattern (f : ℕ →*₀ ℝ) (s : ℂ) :
    weightDirichletSeries (fun d => f d * (d : ℝ) ^ (-(1 / 2 : ℝ))) s =
      ∑' n : ℕ, (f n : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1 / 2)) := by
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  simp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hd0.le, mul_assoc, ← Complex.cpow_add _ _ hdC]
  congr 2
  push_cast
  ring

/-- **A local `|s − 1/2|^{-1/2}` singularity is never paid.** If `c` is half-damped and
`|C(s)|² ≥ κ/|s − 1/2|` for `Re s > 1/2`, `|s − 1/2| < ρ₀`, the receiver of `c` is unbounded: the
segment `0 ≤ t ≤ r` of the line `Re s = 1/2 + u` carries line energy `≥ κ' log(1/u) − O(1)`, while a
paid receiver caps every line energy. -/
theorem not_receiverBounded_of_sq_norm_dirichletSeries_ge {K κ ρ₀ : ℝ} {c : ℕ → ℝ}
    (hc : DampedClass K (1 / 2) c) (hκ : 0 < κ) (hρ₀ : 0 < ρ₀)
    (hlow : ∀ s : ℂ, 1 / 2 < s.re → ‖s - 1 / 2‖ < ρ₀ →
      κ / ‖s - 1 / 2‖ ≤ ‖weightDirichletSeries c s‖ ^ 2) :
    ¬ ReceiverBounded c := by
  rintro ⟨E, hE⟩
  set m : ℝ := ∑' d : ℕ, c d / d
  obtain ⟨r₁, hr₁, hζh⟩ := exists_norm_zeta_gt_near_half
  set r : ℝ := min (min ρ₀ r₁ / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  have hrρ : 2 * r < ρ₀ := by
    have := min_le_left (min ρ₀ r₁ / 4) (1 / 4)
    have := min_le_left ρ₀ r₁
    linarith
  have hr1 : 2 * r < r₁ := by
    have := min_le_left (min ρ₀ r₁ / 4) (1 / 4)
    have := min_le_right ρ₀ r₁
    linarith
  set κ' : ℝ := κ / 8
  have hκ' : 0 < κ' := by positivity
  -- pointwise lower bound on the segment
  have hpt : ∀ u t : ℝ, 0 < u → u ≤ r → 0 ≤ t → t ≤ r →
      κ' / (u + t) - m ^ 2 / 4 ≤ lineIntegrand c m (1 / 2 + u) t := by
    intro u t hu hur ht htr
    set s : ℂ := (((1 / 2 + u : ℝ)) : ℂ) + t * I
    have hs2 : s - 1 / 2 = (u : ℂ) + t * I := by simp only [s]; push_cast; ring
    have hnorm_ut : ‖(u : ℂ) + t * I‖ ≤ u + t := by
      have := Complex.norm_le_abs_re_add_abs_im ((u : ℂ) + t * I)
      simpa [abs_of_pos hu, abs_of_nonneg ht] using this
    have hnorm_ut0 : u ≤ ‖(u : ℂ) + t * I‖ := by
      have := Complex.abs_re_le_norm ((u : ℂ) + t * I)
      simpa [abs_of_pos hu] using this
    have hζs : 1 / 2 < ‖riemannZeta s‖ := hζh s (by rw [hs2]; linarith)
    have hsre : s.re = 1 / 2 + u := by simp [s]
    have hs1 : ‖s‖ ≤ 1 := by
      have := Complex.norm_le_abs_re_add_abs_im s
      have him : s.im = t := by simp [s]
      rw [hsre, him, abs_of_pos (by linarith), abs_of_nonneg ht] at this
      linarith
    have hs0 : 0 < ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hsre, abs_of_pos (by linarith)] at this
      linarith
    have hP2 : κ / (u + t) ≤ ‖weightDirichletSeries c s‖ ^ 2 := by
      have h := hlow s (by rw [hsre]; linarith) (by rw [hs2]; linarith)
      rw [hs2] at h
      exact le_trans (div_le_div_of_nonneg_left hκ.le (by linarith) hnorm_ut) h
    set P := ‖weightDirichletSeries c s‖
    set Y := ‖weightDirichletSeries c s - (m : ℂ)‖
    have hPY : P ≤ Y + |m| := by
      have h := norm_sub_norm_le (weightDirichletSeries c s) (m : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      linarith
    have hY0 : 0 ≤ Y := norm_nonneg _
    have hP0 : 0 ≤ P := norm_nonneg _
    have hYP : P ^ 2 / 2 - m ^ 2 ≤ Y ^ 2 := by
      have h := pow_le_pow_left₀ hP0 hPY 2
      nlinarith [sq_nonneg (Y - |m|), sq_abs m]
    have hint : lineIntegrand c m (1 / 2 + u) t = (‖riemannZeta s‖ * Y / ‖s‖) ^ 2 := by
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
    have hκe : κ' / (u + t) = κ / (u + t) / 8 := by
      simp only [κ']; ring
    rw [hκe]
    linarith
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
  -- the segment `0 ≤ t ≤ r` carries `κ' log((u + r)/u) − m² r/4`
  have hlowI : ∀ u : ℝ, 0 < u → u ≤ r →
      κ' * Real.log ((u + r) / u) - m ^ 2 / 4 * r ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := by
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
    have hg : IntervalIntegrable (fun t : ℝ => κ' * (u + t)⁻¹ - m ^ 2 / 4) volume 0 r :=
      (hinv.const_mul κ').sub intervalIntegrable_const
    have hval : ∫ t in (0 : ℝ)..r, (κ' * (u + t)⁻¹ - m ^ 2 / 4) =
        κ' * Real.log ((u + r) / u) - m ^ 2 / 4 * r := by
      rw [intervalIntegral.integral_sub (hinv.const_mul κ') intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_left (fun x => x⁻¹),
        add_zero, integral_inv_of_pos hu (by linarith), intervalIntegral.integral_const, smul_eq_mul]
      ring
    calc κ' * Real.log ((u + r) / u) - m ^ 2 / 4 * r
        = ∫ t in (0 : ℝ)..r, (κ' * (u + t)⁻¹ - m ^ 2 / 4) := hval.symm
      _ ≤ ∫ t in (0 : ℝ)..r, lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_mono_on hr.le hg hfi.intervalIntegrable fun t ht => by
            have := hpt u t hu hur ht.1 ht.2
            rwa [div_eq_mul_inv] at this
      _ = ∫ t in Ioc (0 : ℝ) r, lineIntegrand c m (1 / 2 + u) t :=
          intervalIntegral.integral_of_le hr.le
      _ ≤ ∫ t, lineIntegrand c m (1 / 2 + u) t := setIntegral_le_integral hfi hf0
  -- choose `u = r e^{-X}` with `κ' X > 4πE + m² r/4`
  set X : ℝ := (4 * Real.pi * E + m ^ 2 / 4 * r + 1) / κ'
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
  have h1 := hlowI u hu hur
  have h2 := hup u hu hur
  have hκX : κ' * X = 4 * Real.pi * E + m ^ 2 / 4 * r + 1 := by
    simp only [X]; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog hκ'.le]

/-! ### The boundary of the quarter law for residue-class flips -/

/-- **Residue-class flips at or below the quarter are never paid at half damping**: if
`4 #(S ∩ (ZMod q)ˣ) ≤ φ(q)`, the weight `f_{q,S}(d) d^{-1/2}` has unbounded receiver. -/
theorem not_receiverBounded_residueFlip_half_of_le {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (h4 : 4 * (S.filter IsUnit).card ≤ q.totient) :
    ¬ ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  -- class constants
  choose B hB using fun a : ZMod q => (show ∃ B : ℝ, ∀ s ∈ nearOneBox,
      (LSeries (classIndC a) s).re ≤
        (if IsUnit a then (q.totient : ℝ)⁻¹ else 0) * Real.log (1 / ‖s - 1‖) + B by
    by_cases ha : IsUnit a
    · obtain ⟨B, hB⟩ := exists_abs_re_LSeries_classIndC_sub_le ha
      exact ⟨B, fun s hs => by rw [if_pos ha]; linarith [(abs_le.mp (hB s hs)).2]⟩
    · refine ⟨q + 1, fun s hs => ?_⟩
      rw [if_neg ha, zero_mul, zero_add]
      exact (le_abs_self _).trans (abs_re_LSeries_classIndC_le_of_not_isUnit ha hs.1.1.1))
  obtain ⟨ρ, hρ, hζ1⟩ := exists_norm_zeta_ge_near_one
  set ρ' : ℝ := min (min ρ 1) (1 / 2)
  have hρ' : 0 < ρ' := lt_min (lt_min hρ one_pos) (by norm_num)
  set δ : ℝ := (S.filter IsUnit).card / q.totient
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hδ : δ ≤ 1 / 4 := by
    simp only [δ]
    rw [div_le_iff₀ hφ]
    have : (4 : ℝ) * (S.filter IsUnit).card ≤ q.totient := by exact_mod_cast h4
    linarith
  have hδ0 : 0 ≤ δ := by positivity
  set S₂ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)
  set B' : ℝ := Real.log 2 + 2 * ∑ a ∈ S, |B a| + 2 * S₂
  refine not_receiverBounded_of_sq_norm_dirichletSeries_ge (K := 1) (κ := Real.exp (-(2 * B')))
    (ρ₀ := ρ') (fun d => ?_) (Real.exp_pos _) hρ' fun s hs hsρ => ?_
  · rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    refine mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) ?_
    have := (residueFlip q S).map_one
    induction d using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime p hp => rcases residueFlip_prime_eq_one_or q S hp with h | h <;> simp [h]
    | mul a b ha hb => rw [map_mul, abs_mul]; exact mul_le_one₀ ha (abs_nonneg _) hb
  · -- the point `w = s + 1/2` near the pole
    set w : ℂ := s + 1 / 2
    have hw1 : w - 1 = s - 1 / 2 := by simp only [w]; ring
    have hwpos : 0 < ‖w - 1‖ := by
      rw [hw1]
      refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm _)
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      rw [abs_of_pos (by linarith)]; linarith
    have hwρ : ‖w - 1‖ < ρ' := by rw [hw1]; exact hsρ
    have hwle1 : ‖w - 1‖ ≤ 1 := by
      have := min_le_left (min ρ 1) (1 / 2)
      have := min_le_right ρ 1
      linarith
    have hwre : 1 < w.re := by
      simp only [w, Complex.add_re, Complex.div_ofNat_re, Complex.one_re]; linarith
    have hwbox : w ∈ nearOneBox := by
      have hre := Complex.abs_re_le_norm (w - 1)
      have him := Complex.abs_im_le_norm (w - 1)
      have hhalf : ‖w - 1‖ < 1 / 2 := lt_of_lt_of_le hwρ (min_le_right _ _)
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at hre him
      rw [abs_lt] at *
      refine ⟨⟨⟨hwre, ?_⟩, ?_⟩, ?_⟩ <;> simp only [Set.mem_setOf_eq] <;>
        linarith [abs_lt.mp (lt_of_le_of_lt hre hhalf), abs_lt.mp (lt_of_le_of_lt him hhalf)]
    have hwne : w ≠ 1 := fun h => by rw [h, sub_self, norm_zero] at hwpos; exact lt_irrefl _ hwpos
    -- `log|ζ(w)| ≥ ℓ − log 2`, `ℓ = log(1/|w − 1|) ≥ 0`
    set ℓ := Real.log (1 / ‖w - 1‖)
    have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by rw [le_div_iff₀ hwpos]; linarith)
    have hζw : ℓ - Real.log 2 ≤ Real.log ‖riemannZeta w‖ := by
      have h := hζ1 w hwne (lt_of_lt_of_le hwρ (by
        have := min_le_left (min ρ 1) (1 / 2); have := min_le_left ρ 1; linarith))
      have hpos : 0 < 1 / (2 * ‖w - 1‖) := by positivity
      have := Real.log_le_log hpos h
      rw [show 1 / (2 * ‖w - 1‖) = (1 / ‖w - 1‖) / 2 by field_simp,
        Real.log_div (by positivity) (by norm_num)] at this
      linarith
    -- the flipped prime sum
    have hflip : ∑' p : Nat.Primes,
        (if residueFlip q S p = -1 then (((p : ℕ) : ℂ) ^ (-w)).re else 0) ≤ δ * ℓ + ∑ a ∈ S, |B a| := by
      rw [tsum_residueFlip_re_eq S hwre]
      calc ∑ a ∈ S, (LSeries (classIndC a) w).re
          ≤ ∑ a ∈ S, ((if IsUnit a then (q.totient : ℝ)⁻¹ else 0) * ℓ + |B a|) :=
            Finset.sum_le_sum fun a _ => (hB a w hwbox).trans (by linarith [le_abs_self (B a)])
        _ = δ * ℓ + ∑ a ∈ S, |B a| := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero,
              add_zero, Finset.sum_const, nsmul_eq_mul]
            simp only [δ]
            ring
    obtain ⟨hFpos, hFlog⟩ := log_norm_patternSeries_ge (residueFlip q S)
      (fun p hp => residueFlip_prime_eq_one_or q S hp) hwre
    -- `log|F(w)| ≥ ℓ/2 − B'`
    have hkey : ℓ / 2 - B' ≤ Real.log ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ := by
      have hB0 : 0 ≤ ∑ a ∈ S, |B a| := Finset.sum_nonneg fun a _ => abs_nonneg _
      have hδℓ : δ * ℓ ≤ ℓ / 4 := by nlinarith
      simp only [B']
      linarith
    -- square: `|F(w)|² ≥ e^{-2B'}/|w − 1|`
    rw [weightDirichletSeries_pattern, ← hw1]
    set F := ‖∑' n : ℕ, (residueFlip q S n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖
    have hFexp : Real.exp (ℓ / 2 - B') ≤ F := by
      rw [← Real.exp_log hFpos]; exact Real.exp_le_exp.mpr hkey
    have hsq := pow_le_pow_left₀ (Real.exp_pos _).le hFexp 2
    rw [← Real.exp_nat_mul] at hsq
    have hval : Real.exp (-(2 * B')) / ‖w - 1‖ = Real.exp (((2 : ℕ) : ℝ) * (ℓ / 2 - B')) := by
      rw [show ((2 : ℕ) : ℝ) * (ℓ / 2 - B') = ℓ + -(2 * B') by push_cast; ring, Real.exp_add,
        Real.exp_log (by positivity), mul_comm, one_div, ← div_eq_mul_inv]
    rw [hval]
    exact hsq

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
