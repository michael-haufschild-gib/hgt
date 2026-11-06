import GaloisForLFunctions.SquareRootThreshold.EffectiveHorizons.HeatGridDegrees
import GaloisForLFunctions.RHTower.ChebyshevShortWindowLowerBound
import GaloisForLFunctions.RHTower.ZetaLocalZeroCount
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.RHTower.XiHadamardSharpRegion
import GaloisForLFunctions.RHTower.VonKochChebyshevBound

/-!
# The prime number theorem and Mertens' theorem with explicit constants

For every `x ≥ 2`,

* `|ψ(x) − x| ≤ 1000 x exp(−√(log x)/20)` (`abs_psi_sub_le`);
* `|Σ_{n≤x} Λ(n)/n − log x + γ| ≤ 6400 exp(−√(log x)/20)` (`abs_mertens_sub_le`).

The input is the zero sum `δ(x) = Σ_ρ x^{β−1}/(|ρ||1−ρ|)`. Below height `T` the zero-free region gives
`x^{β−1} ≤ exp(−log x/(58 log T))`; above `T` the local count `40 log(180|t|)` bounds the tail by `480 log(360T)/T`;
and `T = exp(√(log x)/8)` gives `δ(x) ≤ 5300 exp(−√(log x)/10)`. The genus-kernel explicit formula evaluates the window
statistic squeezing `ψ` up to `2δ/w`, so a window of relative width `η = √δ` gives the first bound. The explicit formula
at one point then gives the second.
-/

open Complex Finset

namespace RHTower.ExplicitPNT

noncomputable section

theorem rpow_anti {a b z : ℝ} (ha : 0 < a) (hab : a ≤ b) (hz : z ≤ 0) : b ^ z ≤ a ^ z := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos (ha.trans_le hab)]
  apply Real.exp_le_exp.2
  have h := Real.log_le_log ha hab
  nlinarith only [h, hz]

/-- Chebyshev's linear bound in the form used below. -/
theorem psi_le_six_mul {x : ℝ} (hx : 1 ≤ x) : Chebyshev.psi x ≤ 6 * x := by
  have h := Chebyshev.psi_le hx
  have hs := Real.sqrt_nonneg x
  have hx0 : 0 < x := by linarith only [hx]
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [← Real.log_rpow (Real.sqrt_pos.mpr hx0), Real.rpow_two, Real.sq_sqrt hx0.le]
    linarith only [h1, h2]
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have h4 : 2 * Real.sqrt x * Real.log x ≤ 4 * x := by nlinarith only [hlog, hs, hsq]
  have hlog2 := Real.log_two_lt_d9
  have hlog4 : Real.log 4 ≤ 2 := by
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [e]
    linarith only [hlog2]
  nlinarith only [h, h4, hlog4, hx0]

/-! ## The weight of a zero -/

/-- The ordinate of a zero copy. -/
abbrev ord (q : XiZeroCopy) : ℝ := (q.1 : ℂ).im

/-- The genus weight of a zero copy. -/
def zeroWeight (q : XiZeroCopy) : ℝ := 1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)

theorem zeroWeight_nonneg (q : XiZeroCopy) : 0 ≤ zeroWeight q := by
  unfold zeroWeight
  positivity

theorem summable_zeroWeight : Summable zeroWeight :=
  summable_norm_inv_mul_one_sub.congr fun q => (norm_inv_mul_one_sub_eq q)

theorem sq_ord_le (q : XiZeroCopy) : ord q ^ 2 ≤ ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ := by
  have h1 : |ord q| ≤ ‖(q.1 : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : |ord q| ≤ ‖1 - (q.1 : ℂ)‖ := by
    have := Complex.abs_im_le_norm (1 - (q.1 : ℂ))
    simpa using this
  rw [← sq_abs, sq]
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

theorem zeroWeight_le_of_le_abs_ord {A : ℝ} (hA : 0 < A) {q : XiZeroCopy} (h : A ≤ |ord q|) :
    zeroWeight q ≤ 1 / A ^ 2 := by
  have hsq : A ^ 2 ≤ ord q ^ 2 := by
    rw [← sq_abs (ord q)]
    exact pow_le_pow_left₀ hA.le h 2
  exact one_div_le_one_div_of_le (by positivity) (hsq.trans (sq_ord_le q))

theorem zeroWeight_le_spectral (q : XiZeroCopy) : zeroWeight q ≤ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  have hγ : (41 : ℝ) / 2 < ord q ^ 2 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hδ := xi_divisor_support_centered_re_sq_lt_quarter q.1
  have hnorm : ‖xiSpectralPoint q‖ ^ 2 = ord q ^ 2 + ((q.1 : ℂ).re - 1 / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [xiSpectralPoint, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    norm_num
    ring
  have hle := sq_ord_le q
  have hpos : 0 < ‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ := by linarith only [hγ, hle]
  have hw : 0 < ‖xiSpectralPoint q‖ ^ 2 := by rw [hnorm]; nlinarith only [hγ, sq_nonneg ((q.1 : ℂ).re - 1 / 2)]
  unfold zeroWeight
  rw [mul_one_div, div_le_div_iff₀ hpos hw]
  rw [hnorm]
  linarith only [hγ, hδ, hle]

/-- The total genus weight is at most `4`. -/
theorem tsum_zeroWeight_le : ∑' q, zeroWeight q ≤ 4 := by
  have hs : Summable fun q : XiZeroCopy => 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    (xiSpectralPoint_inv_sq_summable).mul_left 2
  have h := summable_zeroWeight.tsum_le_tsum zeroWeight_le_spectral hs
  rw [tsum_mul_left] at h
  have h2 := xiSpectralPoint_inverse_square_mass_lt_two
  linarith only [h, h2]

/-! ## The zero sum -/

/-- `δ(x) = Σ_ρ x^{β−1}/(|ρ||1−ρ|)`. -/
def zeroDecay (x : ℝ) : ℝ := ∑' q : XiZeroCopy, x ^ ((q.1 : ℂ).re - 1) * zeroWeight q

theorem rpow_sub_one_le {x : ℝ} (hx : 1 ≤ x) (q : XiZeroCopy) : x ^ ((q.1 : ℂ).re - 1) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith only [xiZeroCopy_re_lt_one q])

theorem summable_zeroDecay {x : ℝ} (hx : 1 ≤ x) :
    Summable fun q : XiZeroCopy => x ^ ((q.1 : ℂ).re - 1) * zeroWeight q := by
  have hx0 : 0 < x := by linarith only [hx]
  refine summable_zeroWeight.of_nonneg_of_le (fun q => mul_nonneg (Real.rpow_nonneg hx0.le _) (zeroWeight_nonneg q))
    fun q => mul_le_of_le_one_left (zeroWeight_nonneg q) (rpow_sub_one_le hx q)

theorem zeroDecay_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ zeroDecay x :=
  tsum_nonneg fun q => mul_nonneg (Real.rpow_nonneg (by linarith only [hx]) _) (zeroWeight_nonneg q)

theorem zeroDecay_anti {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) : zeroDecay b ≤ zeroDecay a := by
  refine (summable_zeroDecay (ha.trans hab)).tsum_le_tsum (fun q => ?_) (summable_zeroDecay ha)
  refine mul_le_mul_of_nonneg_right ?_ (zeroWeight_nonneg q)
  exact rpow_anti (by linarith only [ha]) hab
    (by linarith only [xiZeroCopy_re_lt_one q])

theorem zeroDecay_le_four {x : ℝ} (hx : 1 ≤ x) : zeroDecay x ≤ 4 := by
  refine ((summable_zeroDecay hx).tsum_le_tsum (fun q => ?_) summable_zeroWeight).trans tsum_zeroWeight_le
  exact mul_le_of_le_one_left (zeroWeight_nonneg q) (rpow_sub_one_le hx q)

/-- Below height `T` the zero-free region bounds `x^{β−1}`. -/
theorem rpow_le_exp_of_abs_ord_le {x T : ℝ} (hx : 1 ≤ x) (hT : 4 ≤ T) (q : XiZeroCopy) (hq : |ord q| ≤ T) :
    x ^ ((q.1 : ℂ).re - 1) ≤ Real.exp (-(Real.log x / (58 * Real.log T))) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hLx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hγ : (1 : ℝ) < |ord q| := by
    have h := four_half_lt_abs_im_of_xiZeroCopy q
    norm_num at h
    exact lt_trans (by norm_num) h
  have hLγ : 0 < Real.log |ord q| := Real.log_pos hγ
  have hle : Real.log |ord q| ≤ Real.log T := Real.log_le_log (by linarith only [hγ]) hq
  have hLT : 0 < Real.log T := hLγ.trans_le hle
  have hzf := re_le_one_sub_of_zeta_zero (xiZeroCopy_re_pos q) (xiZeroCopy_re_lt_one q)
    (riemannZeta_eq_zero_of_xiZeroCopy q)
  have hfrac : 1 / (58 * Real.log T) ≤ 1 / 58 / Real.log |ord q| := by
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith only [hle])
  have hβ : (q.1 : ℂ).re - 1 ≤ -(1 / (58 * Real.log T)) := by linarith only [hzf, hfrac]
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h := mul_le_mul_of_nonneg_left hβ hLx
  have e : Real.log x * -(1 / (58 * Real.log T)) = -(Real.log x / (58 * Real.log T)) := by ring
  rw [e] at h
  exact h

/-! ## The local count on bands -/

/-- One unit fibre of the absolute ordinate has at most `80 log(360 A)` copies. -/
theorem card_fibre_le {A : ℝ} {n : ℕ} (hn : 4 ≤ n) (hn2 : (n : ℝ) ≤ 2 * A) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, ⌊|ord q|⌋₊ = n) : (F.card : ℝ) ≤ 80 * Real.log (360 * A) := by
  classical
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith only [hn4]
  have hfloor (q : XiZeroCopy) (hq : q ∈ F) : (n : ℝ) ≤ |ord q| ∧ |ord q| < n + 1 := by
    have h := hF q hq
    constructor
    · rw [← h]
      exact Nat.floor_le (abs_nonneg _)
    · rw [← h]
      exact Nat.lt_floor_add_one _
  have hlog : Real.log (180 * (n : ℝ)) ≤ Real.log (360 * A) :=
    Real.log_le_log (by positivity) (by linarith only [hn2])
  have hpos : ((F.filter fun q => 0 < ord q).card : ℝ) ≤ 40 * Real.log (360 * A) := by
    have h := card_le_of_ordinates_in_window (t := (n : ℝ))
      (by rw [abs_of_pos hn0]; exact hn4) (F.filter fun q => 0 < ord q) (by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hb := hfloor q hq.1
        rw [abs_of_pos hq.2] at hb
        rw [abs_le]
        constructor <;> linarith only [hb.1, hb.2])
    rw [abs_of_pos hn0] at h
    linarith only [h, hlog]
  have hneg : ((F.filter fun q => ¬ 0 < ord q).card : ℝ) ≤ 40 * Real.log (360 * A) := by
    have h := card_le_of_ordinates_in_window (t := -(n : ℝ))
      (by rw [abs_neg, abs_of_pos hn0]; exact hn4) (F.filter fun q => ¬ 0 < ord q) (by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hb := hfloor q hq.1
        rw [abs_of_nonpos (not_lt.1 hq.2)] at hb
        rw [abs_le]
        constructor <;> linarith only [hb.1, hb.2])
    rw [abs_neg, abs_of_pos hn0] at h
    linarith only [h, hlog]
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun q => 0 < ord q)
  have hcast : (F.card : ℝ) = ((F.filter fun q => 0 < ord q).card : ℝ) +
      ((F.filter fun q => ¬ 0 < ord q).card : ℝ) := by
    rw [← hsplit]
    push_cast
    rfl
  rw [hcast]
  linarith only [hpos, hneg]

/-- A band `(A, 2A]` of absolute ordinates has at most `(A+2) 80 log(360 A)` copies. -/
theorem card_band_le {A : ℝ} (hA : 5 ≤ A) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, A < |ord q| ∧ |ord q| ≤ 2 * A) :
    (F.card : ℝ) ≤ (A + 2) * (80 * Real.log (360 * A)) := by
  classical
  have hA0 : 0 < A := by linarith only [hA]
  have hL : 0 ≤ 80 * Real.log (360 * A) := by
    have := Real.log_nonneg (by linarith only [hA] : (1 : ℝ) ≤ 360 * A)
    linarith only [this]
  set f : XiZeroCopy → ℕ := fun q => ⌊|ord q|⌋₊ with hf
  set I := F.image f with hI
  have hIsub : I ⊆ Finset.Icc ⌊A⌋₊ ⌊2 * A⌋₊ := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
    exact Finset.mem_Icc.2 ⟨Nat.floor_le_floor (hF q hq).1.le, Nat.floor_le_floor (hF q hq).2⟩
  have hIcard : (I.card : ℝ) ≤ A + 2 := by
    have h1 := Finset.card_le_card hIsub
    rw [Nat.card_Icc] at h1
    have h2 : ((⌊2 * A⌋₊ + 1 - ⌊A⌋₊ : ℕ) : ℝ) ≤ (⌊2 * A⌋₊ : ℝ) + 1 - ⌊A⌋₊ := by
      have hle : ⌊A⌋₊ ≤ ⌊2 * A⌋₊ + 1 :=
        (Nat.floor_le_floor (by linarith only [hA0])).trans (Nat.le_succ _)
      rw [Nat.cast_sub hle]
      push_cast
      exact le_rfl
    have h3 : (⌊2 * A⌋₊ : ℝ) ≤ 2 * A := Nat.floor_le (by linarith only [hA0])
    have h4 := Nat.lt_floor_add_one A
    have h5 : (I.card : ℝ) ≤ ((⌊2 * A⌋₊ + 1 - ⌊A⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith only [h2, h3, h4, h5]
  have hcard : (F.card : ℝ) ≤ I.card * (80 * Real.log (360 * A)) := by
    rw [Finset.card_eq_sum_card_image f F, ← nsmul_eq_mul]
    push_cast
    refine Finset.sum_le_card_nsmul _ _ _ fun k hk => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hk
    have hb := hF q hq
    refine card_fibre_le ?_ ?_ _ fun q' hq' => (Finset.mem_filter.1 hq').2
    · exact Nat.le_floor (by push_cast; linarith only [hb.1, hA])
    · exact (Nat.floor_le (abs_nonneg _)).trans hb.2
  exact hcard.trans (mul_le_mul_of_nonneg_right hIcard hL)

theorem sum_range_succ_div_two_pow (K : ℕ) :
    ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ k = 4 - (2 * K + 4) / 2 ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h2 : ((2 : ℝ) ^ K) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-- **The tail of the genus weight.** -/
theorem sum_zeroWeight_tail_le {T : ℝ} (hT : 5 ≤ T) (B : Finset XiZeroCopy) (hB : ∀ q ∈ B, T < |ord q|) :
    ∑ q ∈ B, zeroWeight q ≤ 480 * (Real.log (360 * T) / T) := by
  classical
  have hT0 : 0 < T := by linarith only [hT]
  have hL : Real.log 2 ≤ Real.log (360 * T) := Real.log_le_log (by norm_num) (by linarith only [hT])
  have hL0 : 0 ≤ Real.log (360 * T) := Real.log_nonneg (by linarith only [hT])
  have hstep (K : ℕ) : ∑ q ∈ B.filter fun q => |ord q| ≤ 2 ^ K * T, zeroWeight q ≤
      120 * (Real.log (360 * T) / T) * ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ k := by
    induction K with
    | zero =>
      rw [Finset.filter_false_of_mem, Finset.sum_empty]
      · simp
      · intro q hq
        rw [pow_zero, one_mul]
        exact not_le.2 (hB q hq)
    | succ K ih =>
      obtain ⟨X, hX⟩ : ∃ X, X = (2 : ℝ) ^ K * T := ⟨_, rfl⟩
      have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      have hX0 : 0 < X := by rw [hX]; positivity
      have hX1 : T ≤ X := by
        rw [hX]
        exact le_mul_of_one_le_left hT0.le h2K
      have h2X : (2 : ℝ) ^ (K + 1) * T = 2 * X := by
        rw [hX, pow_succ]
        ring
      rw [h2X]
      rw [← hX] at ih
      set S := B.filter fun q => |ord q| ≤ 2 * X with hS
      set S₀ := B.filter fun q => |ord q| ≤ X with hS₀
      have hsub : S₀ ⊆ S := by
        intro q hq
        rw [hS₀, Finset.mem_filter] at hq
        rw [hS, Finset.mem_filter]
        exact ⟨hq.1, hq.2.trans (by linarith only [hX0])⟩
      rw [← Finset.sum_sdiff hsub]
      have hshell : ∑ q ∈ S \ S₀, zeroWeight q ≤ ((S \ S₀).card : ℝ) * (1 / X ^ 2) := by
        rw [← nsmul_eq_mul]
        refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
        rw [Finset.mem_sdiff, hS, hS₀, Finset.mem_filter, Finset.mem_filter] at hq
        have hgt : X ≤ |ord q| := by
          by_contra hc
          exact hq.2 ⟨hq.1.1, (not_le.1 hc).le⟩
        exact zeroWeight_le_of_le_abs_ord hX0 hgt
      have hcard : ((S \ S₀).card : ℝ) ≤ (X + 2) * (80 * Real.log (360 * X)) := by
        refine card_band_le (by linarith only [hT, hX1]) _ fun q hq => ?_
        rw [Finset.mem_sdiff, hS, hS₀, Finset.mem_filter, Finset.mem_filter] at hq
        refine ⟨?_, hq.1.2⟩
        by_contra hc
        exact hq.2 ⟨hq.1.1, not_lt.1 hc⟩
      have hlogX : Real.log (360 * X) ≤ ((K : ℝ) + 1) * Real.log (360 * T) := by
        have e : 360 * X = 2 ^ K * (360 * T) := by rw [hX]; ring
        rw [e, Real.log_mul (by positivity) (by positivity), Real.log_pow]
        nlinarith only [hL, (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
      have hterm : ((S \ S₀).card : ℝ) * (1 / X ^ 2) ≤
          120 * (Real.log (360 * T) / T) * (((K : ℝ) + 1) / 2 ^ K) := by
        have hbound : ((S \ S₀).card : ℝ) ≤ (7 / 5 * X) * (80 * (((K : ℝ) + 1) * Real.log (360 * T))) := by
          refine hcard.trans ?_
          have h1 : X + 2 ≤ 7 / 5 * X := by linarith only [hT, hX1]
          have h2 : 0 ≤ Real.log (360 * X) := Real.log_nonneg (by linarith only [hT, hX1])
          exact mul_le_mul h1 (by linarith only [hlogX]) (by positivity) (by positivity)
        have hq : 0 ≤ 1 / X ^ 2 := by positivity
        refine (mul_le_mul_of_nonneg_right hbound hq).trans ?_
        have e1 : (7 / 5 * X) * (80 * (((K : ℝ) + 1) * Real.log (360 * T))) * (1 / X ^ 2) =
            112 * (((K : ℝ) + 1) * Real.log (360 * T)) / X := by
          field_simp
          ring
        have e2 : 120 * (Real.log (360 * T) / T) * (((K : ℝ) + 1) / 2 ^ K) =
            120 * (((K : ℝ) + 1) * Real.log (360 * T)) / X := by
          rw [hX]
          field_simp
        rw [e1, e2]
        have hnn : 0 ≤ ((K : ℝ) + 1) * Real.log (360 * T) := by positivity
        exact div_le_div_of_nonneg_right (by linarith only [hnn]) hX0.le
      rw [Finset.sum_range_succ, mul_add]
      linarith only [hshell, hterm, ih]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ q ∈ B, |ord q| ≤ 2 ^ K * T := by
    obtain ⟨M, hM⟩ := (B.image fun q => |ord q|).exists_le
    obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (M / T) (by norm_num : (1 : ℝ) < 2)
    refine ⟨K, fun q hq => (hM _ (Finset.mem_image_of_mem _ hq)).trans ?_⟩
    rw [div_lt_iff₀ hT0] at hK
    exact hK.le
  have hall := hstep K
  rw [Finset.filter_true_of_mem hK] at hall
  refine hall.trans ?_
  have hsum : ∑ k ∈ Finset.range K, ((k : ℝ) + 1) / 2 ^ k ≤ 4 := by
    rw [sum_range_succ_div_two_pow]
    have : 0 ≤ (2 * (K : ℝ) + 4) / 2 ^ K := by positivity
    linarith only [this]
  have hpos : 0 ≤ Real.log (360 * T) / T := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left hsum hpos, hpos]

/-- **The zero sum at a split height.** -/
theorem zeroDecay_le_split {x T : ℝ} (hx : 1 ≤ x) (hT : 5 ≤ T) :
    zeroDecay x ≤ 4 * Real.exp (-(Real.log x / (58 * Real.log T))) + 480 * (Real.log (360 * T) / T) := by
  classical
  have hx0 : 0 < x := by linarith only [hx]
  refine (summable_zeroDecay hx).tsum_le_of_sum_le fun S => ?_
  rw [← Finset.sum_filter_add_sum_filter_not S (fun q => |ord q| ≤ T)]
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(Real.log x / (58 * Real.log T))) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  rw [← hE]
  have hlow : ∑ q ∈ S.filter (fun q => |ord q| ≤ T), x ^ ((q.1 : ℂ).re - 1) * zeroWeight q ≤ 4 * E := by
    calc
      _ ≤ ∑ q ∈ S.filter (fun q => |ord q| ≤ T), E * zeroWeight q := by
        refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_right ?_ (zeroWeight_nonneg q)
        rw [hE]
        exact rpow_le_exp_of_abs_ord_le hx (by linarith only [hT]) q (Finset.mem_filter.1 hq).2
      _ = E * ∑ q ∈ S.filter (fun q => |ord q| ≤ T), zeroWeight q := by rw [Finset.mul_sum]
      _ ≤ E * 4 := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        exact (summable_zeroWeight.sum_le_tsum _ fun q _ => zeroWeight_nonneg q).trans tsum_zeroWeight_le
      _ = 4 * E := by ring
  have hhigh : ∑ q ∈ S.filter (fun q => ¬ |ord q| ≤ T), x ^ ((q.1 : ℂ).re - 1) * zeroWeight q ≤
      480 * (Real.log (360 * T) / T) := by
    refine le_trans (Finset.sum_le_sum fun q _ => ?_) (sum_zeroWeight_tail_le hT _ fun q hq =>
      not_le.1 (Finset.mem_filter.1 hq).2)
    exact mul_le_of_le_one_left (zeroWeight_nonneg q) (rpow_sub_one_le hx q)
  linarith only [hlow, hhigh]

theorem log_three_sixty_le_six : Real.log 360 ≤ 6 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have e : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h2 : (2.7 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := pow_le_pow_left₀ (by norm_num) (by linarith only [h]) 6
  norm_num at h2 ⊢
  linarith only [h2]

/-- **The explicit zero sum.** `δ(x) ≤ 5300 exp(−√(log x)/10)` for every `x ≥ 1`. -/
theorem zeroDecay_le_exp {x : ℝ} (hx : 1 ≤ x) :
    zeroDecay x ≤ 5300 * Real.exp (-(Real.sqrt (Real.log x) / 10)) := by
  have hLx : 0 ≤ Real.log x := Real.log_nonneg hx
  obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt (Real.log x) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hy2 : y ^ 2 = Real.log x := by rw [hy]; exact Real.sq_sqrt hLx
  rw [← hy]
  have he2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]
    nlinarith only [h, Real.exp_pos 1]
  rcases lt_or_ge y 16 with hlt | hge
  · refine (zeroDecay_le_four hx).trans ?_
    have h1 : Real.exp (-2) ≤ Real.exp (-(y / 10)) := Real.exp_le_exp.2 (by linarith only [hlt])
    have h2 : (1 / 8 : ℝ) ≤ Real.exp (-2) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (Real.exp_pos 2) he2
    linarith only [h1, h2]
  · obtain ⟨T, hTdef⟩ : ∃ T, T = Real.exp (y / 8) := ⟨_, rfl⟩
    have hLT : Real.log T = y / 8 := by rw [hTdef, Real.log_exp]
    have hT5 : 5 ≤ T := by
      have h1 := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have h2 : Real.exp 2 ≤ T := by
        rw [hTdef]
        exact Real.exp_le_exp.2 (by linarith only [hge])
      rw [e] at h2
      nlinarith only [h1, h2]
    have hT0 : 0 < T := by linarith only [hT5]
    refine (zeroDecay_le_split hx hT5).trans ?_
    have hy16 : 0 < y := by linarith only [hge]
    have h1 : Real.exp (-(Real.log x / (58 * Real.log T))) ≤ Real.exp (-(y / 10)) := by
      apply Real.exp_le_exp.2
      rw [← hy2, hLT]
      have e : y ^ 2 / (58 * (y / 8)) = 4 / 29 * y := by
        field_simp
        ring
      rw [e]
      linarith only [hy16]
    have h2 : Real.log (360 * T) / T ≤ 11 * Real.exp (-(y / 10)) := by
      rw [Real.log_mul (by norm_num) hT0.ne', hLT, div_eq_mul_inv, hTdef, ← Real.exp_neg]
      have esplit : Real.exp (-(y / 8)) = Real.exp (-(y / 10)) * Real.exp (-(y / 40)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [esplit]
      have ht : (y / 40) * Real.exp (-(y / 40)) ≤ 1 := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
        have := Real.add_one_le_exp (y / 40)
        linarith only [this]
      have hle1 : Real.exp (-(y / 40)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith only [hy0])
      have hpos := Real.exp_pos (-(y / 40))
      have hmain : (Real.log 360 + y / 8) * Real.exp (-(y / 40)) ≤ 11 := by
        have := log_three_sixty_le_six
        nlinarith only [ht, hle1, hpos, this]
      have hE := Real.exp_pos (-(y / 10))
      nlinarith only [mul_le_mul_of_nonneg_right hmain hE.le]
    have hE := Real.exp_pos (-(y / 10))
    linarith only [h1, h2, hE]

/-! ## The window squeeze -/

/-- The zero sum of a window is bounded by `2 δ(a)/w`. -/
theorem abs_re_tsum_window_le {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    |(∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b).re| ≤ 2 * zeroDecay a / (1 / a - 1 / b) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hw : 0 < 1 / a - 1 / b := by
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt ha0 hab
  have hsn := summable_norm_lagWindowZeroTerm ha hab
  have hterm (q : XiZeroCopy) : ‖lagWindowZeroTerm (q.1 : ℂ) a b‖ ≤
      (2 / (1 / a - 1 / b)) * (a ^ ((q.1 : ℂ).re - 1) * zeroWeight q) := by
    refine (norm_lagWindowZeroTerm_le ha0 hab _).trans ?_
    have hb : b ^ ((q.1 : ℂ).re - 1) ≤ a ^ ((q.1 : ℂ).re - 1) :=
      rpow_anti ha0 hab.le (by linarith only [xiZeroCopy_re_lt_one q])
    have hq0 : 0 < ‖(q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_ne_zero q)
    have hq1 : 0 < ‖1 - (q.1 : ℂ)‖ := norm_pos_iff.mpr (xiZeroCopy_one_sub_ne_zero q)
    have hA := Real.rpow_nonneg ha0.le ((q.1 : ℂ).re - 1)
    unfold zeroWeight
    have e : (2 / (1 / a - 1 / b)) * (a ^ ((q.1 : ℂ).re - 1) * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖))) =
        (2 * a ^ ((q.1 : ℂ).re - 1)) / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖ * (1 / a - 1 / b)) := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith only [hb]) (by positivity)
  have hsum := ((summable_zeroDecay ha).mul_left (2 / (1 / a - 1 / b)))
  have htotal := hsn.tsum_le_tsum hterm hsum
  rw [tsum_mul_left] at htotal
  have h1 := Complex.abs_re_le_norm (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a b)
  have h2 := norm_tsum_le_tsum_norm hsn
  refine h1.trans (h2.trans (htotal.trans (le_of_eq ?_)))
  rw [zeroDecay]
  ring

/-- **The window inequality.** For `0 < η ≤ ½`, `|ψ(x) − x| ≤ ηx + 3x δ(x/2)/η + 2 + 1/η`. -/
theorem abs_psi_sub_le_of_window {x η : ℝ} (hx : 2 ≤ x) (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    |Chebyshev.psi x - x| ≤ η * x + 3 * x * zeroDecay (x / 2) / η + 2 + 1 / η := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x / 2 := by linarith only [hx]
  have hδ0 := zeroDecay_nonneg hx1
  have hlog2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hlog2π2 := log_two_mul_pi_lt_two
  rw [abs_le]
  constructor
  · -- The lower bound, on the window `[(1−η)x, x]`.
    obtain ⟨a, ha⟩ : ∃ a, a = (1 - η) * x := ⟨_, rfl⟩
    have ha2 : x / 2 ≤ a := by rw [ha]; nlinarith only [hη2, hx0]
    have ha1 : 1 < a ∨ a = 1 := by
      rcases eq_or_lt_of_le (hx1.trans ha2) with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    have ha1' : 1 ≤ a := hx1.trans ha2
    have ha0 : 0 < a := by linarith only [ha1']
    have hab : a < x := by rw [ha]; nlinarith only [hη, hx0]
    have hw : 0 < 1 / a - 1 / x := by
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt ha0 hab
    have hinv : 1 / (1 / a - 1 / x) ≤ x / η := by
      have e : 1 / a - 1 / x = η * x / (a * x) := by
        have : x - a = η * x := by rw [ha]; ring
        field_simp
        linarith only [this]
      rw [e, one_div_div, div_le_div_iff₀ (by positivity) hη]
      have : a ≤ x := hab.le
      nlinarith only [mul_le_mul_of_nonneg_right this (mul_nonneg hη.le hx0.le), hx0, hη]
    -- If `a = 1` the formula needs `1 < a`; use a slightly different case.
    have hzs := abs_re_tsum_window_le ha1' hab
    have hδa : zeroDecay a ≤ zeroDecay (x / 2) := zeroDecay_anti hx1 ha2
    have hδa0 := zeroDecay_nonneg ha1'
    have hre : -(2 * zeroDecay (x / 2) * (x / η)) ≤ (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) a x).re := by
      have h1 : 2 * zeroDecay a / (1 / a - 1 / x) ≤ 2 * zeroDecay (x / 2) * (x / η) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul (by linarith only [hδa]) hinv (by positivity) (by positivity)
      linarith only [(abs_le.1 hzs).1, h1]
    have hL : a ≤ Real.log (x / a) / (1 / a - 1 / x) := by
      rw [le_div_iff₀ hw]
      exact (log_div_le_mul_inv_sub ha0 hab.le).1
    have hsq : chebyshevLagWindow a x / (1 / a - 1 / x) ≤ Chebyshev.psi x := by
      rw [div_le_iff₀ hw]
      exact (chebyshevLagWindow_bounds ha0 hab.le).2
    have hE : 0 ≤ (trivialZeroSeriesReal a / a - trivialZeroSeriesReal x / x) / (1 / a - 1 / x) :=
      div_nonneg (sub_nonneg.mpr (trivialZeroSeriesReal_div_anti ha1' hab.le)) hw.le
    rcases ha1 with ha1s | ha1e
    · rw [chebyshevLagWindow_div_eq ha1s hab] at hsq
      have e : 2 * zeroDecay (x / 2) * (x / η) = 2 * x * zeroDecay (x / 2) / η := by ring
      have hpos : 0 ≤ x * zeroDecay (x / 2) / η := by positivity
      have hinvη : 0 ≤ 1 / η := by positivity
      have hax : a = x - η * x := by rw [ha]; ring
      rw [e] at hre
      have e3 : 3 * x * zeroDecay (x / 2) / η = 2 * x * zeroDecay (x / 2) / η + x * zeroDecay (x / 2) / η := by ring
      linarith only [hsq, hL, hre, hE, hlog2π2, hax, e3, hpos, hinvη]
    · -- `a = 1`, so `x ≤ 2`: the bound is trivial.
      have hx2 : x = 2 := by
        have : x / 2 ≤ 1 := by rw [← ha1e]; exact ha2
        linarith only [this, hx]
      have hψ := Chebyshev.psi_nonneg x
      have hinv1 : 0 ≤ 1 / η := by positivity
      have hp : 0 ≤ 3 * x * zeroDecay (x / 2) / η := by positivity
      have hηx : 0 ≤ η * x := by positivity
      linarith only [hψ, hx2, hinv1, hp, hηx]
  · -- The upper bound, on the window `[x, (1+η)x]`.
    obtain ⟨b, hb⟩ : ∃ b, b = (1 + η) * x := ⟨_, rfl⟩
    have hab : x < b := by rw [hb]; nlinarith only [hη, hx0]
    have hx1' : 1 < x := by linarith only [hx]
    have hb0 : 0 < b := by linarith only [hab, hx0]
    have hw : 0 < 1 / x - 1 / b := by
      rw [sub_pos]
      exact one_div_lt_one_div_of_lt hx0 hab
    have hinv : 1 / (1 / x - 1 / b) ≤ 3 / 2 * (x / η) := by
      have e : 1 / x - 1 / b = η * x / (x * b) := by
        have : b - x = η * x := by rw [hb]; ring
        field_simp
        linarith only [this]
      rw [e, one_div_div, div_le_iff₀ (by positivity)]
      have e2 : 3 / 2 * (x / η) * (η * x) = 3 / 2 * x * x := by
        field_simp
      rw [e2, hb]
      nlinarith only [mul_nonneg hx0.le hx0.le, hη2, mul_le_mul_of_nonneg_right hη2 (mul_nonneg hx0.le hx0.le)]
    have hzs := abs_re_tsum_window_le hx1'.le hab
    have hδa : zeroDecay x ≤ zeroDecay (x / 2) := zeroDecay_anti hx1 (by linarith only [hx0])
    have hδx0 := zeroDecay_nonneg hx1'.le
    have hre : (∑' q : XiZeroCopy, lagWindowZeroTerm (q.1 : ℂ) x b).re ≤
        3 * x * zeroDecay (x / 2) / η := by
      have h1 : 2 * zeroDecay x / (1 / x - 1 / b) ≤ 2 * zeroDecay (x / 2) * (3 / 2 * (x / η)) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul (by linarith only [hδa]) hinv (by positivity) (by positivity)
      have e : 2 * zeroDecay (x / 2) * (3 / 2 * (x / η)) = 3 * x * zeroDecay (x / 2) / η := by ring
      rw [e] at h1
      linarith only [(abs_le.1 hzs).2, h1]
    have hL : Real.log (b / x) / (1 / x - 1 / b) ≤ b := by
      rw [div_le_iff₀ hw]
      exact (log_div_le_mul_inv_sub hx0 hab.le).2
    have hsq : Chebyshev.psi x ≤ chebyshevLagWindow x b / (1 / x - 1 / b) := by
      rw [le_div_iff₀ hw]
      exact (chebyshevLagWindow_bounds hx0 hab.le).1
    rw [chebyshevLagWindow_div_eq hx1' hab] at hsq
    have hE : (trivialZeroSeriesReal x / x - trivialZeroSeriesReal b / b) / (1 / x - 1 / b) ≤ 1 / η := by
      have hEb := trivialZeroSeriesReal_nonneg (hx1'.le.trans hab.le)
      have hEx := trivialZeroSeriesReal_le_two_div_sq hx
      have hnum : trivialZeroSeriesReal x / x - trivialZeroSeriesReal b / b ≤ 2 / x ^ 2 / x := by
        have h1 : 0 ≤ trivialZeroSeriesReal b / b := div_nonneg hEb hb0.le
        have h2 : trivialZeroSeriesReal x / x ≤ 2 / x ^ 2 / x := div_le_div_of_nonneg_right hEx hx0.le
        linarith only [h1, h2]
      rw [div_eq_mul_one_div]
      refine (mul_le_mul hnum hinv (by positivity) (by positivity)).trans ?_
      have e : 2 / x ^ 2 / x * (3 / 2 * (x / η)) = 3 / (x ^ 2) * (1 / η) := by
        field_simp
      rw [e]
      have h3 : 3 / x ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith only [hx]
      exact mul_le_of_le_one_left (by positivity) h3
    have hbx : b = x + η * x := by rw [hb]; ring
    linarith only [hsq, hL, hre, hE, hlog2π, hbx]

/-! ## The explicit theorems -/

theorem exp_one_twentieth_le : Real.exp (1 / 20) ≤ 20 / 19 := by
  have h := Real.add_one_le_exp (-(1 / 20 : ℝ))
  have h2 : Real.exp (1 / 20) * Real.exp (-(1 / 20)) = 1 := by rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos (1 / 20 : ℝ)
  nlinarith only [h, h2, hp]

/-- **The prime number theorem with explicit constants.** -/
theorem abs_psi_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Chebyshev.psi x - x| ≤ 1000 * x * Real.exp (-(Real.sqrt (Real.log x) / 20)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x / 2 := by linarith only [hx]
  have hL2 : 0 ≤ Real.log (x / 2) := Real.log_nonneg hx1
  obtain ⟨y', hy'⟩ : ∃ y', y' = Real.sqrt (Real.log (x / 2)) := ⟨_, rfl⟩
  have hy'0 : 0 ≤ y' := by rw [hy']; exact Real.sqrt_nonneg _
  have hy'2 : y' ^ 2 = Real.log (x / 2) := by rw [hy']; exact Real.sq_sqrt hL2
  have hlogx : Real.log x = y' ^ 2 + Real.log 2 := by
    rw [hy'2, ← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    ring
  have hlog2 := Real.log_two_lt_d9
  have hlog2' := Real.log_two_gt_d9
  -- `√log x ≤ y' + 1`.
  have hyle : Real.sqrt (Real.log x) ≤ y' + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith only [hy'0], ?_⟩
    rw [hlogx]
    nlinarith only [hy'0, hlog2]
  -- `x = 2 exp(y'²)`.
  have hxe : x = 2 * Real.exp (y' ^ 2) := by
    rw [hy'2, Real.exp_log (by positivity)]
    ring
  obtain ⟨s, hs⟩ : ∃ s, s = 73 * Real.exp (-(y' / 20)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  have hd : zeroDecay (x / 2) ≤ s ^ 2 := by
    refine (zeroDecay_le_exp hx1).trans ?_
    rw [← hy', hs, mul_pow, ← Real.exp_nat_mul]
    have e : ((2 : ℕ) : ℝ) * -(y' / 20) = -(y' / 10) := by push_cast; ring
    rw [e]
    have hp := Real.exp_pos (-(y' / 10))
    nlinarith only [hp]
  have hmain : |Chebyshev.psi x - x| ≤ 12 * x * s := by
    rcases le_or_gt s (1 / 2) with hle | hgt
    · have hw := abs_psi_sub_le_of_window hx hs0 hle
      have h1 : 3 * x * zeroDecay (x / 2) / s ≤ 3 * x * s := by
        rw [div_le_iff₀ hs0]
        have : 3 * x * s * s = 3 * x * s ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hd (by positivity)
      -- `x s ≥ 2` and `x s² ≥ 1`.
      have hexp : Real.exp (-(1 / 1600)) ≤ Real.exp (y' ^ 2 - y' / 20) :=
        Real.exp_le_exp.2 (by nlinarith only [sq_nonneg (y' - 1 / 40)])
      have hexp2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 1600)) := by
        have := Real.add_one_le_exp (-(1 / 1600 : ℝ))
        linarith only [this]
      have hxs : x * s = 146 * Real.exp (y' ^ 2 - y' / 20) := by
        rw [hxe, hs, sub_eq_add_neg, Real.exp_add]
        ring
      have hxs2 : 73 ≤ x * s := by rw [hxs]; linarith only [hexp, hexp2]
      have hone : 1 / s ≤ x * s := by
        rw [div_le_iff₀ hs0]
        have : 1 ≤ x * s * s := by
          have hs1 : 73 * s ≤ x * s * s := mul_le_mul_of_nonneg_right hxs2 hs0.le
          -- `x s² ≥ 73 s` and `s` may be small; use `x s ≥ 73`, `s·x ≥ …` through the exponent.
          have hxd : x * s * s = 2 * 73 ^ 2 * Real.exp (y' ^ 2 - y' / 10) := by
            rw [hxe, hs]
            have e : y' ^ 2 - y' / 10 = y' ^ 2 + -(y' / 20) + -(y' / 20) := by ring
            rw [e, Real.exp_add, Real.exp_add]
            ring
          have he : Real.exp (-(1 / 400)) ≤ Real.exp (y' ^ 2 - y' / 10) :=
            Real.exp_le_exp.2 (by nlinarith only [sq_nonneg (y' - 1 / 20)])
          have he2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 400)) := by
            have := Real.add_one_le_exp (-(1 / 400 : ℝ))
            linarith only [this]
          rw [hxd]
          nlinarith only [he, he2]
        exact this
      have hsx : s * x = x * s := mul_comm _ _
      linarith only [hw, h1, hone, hxs2, hsx, mul_pos hx0 hs0]
    · -- For `s > ½` the Chebyshev bound suffices.
      have hψ0 := Chebyshev.psi_nonneg x
      have h6 : Chebyshev.psi x ≤ 6 * x := psi_le_six_mul (by linarith only [hx])
      have hsx : 6 * x ≤ 12 * x * s := by nlinarith only [hgt, hx0]
      rw [abs_le]
      constructor <;> linarith only [hψ0, h6, hsx, hx0]
  refine hmain.trans ?_
  have hexp : Real.exp (-(y' / 20)) ≤ Real.exp (1 / 20) * Real.exp (-(Real.sqrt (Real.log x) / 20)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith only [hyle]
  have hE := Real.exp_pos (-(Real.sqrt (Real.log x) / 20))
  have hc := exp_one_twentieth_le
  have hsbound : s ≤ 73 * (20 / 19) * Real.exp (-(Real.sqrt (Real.log x) / 20)) := by
    rw [hs, mul_assoc]
    refine mul_le_mul_of_nonneg_left (hexp.trans ?_) (by norm_num)
    exact mul_le_mul_of_nonneg_right hc hE.le
  have hx12 : 0 ≤ 12 * x := by positivity
  calc
    12 * x * s ≤ 12 * x * (73 * (20 / 19) * Real.exp (-(Real.sqrt (Real.log x) / 20))) :=
      mul_le_mul_of_nonneg_left hsbound hx12
    _ ≤ _ := by
      have hp : 0 ≤ x * Real.exp (-(Real.sqrt (Real.log x) / 20)) := by positivity
      nlinarith only [hp]

/-- **Mertens' theorem with explicit constants.** -/
theorem abs_mertens_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) - Real.log x +
        Real.eulerMascheroniConstant| ≤ 6400 * Real.exp (-(Real.sqrt (Real.log x) / 20)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) -
      Real.log x + Real.eulerMascheroniConstant := ⟨_, rfl⟩
  rw [← hM]
  have hf := lag_explicit_formula (X := x) (by linarith only [hx])
  rw [trivialZeroSeries_eq_real] at hf
  have hreal : ((x - Chebyshev.psi x : ℝ) : ℂ) +
        x * (((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) : ℝ) : ℂ) - Real.log x +
          Real.eulerMascheroniConstant) -
        Real.log (2 * Real.pi) + (trivialZeroSeriesReal x : ℂ) =
      ((x - Chebyshev.psi x + x * M - Real.log (2 * Real.pi) + trivialZeroSeriesReal x : ℝ) : ℂ) := by
    rw [hM]
    push_cast
    ring
  rw [hreal] at hf
  have hnorm : ‖∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ x * zeroDecay x := by
    have hterm (q : XiZeroCopy) : ‖(x : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ =
        x * (x ^ ((q.1 : ℂ).re - 1) * zeroWeight q) := by
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, norm_mul, zeroWeight,
        Real.rpow_sub_one hx0.ne']
      field_simp
    have hs : Summable fun q : XiZeroCopy => ‖(x : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
      simp_rw [hterm]
      exact (summable_zeroDecay hx1).mul_left x
    refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq ?_)
    simp_rw [hterm]
    rw [tsum_mul_left, zeroDecay]
  have hre := Complex.abs_re_le_norm (∑' q : XiZeroCopy, (x : ℂ) ^ (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))
  rw [hf, Complex.ofReal_re] at hre
  rw [hf] at hnorm
  have hZ : |x - Chebyshev.psi x + x * M - Real.log (2 * Real.pi) + trivialZeroSeriesReal x| ≤ x * zeroDecay x :=
    hre.trans hnorm
  have hψ := abs_psi_sub_le hx
  have hlog := log_two_mul_pi_lt_two
  have hlog0 : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hE0 := trivialZeroSeriesReal_nonneg hx1
  have hE1 := trivialZeroSeriesReal_le_one hx1
  have hδ := zeroDecay_le_exp hx1
  obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt (Real.log x) := ⟨_, rfl⟩
  rw [← hy] at hψ hδ ⊢
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hy2 : y ^ 2 = Real.log x := by rw [hy]; exact Real.sq_sqrt (Real.log_nonneg hx1)
  have hmul : x * |M| ≤ x * zeroDecay x + 1000 * x * Real.exp (-(y / 20)) + 3 := by
    rw [← abs_of_pos hx0, ← abs_mul, abs_of_pos hx0]
    have hψ' := abs_le.1 hψ
    have hZ' := abs_le.1 hZ
    rw [abs_le]
    constructor <;> linarith only [hψ'.1, hψ'.2, hZ'.1, hZ'.2, hlog, hlog0, hE0, hE1]
  have hxinv : 1 ≤ x * Real.exp (-(y / 20)) := by
    -- `x = exp(y²)` and `y² ≥ y/20` once `y ≥ 1/20`.
    have hxe : x = Real.exp (y ^ 2) := by rw [hy2, Real.exp_log hx0]
    have hlogx : Real.log 2 ≤ y ^ 2 := by
      rw [hy2]
      exact Real.log_le_log (by norm_num) hx
    have hl2 := Real.log_two_gt_d9
    have hy1 : 1 / 2 ≤ y := by
      by_contra hc
      nlinarith only [not_le.1 hc, hy0, hlogx, hl2]
    rw [hxe, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [hy1]
  have hee : Real.exp (-(y / 10)) ≤ Real.exp (-(y / 20)) := Real.exp_le_exp.2 (by linarith only [hy0])
  have hdiv : |M| ≤ zeroDecay x + 1000 * Real.exp (-(y / 20)) + 3 * Real.exp (-(y / 20)) := by
    have h3 : 3 ≤ x * (3 * Real.exp (-(y / 20))) := by nlinarith only [hxinv]
    have : x * |M| ≤ x * (zeroDecay x + 1000 * Real.exp (-(y / 20)) + 3 * Real.exp (-(y / 20))) := by
      have e : x * (zeroDecay x + 1000 * Real.exp (-(y / 20)) + 3 * Real.exp (-(y / 20))) =
          x * zeroDecay x + 1000 * x * Real.exp (-(y / 20)) + x * (3 * Real.exp (-(y / 20))) := by ring
      rw [e]
      linarith only [hmul, h3]
    exact le_of_mul_le_mul_left this hx0
  have hE := Real.exp_pos (-(y / 20))
  linarith only [hdiv, hδ, hee, hE]

end

end RHTower.ExplicitPNT

#print axioms RHTower.ExplicitPNT.zeroDecay_le_exp
#print axioms RHTower.ExplicitPNT.abs_psi_sub_le
#print axioms RHTower.ExplicitPNT.abs_mertens_sub_le
