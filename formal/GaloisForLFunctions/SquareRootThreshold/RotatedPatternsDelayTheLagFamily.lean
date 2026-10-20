import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold

/-!
# Rotated patterns delay the lag family

On a configuration with lag formula `W(f, f) = ℓ Σ_m k(mℓ) D(m)` the teeth of the one-parameter
family read the modes: `W(f_{nℓ}) = ℓ‖κ_w‖²(2D(0) − D(n) − D(−n))`
(`W_lag_nat_mul_of_lagFormula`). For a periodic off-line pattern with offsets `c_r` and depths
`d_r` this is `4ℓ‖κ_w‖² Σ_r (1 − cosh(d_r nℓ) cos(c_r nℓ))` (`patternSymbol_tooth`). A tooth sees
only the real part of the rotated mode `e^{ic_r nℓ}`, while the Toeplitz law sees its modulus. On
crystals the two agree (`lag_family_meets_crystal_at_threshold`). A rotation separates them.

**The quarter-turn pattern** (`quarterPattern`): one off-line line of depth `δ` per period
`2π/ℓ`, at offset `π/(2ℓ)`, so that `e^{icnℓ} = iⁿ` (`quarterPattern_delays_lag_family`).

* Every test of aperture `3ℓ/4` can see it. The `2 × 2` Toeplitz section has
  `|D(1)| = 2cosh(δℓ) > D(0) = 2`.
* The one-parameter family stays nonnegative for every lag `v < 4ℓ − 2w`. At the teeth `n = 1, 3`
  the mode is imaginary. At `n = 2` it is negative and adds to the positivity, since
  `κ_w ⋆ κ̃_w ≥ 0` (`weilTest_modScaledBump_zero`). In the gaps only the mean mode is read.
* The first tooth that sees the pattern is `n = 4`, where `iⁿ = 1` and
  `W = 4ℓ‖κ_w‖²(1 − cosh(4δℓ)) < 0`.

So the minimal receiver is threshold-exact on crystals but not aperture-optimal. A quarter turn
of the pattern makes it see the pattern at aperture `2ℓ` instead of `3ℓ/4`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### The unmodulated bump is real and nonnegative -/

theorem modScaledBump_zero_apply (w u : ℝ) :
    modScaledBump w 0 u = ((weilBump (u / (4 * w)) : ℝ) : ℂ) := by
  simp [modScaledBump, scaledBump, weilBumpC]

/-- `κ_w ⋆ κ̃_w` is real: `K(t) = ∫ ψ(s/4w) ψ((s − t)/4w) ds` with `ψ ≥ 0` the corpus bump. -/
theorem weilTest_modScaledBump_zero (w t : ℝ) :
    EF.weilTest (modScaledBump w 0) (modScaledBump w 0) t =
      ((∫ s, weilBump (s / (4 * w)) * weilBump ((s - t) / (4 * w)) : ℝ) : ℂ) := by
  rw [RHTower.weilTest_apply]
  refine (integral_congr_ae (Eventually.of_forall fun s => ?_)).trans integral_ofReal
  show _ = ((weilBump (s / (4 * w)) * weilBump ((s - t) / (4 * w)) : ℝ) : ℂ)
  simp only [modScaledBump_zero_apply, Complex.conj_ofReal]
  push_cast
  ring

theorem integral_weilBump_mul_nonneg (w t : ℝ) :
    0 ≤ ∫ s, weilBump (s / (4 * w)) * weilBump ((s - t) / (4 * w)) :=
  integral_nonneg fun _ => mul_nonneg weilBump.nonneg weilBump.nonneg

/-- `κ_w ⋆ κ̃_w` is even. -/
theorem weilTest_modScaledBump_zero_neg (w t : ℝ) :
    EF.weilTest (modScaledBump w 0) (modScaledBump w 0) (-t) =
      EF.weilTest (modScaledBump w 0) (modScaledBump w 0) t := by
  rw [weilTest_modScaledBump_zero, weilTest_modScaledBump_zero]
  congr 1
  have h := integral_add_right_eq_self (μ := volume)
    (fun s => weilBump (s / (4 * w)) * weilBump ((s - -t) / (4 * w))) (-t)
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show weilBump ((x + -t) / (4 * w)) * weilBump ((x + -t - -t) / (4 * w)) =
    weilBump (x / (4 * w)) * weilBump ((x - t) / (4 * w))
  rw [show x + -t - -t = x by ring, show x + -t = x - t by ring, mul_comm]

/-! ### Teeth of periodic patterns -/

/-- **The teeth of a pattern.** `2D(0) − D(n) − D(−n) = 4 Σ_r (1 − cosh(d_r nℓ) cos(c_r nℓ))`. -/
theorem patternSymbol_tooth (ℓ : ℝ) {P : ℕ} (c d : Fin P → ℝ) (n : ℤ) :
    2 * patternSymbol ℓ c d 0 - patternSymbol ℓ c d n - patternSymbol ℓ c d (-n) =
      ((4 * ∑ r, (1 - Real.cosh (d r * (n * ℓ)) * Real.cos (c r * (n * ℓ))) : ℝ) : ℂ) := by
  simp only [patternSymbol, Finset.mul_sum, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  have hcos : cexp (I * (c r : ℂ) * ((n : ℂ) * ℓ)) + cexp (I * (c r : ℂ) * ((-(n : ℂ)) * ℓ)) =
      2 * Complex.cos ((c r : ℂ) * ((n : ℂ) * ℓ)) := by
    rw [Complex.cos]; ring_nf
  have hch : Complex.cosh ((d r : ℂ) * ((-(n : ℂ)) * ℓ)) =
      Complex.cosh ((d r : ℂ) * ((n : ℂ) * ℓ)) := by
    rw [show (d r : ℂ) * ((-(n : ℂ)) * ℓ) = -((d r : ℂ) * ((n : ℂ) * ℓ)) by ring, Complex.cosh_neg]
  simp only [zero_mul, mul_zero, Complex.cosh_zero, Complex.exp_zero, hch]
  linear_combination (-2 * Complex.cosh ((d r : ℂ) * ((n : ℂ) * ℓ))) * hcos

/-- Toeplitz sections of size at most `1` are nonnegative when `Re D(0) ≥ 0`. -/
theorem re_toeplitzForm_nonneg_of_le_one (D : ℤ → ℂ) (hD : 0 ≤ (D 0).re) {N : ℕ} (hN : N ≤ 1)
    (c : Fin N → ℂ) : 0 ≤ (toeplitzForm D N c).re := by
  interval_cases N
  · simp [toeplitzForm]
  · simp only [toeplitzForm, Fin.sum_univ_one, sub_self, Complex.mul_conj]
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (Complex.normSq_nonneg _) hD

/-! ### The quarter-turn pattern -/

/-- One off-line line of depth `δ` per period `2π/ℓ`, at the quarter offset `π/(2ℓ)`. -/
def quarterPattern {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) : ZeroConfig :=
  patternConfig hℓ ![π / (2 * ℓ)] ![δ] (fun _ => by simpa using hδ) (fun _ => by simpa using hδ')

/-- The lag formula of the quarter-turn pattern. -/
theorem W_quarterPattern {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (quarterPattern hℓ hδ hδ').W f f = ((ℓ : ℝ) : ℂ) *
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * patternSymbol ℓ ![π / (2 * ℓ)] ![δ] m := by
  refine W_patternConfig hℓ _ _ _ _ (fun r r' j j' h => ⟨Subsingleton.elim _ _, ?_⟩) hf hfc
  rw [Subsingleton.elim r r'] at h
  have h1 : (j : ℝ) * (2 * π / ℓ) = j' * (2 * π / ℓ) := by linarith
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * π / ℓ) ≠ 0) h1

theorem quarterPattern_symbol_zero (ℓ δ : ℝ) :
    patternSymbol ℓ ![π / (2 * ℓ)] ![δ] 0 = 2 := by
  simp [patternSymbol]

/-- `2D(0) − D(n) − D(−n) = 4(1 − cosh(δnℓ) cos(nπ/2))` for the quarter-turn pattern. -/
theorem quarterPattern_tooth {ℓ : ℝ} (hℓ : 0 < ℓ) (δ : ℝ) (n : ℤ) :
    2 * patternSymbol ℓ ![π / (2 * ℓ)] ![δ] 0 - patternSymbol ℓ ![π / (2 * ℓ)] ![δ] n -
        patternSymbol ℓ ![π / (2 * ℓ)] ![δ] (-n) =
      ((4 * (1 - Real.cosh (δ * (n * ℓ)) * Real.cos (n * (π / 2)))) : ℝ) := by
  rw [patternSymbol_tooth]
  simp only [Fin.sum_univ_one, Matrix.cons_val_fin_one]
  rw [show π / (2 * ℓ) * (n * ℓ) = n * (π / 2) by field_simp]

/-- **The lag profile of the quarter-turn pattern.** For `ℓ > 4w`, `n ≥ 1` and `|t| < ℓ − 2w`,
`Re W(f_{nℓ+t}) = ℓ(4‖κ_w‖² − 4K(t) cosh(δnℓ) cos(nπ/2))` with `K(t) = ∫ ψψ(· − t) ≥ 0`. -/
theorem re_W_quarterPattern_lag {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : |t| < ℓ - 2 * w) :
    ((quarterPattern hℓ hδ hδ').W (twoBump (modScaledBump w 0) (n * ℓ + t) (-1))
        (twoBump (modScaledBump w 0) (n * ℓ + t) (-1))).re =
      ℓ * (4 * (∫ s, ‖modScaledBump w 0 s‖ ^ 2) -
        4 * (∫ s, weilBump (s / (4 * w)) * weilBump ((s - t) / (4 * w))) *
          (Real.cosh (δ * (n * ℓ)) * Real.cos (n * (π / 2)))) := by
  set D := patternSymbol ℓ ![π / (2 * ℓ)] ![δ] with hD
  have h := W_lag_nat_mul_add_of_lagFormula _ D (W_quarterPattern hℓ hδ hδ') hw hn ht
  have hT := quarterPattern_tooth hℓ δ n
  rw [← hD] at hT
  simp only [Int.cast_natCast] at hT
  have hD0 : D 0 = 2 := quarterPattern_symbol_zero ℓ δ
  set r := Real.cosh (δ * (n * ℓ)) * Real.cos (n * (π / 2)) with hr
  set K₀ := ∫ s, ‖modScaledBump w 0 s‖ ^ 2 with hK₀
  set Kt := ∫ s, weilBump (s / (4 * w)) * weilBump ((s - t) / (4 * w)) with hKt
  rw [weilTest_modScaledBump_zero_neg, weilTest_self_zero, weilTest_modScaledBump_zero] at h
  have hc : (quarterPattern hℓ hδ hδ').W (twoBump (modScaledBump w 0) (n * ℓ + t) (-1))
      (twoBump (modScaledBump w 0) (n * ℓ + t) (-1)) = ((ℓ * (4 * K₀ - 4 * Kt * r) : ℝ) : ℂ) := by
    rw [h]
    push_cast at hT ⊢
    linear_combination ((ℓ : ℂ) * (Kt : ℂ)) * hT + ((ℓ : ℂ) * (2 * (K₀ : ℂ) - 2 * (Kt : ℂ))) * hD0
  rw [hc, Complex.ofReal_re]

/-- `D(1) = 2cosh(δℓ) i` for the quarter-turn pattern. -/
theorem quarterPattern_symbol_one {ℓ : ℝ} (hℓ : 0 < ℓ) (δ : ℝ) :
    patternSymbol ℓ ![π / (2 * ℓ)] ![δ] 1 = 2 * (Real.cosh (δ * ℓ) : ℂ) * I := by
  have harg : I * ((π / (2 * ℓ) : ℝ) : ℂ) * (((1 : ℤ) : ℂ) * (ℓ : ℂ)) = (π : ℂ) / 2 * I := by
    rw [Int.cast_one, one_mul, mul_assoc, ← Complex.ofReal_mul,
      show π / (2 * ℓ) * ℓ = π / 2 by field_simp]
    push_cast; ring
  rw [patternSymbol, Fin.sum_univ_one]
  simp only [Matrix.cons_val_fin_one]
  rw [harg, Complex.exp_pi_div_two_mul_I, Int.cast_one, one_mul]
  push_cast; ring

/-- `D(−1) = −2cosh(δℓ) i` for the quarter-turn pattern. -/
theorem quarterPattern_symbol_neg_one {ℓ : ℝ} (hℓ : 0 < ℓ) (δ : ℝ) :
    patternSymbol ℓ ![π / (2 * ℓ)] ![δ] (-1) = -(2 * (Real.cosh (δ * ℓ) : ℂ) * I) := by
  have harg : I * ((π / (2 * ℓ) : ℝ) : ℂ) * ((((-1) : ℤ) : ℂ) * (ℓ : ℂ)) =
      -((π : ℂ) / 2 * I) := by
    rw [Int.cast_neg, Int.cast_one, neg_one_mul, mul_neg, mul_assoc, ← Complex.ofReal_mul,
      show π / (2 * ℓ) * ℓ = π / 2 by field_simp]
    push_cast; ring
  rw [patternSymbol, Fin.sum_univ_one]
  simp only [Matrix.cons_val_fin_one]
  rw [harg, Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I, Int.cast_neg,
    Int.cast_one, neg_one_mul, show δ * -ℓ = -(δ * ℓ) by ring, Real.cosh_neg]
  push_cast; ring

/-- The `2 × 2` Toeplitz form at `(1, i)`: `2D(0) + iD(1) − iD(−1)`. -/
theorem toeplitzForm_two_one_I (D : ℤ → ℂ) :
    toeplitzForm D 2 ![1, I] = 2 * D 0 + I * D 1 - I * D (-1) := by
  simp [toeplitzForm, Fin.sum_univ_two]
  ring

/-- **Rotated patterns delay the lag family.** Let `ℓ > 4w` and `0 < δ ≤ ½`. On the quarter-turn
pattern every test of aperture `3ℓ/4` can be negative, but the one-parameter family is
nonnegative at every lag `0 ≤ v < 4ℓ − 2w`, and first negative at the tooth `v = 4ℓ`. -/
theorem quarterPattern_delays_lag_family {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ) :
    (∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-(3 * ℓ / 4)) (3 * ℓ / 4) ∧
      ((quarterPattern hℓ hδ hδ').W f f).re < 0) ∧
    (∀ v : ℝ, 0 ≤ v → v < 4 * ℓ - 2 * w → 0 ≤ ((quarterPattern hℓ hδ hδ').W
      (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re) ∧
    ((quarterPattern hℓ hδ hδ').W (twoBump (modScaledBump w 0) (4 * ℓ) (-1))
      (twoBump (modScaledBump w 0) (4 * ℓ) (-1))).re < 0 := by
  set Z := quarterPattern hℓ hδ hδ' with hZ
  set D := patternSymbol ℓ ![π / (2 * ℓ)] ![δ] with hD
  have hW := W_quarterPattern hℓ hδ hδ'
  have hK₀ := integral_norm_sq_modScaledBump_pos hw
  have hD0 : D 0 = 2 := quarterPattern_symbol_zero ℓ δ
  refine ⟨?_, fun v hv0 hv => ?_, ?_⟩
  · -- the `2 × 2` Toeplitz section fails
    by_contra hno
    push Not at hno
    have hall := (weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW (a := 3 * ℓ / 4)
      (by positivity)).mp fun f hf hfs => hno f hf hfs
    have hceil : ⌈2 * (3 * ℓ / 4) / ℓ⌉₊ = 2 := by
      rw [show 2 * (3 * ℓ / 4) / ℓ = 3 / 2 by field_simp; ring, Nat.ceil_eq_iff (by norm_num)]
      norm_num
    rw [hceil] at hall
    have h1 := hall ![1, I]
    rw [toeplitzForm_two_one_I] at h1
    set C := Real.cosh (δ * ℓ) with hC
    have hc : 1 < C := Real.one_lt_cosh.mpr (by positivity)
    have hval : 2 * D 0 + I * D 1 - I * D (-1) = ((4 - 4 * C : ℝ) : ℂ) := by
      rw [hD0, hD, quarterPattern_symbol_one hℓ δ, quarterPattern_symbol_neg_one hℓ δ, ← hC]
      push_cast
      linear_combination (4 * (C : ℂ)) * Complex.I_mul_I
    rw [hval, Complex.ofReal_re] at h1
    linarith
  · -- the family is nonnegative before the fourth tooth
    rcases le_or_gt v (ℓ - 2 * w) with hvl | hvl
    · exact (weil_nonneg_iff_toeplitz_of_lagFormula Z hℓ D hW (a := v / 2 + w)
        (by positivity)).mpr (fun c => re_toeplitzForm_nonneg_of_le_one D
          (by rw [hD0]; norm_num) (Nat.ceil_le.mpr (by
            rw [div_le_iff₀ hℓ]; push_cast; linarith)) c) _
        (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
        (tsupport_twoBump_modScaledBump_subset hw hv0)
    · by_cases hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * ℓ|
      · rw [W_lag_eq_of_gap_of_lagFormula Z D hW hw hwℓ (by linarith) hgap, hD0,
          show (2 : ℂ) * (ℓ : ℂ) * ((∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) * 2 =
            ((4 * ℓ * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
        positivity
      · push Not at hgap
        obtain ⟨n, hn, hnv⟩ := hgap
        have hn3 : n ≤ 3 := by
          by_contra h4
          have : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
          obtain ⟨h, -⟩ := abs_le.mp hnv
          nlinarith [mul_le_mul_of_nonneg_right this hℓ.le]
        have ht : |v - n * ℓ| < ℓ - 2 * w := by linarith
        rw [show v = n * ℓ + (v - n * ℓ) by ring, re_W_quarterPattern_lag hℓ hδ hδ' hw hn ht]
        have hKt := integral_weilBump_mul_nonneg w (v - n * ℓ)
        have hch := Real.cosh_pos (δ * (n * ℓ))
        interval_cases n
        · simp only [Nat.cast_one, one_mul, Real.cos_pi_div_two, mul_zero, sub_zero]
          exact mul_nonneg hℓ.le (by linarith)
        · rw [show ((2 : ℕ) : ℝ) * (π / 2) = π by push_cast; ring, Real.cos_pi]
          exact mul_nonneg hℓ.le (by nlinarith [mul_nonneg hKt hch.le])
        · rw [show ((3 : ℕ) : ℝ) * (π / 2) = π / 2 + π by push_cast; ring, Real.cos_add_pi,
            Real.cos_pi_div_two, neg_zero, mul_zero, mul_zero, sub_zero]
          exact mul_nonneg hℓ.le (by linarith)
  · -- the fourth tooth sees it
    have h := W_lag_nat_mul_of_lagFormula Z D hW hw hwℓ (n := 4) (by norm_num)
    rw [quarterPattern_tooth hℓ δ ((4 : ℕ) : ℤ)] at h
    have hc4 : Real.cos ((((4 : ℕ) : ℤ) : ℝ) * (π / 2)) = 1 := by
      rw [show (((4 : ℕ) : ℤ) : ℝ) * (π / 2) = (1 : ℕ) * (2 * π) by push_cast; ring,
        Real.cos_nat_mul_two_pi]
    rw [hc4, mul_one, ← Complex.ofReal_mul, ← Complex.ofReal_mul] at h
    rw [show ((4 : ℕ) : ℝ) * ℓ = 4 * ℓ by norm_num] at h
    rw [h, Complex.ofReal_re]
    have hc : 1 < Real.cosh (δ * ((((4 : ℕ) : ℤ) : ℝ) * ℓ)) :=
      Real.one_lt_cosh.mpr (by push_cast; positivity)
    nlinarith [mul_pos hℓ hK₀]

end GaloisForLFunctions.SquareRootThreshold
