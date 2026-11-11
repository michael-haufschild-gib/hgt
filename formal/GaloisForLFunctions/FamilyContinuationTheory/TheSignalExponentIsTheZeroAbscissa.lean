import GaloisForLFunctions.FamilyContinuationTheory.TheSignalExponentIsThePositivityLevel
import GaloisForLFunctions.RHTower.InvZetaAbscissaSubpolynomial
import GaloisForLFunctions.RHTower.ZetaHalfPlaneDiscJensen
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The signal exponent is the zero abscissa

The signal of the zeta kernel `exp((s − c)²)/((s − 1) ζ(s))` reads the zero abscissa of `ζ`
exactly.

* **The line can be moved inside a strip of holomorphy and decay** (`signal_eq_of_decay`).
* **A zero-free half-plane bounds the signal** (`exists_signal_zetaKernel_le_of_zeroFree`). If `ζ`
  has no zero in `Re s > Θ`, then for every `b ∈ (Θ, 1]` the signal is `O(Z^b)` on all of
  `Z > 0`. On the strip `b ≤ Re s ≤ 2` the function `(s − 1) ζ(s)` has no zero and is at least
  `κ/(2 + |t|)` in modulus, so the kernel decays like `C/(1 + t²)`; the line `Re s = 2` moves to
  `Re s = b`.
* **The exponent** (`zetaZeroAbscissa_le_iff_forall_signal_le`). For `b ∈ [½, 1)`, the zero
  abscissa is at most `b` if and only if the signal is `O(Z^{b'})` for every `b' > b`.
-/

noncomputable section

open Complex MeasureTheory Set

namespace GaloisForLFunctions.FamilyContinuationTheory

open _root_.RHTower

/-- **Moving the line.** A function holomorphic on the strip `b ≤ Re s ≤ B` with the decay
`C/(1 + t²)` there has the same signal on both boundary lines. -/
theorem signal_eq_of_decay {G : ℂ → ℂ} {b B C : ℝ} (hbB : b ≤ B)
    (hdiff : ∀ s : ℂ, b ≤ s.re → s.re ≤ B → DifferentiableAt ℂ G s)
    (hdecay : ∀ s : ℂ, b ≤ s.re → s.re ≤ B → ‖G s‖ ≤ C / (1 + s.im ^ 2)) {Z : ℝ}
    (hZ : 0 < Z) : signal G B Z = signal G b Z := by
  have hmem : ∀ s : ℂ, s.re ∈ uIcc (-B) (-b) → b ≤ (-s).re ∧ (-s).re ≤ B := by
    intro s hs
    rw [Set.uIcc_of_le (by linarith : -B ≤ -b)] at hs
    rw [neg_re]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  unfold signal
  rw [mellinInv, mellinInv]
  congr 1
  refine HTGeometry.integral_vertical_line_shift_of_decay
    (Φ := fun w : ℂ => (Z : ℂ) ^ (-w) • G (-w)) (C := max (Z ^ b) (Z ^ B) * C) ?_ ?_
  · intro s hs
    have hneg : DifferentiableAt ℂ (fun w : ℂ => -w) s := differentiableAt_id.neg
    exact (hneg.const_cpow (Or.inl (ofReal_ne_zero.mpr hZ.ne'))).smul
      ((hdiff (-s) (hmem s hs).1 (hmem s hs).2).comp s hneg)
  · intro s hs
    obtain ⟨hlo, hhi⟩ := hmem s hs
    have hGs := hdecay (-s) hlo hhi
    rw [neg_im, neg_sq] at hGs
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hZ, mul_div_assoc]
    refine mul_le_mul ?_ hGs (norm_nonneg _)
      (le_max_of_le_left (Real.rpow_nonneg hZ.le _))
    rcases le_total 1 Z with h | h
    · exact le_max_of_le_right (Real.rpow_le_rpow_of_exponent_le h hhi)
    · exact le_max_of_le_left (Real.rpow_le_rpow_of_exponent_ge hZ h hlo)

/-- Right of a zero-free frontier `(s − 1) ζ(s)` has no zero. -/
theorem zetaEntire_ne_zero_of_zeroFree {Θ : ℝ}
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {s : ℂ} (hs : Θ < s.re) :
    zetaEntire s ≠ 0 := by
  rcases eq_or_ne s 1 with h | h
  · rw [h, zetaEntire_eval_one]
    exact one_ne_zero
  · rw [zetaEntire_eq h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (hzf s hs)

/-- **A lower bound on strips.** Right of a zero-free frontier, `|(s − 1) ζ(s)| ≥ κ/(2 + |t|)` on
`Θ + δ ≤ Re s ≤ 2`: a minimum on the rectangle `|t| ≤ 6`, and above it the lower bound for `ζ`
with `|s − 1| ≥ 1`. -/
theorem exists_le_norm_zetaEntire_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, Θ + δ ≤ s.re → s.re ≤ 2 →
      κ / (2 + |s.im|) ≤ ‖zetaEntire s‖ := by
  obtain ⟨κ₁, hκ₁, hbig⟩ :=
    exists_zeta_lower_bound_subpolynomial_of_zeroFree hΘ hΘ1 hzf hδ hδ1 (ε := 1) one_pos
  let K₀ : Set ℂ := Set.Icc (Θ + δ) 2 ×ℂ Set.Icc (-6 : ℝ) 6
  have hKc : IsCompact K₀ := isCompact_Icc.reProdIm isCompact_Icc
  have hKne : K₀.Nonempty := by
    refine ⟨(2 : ℂ), Complex.mem_reProdIm.mpr ⟨?_, ?_⟩⟩
    · rw [Complex.re_ofNat]
      exact ⟨by linarith, le_rfl⟩
    · rw [Complex.im_ofNat]
      constructor <;> norm_num
  obtain ⟨s₀, hs₀, hmin⟩ := hKc.exists_isMinOn hKne
    differentiable_zetaEntire.continuous.norm.continuousOn
  have hs₀re : Θ < s₀.re := by linarith [(Complex.mem_reProdIm.mp hs₀).1.1]
  have hm : 0 < ‖zetaEntire s₀‖ := norm_pos_iff.mpr (zetaEntire_ne_zero_of_zeroFree hzf hs₀re)
  refine ⟨min κ₁ ‖zetaEntire s₀‖, lt_min hκ₁ hm, fun s hlo hhi => ?_⟩
  have hden : (2 : ℝ) ≤ 2 + |s.im| := by linarith [abs_nonneg s.im]
  have hden0 : (0 : ℝ) < 2 + |s.im| := by linarith
  have hκ0 : 0 ≤ min κ₁ ‖zetaEntire s₀‖ := (lt_min hκ₁ hm).le
  rcases le_total |s.im| 6 with ht | ht
  · have hsK : s ∈ K₀ := Complex.mem_reProdIm.mpr ⟨⟨hlo, hhi⟩, abs_le.mp ht⟩
    have h1 : ‖zetaEntire s₀‖ ≤ ‖zetaEntire s‖ := isMinOn_iff.mp hmin s hsK
    calc min κ₁ ‖zetaEntire s₀‖ / (2 + |s.im|) ≤ min κ₁ ‖zetaEntire s₀‖ :=
          div_le_self hκ0 (by linarith)
      _ ≤ ‖zetaEntire s₀‖ := min_le_right _ _
      _ ≤ ‖zetaEntire s‖ := h1
  · have hs1 : s ≠ 1 := by
      intro h
      rw [h, Complex.one_im, abs_zero] at ht
      norm_num at ht
    have hζ := hbig s hlo ht
    rw [Real.rpow_neg_one] at hζ
    have hnorm : (1 : ℝ) ≤ ‖s - 1‖ := by
      have him : |s.im| ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        rwa [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    rw [zetaEntire_eq hs1, norm_mul]
    calc min κ₁ ‖zetaEntire s₀‖ / (2 + |s.im|) ≤ κ₁ / (2 + |s.im|) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hden0.le
      _ = κ₁ * (2 + |s.im|)⁻¹ := div_eq_mul_inv _ _
      _ ≤ ‖riemannZeta s‖ := hζ
      _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := le_mul_of_one_le_left (norm_nonneg _) hnorm

/-- The Gaussian absorbs a linear factor: `e^{−t²} (2 + |t|) ≤ 12/(1 + t²)`. -/
theorem exp_neg_sq_mul_le (t : ℝ) : Real.exp (-(t ^ 2)) * (2 + |t|) ≤ 12 / (1 + t ^ 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hE : 0 < Real.exp (t ^ 2) := Real.exp_pos _
  have hA : 2 + |t| ≤ 3 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (|t| - 1 / 2), sq_abs t, abs_nonneg t]
  have hB : (1 + t ^ 2) ^ 2 ≤ 4 * Real.exp (t ^ 2) := by
    have h1 : t ^ 2 / 2 + 1 ≤ Real.exp (t ^ 2 / 2) := Real.add_one_le_exp _
    have h2 : Real.exp (t ^ 2) = Real.exp (t ^ 2 / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h3 : (0 : ℝ) ≤ t ^ 2 / 2 + 1 := by positivity
    have h4 : (t ^ 2 / 2 + 1) ^ 2 ≤ Real.exp (t ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h3 h1 2
    rw [h2]
    nlinarith [h4, sq_nonneg t]
  have hX : (2 + |t|) * (1 + t ^ 2) ≤ 12 * Real.exp (t ^ 2) := by
    calc (2 + |t|) * (1 + t ^ 2) ≤ 3 * (1 + t ^ 2) * (1 + t ^ 2) :=
          mul_le_mul_of_nonneg_right hA hpos.le
      _ = 3 * (1 + t ^ 2) ^ 2 := by ring
      _ ≤ 3 * (4 * Real.exp (t ^ 2)) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 12 * Real.exp (t ^ 2) := by ring
  rw [le_div_iff₀ hpos]
  calc Real.exp (-(t ^ 2)) * (2 + |t|) * (1 + t ^ 2)
      = (Real.exp (t ^ 2))⁻¹ * ((2 + |t|) * (1 + t ^ 2)) := by
        rw [Real.exp_neg]
        ring
    _ ≤ (Real.exp (t ^ 2))⁻¹ * (12 * Real.exp (t ^ 2)) :=
        mul_le_mul_of_nonneg_left hX (inv_nonneg.mpr hE.le)
    _ = 12 := by
        field_simp

/-- **Decay of the zeta kernel right of a zero-free frontier.** -/
theorem exists_norm_zetaKernel_le_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (c : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < 1) :
    ∃ C : ℝ, ∀ s : ℂ, Θ + δ ≤ s.re → s.re ≤ 2 → ‖zetaKernel c s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨κ, hκ, hlow⟩ := exists_le_norm_zetaEntire_of_zeroFree hΘ hΘ1 hzf hδ hδ1
  refine ⟨12 * Real.exp ((2 + |c|) ^ 2) / κ, fun s hlo hhi => ?_⟩
  have hden : (0 : ℝ) < 2 + |s.im| := by linarith [abs_nonneg s.im]
  have hz := hlow s hlo hhi
  have hzpos : 0 < ‖zetaEntire s‖ := lt_of_lt_of_le (div_pos hκ hden) hz
  have hsq : (s.re - c) ^ 2 ≤ (2 + |c|) ^ 2 := by
    have habs : |s.re - c| ≤ 2 + |c| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le c, le_abs_self c]
    calc (s.re - c) ^ 2 = |s.re - c| ^ 2 := (sq_abs _).symm
      _ ≤ (2 + |c|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hnum : ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((2 + |c|) ^ 2) * Real.exp (-(s.im ^ 2)) := by
    rw [norm_cexp_sub_sq, sub_eq_add_neg, Real.exp_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsq) (Real.exp_pos _).le
  have hG := exp_neg_sq_mul_le s.im
  have hpos : (0 : ℝ) < 1 + s.im ^ 2 := by positivity
  unfold zetaKernel
  rw [norm_div, div_le_iff₀ hzpos]
  calc ‖cexp ((s - c) ^ 2)‖ ≤ Real.exp ((2 + |c|) ^ 2) * Real.exp (-(s.im ^ 2)) := hnum
    _ = Real.exp ((2 + |c|) ^ 2) * (Real.exp (-(s.im ^ 2)) * (2 + |s.im|)) / κ
          * (κ / (2 + |s.im|)) := by
        field_simp
    _ ≤ Real.exp ((2 + |c|) ^ 2) * (12 / (1 + s.im ^ 2)) / κ * (κ / (2 + |s.im|)) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le) hκ.le)
          (div_pos hκ hden).le
    _ = 12 * Real.exp ((2 + |c|) ^ 2) / κ / (1 + s.im ^ 2) * (κ / (2 + |s.im|)) := by ring
    _ ≤ 12 * Real.exp ((2 + |c|) ^ 2) / κ / (1 + s.im ^ 2) * ‖zetaEntire s‖ :=
        mul_le_mul_of_nonneg_left hz (by positivity)

/-- **A zero-free half-plane bounds the signal.** If `ζ` has no zero in `Re s > Θ`, the signal of
the zeta kernel is `O(Z^b)` for every `b ∈ (Θ, 1]`. -/
theorem exists_signal_zetaKernel_le_of_zeroFree {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) (c : ℝ) {b : ℝ} (hb : Θ < b)
    (hb1 : b ≤ 1) :
    ∃ K : ℝ, ∀ Z : ℝ, 0 < Z → ‖signal (zetaKernel c) 2 Z‖ ≤ K * Z ^ b := by
  obtain ⟨C, hC⟩ := exists_norm_zetaKernel_le_of_zeroFree hΘ hΘ1 hzf c
    (by linarith : 0 < b - Θ) (by linarith : b - Θ < 1)
  have hC' : ∀ s : ℂ, b ≤ s.re → s.re ≤ 2 → ‖zetaKernel c s‖ ≤ C / (1 + s.im ^ 2) :=
    fun s h1 h2 => hC s (by linarith) h2
  refine ⟨C / 2, fun Z hZ => ?_⟩
  rw [signal_eq_of_decay (by linarith : b ≤ 2)
    (fun s h1 _ => by
      unfold zetaKernel
      exact (by fun_prop : DifferentiableAt ℂ (fun s : ℂ => cexp ((s - c) ^ 2)) s).div
        (differentiable_zetaEntire s) (zetaEntire_ne_zero_of_zeroFree hzf (by linarith)))
    hC' hZ]
  exact norm_signal_le (fun s hs => hC' s hs.ge (by rw [hs]; linarith)) hZ

/-- **The signal exponent is the zero abscissa.** For `b ∈ [½, 1)`: every zero of `ζ` has real
part at most `b` if and only if the signal of the zeta kernel is `O(Z^{b'})` for every
`b' > b`. -/
theorem zetaZeroAbscissa_le_iff_forall_signal_le {b : ℝ} (hb : (1 : ℝ) / 2 ≤ b) (hb1 : b < 1) :
    zetaZeroAbscissa ≤ b ↔
      ∀ b' : ℝ, b < b' → b' ≤ 1 →
        ∃ K : ℝ, ∀ Z : ℝ, 0 < Z → ‖signal (zetaKernel 0) 2 Z‖ ≤ K * Z ^ b' := by
  constructor
  · intro h b' hb' hb'1
    exact exists_signal_zetaKernel_le_of_zeroFree hb hb1.le
      (fun z hz => riemannZeta_ne_zero_of_zetaZeroAbscissa_lt (lt_of_le_of_lt h hz)) 0 hb' hb'1
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hA1 := zetaZeroAbscissa_le_one
    obtain ⟨K, hK⟩ := h ((b + zetaZeroAbscissa) / 2) (by linarith) (by linarith)
    obtain ⟨ρ, hzero, hρ⟩ :=
      exists_zetaZero_lt_re (by linarith : (b + zetaZeroAbscissa) / 2 < zetaZeroAbscissa)
    have hρ1 : ρ ≠ 1 := fun h1 => riemannZeta_one_ne_zero (h1 ▸ hzero)
    exact riemannZeta_ne_zero_of_signal_le (c := 0) (Z₀ := 1)
      (by linarith : (b + zetaZeroAbscissa) / 2 < 1) one_pos
      (fun Z hZ => hK Z (by linarith)) ρ hρ hρ1 hzero

end GaloisForLFunctions.FamilyContinuationTheory
