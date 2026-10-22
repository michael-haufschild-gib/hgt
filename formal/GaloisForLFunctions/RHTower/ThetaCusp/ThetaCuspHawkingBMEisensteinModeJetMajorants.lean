import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualMaassModeJet
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMBesselOrderExteriorEnvelope
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinWhittakerArithmeticEnvelope

/-!
# All-heights majorants of the Whittaker mode jets

The signed Whittaker modes of the completed Eisenstein Fourier model and their first and second
jets are finite combinations of `√Y · K_{cY}(ν + k)`, `|k| ≤ 2`, with polynomial factors.  On a
height window `Y ∈ [Y₀/2, 2Y₀]` and for orders `‖ν‖ ≤ R`, the Gaussian Schläfli bound gives a
single exponentially decaying majorant `B_N = e^{(R+2)²/(2πY₀)} √(2/Y₀) e^{−π(N+1)Y₀}` for every
Bessel factor, hence explicit summable majorants `C · (N+1)^j · B_N` for the modes and all their
jets, uniformly on the window.  These majorants have no height restriction and are the input of
termwise differentiation of the Fourier model at every height.
-/

open Real Set

namespace RHTower

noncomputable section

/-- The Bessel majorant on the window `[Y₀/2, 2Y₀]` for the `N`-th mode. -/
def besselModeMajorant (Y₀ R : ℝ) (N : ℕ) : ℝ :=
  Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) * Real.sqrt (2 / Y₀) *
    Real.exp (-(Real.pi * ((N : ℝ) + 1) * Y₀))

theorem besselModeMajorant_nonneg (Y₀ R : ℝ) (N : ℕ) : 0 ≤ besselModeMajorant Y₀ R N := by
  unfold besselModeMajorant; positivity

/-- **Window Bessel bound.**  For `Y ∈ [Y₀/2, 2Y₀]` and `‖ν‖ ≤ R`,
`‖K_{2π(N+1)Y}(ν)‖ ≤ B_N(Y₀, R)`. -/
theorem norm_modifiedBesselKOrder_window_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) {Y : ℝ}
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) {R : ℝ} {ν : ℂ} (hν : ‖ν‖ ≤ R) (N : ℕ) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) ν‖ ≤ besselModeMajorant Y₀ R N := by
  have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hYpos : 0 < Y := lt_of_lt_of_le (by linarith) hY.1
  set s : ℝ := (d4BMPositiveFourierScale N : ℝ) * Y with hsdef
  have hs : 0 < s := by rw [hsdef, hc]; positivity
  have hpiN : 0 < Real.pi * ((N : ℝ) + 1) := by positivity
  have hs_lower : Real.pi * ((N : ℝ) + 1) * Y₀ ≤ s := by
    rw [hsdef, hc]
    have h2 : Y₀ ≤ 2 * Y := by linarith [hY.1]
    calc Real.pi * ((N : ℝ) + 1) * Y₀ ≤ Real.pi * ((N : ℝ) + 1) * (2 * Y) :=
          mul_le_mul_of_nonneg_left h2 hpiN.le
      _ = 2 * Real.pi * ((N : ℝ) + 1) * Y := by ring
  have hs_lower' : Real.pi * Y₀ ≤ s := by
    have : Real.pi * Y₀ ≤ Real.pi * ((N : ℝ) + 1) * Y₀ := by
      have := mul_le_mul_of_nonneg_left hN1 Real.pi_pos.le
      calc Real.pi * Y₀ = Real.pi * 1 * Y₀ := by ring
        _ ≤ Real.pi * ((N : ℝ) + 1) * Y₀ := mul_le_mul_of_nonneg_right this hY₀.le
    linarith
  have h := d4BM_norm_modifiedBesselKOrder_le ⟨s, hs⟩ ν
  simp only at h
  refine h.trans ?_
  unfold besselModeMajorant
  have hR0 : 0 ≤ R := (norm_nonneg ν).trans hν
  have h1 : Real.exp (-s) ≤ Real.exp (-(Real.pi * ((N : ℝ) + 1) * Y₀)) := by
    rw [Real.exp_le_exp]; linarith
  have h2 : Real.exp (‖ν‖ ^ 2 / (2 * s)) ≤ Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) := by
    rw [Real.exp_le_exp]
    have hν2 : ‖ν‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg ν]
    calc ‖ν‖ ^ 2 / (2 * s) ≤ R ^ 2 / (2 * s) := div_le_div_of_nonneg_right hν2 (by positivity)
      _ ≤ R ^ 2 / (2 * Real.pi * Y₀) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          linarith
  have h3 : Real.sqrt (2 * Real.pi / s) ≤ Real.sqrt (2 / Y₀) := by
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ hs hY₀]
    nlinarith [Real.pi_pos]
  calc Real.exp (-s) * Real.exp (‖ν‖ ^ 2 / (2 * s)) * Real.sqrt (2 * Real.pi / s) ≤
        Real.exp (-(Real.pi * ((N : ℝ) + 1) * Y₀)) * Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) *
          Real.sqrt (2 / Y₀) := by
        exact mul_le_mul (mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le) h3
          (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) * Real.sqrt (2 / Y₀) *
          Real.exp (-(Real.pi * ((N : ℝ) + 1) * Y₀)) := by ring

/-- Shifted orders `ν + k`, `|k| ≤ 2`, satisfy `‖ν + k‖ ≤ R + 2`. -/
theorem norm_shift_le {ν : ℂ} {R : ℝ} (hν : ‖ν‖ ≤ R) {k : ℤ} (hk : |k| ≤ 2) :
    ‖ν + (k : ℂ)‖ ≤ R + 2 := by
  calc ‖ν + (k : ℂ)‖ ≤ ‖ν‖ + ‖(k : ℂ)‖ := norm_add_le _ _
    _ ≤ R + 2 := by
        have : ‖(k : ℂ)‖ = |(k : ℝ)| := by rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        rw [this]
        have hk' : |(k : ℝ)| ≤ 2 := by exact_mod_cast hk
        linarith

/-- The Bessel factor at any shifted order `ν + k`, `|k| ≤ 2`, on the window. -/
theorem norm_modifiedBesselKOrder_window_shift_le {Y₀ : ℝ} (hY₀ : 0 < Y₀) {Y : ℝ}
    (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀)) {R : ℝ} {ν : ℂ} (hν : ‖ν‖ ≤ R) (N : ℕ) {k : ℤ}
    (hk : |k| ≤ 2) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + k)‖ ≤ besselModeMajorant Y₀ (R + 2) N :=
  norm_modifiedBesselKOrder_window_le hY₀ hY (norm_shift_le hν hk) N

/-! ## Window factors -/

section Window

variable {Y₀ : ℝ} (hY₀ : 0 < Y₀) {Y : ℝ} (hY : Y ∈ Icc (Y₀ / 2) (2 * Y₀))
include hY₀ hY

theorem window_pos : 0 < Y := lt_of_lt_of_le (by linarith) hY.1

omit hY₀ in
theorem window_sqrt_le : Real.sqrt Y ≤ Real.sqrt (2 * Y₀) := Real.sqrt_le_sqrt hY.2

theorem window_inv_sqrt_le : 1 / (2 * Real.sqrt Y) ≤ 1 / (2 * Real.sqrt (Y₀ / 2)) := by
  have h1 : Real.sqrt (Y₀ / 2) ≤ Real.sqrt Y := Real.sqrt_le_sqrt hY.1
  have h2 : 0 < Real.sqrt (Y₀ / 2) := Real.sqrt_pos.mpr (by linarith)
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  linarith

omit hY₀ in
theorem window_scale_mul_le (N : ℕ) :
    (d4BMPositiveFourierScale N : ℝ) * Y ≤ 4 * Real.pi * Y₀ * ((N : ℝ) + 1) := by
  have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
  rw [hc]
  have := hY.2
  have hpos : 0 ≤ 2 * Real.pi * ((N : ℝ) + 1) := by positivity
  calc 2 * Real.pi * ((N : ℝ) + 1) * Y ≤ 2 * Real.pi * ((N : ℝ) + 1) * (2 * Y₀) :=
        mul_le_mul_of_nonneg_left this hpos
    _ = 4 * Real.pi * Y₀ * ((N : ℝ) + 1) := by ring

omit hY₀ hY in
theorem window_scale_le (N : ℕ) :
    (d4BMPositiveFourierScale N : ℝ) ≤ 2 * Real.pi * ((N : ℝ) + 1) := le_of_eq rfl

theorem window_inv_le : 1 / Y ≤ 2 / Y₀ := by
  have hYpos := window_pos hY₀ hY
  rw [div_le_div_iff₀ hYpos hY₀]
  linarith [hY.1]

theorem window_inv_sq_le : 1 / Y ^ 2 ≤ 4 / Y₀ ^ 2 := by
  have hYpos := window_pos hY₀ hY
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have := hY.1
  nlinarith

end Window

/-! ## Majorants of the Whittaker functions and their jets -/

/-- Degree-`d` window domination: `‖f N ν Y‖ ≤ K (N+1)^d B_N` for `‖ν‖ ≤ R`, `Y` in the window. -/
def WindowDominated (Y₀ R : ℝ) (d : ℕ) (f : ℕ → ℂ → ℝ → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (ν : ℂ), ‖ν‖ ≤ R → ∀ Y ∈ Icc (Y₀ / 2) (2 * Y₀),
    ‖f N ν Y‖ ≤ K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N

theorem WindowDominated.add {Y₀ R : ℝ} {d : ℕ} {f g : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (hg : WindowDominated Y₀ R d g) :
    WindowDominated Y₀ R d (fun N ν Y => f N ν Y + g N ν Y) := by
  obtain ⟨K₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, by positivity, fun N ν hν Y hY => ?_⟩
  calc ‖f N ν Y + g N ν Y‖ ≤ ‖f N ν Y‖ + ‖g N ν Y‖ := norm_add_le _ _
    _ ≤ K₁ * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N +
          K₂ * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N :=
        add_le_add (h₁ N ν hν Y hY) (h₂ N ν hν Y hY)
    _ = (K₁ + K₂) * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N := by ring

theorem WindowDominated.sub {Y₀ R : ℝ} {d : ℕ} {f g : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (hg : WindowDominated Y₀ R d g) :
    WindowDominated Y₀ R d (fun N ν Y => f N ν Y - g N ν Y) := by
  obtain ⟨K₁, hK₁, h₁⟩ := hf
  obtain ⟨K₂, hK₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, by positivity, fun N ν hν Y hY => ?_⟩
  calc ‖f N ν Y - g N ν Y‖ ≤ ‖f N ν Y‖ + ‖g N ν Y‖ := norm_sub_le _ _
    _ ≤ K₁ * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N +
          K₂ * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N :=
        add_le_add (h₁ N ν hν Y hY) (h₂ N ν hν Y hY)
    _ = (K₁ + K₂) * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N := by ring

theorem WindowDominated.const_mul {Y₀ R : ℝ} {d : ℕ} {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (a : ℂ) :
    WindowDominated Y₀ R d (fun N ν Y => a * f N ν Y) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨‖a‖ * K, by positivity, fun N ν hν Y hY => ?_⟩
  rw [norm_mul]
  calc ‖a‖ * ‖f N ν Y‖ ≤ ‖a‖ * (K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N) :=
        mul_le_mul_of_nonneg_left (h N ν hν Y hY) (norm_nonneg a)
    _ = ‖a‖ * K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N := by ring

theorem WindowDominated.mono {Y₀ R : ℝ} {d d' : ℕ} (hd : d ≤ d') {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) : WindowDominated Y₀ R d' f := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨K, hK, fun N ν hν Y hY => ?_⟩
  refine (h N ν hν Y hY).trans ?_
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : ((N : ℝ) + 1) ^ d ≤ ((N : ℝ) + 1) ^ d' := pow_le_pow_right₀ hN1 hd
  have hB := besselModeMajorant_nonneg Y₀ (R + 2) N
  calc K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N ≤
        K * ((N : ℝ) + 1) ^ d' * besselModeMajorant Y₀ (R + 2) N := by gcongr

/-- Multiplying by a real factor bounded on the window by `L (N+1)^e` raises the degree by `e`. -/
theorem WindowDominated.mul_window {Y₀ R : ℝ} {d e : ℕ} {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (g : ℕ → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ N : ℕ, ∀ Y ∈ Icc (Y₀ / 2) (2 * Y₀), |g N Y| ≤ L * ((N : ℝ) + 1) ^ e) :
    WindowDominated Y₀ R (d + e) (fun N ν Y => f N ν Y * ((g N Y : ℝ) : ℂ)) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨K * L, by positivity, fun N ν hν Y hY => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := h N ν hν Y hY
  have h2 := hg N Y hY
  have hB := besselModeMajorant_nonneg Y₀ (R + 2) N
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  calc ‖f N ν Y‖ * |g N Y| ≤
        (K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N) * (L * ((N : ℝ) + 1) ^ e) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = K * L * ((N : ℝ) + 1) ^ (d + e) * besselModeMajorant Y₀ (R + 2) N := by
        rw [pow_add]; ring

/-- The Bessel factor at a shifted order is degree-`0` dominated. -/
theorem windowDominated_bessel {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 2) :
    WindowDominated Y₀ R 0 (fun N ν Y =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + k)) := by
  refine ⟨1, zero_le_one, fun N ν hν Y hY => ?_⟩
  have := norm_modifiedBesselKOrder_window_shift_le hY₀ hY hν N hk
  simpa using this

theorem WindowDominated.congr {Y₀ R : ℝ} {d : ℕ} {f g : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f)
    (h : ∀ N ν, ∀ Y ∈ Icc (Y₀ / 2) (2 * Y₀), g N ν Y = f N ν Y) :
    WindowDominated Y₀ R d g := by
  obtain ⟨K, hK, hf⟩ := hf
  exact ⟨K, hK, fun N ν hν Y hY => by rw [h N ν Y hY]; exact hf N ν hν Y hY⟩

theorem WindowDominated.zero {Y₀ R : ℝ} {d : ℕ} : WindowDominated Y₀ R d (fun _ _ _ => 0) :=
  ⟨0, le_rfl, fun N ν _ Y _ => by simp⟩

/-- `P₀(ν + k) = √Y · K_{cY}(ν + k)`, degree `0`. -/
theorem windowDominated_whittakerP0 {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 2) :
    WindowDominated Y₀ R 0
      (fun N ν Y => d4BMWhittakerP0 (d4BMPositiveFourierScale N) (ν + k) Y) := by
  have h := (windowDominated_bessel (R := R) hY₀ hk).mul_window (fun _ Y => Real.sqrt Y)
    (L := Real.sqrt (2 * Y₀)) (Real.sqrt_nonneg _) (fun N Y hY => by
      rw [abs_of_nonneg (Real.sqrt_nonneg _), pow_zero, mul_one]
      exact window_sqrt_le hY)
  refine (h.congr fun N ν Y _ => ?_)
  unfold d4BMWhittakerP0
  ring

/-- `P₀'(ν + k)` for `|k| ≤ 1`, degree `1`. -/
theorem windowDominated_whittakerP0FirstJet {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 1) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMWhittakerP0FirstJet (d4BMPositiveFourierScale N) (ν + k) Y) := by
  have hk0 : |k| ≤ 2 := hk.trans (by norm_num)
  have hk1 : |k + 1| ≤ 2 := by
    have := abs_le.mp hk; rw [abs_le]; constructor <;> linarith
  have hk2 : |k - 1| ≤ 2 := by
    have := abs_le.mp hk; rw [abs_le]; constructor <;> linarith
  -- first summand: (1/(2√Y)) K(ν+k)
  have hA : WindowDominated Y₀ R 1 (fun N ν Y =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + k) * ((1 / (2 * Real.sqrt Y) : ℝ) : ℂ)) := by
    have h := (windowDominated_bessel (R := R) hY₀ hk0).mul_window (fun _ Y => 1 / (2 * Real.sqrt Y))
      (L := 1 / (2 * Real.sqrt (Y₀ / 2))) (by positivity) (fun N Y hY => by
        have hYpos := window_pos hY₀ hY
        rw [abs_of_nonneg (by positivity), pow_zero, mul_one]
        exact window_inv_sqrt_le hY₀ hY)
    exact h.mono (by norm_num)
  -- second summand: √Y c (−1/2)(K(ν+k+1) + K(ν+k−1))
  have hB1 : WindowDominated Y₀ R 0 (fun N ν Y =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + k + 1)) := by
    refine (windowDominated_bessel (R := R) hY₀ hk1).congr fun N ν Y _ => ?_
    push_cast; ring_nf
  have hB2 : WindowDominated Y₀ R 0 (fun N ν Y =>
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        ((d4BMPositiveFourierScale N : ℝ) * Y) (ν + k - 1)) := by
    refine (windowDominated_bessel (R := R) hY₀ hk2).congr fun N ν Y _ => ?_
    push_cast; ring_nf
  have hB := (hB1.add hB2).mul_window (fun N Y => Real.sqrt Y * (d4BMPositiveFourierScale N : ℝ))
    (L := Real.sqrt (2 * Y₀) * (2 * Real.pi)) (by positivity) (fun N Y hY => by
      have hYpos := window_pos hY₀ hY
      have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (d4BMPositiveFourierScale N).2.le), hc,
        pow_one]
      have := window_sqrt_le (Y₀ := Y₀) hY
      have hN : (0 : ℝ) ≤ 2 * Real.pi * ((N : ℝ) + 1) := by positivity
      calc Real.sqrt Y * (2 * Real.pi * ((N : ℝ) + 1)) ≤
            Real.sqrt (2 * Y₀) * (2 * Real.pi * ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right this hN
        _ = Real.sqrt (2 * Y₀) * (2 * Real.pi) * ((N : ℝ) + 1) := by ring)
  have hB' := hB.const_mul (-(1 / 2 : ℂ))
  refine (hA.add (hB'.mono (by norm_num))).congr fun N ν Y _ => ?_
  unfold d4BMWhittakerP0FirstJet
  push_cast
  ring

/-- `P₁(ν + k) = P₀(ν + k) · cY`, degree `1`. -/
theorem windowDominated_whittakerP1 {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 2) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMWhittakerP1 (d4BMPositiveFourierScale N) (ν + k) Y) := by
  have h := (windowDominated_whittakerP0 (R := R) hY₀ hk).mul_window
    (fun N Y => (d4BMPositiveFourierScale N : ℝ) * Y) (L := 4 * Real.pi * Y₀) (by positivity)
    (fun N Y hY => by
      have hYpos := window_pos hY₀ hY
      rw [abs_of_nonneg (mul_nonneg (d4BMPositiveFourierScale N).2.le hYpos.le), pow_one]
      exact window_scale_mul_le hY N)
  exact h.congr fun N ν Y _ => rfl

/-- The real-height form of `P₁'`. -/
def whittakerP1FirstJet (c : D4BMPositiveReal) (ν : ℂ) (Y : ℝ) : ℂ :=
  d4BMWhittakerP0FirstJet c ν Y * (((c : ℝ) * Y : ℝ) : ℂ) + d4BMWhittakerP0 c ν Y * (c : ℂ)

theorem whittakerP1FirstJet_eq (c : D4BMPositiveReal) (ν : ℂ) (Y : D4BMPositiveReal) :
    whittakerP1FirstJet c ν Y = d4BMWhittakerP1Deriv c ν Y := by
  unfold whittakerP1FirstJet d4BMWhittakerP1Deriv
  rw [d4BM_whittakerP0FirstJet_eq_deriv]

/-- `P₁'(ν + k)` for `|k| ≤ 1`, degree `2`. -/
theorem windowDominated_whittakerP1FirstJet {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 1) :
    WindowDominated Y₀ R 2
      (fun N ν Y => whittakerP1FirstJet (d4BMPositiveFourierScale N) (ν + k) Y) := by
  have hk0 : |k| ≤ 2 := hk.trans (by norm_num)
  have hA := (windowDominated_whittakerP0FirstJet (R := R) hY₀ hk).mul_window
    (fun N Y => (d4BMPositiveFourierScale N : ℝ) * Y) (L := 4 * Real.pi * Y₀) (by positivity)
    (fun N Y hY => by
      have hYpos := window_pos hY₀ hY
      rw [abs_of_nonneg (mul_nonneg (d4BMPositiveFourierScale N).2.le hYpos.le), pow_one]
      exact window_scale_mul_le hY N)
  have hB := (windowDominated_whittakerP0 (R := R) hY₀ hk0).mul_window
    (fun N _ => (d4BMPositiveFourierScale N : ℝ)) (L := 2 * Real.pi) (by positivity)
    (fun N Y _ => by
      rw [abs_of_nonneg (d4BMPositiveFourierScale N).2.le, pow_one]
      exact window_scale_le N)
  refine (hA.add (hB.mono (by norm_num))).congr fun N ν Y _ => ?_
  unfold whittakerP1FirstJet
  rfl

/-! ## The shifted radial words and the second jet -/

theorem abs_add_one_le {k : ℤ} (hk : |k| ≤ 1) : |k + 1| ≤ 2 := by
  have := abs_le.mp hk; rw [abs_le]; constructor <;> linarith

theorem abs_sub_one_le {k : ℤ} (hk : |k| ≤ 1) : |k - 1| ≤ 2 := by
  have := abs_le.mp hk; rw [abs_le]; constructor <;> linarith

/-- `P₁(ν + k + 1)` and `P₁(ν + k − 1)` for `|k| ≤ 1`, degree `1`. -/
theorem windowDominated_whittakerP1_shift {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ}
    (j : ℤ) (hj : |k + j| ≤ 2) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMWhittakerP1 (d4BMPositiveFourierScale N) (ν + k + j) Y) := by
  refine (windowDominated_whittakerP1 (R := R) hY₀ hj).congr fun N ν Y _ => ?_
  push_cast; ring_nf

/-- The raise-zero shift word, degree `1`. -/
theorem windowDominated_raiseZeroShift {Y₀ R : ℝ} (hY₀ : 0 < Y₀) {k : ℤ} (hk : |k| ≤ 1) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMPositiveFrequencyRaiseZeroShift (d4BMPositiveFourierScale N) (ν + k) Y) := by
  have hk0 : |k| ≤ 2 := hk.trans (by norm_num)
  have h0 := ((windowDominated_whittakerP0 (R := R) hY₀ hk0).mono (by norm_num : 0 ≤ 1)).const_mul
    (1 / 2 : ℂ)
  have h1 := windowDominated_whittakerP1 (R := R) hY₀ hk0
  have h2 := (windowDominated_whittakerP1_shift (R := R) hY₀ (k := k) 1
    (abs_add_one_le hk)).const_mul (1 / 2 : ℂ)
  have h3 := (windowDominated_whittakerP1_shift (R := R) hY₀ (k := k) (-1) (by
    simpa [sub_eq_add_neg] using abs_sub_one_le hk)).const_mul (1 / 2 : ℂ)
  refine (((h0.sub h1).sub h2).sub h3).congr fun N ν Y _ => ?_
  unfold d4BMPositiveFrequencyRaiseZeroShift
  push_cast
  ring_nf

/-- The real-height raise-zero mode derivative word. -/
def raiseZeroModeDerivR (c : D4BMPositiveReal) (ν : ℂ) (Y : ℝ) : ℂ :=
  (1 / 2 : ℂ) * d4BMWhittakerP0FirstJet c ν Y -
    whittakerP1FirstJet c ν Y -
    (1 / 2 : ℂ) * whittakerP1FirstJet c (ν + 1) Y -
    (1 / 2 : ℂ) * whittakerP1FirstJet c (ν - 1) Y

theorem raiseZeroModeDerivR_eq (c : D4BMPositiveReal) (ν : ℂ) (Y : D4BMPositiveReal) :
    raiseZeroModeDerivR c ν Y = d4BMPositiveFrequencyRaiseZeroModeDeriv c ν Y := by
  unfold raiseZeroModeDerivR d4BMPositiveFrequencyRaiseZeroModeDeriv
  rw [whittakerP1FirstJet_eq, whittakerP1FirstJet_eq, whittakerP1FirstJet_eq,
    d4BM_whittakerP0FirstJet_eq_deriv]

/-- The raise-zero mode derivative word at `ν` (`k = 0`), degree `2`. -/
theorem windowDominated_raiseZeroModeDerivR {Y₀ R : ℝ} (hY₀ : 0 < Y₀) :
    WindowDominated Y₀ R 2
      (fun N ν Y => raiseZeroModeDerivR (d4BMPositiveFourierScale N) ν Y) := by
  have h0 := ((windowDominated_whittakerP0FirstJet (R := R) hY₀ (k := 0) (by norm_num)).mono
    (by norm_num : 1 ≤ 2)).const_mul (1 / 2 : ℂ)
  have h1 := windowDominated_whittakerP1FirstJet (R := R) hY₀ (k := 0) (by norm_num)
  have h2 := (windowDominated_whittakerP1FirstJet (R := R) hY₀ (k := 1) (by norm_num)).const_mul
    (1 / 2 : ℂ)
  have h3 := (windowDominated_whittakerP1FirstJet (R := R) hY₀ (k := -1) (by norm_num)).const_mul
    (1 / 2 : ℂ)
  refine (((h0.sub h1).sub h2).sub h3).congr fun N ν Y _ => ?_
  unfold raiseZeroModeDerivR
  push_cast
  ring_nf

/-- The real-height second jet of `P₀`. -/
def whittakerP0SecondJetR (c : D4BMPositiveReal) (ν : ℂ) (Y : ℝ) : ℂ :=
  raiseZeroModeDerivR c ν Y / (Y : ℂ) -
    d4BMPositiveFrequencyRaiseZeroShift c ν Y / (Y : ℂ) ^ 2 +
    (c : ℂ) * d4BMWhittakerP0FirstJet c ν Y

theorem whittakerP0SecondJetR_eq (c : D4BMPositiveReal) (ν : ℂ) (Y : D4BMPositiveReal) :
    whittakerP0SecondJetR c ν Y = d4BMWhittakerP0SecondJet c ν Y := by
  unfold whittakerP0SecondJetR d4BMWhittakerP0SecondJet
  rw [raiseZeroModeDerivR_eq]

/-- The second jet of `P₀`, degree `2`. -/
theorem windowDominated_whittakerP0SecondJetR {Y₀ R : ℝ} (hY₀ : 0 < Y₀) :
    WindowDominated Y₀ R 2
      (fun N ν Y => whittakerP0SecondJetR (d4BMPositiveFourierScale N) ν Y) := by
  have hA := (windowDominated_raiseZeroModeDerivR (R := R) hY₀).mul_window (fun _ Y => 1 / Y)
    (L := 2 / Y₀) (by positivity) (fun N Y hY => by
      have hYpos := window_pos hY₀ hY
      rw [abs_of_nonneg (by positivity), pow_zero, mul_one]
      exact window_inv_le hY₀ hY)
  have hB := (windowDominated_raiseZeroShift (R := R) hY₀ (k := 0) (by norm_num)).mul_window
    (fun _ Y => 1 / Y ^ 2) (L := 4 / Y₀ ^ 2) (by positivity) (fun N Y hY => by
      have hYpos := window_pos hY₀ hY
      rw [abs_of_nonneg (by positivity), pow_zero, mul_one]
      exact window_inv_sq_le hY₀ hY)
  have hC := (windowDominated_whittakerP0FirstJet (R := R) hY₀ (k := 0) (by norm_num)).mul_window
    (fun N _ => (d4BMPositiveFourierScale N : ℝ)) (L := 2 * Real.pi) (by positivity)
    (fun N Y _ => by
      rw [abs_of_nonneg (d4BMPositiveFourierScale N).2.le, pow_one]
      exact window_scale_le N)
  refine ((hA.mono (by norm_num)).sub (hB.mono (by norm_num)) |>.add (hC.mono (by norm_num))).congr
    fun N ν Y hY => ?_
  have hYpos := window_pos hY₀ hY
  unfold whittakerP0SecondJetR
  simp only [add_zero, Int.cast_zero]
  push_cast
  field_simp

/-! ## The signed Whittaker modes and their jets -/

theorem norm_fourierPhase (negative : Bool) (N : ℕ) (x : ℝ) :
    ‖d4BMCompletedEisensteinFourierPhase negative N x‖ = 1 := by
  unfold d4BMCompletedEisensteinFourierPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_signedFourierRate (negative : Bool) (N : ℕ) :
    ‖d4BMSignedFourierRate negative N‖ = 2 * Real.pi * ((N : ℝ) + 1) := by
  unfold d4BMSignedFourierRate d4BMFourierSign
  have hc : (d4BMPositiveFourierScale N : ℝ) = 2 * Real.pi * ((N : ℝ) + 1) := rfl
  rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (d4BMPositiveFourierScale N).2.le, hc]
  split_ifs <;> simp

/-- Multiplying by the phase (norm one) preserves domination. -/
theorem WindowDominated.phase_mul {Y₀ R : ℝ} {d : ℕ} {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R d
      (fun N ν Y => d4BMCompletedEisensteinFourierPhase negative N x * f N ν Y) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨K, hK, fun N ν hν Y hY => ?_⟩
  rw [norm_mul, norm_fourierPhase, one_mul]
  exact h N ν hν Y hY

/-- Multiplying by the Fourier rate raises the degree by one. -/
theorem WindowDominated.rate_mul {Y₀ R : ℝ} {d : ℕ} {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) (negative : Bool) :
    WindowDominated Y₀ R (d + 1)
      (fun N ν Y => d4BMSignedFourierRate negative N * f N ν Y) := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨2 * Real.pi * K, by positivity, fun N ν hν Y hY => ?_⟩
  rw [norm_mul, norm_signedFourierRate]
  have h1 := h N ν hν Y hY
  have hB := besselModeMajorant_nonneg Y₀ (R + 2) N
  have hN : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
  calc 2 * Real.pi * ((N : ℝ) + 1) * ‖f N ν Y‖ ≤
        2 * Real.pi * ((N : ℝ) + 1) * (K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 * Real.pi * K * ((N : ℝ) + 1) ^ (d + 1) * besselModeMajorant Y₀ (R + 2) N := by
        rw [pow_succ]; ring

theorem windowDominated_mode {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 0 (fun N ν Y => d4BMSignedWhittakerMode negative N ν x Y) := by
  refine ((windowDominated_whittakerP0 (R := R) hY₀ (k := 0) (by norm_num)).phase_mul negative x).congr
    fun N ν Y _ => ?_
  unfold d4BMSignedWhittakerMode
  simp

theorem windowDominated_mode_horizontalFirst {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMSignedWhittakerModeHorizontalFirstJet negative N ν x Y) :=
  ((windowDominated_mode (R := R) hY₀ negative x).rate_mul negative).congr fun _ _ _ _ => rfl

theorem windowDominated_mode_verticalFirst {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 1
      (fun N ν Y => d4BMSignedWhittakerModeVerticalFirstJet negative N ν x Y) := by
  refine ((windowDominated_whittakerP0FirstJet (R := R) hY₀ (k := 0) (by norm_num)).phase_mul
    negative x).congr fun N ν Y _ => ?_
  unfold d4BMSignedWhittakerModeVerticalFirstJet
  simp

theorem windowDominated_mode_horizontalSecond {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 2
      (fun N ν Y => d4BMSignedWhittakerModeHorizontalSecondJet negative N ν x Y) := by
  refine (((windowDominated_mode (R := R) hY₀ negative x).rate_mul negative).rate_mul negative).congr
    fun N ν Y _ => ?_
  unfold d4BMSignedWhittakerModeHorizontalSecondJet
  ring

theorem windowDominated_mode_mixedSecond {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 2
      (fun N ν Y => d4BMSignedWhittakerModeMixedSecondJet negative N ν x Y) :=
  ((windowDominated_mode_verticalFirst (R := R) hY₀ negative x).rate_mul negative).congr
    fun _ _ _ _ => rfl

/-- The real-height vertical second jet of a signed mode. -/
def signedModeVerticalSecondJetR (negative : Bool) (N : ℕ) (ν : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinFourierPhase negative N x *
    whittakerP0SecondJetR (d4BMPositiveFourierScale N) ν Y

theorem signedModeVerticalSecondJetR_eq (negative : Bool) (N : ℕ) (ν : ℂ) (x : ℝ)
    (Y : D4BMPositiveReal) :
    signedModeVerticalSecondJetR negative N ν x Y =
      d4BMSignedWhittakerModeVerticalSecondJet negative N ν x Y := by
  unfold signedModeVerticalSecondJetR d4BMSignedWhittakerModeVerticalSecondJet
  rw [whittakerP0SecondJetR_eq]

theorem windowDominated_mode_verticalSecondR {Y₀ R : ℝ} (hY₀ : 0 < Y₀) (negative : Bool) (x : ℝ) :
    WindowDominated Y₀ R 2 (fun N ν Y => signedModeVerticalSecondJetR negative N ν x Y) :=
  ((windowDominated_whittakerP0SecondJetR (R := R) hY₀).phase_mul negative x).congr
    fun _ _ _ _ => rfl

/-! ## Weighted majorants and summability -/

/-- The summable majorant `(N+1)^p · B_N`. -/
theorem summable_pow_mul_besselModeMajorant {Y₀ : ℝ} (hY₀ : 0 < Y₀) (R : ℝ) (p : ℕ) :
    Summable fun N : ℕ => ((N : ℝ) + 1) ^ p * besselModeMajorant Y₀ R N := by
  unfold besselModeMajorant
  have h := Real.summable_pow_mul_exp_neg_nat_mul p (show 0 < Real.pi * Y₀ by positivity)
  have h' := (summable_nat_add_iff 1).mpr h
  have h'' := h'.mul_left (Real.exp (R ^ 2 / (2 * Real.pi * Y₀)) * Real.sqrt (2 / Y₀))
  refine h''.congr fun N => ?_
  push_cast
  ring_nf

/-- A window-dominated family, weighted by the Whittaker coefficient at the parameter `u`, has the
summable majorant `K (N+1)^{d+m} B_N`, `m = ⌈3R + 1⌉`. -/
theorem WindowDominated.weighted {Y₀ R : ℝ} {d : ℕ} {f : ℕ → ℂ → ℝ → ℂ}
    (hf : WindowDominated Y₀ R d f) {u : ℂ} (hu : ‖u‖ ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, ∀ Y ∈ Icc (Y₀ / 2) (2 * Y₀),
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ * f N u Y‖ ≤
        K * ((N : ℝ) + 1) ^ (d + ⌈3 * R + 1⌉₊) * besselModeMajorant Y₀ (R + 2) N := by
  obtain ⟨K, hK, h⟩ := hf
  refine ⟨K, hK, fun N Y hY => ?_⟩
  rw [norm_mul]
  have hcoef : ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ ≤
      ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
    refine (d4BM_norm_completedEisensteinWhittakerCoefficient_le u ⟨N + 1, by omega⟩).trans ?_
    have hN1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hre : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    calc ((N + 1 : ℕ) : ℝ) ^ (3 * |u.re| + 1) ≤ ((N + 1 : ℕ) : ℝ) ^ (⌈3 * R + 1⌉₊ : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
          have := Nat.le_ceil (3 * R + 1)
          linarith
      _ = ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) := by
          rw [Real.rpow_natCast]; push_cast; rfl
  have h1 := h N u hu Y hY
  have hB := besselModeMajorant_nonneg Y₀ (R + 2) N
  calc ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ * ‖f N u Y‖ ≤
        ((N : ℝ) + 1) ^ (⌈3 * R + 1⌉₊) *
          (K * ((N : ℝ) + 1) ^ d * besselModeMajorant Y₀ (R + 2) N) :=
        mul_le_mul hcoef h1 (norm_nonneg _) (by positivity)
    _ = K * ((N : ℝ) + 1) ^ (d + ⌈3 * R + 1⌉₊) * besselModeMajorant Y₀ (R + 2) N := by
        rw [pow_add]; ring

end

end RHTower
