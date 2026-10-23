import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheQuarterLawOfTheConstantSignPattern
import GaloisForLFunctions.RHTower.ZetaLogDerivBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLowerNearAbscissa

/-!
# The quarter law of the constant-sign pattern on the full range `[−1, 1]`

For `−1 ≤ z < 0` the Euler bracket of `F_z(w) = Σ z^{Ω(n)} n^{-w}` gives
`|F_z(w)| ≤ e^{2S} |ζ(w)|^{z} = e^{2S} (1/|ζ(w)|)^{|z|} ≤ e^{2S}(1 + 1/|ζ(w)|)`, so the receiver of
`z^{Ω(d)} d^{-1/2}` is controlled by `1/ζ` just right of `Re w = 1`:

* `1/|ζ(w)| ≤ K |Im w|^{1/4}` for `1 < Re w ≤ 2`, `|Im w| ≥ 9` (`exists_inv_norm_zeta_le_rpow_large`):
  inside the de la Vallée Poussin strip `|1/ζ| ≤ (20/A) log⁷|t|`; beyond it the `3–4–1` inequality
  gives `1/|ζ(σ+it)| ≤ (1 + 1/(σ−1))^{3/4} (log|2t| + 5)^{1/4} ≤ (1 + log⁹|t|/A)(log|t| + 6)`;
* `1/|ζ(w)|` is bounded on `1 < Re w ≤ 2`, `|Im w| ≤ 9` (`exists_inv_norm_zeta_le_box`):
  `|ζ(w)| ≥ 1/(2|w − 1|)` near the pole and compactness elsewhere, `ζ ≠ 0` on `Re w ≥ 1`.

A bounded shifted series at small heights and an `O(|t|^{1/4})` series at large heights pay the
boundary line energy (`exists_lineEnergy_le_of_bounds`), so the weight is paid for every
`z ∈ [−1, 0)`. With the threshold results this is the complete law: for every `z ∈ [−1, 1]`,
`z^{Ω(d)} d^{-1/2}` is paid **iff** `z < 1/2` (`receiverBounded_constantSign_iff_full`). The endpoint
`z = −1` is the Liouville weight; the interior `(−1, 1)` consists of weights pretending to no
character.
-/

open Filter Topology MeasureTheory Complex Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### `1/ζ` just right of `Re w = 1` -/

/-- `log x ≤ 40 x^{1/40}` for `x ≥ 0`. -/
theorem log_le_forty_rpow {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 40 * x ^ (1 / 40 : ℝ) := by
  have h := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 40 by norm_num)
  rw [div_eq_mul_inv] at h
  linarith [show x ^ (1 / 40 : ℝ) * (1 / 40 : ℝ)⁻¹ = 40 * x ^ (1 / 40 : ℝ) by norm_num; ring]

/-- `log^{10} x ≤ 40^{10} x^{1/4}` for `x ≥ 1`. -/
theorem log_pow_ten_le_rpow {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 10 ≤ 40 ^ 10 * x ^ (1 / 4 : ℝ) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h := pow_le_pow_left₀ h0 (log_le_forty_rpow (by linarith)) 10
  have hp : (40 * x ^ (1 / 40 : ℝ)) ^ 10 = 40 ^ 10 * x ^ (1 / 4 : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ (1 / 40 : ℝ)), ← Real.rpow_mul (by linarith)]
    norm_num
  linarith

/-- **`1/ζ` at large heights**: `1/|ζ(w)| ≤ K |Im w|^{1/4}` for `1 < Re w ≤ 2`, `|Im w| ≥ 9`. -/
theorem exists_inv_norm_zeta_le_rpow_large :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → 9 ≤ |w.im| →
      ‖riemannZeta w‖⁻¹ ≤ K * |w.im| ^ (1 / 4 : ℝ) := by
  set A := RHTower.zetaLowerA
  have hA : 0 < A := RHTower.zetaLowerA_pos
  refine ⟨max (20 / A) (4 * (1 + 1 / A)) * 40 ^ 10, by positivity, fun w hw hw2 ht => ?_⟩
  set σ := w.re
  set t := w.im
  have hwst : w = (σ : ℂ) + (t : ℂ) * I := (Complex.re_add_im w).symm
  set L := Real.log |t|
  have hL2 : 2 ≤ L := by
    have h1 : Real.log (Real.exp 2) ≤ Real.log |t| :=
      Real.log_le_log (Real.exp_pos 2) (by have := RHTower.exp_two_lt_eight; linarith)
    rwa [Real.log_exp] at h1
  have hL1 : 1 ≤ L := by linarith
  have hL9 : 1 ≤ L ^ 9 := one_le_pow₀ hL1
  have hζ0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw.le
  have hpos : 0 < ‖riemannZeta w‖ := norm_pos_iff.mpr hζ0
  -- both regions give `≤ max(20/A, 4(1 + 1/A)) · L^{10}`
  have hmain : ‖riemannZeta w‖⁻¹ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 := by
    by_cases hstrip : σ ≤ 1 + A / L ^ 9
    · have h := RHTower.norm_inv_riemannZeta_le (σ := σ) (t := t) ht
        (by have : 0 ≤ A / L ^ 9 := by positivity
            linarith) hstrip
      rw [← hwst, norm_inv] at h
      calc ‖riemannZeta w‖⁻¹ ≤ 20 / A * L ^ 7 := h
        _ ≤ 20 / A * L ^ 10 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by norm_num)) (by positivity)
        _ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · have hσA : A / L ^ 9 < σ - 1 := by linarith [not_le.mp hstrip]
      have hσ1 : 1 < σ := by have : 0 < A / L ^ 9 := by positivity
                             linarith
      -- the doubled height
      have hB : ‖riemannZeta ((σ : ℂ) + 2 * (t : ℂ) * I)‖ ≤ L + 6 := by
        have h := RHTower.norm_riemannZeta_le_log_add (s := (σ : ℂ) + 2 * (t : ℂ) * I)
          (by simp; linarith) (by simp; linarith) (by simp [abs_mul]; linarith)
        have him : ((σ : ℂ) + 2 * (t : ℂ) * I).im = 2 * t := by simp
        rw [him, abs_mul, abs_two, Real.log_mul (by norm_num) (by linarith)] at h
        have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
        linarith
      have hneg := RHTower.Sieve.neg_log_norm_riemannZeta_le_of_bound (σ := σ) (t := t)
        (B := L + 6) hσ1 hB
      rw [← hwst] at hneg
      have hx1 : 1 ≤ 1 + 1 / (σ - 1) := by
        have : 0 < 1 / (σ - 1) := one_div_pos.mpr (by linarith)
        linarith
      have hx : 1 + 1 / (σ - 1) ≤ 1 + L ^ 9 / A := by
        have hpos' : 0 < A / L ^ 9 := by positivity
        have h1 : 1 / (σ - 1) < 1 / (A / L ^ 9) := one_div_lt_one_div_of_lt hpos' hσA
        rw [one_div_div] at h1
        linarith
      have hB1 : 1 ≤ L + 6 := by linarith
      -- `1/|ζ| = exp(−log|ζ|) ≤ (1 + 1/(σ−1))^{3/4} (L+6)^{1/4} ≤ (1 + 1/(σ−1))(L+6)`
      have hexp : ‖riemannZeta w‖⁻¹ ≤ (1 + 1 / (σ - 1)) * (L + 6) := by
        have h1 : ‖riemannZeta w‖⁻¹ = Real.exp (-Real.log ‖riemannZeta w‖) := by
          rw [Real.exp_neg, Real.exp_log hpos]
        have h2 : Real.exp (3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log (L + 6)) =
            (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) * (L + 6) ^ (1 / 4 : ℝ) := by
          rw [Real.exp_add, Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith),
            mul_comm (3 / 4 : ℝ), mul_comm (1 / 4 : ℝ)]
        have h3 : (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) ≤ 1 + 1 / (σ - 1) := by
          calc (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) ≤ (1 + 1 / (σ - 1)) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
            _ = 1 + 1 / (σ - 1) := Real.rpow_one _
        have h4 : (L + 6) ^ (1 / 4 : ℝ) ≤ L + 6 := by
          calc (L + 6) ^ (1 / 4 : ℝ) ≤ (L + 6) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num)
            _ = L + 6 := Real.rpow_one _
        rw [h1]
        calc Real.exp (-Real.log ‖riemannZeta w‖)
            ≤ Real.exp (3 / 4 * Real.log (1 + 1 / (σ - 1)) + 1 / 4 * Real.log (L + 6)) :=
              Real.exp_le_exp.mpr hneg
          _ = (1 + 1 / (σ - 1)) ^ (3 / 4 : ℝ) * (L + 6) ^ (1 / 4 : ℝ) := h2
          _ ≤ (1 + 1 / (σ - 1)) * (L + 6) :=
              mul_le_mul h3 h4 (by positivity) (by linarith)
      calc ‖riemannZeta w‖⁻¹ ≤ (1 + 1 / (σ - 1)) * (L + 6) := hexp
        _ ≤ (1 + L ^ 9 / A) * (L + 6) := mul_le_mul_of_nonneg_right hx (by linarith)
        _ ≤ (L ^ 9 + L ^ 9 / A) * (4 * L) := by
            apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
        _ = 4 * (1 + 1 / A) * L ^ 10 := by field_simp
        _ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  calc ‖riemannZeta w‖⁻¹ ≤ max (20 / A) (4 * (1 + 1 / A)) * L ^ 10 := hmain
    _ ≤ max (20 / A) (4 * (1 + 1 / A)) * (40 ^ 10 * |t| ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left (log_pow_ten_le_rpow (by linarith)) (by positivity)
    _ = max (20 / A) (4 * (1 + 1 / A)) * 40 ^ 10 * |t| ^ (1 / 4 : ℝ) := by ring

/-- **`1/ζ` on the box** `1 < Re w ≤ 2`, `|Im w| ≤ 9`. -/
theorem exists_inv_norm_zeta_le_box :
    ∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, 1 < w.re → w.re ≤ 2 → |w.im| ≤ 9 → ‖riemannZeta w‖⁻¹ ≤ K := by
  obtain ⟨ρ, hρ, hnear⟩ := exists_norm_zeta_ge_near_one
  set ρ' : ℝ := min ρ 1 / 2
  have hρ' : 0 < ρ' := by positivity
  have hρρ : ρ' < ρ := by have := min_le_left ρ 1; simp only [ρ']; linarith
  have hρ1 : ρ' ≤ 1 / 2 := by have := min_le_right ρ 1; simp only [ρ']; linarith
  set K' : Set ℂ := ((Icc (1 : ℝ) 2) ×ℂ (Icc (-9 : ℝ) 9)) ∩ {w : ℂ | ρ' ≤ ‖w - 1‖}
  have hK' : IsCompact K' :=
    (isCompact_Icc.reProdIm isCompact_Icc).inter_right
      (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hcont : ContinuousOn (fun w => (riemannZeta w)⁻¹) K' := by
    intro w hw
    have hw1 : w ≠ 1 := by
      intro h; have := hw.2; simp only [Set.mem_setOf_eq, h, sub_self, norm_zero] at this; linarith
    have hre : 1 ≤ w.re := ((Complex.mem_reProdIm.mp hw.1).1).1
    exact ((differentiableAt_riemannZeta hw1).continuousAt.inv₀
      (riemannZeta_ne_zero_of_one_le_re hre)).continuousWithinAt
  obtain ⟨C, hC⟩ := hK'.exists_bound_of_continuousOn hcont
  refine ⟨max C 1, by positivity, fun w hw hw2 ht => ?_⟩
  by_cases hfar : ρ' ≤ ‖w - 1‖
  · have hmem : w ∈ K' := ⟨Complex.mem_reProdIm.mpr ⟨⟨hw.le, hw2⟩, abs_le.mp ht⟩, hfar⟩
    have := hC w hmem
    rw [norm_inv] at this
    exact this.trans (le_max_left _ _)
  · have hw1 : w ≠ 1 := by intro h; rw [h] at hw; norm_num at hw
    have hlt : ‖w - 1‖ < ρ' := not_le.mp hfar
    have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw1)
    have h := hnear w hw1 (hlt.trans hρρ)
    have h1 : 1 ≤ 1 / (2 * ‖w - 1‖) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hζ1 : 1 ≤ ‖riemannZeta w‖ := h1.trans h
    exact (inv_le_one_of_one_le₀ hζ1).trans (le_max_right _ _)

/-- `X^a ≤ 1 + X` for `X ≥ 0` and `0 ≤ a ≤ 1`. -/
theorem rpow_le_one_add_self {X a : ℝ} (hX : 0 ≤ X) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    X ^ a ≤ 1 + X := by
  rcases le_total X 1 with h | h
  · have := Real.rpow_le_one hX h ha0; linarith
  · have := Real.rpow_le_rpow_of_exponent_le h ha1
    rw [Real.rpow_one] at this; linarith

/-- For `−1 ≤ z ≤ 0` on `Re w > 1`: `|F_z(w)| ≤ e^{2S}(1 + 1/|ζ(w)|)`. -/
theorem norm_constantSignSeries_le_inv {z : ℝ} (hz : -1 ≤ z) (hz0 : z ≤ 0) {w : ℂ}
    (hw : 1 < w.re) :
    ‖∑' n : ℕ, (constantSignHom z n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)‖ ≤
      Real.exp (2 * primeSquareMass) * (1 + ‖riemannZeta w‖⁻¹) := by
  have h := norm_constantSignSeries_le (z := z) (abs_le.mpr ⟨hz, by linarith⟩) hw
  have hinv : ‖riemannZeta w‖ ^ z = (‖riemannZeta w‖⁻¹) ^ (-z) := by
    rw [Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _), neg_neg]
  rw [hinv] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (rpow_le_one_add_self (inv_nonneg.mpr (norm_nonneg _)) (by linarith) (by linarith))
    (Real.exp_pos _).le)

/-! ### A line-energy criterion -/

/-- **Bounded at small heights, `O(|t|^{1/4})` at large heights pays the line energy.** If the
shifted Dirichlet series satisfies `|C(s) − P| ≤ B₀` for `|t| ≤ 2` and `|C(s) − P| ≤ B₁ |t|^{1/4}` for
`|t| ≥ 2` on the strip `1/2 < σ < 3/4`, the line energies of `ζ(s)(C(s) − P)/s` are uniformly
bounded there. -/
theorem exists_lineEnergy_le_of_bounds {c : ℕ → ℝ} {P B₀ B₁ : ℝ}
    (hsmall : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → |t| ≤ 2 →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₀)
    (hlarge : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 2 ≤ |t| →
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤ B₁ * |t| ^ (1 / 4 : ℝ)) :
    ∃ M : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ < 3 / 4 → ∫ t : ℝ, lineIntegrand c P σ t ≤ M := by
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_box
  obtain ⟨M₂, hM₂⟩ := exists_integral_zeta_sq_rpow_le
  set A₁ : ℝ := 4 * Z₀ ^ 2 * B₀ ^ 2
  set Λ : ℝ := B₁ ^ 2
  refine ⟨2 * (2 * A₁ + Λ * M₂), fun σ hσ hσ' => ?_⟩
  set Φ : ℝ → ℝ := lineIntegrand c P σ with hΦ
  change ∫ t : ℝ, Φ t ≤ _
  have hsnorm : ∀ t : ℝ, σ ≤ ‖(σ : ℂ) + t * I‖ ∧ |t| ≤ ‖(σ : ℂ) + t * I‖ := fun t => by
    constructor
    · have := Complex.abs_re_le_norm ((σ : ℂ) + t * I); simp at this; linarith [le_abs_self σ]
    · have := Complex.abs_im_le_norm ((σ : ℂ) + t * I); simpa using this
  have hΦform : ∀ t, Φ t = ‖riemannZeta ((σ : ℂ) + t * I)‖ ^ 2 *
      ‖weightDirichletSeries c ((σ : ℂ) + t * I) - (P : ℂ)‖ ^ 2 / ‖(σ : ℂ) + t * I‖ ^ 2 :=
    fun t => by simp only [hΦ, lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
  -- small heights: `Φ ≤ 4 Z₀² B₀²`
  have hsmallΦ : ∀ u : ℝ, 0 < u → u ≤ 2 → Φ u ≤ A₁ := by
    intro u hu0 hu2
    have habs : |u| ≤ 2 := by rw [abs_of_pos hu0]; exact hu2
    have hζs := hZ σ u hσ.le hσ'.le habs
    have hCs := hsmall σ u hσ hσ' habs
    have hB₀ : 0 ≤ B₀ := (norm_nonneg _).trans hCs
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + u * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [(hsnorm u).1]) 2
    have hden : 0 < ‖(σ : ℂ) + u * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    rw [hΦform u, div_le_iff₀ hden]
    have hz2 := pow_le_pow_left₀ (norm_nonneg _) hζs 2
    have hc2 := pow_le_pow_left₀ (norm_nonneg _) hCs 2
    calc ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 *
          ‖weightDirichletSeries c ((σ : ℂ) + u * I) - (P : ℂ)‖ ^ 2
        ≤ Z₀ ^ 2 * B₀ ^ 2 := mul_le_mul hz2 hc2 (sq_nonneg _) (sq_nonneg _)
      _ = A₁ * (1 / 2) ^ 2 := by simp only [A₁]; ring
      _ ≤ A₁ * ‖(σ : ℂ) + u * I‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
  -- large heights: `Φ ≤ B₁² |ζ|² u^{-3/2}`
  have hlargeΦ : ∀ u : ℝ, 2 < u →
      Φ u ≤ Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ))) := by
    intro u hu
    have hu0 : 0 < u := by linarith
    have hCu := hlarge σ u hσ hσ' (by rw [abs_of_pos hu0]; linarith)
    rw [abs_of_pos hu0] at hCu
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
  set g : ℝ → ℝ := fun u => if u ≤ 2 then A₁
    else Λ * (‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)))
  obtain ⟨hint2, hbound2⟩ := hM₂ σ hσ.le (by linarith)
  have hgint : IntegrableOn g (Ioi 0) := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_const (C := A₁) (by simp)).congr_fun (fun u hu => ?_) measurableSet_Ioc
      simp only [g, if_pos hu.2]
    · refine IntegrableOn.congr_fun (hint2.const_mul Λ) (fun u hu => ?_) measurableSet_Ioi
      have : ¬ u ≤ 2 := not_le.mpr hu
      simp only [g, if_neg this]
  have hΦle : ∀ u ∈ Ioi (0 : ℝ), Φ u ≤ g u := by
    intro u hu
    by_cases h2 : u ≤ 2
    · simp only [g, if_pos h2]; exact hsmallΦ u hu h2
    · simp only [g, if_neg h2]; exact hlargeΦ u (not_le.mp h2)
  have hΦ0 : ∀ u, 0 ≤ Φ u := fun u => by simp only [hΦ, lineIntegrand]; positivity
  have hhalf : ∫ u in Ioi (0 : ℝ), Φ u ≤ ∫ u in Ioi (0 : ℝ), g u :=
    integral_mono_of_nonneg (Eventually.of_forall hΦ0) hgint
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hΦle))
  have hgval : ∫ u in Ioi (0 : ℝ), g u =
      2 * A₁ + Λ * ∫ u in Ioi (2 : ℝ), ‖riemannZeta ((σ : ℂ) + u * I)‖ ^ 2 * u ^ (-(3 / 2 : ℝ)) := by
    have hsplit : Ioi (0 : ℝ) = Ioc 0 2 ∪ Ioi 2 := (Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
    rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hgint.mono_set (by rw [hsplit]; exact subset_union_left))
      (hgint.mono_set (by rw [hsplit]; exact subset_union_right))]
    congr 1
    · rw [setIntegral_congr_fun (g := fun _ : ℝ => A₁) measurableSet_Ioc
          (fun u hu => by simp only [g, if_pos hu.2]), setIntegral_const]
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

/-! ### The negative range and the full law -/

/-- **The constant-sign pattern is paid on the negative range**: for `−1 ≤ z < 0` the half-damped
weight `z^{Ω(d)} d^{-1/2}` has bounded receiver. -/
theorem receiverBounded_constantSign_neg {z : ℝ} (hz : -1 ≤ z) (hz0 : z < 0) :
    ReceiverBounded (constantSignWeight z) := by
  obtain ⟨K₁, hK₁, hlargeζ⟩ := exists_inv_norm_zeta_le_rpow_large
  obtain ⟨K₂, hK₂, hboxζ⟩ := exists_inv_norm_zeta_le_box
  set P : ℝ := ∑' d : ℕ, constantSignWeight z d / d
  set E2 : ℝ := Real.exp (2 * primeSquareMass)
  have hE2 : 0 < E2 := Real.exp_pos _
  -- the series at `w = s + 1/2`
  have hC : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 →
      ‖weightDirichletSeries (constantSignWeight z) ((σ : ℂ) + t * I) - (P : ℂ)‖ ≤
        E2 * (1 + ‖riemannZeta ((σ : ℂ) + t * I + 1 / 2)‖⁻¹) + |P| := by
    intro σ t hσ hσ'
    rw [weightDirichletSeries_constantSignWeight]
    have hre : 1 < ((σ : ℂ) + t * I + 1 / 2).re := by simp; linarith
    refine (norm_sub_le _ _).trans (add_le_add ?_ (by rw [Complex.norm_real, Real.norm_eq_abs]))
    exact norm_constantSignSeries_le_inv hz hz0.le hre
  have hwre : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).re = σ + 1 / 2 := fun σ t => by simp
  have hwim : ∀ σ t : ℝ, ((σ : ℂ) + t * I + 1 / 2).im = t := fun σ t => by simp
  -- `1/|ζ|` at heights `≥ 2` is `O(|t|^{1/4})`
  have hinv : ∀ σ t : ℝ, 1 / 2 < σ → σ < 3 / 4 → 2 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + t * I + 1 / 2)‖⁻¹ ≤ max K₁ K₂ * |t| ^ (1 / 4 : ℝ) := by
    intro σ t hσ hσ' ht
    have h1 : 1 ≤ |t| ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    by_cases h9 : 9 ≤ |t|
    · have := hlargeζ ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
        (by rw [hwim]; exact h9)
      rw [hwim] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have := hboxζ ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
        (by rw [hwim]; linarith [not_le.mp h9])
      calc _ ≤ K₂ := this
        _ ≤ max K₁ K₂ := le_max_right _ _
        _ ≤ max K₁ K₂ * |t| ^ (1 / 4 : ℝ) := le_mul_of_one_le_right (by positivity) h1
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_bounds (c := constantSignWeight z) (P := P)
    (B₀ := E2 * (1 + K₂) + |P|) (B₁ := E2 * (1 + max K₁ K₂) + |P|)
    (fun σ t hσ hσ' ht => (hC σ t hσ hσ').trans (by
      have := hboxζ ((σ : ℂ) + t * I + 1 / 2) (by rw [hwre]; linarith) (by rw [hwre]; linarith)
        (by rw [hwim]; linarith)
      have := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) this) hE2.le
      linarith))
    (fun σ t hσ hσ' ht => (hC σ t hσ hσ').trans (by
      have h1 : 1 ≤ |t| ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      have h2 := mul_le_mul_of_nonneg_left (hinv σ t hσ hσ' ht) hE2.le
      have hP := abs_nonneg P
      have hm : 0 ≤ max K₁ K₂ := (le_max_left _ _).trans' hK₁.le
      nlinarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ E2 + |P|)]))
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le
    (dampedClass_constantSignWeight (abs_le.mpr ⟨hz, by linarith⟩)) hM⟩

/-- **The quarter law of the constant-sign pattern, full range**: for every `z ∈ [−1, 1]` the
half-damped weight `z^{Ω(d)} d^{-1/2}` is paid exactly when `z < 1/2`. -/
theorem receiverBounded_constantSign_iff_full {z : ℝ} (hz : -1 ≤ z) (hz1 : z ≤ 1) :
    ReceiverBounded (constantSignWeight z) ↔ z < 1 / 2 := by
  rcases lt_or_ge z 0 with h | h
  · exact ⟨fun _ => by linarith, fun _ => receiverBounded_constantSign_neg hz h⟩
  · exact receiverBounded_constantSign_iff h hz1

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
