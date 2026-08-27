import GaloisForLFunctions.RHTower.ZetaChiStripGrowth
import GaloisForLFunctions.RHTower.GammaVerticalRatioUniform
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# The sharp bound for `χ` on a vertical line

Titchmarsh IV.12.3: `|χ(σ+it)| ≍ (|t|/2π)^{1/2-σ}`.  The upper half of that statement, on a *fixed*
line, is what Burnol's Theorem 4.8 feeds into Phragmén--Lindelöf: `ZetaChiStripGrowth` only produces
a power of the height with an exponent coming from the Gamma recurrence, which is far from sharp.

The corpus's parameter-uniform vertical Gamma law `exists_twoSided_gamma_vertical_ratio` gives the
sharp exponent directly once the two abscissae `σ/2` and `(1-σ)/2` are shifted into the region where
it applies: a finite Gamma recurrence moves `σ/2` up by `n = ⌈|σ|⌉ + 1`, which is large enough that
the shifted abscissa always lies to the *right* of `(1-σ)/2`, and the `n` shift factors contribute
exactly the `τ^n` that the recurrence removes.

## Main results

* `norm_Gamma_line_abs` — the vertical Gamma modulus only sees `|t|`
* `exists_norm_zetaChi_line_le` — `‖χ(σ+it)‖ ≤ C|t|^{1/2-σ}` on a fixed line left of `Re s = 1/2`
-/

noncomputable section

open Complex Filter Topology MeasureTheory Set

namespace RHTower

theorem norm_Gamma_line_abs (x t : ℝ) :
    ‖Complex.Gamma ((x : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖Complex.Gamma ((x : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg ht]
    have hconj : ((x : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
        = (starRingEnd ℂ) ((x : ℂ) + (t : ℂ) * Complex.I) := by
      push_cast
      simp [Complex.ext_iff]
    rw [hconj, norm_Gamma_conj]

theorem prod_norm_shift_line_le {y τ : ℝ} (hτ : 1 ≤ τ) (n : ℕ) :
    (∏ i ∈ Finset.range n, ‖((y : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)‖)
      ≤ ((|y| + (n : ℝ) + 1) * τ) ^ n := by
  have hτ0 : 0 < τ := by linarith
  calc (∏ i ∈ Finset.range n, ‖((y : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)‖)
      ≤ ∏ _i ∈ Finset.range n, ((|y| + (n : ℝ) + 1) * τ) := by
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi => ?_)
        have hmem : i < n := Finset.mem_range.1 hi
        have hin : (i : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hmem
        have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        have hz : ((y : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)
            = ((y + (i : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
          push_cast
          ring
        rw [hz]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
        have habs : |y + (i : ℝ)| ≤ |y| + (i : ℝ) := by
          have := norm_add_le y ((i : ℝ))
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hi0] at this
          exact this
        have h1 : |y + (i : ℝ)| ≤ |y| + (n : ℝ) := by linarith
        have h2 : |y| + (n : ℝ) ≤ (|y| + (n : ℝ)) * τ := by
          nlinarith [abs_nonneg y, Nat.cast_nonneg (α := ℝ) n]
        nlinarith
      _ = ((|y| + (n : ℝ) + 1) * τ) ^ n := by
        rw [Finset.prod_const, Finset.card_range]

theorem shift_ne_zero_of_pos_im_line {y τ : ℝ} (hτ : 0 < τ) (i : ℕ) :
    ((y : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ) ≠ 0 := by
  intro h
  have him : (((y : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)).im = τ := by simp
  rw [h] at him
  simp only [Complex.zero_im] at him
  linarith

/-- **The sharp vertical Gamma quotient on a fixed line.** -/
theorem exists_norm_Gamma_quotient_line {σ : ℝ} (hσ : σ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
      ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ C * τ ^ (1 / 2 - σ)
          * ‖Complex.Gamma ((((σ / 2 : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
  classical
  set n : ℕ := ⌈|σ|⌉₊ + 1 with hn
  have hnabs : |σ| + 1 ≤ (n : ℝ) := by
    have h1 : |σ| ≤ (⌈|σ|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (n : ℝ) = (⌈|σ|⌉₊ : ℝ) + 1 := by rw [hn]; push_cast; ring
    linarith
  set β : ℝ := (1 - σ) / 2 with hβ
  set δ : ℝ := σ + (n : ℝ) - 1 / 2 with hδ
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    have : σ ≤ |σ| := le_abs_self σ
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have := abs_nonneg σ
      linarith
    linarith [abs_nonneg σ]
  have hδ0 : 0 ≤ δ := by
    have h1 : -|σ| ≤ σ := neg_abs_le σ
    rw [hδ]
    linarith [neg_abs_le σ]
  have hsum : β + δ = σ / 2 + (n : ℝ) := by rw [hβ, hδ]; ring
  obtain ⟨c, C₀, hc, hC₀, hbnd⟩ :=
    GaloisForLFunctions.RHTower.exists_twoSided_gamma_vertical_ratio (a₁ := β) (δ₁ := δ) hβ0 hδ0
  set K : ℝ := |σ / 2| + (n : ℝ) + 1 with hK
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  refine ⟨C₀ * K ^ n, by positivity, ?_⟩
  intro τ hτ
  have hτ0 : 0 < τ := by linarith
  have hratio := (hbnd β δ τ hβ0 le_rfl hδ0 le_rfl hτ).2
  rw [hsum] at hratio
  -- the recurrence
  have hrec : ‖Complex.Gamma ((((σ / 2 + (n : ℝ) : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖
      = (∏ i ∈ Finset.range n, ‖(((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)‖)
        * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hcast : ((((σ / 2 + (n : ℝ) : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)
        = (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) + (n : ℂ) := by push_cast; ring
    rw [hcast]
    exact GaloisForLFunctions.HTGeometry.norm_Gamma_add_nat _ n
      (fun i _ => shift_ne_zero_of_pos_im_line hτ0 i)
  have hP := prod_norm_shift_line_le (y := σ / 2) hτ n
  have hGpos : 0 < ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ0 (σ / 2))
  have hGden : 0 < ‖Complex.Gamma ((((σ / 2 + (n : ℝ) : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ0 (σ / 2 + (n : ℝ)))
  have hnum : ‖Complex.Gamma (((β : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
      ≤ C₀ * τ ^ (-δ)
        * ‖Complex.Gamma ((((σ / 2 + (n : ℝ) : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    rw [div_le_iff₀ hGden] at hratio
    linarith [hratio]
  have hexp : τ ^ (-δ) * ((K * τ) ^ n) = K ^ n * τ ^ (1 / 2 - σ) := by
    have hpow : ((K * τ) ^ n : ℝ) = K ^ n * τ ^ (n : ℕ) := by rw [mul_pow]
    have hcast : (τ ^ (n : ℕ) : ℝ) = τ ^ ((n : ℕ) : ℝ) := (Real.rpow_natCast τ n).symm
    have hsum2 : -δ + ((n : ℕ) : ℝ) = 1 / 2 - σ := by rw [hδ]; ring
    rw [hpow, hcast]
    calc τ ^ (-δ) * (K ^ n * τ ^ ((n : ℕ) : ℝ))
        = K ^ n * (τ ^ (-δ) * τ ^ ((n : ℕ) : ℝ)) := by ring
      _ = K ^ n * τ ^ (-δ + ((n : ℕ) : ℝ)) := by rw [← Real.rpow_add hτ0]
      _ = K ^ n * τ ^ (1 / 2 - σ) := by rw [hsum2]
  calc ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
      = ‖Complex.Gamma (((β : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ := by rw [hβ]
    _ ≤ C₀ * τ ^ (-δ)
        * ‖Complex.Gamma ((((σ / 2 + (n : ℝ) : ℝ)) : ℂ) + (τ : ℂ) * Complex.I)‖ := hnum
    _ = C₀ * τ ^ (-δ)
        * ((∏ i ∈ Finset.range n, ‖(((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) + (i : ℂ)‖)
          * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) := by rw [hrec]
    _ ≤ C₀ * τ ^ (-δ) * ((K * τ) ^ n
          * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) := by
        have hnn : (0 : ℝ) ≤ C₀ * τ ^ (-δ) := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hnn
        exact mul_le_mul_of_nonneg_right hP hGpos.le
    _ = C₀ * K ^ n * τ ^ (1 / 2 - σ)
          * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
        rw [show C₀ * τ ^ (-δ) * ((K * τ) ^ n
              * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖)
            = C₀ * (τ ^ (-δ) * ((K * τ) ^ n))
              * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ from by ring, hexp]
        ring

/-- **Titchmarsh's sharp bound for `χ` on a fixed vertical line left of the critical line.** -/
theorem exists_norm_zetaChi_line_le {σ : ℝ} (hσ : σ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * |t| ^ (1 / 2 - σ) := by
  obtain ⟨C₁, hC₁, hbnd⟩ := exists_norm_Gamma_quotient_line hσ
  refine ⟨Real.pi ^ (σ - 1 / 2) * C₁ * 2 ^ (σ - 1 / 2), by positivity, ?_⟩
  intro t ht
  have htne : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsim : s.im ≠ 0 := by
    have : s.im = t := by rw [hs]; simp
    rw [this]
    exact htne
  have hsre : s.re = σ := by rw [hs]; simp
  set τ : ℝ := |t| / 2 with hτdef
  have hτ : 1 ≤ τ := by rw [hτdef]; linarith
  have hτ0 : 0 < τ := by linarith
  have h1 : ‖Complex.Gamma ((1 - s) / 2)‖
      = ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hpt : (1 - s) / 2 = (((1 - σ) / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [hpt, norm_Gamma_line_abs]
    congr 2
    rw [hτdef, abs_div, abs_neg]
    norm_num
  have h2 : ‖Complex.Gamma (s / 2)‖
      = ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ := by
    have hpt : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [hpt, norm_Gamma_line_abs]
    congr 2
    rw [hτdef, abs_div]
    norm_num
  have hGpos : 0 < ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (gammaArg_Gamma_ne_zero hτ0 (σ / 2))
  rw [norm_zetaChi_eq_mul_inv hsim, hsre, norm_inv, h1, h2]
  have hratio : ‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
      * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖⁻¹ ≤ C₁ * τ ^ (1 / 2 - σ) := by
    rw [← div_eq_mul_inv, div_le_iff₀ hGpos]
    exact hbnd τ hτ
  have hpipos : (0 : ℝ) < Real.pi ^ (σ - 1 / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hstep : Real.pi ^ (σ - 1 / 2)
      * (‖Complex.Gamma ((((1 - σ) / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        * ‖Complex.Gamma (((σ / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖⁻¹)
      ≤ Real.pi ^ (σ - 1 / 2) * (C₁ * τ ^ (1 / 2 - σ)) :=
    mul_le_mul_of_nonneg_left hratio hpipos.le
  refine hstep.trans (le_of_eq ?_)
  have htpos : (0 : ℝ) < |t| := by linarith
  have hdiv : τ ^ (1 / 2 - σ) = |t| ^ (1 / 2 - σ) * 2 ^ (σ - 1 / 2) := by
    rw [hτdef, Real.div_rpow htpos.le (by norm_num)]
    rw [div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [hdiv]
  ring

end RHTower

end
