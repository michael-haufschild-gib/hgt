import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheTransportOfAZeroIsEffective
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound
import GaloisForLFunctions.PrimeTorusTheory.TheMisalignmentBand
import GaloisForLFunctions.RHTower.BurnolSoninEvaluationNonvanishing
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The slow return bound lives right of the line

Transport of a zero `ρ = β + iγ` along shifts `τ` needs a bound for `ζ(s + iτ)` on a disc about `3 + iγ` that reaches `ρ`. Such a bound is
only possible on discs that stay right of the critical line.

* **Left of `Re s = 0`, `ζ` is a power of the height** (`exists_mul_rpow_le_norm_zeta_left`). By the functional equation,
  `|ζ(−η + it)| ≥ c t^{½+η}` for `0 < η ≤ 1`, `t ≥ 1`. The cosine cancels the decay of `Γ`, and `|ζ(1 + η − it)|` is bounded below.
  At the left edge `−1/10` of the disc of radius `31/10` this is `c t^{3/5}`.
* **Left of `½`, the reflection is small** (`exists_norm_zeta_le_reflect`). For `½ ≤ u < 1`, `|ζ(u + it)| ≤ C t^{½−u} |ζ(1 − u + it)|`.
* **Smallness propagates along a chain of three-circle steps** (`norm_le_of_chain`). A disc about `3 + iγ` of radius `R > 5/2` contains a pair
  `1 − u + iy`, `u + iy` with `u > ½`, so a bound `M` on the disc makes `ζ(· + iτ)` of size `≤ τ^{−δ} M` near `u + iγ`. The chain carries this to
  `Re s = 2`, where `|ζ| ≥ ½`. Hence **`M ≥ c τ^b`** (`exists_rpow_le_of_norm_le_on_disc`), with `b, c > 0` depending only on the disc.
* **An aligned length is polylogarithmic in the height.** A head return up to `N ≥ 11` at `τ ≥ 1` has `N < τ + 1` (`lt_add_one_of_isHeadReturn`).
  At large `τ`, non-alignment gives `N < 1024 (log τ)⁴ (log log τ)²` (`length_lt_of_isHeadReturn`). Hence `N^A` is below every power of `τ`.
* **Consequences.** On every disc of radius `R > 5/2` the bound `|ζ(s + iτ)| ≤ N^A` fails at every long head return, for every exponent `A`
  (`exists_large_value_of_left_edge_lt_half`); on the disc of radius `31/10` the witness is the left edge (`exists_large_value_left`). The
  hypothesis of `asymptoticAbscissaLaw_of_slowReturns` therefore holds exactly when no zero lies right of `½`
  (`slowReturnHypothesis_iff_riemannHypothesis`). Along a phase return, every connected domain of bounded translates that meets `Re s > 1` lies in
  `Re s > ½` (`IsPhaseReturn.re_gt_half_of_translatesBoundedOn`).
* **Transport survives on discs short of the line** (`transport_of_isHeadReturn_on_disc`). For `3 − β < R ≤ 31/10` the explicit exponent
  `transportExponent β R > 0` works. With `R = 3 − σ₀`, `½ ≤ σ₀ < β`, slow aligned returns at each right zero give the asymptotic abscissa law
  (`asymptoticAbscissaLaw_of_slowReturns_right`).
-/

open Complex Filter Topology Metric Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-! ### The cosine and the reflection -/

/-- The cosine on a vertical line is exponentially large in the height. -/
theorem sub_exp_le_two_mul_norm_cos (z : ℂ) :
    Real.exp |z.im| - Real.exp (-|z.im|) ≤ 2 * ‖cos z‖ := by
  have h2 : (2 : ℂ) * cos z = exp (z * I) + exp (-z * I) := by
    rw [Complex.cos]
    ring
  have hnorm : 2 * ‖cos z‖ = ‖exp (z * I) + exp (-z * I)‖ := by
    rw [← h2, norm_mul]
    simp
  have h1 : ‖exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    simp
  have h3 : ‖exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm]
  have hrev := abs_norm_sub_norm_le (exp (-z * I)) (-exp (z * I))
  rw [norm_neg, sub_neg_eq_add, add_comm] at hrev
  refine le_trans ?_ hrev
  rw [h1, h3]
  rcases abs_cases z.im with ⟨ha, _⟩ | ⟨ha, _⟩
  · rw [ha]
    exact le_abs_self _
  · rw [ha, neg_neg]
    rw [abs_sub_comm]
    exact le_abs_self _

/-- `|cos(π s/2)| ≥ e^{π|t|/2}/4` once `|Im s| = |t| ≥ 1`. -/
theorem exp_div_four_le_norm_cos {s : ℂ} (ht : 1 ≤ |s.im|) :
    Real.exp (Real.pi * |s.im| / 2) / 4 ≤ ‖cos ((Real.pi : ℂ) * s / 2)‖ := by
  have h3 := sub_exp_le_two_mul_norm_cos ((Real.pi : ℂ) * s / 2)
  have him : ((Real.pi : ℂ) * s / 2).im = Real.pi / 2 * s.im := by
    have : (Real.pi : ℂ) * s / 2 = ((Real.pi / 2 : ℝ) : ℂ) * s := by
      push_cast
      ring
    rw [this, Complex.im_ofReal_mul]
  have hab : |((Real.pi : ℂ) * s / 2).im| = Real.pi * |s.im| / 2 := by
    rw [him, abs_mul, abs_of_pos (by positivity)]
    ring
  rw [hab, Real.exp_neg] at h3
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (Real.pi * |s.im| / 2) := ⟨_, rfl⟩
  rw [← hE] at h3 ⊢
  have hEpos : 0 < E := hE ▸ Real.exp_pos _
  have hE2 : 2 ≤ E := by
    rw [hE]
    have h5 : (1 : ℝ) ≤ Real.pi * |s.im| / 2 := by
      have := Real.pi_gt_three
      nlinarith
    have h6 := Real.add_one_le_exp (Real.pi * |s.im| / 2)
    linarith
  have hsmall : E⁻¹ ≤ E / 2 := by
    rw [inv_le_iff_one_le_mul₀ hEpos]
    nlinarith
  linarith

/-- **Left of `Re s = 0` the size of `ζ` is a power of the height.** For `0 < η ≤ 1` and `t ≥ 1`, `|ζ(−η + it)| ≥ c t^{½+η}`. -/
theorem exists_mul_rpow_le_norm_zeta_left {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ (1 / 2 + η) ≤ ‖riemannZeta (((-η : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C, hC, hG⟩ := HTGeometry.exists_norm_inv_Gamma_le_sharp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 1 + 1 / η := ⟨_, rfl⟩
  have hZpos : 0 < Z := by rw [hZ]; positivity
  refine ⟨(2 * Real.pi) ^ (-(1 + η)) / (2 * C) * Z⁻¹, by positivity, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (Real.pi * t / 2) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = t ^ (1 / 2 + η) := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos ht0 _
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = ((1 + η : ℝ) : ℂ) - (t : ℂ) * I := ⟨_, rfl⟩
  have hsre : s.re = 1 + η := by simp [hs]
  have hsim : s.im = -t := by simp [hs]
  have hflip : (1 : ℂ) - s = ((-η : ℝ) : ℂ) + (t : ℂ) * I := by
    rw [hs]
    push_cast
    ring
  have hnat : ∀ n : ℕ, s ≠ -(n : ℂ) := by
    intro n h
    have h3 := congrArg Complex.re h
    rw [hsre] at h3
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at h3
    linarith
  have hne1 : s ≠ 1 := by
    intro h
    have h3 := congrArg Complex.im h
    rw [hsim] at h3
    simp at h3
    linarith
  have hfe := riemannZeta_one_sub hnat hne1
  rw [hflip] at hfe
  -- The Gamma factor, through `Γ(u + 1) = u Γ(u)` at `u = η + it`.
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = (η : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hure : u.re = η := by simp [hu]
  have huim : u.im = t := by simp [hu]
  have hune : u ≠ 0 := by
    intro h
    rw [h] at hure
    simp at hure
    linarith
  have hsconj : s = (starRingEnd ℂ) (u + 1) := by
    apply Complex.ext
    · simp [hsre, hure]
      ring
    · simp [hsim, huim]
  have hGamma : ‖Complex.Gamma s‖ = ‖u‖ * ‖Complex.Gamma u‖ := by
    rw [hsconj, Complex.Gamma_conj, Complex.norm_conj, Complex.Gamma_add_one u hune, norm_mul]
  have hGu0 : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hure]; exact hη0)
  have hGupos : 0 < ‖Complex.Gamma u‖ := norm_pos_iff.mpr hGu0
  have hGinv := hG η t hη0.le hη1 (by rwa [abs_of_pos ht0])
  rw [abs_of_pos ht0, ← hu, norm_inv, ← hE] at hGinv
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = t ^ (1 / 2 - η) := ⟨_, rfl⟩
  rw [← hQ] at hGinv
  have hQpos : 0 < Q := by rw [hQ]; exact Real.rpow_pos_of_pos ht0 _
  have hGlow : (C * Q * E)⁻¹ ≤ ‖Complex.Gamma u‖ := by
    rw [← inv_inv ‖Complex.Gamma u‖]
    exact inv_anti₀ (inv_pos.mpr hGupos) hGinv
  have hut : t ≤ ‖u‖ := by
    have := Complex.abs_im_le_norm u
    rwa [huim, abs_of_pos ht0] at this
  have hpowmul : P * Q = t := by
    rw [hP, hQ, ← Real.rpow_add ht0]
    have : (1 / 2 + η) + (1 / 2 - η) = 1 := by ring
    rw [this, Real.rpow_one]
  have hGs : P / (C * E) ≤ ‖Complex.Gamma s‖ := by
    rw [hGamma]
    have hstep : P / (C * E) = t * (C * Q * E)⁻¹ := by
      rw [← hpowmul]
      field_simp
    rw [hstep]
    exact mul_le_mul hut hGlow (by positivity) (norm_nonneg _)
  -- The cosine.
  have hcos : E / 4 ≤ ‖cos ((Real.pi : ℂ) * s / 2)‖ := by
    have habs : |s.im| = t := by rw [hsim, abs_neg, abs_of_pos ht0]
    have h3 := exp_div_four_le_norm_cos (s := s) (by rw [habs]; exact ht)
    rwa [habs, ← hE] at h3
  -- The value of `ζ` right of `1`.
  have hzeta : Z⁻¹ ≤ ‖riemannZeta s‖ := by
    have h3 := RHTower.norm_inv_riemannZeta_le_of_le_re (σ₁ := 1 + η) (by linarith) (s := s) (by rw [hsre])
    have h1re : (1 : ℝ) + η - 1 = η := by ring
    rw [h1re, ← hZ, norm_inv] at h3
    have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; linarith)
    have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hne
    rw [← inv_inv ‖riemannZeta s‖]
    exact inv_anti₀ (inv_pos.mpr hpos) h3
  have hcpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ = (2 * Real.pi) ^ (-(1 + η)) := by
    have h3 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h3, Complex.norm_cpow_eq_rpow_re_of_pos h2pi, Complex.neg_re, hsre]
  rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul, hcpow, Complex.norm_two, ← hP]
  have hprod : (P / (C * E)) * (E / 4) ≤ ‖Complex.Gamma s‖ * ‖cos ((Real.pi : ℂ) * s / 2)‖ :=
    mul_le_mul hGs hcos (by positivity) (norm_nonneg _)
  have hrw : (P / (C * E)) * (E / 4) = P / (4 * C) := by
    field_simp
  rw [hrw] at hprod
  have hpow : 0 < (2 * Real.pi) ^ (-(1 + η)) := Real.rpow_pos_of_pos h2pi _
  calc (2 * Real.pi) ^ (-(1 + η)) / (2 * C) * Z⁻¹ * P
      = 2 * (2 * Real.pi) ^ (-(1 + η)) * (P / (4 * C)) * Z⁻¹ := by
        field_simp
        ring
    _ ≤ 2 * (2 * Real.pi) ^ (-(1 + η)) * (‖Complex.Gamma s‖ * ‖cos ((Real.pi : ℂ) * s / 2)‖) * ‖riemannZeta s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hprod (by positivity)) hzeta (by positivity) (by positivity)
    _ = _ := by ring

/-- At the left edge `Re s = −1/10` of the disc of radius `31/10` about `3 + iγ`: `|ζ(−1/10 + it)| ≥ c t^{3/5}`. -/
theorem exists_mul_rpow_three_fifths_le_norm_zeta :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      c * t ^ (3 / 5 : ℝ) ≤ ‖riemannZeta (((-(1 / 10) : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨c, hc, h⟩ := exists_mul_rpow_le_norm_zeta_left (η := 1 / 10) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun t ht => ?_⟩
  have h3 : (1 / 2 + 1 / 10 : ℝ) = 3 / 5 := by norm_num
  have h4 := h t ht
  rwa [h3] at h4

/-- **The reflection is small left of `½`.** For `½ ≤ u < 1` and `t ≥ 1`, `|ζ(u + it)| ≤ C t^{½−u} |ζ(1 − u + it)|`. -/
theorem exists_norm_zeta_le_reflect :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u t : ℝ, 1 / 2 ≤ u → u < 1 → 1 ≤ t →
      ‖riemannZeta ((u : ℂ) + (t : ℂ) * I)‖ ≤
        C * t ^ (1 / 2 - u) * ‖riemannZeta (((1 - u : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C₀, hC₀, hG⟩ := HTGeometry.exists_norm_inv_Gamma_le_sharp
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have h2pi0 : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨1 + 4 * Real.pi * C₀, by nlinarith [mul_pos hpi hC₀], fun u t hu hu1 ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hu0 : 0 < u := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (u : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hwre : w.re = u := by simp [hw]
  have hwim : w.im = t := by simp [hw]
  have hnat : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n h
    have h3 := congrArg Complex.re h
    rw [hwre] at h3
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp at h3
    linarith
  have hne1 : w ≠ 1 := by
    intro h
    have h3 := congrArg Complex.im h
    rw [hwim] at h3
    simp at h3
    linarith
  have hfe := riemannZeta_one_sub hnat hne1
  obtain ⟨y, hy⟩ : ∃ y : ℂ, y = ((1 - u : ℝ) : ℂ) + (t : ℂ) * I := ⟨_, rfl⟩
  have hyre : y.re = 1 - u := by simp [hy]
  have hyim : y.im = t := by simp [hy]
  have hyne : y ≠ 1 := by
    intro h
    have h3 := congrArg Complex.im h
    rw [hyim] at h3
    simp at h3
    linarith
  have hconj : (1 : ℂ) - w = (starRingEnd ℂ) y := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, hwre, Complex.conj_re, hyre]
    · rw [Complex.sub_im, Complex.one_im, hwim, Complex.conj_im, hyim]
      ring
  have hnorm : ‖riemannZeta (1 - w)‖ = ‖riemannZeta y‖ := by
    rw [hconj, RHTower.riemannZeta_conj_of_re_pos (by rw [hyre]; linarith) hyne, Complex.norm_conj]
  rw [← hw, ← hy, ← hnorm, hfe, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_two]
  -- Lower bounds for the three factors.
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (Real.pi * t / 2) := ⟨_, rfl⟩
  have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = t ^ (1 / 2 - u) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQ]; exact Real.rpow_pos_of_pos ht0 _
  rw [← hQ]
  have hGinv := hG u t hu0.le hu1.le (by rwa [abs_of_pos ht0])
  rw [abs_of_pos ht0, ← hw, norm_inv, ← hE, ← hQ] at hGinv
  have hGu0 : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hwre]; exact hu0)
  have hGupos : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.mpr hGu0
  have hGlow : (C₀ * Q * E)⁻¹ ≤ ‖Complex.Gamma w‖ := by
    rw [← inv_inv ‖Complex.Gamma w‖]
    exact inv_anti₀ (inv_pos.mpr hGupos) hGinv
  have hcos : E / 4 ≤ ‖cos ((Real.pi : ℂ) * w / 2)‖ := by
    have habs : |w.im| = t := by rw [hwim, abs_of_pos ht0]
    have h3 := exp_div_four_le_norm_cos (s := w) (by rw [habs]; exact ht)
    rwa [habs, ← hE] at h3
  have hcpow : (2 * Real.pi)⁻¹ ≤ ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ := by
    have h3 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [h3, Complex.norm_cpow_eq_rpow_re_of_pos h2pi0, Complex.neg_re, hwre, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le h2pi (by linarith)
  obtain ⟨a, ha⟩ : ∃ a, a = ‖riemannZeta w‖ := ⟨_, rfl⟩
  rw [← ha]
  have ha0 : 0 ≤ a := ha ▸ norm_nonneg _
  have hkey : a / (4 * Real.pi * C₀ * Q) ≤
      2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖cos ((Real.pi : ℂ) * w / 2)‖ * a := by
    calc a / (4 * Real.pi * C₀ * Q) = 2 * (2 * Real.pi)⁻¹ * (C₀ * Q * E)⁻¹ * (E / 4) * a := by
          field_simp
      _ ≤ 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖cos ((Real.pi : ℂ) * w / 2)‖ * a := by
          refine mul_le_mul_of_nonneg_right ?_ ha0
          refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcpow (by norm_num)) hGlow
            (by positivity) (by positivity)) hcos (by positivity) (by positivity)
  have hden : 0 < 4 * Real.pi * C₀ * Q := by positivity
  rw [div_le_iff₀ hden] at hkey
  have hQa : 0 ≤ Q * a := mul_nonneg hQpos.le ha0
  nlinarith [mul_nonneg hQa (norm_nonneg (riemannZeta (1 - w)))]

/-! ### Propagation of smallness -/

/-- **One three-circle step.** If `g` is bounded by `M` on the disc of radius `4ρ` about `q` and by `m ≤ M` on the disc of radius `ρ`, then it is
bounded by `√(mM)` on the disc of radius `2ρ`. -/
theorem norm_le_geomMean_step {g : ℂ → ℂ} {q : ℂ} {ρ m M : ℝ} (hρ : 0 < ρ) (hm : 0 < m) (hmM : m ≤ M)
    (hd : ∀ w, ‖w - q‖ ≤ 4 * ρ → DifferentiableAt ℂ g w)
    (hM : ∀ w, ‖w - q‖ ≤ 4 * ρ → ‖g w‖ ≤ M)
    (hsmall : ∀ w, ‖w - q‖ ≤ ρ → ‖g w‖ ≤ m) {w : ℂ} (hw : ‖w - q‖ ≤ 2 * ρ) :
    ‖g w‖ ≤ m ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) := by
  by_cases hin : ‖w - q‖ ≤ ρ
  · have h1 := hsmall w hin
    have h2 : m ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) = m := by
      rw [← Real.rpow_add hm]
      norm_num
    have h3 : m ^ (1 / 2 : ℝ) ≤ M ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hm.le hmM (by norm_num)
    have h4 : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm _
    nlinarith
  · push Not at hin
    obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun y => g (y + q) := ⟨_, rfl⟩
    have hdf : ∀ y : ℂ, ρ ≤ ‖y‖ → ‖y‖ ≤ 4 * ρ → DifferentiableAt ℂ f y := by
      intro y _ hy
      have hy' : ‖(y + q) - q‖ ≤ 4 * ρ := by rwa [add_sub_cancel_right]
      rw [hf]
      exact (hd _ hy').comp y (differentiableAt_id.add_const q)
    have h1' : ∀ y : ℂ, ‖y‖ = ρ → ‖f y‖ ≤ m := by
      intro y hy
      rw [hf]
      show ‖g (y + q)‖ ≤ m
      exact hsmall _ (by rw [add_sub_cancel_right, hy])
    have h3' : ∀ y : ℂ, ‖y‖ = 4 * ρ → ‖f y‖ ≤ M := by
      intro y hy
      rw [hf]
      show ‖g (y + q)‖ ≤ M
      exact hM _ (by rw [add_sub_cancel_right, hy])
    have hthree := HTGeometry.norm_le_of_three_circles (f := f) (z := w - q) hρ (by linarith) hdf h1' h3'
      hin.le (by linarith)
    have hfw : f (w - q) = g w := by
      rw [hf]
      show g (w - q + q) = g w
      rw [sub_add_cancel]
    rw [hfw] at hthree
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h4 : Real.log (4 * ρ) - Real.log ρ = 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num) hρ.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have hs : (Real.log ‖w - q‖ - Real.log ρ) / (Real.log (4 * ρ) - Real.log ρ) ≤ 1 / 2 := by
      rw [h4, div_le_iff₀ (by positivity)]
      have h5 : Real.log ‖w - q‖ ≤ Real.log (2 * ρ) := Real.log_le_log (by linarith) hw
      rw [Real.log_mul (by norm_num) hρ.ne'] at h5
      linarith
    have hi := interp_mono hm hmM hs
    have h6 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [h6] at hi
    exact hthree.trans hi

/-- **A chain of three-circle steps.** Along centres `q k` a distance `≤ ρ` apart, with `g` holomorphic and bounded by `M` on the discs of radius
`4ρ`, a bound `aM` on the first disc of radius `ρ` becomes `a^{2^{-k}} M` on the `k`-th. -/
theorem norm_le_of_chain {g : ℂ → ℂ} {q : ℕ → ℂ} {ρ a M : ℝ} (hρ : 0 < ρ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hMpos : 0 < M) {K : ℕ} (hstep : ∀ k, ‖q (k + 1) - q k‖ ≤ ρ)
    (hd : ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ 4 * ρ → DifferentiableAt ℂ g w)
    (hM : ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ 4 * ρ → ‖g w‖ ≤ M)
    (hsmall : ∀ w, ‖w - q 0‖ ≤ ρ → ‖g w‖ ≤ a * M) :
    ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ ρ → ‖g w‖ ≤ a ^ ((1 / 2 : ℝ) ^ k) * M := by
  intro k
  induction k with
  | zero =>
    intro _ w hw
    simpa using hsmall w hw
  | succ k ih =>
    intro hk w hw
    have hkK : k ≤ K := by omega
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (1 / 2 : ℝ) ^ k := ⟨_, rfl⟩
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hih := ih hkK
    rw [← hθ] at hih
    have haθ : 0 < a ^ θ := Real.rpow_pos_of_pos ha _
    have haθ1 : a ^ θ ≤ 1 := Real.rpow_le_one ha.le ha1 hθ0
    have hstepw : ‖w - q k‖ ≤ 2 * ρ := by
      have h2 : w - q k = (w - q (k + 1)) + (q (k + 1) - q k) := by ring
      rw [h2]
      exact (norm_add_le _ _).trans (by linarith [hstep k])
    have h3 := norm_le_geomMean_step hρ (mul_pos haθ hMpos) (mul_le_of_le_one_left hMpos.le haθ1)
      (hd k hkK) (hM k hkK) hih hstepw
    have hval : (a ^ θ * M) ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) = a ^ ((1 / 2 : ℝ) ^ (k + 1)) * M := by
      rw [Real.mul_rpow haθ.le hMpos.le, mul_assoc, ← Real.rpow_add hMpos, ← Real.rpow_mul ha.le, pow_succ, ← hθ]
      norm_num
    rw [hval] at h3
    exact h3

/-- `|ζ(s)| ≥ ½` for `Re s ≥ 2`. -/
theorem half_le_norm_zeta {s : ℂ} (hs : 2 ≤ s.re) : 1 / 2 ≤ ‖riemannZeta s‖ := by
  have h := RHTower.norm_inv_riemannZeta_le_of_le_re (σ₁ := 2) (by norm_num) hs
  have hne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr hne
  have h2 : ‖riemannZeta s‖⁻¹ ≤ 2 := by
    rw [← norm_inv]
    exact h.trans (by norm_num)
  rw [one_div]
  exact (inv_le_comm₀ hpos two_pos).mp h2

/-- **A disc crossing the critical line sees a power of the height.** For `R > 5/2` and `γ ≥ 0` there are `c, b > 0` and `H` such that, for
`τ ≥ H`, a bound `|ζ(s + iτ)| ≤ M` on the closed disc of radius `R` about `3 + iγ` forces `M ≥ c τ^b`. The disc contains a pair `1 − u + iy`,
`u + iy` with `u > ½`; reflection makes `ζ(· + iτ)` of size `≤ C τ^{−δ} M` on a small disc about `u + iγ`, and a chain of three-circle steps
carries this to `Re s = 2`, where `|ζ| ≥ ½`. -/
theorem exists_rpow_le_of_norm_le_on_disc {R : ℝ} (hR : 5 / 2 < R) {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ c b H : ℝ, 0 < c ∧ 0 < b ∧ ∀ τ : ℝ, H ≤ τ → ∀ M : ℝ,
      (∀ s ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) R, ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ M) →
      c * τ ^ b ≤ M := by
  obtain ⟨C, hC1, hrefl⟩ := exists_norm_zeta_le_reflect
  have hC0 : 0 < C := by linarith
  obtain ⟨d, hd⟩ : ∃ d, d = min R 3 - 5 / 2 := ⟨_, rfl⟩
  have hd0 : 0 < d := by
    have : 5 / 2 < min R 3 := lt_min hR (by norm_num)
    rw [hd]
    linarith
  have hd12 : d ≤ 1 / 2 := by
    have := min_le_right R 3
    rw [hd]
    linarith
  have hdR : 5 / 2 + d ≤ R := by
    have := min_le_left R 3
    rw [hd]
    linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = d / 8 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : ℝ, u₀ = 1 / 2 + d / 2 := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 3 * d / 8 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  have hu2 : 0 < 2 - u₀ := by rw [hu₀]; linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈(2 - u₀) / ρ⌉₊ := ⟨_, rfl⟩
  have hKlow : 2 - u₀ ≤ K * ρ := by
    have h2 := Nat.le_ceil ((2 - u₀) / ρ)
    rw [← hK, div_le_iff₀ hρ] at h2
    exact h2
  have hKhigh : K * ρ < 2 - u₀ + ρ := by
    have h2 := Nat.ceil_lt_add_one (div_pos hu2 hρ).le
    rw [← hK] at h2
    have h3 : (K : ℝ) * ρ < ((2 - u₀) / ρ + 1) * ρ := mul_lt_mul_of_pos_right h2 hρ
    have h4 : ((2 - u₀) / ρ + 1) * ρ = 2 - u₀ + ρ := by
      rw [add_mul, div_mul_cancel₀ _ hρ.ne', one_mul]
    linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = (1 / 2 : ℝ) ^ K := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; positivity
  have hθ1 : θ ≤ 1 := by rw [hθdef]; exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨b, hb⟩ : ∃ b, b = δ * θ := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  have hb1 : b ≤ 1 := by rw [hb]; nlinarith
  refine ⟨1 / (8 * C), b, max 3 (2 * C ^ (1 / δ)), by positivity, hb0, fun τ hτH M hM => ?_⟩
  have hτ3 : 3 ≤ τ := (le_max_left _ _).trans hτH
  have hτC : 2 * C ^ (1 / δ) ≤ τ := (le_max_right _ _).trans hτH
  have hτpos : 0 < τ := by linarith
  obtain ⟨X, hX⟩ : ∃ X, X = τ / 2 := ⟨_, rfl⟩
  have hXpos : 0 < X := by rw [hX]; positivity
  have hX1 : 1 ≤ X := by rw [hX]; linarith
  have hXδ : 0 < X ^ δ := Real.rpow_pos_of_pos hXpos _
  have hXC : C ≤ X ^ δ := by
    have h1 : C ^ (1 / δ) ≤ X := by rw [hX]; linarith
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg hC0.le _) h1 hδ.le
    rwa [← Real.rpow_mul hC0.le, one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one] at h2
  obtain ⟨a, ha⟩ : ∃ a, a = C * X ^ (-δ) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact mul_pos hC0 (Real.rpow_pos_of_pos hXpos _)
  have ha1 : a ≤ 1 := by
    rw [ha, Real.rpow_neg hXpos.le, ← div_eq_mul_inv, div_le_one hXδ]
    exact hXC
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℂ, c₀ = (3 : ℂ) + (γ : ℂ) * I := ⟨_, rfl⟩
  rw [← hc₀] at hM
  -- `M ≥ ½` from the centre.
  have hMpos : 0 < M := by
    have h2 := hM c₀ (mem_closedBall_self (by linarith))
    have h3 : (c₀ + (τ : ℂ) * I).re = 3 := by rw [hc₀]; simp
    have h4 := half_le_norm_zeta (s := c₀ + (τ : ℂ) * I) (by rw [h3]; norm_num)
    linarith
  -- The chain of centres `u₀ + kρ + iγ`.
  obtain ⟨q, hq⟩ : ∃ q : ℕ → ℂ, q = fun k : ℕ => ((u₀ + k * ρ : ℝ) : ℂ) + (γ : ℂ) * I := ⟨_, rfl⟩
  have hqk : ∀ k, q k = ((u₀ + k * ρ : ℝ) : ℂ) + (γ : ℂ) * I := fun k => by rw [hq]
  have hstep : ∀ k, ‖q (k + 1) - q k‖ ≤ ρ := by
    intro k
    have h2 : q (k + 1) - q k = ((ρ : ℝ) : ℂ) := by
      rw [hqk, hqk]
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_of_pos hρ).le
  have hqc : ∀ k ≤ K, ‖q k - c₀‖ = 3 - u₀ - k * ρ := by
    intro k hk
    have h2 : q k - c₀ = ((u₀ + k * ρ - 3 : ℝ) : ℂ) := by
      rw [hqk, hc₀]
      push_cast
      ring
    have hkR : (k : ℝ) * ρ ≤ K * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hρ.le
    rw [h2, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have hin : ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ 4 * ρ → w ∈ closedBall c₀ R := by
    intro k hk w hw
    rw [mem_closedBall, dist_eq_norm]
    have h2 : w - c₀ = (w - q k) + (q k - c₀) := by ring
    rw [h2]
    refine (norm_add_le _ _).trans ?_
    have h3 := hqc k hk
    have h4 : (0 : ℝ) ≤ k * ρ := by positivity
    linarith
  have him : ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ 4 * ρ → 0 < (w + (τ : ℂ) * I).im := by
    intro k _ w hw
    have h2 := (abs_le.mp ((Complex.abs_im_le_norm (w - q k)).trans hw)).1
    have h3 : (q k).im = γ := by rw [hqk]; simp
    rw [Complex.sub_im, h3] at h2
    have h4 : (w + (τ : ℂ) * I).im = w.im + τ := by simp
    rw [h4]
    linarith
  have hdiff : ∀ k ≤ K, ∀ w, ‖w - q k‖ ≤ 4 * ρ →
      DifferentiableAt ℂ (fun w : ℂ => riemannZeta (w + (τ : ℂ) * I)) w := by
    intro k hk w hw
    have hne : w + (τ : ℂ) * I ≠ 1 := by
      intro h1
      have h2 := him k hk w hw
      rw [h1] at h2
      simp at h2
    exact (differentiableAt_riemannZeta hne).comp w (differentiableAt_id.add_const _)
  -- Smallness on the first disc, by reflection.
  have hsmall : ∀ w, ‖w - q 0‖ ≤ ρ → ‖riemannZeta (w + (τ : ℂ) * I)‖ ≤ a * M := by
    intro w hw
    have hq0re : (q 0).re = u₀ := by rw [hqk]; simp
    have hq0im : (q 0).im = γ := by rw [hqk]; simp
    have hre := abs_le.mp ((Complex.abs_re_le_norm (w - q 0)).trans hw)
    have him' := abs_le.mp ((Complex.abs_im_le_norm (w - q 0)).trans hw)
    rw [Complex.sub_re, hq0re] at hre
    rw [Complex.sub_im, hq0im] at him'
    obtain ⟨u, hu⟩ : ∃ u, u = w.re := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = w.im := ⟨_, rfl⟩
    rw [← hu] at hre
    rw [← hy] at him'
    obtain ⟨hre1, hre2⟩ := hre
    obtain ⟨him1, him2⟩ := him'
    obtain ⟨t, ht⟩ : ∃ t, t = y + τ := ⟨_, rfl⟩
    have ht2 : X ≤ t := by
      rw [hX, ht]
      linarith
    have ht1 : 1 ≤ t := hX1.trans ht2
    have hu12 : 1 / 2 + δ ≤ u := by
      rw [hδdef]
      linarith
    have hu1 : u < 1 := by linarith
    have hw' : w + (τ : ℂ) * I = (u : ℂ) + (t : ℂ) * I := by
      apply Complex.ext
      · simp [hu]
      · simp [ht, hy]
    rw [hw']
    have h1 := hrefl u t (by linarith) hu1 ht1
    have hmem : ((1 - u : ℝ) : ℂ) + (y : ℂ) * I ∈ closedBall c₀ R := by
      rw [mem_closedBall, dist_eq_norm]
      have h2 : ((1 - u : ℝ) : ℂ) + (y : ℂ) * I - c₀ = ((-(2 + u) : ℝ) : ℂ) + ((y - γ : ℝ) : ℂ) * I := by
        rw [hc₀]
        push_cast
        ring
      rw [h2]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 + u)]
      have h3 := abs_le.mpr ⟨him1, him2⟩
      linarith
    have h2 := hM _ hmem
    have hsum : ((1 - u : ℝ) : ℂ) + (y : ℂ) * I + (τ : ℂ) * I = ((1 - u : ℝ) : ℂ) + (t : ℂ) * I := by
      rw [ht]
      push_cast
      ring
    rw [hsum] at h2
    have hpow : t ^ (1 / 2 - u) ≤ X ^ (-δ) := by
      calc t ^ (1 / 2 - u) ≤ t ^ (-δ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
        _ ≤ X ^ (-δ) := by
          rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ t), Real.rpow_neg hXpos.le]
          exact inv_anti₀ hXδ (Real.rpow_le_rpow hXpos.le ht2 hδ.le)
    calc ‖riemannZeta ((u : ℂ) + (t : ℂ) * I)‖
        ≤ C * t ^ (1 / 2 - u) * ‖riemannZeta (((1 - u : ℝ) : ℂ) + (t : ℂ) * I)‖ := h1
      _ ≤ C * X ^ (-δ) * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hC0.le) h2 (norm_nonneg _)
            (mul_pos hC0 (Real.rpow_pos_of_pos hXpos _)).le
      _ = a * M := by rw [ha]
  -- The end of the chain sits at `Re s ≥ 2`.
  have hchain : ‖riemannZeta (q K + (τ : ℂ) * I)‖ ≤ a ^ θ * M := by
    rw [hθdef]
    exact norm_le_of_chain (g := fun w : ℂ => riemannZeta (w + (τ : ℂ) * I)) (q := q) hρ ha0 ha1 hMpos
      hstep hdiff (fun k hk w hw => hM w (hin k hk w hw)) hsmall K le_rfl (q K)
      (by rw [sub_self, norm_zero]; exact hρ.le)
  have hre : 2 ≤ (q K + (τ : ℂ) * I).re := by
    have h2 : (q K + (τ : ℂ) * I).re = u₀ + K * ρ := by rw [hqk]; simp
    rw [h2]
    linarith
  have hlow : (1 / 2 : ℝ) ≤ a ^ θ * M := (half_le_norm_zeta hre).trans hchain
  have haθ : a ^ θ ≤ C * X ^ (-b) := by
    rw [ha, Real.mul_rpow hC0.le (Real.rpow_nonneg hXpos.le _), ← Real.rpow_mul hXpos.le]
    have h5 : C ^ θ ≤ C := by
      calc C ^ θ ≤ C ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 hθ1
        _ = C := Real.rpow_one C
    have h6 : -δ * θ = -b := by rw [hb]; ring
    rw [h6]
    exact mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hXpos.le _)
  have hXb : 0 < X ^ b := Real.rpow_pos_of_pos hXpos _
  have h7 : X ^ b / 2 ≤ C * M := by
    have h8 : 1 / 2 ≤ C * (X ^ b)⁻¹ * M := by
      calc (1 / 2 : ℝ) ≤ a ^ θ * M := hlow
        _ ≤ C * X ^ (-b) * M := mul_le_mul_of_nonneg_right haθ hMpos.le
        _ = C * (X ^ b)⁻¹ * M := by rw [Real.rpow_neg hXpos.le]
    have h9 : C * (X ^ b)⁻¹ * M = C * M / X ^ b := by
      rw [div_eq_mul_inv]
      ring
    rw [h9, le_div_iff₀ hXb] at h8
    linarith
  have hτb : τ ^ b / 2 ≤ X ^ b := by
    rw [hX, Real.div_rpow hτpos.le (by norm_num)]
    have h2b : (2 : ℝ) ^ b ≤ 2 := by
      calc (2 : ℝ) ^ b ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hb1
        _ = 2 := Real.rpow_one 2
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hτpos.le _) (by positivity) h2b
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hC0 hMpos]

/-! ### The length of an aligned return -/

/-- The phase at `n + 1` of a head return, written as an exponential. -/
private theorem norm_exp_sub_one_le_of_isHeadReturn {N : ℕ} {τ : ℝ} (h : IsHeadReturn N τ) {n : ℕ} (hn : n < N) :
    ‖exp ((-(Real.log ((n : ℝ) + 1) * τ) : ℝ) * I) - 1‖ ≤ 1 / (N : ℝ) := by
  have h1 := h n hn
  rw [phaseDefect_eq] at h1
  have h2 : -Real.log ((n : ℝ) + 1) * τ = -(Real.log ((n : ℝ) + 1) * τ) := by ring
  rwa [h2] at h1

/-- **An aligned length is below the height.** A head return up to `N ≥ 11` at `τ ≥ 1` has `N < τ + 1`: the integers `⌈τ⌉` and `⌈τ⌉ + 1` have
phases apart by an angle in `[1/3, 1]`. -/
theorem lt_add_one_of_isHeadReturn {N : ℕ} {τ : ℝ} (hN : 11 ≤ N) (hτ : 1 ≤ τ) (h : IsHeadReturn N τ) :
    (N : ℝ) < τ + 1 := by
  by_contra hcon
  push Not at hcon
  have hNR : (11 : ℝ) ≤ N := by exact_mod_cast hN
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈τ⌉₊ := ⟨_, rfl⟩
  have hmlow : τ ≤ m := hm ▸ Nat.le_ceil τ
  have hmhigh : (m : ℝ) < τ + 1 := hm ▸ Nat.ceil_lt_add_one hτ0
  have hmpos : (1 : ℝ) ≤ m := by linarith
  have hm1 : 1 ≤ m := by exact_mod_cast hmpos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hkN : k + 1 < N := by
    have : ((k + 1 : ℕ) : ℝ) < N := by linarith
    exact_mod_cast this
  have hp1 := norm_exp_sub_one_le_of_isHeadReturn h (n := k) (by omega)
  have hp2 := norm_exp_sub_one_le_of_isHeadReturn h (n := k + 1) hkN
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (k : ℝ) + 1 := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; positivity
  have hcast : ((k + 1 : ℕ) : ℝ) = a := by rw [ha]; push_cast; ring
  rw [hcast] at hmlow hmhigh hp2
  rw [← ha] at hp1
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = τ * Real.log ((a + 1) / a) := ⟨_, rfl⟩
  have hlogdiff : Real.log ((a + 1) / a) = Real.log (a + 1) - Real.log a :=
    Real.log_div (by linarith) hapos.ne'
  -- The size of the step.
  have hxpos : 0 < (a + 1) / a := by positivity
  have hup : Real.log ((a + 1) / a) ≤ 1 / a := by
    have h3 := Real.log_le_sub_one_of_pos hxpos
    have h4 : (a + 1) / a - 1 = 1 / a := by field_simp; ring
    linarith
  have hlo : 1 / (a + 1) ≤ Real.log ((a + 1) / a) := by
    have h3 := Real.one_sub_inv_le_log_of_pos hxpos
    have h4 : 1 - ((a + 1) / a)⁻¹ = 1 / (a + 1) := by field_simp; ring
    linarith
  have hθ1 : θ ≤ 1 := by
    rw [hθ]
    calc τ * Real.log ((a + 1) / a) ≤ a * (1 / a) :=
          mul_le_mul hmlow hup (by linarith [Real.log_nonneg (by rw [le_div_iff₀ hapos]; linarith : (1 : ℝ) ≤ (a + 1) / a)]) hapos.le
      _ = 1 := by field_simp
  have hθ3 : 1 / 3 ≤ θ := by
    rw [hθ]
    have h3 : τ / (a + 1) ≤ τ * Real.log ((a + 1) / a) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlo hτ0
    refine le_trans ?_ h3
    rw [le_div_iff₀ (by linarith)]
    linarith
  -- The two phases differ by `e^{−iθ}`.
  have hsplit : exp ((-(Real.log (a + 1) * τ) : ℝ) * I) - exp ((-(Real.log a * τ) : ℝ) * I) =
      exp ((-(Real.log a * τ) : ℝ) * I) * (exp (I * ((-θ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    rw [hθ, hlogdiff]
    push_cast
    ring
  have hdiff : ‖exp (I * ((-θ : ℝ) : ℂ)) - 1‖ ≤ 2 / (N : ℝ) := by
    have h3 : ‖exp ((-(Real.log a * τ) : ℝ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have h4 := congrArg norm hsplit
    rw [norm_mul, h3, one_mul] at h4
    rw [← h4]
    have h5 : exp ((-(Real.log (a + 1) * τ) : ℝ) * I) - exp ((-(Real.log a * τ) : ℝ) * I) =
        (exp ((-(Real.log (a + 1) * τ) : ℝ) * I) - 1) - (exp ((-(Real.log a * τ) : ℝ) * I) - 1) := by ring
    rw [h5]
    refine (norm_sub_le _ _).trans ?_
    have h6 : 2 / (N : ℝ) = 1 / (N : ℝ) + 1 / (N : ℝ) := by ring
    rw [h6]
    exact add_le_add hp2 hp1
  rw [Complex.norm_exp_I_mul_ofReal_sub_one] at hdiff
  have hpi3 := Real.pi_gt_three
  have hpi4 := Real.pi_lt_d2
  have hsin : θ / Real.pi ≤ Real.sin (θ / 2) := by
    have h3 := Real.mul_le_sin (x := θ / 2) (by linarith) (by linarith)
    have h4 : 2 / Real.pi * (θ / 2) = θ / Real.pi := by field_simp
    linarith
  have hsinpos : 0 ≤ Real.sin (θ / 2) := le_trans (by positivity) hsin
  have hnorm : ‖2 * Real.sin ((-θ) / 2)‖ = 2 * Real.sin (θ / 2) := by
    have h3 : (-θ) / 2 = -(θ / 2) := by ring
    rw [h3, Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hsinpos]
    norm_num
  rw [hnorm] at hdiff
  have hlow : 2 * (1 / 3 / Real.pi) ≤ 2 / (N : ℝ) := by
    refine le_trans ?_ hdiff
    have h3 : 1 / 3 / Real.pi ≤ θ / Real.pi := div_le_div_of_nonneg_right hθ3 Real.pi_pos.le
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  rw [le_div_iff₀ hNpos] at hlow
  have h7 : 2 * (1 / 3 / Real.pi) * (N : ℝ) = 2 * (N : ℝ) / (3 * Real.pi) := by
    field_simp
  rw [h7, div_le_iff₀ (by positivity)] at hlow
  nlinarith

/-- **An aligned length is polylogarithmic in the height.** At large `τ`, a head return up to `N` has `N < 1024 (log τ)⁴ (log log τ)²`:
some `n ≤ 50 (log τ)² log log τ` has its phase at least `1/(4096 (log τ)⁴ (log log τ)²)` away from `1`. -/
theorem length_lt_of_isHeadReturn :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ τ : ℝ, T₀ ≤ τ → ∀ N : ℕ, IsHeadReturn N τ →
      (N : ℝ) < 1024 * Real.log τ ^ 4 * Real.log (Real.log τ) ^ 2 := by
  obtain ⟨T₁, hT₁, hna⟩ := PrimeTorusTheory.exists_not_aligned_of_large_of_word
  refine ⟨max T₁ (Real.exp (Real.exp 1)), lt_max_of_lt_left hT₁, fun τ hτ N h => ?_⟩
  have hτ1 : T₁ ≤ τ := (le_max_left _ _).trans hτ
  have hτ2 : Real.exp (Real.exp 1) ≤ τ := (le_max_right _ _).trans hτ
  have hτpos : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ2
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log τ := ⟨_, rfl⟩
  have hLe : Real.exp 1 ≤ L := by
    rw [hL]
    exact (Real.le_log_iff_exp_le hτpos).mpr hτ2
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hLe
  have hLpos : 0 < L := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log L := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ]
    exact (Real.le_log_iff_exp_le hLpos).mpr hLe
  rw [← hL, ← hℓ]
  by_contra hcon
  push Not at hcon
  have htabs : T₁ ≤ |τ| := by rwa [abs_of_pos hτpos]
  obtain ⟨n, hn1, hnle, hfar⟩ := hna τ htabs
  rw [abs_of_pos hτpos, ← hL, ← hℓ] at hnle hfar
  have hbigpos : 0 < 1024 * L ^ 4 * ℓ ^ 2 := by positivity
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hbigpos hcon
  have hnN : (n : ℝ) ≤ N := by
    refine hnle.trans (le_trans ?_ hcon)
    have hL2 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
    have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
    have hp : 0 < L ^ 2 := by positivity
    calc 50 * L ^ 2 * ℓ ≤ 1024 * L ^ 2 * ℓ := by nlinarith [mul_pos hp (by linarith : 0 < ℓ)]
      _ = 1024 * (L ^ 2 * ℓ) := by ring
      _ ≤ 1024 * (L ^ 4 * ℓ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hL2 hℓ2 (by linarith) (by positivity)) (by norm_num)
      _ = _ := by ring
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hkN : k < N := by
    have : ((k + 1 : ℕ) : ℝ) ≤ N := hnN
    have h3 : k + 1 ≤ N := by exact_mod_cast this
    omega
  have hp := norm_exp_sub_one_le_of_isHeadReturn h hkN
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hfar
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = τ * Real.log ((k : ℝ) + 1) / (2 * Real.pi) := ⟨_, rfl⟩
  rw [← hy] at hfar
  obtain ⟨j, hj⟩ : ∃ j : ℤ, j = round y := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = y - j := ⟨_, rfl⟩
  have hxhalf : |x| ≤ 1 / 2 := by
    rw [hx, hj]
    exact abs_sub_round y
  have hfarx : 1 / (4096 * L ^ 4 * ℓ ^ 2) < |x| := by
    rw [hx]
    exact hfar j
  have hpi := Real.pi_pos
  -- The phase modulo `2π`.
  have hexp : exp ((-(Real.log ((k : ℝ) + 1) * τ) : ℝ) * I) = exp (I * ((-(2 * Real.pi * x) : ℝ) : ℂ)) := by
    have hkey : -(Real.log ((k : ℝ) + 1) * τ) = -(2 * Real.pi * x) + (-j : ℤ) * (2 * Real.pi) := by
      rw [hx, hy]
      push_cast
      field_simp
      ring
    rw [hkey]
    push_cast
    rw [add_mul, Complex.exp_add, mul_comm I]
    have h1 : ((-(j : ℂ)) * (2 * (Real.pi : ℂ))) * I = ((-j : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one] at hp
  have harg : (-(2 * Real.pi * x)) / 2 = -(Real.pi * x) := by ring
  rw [harg, Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_neg] at hp
  have hsinlow : 2 * |x| ≤ |Real.sin (Real.pi * x)| := by
    have hle : |Real.pi * x| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos hpi]
      nlinarith
    have h3 := Real.mul_abs_le_abs_sin hle
    have h4 : 2 / Real.pi * |Real.pi * x| = 2 * |x| := by
      rw [abs_mul, abs_of_pos hpi]
      field_simp
    linarith
  have hfour : 4 * |x| ≤ 1 / (N : ℝ) := by
    have h3 : |(2 : ℝ)| = 2 := by norm_num
    rw [h3] at hp
    linarith
  have hsmall : 1 / (N : ℝ) ≤ 1 / (1024 * L ^ 4 * ℓ ^ 2) := one_div_le_one_div_of_le hbigpos hcon
  have hsplit4 : 4 * (1 / (4096 * L ^ 4 * ℓ ^ 2)) = 1 / (1024 * L ^ 4 * ℓ ^ 2) := by
    field_simp
    ring
  linarith

/-- The aligned length at large height is at most `1024 (log τ)⁶`. -/
theorem length_le_pow_log_of_isHeadReturn :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ τ : ℝ, T₀ ≤ τ → ∀ N : ℕ, IsHeadReturn N τ →
      1 ≤ Real.log τ ∧ (N : ℝ) ≤ 1024 * Real.log τ ^ 6 := by
  obtain ⟨T₁, _, hlen⟩ := length_lt_of_isHeadReturn
  have hee : (1 : ℝ) ≤ Real.exp (Real.exp 1) := Real.one_le_exp (Real.exp_pos 1).le
  refine ⟨max T₁ (Real.exp (Real.exp 1)), hee.trans (le_max_right _ _), fun τ hτ N h => ?_⟩
  have hτe : Real.exp (Real.exp 1) ≤ τ := (le_max_right _ _).trans hτ
  have hτpos : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτe
  have hlenN := hlen τ ((le_max_left _ _).trans hτ) N h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log τ := ⟨_, rfl⟩
  have hLe : Real.exp 1 ≤ L := by
    rw [hL]
    exact (Real.le_log_iff_exp_le hτpos).mpr hτe
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hLe
  have hLpos : 0 < L := by linarith
  have hℓ1 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hℓL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  rw [← hL] at hlenN ⊢
  refine ⟨hL1, hlenN.le.trans ?_⟩
  have h3 : Real.log L ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hℓ1 hℓL 2
  calc 1024 * L ^ 4 * Real.log L ^ 2 ≤ 1024 * L ^ 4 * L ^ 2 := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

/-- **`N^A` is below every power of the height** at an aligned return up to `N`, once the height is large. -/
theorem eventually_length_rpow_lt {A c b : ℝ} (hA : 0 < A) (hc : 0 < c) (hb : 0 < b) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ τ : ℝ, H ≤ τ → ∀ N : ℕ, IsHeadReturn N τ → (N : ℝ) ^ A < c * τ ^ b := by
  obtain ⟨T₀, hT₀, hlen⟩ := length_le_pow_log_of_isHeadReturn
  have hK : 0 < c / (2 * (1024 : ℝ) ^ A) := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (6 * A) hb).bound hK
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hlo
  refine ⟨max T₀ H₀, hT₀.trans (le_max_left _ _), fun τ hτ N h => ?_⟩
  have hbd := hH₀ τ ((le_max_right _ _).trans hτ)
  have hτ1 : 1 ≤ τ := hT₀.trans ((le_max_left _ _).trans hτ)
  have hτpos : 0 < τ := by linarith
  obtain ⟨hL1, hN6⟩ := hlen τ ((le_max_left _ _).trans hτ) N h
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log τ := ⟨_, rfl⟩
  rw [← hL] at hL1 hN6 hbd
  have hLpos : 0 < L := by linarith
  have hpow : (N : ℝ) ^ A ≤ (1024 : ℝ) ^ A * L ^ (6 * A) := by
    calc (N : ℝ) ^ A ≤ (1024 * L ^ 6) ^ A := Real.rpow_le_rpow (Nat.cast_nonneg N) hN6 hA.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hLpos.le]
        norm_cast
  have hτp : 0 < τ ^ b := Real.rpow_pos_of_pos hτpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLpos _), abs_of_pos hτp] at hbd
  have h1024 : 0 < (1024 : ℝ) ^ A := by positivity
  calc (N : ℝ) ^ A ≤ (1024 : ℝ) ^ A * L ^ (6 * A) := hpow
    _ ≤ (1024 : ℝ) ^ A * (c / (2 * (1024 : ℝ) ^ A) * τ ^ b) :=
        mul_le_mul_of_nonneg_left hbd h1024.le
    _ = c / 2 * τ ^ b := by field_simp
    _ < c * τ ^ b := by nlinarith [mul_pos hc hτp]

/-! ### The bound fails on discs crossing the line -/

/-- **On a disc crossing `Re s = 0` the left edge exceeds `N^A`.** For `R > 3`, `γ ≥ 0` and `A > 0`, at every head return of length past some
`N₀`, at any `τ ≥ 1`, the point `−η + iγ`, `η = min(R − 3, 1)`, of the disc of radius `R` about `3 + iγ` has `|ζ(s + iτ)| > N^A`. -/
theorem exists_large_value_left {R : ℝ} (hR : 3 < R) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ τ : ℝ, 1 ≤ τ → IsHeadReturn N τ →
      ∃ s ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) R, (N : ℝ) ^ A < ‖riemannZeta (s + (τ : ℂ) * I)‖ := by
  obtain ⟨η, hηdef⟩ : ∃ η, η = min (R - 3) 1 := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hηdef]
    exact lt_min (by linarith) one_pos
  have hη1 : η ≤ 1 := hηdef ▸ min_le_right _ _
  have hηR : η ≤ R - 3 := hηdef ▸ min_le_left _ _
  obtain ⟨c, hc, hlow⟩ := exists_mul_rpow_le_norm_zeta_left hη0 hη1
  obtain ⟨H, hH1, hH⟩ := eventually_length_rpow_lt hA hc (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (H + 1)
  refine ⟨max 11 N₁, fun N hN τ hτ h => ?_⟩
  have hN11 : 11 ≤ N := (le_max_left _ _).trans hN
  have hNH : H + 1 ≤ (N : ℝ) := hN₁.trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hτN := lt_add_one_of_isHeadReturn hN11 hτ h
  have hτH : H ≤ τ := by linarith
  refine ⟨((-η : ℝ) : ℂ) + (γ : ℂ) * I, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    have hval : ((-η : ℝ) : ℂ) + (γ : ℂ) * I - ((3 : ℂ) + (γ : ℂ) * I) = ((-(η + 3) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by linarith)]
    linarith
  · have hsum : ((-η : ℝ) : ℂ) + (γ : ℂ) * I + (τ : ℂ) * I = ((-η : ℝ) : ℂ) + ((γ + τ : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hsum]
    have ht1 : 1 ≤ γ + τ := by linarith
    have hstep := hlow (γ + τ) ht1
    have hτpos : 0 < τ := by linarith
    have hpow : τ ^ (1 / 2 : ℝ) ≤ (γ + τ) ^ (1 / 2 + η) := by
      calc τ ^ (1 / 2 : ℝ) ≤ (γ + τ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hτpos.le (by linarith) (by norm_num)
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    calc (N : ℝ) ^ A < c * τ ^ (1 / 2 : ℝ) := hH τ hτH N h
      _ ≤ c * (γ + τ) ^ (1 / 2 + η) := mul_le_mul_of_nonneg_left hpow hc.le
      _ ≤ _ := hstep

/-- **On a disc crossing the critical line the bound fails for every exponent.** For `R > 5/2`, `γ ≥ 0` and `A > 0`, every head return of
length past some `N₀`, at any `τ ≥ 1`, has `|ζ(s + iτ)| > N^A` somewhere on the disc of radius `R` about `3 + iγ`. No hypothesis on the zeros
enters. -/
theorem exists_large_value_of_left_edge_lt_half {R : ℝ} (hR : 5 / 2 < R) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 < A) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ τ : ℝ, 1 ≤ τ → IsHeadReturn N τ →
      ∃ s ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) R, (N : ℝ) ^ A < ‖riemannZeta (s + (τ : ℂ) * I)‖ := by
  obtain ⟨c, b, H₁, hc, hb, hcore⟩ := exists_rpow_le_of_norm_le_on_disc hR hγ
  obtain ⟨H₂, _, hH₂⟩ := eventually_length_rpow_lt hA hc hb
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (max H₁ H₂ + 1)
  refine ⟨max 11 N₁, fun N hN τ hτ h => ?_⟩
  have hN11 : 11 ≤ N := (le_max_left _ _).trans hN
  have hNH : max H₁ H₂ + 1 ≤ (N : ℝ) := hN₁.trans (by exact_mod_cast (le_max_right _ _).trans hN)
  have hτN := lt_add_one_of_isHeadReturn hN11 hτ h
  have hτH : max H₁ H₂ ≤ τ := by linarith
  by_contra hcon
  push Not at hcon
  have h1 := hcore τ ((le_max_left _ _).trans hτH) _ hcon
  have h2 := hH₂ τ ((le_max_right _ _).trans hτH) N h
  linarith

/-- **No slow returns on a disc crossing the critical line.** -/
theorem not_slowReturns_of_left_edge_lt_half {R : ℝ} (hR : 5 / 2 < R) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 < A) :
    ¬ ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
      ∀ s ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) R, ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A := by
  intro hslow
  obtain ⟨N₀, hN₀⟩ := exists_large_value_of_left_edge_lt_half hR hγ hA
  obtain ⟨N, hN, τ, hτ, hhead, hbd⟩ := hslow N₀ 1
  obtain ⟨s, hs, hlt⟩ := hN₀ N hN τ hτ hhead
  exact absurd (hbd s hs) (not_le.mpr hlt)

/-- A zero right of `½` has a reflection with the same real part in the upper half-plane. -/
private theorem exists_upper_zero {s : ℂ} (hs : 1 / 2 < s.re) (hζ : riemannZeta s = 0) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = s.re ∧ s.re < 1 ∧ 0 < ρ.im := by
  have hs1 : s.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
  have hne1 : s ≠ 1 := fun h => by
    rw [h, one_re] at hs1
    exact lt_irrefl 1 hs1
  rcases lt_trichotomy s.im 0 with him | him | him
  · refine ⟨(starRingEnd ℂ) s, ?_, by simp, hs1, by simpa using him⟩
    exact (RHTower.riemannZeta_conj_eq_zero_iff_of_re_pos (by linarith) hne1).mpr hζ
  · exfalso
    have hreal : s = ((s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hreal] at hζ
    exact RHTower.riemannZeta_real_strip_ne_zero (by linarith) hs1 hζ
  · exact ⟨_, hζ, rfl, hs1, him⟩

/-- **Slow returns on a disc crossing the line are the Riemann hypothesis.** For `R > 5/2`, asking every zero right of `½` in the upper
half-plane for slow aligned returns, at some exponent, on the disc of radius `R` about `3 + iγ` holds exactly when there is no such zero. -/
theorem slowReturns_on_disc_iff_riemannHypothesis {R : ℝ} (hR : 5 / 2 < R) :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ∃ A : ℝ, 0 < A ∧
      ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
        ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) R,
          ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) ↔ RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  constructor
  · intro hslow s hs hζ
    obtain ⟨ρ, hρ, hρre, hs1, hρim⟩ := exists_upper_zero hs hζ
    obtain ⟨A, hA, hbd⟩ := hslow ρ hρ (by rw [hρre]; exact hs) (by rw [hρre]; exact hs1) hρim
    exact not_slowReturns_of_left_edge_lt_half hR hρim.le hA hbd
  · intro hRH ρ hρ h12 _ _
    exact absurd hρ (hRH ρ h12)

/-- **The hypothesis of `asymptoticAbscissaLaw_of_slowReturns` is the Riemann hypothesis.** On the disc of radius `31/10` the bound fails at
every right zero, so the hypothesis holds exactly when no right zero exists, and the receiver reads `RH ⇒ AAL`. -/
theorem slowReturnHypothesis_iff_riemannHypothesis :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ∀ A : ℝ, 0 < A →
      ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
        ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10),
          ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) ↔ RiemannHypothesis := by
  rw [← slowReturns_on_disc_iff_riemannHypothesis (by norm_num : (5 / 2 : ℝ) < 31 / 10)]
  constructor
  · intro hslow ρ hρ h12 h1 him
    exact ⟨1, one_pos, hslow ρ hρ h12 h1 him 1 one_pos⟩
  · intro hslow ρ hρ h12 h1 him A hA
    obtain ⟨A', hA', hbd⟩ := hslow ρ hρ h12 h1 him
    exact absurd hbd (not_slowReturns_of_left_edge_lt_half (by norm_num) him.le hA')

/-- **A domain of bounded translates lies right of the line.** Along a phase return, every connected open domain in the upper half-plane that
meets `Re s > 1` and carries bounded translates lies in `Re s > ½`. Otherwise it contains a disc about a point of the line; at a pair
`1 − u + iy`, `u + iy` of that disc with `u > ½`, the translates converge to `ζ` and the reflection makes them tend to `0` at `u + iy`, so `ζ`
vanishes on an open set. -/
theorem IsPhaseReturn.re_gt_half_of_translatesBoundedOn {τ : ℕ → ℝ} (h : IsPhaseReturn τ) {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUim : ∀ z ∈ U, 0 < z.im) {s₀ : ℂ} (hs₀ : s₀ ∈ U) (hs₀1 : 1 < s₀.re)
    (hbd : TranslatesBoundedOn τ U) {z : ℂ} (hz : z ∈ U) : 1 / 2 < z.re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hwU, hwre⟩ := hUc.intermediate_value hz hs₀ Complex.continuous_re.continuousOn
    (⟨hcon, by linarith⟩ : (1 / 2 : ℝ) ∈ Icc z.re s₀.re)
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hUo w hwU
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ε₀ (1 / 2) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min hε₀ (by norm_num)
  have hεU : ball w ε ⊆ U := (ball_subset_ball (hε ▸ min_le_left _ _)).trans hball
  have hε12 : ε ≤ 1 / 2 := hε ▸ min_le_right _ _
  have hlu := h.tendstoLocallyUniformlyOn hUo hUc hUim hs₀ hs₀1 hbd
  obtain ⟨C, _, hrefl⟩ := exists_norm_zeta_le_reflect
  -- `ζ` vanishes right of the line in the disc about `w`.
  have hzero : ∀ x ∈ ball w ε, 1 / 2 < x.re → riemannZeta x = 0 := by
    intro x hx hx12
    have hxn : ‖x - w‖ < ε := by rwa [mem_ball, dist_eq_norm] at hx
    obtain ⟨y, hy⟩ : ∃ y : ℂ, y = ((1 - x.re : ℝ) : ℂ) + (x.im : ℂ) * I := ⟨_, rfl⟩
    have hyball : y ∈ ball w ε := by
      rw [mem_ball, dist_eq_norm]
      have h2 : y - w = -((starRingEnd ℂ) (x - w)) := by
        apply Complex.ext
        · have h3 : y.re = 1 - x.re := by rw [hy]; simp
          rw [Complex.sub_re, h3, Complex.neg_re, Complex.conj_re, Complex.sub_re, hwre]
          ring
        · have h3 : y.im = x.im := by rw [hy]; simp
          rw [Complex.sub_im, h3, Complex.neg_im, Complex.conj_im, Complex.sub_im]
          ring
      rw [h2, norm_neg, Complex.norm_conj]
      exact hxn
    have hx1 : x.re < 1 := by
      have h2 := (abs_lt.mp ((Complex.abs_re_le_norm (x - w)).trans_lt hxn)).2
      rw [Complex.sub_re, hwre] at h2
      linarith
    have hxlim : Tendsto (fun j => riemannZeta (x + (τ j : ℂ) * I)) atTop (𝓝 (riemannZeta x)) :=
      hlu.tendsto_at (hεU hx)
    have hylim : Tendsto (fun j => riemannZeta (y + (τ j : ℂ) * I)) atTop (𝓝 (riemannZeta y)) :=
      hlu.tendsto_at (hεU hyball)
    have htj : Tendsto (fun j => x.im + τ j) atTop atTop := tendsto_atTop_add_const_left _ _ h.tendsto
    have hpow : Tendsto (fun j => (x.im + τ j) ^ (-(x.re - 1 / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp htj
    have hright : Tendsto (fun j => C * (x.im + τ j) ^ (-(x.re - 1 / 2)) * ‖riemannZeta (y + (τ j : ℂ) * I)‖)
        atTop (𝓝 (C * 0 * ‖riemannZeta y‖)) :=
      (hpow.const_mul C).mul hylim.norm
    rw [mul_zero, zero_mul] at hright
    have hlim0 : Tendsto (fun j => ‖riemannZeta (x + (τ j : ℂ) * I)‖) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hright
      filter_upwards [htj.eventually_ge_atTop 1] with j hj
      have hxj : x + (τ j : ℂ) * I = (x.re : ℂ) + ((x.im + τ j : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      have hyj : y + (τ j : ℂ) * I = ((1 - x.re : ℝ) : ℂ) + ((x.im + τ j : ℝ) : ℂ) * I := by
        rw [hy]
        push_cast
        ring
      rw [hxj, hyj]
      have h5 := hrefl x.re (x.im + τ j) hx12.le hx1 hj
      have h6 : (1 / 2 : ℝ) - x.re = -(x.re - 1 / 2) := by ring
      rwa [h6] at h5
    exact norm_eq_zero.mp (tendsto_nhds_unique hxlim.norm hlim0)
  -- A point right of the line in that disc, where the zeros of `ζ` are isolated.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : ℂ, x₀ = w + ((ε / 2 : ℝ) : ℂ) := ⟨_, rfl⟩
  have hx₀re : x₀.re = 1 / 2 + ε / 2 := by rw [hx₀, Complex.add_re, Complex.ofReal_re, hwre]
  have hx₀ball : x₀ ∈ ball w ε := by
    rw [mem_ball, dist_eq_norm, hx₀, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  have h1 : ∀ᶠ x in 𝓝 x₀, x ∈ ball w ε := isOpen_ball.mem_nhds hx₀ball
  have h2 : ∀ᶠ x in 𝓝 x₀, 1 / 2 < x.re :=
    (Complex.continuous_re.tendsto x₀).eventually (lt_mem_nhds (by rw [hx₀re]; linarith))
  have hiso := RHTower.eventually_riemannZeta_ne_zero_nhdsNE (w := x₀) (by rw [hx₀re]; linarith)
    (by rw [hx₀re]; linarith)
  obtain ⟨x, hne, hx⟩ := (hiso.and ((h1.and h2).filter_mono nhdsWithin_le_nhds)).exists
  exact hne (hzero x hx.1 hx.2)

/-! ### Transport on a disc short of the line -/

/-- The exponent of the transport theorem for a zero of real part `β` on a disc of radius `R` about `3 + iγ`. The zero sits at distance
`3 − β`; the circle halfway to the boundary has logarithmic position `t = log((R + 3 − β)/2)/log R`, and the exponent is `(1 − t)/(2t)`. -/
def transportExponent (β R : ℝ) : ℝ :=
  (1 - Real.log ((R + 3 - β) / 2) / Real.log R) / (2 * (Real.log ((R + 3 - β) / 2) / Real.log R))

/-- The transport exponent is positive when the disc reaches the zero. -/
theorem transportExponent_pos {β R : ℝ} (h1 : β < 1) (hR : 3 - β < R) : 0 < transportExponent β R := by
  have hD1 : 1 < (R + 3 - β) / 2 := by linarith
  have hDR : (R + 3 - β) / 2 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos (by linarith)
  have hlogD : 0 < Real.log ((R + 3 - β) / 2) := Real.log_pos hD1
  have hlt : Real.log ((R + 3 - β) / 2) < Real.log R := Real.log_lt_log (by linarith) hDR
  have ht0 : 0 < Real.log ((R + 3 - β) / 2) / Real.log R := div_pos hlogD hlogR
  have ht1 : Real.log ((R + 3 - β) / 2) / Real.log R < 1 := (div_lt_one hlogR).mpr hlt
  exact div_pos (by linarith) (by positivity)

/-- **Transport on a disc that stops short of the line.** Let `ρ = β + iγ` be a zero, `0 < β < 1`, `γ ≥ 3`, and `3 − β < R ≤ 31/10`. For every
`r > 0`, at every shift aligned up to a large `N`, the bound `|ζ(s + iτ)| ≤ N^{transportExponent β R}` on the disc of radius `R` about `3 + iγ`
puts a zero within `r` of `ρ + iτ`. -/
theorem transport_of_isHeadReturn_on_disc {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hγ : 3 ≤ ρ.im) {R : ℝ} (hR : 3 - ρ.re < R) (hR' : R ≤ 31 / 10) {r : ℝ} (hr : 0 < r) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ τ : ℝ, 1 ≤ τ → IsHeadReturn N τ →
      (∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) R,
        ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ transportExponent ρ.re R) →
      ∃ z ∈ ball ρ r, riemannZeta (z + (τ : ℂ) * I) = 0 := by
  have hρne : ρ ≠ 1 := fun h => by
    rw [h, one_re] at h1
    exact lt_irrefl _ h1
  obtain ⟨g, hg⟩ : ∃ g, g = (R - (3 - ρ.re)) / 2 := ⟨_, rfl⟩
  have hgpos : 0 < g := by rw [hg]; linarith
  obtain ⟨r₂, hr₂def⟩ : ∃ r₂, r₂ = min r (min g ((1 - ρ.re) / 2)) := ⟨_, rfl⟩
  have hr₂ : 0 < r₂ := by
    rw [hr₂def]
    exact lt_min hr (lt_min hgpos (by linarith))
  obtain ⟨r', m, hr'0, hr'lt, hsub, hm0, hmS⟩ :=
    exists_isolating_circle hρne hρ (ball_mem_nhds ρ hr₂) hr₂
  have hr'g : r' < g := hr'lt.trans_le (hr₂def ▸ (min_le_right _ _).trans (min_le_left _ _))
  have hr'2 : r' < (1 - ρ.re) / 2 := hr'lt.trans_le (hr₂def ▸ (min_le_right _ _).trans (min_le_right _ _))
  have hr'r : r' < r := hr'lt.trans_le (hr₂def ▸ min_le_left _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (3 : ℂ) + (ρ.im : ℂ) * I := ⟨_, rfl⟩
  have hcρ : ‖ρ - c‖ = 3 - ρ.re := by
    have hval : ρ - c = ((ρ.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  obtain ⟨D, hD⟩ : ∃ D, D = (R + 3 - ρ.re) / 2 := ⟨_, rfl⟩
  have hDg : D = 3 - ρ.re + g := by rw [hD, hg]; ring
  have hD1 : 1 < D := by rw [hDg]; linarith
  have hDR : D < R := by rw [hD]; linarith
  have hR1 : 1 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR1
  obtain ⟨t, ht⟩ : ∃ t, t = Real.log D / Real.log R := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos (Real.log_pos hD1) hlogR
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hlogR]
    exact Real.log_lt_log (by linarith) hDR
  obtain ⟨A, hA⟩ : ∃ A, A = transportExponent ρ.re R := ⟨_, rfl⟩
  have hAval : A = (1 - t) / (2 * t) := by
    rw [hA, transportExponent, ht, hD]
  have hA0 : 0 < A := hA ▸ transportExponent_pos h1 hR
  have hAt : A * t = (1 - t) / 2 := by
    rw [hAval]
    field_simp
  have hRle : ∀ y : ℂ, ‖y‖ ≤ R → ‖y‖ ≤ 31 / 10 := fun _ hy => hy.trans hR'
  -- The size of `ζ` itself on the disc.
  have hcont : ContinuousOn riemannZeta (closedBall c R) := by
    intro s hs
    have hw : ‖s - c‖ ≤ R := by
      rwa [mem_closedBall, dist_eq_norm] at hs
    have hne := transport_disc_ne_one hγ (hRle _ hw)
    rw [← hc, sub_add_cancel] at hne
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hcont
  -- A large aligned length.
  have hN1 : Tendsto (fun N : ℕ => (N : ℝ) ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA0).comp tendsto_natCast_atTop_atTop
  have hN2 : Tendsto (fun N : ℕ => 8 * (N : ℝ) ^ (-((1 - t) / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < (1 - t) / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul 8
    simpa using this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hN1.eventually_ge_atTop M₀).and
    ((hN2.eventually (gt_mem_nhds (by positivity : 0 < m / 2))).and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN τ hτ hhead hbd => ?_⟩
  rw [← hA] at hbd
  obtain ⟨hNM, hNsmall, hN2'⟩ := hN₀ N hN
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
  have hN0R : (0 : ℝ) < N := by linarith
  have hNA1 : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow (by linarith) hA0.le
  -- The three circles.
  have hbound : ∀ z ∈ closedBall ρ r', ‖riemannZeta (z + (τ : ℂ) * I) - riemannZeta z‖ < m / 2 := by
    intro z hz
    have hzρ : ‖z - ρ‖ ≤ r' := by
      rwa [mem_closedBall, dist_eq_norm] at hz
    obtain ⟨w, hw⟩ : ∃ w, w = z - c := ⟨_, rfl⟩
    have hwc : w + c = z := by rw [hw]; ring
    have hwle : ‖w‖ ≤ D := by
      have h2 : w = (z - ρ) + (ρ - c) := by rw [hw]; ring
      rw [h2, hDg, ← hcρ]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hwge : 1 ≤ ‖w‖ := by
      have h2 : ρ - c = -(z - ρ) + w := by rw [hw]; ring
      have h3 : ‖ρ - c‖ ≤ ‖z - ρ‖ + ‖w‖ := by
        rw [h2]
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
      rw [hcρ] at h3
      linarith
    obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun w => riemannZeta (w + c + (τ : ℂ) * I) - riemannZeta (w + c) := ⟨_, rfl⟩
    have hd : ∀ y : ℂ, 1 ≤ ‖y‖ → ‖y‖ ≤ R → DifferentiableAt ℂ f y := by
      intro y _ hy
      have hne1 := transport_disc_ne_one hγ (hRle _ hy)
      have hne2 := transport_disc_translate_ne_one hγ hτ (hRle _ hy)
      rw [← hc] at hne1 hne2
      rw [hf]
      refine DifferentiableAt.sub ?_ ?_
      · exact (differentiableAt_riemannZeta hne2).comp y
          ((differentiableAt_id.add_const c).add_const _)
      · exact (differentiableAt_riemannZeta hne1).comp y (differentiableAt_id.add_const c)
    have hM1 : ∀ y : ℂ, ‖y‖ = 1 → ‖f y‖ ≤ 4 / (N : ℝ) := by
      intro y hy
      have hre : 2 ≤ (y + c).re := by
        have h3 := (abs_le.mp ((Complex.abs_re_le_norm y).trans hy.le)).1
        simp [hc]
        linarith
      rw [hf]
      exact norm_sub_le_of_isHeadReturn (by omega) hhead hre
    have hM3 : ∀ y : ℂ, ‖y‖ = R → ‖f y‖ ≤ 2 * (N : ℝ) ^ A := by
      intro y hy
      have hmem : y + c ∈ closedBall c R := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, hy]
      rw [hf]
      refine (norm_sub_le _ _).trans ?_
      have h3 := hbd (y + c) (hc ▸ hmem)
      have h4 := hM₀ _ hmem
      linarith
    have hthree := HTGeometry.norm_le_of_three_circles (f := f) (r₁ := 1) (r₃ := R)
      one_pos hR1 hd hM1 hM3 hwge (by linarith)
    rw [Real.log_one, sub_zero, sub_zero] at hthree
    have hfz : f w = riemannZeta (z + (τ : ℂ) * I) - riemannZeta z := by
      rw [hf]
      simp only [hwc]
    rw [hfz] at hthree
    have hs : Real.log ‖w‖ / Real.log R ≤ t := by
      rw [ht]
      refine div_le_div_of_nonneg_right ?_ hlogR.le
      exact Real.log_le_log (by linarith) hwle
    have h4N : 4 / (N : ℝ) ≤ 2 * (N : ℝ) ^ A := by
      have : 4 / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN0R]
        linarith
      linarith
    refine lt_of_le_of_lt (hthree.trans ((interp_mono (by positivity) h4N hs).trans ?_)) hNsmall
    exact interp_value (by linarith) ht0 ht1 hAt
  have hre : ∀ s ∈ closedBall ρ r', s.re < 1 := by
    intro s hs
    have h2 : ‖s - ρ‖ ≤ r' := by
      rwa [mem_closedBall, dist_eq_norm] at hs
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm (s - ρ)).trans h2)).2
    rw [Complex.sub_re] at h3
    linarith
  obtain ⟨z, hz, hzero⟩ := RHTower.exists_zero_of_mem_zetaReturnSet hr'0 hre hρ hmS hbound
  exact ⟨z, ball_subset_ball hr'r.le hz, hzero⟩

/-- **The lower bound behind a finite top layer, on a disc short of the line.** If finitely many zeros lie right of `σ`, then for a zero `ρ`
right of `σ`, at every aligned shift past a height, `ζ` exceeds `N^{transportExponent β R}` somewhere on the disc of radius `R`. -/
theorem exists_large_value_of_finite_on_disc {σ : ℝ} (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hσ : σ < ρ.re) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 3 ≤ ρ.im) {R : ℝ}
    (hR : 3 - ρ.re < R) (hR' : R ≤ 31 / 10) :
    ∃ (N₀ : ℕ) (H : ℝ), ∀ N, N₀ ≤ N → ∀ τ : ℝ, H ≤ τ → IsHeadReturn N τ →
      ∃ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) R,
        (N : ℝ) ^ transportExponent ρ.re R < ‖riemannZeta (s + (τ : ℂ) * I)‖ := by
  obtain ⟨r, hrdef⟩ : ∃ r, r = ρ.re - σ := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  obtain ⟨N₀, hall⟩ := transport_of_isHeadReturn_on_disc hρ h0 h1 hγ hR hR' hr
  obtain ⟨Hm, hHm⟩ := (hfin.image Complex.im).bddAbove
  refine ⟨N₀, max 1 (Hm - ρ.im + r + 1), fun N hN τ hτ hhead => ?_⟩
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτ2 : Hm - ρ.im + r + 1 ≤ τ := (le_max_right _ _).trans hτ
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, hzero⟩ := hall N hN τ hτ1 hhead hcon
  have hzb : ‖z - ρ‖ < r := by
    rwa [mem_ball, dist_eq_norm] at hz
  have hre := (abs_lt.mp ((Complex.abs_re_le_norm (z - ρ)).trans_lt hzb)).1
  have him := (abs_lt.mp ((Complex.abs_im_le_norm (z - ρ)).trans_lt hzb)).1
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have hwre : (z + (τ : ℂ) * I).re = z.re := by simp
  have hwim : (z + (τ : ℂ) * I).im = z.im + τ := by simp
  have hmem : z + (τ : ℂ) * I ∈ {w : ℂ | riemannZeta w = 0 ∧ σ < w.re} :=
    ⟨hzero, by rw [hwre]; linarith⟩
  have hle := hHm ⟨_, hmem, rfl⟩
  rw [hwim] at hle
  linarith

/-- **Slow aligned returns on a disc short of the line give infinitely many zeros.** -/
theorem infinite_zeros_of_slow_returns_on_disc {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hγ : 3 ≤ ρ.im) {R : ℝ} (hR : 3 - ρ.re < R) (hR' : R ≤ 31 / 10)
    (hslow : ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
      ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) R,
        ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ transportExponent ρ.re R)
    {r : ℝ} (hr : 0 < r) : {w : ℂ | riemannZeta w = 0 ∧ ρ.re - r < w.re}.Infinite := by
  intro hfin
  obtain ⟨N₀, H, hall⟩ := exists_large_value_of_finite_on_disc hfin hρ (by linarith) h0 h1 hγ hR hR'
  obtain ⟨N, hN, τ, hτ, hhead, hbd⟩ := hslow N₀ H
  obtain ⟨s, hs, hlt⟩ := hall N hN τ hτ hhead
  exact absurd (hbd s hs) (not_le.mpr hlt)

/-- **Slow aligned returns right of the line give the asymptotic abscissa law.** It is enough that each zero `ρ = β + iγ` right of `½` in the
upper half-plane has some `½ ≤ σ₀ < β` such that aligned shifts of arbitrarily large length and height keep `ζ` below
`N^{transportExponent β (3 − σ₀)}` on the disc about `3 + iγ` with left edge `σ₀`. -/
theorem asymptoticAbscissaLaw_of_slowReturns_right
    (hslow : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ∃ σ₀ : ℝ, 1 / 2 ≤ σ₀ ∧ σ₀ < ρ.re ∧
      ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
        ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (3 - σ₀),
          ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ transportExponent ρ.re (3 - σ₀)) :
    RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_infinite_zeros fun ρ hρ h12 h1 him r hr => ?_
  have hne1 : ρ ≠ 1 := fun h => by
    rw [h, one_re] at h1
    exact lt_irrefl _ h1
  have hxi : RHTower.xi ρ = 0 := (RHTower.xi_eq_zero_iff (by linarith) hne1).mpr hρ
  have hhigh := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
    VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_sixtySeven hxi (by linarith) h1 (ne_of_gt h12)
  rw [abs_of_pos him] at hhigh
  obtain ⟨σ₀, hσ₀, hσβ, hbd⟩ := hslow ρ hρ h12 h1 him
  exact infinite_zeros_of_slow_returns_on_disc hρ (by linarith) h1 (by linarith) (by linarith) (by linarith) hbd hr

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
