import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheTransportOfAZeroIsEffective
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound
import GaloisForLFunctions.PrimeTorusTheory.TheMisalignmentBand
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The slow return bound lives right of the line

A bound `|ζ(s + iτ)| ≤ N^A` at an aligned shift can only hold on a domain that stays right of `Re s = 0`.

* **Left of `Re s = 0` the size is a power of the height** (`exists_mul_rpow_le_norm_zeta_left`). The functional equation gives
  `|ζ(−η + it)| ≥ c t^{½+η}` for `0 < η ≤ 1`, `t ≥ 1`: the cosine cancels the decay of `Γ`, and `|ζ(1 + η − it)|` is bounded below.
* **An aligned length is a power of the logarithm of the height.** A head return up to `N ≥ 11` at `τ ≥ 1` has `N < τ + 1`
  (`lt_add_one_of_isHeadReturn`), since consecutive integers near `τ` have phases apart by a fixed amount. At large `τ`, non-alignment gives the sharper
  `N < 1024 (log τ)⁴ (log log τ)²` (`length_lt_of_isHeadReturn`). With `exists_isHeadReturn_le`, this brackets the aligned length at a height.
* **So on a disc about `3 + iγ` of radius `R > 3` the bound fails for every exponent** (`exists_large_value_left`), at every long enough head return, with no
  hypothesis on the zeros. The disc of radius `31/10` is such a disc. The hypothesis of `asymptoticAbscissaLaw_of_slowReturns` therefore holds exactly when no zero lies right of
  `½` (`slowReturnHypothesis_iff_riemannHypothesis`): as a receiver it reads `RH ⇒ AAL`.
* **The transport theorem survives on discs that stop short of the line** (`transport_of_isHeadReturn_on_disc`). For a zero `ρ = β + iγ` and any radius `3 − β < R ≤ 31/10`,
  the explicit exponent `transportExponent β R` suffices, for every `r > 0`. Taking `R = 3 − σ₀`, `½ ≤ σ₀ < β`, the domain stays right of the line, and
  aligned returns bounded there at each right zero give the asymptotic abscissa law (`asymptoticAbscissaLaw_of_slowReturns_right`).
-/

open Complex Filter Topology Metric Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

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
  -- The Gamma factor.
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
  have htpow : 0 < t ^ (1 / 2 - η) := Real.rpow_pos_of_pos ht0 _
  have hGlow : (C * t ^ (1 / 2 - η) * E)⁻¹ ≤ ‖Complex.Gamma u‖ := by
    rw [← inv_inv ‖Complex.Gamma u‖]
    exact inv_anti₀ (inv_pos.mpr hGupos) hGinv
  have hut : t ≤ ‖u‖ := by
    have := Complex.abs_im_le_norm u
    rwa [huim, abs_of_pos ht0] at this
  have hpowmul : P * t ^ (1 / 2 - η) = t := by
    rw [hP, ← Real.rpow_add ht0]
    have : (1 / 2 + η) + (1 / 2 - η) = 1 := by ring
    rw [this, Real.rpow_one]
  have hGs : P / (C * E) ≤ ‖Complex.Gamma s‖ := by
    rw [hGamma]
    have hstep : P / (C * E) = t * (C * t ^ (1 / 2 - η) * E)⁻¹ := by
      rw [← hpowmul]
      field_simp
    rw [hstep]
    exact mul_le_mul hut hGlow (by positivity) (norm_nonneg _)
  -- The cosine.
  have hcos : E / 4 ≤ ‖cos ((Real.pi : ℂ) * s / 2)‖ := by
    have h3 := sub_exp_le_two_mul_norm_cos ((Real.pi : ℂ) * s / 2)
    have him : ((Real.pi : ℂ) * s / 2).im = -(Real.pi * t / 2) := by
      have : (Real.pi : ℂ) * s / 2 = ((Real.pi / 2 : ℝ) : ℂ) * s := by
        push_cast
        ring
      rw [this, Complex.im_ofReal_mul, hsim]
      ring
    have hab : |((Real.pi : ℂ) * s / 2).im| = Real.pi * t / 2 := by
      rw [him, abs_neg, abs_of_pos (by positivity)]
    rw [hab, ← hE] at h3
    have hsmall : Real.exp (-(Real.pi * t / 2)) ≤ E / 2 := by
      rw [Real.exp_neg, ← hE]
      have hE2 : 2 ≤ E := by
        rw [hE]
        have h5 : (1 : ℝ) ≤ Real.pi * t / 2 := by
          have := Real.pi_gt_three
          nlinarith
        have h6 := Real.add_one_le_exp (Real.pi * t / 2)
        linarith
      rw [inv_le_iff_one_le_mul₀ hEpos]
      nlinarith
    linarith
  -- The value of `ζ` to the right of `1`.
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

/-- The phase at `n + 1` of a head return, written as an exponential. -/
private theorem norm_exp_sub_one_le_of_isHeadReturn {N : ℕ} {τ : ℝ} (h : IsHeadReturn N τ) {n : ℕ} (hn : n < N) :
    ‖exp ((-(Real.log ((n : ℝ) + 1) * τ) : ℝ) * I) - 1‖ ≤ 1 / (N : ℝ) := by
  have h1 := h n hn
  rw [phaseDefect_eq] at h1
  have h2 : -Real.log ((n : ℝ) + 1) * τ = -(Real.log ((n : ℝ) + 1) * τ) := by ring
  rwa [h2] at h1

/-- **An aligned length is below the height.** A head return up to `N ≥ 11` at `τ ≥ 1` has `N < τ + 1`: the integers `⌈τ⌉` and `⌈τ⌉ + 1` have phases apart by an amount in `[1/3, 1]`. -/
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
  -- Size of the step.
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
    have h3 : 1 / 3 / Real.pi ≤ θ / Real.pi := div_le_div_of_nonneg_right hθ3 hpi3.le.trans' (by norm_num) |>.trans le_rfl
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  rw [le_div_iff₀ hNpos] at hlow
  have h7 : 2 * (1 / 3 / Real.pi) * (N : ℝ) = 2 * (N : ℝ) / (3 * Real.pi) := by
    field_simp
  rw [h7, div_le_iff₀ (by positivity)] at hlow
  nlinarith

/-- **An aligned length is polylogarithmic in the height.** At large `τ`, a head return up to `N` has `N < 1024 (log τ)⁴ (log log τ)²`. -/
theorem length_lt_of_isHeadReturn :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ τ : ℝ, T₀ ≤ τ → ∀ N : ℕ, IsHeadReturn N τ →
      (N : ℝ) < 1024 * Real.log τ ^ 4 * Real.log (Real.log τ) ^ 2 := by
  obtain ⟨T₁, hT₁, hna⟩ := PrimeTorusTheory.exists_not_aligned_of_large_of_word
  have hee : (1 : ℝ) < Real.exp (Real.exp 1) := Real.one_lt_exp_iff.mpr (Real.exp_pos 1)
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

/-- The aligned length, read at a real exponent, is small against any power of the height. -/
private theorem eventually_length_rpow_lt {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∃ H : ℝ, 1 ≤ H ∧ ∀ τ : ℝ, H ≤ τ → ∀ N : ℕ, IsHeadReturn N τ → (N : ℝ) ^ A < c * τ ^ (1 / 2 : ℝ) := by
  obtain ⟨T₀, hT₀, hlen⟩ := length_lt_of_isHeadReturn
  have hK : 0 < c / (2 * (1024 : ℝ) ^ A) := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (6 * A) (by norm_num : (0 : ℝ) < 1 / 2)).bound hK
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp
    (hlo.and ((eventually_ge_atTop T₀).and (eventually_ge_atTop (Real.exp (Real.exp 1)))))
  have hee : 1 ≤ Real.exp (Real.exp 1) := Real.one_le_exp (Real.exp_pos 1).le
  refine ⟨max 1 H₀, le_max_left _ _, fun τ hτ N h => ?_⟩
  obtain ⟨hbd, hτT, hτe⟩ := hH₀ τ ((le_max_right _ _).trans hτ)
  have hτpos : 0 < τ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hτ)
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log τ := ⟨_, rfl⟩
  have hLe : Real.exp 1 ≤ L := by
    rw [hL]
    exact (Real.le_log_iff_exp_le hτpos).mpr hτe
  have hL1 : 1 ≤ L := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hLe
  have hLpos : 0 < L := by linarith
  have hℓ1 : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLpos).mpr hLe
  have hℓL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hlenN := hlen τ hτT N h
  rw [← hL] at hlenN hbd
  have hN6 : (N : ℝ) ≤ 1024 * L ^ 6 := by
    refine hlenN.le.trans ?_
    have h3 : Real.log L ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hℓL 2
    calc 1024 * L ^ 4 * Real.log L ^ 2 ≤ 1024 * L ^ 4 * L ^ 2 :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := by ring
  have hpow : (N : ℝ) ^ A ≤ (1024 : ℝ) ^ A * L ^ (6 * A) := by
    calc (N : ℝ) ^ A ≤ (1024 * L ^ 6) ^ A := Real.rpow_le_rpow (Nat.cast_nonneg N) hN6 hA.le
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hLpos.le]
        norm_cast
  have hτp : 0 < τ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hτpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLpos _), abs_of_pos hτp] at hbd
  have h1024 : 0 < (1024 : ℝ) ^ A := by positivity
  calc (N : ℝ) ^ A ≤ (1024 : ℝ) ^ A * L ^ (6 * A) := hpow
    _ ≤ (1024 : ℝ) ^ A * (c / (2 * (1024 : ℝ) ^ A) * τ ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbd h1024.le
    _ = c / 2 * τ ^ (1 / 2 : ℝ) := by field_simp
    _ < c * τ ^ (1 / 2 : ℝ) := by nlinarith [mul_pos hc hτp]

/-- **On a disc crossing `Re s = 0` the bound fails for every exponent.** For `R > 3`, `γ ≥ 0` and `A > 0`, every head return of length past some `N₀`, at any `τ ≥ 1`,
has `|ζ(s + iτ)| > N^A` somewhere on the disc of radius `R` about `3 + iγ`. No hypothesis on the zeros enters. -/
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
  obtain ⟨H, hH1, hH⟩ := eventually_length_rpow_lt hA hc
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

/-- **No slow returns on a disc crossing `Re s = 0`.** -/
theorem not_slowReturns_left {R : ℝ} (hR : 3 < R) {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 < A) :
    ¬ ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
      ∀ s ∈ closedBall ((3 : ℂ) + (γ : ℂ) * I) R, ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A := by
  intro hslow
  obtain ⟨N₀, hN₀⟩ := exists_large_value_left hR hγ hA
  obtain ⟨N, hN, τ, hτ, hhead, hbd⟩ := hslow N₀ 1
  obtain ⟨s, hs, hlt⟩ := hN₀ N hN τ hτ hhead
  exact absurd (hbd s hs) (not_le.mpr hlt)

/-- **The hypothesis of `asymptoticAbscissaLaw_of_slowReturns` is the Riemann hypothesis.** On the disc of radius `31/10` the bound is false at every right zero, so the hypothesis holds
exactly when no right zero exists, and the receiver reads `RH ⇒ AAL`. -/
theorem slowReturnHypothesis_iff_riemannHypothesis :
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ∀ A : ℝ, 0 < A →
      ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
        ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10),
          ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) ↔ RiemannHypothesis := by
  rw [RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re]
  constructor
  · intro hslow s hs hζ
    have hs1 : s.re < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hζ
    have hne1 : s ≠ 1 := fun h => by
      rw [h, one_re] at hs1
      exact lt_irrefl 1 hs1
    obtain ⟨ρ, hρ, hρre, hρim⟩ : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = s.re ∧ 0 < ρ.im := by
      rcases lt_trichotomy s.im 0 with him | him | him
      · refine ⟨(starRingEnd ℂ) s, ?_, by simp, by simpa using him⟩
        exact (RHTower.riemannZeta_conj_eq_zero_iff_of_re_pos (by linarith) hne1).mpr hζ
      · exfalso
        have hreal : s = ((s.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp [him]
        rw [hreal] at hζ
        exact RHTower.riemannZeta_real_strip_ne_zero (by linarith) hs1 hζ
      · exact ⟨_, hζ, rfl, him⟩
    exact not_slowReturns_left (by norm_num : (3 : ℝ) < 31 / 10) hρim.le one_pos
      (hslow ρ hρ (by rw [hρre]; exact hs) (by rw [hρre]; exact hs1) hρim 1 one_pos)
  · intro hRH ρ hρ h12 _ _
    exact absurd hρ (hRH ρ h12)

/-- The exponent of the transport theorem for a zero of real part `β` on a disc of radius `R` about `3 + iγ`. The zero sits at distance `3 − β`, and the
circle halfway to the boundary has logarithmic position `t = log((R + 3 − β)/2)/log R`; the exponent is `(1 − t)/(2t)`. -/
def transportExponent (β R : ℝ) : ℝ :=
  (1 - Real.log ((R + 3 - β) / 2) / Real.log R) / (2 * (Real.log ((R + 3 - β) / 2) / Real.log R))

/-- **Transport on a disc that stops short of the line.** Let `ρ = β + iγ` be a zero, `0 < β < 1`, `γ ≥ 3`, and `3 − β < R ≤ 31/10`. For every `r > 0`, at every shift aligned up to a large `N`, the bound
`|ζ(s + iτ)| ≤ N^{transportExponent β R}` on the disc of radius `R` about `3 + iγ` puts a zero within `r` of `ρ + iτ`. -/
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
  have hA0 : 0 < A := by
    rw [hAval]
    exact div_pos (by linarith) (by positivity)
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

/-- **The lower bound behind a finite top layer, on a disc short of the line.** If finitely many zeros lie right of `σ`, then for a zero `ρ` right of `σ`, at every aligned shift past a height,
`ζ` exceeds `N^{transportExponent β R}` somewhere on the disc of radius `R`. -/
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

/-- **Slow aligned returns right of the line give the asymptotic abscissa law.** It is enough that each zero `ρ = β + iγ` right of `½` in the upper half-plane has some `½ ≤ σ₀ < β` such that aligned
shifts of arbitrarily large length and height keep `ζ` below `N^{transportExponent β (3 − σ₀)}` on the disc about `3 + iγ` with left edge `σ₀`. -/
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
