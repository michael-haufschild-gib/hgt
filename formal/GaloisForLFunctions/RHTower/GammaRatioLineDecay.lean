import GaloisForLFunctions.RHTower.GammaRatioStripUniform
import GaloisForLFunctions.RHTower.SuzukiGammaForcedStripHardy

/-!
# The Gamma quotient decays at the exact vertical rate on a fixed line

On the line of height `σ` the Suzuki Gamma quotient

`‖Γ(1-σ+ix)‖ / ‖Γ(1+σ+ix)‖`

decays like `(1+|x|)^{-2σ}`.  The substrip bound already owned gives the matching lower bound and an
upper bound by a constant; the *upper* bound with the decay is what fixes the propagator exponent
`p = 1/2 + σ`, and it comes from the same parameter-uniform vertical law read in the other
direction, glued to a compactness bound on the unit box.

The exponent is exactly the vertical Stirling gain: raising the real part by `2σ` costs `|x|^{-2σ}`,
and the square root of the quotient contributes `|x|^{-σ}` to the propagator, which together with
the explicit factor `z^{-1/2}` is the card's `(1+|x|)^{-1/2-σ}`.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- **The Gamma quotient decays like `(1+|x|)^{-2σ}` on the line of height `σ`.** -/
theorem exists_upper_gammaRatioPair_decay {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, gammaRatioPair (σ, x) ≤ C * (1 + |x|) ^ (-(2 * σ)) := by
  -- far field, from the parameter-uniform vertical law
  obtain ⟨c₀, C₀, hc₀, hC₀, hvert⟩ :=
    exists_twoSided_gamma_vertical_ratio (a₁ := 1) (δ₁ := 2 * σ) zero_le_one (by linarith)
  -- the unit box, by compactness
  have hcompact : IsCompact ({σ} ×ˢ Icc (-1 : ℝ) 1) := isCompact_singleton.prod isCompact_Icc
  have hne : ({σ} ×ˢ Icc (-1 : ℝ) 1).Nonempty := ⟨(σ, 0), ⟨rfl, by norm_num⟩⟩
  have hsub : ({σ} ×ˢ Icc (-1 : ℝ) 1) ⊆ Icc (0 : ℝ) σ ×ˢ (univ : Set ℝ) := by
    rintro ⟨a, y⟩ ⟨ha, _⟩
    refine ⟨?_, mem_univ _⟩
    rw [mem_singleton_iff] at ha
    subst ha
    exact ⟨h0, le_rfl⟩
  obtain ⟨q₀, hq₀mem, hq₀max⟩ :=
    hcompact.exists_isMaxOn hne ((continuousOn_gammaRatioPair h1).mono hsub)
  set M : ℝ := gammaRatioPair q₀ with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact gammaRatioPair_pos h1 (by
      obtain ⟨ha, _⟩ := hq₀mem
      rw [mem_singleton_iff] at ha
      rw [ha]
      exact ⟨h0, le_rfl⟩)
  -- assemble
  refine ⟨(2 : ℝ) ^ (2 * σ) * (C₀ + M), by positivity, fun x => ?_⟩
  have hpow2 : (0 : ℝ) < (2 : ℝ) ^ (2 * σ) := Real.rpow_pos_of_pos (by norm_num) _
  rcases le_or_gt 1 |x| with hx | hx
  · -- far field
    have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le zero_lt_one hx
    have heven : gammaRatioPair (σ, x) = gammaRatioPair (σ, |x|) := by
      rcases abs_cases x with ⟨heq, _⟩ | ⟨heq, _⟩
      · rw [heq]
      · rw [heq, ← gammaRatioPair_neg σ x]
    have hvertx := (hvert (1 - σ) (2 * σ) |x| (by linarith) (by linarith) (by linarith)
      le_rfl hx).2
    have hcast : ((1 - σ + 2 * σ : ℝ) : ℂ) = ((1 + σ : ℝ) : ℂ) := by
      norm_num
      ring_nf
    have hval : gammaRatioPair (σ, |x|) ≤ C₀ * |x| ^ (-(2 * σ)) := by
      rw [gammaRatioPair]
      simpa [hcast] using hvertx
    have hcomp : |x| ^ (-(2 * σ)) ≤ (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) := by
      have hle : (1 : ℝ) + |x| ≤ 2 * |x| := by linarith
      have hmono : (2 * |x|) ^ (-(2 * σ)) ≤ (1 + |x|) ^ (-(2 * σ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      have hsplit : (2 * |x|) ^ (-(2 * σ)) = (2 : ℝ) ^ (-(2 * σ)) * |x| ^ (-(2 * σ)) :=
        Real.mul_rpow (by norm_num) hxpos.le
      have hinv : (2 : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ (-(2 * σ))) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        norm_num
      calc |x| ^ (-(2 * σ))
          = (2 : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ (-(2 * σ)) * |x| ^ (-(2 * σ))) := by
            rw [← mul_assoc, hinv, one_mul]
        _ = (2 : ℝ) ^ (2 * σ) * (2 * |x|) ^ (-(2 * σ)) := by rw [hsplit]
        _ ≤ (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) :=
            mul_le_mul_of_nonneg_left hmono hpow2.le
    calc gammaRatioPair (σ, x) = gammaRatioPair (σ, |x|) := heven
      _ ≤ C₀ * |x| ^ (-(2 * σ)) := hval
      _ ≤ C₀ * ((2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ))) :=
          mul_le_mul_of_nonneg_left hcomp hC₀.le
      _ ≤ (2 : ℝ) ^ (2 * σ) * (C₀ + M) * (1 + |x|) ^ (-(2 * σ)) := by
          have hnn : (0 : ℝ) ≤ (1 + |x|) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
          have hstep : C₀ ≤ C₀ + M := by linarith
          calc C₀ * ((2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)))
              = C₀ * (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) := by ring
            _ ≤ (C₀ + M) * (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hpow2.le) hnn
            _ = (2 : ℝ) ^ (2 * σ) * (C₀ + M) * (1 + |x|) ^ (-(2 * σ)) := by ring
  · -- unit box
    have hmem : (σ, x) ∈ ({σ} ×ˢ Icc (-1 : ℝ) 1) := by
      refine ⟨rfl, ?_⟩
      rw [mem_Icc]
      constructor <;> [linarith [abs_lt.mp hx |>.1]; linarith [abs_lt.mp hx |>.2]]
    have hMle : gammaRatioPair (σ, x) ≤ M := hq₀max hmem
    have hbox : (1 : ℝ) + |x| ≤ 2 := by
      have := abs_nonneg x
      linarith
    have hlow : ((2 : ℝ)) ^ (-(2 * σ)) ≤ (1 + |x|) ^ (-(2 * σ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hbox (by linarith)
    have hinv : (2 : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ (-(2 * σ))) = 1 := by
      rw [← Real.rpow_add (by norm_num)]
      norm_num
    calc gammaRatioPair (σ, x) ≤ M := hMle
      _ = M * ((2 : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ (-(2 * σ)))) := by rw [hinv, mul_one]
      _ ≤ M * ((2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow hpow2.le) hMpos.le
      _ ≤ (2 : ℝ) ^ (2 * σ) * (C₀ + M) * (1 + |x|) ^ (-(2 * σ)) := by
          have hnn : (0 : ℝ) ≤ (1 + |x|) ^ (-(2 * σ)) := Real.rpow_nonneg (by positivity) _
          have hstep : M ≤ C₀ + M := by linarith
          calc M * ((2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)))
              = M * (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) := by ring
            _ ≤ (C₀ + M) * (2 : ℝ) ^ (2 * σ) * (1 + |x|) ^ (-(2 * σ)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstep hpow2.le) hnn
            _ = (2 : ℝ) ^ (2 * σ) * (C₀ + M) * (1 + |x|) ^ (-(2 * σ)) := by ring

/-! ## The strip carrier decays at the propagator exponent -/

theorem suzukiGammaStripNormSq_eq_pair (σ x : ℝ) :
    suzukiGammaStripNormSq σ x
      = gammaRatioPair (σ, x) / ‖(x : ℂ) + (σ : ℂ) * Complex.I‖ := rfl

/-- **`(3)`, quantitative form.**  On the line of height `σ` the strip carrier decays at the exact
propagator exponent `p = 1/2 + σ`. -/
theorem exists_bound_suzukiGammaStripCarrier {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      suzukiGammaStripCarrier σ x ≤ K * (1 + |x|) ^ (-(1 / 2 + σ)) := by
  obtain ⟨C, hC, hCle⟩ := exists_upper_gammaRatioPair_decay hσ0.le hσ1
  refine ⟨Real.sqrt C * Real.sqrt (1 + σ⁻¹), by positivity, fun x => ?_⟩
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzre : z.re = x := by rw [hz]; simp
  have hznorm : (0 : ℝ) < ‖z‖ := by
    refine norm_pos_iff.mpr ?_
    intro hcon
    rw [hcon] at hzim
    simp at hzim
    linarith
  have hxle : |x| ≤ ‖z‖ := by
    rw [← hzre]
    exact Complex.abs_re_le_norm z
  have hσle : σ ≤ ‖z‖ := by
    have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    rw [hzim, abs_of_nonneg hσ0.le] at h1
    exact h1
  have hcomp : 1 + |x| ≤ (1 + σ⁻¹) * ‖z‖ := by
    have h1 : (1 : ℝ) ≤ σ⁻¹ * ‖z‖ := by
      rw [← div_eq_inv_mul, le_div_iff₀ hσ0]
      linarith
    nlinarith [hxle, h1]
  -- the two factors
  have hpair : Real.sqrt (gammaRatioPair (σ, x)) ≤ Real.sqrt C * (1 + |x|) ^ (-σ) := by
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hsq : Real.sqrt ((1 + |x|) ^ (-(2 * σ))) = (1 + |x|) ^ (-σ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    calc Real.sqrt (gammaRatioPair (σ, x))
        ≤ Real.sqrt (C * (1 + |x|) ^ (-(2 * σ))) := Real.sqrt_le_sqrt (hCle x)
      _ = Real.sqrt C * Real.sqrt ((1 + |x|) ^ (-(2 * σ))) := Real.sqrt_mul hC.le _
      _ = Real.sqrt C * (1 + |x|) ^ (-σ) := by rw [hsq]
  have hscale : (Real.sqrt ‖z‖)⁻¹ ≤ Real.sqrt (1 + σ⁻¹) * (1 + |x|) ^ (-(1 / 2 : ℝ)) := by
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hinvpos : (0 : ℝ) < 1 + σ⁻¹ := by positivity
    have hkey : (1 + |x|) ^ ((1 : ℝ) / 2) ≤ Real.sqrt (1 + σ⁻¹) * Real.sqrt ‖z‖ := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hinvpos.le]
      exact Real.sqrt_le_sqrt hcomp
    rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hznorm)]
    have hxneg : (1 + |x|) ^ (-(1 / 2 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hx0]
      norm_num
    calc (1 : ℝ) = (1 + |x|) ^ (-(1 / 2 : ℝ)) * (1 + |x|) ^ ((1 : ℝ) / 2) := hxneg.symm
      _ ≤ (1 + |x|) ^ (-(1 / 2 : ℝ)) * (Real.sqrt (1 + σ⁻¹) * Real.sqrt ‖z‖) :=
          mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hx0.le _)
      _ = Real.sqrt (1 + σ⁻¹) * (1 + |x|) ^ (-(1 / 2 : ℝ)) * Real.sqrt ‖z‖ := by ring
  -- assemble
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  have hcar : suzukiGammaStripCarrier σ x
      = Real.sqrt (gammaRatioPair (σ, x)) * (Real.sqrt ‖z‖)⁻¹ := by
    rw [suzukiGammaStripCarrier, suzukiGammaStripNormSq_eq_pair, Real.sqrt_div', ← hz]
    · rw [div_eq_mul_inv]
    · exact Real.sqrt_nonneg _
  rw [hcar]
  have hnn1 : (0 : ℝ) ≤ Real.sqrt (gammaRatioPair (σ, x)) := Real.sqrt_nonneg _
  have hnn2 : (0 : ℝ) ≤ (Real.sqrt ‖z‖)⁻¹ := by positivity
  have hsplit : (1 + |x|) ^ (-σ) * (1 + |x|) ^ (-(1 / 2 : ℝ))
      = (1 + |x|) ^ (-(1 / 2 + σ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  calc Real.sqrt (gammaRatioPair (σ, x)) * (Real.sqrt ‖z‖)⁻¹
      ≤ (Real.sqrt C * (1 + |x|) ^ (-σ))
        * (Real.sqrt (1 + σ⁻¹) * (1 + |x|) ^ (-(1 / 2 : ℝ))) :=
        mul_le_mul hpair hscale hnn2 (by positivity)
    _ = Real.sqrt C * Real.sqrt (1 + σ⁻¹)
        * ((1 + |x|) ^ (-σ) * (1 + |x|) ^ (-(1 / 2 : ℝ))) := by ring
    _ = Real.sqrt C * Real.sqrt (1 + σ⁻¹) * (1 + |x|) ^ (-(1 / 2 + σ)) := by rw [hsplit]

/-- **`(3)`, inverse half, quantitative form.**  The strip carrier is bounded below at the same
exponent, so its reciprocal grows at most like `(1+|x|)^{1/2+σ}`. -/
theorem exists_lower_bound_suzukiGammaStripCarrier {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ,
      c * (1 + |x|) ^ (-(1 / 2 + σ)) ≤ suzukiGammaStripCarrier σ x := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hpair⟩ := exists_twoSided_gammaRatioPair hσ0.le hσ1
  refine ⟨Real.sqrt c₀ * (Real.sqrt (1 + σ))⁻¹, by positivity, fun x => ?_⟩
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hznorm : (0 : ℝ) < ‖z‖ := by
    refine norm_pos_iff.mpr ?_
    intro hcon
    rw [hcon] at hzim
    simp at hzim
    linarith
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  have hupper : ‖z‖ ≤ (1 + σ) * (1 + |x|) := by
    have htri : ‖z‖ ≤ ‖(x : ℂ)‖ + ‖(σ : ℂ) * Complex.I‖ := by
      rw [hz]
      exact norm_add_le _ _
    have h1 : ‖(x : ℂ)‖ = |x| := by simp
    have h2 : ‖(σ : ℂ) * Complex.I‖ = σ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hσ0.le]
    rw [h1, h2] at htri
    nlinarith [abs_nonneg x, hσ0.le]
  -- the two factors
  have hpairlow : Real.sqrt c₀ * (1 + |x|) ^ (-σ) ≤ Real.sqrt (gammaRatioPair (σ, x)) := by
    have hbase := (hpair σ ⟨hσ0.le, le_rfl⟩ x).1
    have hsq : Real.sqrt ((1 + |x|) ^ (-(2 * σ))) = (1 + |x|) ^ (-σ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    calc Real.sqrt c₀ * (1 + |x|) ^ (-σ)
        = Real.sqrt c₀ * Real.sqrt ((1 + |x|) ^ (-(2 * σ))) := by rw [hsq]
      _ = Real.sqrt (c₀ * (1 + |x|) ^ (-(2 * σ))) := (Real.sqrt_mul hc₀.le _).symm
      _ ≤ Real.sqrt (gammaRatioPair (σ, x)) := Real.sqrt_le_sqrt hbase
  have hscalelow : (Real.sqrt (1 + σ))⁻¹ * (1 + |x|) ^ (-(1 / 2 : ℝ)) ≤ (Real.sqrt ‖z‖)⁻¹ := by
    have hprodpos : (0 : ℝ) < (1 + σ) * (1 + |x|) := by positivity
    have hkey : Real.sqrt ‖z‖ ≤ Real.sqrt (1 + σ) * (1 + |x|) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1 + σ)]
      exact Real.sqrt_le_sqrt hupper
    have hrhs : (0 : ℝ) < Real.sqrt (1 + σ) * (1 + |x|) ^ ((1 : ℝ) / 2) := by positivity
    have hinvle : (Real.sqrt (1 + σ) * (1 + |x|) ^ ((1 : ℝ) / 2))⁻¹ ≤ (Real.sqrt ‖z‖)⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hznorm) hkey
    refine le_trans (le_of_eq ?_) hinvle
    rw [mul_inv, ← Real.rpow_neg hx0.le]
  -- assemble
  have hcar : suzukiGammaStripCarrier σ x
      = Real.sqrt (gammaRatioPair (σ, x)) * (Real.sqrt ‖z‖)⁻¹ := by
    rw [suzukiGammaStripCarrier, suzukiGammaStripNormSq_eq_pair, Real.sqrt_div', ← hz]
    · rw [div_eq_mul_inv]
    · exact Real.sqrt_nonneg _
  rw [hcar]
  have hsplit : (1 + |x|) ^ (-σ) * (1 + |x|) ^ (-(1 / 2 : ℝ))
      = (1 + |x|) ^ (-(1 / 2 + σ)) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  calc Real.sqrt c₀ * (Real.sqrt (1 + σ))⁻¹ * (1 + |x|) ^ (-(1 / 2 + σ))
      = (Real.sqrt c₀ * (1 + |x|) ^ (-σ))
        * ((Real.sqrt (1 + σ))⁻¹ * (1 + |x|) ^ (-(1 / 2 : ℝ))) := by
        rw [← hsplit]; ring
    _ ≤ Real.sqrt (gammaRatioPair (σ, x)) * (Real.sqrt ‖z‖)⁻¹ :=
        mul_le_mul hpairlow hscalelow (by positivity) (Real.sqrt_nonneg _)

/-- The reciprocal carrier grows at most at the propagator exponent. -/
theorem exists_bound_suzukiGammaStripCarrier_inv {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ,
      (suzukiGammaStripCarrier σ x)⁻¹ ≤ K * (1 + |x|) ^ (1 / 2 + σ) := by
  obtain ⟨c, hc, hlow⟩ := exists_lower_bound_suzukiGammaStripCarrier hσ0 hσ1
  refine ⟨c⁻¹, by positivity, fun x => ?_⟩
  have hx0 : (0 : ℝ) < 1 + |x| := by positivity
  have hcarpos : 0 < suzukiGammaStripCarrier σ x := suzukiGammaStripCarrier_pos hσ0 hσ1 x
  have hbase := hlow x
  have hpowpos : (0 : ℝ) < (1 + |x|) ^ (-(1 / 2 + σ)) := Real.rpow_pos_of_pos hx0 _
  have hinv : (suzukiGammaStripCarrier σ x)⁻¹ ≤ (c * (1 + |x|) ^ (-(1 / 2 + σ)))⁻¹ :=
    inv_anti₀ (by positivity) hbase
  refine hinv.trans (le_of_eq ?_)
  rw [mul_inv, ← Real.rpow_neg hx0.le]
  norm_num

end GaloisForLFunctions.RHTower
