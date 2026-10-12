import GaloisForLFunctions.RHTower.EvenLandauPairTest
import GaloisForLFunctions.RHTower.LandauSharpOffLineExclusion

/-!
# The Nyquist constant `2π` for even tests

**Theorem** (`evenHodgeIndex_forces_critical_line_below_landau`, unconditional). Weil positivity at
level `a` on even tests alone puts every separated zero of bounded multiplicity with ordinate in
`[8, (1-η) 2πe^{2a}]` on the critical line, for all large `a`. The depth condition is
`12C log(t₀+1)/δ + 6 log(1/|β₀ - 1/2|) ≤ (π/2)η^{3/2}e^{2a}`.

The proof is that of `hodgeIndex_forces_critical_line_below_landau`, with
`pairLandau_inequality_even` in place of `pairLandau_inequality`. The larger node constant
`49 N³ A₀² (147 + 12 log(t₀+3))`, `N = 1 + 4/(s|β₀ - 1/2|)`, satisfies
`Z δ₀³ ≤ 373625 A₀² (3+2a)/s³`. It enters the exponent balance with `δ₀^{3/2}` in place of `δ₀`,
which costs `2 log(1/δ₀)` in the depth condition.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- **The level bound.** Under even positivity at level `a`, with `U + w + s ≤ a`, an off-line pair as in
`offLine_pairKernel_package` satisfies
`m_V(θ,t₀,δ/2) t₀² 4w e^{-w/2}∫κ ≤ 2^{2m}(2M e^{(6+3m)U}e^{-π cos(2θ)e^{2U}}) B_w (1+t₀)²
· 49 N³ A₀² (147 + 12 log(t₀+3))`. -/
theorem landauPair_level_bound_even {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (hγ : 8 ≤ ρ₀.im) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : ρ₀.re - 1 / 2 ≤ δ / 2)
    {U w s a : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : U + w + s ≤ a) (hH : EvenHodgeIndexAtLevel zetaZeroConfig a)
    (hrate : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * U))
    (hslope : 6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ) ≤
      2 * (π * Real.cos (2 * θ)) * Real.exp (2 * U)) :
    dividedKernelFloor θ ρ₀.im (δ / 2) *
        (ρ₀.im ^ 2 * (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)))) ≤
      (2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst *
        Real.exp ((6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) * U) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * U))))) *
      (scaledBumpConst w * (1 + ρ₀.im) ^ 2) *
      (49 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (ρ₀.im + 3))) := by
  have hoff : ρ₀.re ≠ 1 / 2 := ne_of_gt hβ
  have hdep' : |ρ₀.re - 1 / 2| ≤ δ / 2 := by rw [abs_of_pos (by linarith)]; exact hdep
  obtain ⟨h, hK, hprod, hF₀, hF₁, htail⟩ :=
    offLine_pairKernel_package hθ0 hθ hρ₀ hoff hγ hδ hδ2 hsep hdep'
  have hnt : IsNontrivialZero ρ₀ := hρ₀
  set t₀ := ρ₀.im with ht₀
  set γ₀ := gammaOf ρ₀ with hγ₀
  have him2 : |γ₀.im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt ⟨hnt.2.1, hnt.2.2⟩).le
  have him2' : |((starRingEnd ℂ) γ₀).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact him2
  have hre₀ : γ₀.re = t₀ := WeilEF.gammaOf_re ρ₀
  have hre₁ : ((starRingEnd ℂ) γ₀).re = t₀ := by rw [Complex.conj_re]; exact hre₀
  set F := dividedKernelFloor θ t₀ (δ / 2) with hFdef
  have hF0 : 0 < F := dividedKernelFloor_pos (by linarith)
  set Kb := 4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)) with hKb
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hKb0 : 0 ≤ Kb := by rw [hKb]; positivity
  have hκ₀ := norm_paperFT_scaledBumpPolarFree_node_ge hw t₀ hre₀ him2
  have hκ₁ := norm_paperFT_scaledBumpPolarFree_node_ge hw t₀ hre₁ him2'
  have hlam0 : 0 ≤ F * (t₀ ^ 2 * Kb) := by positivity
  have hX₀ : F * (t₀ ^ 2 * Kb) ≤ ‖paperFT h γ₀‖ * ‖paperFT (scaledBumpPolarFree w t₀) γ₀‖ :=
    mul_le_mul hF₀ hκ₀ (by positivity) (norm_nonneg _)
  have hX₁ : F * (t₀ ^ 2 * Kb) ≤ ‖paperFT h ((starRingEnd ℂ) γ₀)‖ *
      ‖paperFT (scaledBumpPolarFree w t₀) ((starRingEnd ℂ) γ₀)‖ :=
    mul_le_mul hF₁ hκ₁ (by positivity) (norm_nonneg _)
  have hpair := pairLandau_inequality_even hA₀ hloc hθ0 hθ hρ₀ hoff (by linarith) hK hprod hw hw4
    hs hs1 ha hH hlam0 hX₀ hX₁
  -- the tail of the divided kernel
  have ht1 := htail (1 / 2) U (by norm_num)
  have hb : (1 / 2 : ℝ) + 3 / 2 * ((2 * zetaZeroConfig.mult ρ₀ : ℕ) : ℝ) =
      1 / 2 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ) := by push_cast; ring
  rw [hb] at ht1
  have hslope' : 11 / 2 + (1 / 2 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) ≤
      2 * (π * Real.cos (2 * θ)) * Real.exp (2 * U) := by linarith
  have ht2 := expTail_tiltedPhi_le_of_rate hθ0 hθ hrate hslope'
  have he : (11 / 2 + (1 / 2 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ))) =
      6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ) := by ring
  rw [he] at ht2
  have hεt : expTail h (1 / 2) U ≤ 2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst *
      Real.exp ((6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) * U) *
      Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * U)))) :=
    ht1.trans (mul_le_mul_of_nonneg_left ht2 (by positivity))
  have hA0 : 0 ≤ A₀ := by linarith
  have hZ0 : 0 ≤ 49 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 3 * A₀ ^ 2 *
      (147 + 12 * Real.log (t₀ + 3)) := by
    have : 0 ≤ Real.log (t₀ + 3) := Real.log_nonneg (by linarith)
    positivity
  have hBw0 : 0 ≤ scaledBumpConst w * (1 + t₀) ^ 2 := by
    have := scaledBumpConst_nonneg hw; positivity
  refine hpair.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hεt hBw0) hZ0


/-- `Z δ₀³ ≤ 373625 A₀² (3+2a)/s³` for `Z = 49(1 + 4/(sδ₀))³ A₀² (147 + 12 log(t₀+3))`,
`0 < δ₀ ≤ 1/4`, `0 < s ≤ 1`, `t₀ ≤ 2πe^{2a}`. -/
theorem landauPair_Ze_bound {s δ₀ A₀ t₀ a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hδ₀ : 0 < δ₀)
    (hδ₀4 : δ₀ ≤ 1 / 4) (hA₀ : 1 ≤ A₀) (ht₀ : 0 ≤ t₀) (ha : 0 ≤ a)
    (hta : t₀ ≤ 2 * π * Real.exp (2 * a)) :
    (49 * (1 + 4 / (s * |δ₀|)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (t₀ + 3))) * δ₀ ^ 3 ≤
      373625 * A₀ ^ 2 * (3 + 2 * a) / s ^ 3 := by
  rw [abs_of_pos hδ₀]
  have hlog : Real.log (t₀ + 3) ≤ 3 + 2 * a := by
    have hE := Real.exp_pos (2 * a)
    have hE1 : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
    have h1 : t₀ + 3 ≤ 10 * Real.exp (2 * a) := by nlinarith [Real.pi_lt_d2]
    have h2 : Real.log (t₀ + 3) ≤ Real.log (10 * Real.exp (2 * a)) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) hE.ne', Real.log_exp] at h2
    have h3 : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h4 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hlog0 : 0 ≤ Real.log (t₀ + 3) := Real.log_nonneg (by linarith)
  have hcube : (1 + 4 / (s * δ₀)) ^ 3 * δ₀ ^ 3 ≤ 125 / s ^ 3 := by
    have e : (1 + 4 / (s * δ₀)) * δ₀ = δ₀ + 4 / s := by field_simp
    have h1 : δ₀ + 4 / s ≤ 5 / s := by
      have : δ₀ ≤ 1 / s := by
        rw [le_div_iff₀ hs]; nlinarith
      have e2 : 5 / s = 1 / s + 4 / s := by ring
      linarith
    have h0 : 0 ≤ δ₀ + 4 / s := by positivity
    calc (1 + 4 / (s * δ₀)) ^ 3 * δ₀ ^ 3 = (δ₀ + 4 / s) ^ 3 := by rw [← e]; ring
      _ ≤ (5 / s) ^ 3 := pow_le_pow_left₀ h0 h1 3
      _ = 125 / s ^ 3 := by ring
  have hL : 147 + 12 * Real.log (t₀ + 3) ≤ 61 * (3 + 2 * a) := by nlinarith
  have hA2 : 0 ≤ 49 * A₀ ^ 2 := by positivity
  calc (49 * (1 + 4 / (s * δ₀)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (t₀ + 3))) * δ₀ ^ 3
      = 49 * A₀ ^ 2 * (147 + 12 * Real.log (t₀ + 3)) * ((1 + 4 / (s * δ₀)) ^ 3 * δ₀ ^ 3) := by
        ring
    _ ≤ 49 * A₀ ^ 2 * (61 * (3 + 2 * a)) * (125 / s ^ 3) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hL hA2) hcube (by positivity)
        positivity
    _ = 373625 * A₀ ^ 2 * (3 + 2 * a) / s ^ 3 := by ring

/-- **The balance at a fixed level.** Under even positivity at level `a`, for an off-line zero as in the theorem,
`e^{G/2} ≤ 2e^{5/4} P B_w 303 A₀/(c₀ K_b w²) e^{(6+3M)a}(3+2a)` with `G = (π/2)η^{3/2}e^{2a}`,
`P = 2^{2m} 2M_θ`, `w = η/16`, `K_b = 4w e^{-w/2}∫κ`. -/
theorem landau_level_balance_even {η a A₀ : ℝ} {M : ℕ} (hη0 : 0 < η) (hη2 : η ≤ 1 / 2)
    (ha1 : 1 ≤ a) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hH : EvenHodgeIndexAtLevel zetaZeroConfig a) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (hmM : zetaZeroConfig.mult ρ₀ ≤ M) (hγ : 8 ≤ ρ₀.im)
    (hτ : ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a))) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hdep : ρ₀.re - 1 / 2 ≤ δ / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|)
    (hloss : 12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
      6 * Real.log (1 / (ρ₀.re - 1 / 2)) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a))
    (hbig : 40 + 12 * (M : ℝ) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a)) :
    Real.exp (π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) / 2) ≤
      2 * Real.exp (5 / 4) * (2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst) *
        (373625 * A₀ / (303 * (η / 16)))) * scaledBumpConst (η / 16) * 303 * A₀ /
        (xiNearLineLowerConst * (4 * (η / 16) * (Real.exp (-(η / 16 / 2)) * (∫ u, weilBump u))) *
          (η / 16) ^ 2) * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) := by
  have hpi := Real.pi_pos
  have hsq0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  have hsq1 : Real.sqrt η ≤ 1 := by rw [Real.sqrt_le_one]; linarith
  have hε0 : 0 ≤ Real.sqrt η / 2 := by positivity
  have hθ0 : 0 ≤ π / 4 - Real.sqrt η / 2 := by linarith [Real.pi_gt_three]
  have hθ : 2 * (π / 4 - Real.sqrt η / 2) < π / 2 := by linarith
  have hw0 : 0 < η / 16 := by positivity
  have hmR : (zetaZeroConfig.mult ρ₀ : ℝ) ≤ M := by exact_mod_cast hmM
  -- the gain
  have hgain := landau_gain (L := a) hη0 hη2 hτ
  obtain ⟨G, hG⟩ : ∃ G, G = π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = π * Real.cos (2 * (π / 4 - Real.sqrt η / 2)) *
      Real.exp (2 * (a - η / 8)) := ⟨_, rfl⟩
  rw [← hG, ← hR] at hgain
  rw [← hG] at hloss hbig ⊢
  have hgain' : G - 1 / 4 ≤ R - Real.sqrt η / 2 * (ρ₀.im + 1 / 2) := by linarith
  have hprod0 : 0 ≤ Real.sqrt η / 2 * (ρ₀.im + 1 / 2) := by positivity
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hR1 : 1 ≤ π * Real.cos (2 * (π / 4 - Real.sqrt η / 2)) * Real.exp (2 * (a - η / 8)) := by
    rw [← hR]; linarith
  have hslope : 6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ) ≤
      2 * (π * Real.cos (2 * (π / 4 - Real.sqrt η / 2))) * Real.exp (2 * (a - η / 8)) := by
    have e : 2 * (π * Real.cos (2 * (π / 4 - Real.sqrt η / 2))) * Real.exp (2 * (a - η / 8)) =
        2 * R := by rw [hR]; ring
    rw [e]; linarith
  -- the level bound
  have hlevel := landauPair_level_bound_even hA₀ hloc hθ0 hθ hρ₀ hβ hγ hδ hδ2 hsep hdep
    (U := a - η / 8) (w := η / 16) (s := η / 16) (a := a) hw0 (by linarith) hw0 (by linarith)
    (by linarith) hH hR1 hslope
  rw [← hR] at hlevel
  -- the floor
  obtain ⟨L, hL⟩ : ∃ L, L = 3 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / (δ / 2) :=
    ⟨_, rfl⟩
  have hfloor := dividedKernelFloor_ge_exp (ε := Real.sqrt η / 2) (γ₀ := ρ₀.im) (δ := δ / 2)
    (G := 16 * L) hε0 (by linarith) (by rw [hL]; linarith)
  rw [show 16 * L / 16 = L by ring] at hfloor
  obtain ⟨Kb, hKb⟩ : ∃ Kb, Kb = 4 * (η / 16) * (Real.exp (-(η / 16 / 2)) * (∫ u, weilBump u)) :=
    ⟨_, rfl⟩
  rw [← hKb] at hlevel ⊢
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hKb0 : 0 < Kb := by rw [hKb]; positivity
  have hc₀ := xiNearLineLowerConst_pos
  have hMθ := tiltedPhiTailConst_nonneg
  obtain ⟨P, hP⟩ : ∃ P, P = 2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst) :=
    ⟨_, rfl⟩
  rw [← hP]
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hbound : xiNearLineLowerConst / Real.exp 1 * Real.exp (-(Real.sqrt η / 2 * (ρ₀.im + 1 / 2))) *
      Real.exp (-L) * (ρ₀.im ^ 2 * Kb) ≤
      P * Real.exp ((6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) * (a - η / 8)) * Real.exp (-R) *
        (scaledBumpConst (η / 16) * (1 + ρ₀.im) ^ 2) *
        (49 * (1 + 4 / (η / 16 * |ρ₀.re - 1 / 2|)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (ρ₀.im + 3))) := by
    have h1 := mul_le_mul_of_nonneg_right hfloor (by positivity : (0 : ℝ) ≤ ρ₀.im ^ 2 * Kb)
    refine h1.trans (hlevel.trans (le_of_eq ?_))
    rw [hP]; ring
  have hδ₀ : 0 < ρ₀.re - 1 / 2 := by linarith
  set δ₀ := ρ₀.re - 1 / 2 with hδ₀def
  set δ₁ := δ₀ * Real.sqrt δ₀ with hδ₁def
  have hsq := Real.sq_sqrt hδ₀.le
  have hsqpos := Real.sqrt_pos.2 hδ₀
  have hδ₁ : 0 < δ₁ := mul_pos hδ₀ hsqpos
  have hδ₁sq : δ₁ ^ 2 = δ₀ ^ 3 := by rw [hδ₁def, mul_pow, hsq]; ring
  have hlogδ₁ : 4 * Real.log (1 / δ₁) = 6 * Real.log (1 / δ₀) := by
    have h1 : Real.log (1 / δ₁) = Real.log (1 / δ₀) + Real.log (1 / Real.sqrt δ₀) := by
      rw [hδ₁def, one_div, Real.log_inv, Real.log_mul hδ₀.ne' hsqpos.ne', one_div, Real.log_inv,
        one_div, Real.log_inv]
      ring
    have h2 : Real.log (1 / Real.sqrt δ₀) = Real.log (1 / δ₀) / 2 := by
      rw [one_div, Real.log_inv, Real.log_sqrt hδ₀.le, one_div, Real.log_inv]; ring
    rw [h1, h2]; ring
  have hloss' : 2 * L + 4 * Real.log (1 / δ₁) ≤ G := by
    have e : 2 * L = 12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ := by
      rw [hL]; field_simp; ring
    rw [e, hlogδ₁]; exact hloss
  have hta : ρ₀.im ≤ 2 * π * Real.exp (2 * a) :=
    le_trans hτ (mul_le_of_le_one_left (by positivity) (by linarith))
  have hZb := landauPair_Ze_bound (s := η / 16) (δ₀ := δ₀) (A₀ := A₀) (t₀ := ρ₀.im)
    (a := a) hw0 (by linarith) hδ₀ (by linarith) hA₀ (by linarith) (by linarith) hta
  have hU0 : 0 ≤ a - η / 8 := by linarith
  have hUa : a - η / 8 ≤ a := by linarith
  have ht3 : (3 : ℝ) ≤ ρ₀.im := by linarith
  have hA0 : (0 : ℝ) ≤ A₀ := by linarith
  have hA1 : (0 : ℝ) < A₀ := by linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  set κ := 303 * (η / 16) / (373625 * A₀) with hκ
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  set Z := 49 * (1 + 4 / (η / 16 * |δ₀|)) ^ 3 * A₀ ^ 2 * (147 + 12 * Real.log (ρ₀.im + 3))
    with hZdef
  have hZκ : Z * κ * δ₁ ^ 2 ≤ 303 * A₀ * (3 + 2 * a) / (η / 16) ^ 2 := by
    rw [hδ₁sq]
    calc Z * κ * δ₀ ^ 3 = Z * δ₀ ^ 3 * κ := by ring
      _ ≤ 373625 * A₀ ^ 2 * (3 + 2 * a) / (η / 16) ^ 3 * κ :=
          mul_le_mul_of_nonneg_right hZb hκ0.le
      _ = 303 * A₀ * (3 + 2 * a) / (η / 16) ^ 2 := by rw [hκ]; field_simp
  have hbound' : xiNearLineLowerConst / Real.exp 1 *
      Real.exp (-(Real.sqrt η / 2 * (ρ₀.im + 1 / 2))) * Real.exp (-L) * (ρ₀.im ^ 2 * Kb) ≤
      P * (373625 * A₀ / (303 * (η / 16))) * Real.exp ((6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) *
        (a - η / 8)) * Real.exp (-R) * (scaledBumpConst (η / 16) * (1 + ρ₀.im) ^ 2) * (Z * κ) := by
    refine hbound.trans (le_of_eq ?_)
    rw [hκ]; field_simp
  have hP0' : 0 ≤ P * (373625 * A₀ / (303 * (η / 16))) := by positivity
  exact landauPair_exponent_balance (c₀ := xiNearLineLowerConst) (ε := Real.sqrt η / 2)
    (t₀ := ρ₀.im) (L := L) (K := Kb) (P := P * (373625 * A₀ / (303 * (η / 16))))
    (m := (zetaZeroConfig.mult ρ₀ : ℝ)) (M := (M : ℝ))
    (U := a - η / 8) (a := a) (R := R) (B := scaledBumpConst (η / 16)) (Z := Z * κ)
    (G := G) (δ₀ := δ₁) (A₀ := A₀) (s := η / 16) hc₀ ht3 hKb0 hP0'
    (scaledBumpConst_nonneg hw0) hw0 hδ₁ hmR hU0 hUa (Nat.cast_nonneg _) hA0 ha0 hbound' hgain'
    hloss' hZκ

/-! ## The Nyquist constant for even tests -/

/-- **Even positivity at level `a` excludes off-line zeros up to the Landau height.** For `0 < η ≤ 1/2` and every
multiplicity bound `M` there is `a₀` such that, for `a ≥ a₀`, even Weil positivity at level `a` excludes
every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > 1/2`, `mult ρ₀ ≤ M`,
`8 ≤ t₀ ≤ (1 - η)·2πe^{2a}`, ordinate separation `δ ≤ 1/2` from every zero other than `ρ₀` and
`1 - ρ̄₀`, `β₀ - 1/2 ≤ δ/2`, and `12C log(t₀+1)/δ + 6 log(1/(β₀ - 1/2)) ≤ (π/2)η^{3/2}e^{2a}`. -/
theorem evenHodgeIndex_excludes_offLine_below_landau :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a →
      EvenHodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ₀.re → zetaZeroConfig.mult ρ₀ ≤ M →
      8 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ρ₀.re - 1 / 2 ≤ δ / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
        6 * Real.log (1 / (ρ₀.re - 1 / 2)) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) →
      False := by
  intro η hη0 hη2 M
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hpi := Real.pi_pos
  have hsq0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη0
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = π / 2 * (η * Real.sqrt η) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; positivity
  obtain ⟨Kb, hKb⟩ : ∃ Kb, Kb = 4 * (η / 16) * (Real.exp (-(η / 16 / 2)) * (∫ u, weilBump u)) :=
    ⟨_, rfl⟩
  have hIκ : 0 < ∫ u, weilBump u := weilBump.integral_pos
  have hKb0 : 0 < Kb := by rw [hKb]; positivity
  have hc₀ := xiNearLineLowerConst_pos
  have hMθ := tiltedPhiTailConst_nonneg
  have hBw := scaledBumpConst_nonneg (show (0 : ℝ) < η / 16 by positivity)
  have hA0 : 0 ≤ A₀ := by linarith
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = 2 * Real.exp (5 / 4) * ((4 : ℝ) ^ M * (2 * (tiltedPhiTailConst + 1)) * (373625 * A₀ / (303 * (η / 16)))) *
      scaledBumpConst (η / 16) * 303 * A₀ / (xiNearLineLowerConst * Kb * (η / 16) ^ 2) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; positivity
  obtain ⟨K', hK'⟩ : ∃ K', K' = K₀ + 1 := ⟨_, rfl⟩
  have hK'0 : 0 < K' := by rw [hK']; linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = |Real.log K'| + 12 * (M : ℝ) + 50 := ⟨_, rfl⟩
  have hev := eventually_mul_pow_four_le_exp (K := g / 4) (by positivity) c
  obtain ⟨a₁, ha₁⟩ := Filter.eventually_atTop.mp ((eventually_ge_atTop (1 : ℝ)).and hev)
  refine ⟨a₁, fun a ha hH ρ₀ hρ₀ hβ hmM hγ hτ δ hδ hδ2 hdep hsep hloss => ?_⟩
  obtain ⟨ha1, hpoly⟩ := ha₁ a ha
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hc1 : 50 ≤ c := by rw [hc]; have := abs_nonneg (Real.log K'); linarith
  have hp1 : 1 ≤ (1 + a) ^ 4 := one_le_pow₀ (by linarith)
  have hpa : 1 + a ≤ (1 + a) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hE := Real.exp_pos (2 * a)
  -- the two size conditions
  have hbig : 40 + 12 * (M : ℝ) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) := by
    rw [← hg]
    have h1 : c ≤ c * (1 + a) ^ 4 := le_mul_of_one_le_right (by linarith) hp1
    have h2 : 40 + 12 * (M : ℝ) ≤ c := by rw [hc]; have := abs_nonneg (Real.log K'); linarith
    nlinarith
  have hbal := landau_level_balance_even hη0 hη2 ha1 hA₀ hloc hH hρ₀ hβ hmM hγ hτ hδ hδ2 hdep hsep
    hloss hbig
  rw [← hKb, ← hg] at hbal
  -- the constant does not depend on `ρ₀`
  have hPle : (2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst) ≤
      (4 : ℝ) ^ M * (2 * (tiltedPhiTailConst + 1)) := by
    have h4 : (2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) ≤ (4 : ℝ) ^ M := by
      rw [pow_mul]; norm_num
      exact pow_le_pow_right₀ (by norm_num) hmM
    exact mul_le_mul h4 (by linarith) (by positivity) (by positivity)
  have hup : 2 * Real.exp (5 / 4) * ((2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) *
      (2 * tiltedPhiTailConst) * (373625 * A₀ / (303 * (η / 16)))) * scaledBumpConst (η / 16) * 303 * A₀ /
      (xiNearLineLowerConst * Kb * (η / 16) ^ 2) * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) ≤
      K' * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) := by
    have hden : 0 < xiNearLineLowerConst * Kb * (η / 16) ^ 2 := by positivity
    have h1 : 2 * Real.exp (5 / 4) * ((2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) *
        (2 * tiltedPhiTailConst) * (373625 * A₀ / (303 * (η / 16)))) * scaledBumpConst (η / 16) * 303 * A₀ /
        (xiNearLineLowerConst * Kb * (η / 16) ^ 2) ≤ K' := by
      rw [hK', hK₀]
      have : 2 * Real.exp (5 / 4) * ((2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) *
          (2 * tiltedPhiTailConst) * (373625 * A₀ / (303 * (η / 16)))) * scaledBumpConst (η / 16) * 303 * A₀ /
          (xiNearLineLowerConst * Kb * (η / 16) ^ 2) ≤
          2 * Real.exp (5 / 4) * ((4 : ℝ) ^ M * (2 * (tiltedPhiTailConst + 1)) * (373625 * A₀ / (303 * (η / 16)))) *
          scaledBumpConst (η / 16) * 303 * A₀ / (xiNearLineLowerConst * Kb * (η / 16) ^ 2) := by
        gcongr
      linarith
    have h2 : 0 ≤ Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) := by positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    linarith
  -- the eventual inequality
  have hlogK : Real.log (K' * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a)) < g * Real.exp (2 * a) / 2 := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul hK'0.ne' (Real.exp_pos _).ne',
      Real.log_exp]
    have h1 : Real.log (3 + 2 * a) ≤ 3 + 2 * a := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 + 2 * a by linarith); linarith
    have h2 : Real.log K' ≤ |Real.log K'| := le_abs_self _
    have h3 : Real.log K' + (6 + 3 * (M : ℝ)) * a + Real.log (3 + 2 * a) ≤ c * (1 + a) := by
      rw [hc]
      have := abs_nonneg (Real.log K')
      nlinarith
    have h4 : c * (1 + a) ≤ c * (1 + a) ^ 4 := mul_le_mul_of_nonneg_left hpa (by linarith)
    have h5 : g / 4 * Real.exp (2 * a) < g * Real.exp (2 * a) / 2 := by
      have : 0 < g * Real.exp (2 * a) := by positivity
      linarith
    linarith
  have hlt : K' * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) < Real.exp (g * Real.exp (2 * a) / 2) := by
    have hpos : 0 < K' * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) := by positivity
    rw [← Real.exp_log hpos]
    exact Real.exp_lt_exp.mpr hlogK
  linarith

/-- **Even positivity at level `a` puts separated zeros on the critical line up to the Landau height.** Under the
hypotheses of `evenHodgeIndex_excludes_offLine_below_landau`, stated with `|β₀ - 1/2|`, every such zero
has `β₀ = 1/2`. -/
theorem evenHodgeIndex_forces_critical_line_below_landau :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a →
      EvenHodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, zetaZeroConfig.mult ρ₀ ≤ M →
      8 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → |ρ₀.re - 1 / 2| ≤ δ / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
        6 * Real.log (1 / |ρ₀.re - 1 / 2|) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) →
      ρ₀.re = 1 / 2 := by
  intro η hη0 hη2 M
  obtain ⟨a₀, ha₀⟩ := evenHodgeIndex_excludes_offLine_below_landau η hη0 hη2 M
  refine ⟨a₀, fun a ha hH ρ₀ hρ₀ hmM hγ hτ δ hδ hδ2 hdep hsep hloss => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the mirror zero lies to the right of the line
    set ρ₁ := Zeta23.reflect ρ₀ with hρ₁
    have h₁ : ρ₁ ∈ zetaZeroConfig.carrier := zetaZeroConfig.reflect_mem ρ₀ hρ₀
    have hre : ρ₁.re = 1 - ρ₀.re := by simp [hρ₁, Zeta23.reflect]
    have him : ρ₁.im = ρ₀.im := by simp [hρ₁, Zeta23.reflect]
    have hmult : zetaZeroConfig.mult ρ₁ = zetaZeroConfig.mult ρ₀ :=
      zetaZeroConfig.mult_reflect ρ₀ hρ₀
    have hrr : Zeta23.reflect ρ₁ = ρ₀ := by rw [hρ₁, reflect_reflect]
    have habs : |ρ₀.re - 1 / 2| = ρ₁.re - 1 / 2 := by
      rw [hre, abs_of_neg (by linarith)]; ring
    refine ha₀ a ha hH ρ₁ h₁ (by rw [hre]; linarith) (by rw [hmult]; exact hmM)
      (by rw [him]; exact hγ) (by rw [him]; exact hτ) δ hδ hδ2 (by rw [← habs]; exact hdep)
      (fun ρ hρ h0 h1 => by
        rw [him]; exact hsep ρ hρ (by rw [hrr] at h1; exact h1) h0) ?_
    rw [him, ← habs]; exact hloss
  · have habs : |ρ₀.re - 1 / 2| = ρ₀.re - 1 / 2 := abs_of_pos (by linarith)
    rw [habs] at hdep hloss
    exact ha₀ a ha hH ρ₀ hρ₀ hgt hmM hγ hτ δ hδ hδ2 hdep hsep hloss


end

end RHTower
