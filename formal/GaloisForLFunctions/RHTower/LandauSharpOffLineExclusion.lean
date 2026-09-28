import GaloisForLFunctions.RHTower.LandauPairTest
import GaloisForLFunctions.RHTower.SharpWeilNearRadicalCount

/-!
# The Nyquist constant is `2π`

**Theorem** (`hodgeIndex_excludes_offLine_below_landau`, unconditional). For `0 < η ≤ 1/2` and every
multiplicity bound `M`, there is `a₀` such that for `a ≥ a₀` the level-`a` Hodge index excludes
every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > 1/2`, `mult ρ₀ ≤ M`,
`8 ≤ t₀ ≤ (1 - η) 2πe^{2a}`, ordinate separation `δ ≤ 1/2` from every zero other than `ρ₀` and
`1 - ρ̄₀`, `β₀ - 1/2 ≤ δ/2`, and `12 C log(t₀+1)/δ + 4 log(1/(β₀ - 1/2)) ≤ (π/2)η^{3/2}e^{2a}`.

`2πe^{2a}` is the height where the zero density `(1/2π) log(t/2π)` equals the Nyquist density `a/π`
of tests supported in `[-a, a]`. The off-line lattice pair of that density satisfies Weil
positivity at level `a` (`offLineLattice_weil_positive_iff`), so the constant `2π` cannot be
improved by any argument that sees only the local zero density.

Proof. Take `θ = π/4 - √η/2`, `U = a - η/8`, `w = s = η/16`, and the kernel `h` divided at the pair
(`offLine_pairKernel_package`): `|ĥ(γ_j)| ≥ m_V(θ, t₀, δ/2)`, which is `e^{-(√η/2)t₀}` up to
`exp(-6C log(t₀+1)/δ)` and constants. The Landau test of `h` (`pairLandau_inequality`) gives
`m_V t₀² κ_w ≤ ε_h B_w (1+t₀)² (3 + 12 N² A₀ log(t₀+3))`, where
`ε_h ≤ 2^{2m} 2M e^{(6+3m)U} e^{-π cos(2θ)e^{2U}}` (`landauPair_level_bound`). The exponent gap is
`landau_gain`: `π cos(2θ)e^{2U} - (√η/2)(t₀ + 1/2) ≥ (π/2)η^{3/2}e^{2a} - √η/4`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- **The level bound.** Under Hodge(a), with `U + w + s ≤ a`, an off-line pair as in
`offLine_pairKernel_package` satisfies
`m_V(θ,t₀,δ/2) t₀² 4w e^{-w/2}∫κ ≤ 2^{2m}(2M e^{(6+3m)U}e^{-π cos(2θ)e^{2U}}) B_w (1+t₀)²
(3 + 12(1 + 4/(s(β₀-1/2)))² A₀ log(t₀+3))`. -/
theorem landauPair_level_bound {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : 2 * θ < π / 2) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (hγ : 8 ≤ ρ₀.im) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|) (hdep : ρ₀.re - 1 / 2 ≤ δ / 2)
    {U w s a : ℝ} (hw : 0 < w) (hw4 : 4 * w ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1)
    (ha : U + w + s ≤ a) (hH : HodgeIndexAtLevel zetaZeroConfig a)
    (hrate : 1 ≤ π * Real.cos (2 * θ) * Real.exp (2 * U))
    (hslope : 6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ) ≤
      2 * (π * Real.cos (2 * θ)) * Real.exp (2 * U)) :
    dividedKernelFloor θ ρ₀.im (δ / 2) *
        (ρ₀.im ^ 2 * (4 * w * (Real.exp (-(w / 2)) * (∫ u, weilBump u)))) ≤
      (2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst *
        Real.exp ((6 + 3 * (zetaZeroConfig.mult ρ₀ : ℝ)) * U) *
        Real.exp (-(π * Real.cos (2 * θ) * Real.exp (2 * U))))) *
      (scaledBumpConst w * (1 + ρ₀.im) ^ 2) *
      (3 + 12 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 2 * A₀ * Real.log (ρ₀.im + 3)) := by
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
  have hpair := pairLandau_inequality hA₀ hloc hθ0 hθ hρ₀ hoff (by linarith) hK hprod hw hw4
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
  have hZ0 : 0 ≤ 3 + 12 * (1 + 4 / (s * |ρ₀.re - 1 / 2|)) ^ 2 * A₀ * Real.log (t₀ + 3) := by
    have : 0 ≤ Real.log (t₀ + 3) := Real.log_nonneg (by linarith)
    positivity
  have hBw0 : 0 ≤ scaledBumpConst w * (1 + t₀) ^ 2 := by
    have := scaledBumpConst_nonneg hw; positivity
  refine hpair.trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hεt hBw0) hZ0

/-- **The exponent balance.** If
`(c₀/e) e^{-ε(t₀+1/2)} e^{-L} t₀² K ≤ P e^{(6+3m)U} e^{-R} B (1+t₀)² Z` with
`R - ε(t₀+1/2) ≥ G - 1/4`, `2L + 4 log(1/δ₀) ≤ G`, `Z δ₀² ≤ 303 A₀ (3+2a)/s²` and `m ≤ M`,
`0 ≤ U ≤ a`, then `e^{G/2} ≤ P' e^{(6+3M)a}(3+2a)` with `P' = 2e^{5/4} P B 303 A₀/(c₀ K s²)`. -/
theorem landauPair_exponent_balance {c₀ ε t₀ L K P m M U a R B Z G δ₀ A₀ s : ℝ}
    (hc₀ : 0 < c₀) (ht₀ : 3 ≤ t₀) (hK : 0 < K) (hP : 0 ≤ P) (hB : 0 ≤ B) (hs : 0 < s)
    (hδ₀ : 0 < δ₀) (hmM : m ≤ M) (hU0 : 0 ≤ U) (hUa : U ≤ a) (hm0 : 0 ≤ m)
    (hA₀ : 0 ≤ A₀) (ha : 0 ≤ a)
    (hbound : c₀ / Real.exp 1 * Real.exp (-(ε * (t₀ + 1 / 2))) * Real.exp (-L) * (t₀ ^ 2 * K) ≤
      P * Real.exp ((6 + 3 * m) * U) * Real.exp (-R) * (B * (1 + t₀) ^ 2) * Z)
    (hgain : G - 1 / 4 ≤ R - ε * (t₀ + 1 / 2))
    (hloss : 2 * L + 4 * Real.log (1 / δ₀) ≤ G)
    (hZ : Z * δ₀ ^ 2 ≤ 303 * A₀ * (3 + 2 * a) / s ^ 2) :
    Real.exp (G / 2) ≤ 2 * Real.exp (5 / 4) * P * B * 303 * A₀ / (c₀ * K * s ^ 2) *
      Real.exp ((6 + 3 * M) * a) * (3 + 2 * a) := by
  have hE1 := Real.exp_pos 1
  have ht0 : 0 < 1 + t₀ := by linarith
  have ht2 : (1 + t₀) ^ 2 ≤ 2 * t₀ ^ 2 := by nlinarith
  -- rewrite `e^{-L}` through the loss
  have hlogδ : Real.exp (2 * Real.log (1 / δ₀)) = 1 / δ₀ ^ 2 := by
    rw [show 2 * Real.log (1 / δ₀) = Real.log ((1 / δ₀) ^ 2) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    ring
  have hL : Real.exp (-(G / 2)) / δ₀ ^ 2 ≤ Real.exp (-L) := by
    rw [← mul_one_div, ← hlogδ, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hΩ : Real.exp (G - 1 / 4) ≤ Real.exp R * Real.exp (-(ε * (t₀ + 1 / 2))) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hU : Real.exp ((6 + 3 * m) * U) ≤ Real.exp ((6 + 3 * M) * a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  -- multiply the bound by `e^R δ₀²/(1+t₀)²`
  set LHS := c₀ / Real.exp 1 * Real.exp (-(ε * (t₀ + 1 / 2))) * Real.exp (-L) * (t₀ ^ 2 * K)
    with hLHS
  set RHS := P * Real.exp ((6 + 3 * m) * U) * Real.exp (-R) * (B * (1 + t₀) ^ 2) * Z with hRHS
  have hR : Real.exp R * Real.exp (-R) = 1 := by rw [← Real.exp_add]; simp
  have hlow : c₀ * K / (2 * Real.exp (5 / 4)) * Real.exp (G / 2) * ((1 + t₀) ^ 2 / δ₀ ^ 2) ≤
      Real.exp R * LHS := by
    have h1 : Real.exp R * LHS = c₀ / Real.exp 1 * (Real.exp R * Real.exp (-(ε * (t₀ + 1 / 2)))) *
        Real.exp (-L) * (t₀ ^ 2 * K) := by rw [hLHS]; ring
    rw [h1]
    have h2 : c₀ * K / (2 * Real.exp (5 / 4)) * Real.exp (G / 2) * ((1 + t₀) ^ 2 / δ₀ ^ 2) ≤
        c₀ / Real.exp 1 * Real.exp (G - 1 / 4) * (Real.exp (-(G / 2)) / δ₀ ^ 2) *
          (t₀ ^ 2 * K) := by
      have e : Real.exp (G - 1 / 4) * Real.exp (-(G / 2)) =
          Real.exp (G / 2) / Real.exp (1 / 4) := by
        rw [← Real.exp_add, ← Real.exp_sub]; ring_nf
      have e2 : Real.exp (5 / 4) = Real.exp 1 * Real.exp (1 / 4) := by
        rw [← Real.exp_add]; norm_num
      rw [show c₀ / Real.exp 1 * Real.exp (G - 1 / 4) * (Real.exp (-(G / 2)) / δ₀ ^ 2) *
          (t₀ ^ 2 * K) = c₀ / Real.exp 1 * (Real.exp (G - 1 / 4) * Real.exp (-(G / 2))) / δ₀ ^ 2 *
          (t₀ ^ 2 * K) by ring, e, e2]
      have hE14 := Real.exp_pos (1 / 4)
      have hG := Real.exp_pos (G / 2)
      rw [div_le_iff₀ (by positivity)] at *
      field_simp
      have : (1 + t₀) ^ 2 * K ≤ 2 * t₀ ^ 2 * K := mul_le_mul_of_nonneg_right ht2 hK.le
      nlinarith [mul_pos hc₀ hG, mul_pos (mul_pos hc₀ hG) hE1, mul_pos hE14 hE1]
    refine h2.trans ?_
    gcongr
  have hup : Real.exp R * RHS ≤ P * Real.exp ((6 + 3 * M) * a) * B * ((1 + t₀) ^ 2 / δ₀ ^ 2) *
      (303 * A₀ * (3 + 2 * a) / s ^ 2) := by
    have h1 : Real.exp R * RHS = P * Real.exp ((6 + 3 * m) * U) * (Real.exp R * Real.exp (-R)) *
        B * (1 + t₀) ^ 2 * Z := by rw [hRHS]; ring
    rw [h1, hR, mul_one]
    have hZ' : Z ≤ 303 * A₀ * (3 + 2 * a) / s ^ 2 / δ₀ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; exact hZ
    have hZ0 : 0 ≤ Z ∨ Z < 0 := le_or_gt 0 Z
    calc P * Real.exp ((6 + 3 * m) * U) * B * (1 + t₀) ^ 2 * Z
        ≤ P * Real.exp ((6 + 3 * M) * a) * B * (1 + t₀) ^ 2 *
            (303 * A₀ * (3 + 2 * a) / s ^ 2 / δ₀ ^ 2) := by
          rcases hZ0 with hz | hz
          · gcongr
          · have : P * Real.exp ((6 + 3 * m) * U) * B * (1 + t₀) ^ 2 * Z ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) hz.le
            have : 0 ≤ P * Real.exp ((6 + 3 * M) * a) * B * (1 + t₀) ^ 2 *
                (303 * A₀ * (3 + 2 * a) / s ^ 2 / δ₀ ^ 2) := by positivity
            linarith
      _ = _ := by ring
  have hbound' : Real.exp R * LHS ≤ Real.exp R * RHS :=
    mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
  have hchain := hlow.trans (hbound'.trans hup)
  have hq : 0 < (1 + t₀) ^ 2 / δ₀ ^ 2 := by positivity
  have hck : 0 < c₀ * K / (2 * Real.exp (5 / 4)) := by positivity
  have h3 : c₀ * K / (2 * Real.exp (5 / 4)) * Real.exp (G / 2) ≤
      P * Real.exp ((6 + 3 * M) * a) * B * (303 * A₀ * (3 + 2 * a) / s ^ 2) := by
    have := hchain
    rw [show P * Real.exp ((6 + 3 * M) * a) * B * ((1 + t₀) ^ 2 / δ₀ ^ 2) *
      (303 * A₀ * (3 + 2 * a) / s ^ 2) = (P * Real.exp ((6 + 3 * M) * a) * B *
      (303 * A₀ * (3 + 2 * a) / s ^ 2)) * ((1 + t₀) ^ 2 / δ₀ ^ 2) by ring] at this
    exact le_of_mul_le_mul_right this hq
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h3
  rw [show 2 * Real.exp (5 / 4) * P * B * 303 * A₀ / (c₀ * K * s ^ 2) *
    Real.exp ((6 + 3 * M) * a) * (3 + 2 * a) = (P * Real.exp ((6 + 3 * M) * a) * B *
    (303 * A₀ * (3 + 2 * a) / s ^ 2)) * (2 * Real.exp (5 / 4)) / (c₀ * K) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- The bound on the `N`-factor: `Z δ₀² ≤ 303 A₀ (3+2a)/s²` for
`Z = 3 + 12(1 + 4/(sδ₀))² A₀ log(t₀+3)`, `0 < δ₀ ≤ 1/4`, `0 < s ≤ 1`, `t₀ ≤ 2πe^{2a}`. -/
theorem landauPair_Z_bound {s δ₀ A₀ t₀ a : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hδ₀ : 0 < δ₀)
    (hδ₀4 : δ₀ ≤ 1 / 4) (hA₀ : 1 ≤ A₀) (ht₀ : 0 ≤ t₀) (ha : 0 ≤ a)
    (hta : t₀ ≤ 2 * π * Real.exp (2 * a)) :
    (3 + 12 * (1 + 4 / (s * |δ₀|)) ^ 2 * A₀ * Real.log (t₀ + 3)) * δ₀ ^ 2 ≤
      303 * A₀ * (3 + 2 * a) / s ^ 2 := by
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
  have hsq : (1 + 4 / (s * δ₀)) ^ 2 * δ₀ ^ 2 ≤ 25 / s ^ 2 := by
    have e : (1 + 4 / (s * δ₀)) * δ₀ = δ₀ + 4 / s := by field_simp
    have h1 : δ₀ + 4 / s ≤ 5 / s := by
      have : δ₀ ≤ 1 / s := by
        rw [le_div_iff₀ hs]; nlinarith
      have e2 : 5 / s = 1 / s + 4 / s := by ring
      linarith
    have h0 : 0 ≤ δ₀ + 4 / s := by positivity
    calc (1 + 4 / (s * δ₀)) ^ 2 * δ₀ ^ 2 = (δ₀ + 4 / s) ^ 2 := by rw [← e]; ring
      _ ≤ (5 / s) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 25 / s ^ 2 := by ring
  have hd2 : 3 * δ₀ ^ 2 ≤ 3 / s ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : δ₀ ^ 2 * s ^ 2 ≤ 1 := by
      have h1 : δ₀ ^ 2 ≤ 1 := by nlinarith
      have h2 : s ^ 2 ≤ 1 := by nlinarith
      calc δ₀ ^ 2 * s ^ 2 ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = 1 := one_mul 1
    linarith
  have hmain : 12 * (1 + 4 / (s * δ₀)) ^ 2 * A₀ * Real.log (t₀ + 3) * δ₀ ^ 2 ≤
      300 * A₀ * (3 + 2 * a) / s ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 12 * A₀ * Real.log (t₀ + 3))
    have e : 12 * A₀ * Real.log (t₀ + 3) * ((1 + 4 / (s * δ₀)) ^ 2 * δ₀ ^ 2) =
        12 * (1 + 4 / (s * δ₀)) ^ 2 * A₀ * Real.log (t₀ + 3) * δ₀ ^ 2 := by ring
    rw [e] at this
    refine this.trans ?_
    rw [show 12 * A₀ * Real.log (t₀ + 3) * (25 / s ^ 2) = 300 * A₀ * Real.log (t₀ + 3) / s ^ 2 by
      ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hA0 : 0 ≤ A₀ := by linarith
    nlinarith
  have hfin : 3 / s ^ 2 + 300 * A₀ * (3 + 2 * a) / s ^ 2 ≤ 303 * A₀ * (3 + 2 * a) / s ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  nlinarith

/-- **The balance at a fixed level.** Under Hodge(a), for an off-line zero as in the theorem,
`e^{G/2} ≤ 2e^{5/4} P B_w 303 A₀/(c₀ K_b w²) e^{(6+3M)a}(3+2a)` with `G = (π/2)η^{3/2}e^{2a}`,
`P = 2^{2m} 2M_θ`, `w = η/16`, `K_b = 4w e^{-w/2}∫κ`. -/
theorem landau_level_balance {η a A₀ : ℝ} {M : ℕ} (hη0 : 0 < η) (hη2 : η ≤ 1 / 2)
    (ha1 : 1 ≤ a) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hH : HodgeIndexAtLevel zetaZeroConfig a) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ zetaZeroConfig.carrier)
    (hβ : 1 / 2 < ρ₀.re) (hmM : zetaZeroConfig.mult ρ₀ ≤ M) (hγ : 8 ≤ ρ₀.im)
    (hτ : ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a))) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hdep : ρ₀.re - 1 / 2 ≤ δ / 2)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ →
      δ ≤ |ρ.im - ρ₀.im|)
    (hloss : 12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
      4 * Real.log (1 / (ρ₀.re - 1 / 2)) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a))
    (hbig : 40 + 12 * (M : ℝ) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a)) :
    Real.exp (π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) / 2) ≤
      2 * Real.exp (5 / 4) * (2 ^ (2 * zetaZeroConfig.mult ρ₀) * (2 * tiltedPhiTailConst)) *
        scaledBumpConst (η / 16) * 303 * A₀ /
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
  have hlevel := landauPair_level_bound hA₀ hloc hθ0 hθ hρ₀ hβ hγ hδ hδ2 hsep hdep
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
        (3 + 12 * (1 + 4 / (η / 16 * |ρ₀.re - 1 / 2|)) ^ 2 * A₀ * Real.log (ρ₀.im + 3)) := by
    have h1 := mul_le_mul_of_nonneg_right hfloor (by positivity : (0 : ℝ) ≤ ρ₀.im ^ 2 * Kb)
    refine h1.trans (hlevel.trans (le_of_eq ?_))
    rw [hP]; ring
  have hloss' : 2 * L + 4 * Real.log (1 / (ρ₀.re - 1 / 2)) ≤ G := by
    have e : 2 * L = 12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ := by
      rw [hL]; field_simp; ring
    rw [e]; exact hloss
  have hδ₀ : 0 < ρ₀.re - 1 / 2 := by linarith
  have hta : ρ₀.im ≤ 2 * π * Real.exp (2 * a) :=
    le_trans hτ (mul_le_of_le_one_left (by positivity) (by linarith))
  have hZb := landauPair_Z_bound (s := η / 16) (δ₀ := ρ₀.re - 1 / 2) (A₀ := A₀) (t₀ := ρ₀.im)
    (a := a) hw0 (by linarith) hδ₀ (by linarith) hA₀ (by linarith) (by linarith) hta
  have hU0 : 0 ≤ a - η / 8 := by linarith
  have hUa : a - η / 8 ≤ a := by linarith
  have ht3 : (3 : ℝ) ≤ ρ₀.im := by linarith
  have hA0 : (0 : ℝ) ≤ A₀ := by linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  exact landauPair_exponent_balance (c₀ := xiNearLineLowerConst) (ε := Real.sqrt η / 2)
    (t₀ := ρ₀.im) (L := L) (K := Kb) (P := P) (m := (zetaZeroConfig.mult ρ₀ : ℝ)) (M := (M : ℝ))
    (U := a - η / 8) (a := a) (R := R) (B := scaledBumpConst (η / 16))
    (Z := 3 + 12 * (1 + 4 / (η / 16 * |ρ₀.re - 1 / 2|)) ^ 2 * A₀ * Real.log (ρ₀.im + 3))
    (G := G) (δ₀ := ρ₀.re - 1 / 2) (A₀ := A₀) (s := η / 16) hc₀ ht3 hKb0 hP0
    (scaledBumpConst_nonneg hw0) hw0 hδ₀ hmR hU0 hUa (Nat.cast_nonneg _) hA0 ha0 hbound hgain'
    hloss' hZb

/-! ## The Nyquist constant -/

/-- **Hodge(a) excludes off-line zeros up to the Landau height.** For `0 < η ≤ 1/2` and every
multiplicity bound `M` there is `a₀` such that, for `a ≥ a₀`, the level-`a` Hodge index excludes
every nontrivial zero `ρ₀ = β₀ + it₀` with `β₀ > 1/2`, `mult ρ₀ ≤ M`,
`8 ≤ t₀ ≤ (1 - η)·2πe^{2a}`, ordinate separation `δ ≤ 1/2` from every zero other than `ρ₀` and
`1 - ρ̄₀`, `β₀ - 1/2 ≤ δ/2`, and `12C log(t₀+1)/δ + 4 log(1/(β₀ - 1/2)) ≤ (π/2)η^{3/2}e^{2a}`. -/
theorem hodgeIndex_excludes_offLine_below_landau :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a →
      HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, 1 / 2 < ρ₀.re → zetaZeroConfig.mult ρ₀ ≤ M →
      8 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ρ₀.re - 1 / 2 ≤ δ / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
        4 * Real.log (1 / (ρ₀.re - 1 / 2)) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) →
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
  obtain ⟨K₀, hK₀⟩ : ∃ K₀, K₀ = 2 * Real.exp (5 / 4) * ((4 : ℝ) ^ M * (2 * (tiltedPhiTailConst + 1))) *
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
  have hbal := landau_level_balance hη0 hη2 ha1 hA₀ hloc hH hρ₀ hβ hmM hγ hτ hδ hδ2 hdep hsep
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
      (2 * tiltedPhiTailConst)) * scaledBumpConst (η / 16) * 303 * A₀ /
      (xiNearLineLowerConst * Kb * (η / 16) ^ 2) * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) ≤
      K' * Real.exp ((6 + 3 * (M : ℝ)) * a) * (3 + 2 * a) := by
    have hden : 0 < xiNearLineLowerConst * Kb * (η / 16) ^ 2 := by positivity
    have h1 : 2 * Real.exp (5 / 4) * ((2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) *
        (2 * tiltedPhiTailConst)) * scaledBumpConst (η / 16) * 303 * A₀ /
        (xiNearLineLowerConst * Kb * (η / 16) ^ 2) ≤ K' := by
      rw [hK', hK₀]
      have : 2 * Real.exp (5 / 4) * ((2 : ℝ) ^ (2 * zetaZeroConfig.mult ρ₀) *
          (2 * tiltedPhiTailConst)) * scaledBumpConst (η / 16) * 303 * A₀ /
          (xiNearLineLowerConst * Kb * (η / 16) ^ 2) ≤
          2 * Real.exp (5 / 4) * ((4 : ℝ) ^ M * (2 * (tiltedPhiTailConst + 1))) *
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

/-- **Hodge(a) puts separated zeros on the critical line up to the Landau height.** Under the
hypotheses of `hodgeIndex_excludes_offLine_below_landau`, stated with `|β₀ - 1/2|`, every such zero
has `β₀ = 1/2`. -/
theorem hodgeIndex_forces_critical_line_below_landau :
    ∀ η : ℝ, 0 < η → η ≤ 1 / 2 → ∀ M : ℕ, ∃ a₀ : ℝ, ∀ a : ℝ, a₀ ≤ a →
      HodgeIndexAtLevel zetaZeroConfig a →
      ∀ ρ₀ ∈ zetaZeroConfig.carrier, zetaZeroConfig.mult ρ₀ ≤ M →
      8 ≤ ρ₀.im → ρ₀.im ≤ (1 - η) * (2 * π * Real.exp (2 * a)) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → |ρ₀.re - 1 / 2| ≤ δ / 2 →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ ≠ ρ₀ → ρ ≠ Zeta23.reflect ρ₀ → δ ≤ |ρ.im - ρ₀.im|) →
      12 * logDerivZetaConstant * Real.log (ρ₀.im + 1) / δ +
        4 * Real.log (1 / |ρ₀.re - 1 / 2|) ≤ π / 2 * (η * Real.sqrt η) * Real.exp (2 * a) →
      ρ₀.re = 1 / 2 := by
  intro η hη0 hη2 M
  obtain ⟨a₀, ha₀⟩ := hodgeIndex_excludes_offLine_below_landau η hη0 hη2 M
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
