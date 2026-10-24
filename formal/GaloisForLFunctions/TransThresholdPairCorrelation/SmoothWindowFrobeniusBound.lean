import GaloisForLFunctions.TransThresholdPairCorrelation.SmoothWindowProfile

/-!
# The Smooth-Window Frobenius Bound at One Height

For a window profile `u` with collar `ε₁`, the weighted Frobenius sum of the Gram matrix of `ν_X`
with grid weights `u_T(τ_k)²` is bounded at every height `T ≥ 2π` with `ε₁T ≥ 5` by
`L² (∫Φ² ∫_T^{2T} μ² + π⁻¹ T Σ a_n² g(log n) + coalSum + channelError) + gridError`
(`weightedFrobenius_le`): the grid comparison (`abs_weightedFrobenius_sub_smoothForm_le`), Fubini
for `ν_X` of logarithmic growth, and the nine channels (`smoothPair_nuX_le`) applied to the window
`Ω_T = u_T⁴`. The lattice deficit enters through
`ρ ≤ (c_ϱ/w)² (3 + 1/h)/(ε₁T − 1)³` on `[T + ε₁T, 2T − ε₁T]` (`rho_le_profile`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction

open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ε₁ : ℝ} {u : ℝ → ℝ}

/-- The deficit radius at distance `D` from the window ends. -/
def deficitRadius (cϱ : ℝ) (p : Setting) (D : ℝ) : ℝ :=
  cϱ / p.w * Real.sqrt ((3 + 1 / p.h) / (D - 1) ^ 3)

theorem rho_le_profile (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {D : ℝ} (hD : 2 ≤ D) {τ : ℝ}
    (hτ : τ ∈ Icc (p.T + D) (2 * p.T - D)) : rho p F τ ≤ deficitRadius cϱ p D ^ 2 := by
  have hh := h_pos hF
  have hD1 : 1 ≤ D - 1 := by linarith
  have h3 : 0 < (D - 1) ^ 3 := by positivity
  have hcube : (D - 1) ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have a1 : 2 / D ^ 4 ≤ 2 / (D - 1) ^ 3 := by
    apply div_le_div_of_nonneg_left (by norm_num) h3
    nlinarith [pow_pos (by linarith : (0:ℝ) < D) 3]
  have a2 : 2 / (3 * p.h * D ^ 3) ≤ (1 / p.h) / (D - 1) ^ 3 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hcube hh.le]
  have a3 : 1 / (D - 1) ^ 4 ≤ 1 / (D - 1) ^ 3 := by
    apply one_div_le_one_div_of_le h3
    calc (D - 1) ^ 3 = (D - 1) ^ 3 * 1 := by ring
      _ ≤ (D - 1) ^ 3 * (D - 1) := mul_le_mul_of_nonneg_left hD1 h3.le
      _ = (D - 1) ^ 4 := by ring
  have e : (3 + 1 / p.h) / (D - 1) ^ 3 = 2 / (D - 1) ^ 3 + (1 / p.h) / (D - 1) ^ 3
      + 1 / (D - 1) ^ 3 := by ring
  calc rho p F τ ≤ (cϱ / p.w) ^ 2 * (2 / D ^ 4 + 2 / (3 * p.h * D ^ 3) + 1 / (D - 1) ^ 4) :=
        rho_le_of_dist hF hT hD hτ
    _ ≤ (cϱ / p.w) ^ 2 * ((3 + 1 / p.h) / (D - 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (by rw [e]; linarith) (sq_nonneg _)
    _ = deficitRadius cϱ p D ^ 2 := by
        unfold deficitRadius
        rw [mul_pow, Real.sq_sqrt (by positivity)]

theorem deficitRadius_pos (hF : LocalHypsCoreW cϱ p F) {D : ℝ} (hD : 2 ≤ D) :
    0 < deficitRadius cϱ p D := by
  have hh := h_pos hF
  have hc := hF.four_le_cϱ
  have hw := hF.one_le_w
  unfold deficitRadius
  have : 0 < (3 + 1 / p.h) / (D - 1) ^ 3 := by
    have : 0 < D - 1 := by linarith
    positivity
  have := Real.sqrt_pos.mpr this
  have : 0 < cϱ / p.w := by positivity
  positivity

theorem sum_acoef_sq_mul_eq_sumA2g (X : ℝ) (g : ℝ → ℝ) :
    ∑ n ∈ primeRange X, acoef n ^ 2 * g (Real.log n) = sumA2g X g := by
  unfold sumA2g
  exact Finset.sum_congr rfl fun n _ => by rw [acoef_sq]

/-- **The smooth-window Frobenius bound at one height.** -/
theorem weightedFrobenius_le (hF : LocalHypsCoreW cϱ p F) (hT : 2 * π ≤ p.T)
    (hu : WindowProfile ε₁ u) {ℓ₀ : ℝ} (hℓ₀ : 0 ≤ ℓ₀) (hlip : ∀ s t, |u s - u t| ≤ ℓ₀ * |s - t|)
    (hℓ1 : 2 * ℓ₀ / p.T ≤ 1) (hD : 5 ≤ ε₁ * p.T) {k : ℕ}
    {K : ℝ} (hK : 0 ≤ K)
    (hμinc : ∀ t, 2 ≤ t → ∀ r, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hμ : NuBound p (C₀ * p.l) Zeta23.mu) (hν : NuBound p (Bconst p) (Zeta23.nuX p.X))
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, gridW p (profileW u p.T) k * gridW p (profileW u p.T) l
        * GentryNu (Zeta23.nuX p.X) p F k l ^ 2
      ≤ p.L ^ 2 * ((∫ x, F.Phi x ^ 2) * (∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2)
          + (1 / π) * p.T * sumA2g p.X F.g
          + coalSum (profileΩ u p.T) F.g p.X θ₀
          + channelError (∑ n ∈ primeRange p.X, acoef n)
            (K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2)
            ((∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x|) (∫ x, F.Phi x ^ 2)
            ((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T)) (p.T + ε₁ * p.T) p.L p.l
            ((1 / 2) * (((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T) + 5)
              * (4 * ℓ₀ / p.T * 5 * p.l + (K * 5 + 10 * 5 ^ 2) / (p.T + ε₁ * p.T))))
            (∫ τ in (p.T + ε₁ * p.T - 1)..(2 * p.T - ε₁ * p.T + 1),
              |iteratedDeriv k (profileΩ u p.T) τ|) θ₀ p.X
            (∫ τ, profileΩ u p.T τ * Zeta23.PX p.X τ ^ 2)
            (∫ τ, profileΩ u p.T τ * primeDirichletCos F.g p.X τ ^ 2) k)
        + (p.L ^ 2 * (p.L + cϱ / p.w) ^ 2
            * (π * (40 * π * Real.sqrt (2 * ℓ₀ / p.T) / p.h + 32 * p.d / (9 * p.T ^ 2))
              + 2 * π * Real.sqrt (2 * ℓ₀ / p.T) * (20 * π / p.h + 32 * p.d / (9 * p.T ^ 2)))
            * (∫ τ, lorentzW p.T (3 * p.T / 2) τ * Zeta23.nuX p.X τ ^ 2)
          + p.L * deficitRadius cϱ p (ε₁ * p.T) * Bconst p
            * (π * Bconst p + ∫ r, lor1 r * Real.sqrt |r|)
            * ((p.L + cϱ / p.w) ^ 2 * (p.d * π)
              + p.L * (p.L + cϱ / p.w) * ((2 * p.T - ε₁ * p.T) - (p.T + ε₁ * p.T)))) := by
  have hT0 : 0 < p.T := by linarith [Real.pi_pos]
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hε := hu.pos
  have hε8 := hu.le
  set s₀ := p.T + ε₁ * p.T with hs₀
  set s₁ := 2 * p.T - ε₁ * p.T with hs₁
  have hεT : ε₁ * p.T ≤ p.T / 8 := by nlinarith
  have hs : s₀ ≤ s₁ := by rw [hs₀, hs₁]; linarith
  have hS₀ : p.T ≤ s₀ := by rw [hs₀]; nlinarith
  have hS₁ : s₁ ≤ 2 * p.T := by rw [hs₁]; nlinarith
  have hB0 : 0 ≤ Bconst p := by
    unfold Bconst; have := hF.one_le_l; positivity
  -- the height weight and the window
  have hℓpos : 0 ≤ 2 * ℓ₀ / p.T := by positivity
  set W := profileW u p.T with hW
  set Ω := profileΩ u p.T with hΩ
  have hWh := heightWeight_profileW hu hlip hT0
  have hWS : ∀ τ, τ ∉ Icc s₀ s₁ → W τ = 0 := fun τ hτ => by
    rw [hW]; unfold profileW; rw [profileU_eq_zero hu hT0 hτ]; norm_num
  have hΩS : ∀ τ, τ ∉ Icc s₀ s₁ → Ω τ = 0 := fun τ hτ => by
    rw [hΩ]; unfold profileΩ; rw [profileU_eq_zero hu hT0 hτ]; norm_num
  -- the comparison step
  have hD2 : 2 ≤ ε₁ * p.T := by linarith
  have hρ : ∀ τ ∈ Icc s₀ s₁, rho p F τ ≤ deficitRadius cϱ p (ε₁ * p.T) ^ 2 := fun τ hτ =>
    rho_le_profile hF hT0 hD2 hτ
  by_cases hℓz : ℓ₀ = 0
  · -- a constant-free profile is impossible: `u = 0` near `0` and `u = 1` on the bulk
    exfalso
    have h1 := hu.one_of (1 / 2) ⟨by linarith, by linarith⟩
    have h0 := hu.zero_of 0 (fun h => by linarith [h.1])
    have := hlip (1 / 2) 0
    rw [h1, h0, hℓz] at this
    norm_num at this
  have hℓ0 : 0 < 2 * ℓ₀ / p.T := by
    have : 0 < ℓ₀ := lt_of_le_of_ne hℓ₀ (Ne.symm hℓz)
    positivity
  have hμc : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  have hνc : Continuous (Zeta23.nuX p.X) := by
    have h := (hμc.add hF.PiX_cont).add (continuous_PX' p.X)
    exact h
  have hcomp := abs_weightedFrobenius_sub_smoothForm_le hF hT hℓ0 hℓ1 hWh hs hS₀ hS₁ hWS
    (deficitRadius_pos hF hD2) hρ hνc hB0 hν
  -- the smooth form is the iterated form
  have hWΩ : (fun τ => W τ ^ 2) = Ω := by funext τ; rw [hΩ, hW, profileΩ_eq_sq]
  rw [hWΩ] at hcomp
  have hΩk : ∀ j : ℕ, ContDiff ℝ j Ω := fun j => contDiff_profileΩ hu p.T j
  have hΩc : Continuous Ω := (hΩk 0).continuous
  have hΩ0 : ∀ τ, 0 ≤ Ω τ := fun τ => by rw [hΩ]; unfold profileΩ; positivity
  have hΩ1 : ∀ τ, Ω τ ≤ 1 := fun τ => by
    rw [hΩ]; unfold profileΩ; exact pow_le_one₀ (hu.nonneg _) (hu.le_one _)
  have hgrowth : ∀ τ τ', Ω τ ≠ 0 → |Zeta23.nuX p.X τ'| ≤ (Bconst p + 1) * (1 + |τ - τ'|) := by
    intro τ τ' hτ
    have hτS : τ ∈ Icc s₀ s₁ := by by_contra h; exact hτ (hΩS τ h)
    have h := abs_le_of_nuBound hν hT1 ⟨hS₀.trans hτS.1, hτS.2.trans hS₁⟩ τ'
    have hsq : Real.sqrt |τ' - τ| ≤ 1 + |τ - τ'| := by
      rw [abs_sub_comm]
      refine (Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (τ - τ')] :
        |τ - τ'| ≤ (1 + |τ - τ'|) ^ 2)).trans ?_
      rw [Real.sqrt_sq (by positivity)]
    have hr := abs_nonneg (τ - τ')
    calc |Zeta23.nuX p.X τ'| ≤ Bconst p + (1 + |τ - τ'|) := by linarith
      _ ≤ (Bconst p + 1) * (1 + |τ - τ'|) := by
          have h4 := mul_nonneg hB0 hr
          have e : (Bconst p + 1) * (1 + |τ - τ'|) = Bconst p + (1 + |τ - τ'|) + Bconst p * |τ - τ'| := by
            ring
          linarith
  have hΩν : Integrable fun τ => Ω τ * Zeta23.nuX p.X τ := integrable_window_mul hΩc hΩS hνc
  have hFub := smoothForm_eq_smoothPair (Φ := F.Phi) hF.Phi_contDiff.continuous hF.Phi_sq_integrable
    hF.Phi_sq_mul_abs_integrable hΩc hνc hνc hΩν hgrowth
  -- the nine channels
  have hs₀2 : 2 ≤ s₀ := by rw [hs₀]; nlinarith [Real.pi_gt_three]
  have hΩL : ∀ s t, |Ω s - Ω t| ≤ 4 * ℓ₀ / p.T * |s - t| := abs_profileΩ_sub_le hu hlip hT0
  have hμM : ∀ τ ∈ Icc s₀ (s₁ + 5), |Zeta23.mu τ| ≤ p.l := fun τ hτ =>
    hμl τ ⟨hS₀.trans hτ.1, by rw [hs₁] at hτ; linarith [hτ.2]⟩
  have hμg : ∀ τ τ', Ω τ ≠ 0 → |Zeta23.mu τ'| ≤ (C₀ * p.l + 1) * (1 + |τ - τ'|) := by
    intro τ τ' hτ
    have hτS : τ ∈ Icc s₀ s₁ := by by_contra h; exact hτ (hΩS τ h)
    have h := abs_le_of_nuBound hμ hT1 ⟨hS₀.trans hτS.1, hτS.2.trans hS₁⟩ τ'
    have hsq : Real.sqrt |τ' - τ| ≤ 1 + |τ - τ'| := by
      rw [abs_sub_comm]
      refine (Real.sqrt_le_sqrt (by nlinarith [abs_nonneg (τ - τ')] :
        |τ - τ'| ≤ (1 + |τ - τ'|) ^ 2)).trans ?_
      rw [Real.sqrt_sq (by positivity)]
    have hl0 : 0 ≤ C₀ * p.l := by have := hF.one_le_l; positivity
    have hr := abs_nonneg (τ - τ')
    calc |Zeta23.mu τ'| ≤ C₀ * p.l + (1 + |τ - τ'|) := by linarith
      _ ≤ (C₀ * p.l + 1) * (1 + |τ - τ'|) := by
          have h4 := mul_nonneg hl0 hr
          have e : (C₀ * p.l + 1) * (1 + |τ - τ'|) = C₀ * p.l + (1 + |τ - τ'|) + C₀ * p.l * |τ - τ'| := by
            ring
          linarith
  have hl0 : 0 ≤ C₀ * p.l + 1 := by have := hF.one_le_l; positivity
  have hch := smoothPair_nuX_le hF hs hs₀2 (by positivity : (0:ℝ) ≤ 4 * ℓ₀ / p.T) (hΩk k) hΩ0 hΩ1
    hΩL hΩS hK hμc hμinc hμM hl0 hμg hθ₀
  -- the diagonal terms over the whole window
  have hIΦ0 : 0 ≤ ∫ x, F.Phi x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hμ2 : ∫ τ in s₀..s₁, Zeta23.mu τ ^ 2 ≤ ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2 :=
    intervalIntegral.integral_mono_interval hS₀ hs hS₁
      (Eventually.of_forall fun τ => sq_nonneg _) ((hμc.pow 2).intervalIntegrable _ _)
  have hIΩ : ∫ τ, Ω τ ≤ p.T := by
    have h := integral_window_mul_le hs hΩc hΩ1 hΩS (h := fun _ => (1:ℝ)) continuous_const
      (fun _ _ => zero_le_one) (C := 1) (fun _ _ => le_rfl)
    simp only [mul_one, one_mul] at h
    have hεT0 := mul_pos hε hT0
    exact h.trans (by linarith)
  have hsg : 0 ≤ ∑ n ∈ primeRange p.X, acoef n ^ 2 * F.g (Real.log n) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (hF.g_nonneg _)
  have hdiag : (1 / π) * (∫ τ, Ω τ) * ∑ n ∈ primeRange p.X, acoef n ^ 2 * F.g (Real.log n)
      ≤ (1 / π) * p.T * sumA2g p.X F.g := by
    rw [← sum_acoef_sq_mul_eq_sumA2g]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIΩ (by positivity)) hsg
  have hmu' := mul_le_mul_of_nonneg_left hμ2 hIΦ0
  have hL2 : 0 ≤ p.L ^ 2 := sq_nonneg _
  have hpair : smoothPair F.Phi Ω (Zeta23.nuX p.X) (Zeta23.nuX p.X)
      ≤ (∫ x, F.Phi x ^ 2) * (∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2)
          + (1 / π) * p.T * sumA2g p.X F.g
          + coalSum Ω F.g p.X θ₀
          + channelError (∑ n ∈ primeRange p.X, acoef n)
            (K * (∫ x, F.Phi x ^ 2 * |x|) + 10 * ∫ x, F.Phi x ^ 2 * x ^ 2)
            ((∫ x, F.Phi x ^ 2) + ∫ x, F.Phi x ^ 2 * |x|) (∫ x, F.Phi x ^ 2)
            (s₁ - s₀) s₀ p.L p.l
            ((1 / 2) * ((s₁ - s₀ + 5) * (4 * ℓ₀ / p.T * 5 * p.l + (K * 5 + 10 * 5 ^ 2) / s₀)))
            (∫ τ in (s₀ - 1)..(s₁ + 1), |iteratedDeriv k Ω τ|) θ₀ p.X
            (∫ τ, Ω τ * Zeta23.PX p.X τ ^ 2)
            (∫ τ, Ω τ * primeDirichletCos F.g p.X τ ^ 2) k := by
    linarith [hch, hdiag, hmu']
  have h1 := (abs_le.mp hcomp).2
  rw [hFub] at h1
  have h2 := mul_le_mul_of_nonneg_left hpair hL2
  linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
