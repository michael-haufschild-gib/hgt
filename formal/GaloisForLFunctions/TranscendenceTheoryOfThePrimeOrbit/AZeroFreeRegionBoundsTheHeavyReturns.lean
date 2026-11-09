import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheTestOfAHeavyReturn
import GaloisForLFunctions.SquareRootThreshold.AStripGivesLittlewoodWindows
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovLogDeriv
import GaloisForLFunctions.RHTower.XiCosineShiftVinogradovKorobovWindow
import GaloisForLFunctions.RHTower.EvenLandauPairTest

/-!
# A zero-free region bounds the heavy returns

Pole imitation (`norm_zeroSide_add_orbitPoly_zero_le`) with the test of a heavy return
(`TheTestOfAHeavyReturn`): a return at height `t` of a heavy subset of the primes `≤ y` forces the
zeros near `t` to reproduce `P_{φ_y}(0) ≥ √y/4`, while a zero of depth `|Re ρ − ½|` weighs only
`y^{|Re ρ − ½|}/(1 + (γ − t)²)`.

* **The zero side under a depth profile** (`eventually_norm_zeroSide_le`). If every zero of height
  `|γ| ≥ T₀` has depth at most `d(|γ|)`, `d` nondecreasing, then for large `t`,
  `‖Z_{φ_y}(t)‖ ≤ C_b (C y^{d(2t)} log t + ε√y)`: the zeros below `T₀` and above `2t` are dominated
  by `Σ_ρ m_ρ/(1 + |γ_ρ|²) < ∞` and fade (Tannery), the others are counted by the local density
  `Σ_ρ m_ρ/(1 + (t − γ_ρ)²) ≪ log t`.
* **Heavy returns under a depth profile** (`heavy_return_bound_of_depthProfile`). For large `y`,
  every return of precision `δ ≤ 1/20` of a `1/1000`-heavy subset of the primes `≤ y` at a height
  `t ≥ T₁` satisfies `√y ≤ K (y^{d(2t)} log t + log(2 + t))`.
* **A strip** (`log_ge_of_heavy_return_of_strip`). If every zero of height `≥ T₀` lies within `h < ½`
  of the line, heavy returns at heights `≥ T₁` satisfy `log t ≥ c y^{½−h}`: the main conjecture B97
  holds beyond a fixed height with every exponent `c < ½ − h`; RH gives `log t ≫ √y`.

The test only sees prime powers in `(y/9, y)`, so the argument lives at the top of the column,
where the weights `p^{−½}` sit and where the spike of `ζ(1 + it)` is blind.
-/

open Complex MeasureTheory Real Finset Filter Topology
open scoped Real

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open Zeta23
open PrimeTorusTheory (dist01)
open scoped Classical

/-! ## The zero side under a depth profile -/

theorem carrier_re_mem {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) : 0 < ρ.re ∧ ρ.re < 1 :=
  (RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hρ).2

theorem abs_re_sub_half_lt {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) : |ρ.re - 1 / 2| < 1 / 2 := by
  have h := carrier_re_mem hρ
  rw [abs_lt]; constructor <;> linarith [h.1, h.2]

/-- `1/(1 + |x|)² ≤ 1/(1 + x²)`. -/
theorem one_div_one_add_abs_sq_le (x : ℝ) : 1 / (1 + |x|) ^ 2 ≤ 1 / (1 + x ^ 2) := by
  apply one_div_le_one_div_of_le (by positivity)
  have := abs_nonneg x
  nlinarith [sq_abs x]

/-- The heights that are bad at `t`: below `T₀` or above `2t`. -/
def IsBadHeight (T₀ t : ℝ) (ρ : ℂ) : Prop := |ρ.im| < T₀ ∨ 2 * t < |ρ.im|

/-- The mass of the bad zeros at `t`. -/
def badMass (T₀ t : ℝ) : ℝ := ∑' ρ : zetaZeroConfig.carrier,
  (zetaZeroConfig.mult ρ : ℝ) * ((if IsBadHeight T₀ t (ρ : ℂ) then 1 else 0) / (1 + (t - (ρ : ℂ).im) ^ 2))

/-- **The bad zeros fade.** -/
theorem tendsto_badMass (T₀ : ℝ) : Tendsto (badMass T₀) atTop (𝓝 0) := by
  classical
  have hsum := RHTower.summable_zetaZeroConfig
  set bound : zetaZeroConfig.carrier → ℝ := fun ρ =>
    5 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)))
  have hb : Summable bound := hsum.mul_left 5
  unfold badMass
  suffices h : Tendsto (fun t : ℝ => ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) * ((if IsBadHeight T₀ t (ρ : ℂ) then 1 else 0) /
        (1 + (t - (ρ : ℂ).im) ^ 2))) atTop (𝓝 (∑' _ρ : zetaZeroConfig.carrier, (0 : ℝ))) by
    simpa using h
  refine tendsto_tsum_of_dominated_convergence hb (fun ρ => ?_) ?_
  · -- pointwise: the weight tends to `0`
    have h1 : Tendsto (fun t : ℝ => 1 + (t - (ρ : ℂ).im) ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_left _ 1 ?_
      exact (tendsto_pow_atTop (by norm_num)).comp (tendsto_atTop_add_const_right _ _ tendsto_id)
    have hlim : Tendsto (fun t : ℝ => 1 / (1 + (t - (ρ : ℂ).im) ^ 2)) atTop (𝓝 0) :=
      (h1.inv_tendsto_atTop).congr fun t => by simp [one_div]
    have hg : Tendsto (fun t : ℝ =>
        (if IsBadHeight T₀ t (ρ : ℂ) then (1 : ℝ) else 0) / (1 + (t - (ρ : ℂ).im) ^ 2))
        atTop (𝓝 0) := by
      refine squeeze_zero (fun t => ?_) (fun t => ?_) hlim
      · split_ifs <;> positivity
      · split_ifs
        · exact le_rfl
        · rw [zero_div]; positivity
    simpa using (tendsto_const_nhds (x := (zetaZeroConfig.mult ρ : ℝ))).mul hg
  · -- domination for `t ≥ 2T₀`
    filter_upwards [eventually_ge_atTop (2 * |T₀| + 1)] with t ht ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    simp only [bound]
    split_ifs with hbad
    · -- a bad zero is at distance at least `|γ|/2` from `t`
      have hdist : |(ρ : ℂ).im| / 2 ≤ |t - (ρ : ℂ).im| := by
        rcases hbad with h | h
        · have := abs_nonneg (ρ : ℂ).im
          have h1 := abs_sub_abs_le_abs_sub t (ρ : ℂ).im
          have : |t| = t := abs_of_nonneg (by linarith [abs_nonneg T₀])
          linarith [le_abs_self T₀]
        · have h1 := abs_sub_abs_le_abs_sub (ρ : ℂ).im t
          have : |t| = t := abs_of_nonneg (by linarith [abs_nonneg T₀])
          rw [abs_sub_comm] at h1; linarith
      have hnorm : Complex.normSq (gammaOf ρ) ≤ (ρ : ℂ).im ^ 2 + 1 / 4 := by
        have hre : (gammaOf ρ).re = (ρ : ℂ).im := by simp [gammaOf]
        have him : (gammaOf ρ).im = -((ρ : ℂ).re - 1 / 2) := by simp [gammaOf]
        rw [Complex.normSq_apply, hre, him]
        have := abs_re_sub_half_lt ρ.2
        have hsq : ((ρ : ℂ).re - 1 / 2) ^ 2 ≤ 1 / 4 := by
          have := sq_abs ((ρ : ℂ).re - 1 / 2)
          nlinarith [abs_nonneg ((ρ : ℂ).re - 1 / 2)]
        nlinarith
      have hsq : (ρ : ℂ).im ^ 2 / 4 ≤ (t - (ρ : ℂ).im) ^ 2 := by
        have := mul_self_le_mul_self (by positivity) hdist
        rw [← sq_abs (t - (ρ : ℂ).im)]; nlinarith [sq_abs (ρ : ℂ).im]
      have hns : 0 ≤ Complex.normSq (gammaOf ρ) := Complex.normSq_nonneg _
      have hden : (1 + Complex.normSq (gammaOf ρ)) / 5 ≤ 1 + (t - (ρ : ℂ).im) ^ 2 := by
        nlinarith
      calc (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))
          = (zetaZeroConfig.mult ρ : ℝ) / (1 + (t - (ρ : ℂ).im) ^ 2) := by ring
        _ ≤ (zetaZeroConfig.mult ρ : ℝ) / ((1 + Complex.normSq (gammaOf ρ)) / 5) :=
            div_le_div_of_nonneg_left hm (by positivity) hden
        _ = 5 * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
            field_simp
    · rw [zero_div, mul_zero]
      exact mul_nonneg (by norm_num) (div_nonneg hm (by linarith [Complex.normSq_nonneg (gammaOf ρ)]))

/-- The local density `S(t) = Σ_ρ m_ρ/(1 + (t − γ_ρ)²)`. -/
def localDensity (t : ℝ) : ℝ :=
  ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))

/-- **The zero side under a depth profile.** -/
theorem norm_zeroSide_le_profile {φ : ℝ → ℂ} {a : ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, φ u ≠ 0 → |u| ≤ a) (ha : 0 ≤ a) {d : ℝ → ℝ} {T₀ : ℝ}
    (hmono : MonotoneOn d (Set.Ici T₀))
    (hd : ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ d |ρ.im|) {t : ℝ}
    (ht : T₀ ≤ 2 * t)
    (hS : Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) :
    ‖zeroSide φ t‖ ≤ decayMass φ *
      (Real.exp (a * d (2 * t)) * localDensity t + Real.exp (a / 2) * badMass T₀ t) := by
  set D := decayMass φ
  have hD := decayMass_nonneg φ
  set E := Real.exp (a * d (2 * t))
  set F := Real.exp (a / 2)
  set u : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))
  set v : zetaZeroConfig.carrier → ℝ := fun ρ =>
    (zetaZeroConfig.mult ρ : ℝ) * ((if IsBadHeight T₀ t (ρ : ℂ) then 1 else 0) /
      (1 + (t - (ρ : ℂ).im) ^ 2))
  have hv : Summable v := by
    refine Summable.of_nonneg_of_le (fun ρ => ?_) (fun ρ => ?_) hS
    · simp only [v]; split_ifs <;> positivity
    · simp only [v, u]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      split_ifs
      · exact le_rfl
      · rw [zero_div]; positivity
  have hsum : HasSum (fun ρ => D * (E * u ρ + F * v ρ)) (D * (E * localDensity t + F * badMass T₀ t)) := by
    have := ((hS.hasSum.mul_left E).add (hv.hasSum.mul_left F)).mul_left D
    simpa [localDensity, badMass, u, v] using this
  refine tsum_of_norm_bounded hsum fun ρ => ?_
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  rw [norm_mul, Complex.norm_natCast]
  have hbound := norm_paperFT_gammaOf_sub_le hφ hsupp (ρ : ℂ) t
  have hden : 1 / (1 + |(ρ : ℂ).im - t|) ^ 2 ≤ 1 / (1 + (t - (ρ : ℂ).im) ^ 2) := by
    have := one_div_one_add_abs_sq_le ((ρ : ℂ).im - t)
    rwa [show ((ρ : ℂ).im - t) ^ 2 = (t - (ρ : ℂ).im) ^ 2 by ring] at this
  -- the weight of the zero
  have hweight : Real.exp (|(ρ : ℂ).re - 1 / 2| * a) ≤
      E + F * (if IsBadHeight T₀ t (ρ : ℂ) then 1 else 0) := by
    by_cases hbad : IsBadHeight T₀ t (ρ : ℂ)
    · rw [if_pos hbad, mul_one]
      have : |(ρ : ℂ).re - 1 / 2| * a ≤ a / 2 := by
        have := abs_re_sub_half_lt ρ.2
        nlinarith
      have := Real.exp_le_exp.mpr this
      have : 0 ≤ E := (Real.exp_pos _).le
      linarith
    · rw [if_neg hbad, mul_zero, add_zero]
      simp only [IsBadHeight, not_or, not_lt] at hbad
      have h1 := hd ρ ρ.2 hbad.1
      have h2 : d |(ρ : ℂ).im| ≤ d (2 * t) :=
        hmono (Set.mem_Ici.mpr hbad.1) (Set.mem_Ici.mpr ht) hbad.2
      apply Real.exp_le_exp.mpr
      nlinarith
  have hpos : 0 ≤ 1 / (1 + (t - (ρ : ℂ).im) ^ 2) := by positivity
  calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT φ (gammaOf ρ - t)‖
      ≤ (zetaZeroConfig.mult ρ : ℝ) * (Real.exp (|(ρ : ℂ).re - 1 / 2| * a) * D *
          (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (hbound.trans ?_) hm
        calc Real.exp (|(ρ : ℂ).re - 1 / 2| * a) * decayMass φ / (1 + |(ρ : ℂ).im - t|) ^ 2
            = Real.exp (|(ρ : ℂ).re - 1 / 2| * a) * D * (1 / (1 + |(ρ : ℂ).im - t|) ^ 2) := by
              simp only [D]; ring
          _ ≤ Real.exp (|(ρ : ℂ).re - 1 / 2| * a) * D * (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
              mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * ((E + F * (if IsBadHeight T₀ t (ρ : ℂ) then 1 else 0)) * D *
          (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by gcongr
    _ = D * (E * u ρ + F * v ρ) := by simp only [u, v]; ring

/-! ## Heavy returns under a depth profile -/

theorem eventually_twelve_log_le_sqrt :
    ∀ᶠ y : ℕ in atTop, 12 * Real.log y ≤ Real.sqrt y / 40 := by
  have hlo := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 480 by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ 1 / 480 * ‖x ^ (1 / 2 : ℝ)‖ ∧ 1 ≤ x :=
    hlo.and (eventually_ge_atTop 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hev] with y ⟨h, hy⟩
  have h0 : 0 ≤ Real.log y := Real.log_nonneg hy
  rw [Real.norm_eq_abs, abs_of_nonneg h0, ← Real.sqrt_eq_rpow, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] at h
  linarith

theorem pi_sq_lt_ten : π ^ 2 < 10 := by
  have h1 := Real.pi_lt_d2
  have h2 := Real.pi_pos
  nlinarith

theorem two_pi_sq_mul_sq_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 20) : 2 * π ^ 2 * δ ^ 2 ≤ 1 / 20 := by
  have h1 : δ ^ 2 ≤ (1 / 20) ^ 2 := pow_le_pow_left₀ hδ0 hδ 2
  have h2 := pi_sq_lt_ten
  have h3 : 0 ≤ δ ^ 2 := sq_nonneg δ
  nlinarith

/-- The final arithmetic of the heavy-return bound. -/
theorem heavy_return_arith {s R p g z DC DK X L : ℝ} (hs : 0 ≤ s) (hDC : 0 ≤ DC) (hDK : 0 ≤ DK)
    (hX : 0 ≤ X) (hL : 1 ≤ L) (hlow : 2 / 10 * s ≤ R) (hup : R ≤ p + g + z) (hp : p ≤ s / 20)
    (hg : g ≤ DK * (1 + L)) (hz : z ≤ DC * X + s / 20) :
    s ≤ (20 * (DC + DK) + 1) * (X + L) := by
  have h1 : s ≤ 10 * (DC * X + DK * (1 + L)) := by linarith
  have h2 : DK * (1 + L) ≤ 2 * DK * L := by nlinarith
  have h3 : 0 ≤ DC * X := mul_nonneg hDC hX
  have h4 : 0 ≤ DK * L := mul_nonneg hDK (by linarith)
  nlinarith

/-- **Heavy returns under a depth profile.** If every zero of height `|γ| ≥ T₀` has depth at most
`d(|γ|)` with `d` nondecreasing, then for large `y` every return of precision `δ ≤ 1/20` of a
`1/1000`-heavy subset of the primes `≤ y` at a height `t ≥ T₁` satisfies
`√y ≤ K (y^{d(2t)} log t + log(2 + t))`. -/
theorem heavy_return_bound_of_depthProfile {d : ℝ → ℝ} {T₀ : ℝ}
    (hmono : MonotoneOn d (Set.Ici T₀))
    (hd : ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ d |ρ.im|) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
      ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
        IsDeltaReturn H (fun p : ℕ => Real.log p) δ t →
          Real.sqrt y ≤ K * ((y : ℝ) ^ d (2 * t) * Real.log t + Real.log (2 + t)) := by
  obtain ⟨C₁, hC₁, hdens⟩ := RHTower.Littlewood.exists_tsum_carrier_density_le
  obtain ⟨KΓ, hKΓ, hgam⟩ := exists_norm_gammaTerm_le
  set D := decayMass (heavyTest 1)
  have hD : 0 ≤ D := decayMass_nonneg _
  refine ⟨20 * (D * C₁ + D * KΓ) + 1, by positivity, ?_⟩
  have hbadT : ∀ᶠ t in atTop, D * badMass T₀ t ≤ 1 / 20 := by
    have h := (tendsto_const_nhds (x := D)).mul (tendsto_badMass T₀)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  have hT : ∀ᶠ t in atTop, ((Summable fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) ∧ localDensity t ≤ C₁ * Real.log t) ∧
      D * badMass T₀ t ≤ 1 / 20 ∧ 40 * D + |T₀| + 1 ≤ t :=
    (hdens.and hbadT).and (eventually_ge_atTop _) |>.mono fun t ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hT
  refine ⟨T₁, ?_⟩
  filter_upwards [eventually_orbitPoly_heavyTest_zero_ge,
    eventually_re_orbitPoly_heavyTest_ge (κ := 1 / 1000) (by norm_num), eventually_ge_atTop 9,
    eventually_twelve_log_le_sqrt] with y hP0 hheavy hy9 hlog H hH δ t hδ0 hδ ht hret
  obtain ⟨⟨hSum, hS⟩, hbad, htT⟩ := hT₁ t ht
  have hy9' : (9 : ℝ) ≤ y := by exact_mod_cast hy9
  have hy0 : (0 : ℝ) < y := by linarith
  have ht1 : 1 ≤ t := by linarith [abs_nonneg T₀]
  have hT0t : T₀ ≤ 2 * t := by linarith [le_abs_self T₀]
  set φ := heavyTest (y : ℝ)
  have hφ := contDiff_heavyTest (y : ℝ)
  have hφc := hasCompactSupport_heavyTest hy9'
  have hφ0 : ∀ u ≤ 0, φ u = 0 := fun u hu => heavyTest_eq_zero_of_nonpos hy9' hu
  have hsupp : ∀ u, φ u ≠ 0 → |u| ≤ Real.log y := fun u hu => heavyTest_abs_le hy9' hu
  have hDφ : decayMass φ = D := decayMass_heavyTest _
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hsqrt : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy0]; ring_nf
  have hpow : Real.exp (Real.log y * d (2 * t)) = (y : ℝ) ^ d (2 * t) := by
    rw [Real.rpow_def_of_pos hy0]
  -- the upper side: reciprocity
  have hrec := orbit_reciprocity hφ hφc hφ0 t
  have hup : (orbitPoly φ t).re ≤ ‖poleTerm φ t‖ + ‖gammaTerm φ t‖ + ‖zeroSide φ t‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hrec]
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_add_le (poleTerm φ t) (gammaTerm φ t)]
  have hpole := norm_poleTerm_le hφ hsupp t
  rw [hDφ, hsqrt, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at hpole
  have hpole' : ‖poleTerm φ t‖ ≤ Real.sqrt y / 20 := by
    have h1 : (1 : ℝ) + t ≥ 40 * D + 2 := by linarith [abs_nonneg T₀]
    have h2 : (1 + t) ^ 2 ≥ 40 * D + 2 := by nlinarith
    have h3 : 2 * (Real.sqrt y * D / (1 + t) ^ 2) ≤ Real.sqrt y / 20 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      have := Real.sqrt_nonneg (y : ℝ)
      nlinarith
    linarith
  have hgam' := hgam φ (Real.log y) hφ hsupp t
  rw [hDφ, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] at hgam'
  have hzero := norm_zeroSide_le_profile hφ hsupp hlogy hmono hd hT0t hSum
  rw [hDφ, hpow, hsqrt] at hzero
  have hzero' : ‖zeroSide φ t‖ ≤ D * C₁ * ((y : ℝ) ^ d (2 * t) * Real.log t) + Real.sqrt y / 20 := by
    have hypow : 0 ≤ (y : ℝ) ^ d (2 * t) := (Real.rpow_pos_of_pos hy0 _).le
    have h1 : D * ((y : ℝ) ^ d (2 * t) * localDensity t) ≤
        D * ((y : ℝ) ^ d (2 * t) * (C₁ * Real.log t)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hypow) hD
    have h2 : D * (Real.sqrt y * badMass T₀ t) ≤ Real.sqrt y / 20 := by
      have := mul_le_mul_of_nonneg_left hbad (Real.sqrt_nonneg (y : ℝ))
      calc D * (Real.sqrt y * badMass T₀ t) = Real.sqrt y * (D * badMass T₀ t) := by ring
        _ ≤ Real.sqrt y * (1 / 20) := this
        _ = Real.sqrt y / 20 := by ring
    calc ‖zeroSide φ t‖ ≤ D * ((y : ℝ) ^ d (2 * t) * localDensity t + Real.sqrt y * badMass T₀ t) :=
          hzero
      _ = D * ((y : ℝ) ^ d (2 * t) * localDensity t) + D * (Real.sqrt y * badMass T₀ t) := by ring
      _ ≤ D * ((y : ℝ) ^ d (2 * t) * (C₁ * Real.log t)) + Real.sqrt y / 20 := add_le_add h1 h2
      _ = D * C₁ * ((y : ℝ) ^ d (2 * t) * Real.log t) + Real.sqrt y / 20 := by ring
  -- the lower side: the heavy return copies the pole
  have hlow := hheavy H hH δ t hδ0 hret
  have hδ2 := two_pi_sq_mul_sq_le hδ0 hδ
  have hlow' : 2 / 10 * Real.sqrt y ≤ (orbitPoly φ t).re := by
    have h1 : (19 / 20) * (Real.sqrt y / 4) ≤ (1 - 2 * π ^ 2 * δ ^ 2) * (orbitPoly (heavyTest y) 0).re :=
      mul_le_mul (by linarith) hP0 (by positivity) (by linarith)
    have := Real.sqrt_nonneg (y : ℝ)
    linarith
  -- combine
  have hl2 : 1 ≤ Real.log (2 + t) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hX : 0 ≤ (y : ℝ) ^ d (2 * t) * Real.log t := mul_nonneg (Real.rpow_pos_of_pos hy0 _).le hlt
  have hgam'' : ‖gammaTerm φ t‖ ≤ D * KΓ * (1 + Real.log (2 + t)) := hgam'
  have := heavy_return_arith (Real.sqrt_nonneg _) (mul_nonneg hD hC₁.le) (mul_nonneg hD hKΓ) hX hl2
    hlow' hup hpole' hgam'' hzero'
  simpa [mul_add] using this

/-! ## A strip and the Vinogradov–Korobov region -/

/-- **A strip bounds the heavy returns.** If every zero of height `≥ T₀` lies within `h ≥ 0` of the
critical line, then every return of precision `δ ≤ 1/20` of a `1/1000`-heavy subset of the primes
`≤ y` at a height `t ≥ T₁` satisfies `log t ≥ c y^{½−h}`, for large `y`. -/
theorem log_ge_of_heavy_return_of_strip {h T₀ : ℝ} (hh : 0 ≤ h)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ h) :
    ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
      ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
        IsDeltaReturn H (fun p : ℕ => Real.log p) δ t → c * (y : ℝ) ^ (1 / 2 - h) ≤ Real.log t := by
  obtain ⟨K, hK, T₁, hev⟩ := heavy_return_bound_of_depthProfile (d := fun _ => h) (T₀ := T₀)
    (fun _ _ _ _ _ => le_rfl) (fun ρ hρ hT => hstrip ρ hρ hT)
  refine ⟨1 / (3 * K), by positivity, max T₁ 2, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with y hy hy1 H hH δ t hδ0 hδ ht hret
  have hb := hy H hH δ t hδ0 hδ ((le_max_left _ _).trans ht) hret
  have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hyh : 1 ≤ (y : ℝ) ^ h := Real.one_le_rpow (by exact_mod_cast hy1) hh
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
  have hl2t : Real.log (2 + t) ≤ 2 * Real.log t := by
    have : Real.log (2 + t) ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at this; linarith
  have hlt0 : 0 ≤ Real.log t := (Real.log_nonneg (by norm_num)).trans hlt
  have hmain : Real.sqrt y ≤ 3 * K * ((y : ℝ) ^ h * Real.log t) := by
    have h1 : Real.log (2 + t) ≤ 2 * ((y : ℝ) ^ h * Real.log t) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 ((y : ℝ) ^ h * Real.log t)) hK.le
    linarith
  have hsplit : (y : ℝ) ^ (1 / 2 - h) = Real.sqrt y / (y : ℝ) ^ h := by
    rw [Real.rpow_sub hy0, ← Real.sqrt_eq_rpow]
  rw [hsplit, div_mul_div_comm, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- The Vinogradov–Korobov depth profile: zeros of height `≥ T₀` have depth at most
`½ − w(|γ|)`, `w` the Vinogradov–Korobov width. -/
theorem exists_vk_depthProfile : ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧
    ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| →
      |ρ.re - 1 / 2| ≤ 1 / 2 - RHTower.vkHadamardWidth |ρ.im| := by
  obtain ⟨T₀, hT₀, hvk⟩ := RHTower.Sieve.exists_vk_zero_free_region_abs
  refine ⟨T₀, hT₀, fun ρ hρ hT => ?_⟩
  have hzero : ∀ σ ∈ zetaZeroConfig.carrier, σ.re ≤ 1 - RHTower.vkHadamardWidth |σ.im| ∨
      |σ.im| < T₀ := fun σ hσ => by
    by_cases hTσ : T₀ ≤ |σ.im|
    · left
      have hstrip := carrier_re_mem hσ
      have hxi := (RHTower.CrossRouteReceiverBridges.mem_zetaZeroConfig_carrier_iff_xi_eq_zero_and_strip.mp hσ).1
      have hne : σ ≠ 1 := by intro h1; rw [h1] at hstrip; simp at hstrip
      have hζ : riemannZeta σ = 0 := (RHTower.xi_eq_zero_iff hstrip.1 hne).mp hxi
      by_contra hlt
      push Not at hlt
      apply hvk σ.re σ.im hTσ hstrip.2.le hlt
      rw [Complex.re_add_im]; exact hζ
    · right; exact not_le.mp hTσ
  have h1 := hzero ρ hρ
  have h2 := hzero (1 - ρ) (RHTower.one_sub_mem_zetaZeroConfig hρ)
  have him : |(1 - ρ).im| = |ρ.im| := by simp [abs_neg]
  rw [him] at h2
  have hre : (1 - ρ).re = 1 - ρ.re := by simp
  rw [hre] at h2
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · rw [abs_le]; constructor <;> linarith
    · linarith
  · linarith

/-- **The Vinogradov–Korobov region bounds the heavy returns.** For large `y`, every return of
precision `δ ≤ 1/20` of a `1/1000`-heavy subset of the primes `≤ y` at a height `t ≥ T₁` satisfies
`√y ≤ K(y^{½ − w(2t)} log t + log(2 + t))`, `w` the Vinogradov–Korobov width. -/
theorem heavy_return_bound_vinogradovKorobov :
    ∃ K : ℝ, 0 < K ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
      ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
        IsDeltaReturn H (fun p : ℕ => Real.log p) δ t →
          Real.sqrt y ≤ K * ((y : ℝ) ^ (1 / 2 - RHTower.vkHadamardWidth (2 * t)) * Real.log t +
            Real.log (2 + t)) := by
  obtain ⟨T₀, hT₀, hprof⟩ := exists_vk_depthProfile
  have hmono : MonotoneOn (fun T => 1 / 2 - RHTower.vkHadamardWidth T) (Set.Ici T₀) := by
    intro a ha b hb hab
    have ha' : a ∈ Set.Ici (Real.exp (Real.exp 1)) := hT₀.trans ha
    have hb' : b ∈ Set.Ici (Real.exp (Real.exp 1)) := hT₀.trans hb
    have := RHTower.vkHadamardWidth_antitoneOn ha' hb' hab
    simp only; linarith
  exact heavy_return_bound_of_depthProfile hmono hprof

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
