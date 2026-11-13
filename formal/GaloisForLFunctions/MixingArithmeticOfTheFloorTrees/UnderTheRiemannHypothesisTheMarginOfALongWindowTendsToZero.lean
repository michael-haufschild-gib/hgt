import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheNeutralPartIsWeilsFormOfTheZerosMinusThePoles
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity
import GaloisForLFunctions.RHTower.RelaxedHodgeDepthDictionary
import GaloisForLFunctions.RHTower.RadicalDetectionKernel
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheNormalizedAtomicTransform

/-!
# Under the Riemann hypothesis the margin of a long window tends to zero

At infinite block size the window form is the neutral form `N(f) = W(f) − 2 A(f) B(f)` on the
smooth packets supported in the window, with `W` Weil's form of the zeros and
`A(f) = ∫ f e^{−u/2}`, `B(f) = ∫ f e^{u/2}` the two charges. Its second eigenvalue — the margin,
gap minus binding energy — is the least `m` such that some plane of packets carries `N ≤ m · mass`.

* **Lower side.** On the hyperplane `A = 0` the neutral form is Weil's form, a sum
  `Σ_ρ m_ρ |f̂(γ_ρ)|²` over the zeros under RH (`re_zetaW_nonneg_of_riemannHypothesis`); so the
  neutral form is nonnegative there (`neutralForm_nonneg_of_charge_eq_zero`) and the margin is
  nonnegative: one bound state.
* **Upper side.** Spread a fixed profile `β` over the scale `L`: `g_d(u) = β((u − d)/L)`. Its
  transform is `L β̂(Lγ)` up to a phase (`norm_paperFT_spreadTest`); since every zero has
  `|γ| ≥ 2` and `β̂` decays like `|γ|^{−2}`, Weil's form of a combination of three spread copies
  at the centres `d, d + 3L, d + 6L` is at most `3 Σ c_i² N²/L² · Σ_ρ m_ρ/(1 + γ²)`
  (`re_zetaW_threeSpread_le`), while its mass is `Σ c_i² · L ∫ β²`
  (`integral_threeSpread_sq`). The first charge of a copy moves by the factor `e^{−3L/2}` from one
  centre to the next (`integral_spreadTest_add_mul_exp_neg`), so the plane
  `a (g_0 − E g_1) + b (g_1 − E g_2)`, `E = e^{3L/2}`, lies in the hyperplane `A = 0`
  (`firstCharge_planeTest`), and on it `N ≤ C L^{−3} · mass`.

Hence (`exists_plane_neutralForm_le_of_riemannHypothesis`): under RH, for every `ε > 0` every
window of logarithmic length `8L ≥ 8L₀(ε)` carries a plane of smooth packets on which the neutral
form lies between `0` and `ε` times the mass. **The margin of a long window tends to zero**: the
inequality "gap ≥ binding energy" that RH asserts is asymptotically sharp, and no proof of RH can
rest on a uniform positive margin.
-/

open MeasureTheory Complex
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx)
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (atomDilate paperFT_atomDilate)
open Zeta23

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-! ### Spread copies of a profile -/

/-- The profile `β` spread over the scale `L` and centred at `d`. -/
def spreadTest (β : ℝ → ℝ) (L d : ℝ) (u : ℝ) : ℝ := β ((u - d) / L)

variable {β : ℝ → ℝ}

theorem spreadTest_eq_zero (hβs : ∀ v, 1 < |v| → β v = 0) {L d u : ℝ} (hL : 0 < L)
    (hu : L < |u - d|) : spreadTest β L d u = 0 :=
  hβs _ (by rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL, one_mul]; exact hu)

theorem contDiff_spreadTest (hβ : ContDiff ℝ 2 β) (L d : ℝ) : ContDiff ℝ 2 (spreadTest β L d) :=
  hβ.comp ((contDiff_id.sub contDiff_const).div_const L)

theorem hasCompactSupport_spreadTest (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ} (hL : 0 < L)
    (d : ℝ) : HasCompactSupport (spreadTest β L d) :=
  HasCompactSupport.intro (isCompact_Icc (a := d - L) (b := d + L)) fun u hu =>
    spreadTest_eq_zero hβs hL (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)

/-- **The transform of a spread copy** is `e^{izd} L β̂(Lz)`. -/
theorem paperFT_spreadTest (β : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (d : ℝ) (z : ℂ) :
    paperFT (cx (spreadTest β L d)) z =
      Complex.exp (I * z * d) * ((L : ℂ) * paperFT (cx β) ((L : ℂ) * z)) := by
  show paperFT (fun u => cx (atomDilate β L) (u - d)) z = _
  rw [_root_.RHTower.paperFT_comp_sub, paperFT_atomDilate hL]

theorem norm_paperFT_spreadTest (β : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (d r : ℝ) :
    ‖paperFT (cx (spreadTest β L d)) r‖ = L * ‖paperFT (cx β) ((L * r : ℝ) : ℂ)‖ := by
  have h1 : ‖Complex.exp (I * (r : ℂ) * d)‖ = 1 := by
    rw [show I * (r : ℂ) * d = ((r * d : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [paperFT_spreadTest β hL d, norm_mul, norm_mul, h1, Complex.norm_of_nonneg hL.le, one_mul,
    Complex.ofReal_mul]

/-- The mass of a spread copy is `L ∫ β²`. -/
theorem integral_spreadTest_sq (β : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (d : ℝ) :
    ∫ u, spreadTest β L d u ^ 2 = L * ∫ v, β v ^ 2 := by
  have h1 : ∫ u, β ((u - d) / L) ^ 2 = ∫ w, β (w / L) ^ 2 :=
    integral_sub_right_eq_self (fun w => β (w / L) ^ 2) d
  have h2 : ∫ w, β (w / L) ^ 2 = |L| • ∫ v, β v ^ 2 :=
    Measure.integral_comp_div (fun v => β v ^ 2) L
  show ∫ u, β ((u - d) / L) ^ 2 = _
  rw [h1, h2, abs_of_pos hL, smul_eq_mul]

/-- **The first charge of a copy moves by `e^{−t/2}` under translation by `t`.** -/
theorem integral_spreadTest_add_mul_exp_neg (β : ℝ → ℝ) (L d t : ℝ) :
    ∫ u, spreadTest β L (d + t) u * Real.exp (-u / 2) =
      Real.exp (-t / 2) * ∫ u, spreadTest β L d u * Real.exp (-u / 2) := by
  have h : ∫ u, spreadTest β L d (u - t) * Real.exp (-(u - t + t) / 2) =
      ∫ w, spreadTest β L d w * Real.exp (-(w + t) / 2) :=
    integral_sub_right_eq_self (fun w => spreadTest β L d w * Real.exp (-(w + t) / 2)) t
  rw [← integral_const_mul]
  calc ∫ u, spreadTest β L (d + t) u * Real.exp (-u / 2) =
        ∫ u, spreadTest β L d (u - t) * Real.exp (-(u - t + t) / 2) := by
        congr 1
        funext u
        simp only [spreadTest]
        ring_nf
    _ = ∫ w, spreadTest β L d w * Real.exp (-(w + t) / 2) := h
    _ = ∫ w, Real.exp (-t / 2) * (spreadTest β L d w * Real.exp (-w / 2)) := by
        congr 1
        funext w
        rw [show -(w + t) / 2 = -t / 2 + -w / 2 by ring, Real.exp_add]
        ring

/-! ### Three copies -/

/-- A combination of three copies at the centres `d, d + 3L, d + 6L`. -/
def threeSpread (β : ℝ → ℝ) (L d c₀ c₁ c₂ : ℝ) (u : ℝ) : ℝ :=
  c₀ * spreadTest β L d u + c₁ * spreadTest β L (d + 3 * L) u + c₂ * spreadTest β L (d + 6 * L) u

theorem contDiff_threeSpread (hβ : ContDiff ℝ 2 β) (L d c₀ c₁ c₂ : ℝ) :
    ContDiff ℝ 2 (threeSpread β L d c₀ c₁ c₂) :=
  ((contDiff_const.mul (contDiff_spreadTest hβ L d)).add
    (contDiff_const.mul (contDiff_spreadTest hβ L _))).add
    (contDiff_const.mul (contDiff_spreadTest hβ L _))

/-- The three copies vanish off `[d − L, d + 7L]`. -/
theorem threeSpread_eq_zero (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ} (hL : 0 < L)
    (d c₀ c₁ c₂ : ℝ) {u : ℝ} (hu : u < d - L ∨ d + 7 * L < u) :
    threeSpread β L d c₀ c₁ c₂ u = 0 := by
  have h : ∀ e, d ≤ e → e ≤ d + 6 * L → spreadTest β L e u = 0 := fun e he1 he2 =>
    spreadTest_eq_zero hβs hL (by
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  simp only [threeSpread, h d le_rfl (by linarith), h (d + 3 * L) (by linarith) (by linarith),
    h (d + 6 * L) (by linarith) le_rfl, mul_zero, add_zero]

theorem hasCompactSupport_threeSpread (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ} (hL : 0 < L)
    (d c₀ c₁ c₂ : ℝ) : HasCompactSupport (threeSpread β L d c₀ c₁ c₂) :=
  HasCompactSupport.intro (isCompact_Icc (a := d - L) (b := d + 7 * L)) fun u hu =>
    threeSpread_eq_zero hβs hL d c₀ c₁ c₂ (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      exact hu)

/-- Copies at centres `3L` apart have disjoint supports. -/
theorem spreadTest_mul_eq_zero (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ} (hL : 0 < L)
    {d e : ℝ} (hde : 3 * L ≤ |d - e|) (u : ℝ) :
    spreadTest β L d u * spreadTest β L e u = 0 := by
  by_cases h : L < |u - d|
  · rw [spreadTest_eq_zero hβs hL h, zero_mul]
  · push Not at h
    have htri := abs_sub_le d u e
    rw [abs_sub_comm d u] at htri
    rw [spreadTest_eq_zero hβs hL (show L < |u - e| by linarith), mul_zero]

/-- Pointwise, the square of three disjoint copies is the sum of their squares. -/
theorem threeSpread_sq_eq (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ} (hL : 0 < L)
    (d c₀ c₁ c₂ u : ℝ) :
    threeSpread β L d c₀ c₁ c₂ u ^ 2 =
      (c₀ ^ 2 * spreadTest β L d u ^ 2 + c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2) +
        c₂ ^ 2 * spreadTest β L (d + 6 * L) u ^ 2 := by
  have e3 : |d - (d + 3 * L)| = 3 * L := by
    rw [show d - (d + 3 * L) = -(3 * L) by ring, abs_neg, abs_of_pos (by linarith)]
  have e6 : |d - (d + 6 * L)| = 6 * L := by
    rw [show d - (d + 6 * L) = -(6 * L) by ring, abs_neg, abs_of_pos (by linarith)]
  have e36 : |d + 3 * L - (d + 6 * L)| = 3 * L := by
    rw [show d + 3 * L - (d + 6 * L) = -(3 * L) by ring, abs_neg, abs_of_pos (by linarith)]
  have h01 : spreadTest β L d u * spreadTest β L (d + 3 * L) u = 0 :=
    spreadTest_mul_eq_zero hβs hL e3.ge u
  have h02 : spreadTest β L d u * spreadTest β L (d + 6 * L) u = 0 :=
    spreadTest_mul_eq_zero hβs hL (by rw [e6]; linarith) u
  have h12 : spreadTest β L (d + 3 * L) u * spreadTest β L (d + 6 * L) u = 0 :=
    spreadTest_mul_eq_zero hβs hL e36.ge u
  unfold threeSpread
  linear_combination (2 * c₀ * c₁) * h01 + (2 * c₀ * c₂) * h02 + (2 * c₁ * c₂) * h12

theorem integrable_spreadTest_sq (hβ : ContDiff ℝ 2 β) (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ}
    (hL : 0 < L) (e : ℝ) : Integrable fun u => spreadTest β L e u ^ 2 := by
  have hc : Continuous fun u => spreadTest β L e u ^ 2 :=
    (contDiff_spreadTest hβ L e).continuous.pow 2
  have hs : HasCompactSupport fun u => spreadTest β L e u ^ 2 :=
    (hasCompactSupport_spreadTest hβs hL e).comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact hc.integrable_of_hasCompactSupport hs

theorem integral_const_mul_spreadTest_sq (β : ℝ → ℝ) {L : ℝ} (hL : 0 < L) (c e : ℝ) :
    ∫ u, c ^ 2 * spreadTest β L e u ^ 2 = c ^ 2 * (L * ∫ v, β v ^ 2) := by
  rw [integral_const_mul, integral_spreadTest_sq β hL e]

/-- **The mass of three copies is `Σ c_i² · L ∫ β²`.** -/
theorem integral_threeSpread_sq (hβ : ContDiff ℝ 2 β) (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ}
    (hL : 0 < L) (d c₀ c₁ c₂ : ℝ) :
    ∫ u, threeSpread β L d c₀ c₁ c₂ u ^ 2 =
      (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (L * ∫ v, β v ^ 2) := by
  have i0 : Integrable fun u => c₀ ^ 2 * spreadTest β L d u ^ 2 :=
    (integrable_spreadTest_sq hβ hβs hL d).const_mul _
  have i1 : Integrable fun u => c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2 :=
    (integrable_spreadTest_sq hβ hβs hL _).const_mul _
  have i2 : Integrable fun u => c₂ ^ 2 * spreadTest β L (d + 6 * L) u ^ 2 :=
    (integrable_spreadTest_sq hβ hβs hL _).const_mul _
  have i01 : Integrable fun u =>
      c₀ ^ 2 * spreadTest β L d u ^ 2 + c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2 := i0.add i1
  have hsum : ∫ u, threeSpread β L d c₀ c₁ c₂ u ^ 2 =
      ∫ u, (c₀ ^ 2 * spreadTest β L d u ^ 2 + c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2) +
        c₂ ^ 2 * spreadTest β L (d + 6 * L) u ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (threeSpread_sq_eq hβs hL d c₀ c₁ c₂))
  have hA : ∫ u, (c₀ ^ 2 * spreadTest β L d u ^ 2 +
        c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2) + c₂ ^ 2 * spreadTest β L (d + 6 * L) u ^ 2 =
      (∫ u, c₀ ^ 2 * spreadTest β L d u ^ 2 + c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2) +
        ∫ u, c₂ ^ 2 * spreadTest β L (d + 6 * L) u ^ 2 := integral_add i01 i2
  have hB : ∫ u, c₀ ^ 2 * spreadTest β L d u ^ 2 + c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2 =
      (∫ u, c₀ ^ 2 * spreadTest β L d u ^ 2) +
        ∫ u, c₁ ^ 2 * spreadTest β L (d + 3 * L) u ^ 2 := integral_add i0 i1
  rw [hsum, hA, hB, integral_const_mul_spreadTest_sq β hL c₀ d,
    integral_const_mul_spreadTest_sq β hL c₁ (d + 3 * L),
    integral_const_mul_spreadTest_sq β hL c₂ (d + 6 * L)]
  ring

/-- The transform of three copies is the combination of their transforms. -/
theorem paperFT_threeSpread (hβ : ContDiff ℝ 2 β) (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ}
    (hL : 0 < L) (d c₀ c₁ c₂ : ℝ) (z : ℂ) :
    paperFT (cx (threeSpread β L d c₀ c₁ c₂)) z =
      c₀ * paperFT (cx (spreadTest β L d)) z + c₁ * paperFT (cx (spreadTest β L (d + 3 * L))) z +
        c₂ * paperFT (cx (spreadTest β L (d + 6 * L))) z := by
  have hi : ∀ e, Integrable fun u => cx (spreadTest β L e) u * Complex.exp (I * z * u) := fun e =>
    ((Complex.continuous_ofReal.comp (contDiff_spreadTest hβ L e).continuous).mul
      (by fun_prop)).integrable_of_hasCompactSupport
      ((hasCompactSupport_spreadTest hβs hL e).comp_left Complex.ofReal_zero).mul_right
  have e : (fun u => cx (threeSpread β L d c₀ c₁ c₂) u * Complex.exp (I * z * u)) = fun u =>
      (c₀ : ℂ) * (cx (spreadTest β L d) u * Complex.exp (I * z * u)) +
        (c₁ : ℂ) * (cx (spreadTest β L (d + 3 * L)) u * Complex.exp (I * z * u)) +
        (c₂ : ℂ) * (cx (spreadTest β L (d + 6 * L)) u * Complex.exp (I * z * u)) := by
    funext u
    simp only [cx, threeSpread]
    push_cast
    ring
  have i0 : Integrable fun u => (c₀ : ℂ) * (cx (spreadTest β L d) u * Complex.exp (I * z * u)) :=
    (hi d).const_mul _
  have i1 : Integrable fun u =>
      (c₁ : ℂ) * (cx (spreadTest β L (d + 3 * L)) u * Complex.exp (I * z * u)) :=
    (hi _).const_mul _
  have i2 : Integrable fun u =>
      (c₂ : ℂ) * (cx (spreadTest β L (d + 6 * L)) u * Complex.exp (I * z * u)) :=
    (hi _).const_mul _
  have i01 : Integrable fun u =>
      (c₀ : ℂ) * (cx (spreadTest β L d) u * Complex.exp (I * z * u)) +
        (c₁ : ℂ) * (cx (spreadTest β L (d + 3 * L)) u * Complex.exp (I * z * u)) := i0.add i1
  unfold paperFT
  rw [e, integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-! ### Weil's form of the zeros under RH -/

/-- Under RH Weil's form of the zeros is a sum of on-line terms `m_ρ ‖f̂(γ_ρ)‖² ≥ 0`. -/
theorem re_zetaW_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) (f : ℝ → ℂ) :
    0 ≤ (zetaZeroConfig.W f f).re := by
  have hon := SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
  by_cases hs : Summable fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ
  · have hre := Complex.hasSum_re hs.hasSum
    rw [ZeroConfig.W, ← hre.tsum_eq]
    refine tsum_nonneg fun ρ => ?_
    show 0 ≤ (zetaZeroConfig.Wsummand f f ρ).re
    rw [WindowVisibilityLaw.re_Wsummand_onLine_eq _ _ (hon ρ ρ.2)]
    positivity
  · rw [ZeroConfig.W, tsum_eq_zero_of_not_summable hs, Complex.zero_re]

/-- **Under RH, a transform bounded by `K/(1 + r²)` on `|r| ≥ 2` has Weil form at most
`K Σ_ρ m_ρ/(1 + |γ_ρ|²)`.** Every zero of `ζ` has `|γ| ≥ 2`. -/
theorem re_zetaW_le_of_riemannHypothesis (hRH : RiemannHypothesis) (f : ℝ → ℂ) {K : ℝ}
    (hK : 0 ≤ K) (hf : ∀ r : ℝ, 2 ≤ |r| → ‖paperFT f r‖ ^ 2 ≤ K / (1 + r ^ 2)) :
    (zetaZeroConfig.W f f).re ≤
      K * ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := by
  have hon := SquareRootThreshold.riemannHypothesis_iff_zetaZeroConfig_onLine.mp hRH
  have htemp := SquareRootThreshold.temperedConfig_zetaZeroConfig
  have hterm : ∀ ρ : zetaZeroConfig.carrier, (zetaZeroConfig.Wsummand f f ρ).re ≤
      K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
    intro ρ
    have hre := hon ρ ρ.2
    rw [WindowVisibilityLaw.re_Wsummand_onLine_eq _ _ hre]
    have hg : gammaOf (ρ : ℂ) = (((ρ : ℂ).im : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [WeilEF.gammaOf_re, WeilEF.gammaOf_im, hre]
    rw [hg, Complex.normSq_ofReal]
    have hb := hf _ (_root_.RHTower.zeta_two_le_abs_im ρ ρ.2)
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT f ((ρ : ℂ).im)‖ ^ 2 ≤
          (zetaZeroConfig.mult ρ : ℝ) * (K / (1 + (ρ : ℂ).im ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hm
      _ = K * ((zetaZeroConfig.mult ρ : ℝ) / (1 + (ρ : ℂ).im * (ρ : ℂ).im)) := by ring
  by_cases hs : Summable fun ρ : zetaZeroConfig.carrier => zetaZeroConfig.Wsummand f f ρ
  · have hre := Complex.hasSum_re hs.hasSum
    rw [ZeroConfig.W, ← hre.tsum_eq, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hre.summable (Summable.mul_left K htemp)
  · rw [ZeroConfig.W, tsum_eq_zero_of_not_summable hs, Complex.zero_re]
    exact mul_nonneg hK (tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf ρ); linarith))

/-- **Weil's form of three spread copies** is at most `3 Σ c_i² N²/L² · Σ_ρ m_ρ/(1 + γ²)`, with
`N` the decay constant of `β̂`. -/
theorem re_zetaW_threeSpread_le (hRH : RiemannHypothesis) (hβ : ContDiff ℝ 2 β)
    (hβs : ∀ v, 1 < |v| → β v = 0) {N : ℝ}
    (hN : ∀ s : ℝ, ‖paperFT (fun u => (β u : ℂ)) s‖ ^ 2 ≤ N ^ 2 / ((1 + |s|) ^ 2) ^ 2)
    {L : ℝ} (hL : 1 ≤ L) (d c₀ c₁ c₂ : ℝ) :
    (zetaZeroConfig.W (cx (threeSpread β L d c₀ c₁ c₂)) (cx (threeSpread β L d c₀ c₁ c₂))).re ≤
      3 * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) * N ^ 2 / L ^ 2 *
        ∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := by
  have hL0 : 0 < L := by linarith
  refine re_zetaW_le_of_riemannHypothesis hRH _ (by positivity) fun r hr => ?_
  set b := ‖paperFT (cx β) ((L * r : ℝ) : ℂ)‖
  have hb0 : 0 ≤ b := norm_nonneg _
  -- the transform of the combination is at most `(Σ |c_i|) L ‖β̂(Lr)‖`
  have hF : ‖paperFT (cx (threeSpread β L d c₀ c₁ c₂)) r‖ ≤
      (|c₀| + |c₁| + |c₂|) * (L * b) := by
    rw [paperFT_threeSpread hβ hβs hL0]
    refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_paperFT_spreadTest β hL0]
    rw [show ‖paperFT (cx β) ((L * r : ℝ) : ℂ)‖ = b from rfl]
    exact le_of_eq (by ring)
  -- decay of `β̂` at `Lr` with `|r| ≥ 2`, `L ≥ 1`
  have hdec : b ^ 2 ≤ N ^ 2 / (L ^ 4 * (1 + r ^ 2)) := by
    have h := hN (L * r)
    have hpos : 0 < L ^ 4 * (1 + r ^ 2) := mul_pos (pow_pos hL0 4) (by positivity)
    have ht : 2 ≤ |r| := hr
    have h4 : 4 ≤ r ^ 2 := by
      nlinarith [sq_abs r, mul_le_mul ht ht (by norm_num) (abs_nonneg r)]
    have hr4 : 1 + r ^ 2 ≤ r ^ 4 := by nlinarith
    have hLr : |L * r| = L * |r| := by rw [abs_mul, abs_of_pos hL0]
    have hle : L ^ 4 * (1 + r ^ 2) ≤ ((1 + |L * r|) ^ 2) ^ 2 := by
      rw [hLr]
      have hx : 0 ≤ L * |r| := mul_nonneg hL0.le (abs_nonneg r)
      have h1 : (L * |r|) ^ 4 ≤ ((1 + L * |r|) ^ 2) ^ 2 := by
        have := pow_le_pow_left₀ hx (show L * |r| ≤ 1 + L * |r| by linarith) 4
        calc (L * |r|) ^ 4 ≤ (1 + L * |r|) ^ 4 := this
          _ = ((1 + L * |r|) ^ 2) ^ 2 := by ring
      have habs4 : |r| ^ 4 = r ^ 4 := by
        rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, ← sq_abs r]
        ring
      have h2 : L ^ 4 * (1 + r ^ 2) ≤ (L * |r|) ^ 4 := by
        rw [mul_pow, habs4]
        exact mul_le_mul_of_nonneg_left hr4 (by positivity)
      linarith
    calc b ^ 2 ≤ N ^ 2 / ((1 + |L * r|) ^ 2) ^ 2 := h
      _ ≤ N ^ 2 / (L ^ 4 * (1 + r ^ 2)) :=
        div_le_div_of_nonneg_left (sq_nonneg N) hpos hle
  have hsum3 : (|c₀| + |c₁| + |c₂|) ^ 2 ≤ 3 * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) := by
    nlinarith [sq_nonneg (|c₀| - |c₁|), sq_nonneg (|c₀| - |c₂|), sq_nonneg (|c₁| - |c₂|),
      sq_abs c₀, sq_abs c₁, sq_abs c₂]
  have hS : 0 ≤ |c₀| + |c₁| + |c₂| := by positivity
  calc ‖paperFT (cx (threeSpread β L d c₀ c₁ c₂)) r‖ ^ 2 ≤
        ((|c₀| + |c₁| + |c₂|) * (L * b)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hF 2
    _ = (|c₀| + |c₁| + |c₂|) ^ 2 * L ^ 2 * b ^ 2 := by ring
    _ ≤ 3 * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) * L ^ 2 * (N ^ 2 / (L ^ 4 * (1 + r ^ 2))) := by
        gcongr
    _ = 3 * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) * N ^ 2 / L ^ 2 / (1 + r ^ 2) := by
        have hLne : L ≠ 0 := hL0.ne'
        have hr0 : (1 + r ^ 2) ≠ 0 := by positivity
        field_simp

/-! ### The plane of vanishing first charge -/

/-- The first charge `A(f) = ∫ f e^{−u/2}`. -/
def firstCharge (f : ℝ → ℝ) : ℝ := ∫ u, f u * Real.exp (-u / 2)

/-- The plane `a (g_0 − E g_1) + b (g_1 − E g_2)`, `E = e^{3L/2}`, of copies centred at
`d, d + 3L, d + 6L`. -/
def planeTest (β : ℝ → ℝ) (L d a b : ℝ) : ℝ → ℝ :=
  threeSpread β L d a (b - a * Real.exp (3 * L / 2)) (-(b * Real.exp (3 * L / 2)))

/-- **The plane lies in the hyperplane of vanishing first charge.** -/
theorem firstCharge_planeTest (hβ : ContDiff ℝ 2 β) (hβs : ∀ v, 1 < |v| → β v = 0) {L : ℝ}
    (hL : 0 < L) (d a b : ℝ) : firstCharge (planeTest β L d a b) = 0 := by
  have hi : ∀ e, Integrable fun u => spreadTest β L e u * Real.exp (-u / 2) := fun e =>
    ((contDiff_spreadTest hβ L e).continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hasCompactSupport_spreadTest hβs hL e).mul_right
  have hEF : Real.exp (3 * L / 2) * Real.exp (-(3 * L) / 2) = 1 := by
    rw [← Real.exp_add, show 3 * L / 2 + -(3 * L) / 2 = 0 by ring, Real.exp_zero]
  have h1 := integral_spreadTest_add_mul_exp_neg β L d (3 * L)
  have h2 := integral_spreadTest_add_mul_exp_neg β L (d + 3 * L) (3 * L)
  rw [show d + 3 * L + 3 * L = d + 6 * L by ring] at h2
  have e : (fun u => planeTest β L d a b u * Real.exp (-u / 2)) = fun u =>
      a * (spreadTest β L d u * Real.exp (-u / 2)) +
        (b - a * Real.exp (3 * L / 2)) * (spreadTest β L (d + 3 * L) u * Real.exp (-u / 2)) +
        -(b * Real.exp (3 * L / 2)) * (spreadTest β L (d + 6 * L) u * Real.exp (-u / 2)) := by
    funext u
    simp only [planeTest, threeSpread]
    ring
  have i0 : Integrable fun u => a * (spreadTest β L d u * Real.exp (-u / 2)) :=
    (hi d).const_mul _
  have i1 : Integrable fun u =>
      (b - a * Real.exp (3 * L / 2)) * (spreadTest β L (d + 3 * L) u * Real.exp (-u / 2)) :=
    (hi _).const_mul _
  have i2 : Integrable fun u =>
      -(b * Real.exp (3 * L / 2)) * (spreadTest β L (d + 6 * L) u * Real.exp (-u / 2)) :=
    (hi _).const_mul _
  have i01 : Integrable fun u => a * (spreadTest β L d u * Real.exp (-u / 2)) +
      (b - a * Real.exp (3 * L / 2)) * (spreadTest β L (d + 3 * L) u * Real.exp (-u / 2)) :=
    i0.add i1
  unfold firstCharge
  rw [e, integral_add i01 i2, integral_add i0 i1, integral_const_mul, integral_const_mul,
    integral_const_mul, h2, h1]
  linear_combination ((∫ u, spreadTest β L d u * Real.exp (-u / 2)) *
    (-a - b * Real.exp (-(3 * L) / 2))) * hEF

/-- The plane is a combination of three copies with coefficient square sum at least
`a² + b²`. -/
theorem planeTest_coeff_ge {L : ℝ} (hL : 0 ≤ L) (a b : ℝ) :
    a ^ 2 + b ^ 2 ≤ a ^ 2 + (b - a * Real.exp (3 * L / 2)) ^ 2 +
      (-(b * Real.exp (3 * L / 2))) ^ 2 := by
  have hE : 1 ≤ Real.exp (3 * L / 2) := Real.one_le_exp (by positivity)
  have hE2 : 1 ≤ Real.exp (3 * L / 2) ^ 2 := by nlinarith
  nlinarith [sq_nonneg (b - a * Real.exp (3 * L / 2)),
    mul_le_mul_of_nonneg_left hE2 (sq_nonneg b)]

/-! ### Both sides of the margin -/

theorem packetAutocorr_eq_zero_of_vanishing_off {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ∀ u, u < a ∨ b < u → f u = 0) (hx : b - a < x) : packetAutocorr f x = 0 := by
  have h : ∀ u, f u * f (u + x) = 0 := fun u => by
    by_cases hu : u < a
    · rw [hf u (Or.inl hu), zero_mul]
    · rw [hf (u + x) (Or.inr (by linarith)), mul_zero]
  simp only [packetAutocorr, h, integral_zero]

/-- **On packets of vanishing first charge the neutral form is Weil's form of the zeros**, and
so nonnegative under RH: at most one bound state at infinite block size. -/
theorem neutralForm_nonneg_of_charge_eq_zero (hRH : RiemannHypothesis) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {Q : ℕ}
    (hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0) (hA : firstCharge f = 0) :
    0 ≤ neutralForm Q f := by
  rw [neutralForm_eq_re_sub hf hfc hQ, Complex.sub_re, poleConfig_W_ofReal, Complex.ofReal_re]
  unfold firstCharge at hA
  rw [hA, zero_mul, mul_zero, sub_zero]
  exact re_zetaW_nonneg_of_riemannHypothesis hRH _

/-- **Under RH the margin of a long window tends to zero.** For every `ε > 0` there is `L₀ ≥ 1`
such that for `L ≥ L₀`, every window `[d − L, d + 7L]` and every `Q ≥ e^{8L}`, the plane
`planeTest β L d a b` of smooth packets in the window, of positive mass for `(a, b) ≠ 0`, carries
`0 ≤ N(f) ≤ ε ∫ f²`. -/
theorem exists_plane_neutralForm_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    (hβ : ContDiff ℝ 2 β) (hβs : ∀ v, 1 < |v| → β v = 0) (hβ0 : 0 < ∫ v, β v ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ (d : ℝ) (Q : ℕ), Real.exp (8 * L) ≤ Q →
      ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0 → 0 < ∫ u, planeTest β L d a b u ^ 2) ∧
        0 ≤ neutralForm Q (planeTest β L d a b) ∧
        neutralForm Q (planeTest β L d a b) ≤ ε * ∫ u, planeTest β L d a b u ^ 2 := by
  have hβc : HasCompactSupport β := HasCompactSupport.intro (isCompact_Icc (a := -1) (b := 1))
    fun v hv => hβs v (by
      simp only [Set.mem_Icc, not_and_or, not_le] at hv
      rcases hv with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith)
  obtain ⟨N, hN0, hN⟩ := _root_.RHTower.exists_normSq_paperFT_le hβ hβc
  obtain ⟨S, hS_def⟩ : ∃ S, S = ∑' ρ : zetaZeroConfig.carrier,
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) := ⟨_, rfl⟩
  have hS : 0 ≤ S := by
    rw [hS_def]
    exact tsum_nonneg fun ρ => div_nonneg (Nat.cast_nonneg _)
      (by have := Complex.normSq_nonneg (gammaOf ρ); linarith)
  obtain ⟨M, hM_def⟩ : ∃ M, M = ∫ v, β v ^ 2 := ⟨_, rfl⟩
  rw [← hM_def] at hβ0
  refine ⟨max 1 (3 * N ^ 2 * S / (ε * M)), le_max_left _ _, fun L hL d Q hQ a b => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hLc : 3 * N ^ 2 * S / (ε * M) ≤ L := (le_max_right _ _).trans hL
  set c₁ := b - a * Real.exp (3 * L / 2)
  set c₂ := -(b * Real.exp (3 * L / 2))
  have hplane : planeTest β L d a b = threeSpread β L d a c₁ c₂ := rfl
  have hmass : ∫ u, planeTest β L d a b u ^ 2 = (a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (L * M) := by
    rw [hplane, hM_def]
    exact integral_threeSpread_sq hβ hβs hL0 d a c₁ c₂
  have hfd : ContDiff ℝ 2 (planeTest β L d a b) := contDiff_threeSpread hβ L d a c₁ c₂
  have hfc : HasCompactSupport (planeTest β L d a b) :=
    hasCompactSupport_threeSpread hβs hL0 d a c₁ c₂
  have hQ' : ∀ n : ℕ, Q < n → packetAutocorr (planeTest β L d a b) (Real.log n) = 0 := by
    intro n hn
    refine packetAutocorr_eq_zero_of_vanishing_off (a := d - L) (b := d + 7 * L)
      (fun u hu => threeSpread_eq_zero hβs hL0 d a c₁ c₂ hu) ?_
    have hnQ : Real.exp (8 * L) < n := lt_of_le_of_lt hQ (by exact_mod_cast hn)
    have := (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < n by omega))).mpr hnQ
    linarith
  have hA := firstCharge_planeTest hβ hβs hL0 d a b
  have hW := re_zetaW_threeSpread_le hRH hβ hβs hN hL1 d a c₁ c₂
  rw [← hS_def] at hW
  have hneut : neutralForm Q (planeTest β L d a b) =
      (zetaZeroConfig.W (cx (planeTest β L d a b)) (cx (planeTest β L d a b))).re := by
    rw [neutralForm_eq_re_sub hfd hfc hQ', Complex.sub_re, poleConfig_W_ofReal,
      Complex.ofReal_re]
    unfold firstCharge at hA
    rw [hA, zero_mul, mul_zero, sub_zero]
    rfl
  have hc : 0 ≤ a ^ 2 + c₁ ^ 2 + c₂ ^ 2 := by positivity
  refine ⟨fun hab => ?_, neutralForm_nonneg_of_charge_eq_zero hRH hfd hfc hQ' hA, ?_⟩
  · rw [hmass]
    have : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with h | h
      · have h2 := mul_pos (abs_pos.mpr h) (abs_pos.mpr h)
        nlinarith [abs_mul_abs_self a, sq_nonneg b]
      · have h2 := mul_pos (abs_pos.mpr h) (abs_pos.mpr h)
        nlinarith [abs_mul_abs_self b, sq_nonneg a]
    have hge : a ^ 2 + b ^ 2 ≤ a ^ 2 + c₁ ^ 2 + c₂ ^ 2 := planeTest_coeff_ge hL0.le a b
    exact mul_pos (by linarith) (mul_pos hL0 hβ0)
  · rw [hneut, hmass, hplane]
    refine hW.trans ?_
    -- `3 N² S / L² ≤ ε L M` because `L³ ≥ L ≥ 3 N² S/(ε M)`
    have hL3 : L ≤ L ^ 3 := by
      nlinarith [mul_nonneg hL0.le (sub_nonneg.mpr hL1),
        mul_nonneg (mul_nonneg hL0.le hL0.le) (sub_nonneg.mpr hL1)]
    have hkey : 3 * N ^ 2 * S ≤ ε * M * L ^ 3 := by
      have h1 : 3 * N ^ 2 * S ≤ ε * M * L := by
        rw [div_le_iff₀ (mul_pos hε hβ0)] at hLc
        linarith
      nlinarith [mul_pos hε hβ0]
    rw [show 3 * (a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * N ^ 2 / L ^ 2 * S =
      (a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (3 * N ^ 2 * S) / L ^ 2 by ring,
      div_le_iff₀ (pow_pos hL0 2)]
    calc (a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (3 * N ^ 2 * S) ≤
          (a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (ε * M * L ^ 3) := mul_le_mul_of_nonneg_left hkey hc
      _ = ε * ((a ^ 2 + c₁ ^ 2 + c₂ ^ 2) * (L * M)) * L ^ 2 := by ring

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
