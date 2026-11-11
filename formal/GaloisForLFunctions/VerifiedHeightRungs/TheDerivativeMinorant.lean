import GaloisForLFunctions.VerifiedHeightRungs.ThePrimePolynomialIsRarelyLarge
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# The derivative minorant

For a test `g` with derivative `g'`, `ĝ'(z) = −iz ĝ(z)`. At an on-line zero at distance `x` from `t` the summand of

  `D = σ² W(S_ξ g, S_ξ g) − W(S_ξ g', S_ξ g')`,  `t = −2πξ`,

is `m (σ² − x²) |ĝ(x)|²`, nonpositive once `|x| ≥ σ`: the transform of the form is a minorant of the interval
`[t − σ, t + σ]`. So if no zero lies within `σ` of `t` and RH holds within `e^Y` of `t`, only the zeros beyond `e^Y`
can make `D` positive, and they cost `16 B² Y⁻² · 5760 log(|t| + 3)` (`re_minorantForm_le_of_gap`). Clusters of
zeros away from `t` only lower `D`; no local count enters.

The test is `g(u) = φ(u/Y)`, `φ` a smooth bump (`1` on `[−½, ½]`, support in `[−1, 1]`), with `ĝ(z) = Y φ̂(Yz)` and
`ĝ'(z) = φ̂'(Yz)`, both decaying like `(1 + Y|Re z|)⁻²`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### The profile -/

/-- The smooth bump: `1` on `[−½, ½]`, supported in `[−1, 1]`. -/
def minorantBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The profile `φ`. -/
def minorantProfile (u : ℝ) : ℂ := ((minorantBump u : ℝ) : ℂ)

/-- Its derivative `φ'`. -/
def minorantProfileD : ℝ → ℂ := deriv minorantProfile

theorem minorantProfile_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) minorantProfile :=
  Complex.ofRealCLM.contDiff.comp minorantBump.contDiff

theorem minorantProfileD_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) minorantProfileD := by
  have h := ContDiff.iterate_deriv 1 minorantProfile_smooth
  rw [Function.iterate_one] at h
  exact h

theorem minorantProfile_contDiff {n : ℕ} : ContDiff ℝ n minorantProfile :=
  minorantProfile_smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

theorem minorantProfileD_contDiff {n : ℕ} : ContDiff ℝ n minorantProfileD :=
  minorantProfileD_smooth.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))

theorem minorantProfile_supp : ∀ u, minorantProfile u ≠ 0 → |u| ≤ 1 := by
  intro u hu
  have h : u ∈ Function.support minorantBump := fun h => hu (by simp [minorantProfile, h])
  rw [minorantBump.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at h
  exact h.le

theorem minorantProfileD_supp : ∀ u, minorantProfileD u ≠ 0 → |u| ≤ 1 := by
  intro u hu
  have h1 : u ∈ tsupport minorantProfileD := subset_tsupport _ hu
  have h2 := tsupport_subset_of_support_subset_abs minorantProfile_supp
    ((tsupport_deriv_subset (f := minorantProfile)) h1)
  exact abs_le.2 h2

/-- `E₀ = ∫ |φ|²`. -/
def minorantE₀ : ℝ := ∫ u, ‖minorantProfile u‖ ^ 2

/-- `E₁ = ∫ |φ'|²`. -/
def minorantE₁ : ℝ := ∫ u, ‖minorantProfileD u‖ ^ 2

theorem one_le_minorantE₀ : 1 ≤ minorantE₀ := by
  have hc : Continuous fun u => ‖minorantProfile u‖ ^ 2 :=
    (minorantProfile_contDiff (n := 0)).continuous.norm.pow 2
  have hcs : HasCompactSupport fun u => ‖minorantProfile u‖ ^ 2 := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun u hu => ?_
    have hne : minorantProfile u ≠ 0 := fun h => hu (by simp [h])
    exact abs_le.1 (minorantProfile_supp u hne)
  have hi : Integrable fun u => ‖minorantProfile u‖ ^ 2 := hc.integrable_of_hasCompactSupport hcs
  have hone : ∀ u ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖minorantProfile u‖ ^ 2 = 1 := by
    intro u hu
    have hb : minorantBump u = 1 := minorantBump.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      exact abs_le.2 hu)
    simp [minorantProfile, hb]
  have h1 : ∫ u in Icc (-(1 / 2) : ℝ) (1 / 2), ‖minorantProfile u‖ ^ 2 = 1 := by
    rw [setIntegral_congr_fun measurableSet_Icc hone, setIntegral_const]
    simp [Measure.real, Real.volume_Icc]
    norm_num
  calc (1 : ℝ) = ∫ u in Icc (-(1 / 2) : ℝ) (1 / 2), ‖minorantProfile u‖ ^ 2 := h1.symm
    _ ≤ minorantE₀ := setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)

theorem minorantE₁_nonneg : 0 ≤ minorantE₁ := integral_nonneg fun _ => sq_nonneg _

/-- The decay constant `B` of `φ̂` and `φ̂'`. -/
def minorantB : ℝ :=
  4 * ((∫ u, ‖minorantProfile u‖) + ∫ u, ‖deriv (deriv minorantProfile) u‖) +
    4 * ((∫ u, ‖minorantProfileD u‖) + ∫ u, ‖deriv (deriv minorantProfileD) u‖)

theorem norm_paperFT_minorantProfile_le (w : ℂ) :
    ‖paperFT minorantProfile w‖ ≤ minorantB * Real.exp |w.im| / (1 + |w.re|) ^ 2 := by
  have h := norm_paperFT_le_decay (a := 1) minorantProfile_contDiff minorantProfile_supp w
  rw [mul_one] at h
  refine h.trans ?_
  rw [mul_comm (Real.exp _)]
  gcongr
  unfold minorantB
  have : 0 ≤ 4 * ((∫ u, ‖minorantProfileD u‖) + ∫ u, ‖deriv (deriv minorantProfileD) u‖) := by
    have h1 : 0 ≤ ∫ u, ‖minorantProfileD u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv minorantProfileD) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  linarith only [this]

theorem norm_paperFT_minorantProfileD_le (w : ℂ) :
    ‖paperFT minorantProfileD w‖ ≤ minorantB * Real.exp |w.im| / (1 + |w.re|) ^ 2 := by
  have h := norm_paperFT_le_decay (a := 1) minorantProfileD_contDiff minorantProfileD_supp w
  rw [mul_one] at h
  refine h.trans ?_
  rw [mul_comm (Real.exp _)]
  gcongr
  unfold minorantB
  have : 0 ≤ 4 * ((∫ u, ‖minorantProfile u‖) + ∫ u, ‖deriv (deriv minorantProfile) u‖) := by
    have h1 : 0 ≤ ∫ u, ‖minorantProfile u‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ u, ‖deriv (deriv minorantProfile) u‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  linarith only [this]

theorem minorantB_nonneg : 0 ≤ minorantB := by
  have h := norm_paperFT_minorantProfile_le 0
  have h0 := norm_nonneg (paperFT minorantProfile 0)
  simp only [Complex.zero_im, Complex.zero_re, abs_zero, Real.exp_zero, mul_one, add_zero, one_pow,
    div_one] at h
  linarith only [h, h0]

/-! ### The test of width `Y` -/

/-- The test `g(u) = φ(u/Y)`. -/
def minorantTest (Y : ℝ) (u : ℝ) : ℂ := minorantProfile (Y⁻¹ * u)

/-- Its derivative `g'`. -/
def minorantTestD (Y : ℝ) : ℝ → ℂ := deriv (minorantTest Y)

theorem minorantTestD_eq (Y : ℝ) :
    minorantTestD Y = fun u => (Y⁻¹ : ℂ) * minorantProfileD (Y⁻¹ * u) := by
  funext u
  change deriv (fun x => minorantProfile (Y⁻¹ * x)) u = _
  rw [deriv_comp_mul_left, Complex.real_smul]
  push_cast
  rfl

theorem minorantTest_contDiff (Y : ℝ) {n : ℕ} : ContDiff ℝ n (minorantTest Y) :=
  minorantProfile_contDiff.comp (contDiff_const.mul contDiff_id)

theorem minorantTestD_contDiff (Y : ℝ) {n : ℕ} : ContDiff ℝ n (minorantTestD Y) := by
  rw [minorantTestD_eq]
  exact contDiff_const.mul (minorantProfileD_contDiff.comp (contDiff_const.mul contDiff_id))

theorem abs_le_of_inv_mul {Y u : ℝ} (hY : 0 < Y) (h : |Y⁻¹ * u| ≤ 1) : |u| ≤ Y := by
  rw [abs_mul, abs_inv, abs_of_pos hY, inv_mul_le_iff₀ hY, mul_one] at h
  exact h

theorem minorantTest_supp {Y : ℝ} (hY : 0 < Y) : ∀ u, minorantTest Y u ≠ 0 → |u| ≤ Y := fun _ hu =>
  abs_le_of_inv_mul hY (minorantProfile_supp _ hu)

theorem minorantTestD_supp {Y : ℝ} (hY : 0 < Y) : ∀ u, minorantTestD Y u ≠ 0 → |u| ≤ Y := by
  intro u hu
  rw [minorantTestD_eq] at hu
  exact abs_le_of_inv_mul hY (minorantProfileD_supp _ fun h => hu (by simp [h]))

theorem tsupport_minorantTest {Y : ℝ} (hY : 0 < Y) : tsupport (minorantTest Y) ⊆ Icc (-Y) Y :=
  tsupport_subset_of_support_subset_abs (minorantTest_supp hY)

theorem tsupport_minorantTestD {Y : ℝ} (hY : 0 < Y) : tsupport (minorantTestD Y) ⊆ Icc (-Y) Y :=
  tsupport_subset_of_support_subset_abs (minorantTestD_supp hY)

/-- Dilation: `∫ h(u/Y) e^{izu} du = Y ĥ(Yz)`. -/
theorem paperFT_comp_mul_left {Y : ℝ} (hY : 0 < Y) (h : ℝ → ℂ) (z : ℂ) :
    paperFT (fun u => h (Y⁻¹ * u)) z = Y * paperFT h (Y * z) := by
  rw [paperFT_def, paperFT_def]
  have hI := Measure.integral_comp_mul_left (fun v => h v * cexp (I * ((Y : ℂ) * z) * v)) Y⁻¹
  rw [inv_inv, abs_of_pos hY, Complex.real_smul] at hI
  rw [← hI]
  congr 1 with _
  congr 2
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  push_cast
  field_simp

theorem paperFT_minorantTest {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    paperFT (minorantTest Y) z = Y * paperFT minorantProfile (Y * z) :=
  paperFT_comp_mul_left hY minorantProfile z

theorem paperFT_minorantTestD {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    paperFT (minorantTestD Y) z = paperFT minorantProfileD (Y * z) := by
  rw [minorantTestD_eq]
  have h1 : paperFT (fun u => (Y⁻¹ : ℂ) * minorantProfileD (Y⁻¹ * u)) z =
      (Y⁻¹ : ℂ) * paperFT (fun u => minorantProfileD (Y⁻¹ * u)) z := by
    rw [paperFT_def, paperFT_def, ← integral_const_mul]
    congr 1 with u
    ring
  have hYC : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  rw [h1, paperFT_comp_mul_left hY]
  field_simp

/-- `ĝ'(z) = −iz ĝ(z)`. -/
theorem paperFT_minorantTestD_eq_mul {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    paperFT (minorantTestD Y) z = -(I * z) * paperFT (minorantTest Y) z :=
  EvenSector.paperFT_deriv_of_compact (minorantTest_contDiff Y)
    (hasCompactSupport_of_tsupport_subset_Icc (tsupport_minorantTest hY)) z

theorem norm_paperFT_minorantTest_le {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖paperFT (minorantTest Y) z‖ ≤ Y * minorantB * Real.exp (Y * |z.im|) / (1 + Y * |z.re|) ^ 2 := by
  rw [paperFT_minorantTest hY, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have h := norm_paperFT_minorantProfile_le ((Y : ℂ) * z)
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_mul, abs_of_pos hY] at h
  calc Y * ‖paperFT minorantProfile ((Y : ℂ) * z)‖
      ≤ Y * (minorantB * Real.exp (Y * |z.im|) / (1 + Y * |z.re|) ^ 2) := mul_le_mul_of_nonneg_left h hY.le
    _ = _ := by ring

theorem norm_paperFT_minorantTestD_le {Y : ℝ} (hY : 0 < Y) (z : ℂ) :
    ‖paperFT (minorantTestD Y) z‖ ≤ minorantB * Real.exp (Y * |z.im|) / (1 + Y * |z.re|) ^ 2 := by
  rw [paperFT_minorantTestD hY]
  have h := norm_paperFT_minorantProfileD_le ((Y : ℂ) * z)
  rwa [Complex.re_ofReal_mul, Complex.im_ofReal_mul, abs_mul, abs_mul, abs_of_pos hY] at h

/-! ### The minorant form -/

/-- The minorant form `D = σ² W(S_ξ g, S_ξ g) − W(S_ξ g', S_ξ g')`. -/
def minorantForm (σ Y ξ : ℝ) : ℂ :=
  (σ ^ 2 : ℂ) * zetaZeroConfig.W (heightShift ξ (minorantTest Y)) (heightShift ξ (minorantTest Y)) -
    zetaZeroConfig.W (heightShift ξ (minorantTestD Y)) (heightShift ξ (minorantTestD Y))

theorem Wsummand_heightShift_eq (f : ℝ → ℂ) (t : ℝ) (ρ : ℂ) :
    zetaZeroConfig.Wsummand (heightShift (-t / (2 * π)) f) (heightShift (-t / (2 * π)) f) ρ =
      (zetaZeroConfig.mult ρ : ℂ) * paperFT f (gammaOf ρ - t) * conj (paperFT f (conj (gammaOf ρ) - t)) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : (2 * (π : ℂ) * ((-t / (2 * π) : ℝ) : ℂ)) = -(t : ℂ) := by
    push_cast
    field_simp
  unfold ZeroConfig.Wsummand
  rw [paperFT_heightShift, paperFT_heightShift, e, ← sub_eq_add_neg, ← sub_eq_add_neg]

/-- On the line, `γ(ρ) = Im ρ`. -/
theorem gammaOf_eq_of_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) : gammaOf ρ = ((ρ.im : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [WeilEF.gammaOf_re, Complex.ofReal_re]
  · rw [WeilEF.gammaOf_im, Complex.ofReal_im, hρ, sub_self]

/-- **The summand at an on-line zero** is `m (σ² − x²) |ĝ(x)|²`. -/
theorem re_minorant_summand_of_re {σ Y t : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((σ ^ 2 : ℂ) * zetaZeroConfig.Wsummand (heightShift (-t / (2 * π)) (minorantTest Y))
        (heightShift (-t / (2 * π)) (minorantTest Y)) ρ -
      zetaZeroConfig.Wsummand (heightShift (-t / (2 * π)) (minorantTestD Y))
        (heightShift (-t / (2 * π)) (minorantTestD Y)) ρ).re =
      (zetaZeroConfig.mult ρ : ℝ) * (σ ^ 2 - (ρ.im - t) ^ 2) *
        ‖paperFT (minorantTest Y) ((ρ.im - t : ℝ) : ℂ)‖ ^ 2 := by
  rw [Wsummand_heightShift_eq, Wsummand_heightShift_eq, gammaOf_eq_of_re hρ, Complex.conj_ofReal]
  have hx : ((ρ.im : ℝ) : ℂ) - (t : ℂ) = ((ρ.im - t : ℝ) : ℂ) := by push_cast; ring
  rw [hx, paperFT_minorantTestD_eq_mul hY]
  set w := paperFT (minorantTest Y) ((ρ.im - t : ℝ) : ℂ)
  set x : ℝ := ρ.im - t
  have h1 : w * conj w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h2 : -(I * (x : ℂ)) * w * conj (-(I * (x : ℂ)) * w) = ((x ^ 2 * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [map_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    have : -(I * (x : ℂ)) * w * (-(-I * (x : ℂ)) * conj w) = -(I * I) * (x : ℂ) ^ 2 * (w * conj w) := by ring
    rw [this, h1, Complex.I_mul_I]
    push_cast
    ring
  have e : (σ ^ 2 : ℂ) * ((zetaZeroConfig.mult ρ : ℂ) * w * conj w) -
      (zetaZeroConfig.mult ρ : ℂ) * (-(I * (x : ℂ)) * w) * conj (-(I * (x : ℂ)) * w) =
      (((zetaZeroConfig.mult ρ : ℝ) * (σ ^ 2 - x ^ 2) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : (σ ^ 2 : ℂ) * ((zetaZeroConfig.mult ρ : ℂ) * w * conj w) =
        (σ ^ 2 : ℂ) * (zetaZeroConfig.mult ρ : ℂ) * (w * conj w) := by ring
    have e2 : (zetaZeroConfig.mult ρ : ℂ) * (-(I * (x : ℂ)) * w) * conj (-(I * (x : ℂ)) * w) =
        (zetaZeroConfig.mult ρ : ℂ) * (-(I * (x : ℂ)) * w * conj (-(I * (x : ℂ)) * w)) := by ring
    rw [e1, e2, h1, h2]
    push_cast
    ring
  rw [e, Complex.ofReal_re]

/-- The size of the two summands at any zero of the strip. -/
theorem norm_minorant_summands_le {σ Y t : ℝ} (hY : 0 < Y) {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    ‖(σ ^ 2 : ℂ) * zetaZeroConfig.Wsummand (heightShift (-t / (2 * π)) (minorantTest Y))
        (heightShift (-t / (2 * π)) (minorantTest Y)) ρ‖ +
      ‖zetaZeroConfig.Wsummand (heightShift (-t / (2 * π)) (minorantTestD Y))
        (heightShift (-t / (2 * π)) (minorantTestD Y)) ρ‖ ≤
      (zetaZeroConfig.mult ρ : ℝ) * ((σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y /
        (1 + Y * |ρ.im - t|) ^ 4) := by
  have hst := zetaZeroConfig.strip ρ hρ
  have hδ : |1 / 2 - ρ.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith only [hst.1, hst.2]
  have hB := minorantB_nonneg
  rw [Wsummand_heightShift_eq, Wsummand_heightShift_eq]
  have e1 : (gammaOf ρ - t).re = ρ.im - t := by simp [WeilEF.gammaOf_re]
  have e2 : |(gammaOf ρ - t).im| = |1 / 2 - ρ.re| := by simp [WeilEF.gammaOf_im]
  have e3 : (conj (gammaOf ρ) - t).re = ρ.im - t := by simp [WeilEF.gammaOf_re]
  have e4 : |(conj (gammaOf ρ) - t).im| = |1 / 2 - ρ.re| := by
    simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, sub_zero, WeilEF.gammaOf_im, abs_neg]
  obtain ⟨x, hx⟩ : ∃ x, x = |ρ.im - t| := ⟨_, rfl⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = |1 / 2 - ρ.re| := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ abs_nonneg _
  have hD1 : 0 < 1 + Y * x := by nlinarith only [hx0, hY]
  have hD : 0 < (1 + Y * x) ^ 2 := pow_pos hD1 2
  have g1 := norm_paperFT_minorantTest_le hY (gammaOf ρ - t)
  have g2 := norm_paperFT_minorantTest_le hY (conj (gammaOf ρ) - t)
  have d1 := norm_paperFT_minorantTestD_le hY (gammaOf ρ - t)
  have d2 := norm_paperFT_minorantTestD_le hY (conj (gammaOf ρ) - t)
  rw [e1, e2, ← hx, ← hδdef] at g1 d1
  rw [e3, e4, ← hx, ← hδdef] at g2 d2
  have hexp : Real.exp (Y * δ) * Real.exp (Y * δ) ≤ Real.exp Y := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (hδdef ▸ hδ) hY.le
    linarith only [this]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hprod1 : ‖paperFT (minorantTest Y) (gammaOf ρ - t)‖ * ‖paperFT (minorantTest Y) (conj (gammaOf ρ) - t)‖ ≤
      Y ^ 2 * minorantB ^ 2 * Real.exp Y / (1 + Y * x) ^ 4 := by
    refine (mul_le_mul g1 g2 (norm_nonneg _)
      (div_nonneg (mul_nonneg (mul_nonneg hY.le hB) (Real.exp_pos _).le) hD.le)).trans ?_
    rw [div_mul_div_comm, ← pow_add, div_le_div_iff_of_pos_right (pow_pos hD1 _)]
    have : Y * minorantB * Real.exp (Y * δ) * (Y * minorantB * Real.exp (Y * δ)) =
        Y ^ 2 * minorantB ^ 2 * (Real.exp (Y * δ) * Real.exp (Y * δ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hprod2 : ‖paperFT (minorantTestD Y) (gammaOf ρ - t)‖ *
      ‖paperFT (minorantTestD Y) (conj (gammaOf ρ) - t)‖ ≤ minorantB ^ 2 * Real.exp Y / (1 + Y * x) ^ 4 := by
    refine (mul_le_mul d1 d2 (norm_nonneg _)
      (div_nonneg (mul_nonneg hB (Real.exp_pos _).le) hD.le)).trans ?_
    rw [div_mul_div_comm, ← pow_add, div_le_div_iff_of_pos_right (pow_pos hD1 _)]
    have : minorantB * Real.exp (Y * δ) * (minorantB * Real.exp (Y * δ)) =
        minorantB ^ 2 * (Real.exp (Y * δ) * Real.exp (Y * δ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  simp only [norm_mul, Complex.norm_conj, Complex.norm_natCast, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  rw [sq_abs]
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  calc σ ^ 2 * ((zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (minorantTest Y) (gammaOf ρ - t)‖ *
        ‖paperFT (minorantTest Y) (conj (gammaOf ρ) - t)‖) +
        (zetaZeroConfig.mult ρ : ℝ) * ‖paperFT (minorantTestD Y) (gammaOf ρ - t)‖ *
          ‖paperFT (minorantTestD Y) (conj (gammaOf ρ) - t)‖
      = (zetaZeroConfig.mult ρ : ℝ) * (σ ^ 2 * (‖paperFT (minorantTest Y) (gammaOf ρ - t)‖ *
        ‖paperFT (minorantTest Y) (conj (gammaOf ρ) - t)‖) + ‖paperFT (minorantTestD Y) (gammaOf ρ - t)‖ *
          ‖paperFT (minorantTestD Y) (conj (gammaOf ρ) - t)‖) := by ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * (σ ^ 2 * (Y ^ 2 * minorantB ^ 2 * Real.exp Y / (1 + Y * x) ^ 4) +
        minorantB ^ 2 * Real.exp Y / (1 + Y * x) ^ 4) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hprod1 hσ2) hprod2) hm
    _ = _ := by rw [← hx]; ring

/-- `(σ²Y² + 1) e^Y (1 + Yx)⁻⁴ ≤ 16 Y⁻² (1 + x)⁻³` beyond `x ≥ e^Y`. -/
theorem minorant_far_weight_le {σ Y x : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 1 ≤ Y) (hx : Real.exp Y ≤ x) :
    (σ ^ 2 * Y ^ 2 + 1) * Real.exp Y / (1 + Y * x) ^ 4 ≤ 16 / Y ^ 2 * (1 / (1 + x) ^ 3) := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hx1 : 1 ≤ x := (Real.one_le_exp hY0.le).trans hx
  have hx0 : 0 < x := by linarith only [hx1]
  rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : σ ^ 2 * Y ^ 2 + 1 ≤ 2 * Y ^ 2 := by
    have : σ ^ 2 ≤ 1 := by nlinarith only [hσ, hσ1]
    nlinarith only [this, hY]
  have h2 : (1 + x) ^ 3 ≤ 8 * x ^ 3 := by
    have : 1 + x ≤ 2 * x := by linarith only [hx1]
    calc (1 + x) ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ (by positivity) this 3
      _ = 8 * x ^ 3 := by ring
  have h3 : (Y * x) ^ 4 ≤ (1 + Y * x) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith only) 4
  calc (σ ^ 2 * Y ^ 2 + 1) * Real.exp Y * (Y ^ 2 * (1 + x) ^ 3)
      ≤ (2 * Y ^ 2) * x * (Y ^ 2 * (8 * x ^ 3)) := by
        gcongr
    _ = 16 * (Y * x) ^ 4 := by ring
    _ ≤ 16 * (1 + Y * x) ^ 4 := by linarith only [h3]

/-- **No zero within `σ` of `t`.** Then the minorant form is at most the cost of the zeros beyond `e^Y`. -/
theorem re_minorantForm_le_of_gap {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 1 ≤ Y)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2)
    (hgap : ∀ ρ ∈ zetaZeroConfig.carrier, σ ≤ |ρ.im - t|) :
    (minorantForm σ Y (-t / (2 * π))).re ≤
      16 * minorantB ^ 2 / Y ^ 2 * (24 * 240 * Real.log (|t| + 3)) := by
  have hY0 : 0 < Y := by linarith only [hY]
  have hB := minorantB_nonneg
  set ξ := -t / (2 * π) with hξ
  obtain ⟨hwsum, hwle⟩ := window_tsum_le zetaZeroConfig (A₀ := 240) (by norm_num) zeta_unit_count_le_240 t
  set w : zetaZeroConfig.carrier → ℝ := fun ρ => (zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3
    with hw
  set A : zetaZeroConfig.carrier → ℂ := fun ρ => (σ ^ 2 : ℂ) *
    zetaZeroConfig.Wsummand (heightShift ξ (minorantTest Y)) (heightShift ξ (minorantTest Y)) ρ with hA
  set Bs : zetaZeroConfig.carrier → ℂ := fun ρ =>
    zetaZeroConfig.Wsummand (heightShift ξ (minorantTestD Y)) (heightShift ξ (minorantTestD Y)) ρ with hBs
  -- Both families are summable: `‖·‖ ≤ (Y²+1) B² e^Y · m (1 + x)⁻³`.
  have hcomp : ∀ ρ : zetaZeroConfig.carrier, ‖A ρ‖ + ‖Bs ρ‖ ≤ (σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 *
      Real.exp Y * w ρ := by
    intro ρ
    have h := norm_minorant_summands_le (σ := σ) (t := t) hY0 ρ.2
    refine h.trans ?_
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hx := abs_nonneg ((ρ : ℂ).im - t)
    have hle : (1 + |(ρ : ℂ).im - t|) ^ 3 ≤ (1 + Y * |(ρ : ℂ).im - t|) ^ 4 := by
      have h1 : 1 + |(ρ : ℂ).im - t| ≤ 1 + Y * |(ρ : ℂ).im - t| := by nlinarith only [hY, hx]
      have h2 : (1 : ℝ) ≤ 1 + Y * |(ρ : ℂ).im - t| := by nlinarith only [hY0, hx]
      calc (1 + |(ρ : ℂ).im - t|) ^ 3 ≤ (1 + Y * |(ρ : ℂ).im - t|) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
        _ ≤ (1 + Y * |(ρ : ℂ).im - t|) ^ 4 := pow_le_pow_right₀ h2 (by norm_num)
    rw [hw]
    simp only
    rw [div_eq_mul_one_div, div_eq_mul_one_div ((zetaZeroConfig.mult ρ : ℝ))]
    have : 1 / (1 + Y * |(ρ : ℂ).im - t|) ^ 4 ≤ 1 / (1 + |(ρ : ℂ).im - t|) ^ 3 :=
      one_div_le_one_div_of_le (by positivity) hle
    have hc : 0 ≤ (σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y := by positivity
    calc (zetaZeroConfig.mult ρ : ℝ) * ((σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y *
          (1 / (1 + Y * |(ρ : ℂ).im - t|) ^ 4))
        ≤ (zetaZeroConfig.mult ρ : ℝ) * ((σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y *
          (1 / (1 + |(ρ : ℂ).im - t|) ^ 3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hc) hm
      _ = _ := by ring
  have hsumR : Summable fun ρ => (σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y * w ρ := hwsum.mul_left _
  have hAs : Summable A := Summable.of_norm_bounded hsumR fun ρ =>
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hcomp ρ)
  have hBss : Summable Bs := Summable.of_norm_bounded hsumR fun ρ =>
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hcomp ρ)
  have hform : minorantForm σ Y ξ = ∑' ρ, (A ρ - Bs ρ) := by
    rw [minorantForm, ZeroConfig.W, ZeroConfig.W, ← tsum_mul_left, ← hAs.tsum_sub hBss]
  have hDs : Summable fun ρ => A ρ - Bs ρ := hAs.sub hBss
  rw [hform, Complex.re_tsum hDs]
  -- Termwise.
  have hterm : ∀ ρ : zetaZeroConfig.carrier, (A ρ - Bs ρ).re ≤ 16 * minorantB ^ 2 / Y ^ 2 * w ρ := by
    intro ρ
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
    have hw0 : 0 ≤ w ρ := by rw [hw]; positivity
    rcases le_or_gt |(ρ : ℂ).im - t| (Real.exp Y) with hnear | hfar
    · have hre := hon ρ ρ.2 hnear
      have h := re_minorant_summand_of_re (σ := σ) (t := t) hY0 hre
      change ((σ ^ 2 : ℂ) * _ - _).re = _ at h
      simp only [hA, hBs]
      rw [h]
      have hg := hgap ρ ρ.2
      have hsq : σ ^ 2 ≤ ((ρ : ℂ).im - t) ^ 2 := by
        rw [← sq_abs ((ρ : ℂ).im - t)]
        exact pow_le_pow_left₀ hσ.le hg 2
      have : (zetaZeroConfig.mult ρ : ℝ) * (σ ^ 2 - ((ρ : ℂ).im - t) ^ 2) *
          ‖paperFT (minorantTest Y) (((ρ : ℂ).im - t : ℝ) : ℂ)‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hm (by linarith only [hsq]))
          (sq_nonneg _)
      have : 0 ≤ 16 * minorantB ^ 2 / Y ^ 2 * w ρ := by positivity
      linarith
    · have h1 : (A ρ - Bs ρ).re ≤ ‖A ρ‖ + ‖Bs ρ‖ :=
        (Complex.re_le_norm _).trans (norm_sub_le _ _)
      have h2 := norm_minorant_summands_le (σ := σ) (t := t) hY0 ρ.2
      have h3 := minorant_far_weight_le hσ hσ1 hY hfar.le
      have h4 : (zetaZeroConfig.mult ρ : ℝ) * ((σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y /
          (1 + Y * |(ρ : ℂ).im - t|) ^ 4) ≤ 16 * minorantB ^ 2 / Y ^ 2 * w ρ := by
        rw [hw]
        have e : (σ ^ 2 * Y ^ 2 + 1) * minorantB ^ 2 * Real.exp Y / (1 + Y * |(ρ : ℂ).im - t|) ^ 4 =
            minorantB ^ 2 * ((σ ^ 2 * Y ^ 2 + 1) * Real.exp Y / (1 + Y * |(ρ : ℂ).im - t|) ^ 4) := by ring
        rw [e]
        calc (zetaZeroConfig.mult ρ : ℝ) * (minorantB ^ 2 * ((σ ^ 2 * Y ^ 2 + 1) * Real.exp Y /
              (1 + Y * |(ρ : ℂ).im - t|) ^ 4))
            ≤ (zetaZeroConfig.mult ρ : ℝ) * (minorantB ^ 2 * (16 / Y ^ 2 * (1 / (1 + |(ρ : ℂ).im - t|) ^ 3))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg _)) hm
          _ = _ := by ring
      simp only [hA, hBs] at h1 h2 ⊢
      linarith only [h1, h2, h4]
  have hsumW : Summable fun ρ => 16 * minorantB ^ 2 / Y ^ 2 * w ρ := hwsum.mul_left _
  calc ∑' ρ, (A ρ - Bs ρ).re ≤ ∑' ρ, 16 * minorantB ^ 2 / Y ^ 2 * w ρ :=
        (Complex.reCLM.summable hDs).tsum_le_tsum hterm hsumW
    _ = 16 * minorantB ^ 2 / Y ^ 2 * ∑' ρ, w ρ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hwle (by positivity)

end

end GaloisForLFunctions.VerifiedHeightRungs
