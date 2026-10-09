import GaloisForLFunctions.HTGeometry.ModularCellPointPair
import GaloisForLFunctions.HTGeometry.ModularFundamentalDomainVolume
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Point-pair operators on fields twisted by a representation of `SL(2, ℤ)`

Let `ρ` be a unitary representation of `SL(2, ℤ)` on `ℂ^ι` (`ι` finite).
For a continuous bounded kernel `φ` vanishing for `u > R`, the point-pair operator on `ℂ^ι`-valued
fields over the modular cell `𝒟` is
`(L_φ F)(z) = ½ Σ_{B ∈ SL(2,ℤ)} ∫_𝒟 φ(u(z, Bz')) ρ(B) F(z') dμ(z')`.
When `F` is `ρ`-equivariant this is `∫_ℍ φ(u(z,w)) F(w) dμ(w)`.  Only the
finitely many near translates contribute (`tsum_ppTerm_eq_sum`); `L_φ F` is continuous
(`continuous_ppApply`); the arithmetic–geometric Cauchy–Schwarz and the tiling of `ℍ` by the
translates of `𝒟` give Schur's bound `∫_𝒟 ‖L_φ F‖² ≤ ‖φ‖₁² ∫_𝒟 ‖F‖²` (`lintegral_ppApply_sq_le`),
with `‖φ‖₁ = ∫_ℍ |φ(u(i,w))| dμ(w)`.  The result is a bounded operator `ppL2` on `L²(𝒟; ℂ^ι)`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] {ρ : SL(2, ℤ) →* (EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι)}

/-- The hyperbolic measure restricted to the modular cell. -/
abbrev cellMeasure : Measure ℍ := (volume : Measure ℍ).restrict fd

instance cellMeasure_finite : IsFiniteMeasure cellMeasure :=
  isFiniteMeasure_restrict.mpr volume_fd_ne_top

/-- `L²` of `ℂ^ι`-valued fields on the modular cell. -/
abbrev RepL2 (ι : Type) [Fintype ι] : Type := Lp (EuclideanSpace ℂ ι) 2 cellMeasure

/-- The `L²` class of a square-integrable field. -/
def toRepL2 (F : ℍ → EuclideanSpace ℂ ι) (hF : MemLp F 2 cellMeasure) : RepL2 ι := hF.toLp F

variable (ρ) in
/-- One translate of the point-pair kernel: `∫_𝒟 φ(u(z, Bz')) ρ(B) F(z') dμ(z')`. -/
def ppTerm (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (z : ℍ) (B : SL(2, ℤ)) : EuclideanSpace ℂ ι :=
  ∫ z' in fd, ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B (F z')

variable (ρ) in
/-- **The point-pair operator on twisted fields**:
`(L_φ F)(z) = ½ Σ_{B ∈ SL(2,ℤ)} ∫_𝒟 φ(u(z, Bz')) ρ(B) F(z') dμ(z')`, i.e. `∫_ℍ φ(u(z,w)) F(w) dμ(w)` for
the `ρ`-equivariant extension of `F`. -/
def ppApply (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (z : ℍ) : EuclideanSpace ℂ ι :=
  (1 / 2 : ℂ) • ∑' B : SL(2, ℤ), ppTerm ρ φ F z B

/-- A kernel supported in `u ≤ R`. -/
def KernelSupport (φ : ℝ → ℝ) (R : ℝ) : Prop := ∀ u, R < u → φ u = 0

theorem ppTerm_eq_zero {φ : ℝ → ℝ} {R : ℝ} (hφ : KernelSupport φ R) (F : ℍ → EuclideanSpace ℂ ι)
    (z : ℍ) {B : SL(2, ℤ)} (hB : B ∉ {B : SL(2, ℤ) | ∃ z' ∈ fd, pairU z (B • z') ≤ R}) :
    ppTerm ρ φ F z B = 0 := by
  unfold ppTerm
  refine setIntegral_eq_zero_of_forall_eq_zero fun z' hz' => ?_
  have : R < pairU z (B • z') := by
    by_contra h; push Not at h; exact hB ⟨z', hz', h⟩
  rw [hφ _ this]; simp

/-- The contributing translates form a finite set. -/
def ppNearSet (z : ℍ) (R : ℝ) : Finset (SL(2, ℤ)) := (finite_near_fd z R).toFinset

theorem tsum_ppTerm_eq_sum {φ : ℝ → ℝ} {R : ℝ} (hφ : KernelSupport φ R) (F : ℍ → EuclideanSpace ℂ ι)
    (z : ℍ) : ∑' B : SL(2, ℤ), ppTerm ρ φ F z B = ∑ B ∈ ppNearSet z R, ppTerm ρ φ F z B := by
  refine tsum_eq_sum fun B hB => ppTerm_eq_zero hφ F z ?_
  simpa [ppNearSet] using hB

/-- **Cauchy–Schwarz from the arithmetic–geometric inequality.**  If `2S ≤ tX + Y/t` for every
`t > 0`, then `S² ≤ XY`. -/
theorem sq_le_mul_of_forall_pos {S X Y : ℝ} (hS : 0 ≤ S) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : ∀ t : ℝ, 0 < t → 2 * S ≤ t * X + Y / t) : S ^ 2 ≤ X * Y := by
  rcases hS.lt_or_eq with hS0 | hS0
  · rcases hX.lt_or_eq with hX0 | hX0
    · have ht : 0 < S / X := div_pos hS0 hX0
      have h1 := h (S / X) ht
      rw [div_mul_cancel₀ _ hX0.ne', div_div_eq_mul_div] at h1
      have h2 : S ≤ Y * X / S := by linarith
      rw [le_div_iff₀ hS0] at h2
      nlinarith
    · -- `X = 0`: then `2S ≤ Y/t` for all `t`, forcing `S = 0`
      exfalso
      have h1 := h ((Y + 1) / S) (by positivity)
      rw [← hX0, mul_zero, zero_add, div_div_eq_mul_div] at h1
      have h2 : Y * S / (Y + 1) < S := by
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      linarith
  · rw [← hS0]; simp; exact mul_nonneg hX hY

/-- The pointwise arithmetic–geometric bound `a g ≤ (t a + a g²/t)/2` for `a ≥ 0`, `t > 0`. -/
theorem mul_le_half_of_pos {a g t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    2 * (a * g) ≤ t * a + a * g ^ 2 / t := by
  rw [← sub_nonneg]
  have : t * a + a * g ^ 2 / t - 2 * (a * g) = a * (g - t) ^ 2 / t := by
    field_simp; ring
  rw [this]; positivity

theorem continuous_pairU_right (z : ℍ) : Continuous (fun w : ℍ => pairU z w) := by
  unfold pairU
  have hc : Continuous (fun w : ℍ => (w : ℂ)) := UpperHalfPlane.continuous_coe
  have hi : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  refine ((continuous_const.dist hc).pow 2).div (continuous_const.mul hi) fun w => ?_
  have := z.im_pos; have := w.im_pos; positivity

theorem continuous_smul_int (B : SL(2, ℤ)) : Continuous (fun w : ℍ => B • w) :=
  (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ B)).congr fun _ => rfl

section Bounds

variable {φ : ℝ → ℝ} {M : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
include hφc hφM

theorem integrable_ppKernel_mul_norm {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) (z : ℍ)
    (B : SL(2, ℤ)) :
    Integrable (fun z' => |φ (pairU z (B • z'))| * ‖F z'‖) cellMeasure := by
  have hk : Continuous (fun z' : ℍ => |φ (pairU z (B • z'))|) :=
    (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B))).abs
  have hF1 : Integrable (fun z' => ‖F z'‖) cellMeasure := (hF.integrable one_le_two).norm
  refine hF1.bdd_mul (c := M) hk.aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
  rw [Real.norm_eq_abs, abs_abs]; exact hφM _

theorem integrable_ppKernel_mul_normSq {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) (z : ℍ)
    (B : SL(2, ℤ)) :
    Integrable (fun z' => |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2) cellMeasure := by
  have hk : Continuous (fun z' : ℍ => |φ (pairU z (B • z'))|) :=
    (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B))).abs
  have hF2 : Integrable (fun z' => ‖F z'‖ ^ 2) cellMeasure :=
    (memLp_two_iff_integrable_sq_norm hF.1).1 hF
  refine hF2.bdd_mul (c := M) hk.aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
  rw [Real.norm_eq_abs, abs_abs]; exact hφM _

theorem integrable_ppKernel (z : ℍ) (B : SL(2, ℤ)) :
    Integrable (fun z' => |φ (pairU z (B • z'))|) cellMeasure := by
  have hk : Continuous (fun z' : ℍ => |φ (pairU z (B • z'))|) :=
    (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B))).abs
  refine Integrable.of_bound (C := M) hk.aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
  rw [Real.norm_eq_abs, abs_abs]; exact hφM _

omit hφc hφM in
theorem norm_ppTerm_le (φ : ℝ → ℝ) (F : ℍ → EuclideanSpace ℂ ι) (z : ℍ) (B : SL(2, ℤ)) :
    ‖ppTerm ρ φ F z B‖ ≤ ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ := by
  unfold ppTerm
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]

/-- **Pointwise Schur bound.**  `‖(L_φ F)(z)‖² ≤ ¼ X(z) Y(z)` with `X = Σ_B ∫_𝒟 |φ(u(z,Bz'))|` and
`Y = Σ_B ∫_𝒟 |φ(u(z,Bz'))| ‖F(z')‖²`, the sums over the finite set of near translates. -/
theorem norm_ppApply_sq_le {R : ℝ} (hφR : KernelSupport φ R) {F : ℍ → EuclideanSpace ℂ ι}
    (hF : MemLp F 2 cellMeasure) (z : ℍ) :
    ‖ppApply ρ φ F z‖ ^ 2 ≤ 1 / 4 * ((∑ B ∈ ppNearSet z R, ∫ z' in fd, |φ (pairU z (B • z'))|) *
      (∑ B ∈ ppNearSet z R, ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2)) := by
  set S := ∑ B ∈ ppNearSet z R, ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ with hS
  set X := ∑ B ∈ ppNearSet z R, ∫ z' in fd, |φ (pairU z (B • z'))| with hX
  set Y := ∑ B ∈ ppNearSet z R, ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2 with hY
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun B _ =>
    integral_nonneg fun z' => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun B _ => integral_nonneg fun z' => abs_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun B _ =>
    integral_nonneg fun z' => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hL : ‖ppApply ρ φ F z‖ ≤ 1 / 2 * S := by
    unfold ppApply
    rw [tsum_ppTerm_eq_sum hφR, norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun B _ => norm_ppTerm_le φ F z B)) (by norm_num)
  have hCS : S ^ 2 ≤ X * Y := by
    refine sq_le_mul_of_forall_pos hS0 hX0 hY0 fun t ht => ?_
    have hterm : ∀ B ∈ ppNearSet z R, 2 * ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ≤
        t * (∫ z' in fd, |φ (pairU z (B • z'))|) +
          (∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2) / t := by
      intro B _
      have h1 := integrable_ppKernel_mul_norm hφc hφM hF z B
      have h2 := integrable_ppKernel hφc hφM z B
      have h3 := integrable_ppKernel_mul_normSq hφc hφM hF z B
      have hm := integral_mono (h1.const_mul 2) ((h2.const_mul t).add (h3.div_const t))
        (fun z' => mul_le_half_of_pos (g := ‖F z'‖) (abs_nonneg (φ (pairU z (B • z')))) ht)
      simp only [Pi.add_apply] at hm
      rw [integral_const_mul, integral_add (h2.const_mul t) (h3.div_const t), integral_const_mul,
        integral_div] at hm
      exact hm
    calc 2 * S = ∑ B ∈ ppNearSet z R, 2 * ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ := by
          rw [hS, Finset.mul_sum]
      _ ≤ ∑ B ∈ ppNearSet z R, (t * (∫ z' in fd, |φ (pairU z (B • z'))|) +
          (∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2) / t) := Finset.sum_le_sum hterm
      _ = t * X + Y / t := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
  have h1 : ‖ppApply ρ φ F z‖ ^ 2 ≤ (1 / 2 * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
  calc ‖ppApply ρ φ F z‖ ^ 2 ≤ (1 / 2 * S) ^ 2 := h1
    _ = 1 / 4 * S ^ 2 := by ring
    _ ≤ 1 / 4 * (X * Y) := by gcongr

end Bounds

/-- Moving the centre by hyperbolic distance at most `1` enlarges the support radius to
`2(1+2R)`. -/
theorem pairU_le_of_dist_le {z₀ z w : ℍ} (hz : dist z₀ z ≤ 1) {R : ℝ} (h : pairU z w ≤ R) :
    pairU z₀ w ≤ 2 * (1 + 2 * R) := by
  rw [pairU_eq_cosh] at h ⊢
  have hd := dist_triangle z₀ z w
  have hc : Real.cosh (dist z₀ w) ≤ Real.cosh (dist z₀ z + dist z w) :=
    Real.cosh_le_cosh.2 (by rw [abs_of_nonneg dist_nonneg, abs_of_nonneg (by positivity)]; exact hd)
  have hadd := Real.cosh_add (dist z₀ z) (dist z w)
  have h1 : Real.cosh (dist z₀ z) ≤ 2 := by
    have := Real.cosh_le_cosh.2 (show |dist z₀ z| ≤ |1| by
      rw [abs_of_nonneg dist_nonneg, abs_one]; exact hz)
    have h2 : Real.cosh 1 < 2 := by
      rw [Real.cosh_eq]
      have e1 := Real.exp_one_lt_d9
      have e2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.2 (by norm_num)
      linarith
    linarith
  have h2 : Real.sinh (dist z₀ z) * Real.sinh (dist z w) ≤
      Real.cosh (dist z₀ z) * Real.cosh (dist z w) := by
    have a := Real.sinh_lt_cosh (dist z₀ z)
    have b := Real.sinh_lt_cosh (dist z w)
    have a0 : 0 ≤ Real.sinh (dist z₀ z) := Real.sinh_nonneg_iff.2 dist_nonneg
    have b0 : 0 ≤ Real.sinh (dist z w) := Real.sinh_nonneg_iff.2 dist_nonneg
    exact mul_le_mul a.le b.le b0 (Real.cosh_pos _).le
  have hcw : Real.cosh (dist z w) ≤ 1 + 2 * R := by linarith
  have hc1 := Real.one_le_cosh (dist z₀ z)
  have hc2 := Real.one_le_cosh (dist z w)
  nlinarith [Real.cosh_pos (dist z₀ z)]

theorem continuous_pairU_left (w : ℍ) : Continuous (fun z : ℍ => pairU z w) := by
  simp_rw [pairU_comm _ w]; exact continuous_pairU_right w

theorem continuous_ppTerm {φ : ℝ → ℝ} {M : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) (B : SL(2, ℤ)) :
    Continuous (fun z => ppTerm ρ φ F z B) := by
  unfold ppTerm
  have hF1 : Integrable (fun z' => M * ‖F z'‖) cellMeasure :=
    ((hF.integrable one_le_two).norm).const_mul M
  refine continuous_of_dominated (bound := fun z' => M * ‖F z'‖) (fun z => ?_) (fun z => ?_) hF1
    (Eventually.of_forall fun z' => ?_)
  · have hk : Continuous (fun z' : ℍ => ((φ (pairU z (B • z')) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B)))
    exact hk.aestronglyMeasurable.smul ((ρ B).continuous.comp_aestronglyMeasurable hF.1)
  · refine Eventually.of_forall fun z' => ?_
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]
    exact mul_le_mul_of_nonneg_right (hφM _) (norm_nonneg _)
  · exact (Complex.continuous_ofReal.comp (hφc.comp (continuous_pairU_left (B • z')))).smul
      continuous_const

theorem continuous_ppApply {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    (hφR : KernelSupport φ R) {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) :
    Continuous (ppApply ρ φ F) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  have hloc : ∀ᶠ z in 𝓝 z₀, ppApply ρ φ F z =
      (1 / 2 : ℂ) • ∑ B ∈ ppNearSet z₀ (2 * (1 + 2 * R)), ppTerm ρ φ F z B := by
    filter_upwards [Metric.ball_mem_nhds z₀ one_pos] with z hz
    unfold ppApply
    congr 1
    refine tsum_eq_sum fun B hB => ppTerm_eq_zero hφR F z ?_
    rintro ⟨z', hz', h⟩
    apply hB
    simp only [ppNearSet, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨z', hz', pairU_le_of_dist_le (Metric.mem_ball'.1 hz).le h⟩
  refine ContinuousAt.congr ?_ (Filter.EventuallyEq.symm hloc)
  exact ((continuous_finsetSum _ fun B _ => continuous_ppTerm hφc hφM hF B).const_smul
    (1 / 2 : ℂ)).continuousAt

/-- The `L¹` mass of the kernel, `∫_ℍ |φ(u(i,w))| dμ(w)`. -/
def ppKernelMass (φ : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal |φ (pairU UpperHalfPlane.I w)|

theorem kernelMass_centre (φ : ℝ → ℝ) (z : ℍ) :
    ∫⁻ w, ENNReal.ofReal |φ (pairU z w)| = ppKernelMass φ :=
  lintegral_pairU_eq (fun u => ENNReal.ofReal |φ u|) z

theorem kernelMass_lt_top {φ : ℝ → ℝ} {M R : ℝ} (hR : 0 ≤ R) (hφM : ∀ u, |φ u| ≤ M)
    (hφR : KernelSupport φ R) : ppKernelMass φ < ∞ := by
  have hK : IsCompact {w : ℍ | pairU UpperHalfPlane.I w ≤ R} :=
    (isCompact_closedBall UpperHalfPlane.I (Real.arcosh (1 + 2 * R))).of_isClosed_subset
      (isClosed_le (continuous_pairU_right _) continuous_const) (by
        intro w hw
        simp only [Set.mem_setOf_eq] at hw
        rw [Metric.mem_closedBall, dist_comm]
        rw [pairU_eq_cosh] at hw
        have hc : Real.cosh (dist UpperHalfPlane.I w) ≤ 1 + 2 * R := by linarith
        have hd := dist_nonneg (x := UpperHalfPlane.I) (y := w)
        calc dist UpperHalfPlane.I w = Real.arcosh (Real.cosh (dist UpperHalfPlane.I w)) :=
              (Real.arcosh_cosh hd).symm
          _ ≤ Real.arcosh (1 + 2 * R) :=
              (Real.arcosh_le_arcosh (Real.cosh_pos _) (by linarith)).2 hc)
  have hb : ∀ w, ENNReal.ofReal |φ (pairU UpperHalfPlane.I w)| ≤
      {w : ℍ | pairU UpperHalfPlane.I w ≤ R}.indicator (fun _ => ENNReal.ofReal M) w := by
    intro w
    by_cases hw : pairU UpperHalfPlane.I w ≤ R
    · rw [Set.indicator_of_mem (show w ∈ {w : ℍ | pairU UpperHalfPlane.I w ≤ R} from hw)]
      exact ENNReal.ofReal_le_ofReal (hφM _)
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℍ | pairU UpperHalfPlane.I w ≤ R} from hw),
        hφR _ (lt_of_not_ge hw)]
      simp
  calc ppKernelMass φ ≤ ∫⁻ w, {w : ℍ | pairU UpperHalfPlane.I w ≤ R}.indicator
        (fun _ => ENNReal.ofReal M) w := lintegral_mono hb
    _ = ENNReal.ofReal M * volume {w : ℍ | pairU UpperHalfPlane.I w ≤ R} :=
        lintegral_indicator_const hK.measurableSet _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- **Kernel tiling.** `Σ_B ∫_𝒟 |φ(u(z,Bz'))| = 2 ∫_ℍ |φ(u(i,w))|`. -/
theorem tsum_kernel_fd (φ : ℝ → ℝ) (z : ℍ) :
    ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| = 2 * ppKernelMass φ := by
  rw [tsum_lintegral_fd_smul (fun w => ENNReal.ofReal |φ (pairU z w)|), kernelMass_centre]

theorem pairU_smul_int (B : SL(2, ℤ)) (z w : ℍ) : pairU (B • z) (B • w) = pairU z w :=
  pairU_smul (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) B) z w

theorem continuous_pairU : Continuous (fun p : ℍ × ℍ => pairU p.1 p.2) := by
  unfold pairU
  have hc : Continuous (fun w : ℍ => (w : ℂ)) := UpperHalfPlane.continuous_coe
  have hi : Continuous (fun w : ℍ => w.im) := UpperHalfPlane.continuous_im
  refine (((hc.comp continuous_fst).dist (hc.comp continuous_snd)).pow 2).div
    ((continuous_const.mul (hi.comp continuous_fst)).mul (hi.comp continuous_snd)) fun p => ?_
  have := p.1.im_pos; have := p.2.im_pos; positivity

/-- **The dual tiling.**  `Σ_B ∫_𝒟 |φ(u(z,Bz'))| dμ(z) = 2 ∫_ℍ |φ(u(i,w))|` for every `z'`. -/
theorem tsum_kernel_fd_left (φ : ℝ → ℝ) (z' : ℍ) :
    ∑' B : SL(2, ℤ), ∫⁻ z in fd, ENNReal.ofReal |φ (pairU z (B • z'))| = 2 * ppKernelMass φ := by
  have e : ∀ (B : SL(2, ℤ)) (z : ℍ), pairU z (B • z') = pairU z' (B⁻¹ • z) := by
    intro B z
    rw [pairU_comm, ← pairU_smul_int B⁻¹, inv_smul_smul]
  simp_rw [e]
  rw [← tsum_kernel_fd φ z']
  exact (Equiv.inv (SL(2, ℤ))).tsum_eq (fun B => ∫⁻ z in fd, ENNReal.ofReal |φ (pairU z' (B • z))|)

/-- **The Schur integral.**  For measurable `G ≥ 0`,
`∫_𝒟 Σ_B ∫_𝒟 |φ(u(z,Bz'))| G(z') dμ(z') dμ(z) = 2 ‖φ‖₁ ∫_𝒟 G`. -/
theorem lintegral_tsum_kernel_mul {φ : ℝ → ℝ} (hφc : Continuous φ) {G : ℍ → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ z in fd, ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| * G z' =
      2 * ppKernelMass φ * ∫⁻ z' in fd, G z' := by
  have hjoint : ∀ B : SL(2, ℤ), Measurable (fun p : ℍ × ℍ =>
      ENNReal.ofReal |φ (pairU p.1 (B • p.2))| * G p.2) := by
    intro B
    have hc : Continuous (fun p : ℍ × ℍ => ENNReal.ofReal |φ (pairU p.1 (B • p.2))|) :=
      ENNReal.continuous_ofReal.comp ((hφc.comp (continuous_pairU.comp
        (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd)))).abs)
    exact hc.measurable.mul (hG.comp measurable_snd)
  rw [lintegral_tsum fun B => ((hjoint B).lintegral_prod_right').aemeasurable]
  have hswap : ∀ B : SL(2, ℤ), ∫⁻ z in fd, ∫⁻ z' in fd,
      ENNReal.ofReal |φ (pairU z (B • z'))| * G z' =
      ∫⁻ z' in fd, (∫⁻ z in fd, ENNReal.ofReal |φ (pairU z (B • z'))|) * G z' := by
    intro B
    rw [lintegral_lintegral_swap ((hjoint B).aemeasurable)]
    refine lintegral_congr fun z' => ?_
    rw [lintegral_mul_const _ ?_]
    exact (ENNReal.continuous_ofReal.comp ((hφc.comp ((continuous_pairU_left _))).abs)).measurable
  refine (tsum_congr hswap).trans ?_
  have hmeas : ∀ B : SL(2, ℤ), AEMeasurable (fun z' => (∫⁻ z in fd,
      ENNReal.ofReal |φ (pairU z (B • z'))|) * G z') (volume.restrict fd) := by
    intro B
    have hc : Continuous (fun p : ℍ × ℍ => ENNReal.ofReal |φ (pairU p.1 (B • p.2))|) :=
      ENNReal.continuous_ofReal.comp ((hφc.comp (continuous_pairU.comp
        (continuous_fst.prodMk ((continuous_smul_int B).comp continuous_snd)))).abs)
    exact ((hc.measurable.lintegral_prod_left').mul hG).aemeasurable
  rw [← lintegral_tsum hmeas]
  simp_rw [ENNReal.tsum_mul_right, tsum_kernel_fd_left]
  exact lintegral_const_mul _ hG

/-- The finite sum of kernel integrals is at most `2‖φ‖₁`. -/
theorem ofReal_sum_kernel_le {φ : ℝ → ℝ} {M : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    (z : ℍ) (S : Finset (SL(2, ℤ))) :
    ENNReal.ofReal (∑ B ∈ S, ∫ z' in fd, |φ (pairU z (B • z'))|) ≤ 2 * ppKernelMass φ := by
  rw [ENNReal.ofReal_sum_of_nonneg fun B _ => integral_nonneg fun z' => abs_nonneg _]
  rw [← tsum_kernel_fd φ z]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun B _ => ?_)) (ENNReal.sum_le_tsum S)
  exact ofReal_integral_eq_lintegral_ofReal (integrable_ppKernel hφc hφM z B)
    (Eventually.of_forall fun z' => abs_nonneg _)

theorem ofReal_sum_kernel_mul_le {φ : ℝ → ℝ} {M : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M)
    {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) (z : ℍ) (S : Finset (SL(2, ℤ))) :
    ENNReal.ofReal (∑ B ∈ S, ∫ z' in fd, |φ (pairU z (B • z'))| * ‖F z'‖ ^ 2) ≤
      ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖F z'‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun B _ =>
    integral_nonneg fun z' => mul_nonneg (abs_nonneg _) (sq_nonneg _)]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun B _ => ?_)) (ENNReal.sum_le_tsum S)
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_ppKernel_mul_normSq hφc hφM hF z B)
    (Eventually.of_forall fun z' => mul_nonneg (abs_nonneg _) (sq_nonneg _))]
  refine lintegral_congr fun z' => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]

/-- **The `L²` bound of the point-pair operator**: `∫_𝒟 ‖L_φ F‖² ≤ ‖φ‖₁² ∫_𝒟 ‖F‖²`. -/
theorem lintegral_ppApply_sq_le {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ)
    (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R) (hφR : KernelSupport φ R) {F : ℍ → EuclideanSpace ℂ ι}
    (hFm : StronglyMeasurable F) (hF : MemLp F 2 cellMeasure) :
    ∫⁻ z in fd, ENNReal.ofReal (‖ppApply ρ φ F z‖ ^ 2) ≤
      ppKernelMass φ ^ 2 * ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2) := by
  have hm := kernelMass_lt_top hR hφM hφR
  have hpt : ∀ z, ENNReal.ofReal (‖ppApply ρ φ F z‖ ^ 2) ≤ ENNReal.ofReal (1 / 4) * (2 * ppKernelMass φ) *
      ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
        ENNReal.ofReal (‖F z'‖ ^ 2) := by
    intro z
    refine (ENNReal.ofReal_le_ofReal (norm_ppApply_sq_le hφc hφM hφR hF z)).trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (Finset.sum_nonneg fun B _ =>
      integral_nonneg fun z' => abs_nonneg _), mul_assoc (ENNReal.ofReal (1 / 4))]
    exact mul_le_mul_right (mul_le_mul' (ofReal_sum_kernel_le hφc hφM z _)
      (ofReal_sum_kernel_mul_le hφc hφM hF z _)) _
  have hG : Measurable (fun z' : ℍ => ENNReal.ofReal (‖F z'‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hFm.measurable.norm).pow_const 2)
  calc ∫⁻ z in fd, ENNReal.ofReal (‖ppApply ρ φ F z‖ ^ 2)
      ≤ ∫⁻ z in fd, ENNReal.ofReal (1 / 4) * (2 * ppKernelMass φ) *
        ∑' B : SL(2, ℤ), ∫⁻ z' in fd, ENNReal.ofReal |φ (pairU z (B • z'))| *
          ENNReal.ofReal (‖F z'‖ ^ 2) := lintegral_mono hpt
    _ = ENNReal.ofReal (1 / 4) * (2 * ppKernelMass φ) * (2 * ppKernelMass φ *
          ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hm.ne)), lintegral_tsum_kernel_mul hφc hG]
    _ = ppKernelMass φ ^ 2 * ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2) := by
        have h4 : ENNReal.ofReal (1 / 4) * 2 * 2 = 1 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
          rw [show (4 : ℝ) = (4 : ℝ≥0∞).toReal by norm_num, ENNReal.ofReal_toReal (by norm_num)]
          rw [mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num, ENNReal.div_mul_cancel (by norm_num)
            (by norm_num)]
        calc ENNReal.ofReal (1 / 4) * (2 * ppKernelMass φ) * (2 * ppKernelMass φ *
              ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2))
            = (ENNReal.ofReal (1 / 4) * 2 * 2) * (ppKernelMass φ ^ 2 *
              ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2)) := by ring
          _ = ppKernelMass φ ^ 2 * ∫⁻ z' in fd, ENNReal.ofReal (‖F z'‖ ^ 2) := by rw [h4, one_mul]

theorem eLpNorm_two_sq_ofReal {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem eLpNorm_le_of_sq_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f g : α → E} {c : ℝ≥0∞}
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ c ^ 2 * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ) :
    eLpNorm f 2 μ ≤ c * eLpNorm g 2 μ := by
  rw [← eLpNorm_two_sq_ofReal, ← eLpNorm_two_sq_ofReal, ← mul_pow] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

theorem ppApply_congr_ae (φ : ℝ → ℝ) {F G : ℍ → EuclideanSpace ℂ ι} (h : F =ᵐ[cellMeasure] G) :
    ppApply ρ φ F = ppApply ρ φ G := by
  funext z
  unfold ppApply ppTerm
  congr 1
  refine tsum_congr fun B => integral_congr_ae ?_
  filter_upwards [h] with z' hz'
  rw [hz']

section Operator

variable {φ : ℝ → ℝ} {M R : ℝ} (hφc : Continuous φ) (hφM : ∀ u, |φ u| ≤ M) (hR : 0 ≤ R)
  (hφR : KernelSupport φ R)
include hφc hφM hR hφR

theorem eLpNorm_ppApply_le {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) :
    eLpNorm (ppApply ρ φ F) 2 cellMeasure ≤ ppKernelMass φ * eLpNorm F 2 cellMeasure := by
  obtain ⟨F', hF'm, hFF'⟩ : ∃ F' : ℍ → EuclideanSpace ℂ ι, StronglyMeasurable F' ∧
      F =ᵐ[cellMeasure] F' := ⟨hF.1.mk F, hF.1.stronglyMeasurable_mk, hF.1.ae_eq_mk⟩
  rw [ppApply_congr_ae φ hFF', eLpNorm_congr_ae hFF']
  exact eLpNorm_le_of_sq_le (lintegral_ppApply_sq_le hφc hφM hR hφR hF'm (hF.ae_eq hFF'))

theorem memLp_ppApply {F : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure) :
    MemLp (ppApply ρ φ F) 2 cellMeasure := by
  refine ⟨(continuous_ppApply hφc hφM hφR hF).aestronglyMeasurable, ?_⟩
  refine lt_of_le_of_lt (eLpNorm_ppApply_le hφc hφM hR hφR hF) ?_
  exact ENNReal.mul_lt_top (kernelMass_lt_top hR hφM hφR) hF.2

omit hR in
theorem ppApply_add {F G : ℍ → EuclideanSpace ℂ ι} (hF : MemLp F 2 cellMeasure)
    (hG : MemLp G 2 cellMeasure) : ppApply ρ φ (F + G) = ppApply ρ φ F + ppApply ρ φ G := by
  funext z
  simp only [ppApply, Pi.add_apply]
  rw [tsum_ppTerm_eq_sum hφR, tsum_ppTerm_eq_sum hφR, tsum_ppTerm_eq_sum hφR, ← smul_add,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold ppTerm
  have hk : Continuous (fun z' : ℍ => ((φ (pairU z (B • z')) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp (continuous_smul_int B)))
  have hint : ∀ {H : ℍ → EuclideanSpace ℂ ι}, MemLp H 2 cellMeasure → Integrable
      (fun z' => ((φ (pairU z (B • z')) : ℝ) : ℂ) • ρ B (H z')) cellMeasure := by
    intro H hH
    have hH1 : Integrable (fun z' => ρ B (H z')) cellMeasure :=
      (ρ B).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
        (hH.integrable one_le_two)
    refine hH1.bdd_smul M hk.aestronglyMeasurable (Eventually.of_forall fun z' => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hφM _
  rw [← integral_add (hint hF) (hint hG)]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only [Pi.add_apply, map_add, smul_add]

omit hR hφc hφM hφR in
theorem ppApply_smul (c : ℂ) (F : ℍ → EuclideanSpace ℂ ι) : ppApply ρ φ (c • F) = c • ppApply ρ φ F := by
  funext z
  simp only [ppApply, ppTerm, Pi.smul_apply, map_smul]
  rw [smul_comm]
  congr 1
  rw [← tsum_const_smul'' c]
  refine tsum_congr fun B => ?_
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun z' => ?_)
  simp only
  rw [smul_comm]

variable (ρ) in
/-- The point-pair operator on `L²(𝒟; ℂ^ι)`, as a linear map. -/
def ppLinear : RepL2 ι →ₗ[ℂ] RepL2 ι where
  toFun F := toRepL2 (ppApply ρ φ F) (memLp_ppApply hφc hφM hR hφR (Lp.memLp F))
  map_add' F G := by
    have e : ppApply ρ φ ⇑(F + G) = ppApply ρ φ ⇑F + ppApply ρ φ ⇑G := by
      rw [ppApply_congr_ae φ (Lp.coeFn_add F G),
        ppApply_add hφc hφM hφR (Lp.memLp F) (Lp.memLp G)]
    simp only [toRepL2]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq e)
  map_smul' c F := by
    have e : ppApply ρ φ ⇑(c • F) = c • ppApply ρ φ ⇑F := by
      rw [ppApply_congr_ae φ (Lp.coeFn_smul c F), ppApply_smul]
    simp only [toRepL2, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq e)

theorem ppLinear_apply (F : RepL2 ι) :
    ppLinear ρ hφc hφM hR hφR F =
      toRepL2 (ppApply ρ φ F) (memLp_ppApply hφc hφM hR hφR (Lp.memLp F)) := rfl

theorem norm_ppLinear_le (F : RepL2 ι) :
    ‖ppLinear ρ hφc hφM hR hφR F‖ ≤ (ppKernelMass φ).toReal * ‖F‖ := by
  rw [ppLinear_apply, toRepL2, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (kernelMass_lt_top hR hφM hφR).ne
    (Lp.eLpNorm_ne_top F)) (eLpNorm_ppApply_le hφc hφM hR hφR (Lp.memLp F))

variable (ρ) in
/-- **The point-pair operator on `L²(𝒟; ℂ^ι)`**, bounded by `‖φ‖₁`. -/
def ppL2 : RepL2 ι →L[ℂ] RepL2 ι :=
  LinearMap.mkContinuous (ppLinear ρ hφc hφM hR hφR) (ppKernelMass φ).toReal
    (norm_ppLinear_le hφc hφM hR hφR)

theorem ppL2_apply (F : RepL2 ι) :
    ppL2 ρ hφc hφM hR hφR F =
      toRepL2 (ppApply ρ φ F) (memLp_ppApply hφc hφM hR hφR (Lp.memLp F)) := rfl

theorem ppL2_coeFn (F : RepL2 ι) :
    (ppL2 ρ hφc hφM hR hφR F : ℍ → EuclideanSpace ℂ ι) =ᵐ[cellMeasure] ppApply ρ φ F :=
  MemLp.coeFn_toLp (memLp_ppApply hφc hφM hR hφR (Lp.memLp F))

end Operator

end

end GaloisForLFunctions.RHTower.RepPointPair
