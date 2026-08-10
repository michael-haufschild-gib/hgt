import GaloisForLFunctions.RHTower.XiMassAdaptiveApertureFaithfulnessWall
import GaloisForLFunctions.RHTower.SoninDoublyContractedPacket

/-!
# Cubic-clock vertical Hilbert energy of the Xi mass carrier

The scalar mass trace can hide a fixed off-line orbit behind the growing spectral tail.  Moving the
norm inside the trace removes that cancellation without truncating the divisor.  At aperture
`aₙ = n + 1` and vertical clock `uₙ = aₙ³`, the complete squared-term sum tends to zero under RH and
to infinity off RH.  Thus its convergence to zero is an unconditional, premise-free RH criterion.
-/

open Complex Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Integer aperture, shifted away from zero. -/
def xiMassCubicAperture (n : ℕ) : ℝ := (n : ℝ) + 1

theorem xiMassCubicAperture_half_le (n : ℕ) :
    1 / 2 ≤ xiMassCubicAperture n := by
  rw [xiMassCubicAperture]
  positivity

theorem xiMassCubicAperture_pos (n : ℕ) : 0 < xiMassCubicAperture n :=
  lt_of_lt_of_le (by norm_num) (xiMassCubicAperture_half_le n)

theorem tendsto_xiMassCubicAperture_atTop :
    Tendsto xiMassCubicAperture atTop atTop := by
  simpa only [xiMassCubicAperture] using
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop)

/-- Cubic vertical clock. -/
def xiMassCubicTime (n : ℕ) : ℝ := xiMassCubicAperture n ^ 3

theorem xiMassCubicTime_nonneg (n : ℕ) : 0 ≤ xiMassCubicTime n := by
  rw [xiMassCubicTime]
  positivity

/-- One reflection-diagonal squared half-wave term. -/
def xiMassCubicVerticalHilbertTerm (n : ℕ) (q : XiZeroCopy) : ℝ :=
  let F := xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)
  Real.exp (-2 * ((F.pt q).re - xiMassCubicTime n * (F.pt q).im))

/-- Complete multiplicity-exact vertical Hilbert energy. -/
def xiMassCubicVerticalHilbertEnergy (n : ℕ) : ℝ :=
  ∑' q : XiZeroCopy, xiMassCubicVerticalHilbertTerm n q

theorem xiMassCubicVerticalHilbertTerm_eq_norm_sq (n : ℕ) (q : XiZeroCopy) :
    xiMassCubicVerticalHilbertTerm n q =
      ‖(xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)).term
          ((1 : ℂ) + xiMassCubicTime n * I) q‖ ^ 2 := by
  let F := xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)
  rw [xiMassCubicVerticalHilbertTerm, F.norm_term, ← Real.exp_nat_mul]
  simp only [add_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, add_zero,
    one_mul, add_im, one_im, zero_add]
  congr 1
  ring

theorem xiMassCubicVerticalHilbertTerm_nonneg (n : ℕ) (q : XiZeroCopy) :
    0 ≤ xiMassCubicVerticalHilbertTerm n q :=
  (Real.exp_pos _).le

theorem summable_xiMassCubicVerticalHilbertTerm (n : ℕ) :
    Summable (xiMassCubicVerticalHilbertTerm n) := by
  let F := xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)
  let u := xiMassCubicTime n
  have hu : 0 ≤ u := xiMassCubicTime_nonneg n
  have hbound : ∀ q : XiZeroCopy,
      xiMassCubicVerticalHilbertTerm n q ≤ Real.exp u * F.weight 2 q := by
    intro q
    rw [xiMassCubicVerticalHilbertTerm, F.weight, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hK : (F.pt q).im ≤ 1 / 2 :=
      (le_abs_self _).trans (F.abs_im_lt q).le
    dsimp only [u]
    nlinarith
  exact Summable.of_nonneg_of_le
    (fun q => xiMassCubicVerticalHilbertTerm_nonneg n q) hbound
    ((F.summable_weight (by norm_num : (0 : ℝ) < 2)).mul_left (Real.exp u))

theorem xiMassCubicVerticalHilbertEnergy_nonneg (n : ℕ) :
    0 ≤ xiMassCubicVerticalHilbertEnergy n := by
  rw [xiMassCubicVerticalHilbertEnergy]
  exact tsum_nonneg fun q => xiMassCubicVerticalHilbertTerm_nonneg n q

theorem xiMassCubicVerticalHilbertTerm_le_energy (n : ℕ) (q : XiZeroCopy) :
    xiMassCubicVerticalHilbertTerm n q ≤ xiMassCubicVerticalHilbertEnergy n := by
  rw [xiMassCubicVerticalHilbertEnergy]
  exact (summable_xiMassCubicVerticalHilbertTerm n).le_tsum q
    (fun r _ => xiMassCubicVerticalHilbertTerm_nonneg n r)

/-- Under RH the complete energy has an exponentially decaying aperture majorant. -/
theorem xiMassCubicVerticalHilbertEnergy_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n : ℕ) :
    xiMassCubicVerticalHilbertEnergy n ≤
      Real.exp (-xiMassCubicAperture n) * xiPoissonAbstract.traceReal 1 := by
  let a := xiMassCubicAperture n
  let ha := xiMassCubicAperture_half_le n
  let F := xiPoissonAbstract.mass ha
  have hterm : ∀ q : XiZeroCopy,
      xiMassCubicVerticalHilbertTerm n q ≤
        Real.exp (-a) * xiPoissonAbstract.weight 1 q := by
    intro q
    have hK : (F.pt q).im = 0 :=
      (xiPoissonAbstract.mass_im_eq_zero_iff ha q).mpr
        (xiPoissonPoint_im_eq_zero_of_riemannHypothesis hRH q)
    have haM : a ≤ (F.pt q).re := F.base_le q
    have hRM : (xiPoissonPoint q).re ≤ (F.pt q).re := by
      simpa only [F, xiPoissonAbstract_pt] using
        (xiPoissonAbstract.re_lt_csqrtRe_massArg ha q).le
    rw [xiMassCubicVerticalHilbertTerm, hK, mul_zero, sub_zero,
      xiPoissonAbstract.weight, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp only [a]
    nlinarith
  rw [xiMassCubicVerticalHilbertEnergy]
  calc
    (∑' q : XiZeroCopy, xiMassCubicVerticalHilbertTerm n q)
        ≤ ∑' q : XiZeroCopy,
            Real.exp (-a) * xiPoissonAbstract.weight 1 q :=
      Summable.tsum_le_tsum hterm (summable_xiMassCubicVerticalHilbertTerm n)
        ((xiPoissonAbstract.summable_weight (by norm_num : (0 : ℝ) < 1)).mul_left _)
    _ = Real.exp (-a) * xiPoissonAbstract.traceReal 1 := by
      rw [xiPoissonAbstract.traceReal, tsum_mul_left]
    _ = Real.exp (-xiMassCubicAperture n) * xiPoissonAbstract.traceReal 1 := rfl

/-- RH makes the complete cubic-clock vertical Hilbert energy vanish. -/
theorem tendsto_xiMassCubicVerticalHilbertEnergy_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    Tendsto xiMassCubicVerticalHilbertEnergy atTop (nhds 0) := by
  refine squeeze_zero xiMassCubicVerticalHilbertEnergy_nonneg
    (xiMassCubicVerticalHilbertEnergy_le_of_riemannHypothesis hRH) ?_
  exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    tendsto_xiMassCubicAperture_atTop).mul_const (xiPoissonAbstract.traceReal 1)

/-- Failure of RH supplies a divisor copy in the positive displacement half of its reflection
orbit. -/
theorem exists_xiPoissonPoint_im_pos_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, 0 < (xiPoissonPoint q).im := by
  have hex : ∃ q : XiZeroCopy, (xiPoissonPoint q).im ≠ 0 := by
    by_contra hnone
    have hall : ∀ q : XiZeroCopy, (xiPoissonPoint q).im = 0 := by
      intro q
      by_contra hq
      exact hnone ⟨q, hq⟩
    exact hRH (riemannHypothesis_of_xiSpectralPoint_real
      (xiSpectralPoint_real_of_xiPoissonPoint_im_eq_zero hall))
  rcases hex with ⟨q, hq⟩
  by_cases hpos : 0 < (xiPoissonPoint q).im
  · exact ⟨q, hpos⟩
  · refine ⟨xiZeroCopyLineConjEquiv q, ?_⟩
    rw [xiPoissonPoint_lineConj, Complex.conj_im]
    linarith

/-- One fixed off-line copy has exponentially divergent cubic-clock squared response. -/
theorem tendsto_xiMassCubicVerticalHilbertTerm_atTop_of_im_pos
    (q : XiZeroCopy) (hJ : 0 < (xiPoissonPoint q).im) :
    Tendsto (fun n => xiMassCubicVerticalHilbertTerm n q) atTop atTop := by
  let R := (xiPoissonPoint q).re
  let J := (xiPoissonPoint q).im
  let c := R * J
  have hR : 0 < R := by dsimp only [R]; linarith [three_lt_xiPoissonPoint_re q]
  have hc : 0 < c := mul_pos hR hJ
  have hminor : ∀ᶠ n : ℕ in atTop,
      c * xiMassCubicAperture n ^ 2 - 2 * xiMassCubicAperture n - 2 * R ≤
        -2 * (((xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)).pt q).re -
          xiMassCubicTime n *
            ((xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)).pt q).im) := by
    filter_upwards [tendsto_xiMassCubicAperture_atTop.eventually_ge_atTop R] with n haR
    let a := xiMassCubicAperture n
    let ha := xiMassCubicAperture_half_le n
    let F := xiPoissonAbstract.mass ha
    let M := (F.pt q).re
    let K := (F.pt q).im
    have ha0 : 0 < a := xiMassCubicAperture_pos n
    have hM0 : 0 < M := F.re_pos q
    have hK0 : 0 < K := by
      have hprod := xiPoissonAbstract.re_mul_im_mass ha q
      have : 0 < M * K := by
        simpa only [M, K, R, J, F, xiPoissonAbstract_pt] using hc
      nlinarith
    have hMup : M ≤ R + a := by
      simpa only [M, F, R, a, xiPoissonAbstract_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.csqrtRe_massArg_le_add ha q
    have hMtwo : M ≤ 2 * a := by
      linarith
    have hcharge : M * K = c := by
      simpa only [M, K, R, J, c, F, xiPoissonAbstract_pt] using
        xiPoissonAbstract.re_mul_im_mass ha q
    have hboost : c * a ^ 2 ≤ 2 * a ^ 3 * K := by
      have hmul := mul_le_mul_of_nonneg_right hMtwo hK0.le
      rw [hcharge] at hmul
      nlinarith [sq_nonneg a]
    rw [xiMassCubicTime]
    dsimp only [M, K, F, a] at hMup hboost ⊢
    nlinarith
  have hquad : Tendsto
      (fun n : ℕ => c * xiMassCubicAperture n ^ 2 -
        2 * xiMassCubicAperture n - 2 * R) atTop atTop := by
    have hgap := tendsto_sq_gap_atTop tendsto_xiMassCubicAperture_atTop
      (q := (2 : ℝ)) (t := c) (by norm_num) hc
    have hshift := tendsto_atTop_add_const_right atTop (-2 * R) hgap
    convert hshift using 1
    ext n
    rw [abs_of_nonneg]
    · ring
    · positivity
  have hexponent : Tendsto
      (fun n : ℕ => -2 *
        (((xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)).pt q).re -
          xiMassCubicTime n *
            ((xiPoissonAbstract.mass (xiMassCubicAperture_half_le n)).pt q).im))
      atTop atTop :=
    tendsto_atTop_mono' atTop hminor hquad
  exact (Real.tendsto_exp_atTop.comp hexponent).congr'
    (Eventually.of_forall fun n => by rw [xiMassCubicVerticalHilbertTerm])

/-- Off RH the complete positive energy diverges; no tail estimate or interchange is needed. -/
theorem tendsto_xiMassCubicVerticalHilbertEnergy_atTop_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    Tendsto xiMassCubicVerticalHilbertEnergy atTop atTop := by
  rcases exists_xiPoissonPoint_im_pos_of_not_riemannHypothesis hRH with ⟨q, hq⟩
  exact tendsto_atTop_mono' atTop
    (Eventually.of_forall fun n => xiMassCubicVerticalHilbertTerm_le_energy n q)
    (tendsto_xiMassCubicVerticalHilbertTerm_atTop_of_im_pos q hq)

/-- **Complete cubic-clock dichotomy.**  This closed theorem has no analytic premise: RH is exactly
vanishing of the complete reflection-diagonal vertical Hilbert energy. -/
theorem riemannHypothesis_iff_tendsto_xiMassCubicVerticalHilbertEnergy_zero :
    RiemannHypothesis ↔
      Tendsto xiMassCubicVerticalHilbertEnergy atTop (nhds 0) := by
  constructor
  · exact tendsto_xiMassCubicVerticalHilbertEnergy_zero_of_riemannHypothesis
  · intro hzero
    by_contra hRH
    have htop := tendsto_xiMassCubicVerticalHilbertEnergy_atTop_of_not_riemannHypothesis hRH
    have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ xiMassCubicVerticalHilbertEnergy n :=
      htop (eventually_ge_atTop 1)
    have hsmall : ∀ᶠ n : ℕ in atTop, xiMassCubicVerticalHilbertEnergy n < 1 :=
      (tendsto_order.1 hzero).2 1 (by norm_num)
    have hfalse : ∀ᶠ _ : ℕ in atTop, False := by
      filter_upwards [hlarge, hsmall] with n hnlarge hnsmall
      linarith
    exact (Filter.Eventually.exists hfalse).elim fun _ h => h

end

end RHTower
