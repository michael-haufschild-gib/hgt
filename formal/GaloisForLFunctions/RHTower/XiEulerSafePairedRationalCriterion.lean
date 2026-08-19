import GaloisForLFunctions.RHTower.XiEulerSafePairedClosure

/-!
# The countable absolute-Euler paired criterion

The Cauchy transform of a divisor vector is holomorphic away from the divisor, so vanishing of its
real part on a dense subset of a divisor-free ball already forces it to vanish on that ball.  Only
Gaussian-rational poles of one open absolute-Euler quadrant are therefore needed in the
completeness argument, and the resulting countable passivity assertion is again exactly the
Riemann hypothesis.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

local notation "XiLp" => lp (fun _ : XiZeroCopy => ℂ) 2

/-! ## Gaussian rationals -/

/-- The Gaussian-rational points of the plane. -/
def gaussianRationalSet : Set ℂ := {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * Complex.I}

theorem mul_I_mem_gaussianRationalSet {z : ℂ} (hz : z ∈ gaussianRationalSet) :
    Complex.I * z ∈ gaussianRationalSet := by
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨-b, a, ?_⟩
  push_cast
  linear_combination ((b : ℂ)) * Complex.I_sq

theorem dense_gaussianRationalSet : Dense gaussianRationalSet := by
  rw [Metric.dense_iff]
  intro z ε hε
  obtain ⟨a, ha⟩ := exists_rat_near z.re (by positivity : (0 : ℝ) < ε / 4)
  obtain ⟨b, hb⟩ := exists_rat_near z.im (by positivity : (0 : ℝ) < ε / 4)
  refine ⟨(a : ℂ) + (b : ℂ) * Complex.I, ?_, ⟨a, b, rfl⟩⟩
  rw [Metric.mem_ball, Complex.dist_eq]
  have hre : ((a : ℂ) + (b : ℂ) * Complex.I - z).re = (a : ℝ) - z.re := by
    simp
  have him : ((a : ℂ) + (b : ℂ) * Complex.I - z).im = (b : ℝ) - z.im := by
    simp
  have hbound := Complex.norm_le_abs_re_add_abs_im ((a : ℂ) + (b : ℂ) * Complex.I - z)
  rw [hre, him] at hbound
  have h1 : |(a : ℝ) - z.re| < ε / 4 := by rw [abs_sub_comm]; exact ha
  have h2 : |(b : ℝ) - z.im| < ε / 4 := by rw [abs_sub_comm]; exact hb
  linarith

/-! ## Rational completeness -/

/-- **Countable completeness.**  Only Gaussian-rational poles are needed. -/
theorem eq_zero_of_re_inner_eulerPaired_rational_eq_zero
    {v : XiLp} (hv : xiWeilSchwarzLp v = v) (hfib : XiFiberConstant v)
    (h : ∀ w : ℂ, w ∈ gaussianRationalSet → ∀ (hw1 : 1 / 2 < w.re), 0 < w.im →
      (inner ℂ v (xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw1)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw1))).re = 0) :
    v = 0 := by
  set z₀ : ℂ := 1 - Complex.I with hz₀
  have hquad : ∀ z ∈ ball z₀ (1 / 4 : ℝ),
      1 / 2 < (Complex.I * z).re ∧ 0 < (Complex.I * z).im := by
    intro z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have him : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
    have hre' : |z.re - 1| < 1 / 4 := by
      have : (z - z₀).re = z.re - 1 := by rw [hz₀]; simp
      rw [this] at hre; linarith
    have him' : |z.im + 1| < 1 / 4 := by
      have : (z - z₀).im = z.im + 1 := by rw [hz₀]; simp
      rw [this] at him; linarith
    rw [abs_lt] at hre' him'
    constructor
    · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      linarith [him'.2]
    · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul]
      linarith [hre'.1]
  have hcentered : ∀ z ∈ ball z₀ (1 / 4 : ℝ), xiEulerCentered (Complex.I * z) = z := by
    intro z _
    rw [xiEulerCentered]
    linear_combination (-z) * Complex.I_sq
  have hballfree : ball z₀ (1 / 4 : ℝ) ⊆ {z : ℂ | XiC z ≠ 0} := by
    intro z hz
    obtain ⟨hq1, _⟩ := hquad z hz
    have := XiC_xiEulerCentered_ne_zero hq1
    rwa [hcentered z hz] at this
  have hcontAt : ∀ z ∈ ball z₀ (1 / 4 : ℝ),
      ContinuousAt (fun y : ℂ => (xiCauchyTransform v y).re) z := by
    intro z hz
    have hdiff : DifferentiableAt ℂ (xiCauchyTransform v) z :=
      (differentiableOn_xiCauchyTransform v).differentiableAt
        (isOpen_xiRegularSet.mem_nhds (hballfree hz))
    exact Complex.continuous_re.continuousAt.comp hdiff.continuousAt
  have hreD : ∀ z ∈ ball z₀ (1 / 4 : ℝ) ∩ gaussianRationalSet,
      (xiCauchyTransform v z).re = 0 := by
    rintro z ⟨hz, hzq⟩
    obtain ⟨hq1, hq2⟩ := hquad z hz
    have hval := h (Complex.I * z) (mul_I_mem_gaussianRationalSet hzq) hq1 hq2
    rw [re_inner_eulerPaired hv] at hval
    rw [hcentered z hz] at hval
    linarith
  have hre : ∀ z ∈ ball z₀ (1 / 4 : ℝ), (xiCauchyTransform v z).re = 0 := by
    intro z hz
    have hmem : z ∈ closure (ball z₀ (1 / 4 : ℝ) ∩ gaussianRationalSet) :=
      dense_gaussianRationalSet.open_subset_closure_inter isOpen_ball hz
    obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.mp hmem
    have hlim := (hcontAt z hz).tendsto.comp hxlim
    have hconst : ((fun y : ℂ => (xiCauchyTransform v y).re) ∘ x) = fun _ => (0 : ℝ) := by
      funext k
      exact hreD (x k) (hx k)
    rw [hconst] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  refine eq_zero_of_fiberConstant_of_fiberSum_eq_zero hfib (fun ρ => ?_)
  exact xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball v
    (by norm_num) hballfree hre ρ

/-! ## The countable criterion -/

/-- The Gaussian-rational absolute-Euler paired generators. -/
def xiEulerPairedRationalSet : Set XiLp :=
  {v : XiLp | ∃ (w : ℂ) (h : 1 / 2 < w.re), 0 < w.im ∧ w ∈ gaussianRationalSet ∧
    v = xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero h)
      (XiC_neg_conj_xiEulerCentered_ne_zero h)}

theorem xiEulerPairedRationalSet_subset_sector :
    xiEulerPairedRationalSet ⊆ (xiSchwarzFiberSector : Set XiLp) := by
  rintro v ⟨w, h, _, _, rfl⟩
  exact xiEulerPairedSet_subset_sector ⟨w, h, by assumption, rfl⟩

/-- The closed real span of the Gaussian-rational absolute-Euler paired vectors. -/
def xiEulerPairedRationalClosure : Submodule ℝ XiLp :=
  (Submodule.span ℝ xiEulerPairedRationalSet).topologicalClosure

theorem xiEulerPairedRationalClosure_le_sector :
    xiEulerPairedRationalClosure ≤ xiSchwarzFiberSector :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr xiEulerPairedRationalSet_subset_sector) isClosed_xiSchwarzFiberSector

theorem mem_xiEulerPairedRationalClosure_of_mem_sector {v : XiLp}
    (hv : v ∈ xiSchwarzFiberSector) : v ∈ xiEulerPairedRationalClosure := by
  haveI hcl : IsClosed ((xiEulerPairedRationalClosure : Submodule ℝ XiLp) : Set XiLp) :=
    Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace ((xiEulerPairedRationalClosure : Submodule ℝ XiLp)) := hcl.completeSpace_coe
  set K : Submodule ℝ XiLp := xiEulerPairedRationalClosure with hK
  have hpm : K.starProjection v ∈ K := K.starProjection_apply_mem v
  have horth : v - K.starProjection v ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have husec : v - K.starProjection v ∈ xiSchwarzFiberSector :=
    Submodule.sub_mem _ hv (xiEulerPairedRationalClosure_le_sector hpm)
  obtain ⟨hs, hf⟩ := (mem_xiSchwarzFiberSector_iff _).mp husec
  have huzero : v - K.starProjection v = 0 := by
    refine eq_zero_of_re_inner_eulerPaired_rational_eq_zero hs hf (fun w hwq hw1 hw2 => ?_)
    have hmem : xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw1)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw1) ∈ K := by
      refine Submodule.le_topologicalClosure _ ?_
      exact Submodule.subset_span ⟨w, hw1, hw2, hwq, rfl⟩
    have hzero := (Submodule.mem_orthogonal K _).mp horth _ hmem
    rw [← inner_conj_symm, Complex.conj_re, ← xiLp_real_inner_eq_re]
    exact hzero
  rw [sub_eq_zero.mp huzero]
  exact hpm

/-- **Equation `(9)`, countable form.** -/
theorem xiHurwitzOrientationVector_mem_xiEulerPairedRationalClosure :
    xiHurwitzOrientationVector ∈ xiEulerPairedRationalClosure :=
  mem_xiEulerPairedRationalClosure_of_mem_sector
    xiHurwitzOrientationVector_mem_xiSchwarzFiberSector

/-- Equation `(18)`: passivity of the Weil quadratic form on real finite packets of
Gaussian-rational absolute-Euler paired Cauchy vectors. -/
def XiEulerSafePairedRationalPassivity : Prop :=
  ∀ v ∈ Submodule.span ℝ xiEulerPairedRationalSet, 0 ≤ xiWeilHilbertQuadratic v

/-- **Equation `(19)`.**  Countable absolute-Euler paired passivity is exactly the Riemann
hypothesis. -/
theorem riemannHypothesis_iff_xiEulerSafePairedRationalPassivity :
    RiemannHypothesis ↔ XiEulerSafePairedRationalPassivity := by
  constructor
  · intro hRH _ _
    exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH _
  · intro hpos
    refine riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.mpr ?_
    have hclosed : IsClosed {u : XiLp | 0 ≤ xiWeilHilbertQuadratic u} :=
      isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
    have hmem : xiHurwitzOrientationVector ∈
        closure ((Submodule.span ℝ xiEulerPairedRationalSet : Submodule ℝ XiLp) : Set XiLp) :=
      xiHurwitzOrientationVector_mem_xiEulerPairedRationalClosure
    exact closure_minimal hpos hclosed hmem

end

end RHTower
