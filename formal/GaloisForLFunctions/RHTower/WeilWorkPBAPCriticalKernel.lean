import GaloisForLFunctions.RHTower.WeilWorkPBAPCriticalDatum
import GaloisForLFunctions.RHTower.WeilFullConeBochnerMeasure

/-!
# Bounded translates for a modified full Weil datum

Positivity on actual smooth autocorrelations bounds every translate of each
fixed autocorrelation. No spectral measure or coefficient summability is
assumed. This is the bounded remainder needed for the residue argument in
`CRITICAL-SLOPE.md`.
-/

open Complex MeasureTheory Finsupp Zeta23
open scoped Real ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided WeilSpectral

/-- The two linear pole evaluations. -/
def poleLinear (k : ℝ → ℂ) : ℂ := paperFT k (I / 2) + paperFT k (-I / 2)

/-- The modified functional, expressed using already verified linear Weil functionals. -/
def criticalFunctional (a b C : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  weilFullFunctional lam k + ((a - 1 : ℝ) : ℂ) * weilFullFunctional 0 k +
    ((b - a : ℝ) : ℂ) * poleLinear k + (C : ℂ) * k 0

theorem poleLinear_add {k l : ℝ → ℂ} (hk : Admissible k) (hl : Admissible l) :
    poleLinear (k + l) = poleLinear k + poleLinear l := by
  simp only [poleLinear, paperFT_add hk hl]
  ring

theorem poleLinear_smul (z : ℂ) (k : ℝ → ℂ) : poleLinear (z • k) = z * poleLinear k := by
  simp only [poleLinear, paperFT_smul]
  ring

theorem poleLinear_tilde (k : ℝ → ℂ) : poleLinear (EF.tilde k) = conj (poleLinear k) := by
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  simp only [poleLinear, EF.paperFT_tilde, hc1, hc2, map_add]
  ring

theorem criticalFunctional_add (a b C : ℝ) (lam : ℕ → ℝ) {k l : ℝ → ℂ}
    (hk : Admissible k) (hl : Admissible l) :
    criticalFunctional a b C lam (k + l) =
      criticalFunctional a b C lam k + criticalFunctional a b C lam l := by
  simp only [criticalFunctional, weilFullFunctional_add lam hk hl,
    weilFullFunctional_add 0 hk hl, poleLinear_add hk hl, Pi.add_apply]
  ring

theorem criticalFunctional_smul (a b C : ℝ) (lam : ℕ → ℝ) (z : ℂ) (k : ℝ → ℂ) :
    criticalFunctional a b C lam (z • k) = z * criticalFunctional a b C lam k := by
  simp only [criticalFunctional, weilFullFunctional_smul, poleLinear_smul,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem criticalFunctional_zero (a b C : ℝ) (lam : ℕ → ℝ) :
    criticalFunctional a b C lam 0 = 0 := by
  have h := criticalFunctional_smul a b C lam 0 0
  simpa using h

theorem criticalFunctional_sum (a b C : ℝ) (lam : ℕ → ℝ) {ι : Type*}
    (s : Finset ι) {k : ι → ℝ → ℂ} (hk : ∀ i ∈ s, Admissible (k i)) :
    criticalFunctional a b C lam (∑ i ∈ s, k i) =
      ∑ i ∈ s, criticalFunctional a b C lam (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using criticalFunctional_zero a b C lam
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      criticalFunctional_add a b C lam (hk i (Finset.mem_insert_self i s))
        (Admissible.sum s fun j hj => hk j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hk j (Finset.mem_insert_of_mem hj)]

theorem criticalFunctional_tilde (a b C : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    criticalFunctional a b C lam (EF.tilde k) = conj (criticalFunctional a b C lam k) := by
  simp only [criticalFunctional, weilFullFunctional_tilde, poleLinear_tilde, EF.tilde,
    neg_zero, map_add, map_mul, Complex.conj_ofReal]

theorem im_criticalFunctional_autocorr (a b C : ℝ) (lam : ℕ → ℝ) (f : ℝ → ℂ) :
    (criticalFunctional a b C lam (EF.weilTest f f)).im = 0 := by
  have h := criticalFunctional_tilde a b C lam (EF.weilTest f f)
  rw [tilde_weilTest_self] at h
  have hi := congrArg Complex.im h
  rw [Complex.conj_im] at hi
  linarith

theorem weilArchRe_eq_testPole_add_testGamma (f : WeilTestFn) :
    weilArchRe (EF.weilTest f.1 f.1) = testPole f.1 + testGamma f.1 := by
  have hG : (∫ t : ℝ, paperFT (EF.weilTest f.1 f.1) t * (EF.gammaBracket t : ℂ)) =
      ((∫ t : ℝ, ‖paperFT f.1 t‖ ^ 2 * EF.gammaBracket t : ℝ) : ℂ) := by
    simp_rw [paperFT_weilTest_self_ofReal f.2.1.continuous f.2.2, ← Complex.ofReal_mul]
    exact integral_complex_ofReal
  have hfac : (1 / (2 * (π : ℂ)) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
  unfold weilArchRe testPole testGamma
  rw [hG, hfac, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re]

theorem autocorr_zero_eq_testMass (f : ℝ → ℂ) :
    EF.weilTest f f 0 = (testMass f : ℂ) := by
  rw [weilTest_apply]
  simp only [sub_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact integral_complex_ofReal

/-- Exact matching with the original finite sample pairing. -/
theorem re_criticalFunctional_autocorr (a b C : ℝ) (lam : ℕ → ℝ) (f : WeilTestFn) :
    (criticalFunctional a b C lam (EF.weilTest f.1 f.1)).re =
      criticalDatum a b C f.1 - testAtoms lam f := by
  have h0 : linearCombination ℝ (fun j : LogIndex => (0 : ℕ → ℝ) j) (logVector f) = 0 := by
    simp [linearCombination_apply]
  simp only [criticalFunctional, Complex.add_re, Complex.re_ofReal_mul]
  rw [re_weilFullFunctional_eq lam f, re_weilFullFunctional_eq 0 f, h0,
    weilArchRe_eq_testPole_add_testGamma, autocorr_zero_eq_testMass, Complex.ofReal_re]
  change _ = (a * testGamma f.1 + b * testPole f.1 + C * testMass f.1) - _
  change _ + (a - 1) * _ + (b - a) * testPole f.1 + _ = _
  unfold testAtoms
  ring

/-- Positive definiteness comes from actual finite sums of smooth translates. -/
theorem positiveDefinite_criticalKernel {a b C : ℝ} {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal
      (fun y => criticalFunctional a b C lam (transl y (EF.weilTest f f))) := by
  intro N t c
  let g : ℝ → ℂ := ∑ j, c j • transl (t j) f
  have hgc : ContDiff ℝ ∞ g := by
    have heq : g = fun x => ∑ j, c j * f (x - t j) := by
      funext x
      simp [g, Finset.sum_apply, transl]
    rw [heq]
    exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))
  have hgs : HasCompactSupport g := HasCompactSupport.finset_sum fun j _ =>
    (hfc.comp_homeomorph (Homeomorph.subRight (t j))).smul_left
  have hadm := admissible_weilTest (contDiff_infty.mp hf 2) hfc
  have hkey : ∑ i, ∑ j, star (c i) *
        criticalFunctional a b C lam (transl (t j - t i) (EF.weilTest f f)) * c j =
      criticalFunctional a b C lam (EF.weilTest g g) := by
    rw [show g = ∑ j, c j • transl (t j) f from rfl,
      weilTest_sum_transl hf.continuous hfc,
      criticalFunctional_sum a b C lam _ fun i _ => Admissible.sum _ fun j _ =>
        (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [criticalFunctional_sum a b C lam _ fun j _ => (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [criticalFunctional_smul]
    ring
  let G : SmoothTest := ⟨⟨g, contDiff_infty.mp hgc 2, hgs⟩, hgc⟩
  have hpos : 0 ≤ (criticalFunctional a b C lam (EF.weilTest g g)).re := by
    rw [re_criticalFunctional_autocorr a b C lam G.1]
    exact sub_nonneg.mpr (h G)
  refine ⟨_, hpos, ?_⟩
  rw [hkey]
  exact Complex.ext rfl (by simpa using im_criticalFunctional_autocorr a b C lam g)

/-- Every translate is bounded by the unshifted positive value. -/
theorem norm_criticalFunctional_transl_le {a b C : ℝ} {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (y : ℝ) :
    ‖criticalFunctional a b C lam (transl y (EF.weilTest f f))‖ ≤
      (criticalFunctional a b C lam (EF.weilTest f f)).re := by
  have hb := (positiveDefinite_criticalKernel h hf hfc).norm_le y
  change ‖criticalFunctional a b C lam (transl y (EF.weilTest f f))‖ ≤
    (criticalFunctional a b C lam (transl 0 (EF.weilTest f f))).re at hb
  have hz : transl 0 (EF.weilTest f f) = EF.weilTest f f := by funext x; simp [transl]
  rw [hz] at hb
  exact hb

/-- Linear gamma pairing, with the paper Fourier normalization. -/
def criticalGammaLinear (k : ℝ → ℂ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, paperFT k t * (EF.gammaBracket t : ℂ)

/-- The locally finite symmetric integer atom pairing. -/
def criticalAtomLinear (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
    (k (Real.log n) + k (-Real.log n))

theorem criticalFunctional_eq (a b C : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    criticalFunctional a b C lam k = (a : ℂ) * criticalGammaLinear k +
      (b : ℂ) * poleLinear k + (C : ℂ) * k 0 - criticalAtomLinear lam k := by
  simp only [criticalFunctional, weilFullFunctional, criticalGammaLinear, criticalAtomLinear,
    poleLinear, Pi.zero_apply, zero_div, ite_self, Complex.ofReal_zero, zero_mul, tsum_zero]
  push_cast
  ring

/-- Translating an admissible gamma pairing cannot increase its absolute-integral envelope. -/
theorem norm_criticalGammaLinear_transl_le (k : ℝ → ℂ) (y : ℝ) :
    ‖criticalGammaLinear (transl y k)‖ ≤
      (1 / (2 * π)) * ∫ t : ℝ, ‖paperFT k t * (EF.gammaBracket t : ℂ)‖ := by
  have hfac : (1 / (2 * (π : ℂ)) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) := by push_cast; rfl
  rw [criticalGammaLinear, norm_mul, hfac, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (by positivity : (0 : ℝ) ≤ 1 / (2 * π))).trans (le_of_eq ?_)
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    simp only [paperFT_transl, norm_mul, norm_cexp_I_mul_ofReal, one_mul]

/-- The actual pole-minus-atom expression has a bounded remainder on every translate.
This uses no coefficient convergence or spectral-measure hypothesis. -/
theorem exists_norm_pole_sub_atoms_transl_le {a b C : ℝ} {lam : ℕ → ℝ}
    (h : ∀ f : SmoothTest, testAtoms lam f.1 ≤ criticalDatum a b C f.1.1)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ M : ℝ, ∀ y : ℝ,
      ‖(b : ℂ) * poleLinear (transl y (EF.weilTest f f)) -
        criticalAtomLinear lam (transl y (EF.weilTest f f))‖ ≤ M := by
  let k := EF.weilTest f f
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hcont : Continuous k :=
    (EF.weilTest_contDiff (contDiff_infty.mp hf 2) hf.continuous hfc).continuous
  obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuous hcont
  let G : ℝ := (1 / (2 * π)) * ∫ t : ℝ, ‖paperFT k t * (EF.gammaBracket t : ℂ)‖
  let K : ℝ := (criticalFunctional a b C lam k).re
  refine ⟨K + |a| * G + |C| * B, fun y => ?_⟩
  have hid : (b : ℂ) * poleLinear (transl y k) - criticalAtomLinear lam (transl y k) =
      criticalFunctional a b C lam (transl y k) -
        (a : ℂ) * criticalGammaLinear (transl y k) - (C : ℂ) * k (-y) := by
    rw [criticalFunctional_eq]
    simp only [transl, zero_sub]
    ring
  change ‖(b : ℂ) * poleLinear (transl y k) - criticalAtomLinear lam (transl y k)‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖criticalFunctional a b C lam (transl y k)‖ +
        ‖(a : ℂ) * criticalGammaLinear (transl y k)‖ + ‖(C : ℂ) * k (-y)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ K + |a| * G + |C| * B := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (add_le_add (norm_criticalFunctional_transl_le h hf hfc y)
        (mul_le_mul_of_nonneg_left (norm_criticalGammaLinear_transl_le k y) (abs_nonneg a)))
        (mul_le_mul_of_nonneg_left (hB (-y)) (abs_nonneg C))

end RHTower.WeilWorkPBAP
