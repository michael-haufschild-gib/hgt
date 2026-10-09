import GaloisForLFunctions.RHTower.CCMFullGroundGaussianGrowthRH
import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.HTGeometry.WeierstrassFactorizationEntire

/-!
# Even real-rooted ground states with bounded inverse-square zero sums force RH

Let `u_j` be ground states of the unconstrained restricted Weil forms at apertures `a_j → ∞`. Assume
their physical functions `f_j` are even, with nonzero mass `∫ f_j` and real-rooted Fourier–Laplace
transforms. Let `F_j(z) = ∫ conj(f_j(t)) e^{izt} dt`, with zeros `ρ` counted with multiplicity.
Suppose that

* `∫ |f_j| ≤ M e^{a_j} |∫ f_j|`, and
* `∑_ρ 1/|ρ|² ≤ S`.

Then the Riemann hypothesis holds.

The second hypothesis says that the zeros of the ground-state transforms stay away from the origin
in the inverse-square sense, uniformly in the aperture.

**Proof.** `F_j` is even and of exponential type, so it is `F_j(0)` times its genus-one canonical
product. The canonical product is bounded by `exp(2|z|² ∑ 1/|ρ|²)`. Hence
`|F_j(z)| ≤ |∫ f_j| e^{2S(1/2+η)²} e^{2S (Re z)²}` on the strip, and the Gaussian-growth capstone
applies.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.EntireZeroDivisor RHTower.OrderOneHadamard

namespace RHTower.CCMFullGroundEigen

open GaloisForLFunctions.HTGeometry
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

theorem conjTransform_neg_of_even {f : ℝ → ℂ} (heven : ∀ t, f (-t) = f t) (z : ℂ) :
    conjTransform f (-z) = conjTransform f z := by
  rw [conjTransform, conjTransform,
    ← integral_neg_eq_self (fun t : ℝ => (starRingEnd ℂ) (f t) * cexp (I * -z * (t : ℂ)))]
  congr 1
  funext t
  rw [heven]
  push_cast
  ring_nf

/-- A transform of an integrable function supported in `[-a, a]` grows at most like `e^{aY}` on
`|Im z| ≤ Y`. -/
theorem norm_conjTransform_le_mul_exp {a Y : ℝ} (hY : 0 ≤ Y) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖conjTransform f z‖ ≤ (∫ t : ℝ, ‖f t‖) * Real.exp (Y * a) := by
  have hmom : ∀ t : ℝ, ‖f t‖ * Real.exp (Y * |t|) ≤ ‖f t‖ * Real.exp (Y * a) := by
    intro t
    by_cases hx : f t = 0
    · rw [hx, norm_zero, zero_mul, zero_mul]
    · gcongr
      exact hs t hx
  have hmomint : Integrable fun t : ℝ => ‖f t‖ * Real.exp (Y * |t|) :=
    (hf.norm.mul_const (Real.exp (Y * a))).mono'
      (hf.norm.aestronglyMeasurable.mul
        (by fun_prop : Continuous fun t : ℝ => Real.exp (Y * |t|)).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hmom t)
  calc ‖conjTransform f z‖ ≤ ∫ t : ℝ, ‖f t‖ * Real.exp (Y * |t|) := norm_conjTransform_le hz hmomint
    _ ≤ ∫ t : ℝ, ‖f t‖ * Real.exp (Y * a) := integral_mono hmomint (hf.norm.mul_const _) hmom
    _ = (∫ t : ℝ, ‖f t‖) * Real.exp (Y * a) := integral_mul_const _ _

/-- The order-one envelope of a nonzero Paley–Wiener transform. -/
theorem exists_orderOne_bound_conjTransform {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) (h0 : conjTransform f 0 ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖conjTransform f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  set L : ℝ := ∫ t : ℝ, ‖f t‖ with hL
  have hbd : ∀ z : ℂ, ‖conjTransform f z‖ ≤ L * Real.exp (‖z‖ * a) := fun z =>
    norm_conjTransform_le_mul_exp (norm_nonneg z) hf hs (Complex.abs_im_le_norm z)
  have hLpos : 0 < L := by
    have h := hbd 0
    rw [norm_zero, zero_mul, Real.exp_zero, mul_one] at h
    exact lt_of_lt_of_le (norm_pos_iff.mpr h0) h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(|Real.log L| + a) / Real.log 2, by positivity, fun z => ?_⟩
  refine (hbd z).trans ?_
  have hLe : L * Real.exp (‖z‖ * a) = Real.exp (Real.log L + ‖z‖ * a) := by
    rw [Real.exp_add, Real.exp_log hLpos]
  rw [hLe]
  apply Real.exp_le_exp.mpr
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hlog : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hcoef : 0 ≤ (|Real.log L| + a) / Real.log 2 := by positivity
  calc Real.log L + ‖z‖ * a ≤ (|Real.log L| + a) * (1 + ‖z‖) := by
        nlinarith [le_abs_self (Real.log L), abs_nonneg (Real.log L)]
    _ = (|Real.log L| + a) / Real.log 2 * (1 + ‖z‖) * Real.log 2 := by
        field_simp
    _ ≤ (|Real.log L| + a) / Real.log 2 * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
        gcongr

/-- **Gaussian growth from an inverse-square zero sum.** An even entire function with an
order-one envelope and `f(0) ≠ 0` satisfies `|f(z)| ≤ |f(0)| exp(2|z|² ∑_ρ 1/|ρ|²)`. -/
theorem norm_le_mul_exp_zeroSum_of_even {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hF : Differentiable ℂ F) (hF0 : F 0 ≠ 0) (heven : ∀ z, F (-z) = F z)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) (z : ℂ) :
    ‖F z‖ ≤ ‖F 0‖ * Real.exp (2 * ‖z‖ ^ 2 *
      ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) := by
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have hord : ∀ w, analyticOrderAt F w ≠ ⊤ :=
    GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hF hF0
  have hfac := eq_const_mul_hadamardProduct_of_even hC hAn hF0 hord heven hbound z
  have hsum := summable_inv_sq_zeroCopyPoint hC hAn hF0 hbound
  have hne := zeroCopyPoint_ne_zero hAn hF0
  rw [hfac, norm_mul]
  gcongr
  refine (canonicalProductE1Indexed_norm_le_exp_min (zeroCopyPoint F) hne hsum z).trans ?_
  apply Real.exp_le_exp.mpr
  have hdom : Summable fun q : ZeroCopy F =>
      2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) := hsum.mul_left _
  have hle : ∀ q : ZeroCopy F, min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
      (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) ≤
        2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) := by
    intro q
    refine (min_le_right _ _).trans (le_of_eq ?_)
    ring
  have hnn : ∀ q : ZeroCopy F, 0 ≤ min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
      (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) :=
    fun q => le_min (by positivity) (by positivity)
  calc ∑' q : ZeroCopy F, min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
        (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ))
      ≤ ∑' q : ZeroCopy F, 2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) :=
        Summable.tsum_le_tsum hle (hdom.of_nonneg_of_le hnn hle) hdom
    _ = 2 * ‖z‖ ^ 2 * ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) := tsum_mul_left

/-- **Even real-rooted eigenvectors with bounded inverse-square zero sums force RH.** -/
theorem riemannHypothesis_of_evenEigenvectors_zeroSum {η M S : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (μ : ℕ → ℝ)
    (heig : ∀ j (s : CCMComplexSmoothInteriorSource (a j)),
      ccmRestrictedWeilForm (a j) (u j) s.toCCMFormVector =
        (μ j : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep (a j) (u j) t) * s t)
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hzero : ∀ j, ∑' q : ZeroCopy (conjTransform (timeRep (a j) (u j))),
      1 / ‖zeroCopyPoint (conjTransform (timeRep (a j) (u j))) q‖ ^ (2 : ℕ) ≤ S) :
    RiemannHypothesis := by
  set Y : ℝ := 1 / 2 + η with hY
  have hS : 0 ≤ S := le_trans (tsum_nonneg fun q => by positivity) (hzero 0)
  have hF0eq : ∀ j, ‖conjTransform (timeRep (a j) (u j)) 0‖ =
      ‖∫ t : ℝ, timeRep (a j) (u j) t‖ := by
    intro j
    simp only [conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [integral_conj, Complex.norm_conj]
  refine riemannHypothesis_of_gaussianGrowthEigenvectors (η := η) (A := 2 * S)
    (M := max M (Real.exp (2 * S * Y ^ 2))) hη (by positivity) a ha u μ heig hreal hmass
    (fun j => (hl1 j).trans ?_) (fun j z hz => ?_)
  · gcongr
    exact le_max_left _ _
  · set f : ℝ → ℂ := timeRep (a j) (u j) with hf
    have hsupp := bound_support_of_supportedIn (supportedIn_timeRep (a j) (u j))
    have hfi := integrable_timeRep (a j) (u j)
    have hF0 : conjTransform f 0 ≠ 0 := by
      rw [← norm_ne_zero_iff, hF0eq]
      exact norm_ne_zero_iff.mpr (hmass j)
    obtain ⟨C, hC, hbound⟩ := exists_orderOne_bound_conjTransform (a j).2.le hfi hsupp hF0
    have hdiff : Differentiable ℂ (conjTransform f) :=
      differentiable_conjTransform (a j).2.le hfi (supportedIn_timeRep (a j) (u j))
    have hFeven : ∀ w, conjTransform f (-w) = conjTransform f w :=
      conjTransform_neg_of_even (heven j)
    have hG := norm_le_mul_exp_zeroSum_of_even hC hdiff hF0 hFeven hbound z
    rw [hF0eq] at hG
    have hz2 : ‖z‖ ^ 2 ≤ z.re ^ 2 + Y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hz' : |z.im| < Y := hz
      have h0 : 0 ≤ |z.im| := abs_nonneg _
      have := mul_self_le_mul_self h0 hz'.le
      nlinarith [sq_abs z.im]
    have hmass0 : 0 ≤ ‖∫ t : ℝ, f t‖ := norm_nonneg _
    calc ‖conjTransform f z‖
        ≤ ‖∫ t : ℝ, f t‖ * Real.exp (2 * ‖z‖ ^ 2 *
          ∑' q : ZeroCopy (conjTransform f), 1 / ‖zeroCopyPoint (conjTransform f) q‖ ^ (2 : ℕ)) :=
          hG
      _ ≤ ‖∫ t : ℝ, f t‖ * Real.exp (2 * S * Y ^ 2 + 2 * S * z.re ^ 2) := by
          gcongr
          calc 2 * ‖z‖ ^ 2 * ∑' q : ZeroCopy (conjTransform f),
                1 / ‖zeroCopyPoint (conjTransform f) q‖ ^ (2 : ℕ)
              ≤ 2 * ‖z‖ ^ 2 * S := by gcongr; exact hzero j
            _ ≤ 2 * S * Y ^ 2 + 2 * S * z.re ^ 2 := by nlinarith
      _ = Real.exp (2 * S * Y ^ 2) * Real.exp (2 * S * z.re ^ 2) * ‖∫ t : ℝ, f t‖ := by
          rw [Real.exp_add]; ring
      _ ≤ max M (Real.exp (2 * S * Y ^ 2)) * Real.exp (2 * S * z.re ^ 2) *
          ‖∫ t : ℝ, f t‖ := by
          gcongr
          exact le_max_right _ _

/-- **Even real-rooted full ground states with bounded inverse-square zero sums force RH.** -/
theorem riemannHypothesis_of_evenFullGrounds_zeroSum {η M S : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hzero : ∀ j, ∑' q : ZeroCopy (conjTransform (timeRep (a j) (u j))),
      1 / ‖zeroCopyPoint (conjTransform (timeRep (a j) (u j))) q‖ ^ (2 : ℕ) ≤ S) :
    RiemannHypothesis :=
  riemannHypothesis_of_evenEigenvectors_zeroSum hη a ha u
    (fun j => ccmRestrictedWeilGroundEnergy (a j))
    (fun j => formEigen_of_isFullGround (a j) (hground j)) hreal hmass heven hl1 hzero

end

end RHTower.CCMFullGroundEigen
