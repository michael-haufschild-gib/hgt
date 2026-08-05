import GaloisForLFunctions.RHTower.XiMassBottomEdge
import GaloisForLFunctions.RHTower.StripHorizontalShift

/-!
# Exact prime-atom depth erasure for the mass-shifted Xi bottom edge

The literal von-Mangoldt bottom source is expanded before any absolute value is taken.  For each
Dirichlet atom, its Euler depth factor is exactly the Fourier character evaluated on the lower
horizontal line.  Holomorphic strip transport therefore removes the contour depth atom by atom:

`∫ g(x-ci) Λ(n)n^{-(1/2+c+ix)} dx = Λ(n)n^{-1/2} ĝ(log n)`.

The atom integral norms are summable on every legal Euler line, so the Bochner integral and
Dirichlet `tsum` interchange unconditionally.  The complete prime source is consequently an
absolutely convergent, depth-free series at the prime-log frequencies.  This preserves the phase
that sourcewise norm estimates discard and isolates the remaining obstruction as a cofinal scalar
cancellation problem rather than a contour-depth problem.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Lower-line form of horizontal strip transport, obtained from the upper-line theorem by the
holomorphic reflection `z ↦ -z`. -/
theorem integral_horizontal_shift_neg_of_decay {F : ℂ → ℂ} {c C r : ℝ}
    (hc : 0 ≤ c) (hr : 0 < r)
    (hF : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖F z‖ ≤ C * Real.exp (-(r * |z.re|))) :
    (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I)) = ∫ x : ℝ, F (x : ℂ) := by
  let G : ℂ → ℂ := fun z => F (-z)
  have hG : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z := by
    intro z hz
    refine (hF (-z) ?_).comp z (by fun_prop)
    simpa using hz
  have hGbound : ∀ z : ℂ, |z.im| ≤ c →
      ‖G z‖ ≤ C * Real.exp (-(r * |z.re|)) := by
    intro z hz
    simpa [G] using hbound (-z) (by simpa using hz)
  have hshift := integral_horizontal_shift_of_decay hc hr hG hGbound
  have hleft :
      (∫ x : ℝ, G ((x : ℂ) + (c : ℂ) * I)) =
        ∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I) := by
    rw [← MeasureTheory.integral_neg_eq_self
      (fun x : ℝ => F ((x : ℂ) - (c : ℂ) * I)) volume]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only [G]
    congr 1
    push_cast
    ring
  have hright : (∫ x : ℝ, G (x : ℂ)) = ∫ x : ℝ, F (x : ℂ) := by
    simpa [G] using
      (MeasureTheory.integral_neg_eq_self (fun x : ℝ => F (x : ℂ)) volume)
  rw [← hleft, hshift, hright]

/-- One literal von-Mangoldt atom on the mass bottom edge. -/
def xiMassBottomPrimeAtomIntegrand (a c : ℝ) (τ : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  xiMassBottomTest a c τ x *
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
      (xiMassBottomEulerPoint c x) n

/-- Depth-free centered Fourier atom at the logarithmic frequency of `n`. -/
def xiMassCenteredPrimeAtom (a : ℝ) (τ : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n *
    stripFourier (xiMassAnalyticTest a τ) (Real.log n : ℂ)

lemma xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase
    {c x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
        (xiMassBottomEulerPoint c x) n =
      LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) (1 / 2 : ℂ) n *
        Complex.exp (-(I * (Real.log n : ℂ) * ((x : ℂ) - (c : ℂ) * I))) := by
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero hnC,
    hlog, div_eq_mul_inv, div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_neg,
    mul_assoc, ← Complex.exp_add]
  congr 2
  simp [xiMassBottomEulerPoint]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_xiMassFourierKernel_le
    {a c : ℝ} (hca : c < a) {τ : ℂ} (hτ : 0 < τ.re) (w : ℝ)
    {z : ℂ} (hz : |z.im| ≤ c) :
    ‖xiMassAnalyticTest a τ z * Complex.exp (-(I * (w : ℂ) * z))‖ ≤
      Real.exp ((|τ.im| + |w|) * c) * Real.exp (-(τ.re * |z.re|)) := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg z.im) (lt_of_le_of_lt hz hca)
  have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hca
  have hg := norm_xiMassAnalyticTest_le ha hτ.le hmem
  have hphase : (-(I * (w : ℂ) * z)).re = w * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have hwz : w * z.im ≤ |w| * |z.im| := by
    calc
      w * z.im ≤ |w * z.im| := le_abs_self _
      _ = |w| * |z.im| := abs_mul _ _
  have hu : |τ.im| * |z.im| ≤ |τ.im| * c :=
    mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  have hw : |w| * |z.im| ≤ |w| * c :=
    mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  rw [norm_mul, Complex.norm_exp, hphase]
  calc
    ‖xiMassAnalyticTest a τ z‖ * Real.exp (w * z.im) ≤
        Real.exp (-τ.re * |z.re| + |τ.im| * |z.im|) *
          Real.exp (w * z.im) :=
      mul_le_mul_of_nonneg_right hg (Real.exp_nonneg _)
    _ = Real.exp (-τ.re * |z.re| + |τ.im| * |z.im| + w * z.im) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp ((|τ.im| + |w|) * c - τ.re * |z.re|) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp ((|τ.im| + |w|) * c) * Real.exp (-(τ.re * |z.re|)) := by
      rw [← Real.exp_add]
      congr 1

/-- Exact atomwise depth erasure: every legal bottom line gives the same centered Fourier atom. -/
theorem integral_xiMassBottomPrimeAtom_eq_centered
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    (∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a c τ n x) =
      xiMassCenteredPrimeAtom a τ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [xiMassBottomPrimeAtomIntegrand, xiMassCenteredPrimeAtom, LSeries.term_zero]
  · let F : ℂ → ℂ := fun z =>
      xiMassAnalyticTest a τ z * Complex.exp (-(I * (Real.log n : ℂ) * z))
    have hc0 : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
    have hdiff : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := by
      intro z hz
      have ha : 0 < a := lt_trans (lt_trans (by norm_num) hhalf) hca
      have hmem : z ∈ xiMassStrip a := lt_of_le_of_lt hz hca
      exact (hasDerivAt_xiMassAnalyticTest ha τ hmem).differentiableAt.mul (by fun_prop)
    have hbound : ∀ z : ℂ, |z.im| ≤ c →
        ‖F z‖ ≤ Real.exp ((|τ.im| + |Real.log n|) * c) *
          Real.exp (-(τ.re * |z.re|)) := by
      intro z hz
      exact norm_xiMassFourierKernel_le hca hτ (Real.log n) hz
    have hshift := integral_horizontal_shift_neg_of_decay hc0 hτ hdiff hbound
    have hpoint : ∀ x : ℝ,
        xiMassBottomPrimeAtomIntegrand a c τ n x =
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (c : ℂ) * I) := by
      intro x
      rw [xiMassBottomPrimeAtomIntegrand, xiMassBottomTest,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      dsimp only [F]
      ring
    rw [show (∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a c τ n x) =
        ∫ x : ℝ,
          LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (c : ℂ) * I) by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [MeasureTheory.integral_const_mul, hshift]
    rfl

/-- Absolute Dirichlet weight on the legal Euler line `Re s = 1/2+c`. -/
def xiMassBottomPrimeAtomWeight (c : ℝ) (n : ℕ) : ℝ :=
  ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
    (((1 / 2 + c : ℝ) : ℂ)) n‖

theorem continuous_xiMassBottomPrimeAtomIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a) (τ : ℂ) (n : ℕ) :
    Continuous (xiMassBottomPrimeAtomIntegrand a c τ n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show xiMassBottomPrimeAtomIntegrand a c τ 0 = fun _ : ℝ => (0 : ℂ) by
      funext x
      rw [xiMassBottomPrimeAtomIntegrand, LSeries.term_zero, mul_zero]]
    exact continuous_const
  · have hpoint : xiMassBottomPrimeAtomIntegrand a c τ n = fun x =>
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
            (1 / 2 : ℂ) n *
          (xiMassBottomTest a c τ x *
            Complex.exp (-(I * (Real.log n : ℂ) * ((x : ℂ) - (c : ℂ) * I)))) := by
      funext x
      rw [xiMassBottomPrimeAtomIntegrand,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      ring
    rw [hpoint]
    exact continuous_const.mul ((continuous_xiMassBottomTest hhalf hca τ).mul
      (Complex.continuous_exp.comp (by fun_prop)))

theorem norm_xiMassBottomPrimeAtomIntegrand_le
    {a c x : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 ≤ τ.re) (n : ℕ) :
    ‖xiMassBottomPrimeAtomIntegrand a c τ n x‖ ≤
      (Real.exp (|τ.im| * c) * xiMassBottomPrimeAtomWeight c n) *
        Real.exp (-(τ.re * |x|)) := by
  have hm := norm_xiMassBottomTest_le hhalf hca hτ (x := x)
  have hterm :
      ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ))
          (xiMassBottomEulerPoint c x) n‖ = xiMassBottomPrimeAtomWeight c n := by
    unfold xiMassBottomPrimeAtomWeight
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp [xiMassBottomEulerPoint, Complex.mul_re]
  rw [xiMassBottomPrimeAtomIntegrand, norm_mul, hterm]
  calc
    ‖xiMassBottomTest a c τ x‖ * xiMassBottomPrimeAtomWeight c n ≤
        (Real.exp (|τ.im| * c) * Real.exp (-(τ.re * |x|))) *
          xiMassBottomPrimeAtomWeight c n :=
      mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ = (Real.exp (|τ.im| * c) * xiMassBottomPrimeAtomWeight c n) *
        Real.exp (-(τ.re * |x|)) := by ring

theorem integrable_xiMassBottomPrimeAtomIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) (n : ℕ) :
    Integrable (xiMassBottomPrimeAtomIntegrand a c τ n) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs hτ).const_mul
      (Real.exp (|τ.im| * c) * xiMassBottomPrimeAtomWeight c n))
    (continuous_xiMassBottomPrimeAtomIntegrand hhalf hca τ n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      norm_xiMassBottomPrimeAtomIntegrand_le hhalf hca hτ.le n)

theorem summable_xiMassBottomPrimeAtomWeight {c : ℝ} (hhalf : 1 / 2 < c) :
    Summable (xiMassBottomPrimeAtomWeight c) := by
  have hsum : LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (((1 / 2 + c : ℝ) : ℂ)) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by
      simp
      linarith)
  exact summable_norm_iff.mpr hsum

theorem summable_integral_norm_xiMassBottomPrimeAtomIntegrand
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖xiMassBottomPrimeAtomIntegrand a c τ n x‖) := by
  let E : ℝ := Real.exp (|τ.im| * c)
  let J : ℝ := ∫ x : ℝ, Real.exp (-(τ.re * |x|))
  have hbound : ∀ n : ℕ,
      (∫ x : ℝ, ‖xiMassBottomPrimeAtomIntegrand a c τ n x‖) ≤
        (E * J) * xiMassBottomPrimeAtomWeight c n := by
    intro n
    have hmajor : Integrable (fun x : ℝ =>
        (E * xiMassBottomPrimeAtomWeight c n) * Real.exp (-(τ.re * |x|))) :=
      (integrable_exp_neg_mul_abs hτ).const_mul _
    calc
      (∫ x : ℝ, ‖xiMassBottomPrimeAtomIntegrand a c τ n x‖) ≤
          ∫ x : ℝ,
            (E * xiMassBottomPrimeAtomWeight c n) * Real.exp (-(τ.re * |x|)) :=
        integral_mono
          (integrable_xiMassBottomPrimeAtomIntegrand hhalf hca hτ n).norm
          hmajor
          (fun x => norm_xiMassBottomPrimeAtomIntegrand_le hhalf hca hτ.le n)
      _ = (E * J) * xiMassBottomPrimeAtomWeight c n := by
        rw [MeasureTheory.integral_const_mul]
        dsimp only [J]
        ring
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)
    hbound
    ((summable_xiMassBottomPrimeAtomWeight hhalf).mul_left (E * J))

/-- The depth-free prime-log Fourier atoms form an absolutely summable family. -/
theorem summable_xiMassCenteredPrimeAtom
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Summable (xiMassCenteredPrimeAtom a τ) := by
  have hnorm : Summable (fun n : ℕ =>
      ‖∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a c τ n x‖) :=
    Summable.of_nonneg_of_le
      (fun _ => norm_nonneg _)
      (fun _ => norm_integral_le_integral_norm _)
      (summable_integral_norm_xiMassBottomPrimeAtomIntegrand hhalf hca hτ)
  have hint : Summable (fun n : ℕ =>
      ∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a c τ n x) :=
    summable_norm_iff.mp hnorm
  exact hint.congr (fun n => integral_xiMassBottomPrimeAtom_eq_centered hhalf hca hτ n)

theorem xiMassBottomPrimeIntegrand_eq_tsum_atom
    (a c : ℝ) (τ : ℂ) (x : ℝ) :
    xiMassBottomPrimeIntegrand a c τ x =
      ∑' n : ℕ, xiMassBottomPrimeAtomIntegrand a c τ n x := by
  unfold xiMassBottomPrimeIntegrand xiMassBottomPrimeAtomIntegrand LSeries
  rw [tsum_mul_left]

/-- Complete source-sensitive atomization of the literal prime bottom integral. -/
theorem integral_xiMassBottomPrimeIntegrand_eq_tsum_centeredAtom
    {a c : ℝ} (hhalf : 1 / 2 < c) (hca : c < a)
    {τ : ℂ} (hτ : 0 < τ.re) :
    (∫ x : ℝ, xiMassBottomPrimeIntegrand a c τ x) =
      ∑' n : ℕ, xiMassCenteredPrimeAtom a τ n := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrable_xiMassBottomPrimeAtomIntegrand hhalf hca hτ n)
    (summable_integral_norm_xiMassBottomPrimeAtomIntegrand hhalf hca hτ)
  calc
    (∫ x : ℝ, xiMassBottomPrimeIntegrand a c τ x) =
        ∫ x : ℝ, ∑' n : ℕ, xiMassBottomPrimeAtomIntegrand a c τ n x := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
        xiMassBottomPrimeIntegrand_eq_tsum_atom a c τ x)
    _ = ∑' n : ℕ, ∫ x : ℝ, xiMassBottomPrimeAtomIntegrand a c τ n x := hswap.symm
    _ = ∑' n : ℕ, xiMassCenteredPrimeAtom a τ n := by
      exact tsum_congr (fun n => integral_xiMassBottomPrimeAtom_eq_centered hhalf hca hτ n)

end

end RHTower
