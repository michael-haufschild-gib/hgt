import GaloisForLFunctions.RHTower.PrimeQuasiInnerEulerReconstruction
import GaloisForLFunctions.RHTower.PrimeWinningFaceUnit
import GaloisForLFunctions.RHTower.MobiusLaplaceLandauOscillation
import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation
import GaloisForLFunctions.RHTower.CCMSimplePrimeDivisorSource

/-!
# Surviving poles of finitely weighted divisor sources

The exact pole-filled source `-ζ'/ζ - ζ` is multiplied by an arbitrary finite
Dirichlet polynomial. A nonzero weight leaves simple critical poles beyond every
height. Finite Euler denominators, the two Mellin integration factors, and an
arbitrary constant correction preserve those poles. The same candidate Mellin
expression is analytic on the low-height balls used by positive-carrier Landau
transfer. Its equality with the literal retained-source integral is not asserted.
-/

noncomputable section
open Complex Filter Function Set Topology
namespace RHTower

/-- The unshifted, pole-filled divisor source with a finite Dirichlet weight and a
constant correction. The Mellin variable is obtained by adding `1/2`. -/
def finiteDirichletDivisorSource (a : ℕ →₀ ℂ) (c : ℂ) (w : ℂ) : ℂ :=
  finiteDirichletPolynomial a w * (simplePrimeDivisorContinuedSource (w + 1 / 2) + c)

private lemma analyticAt_divisorSourceCorrection (c s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => -dslope regularizedRiemannZeta 1 z + c) s := by
  have hd : Differentiable ℂ (dslope regularizedRiemannZeta 1) := by
    rw [← differentiableOn_univ, differentiableOn_dslope Filter.univ_mem]
    exact differentiable_regularizedRiemannZeta.differentiableOn
  exact (hd.analyticAt s).neg.add analyticAt_const

/-- A nonvanishing finite weight leaves the exact simple pole at every zero of
pole-filled zeta. The constant correction cannot alter the pole order. -/
theorem meromorphicOrderAt_finiteDirichletDivisorSource_eq_neg_one
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (c : ℂ) {s : ℂ}
    (hz : regularizedRiemannZeta s = 0) (hp : finiteDirichletPolynomial a s ≠ 0) :
    meromorphicOrderAt (finiteDirichletDivisorSource a c) s =
      ((-1 : ℤ) : WithTop ℤ) := by
  let singular : ℂ → ℂ := fun z => -logDeriv regularizedRiemannZeta z
  let correction : ℂ → ℂ := fun z => -dslope regularizedRiemannZeta 1 z + c
  have hs : MeromorphicAt singular s := (meromorphicAt_logDeriv_regularizedRiemannZeta s).neg
  have hso : meromorphicOrderAt singular s = ((-1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt (-(logDeriv regularizedRiemannZeta)) s = _
    rw [← meromorphicOrderAt_neg, meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hz]
  have hc : AnalyticAt ℂ correction s := analyticAt_divisorSourceCorrection c s
  have hlt : meromorphicOrderAt singular s < meromorphicOrderAt correction s := by
    rw [hso]
    exact lt_of_lt_of_le (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hc.meromorphicOrderAt_nonneg
  have hsum : meromorphicOrderAt (singular + correction) s =
      ((-1 : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_add_eq_left_of_lt hc.meromorphicAt hlt, hso]
  have hpoly : AnalyticAt ℂ (finiteDirichletPolynomial a) s :=
    (differentiable_finiteDirichletPolynomial a ha).analyticAt s
  have hpo : meromorphicOrderAt (finiteDirichletPolynomial a) s = 0 := by
    rw [hpoly.meromorphicOrderAt_eq, hpoly.analyticOrderAt_eq_zero.mpr hp]
    simp
  have hfun : finiteDirichletDivisorSource a c =
      finiteDirichletPolynomial a * (singular + correction) := by
    ext z
    simp only [finiteDirichletDivisorSource, simplePrimeDivisorContinuedSource,
      add_sub_cancel_right, Pi.mul_apply, Pi.add_apply, singular, correction]
    ring
  rw [hfun, meromorphicOrderAt_mul hpoly.meromorphicAt (hs.add hc.meromorphicAt), hpo, hsum]
  simp

/-- Finite nonzero weights leave genuine simple poles above every height on the
critical line, independently of the constant correction. -/
theorem exists_high_simpleCritical_finiteDirichletDivisorSource_pole
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) (c : ℂ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      meromorphicOrderAt (finiteDirichletDivisorSource a c) (linePt t) =
        ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨t, hT, ht, hz, ho, hp⟩ :=
    exists_high_simpleCritical_finiteDirichletPolynomial_ne_zero a ha hne T
  refine ⟨t, hT, ht, hz, ho, meromorphicOrderAt_finiteDirichletDivisorSource_eq_neg_one a ha c ?_ hp⟩
  have hs1 : linePt t ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    rw [linePt_re] at hr
    norm_num at hr
  have hzeta : riemannZeta (linePt t) = 0 :=
    (xi_eq_zero_iff (by rw [linePt_re]; norm_num) hs1).mp hz
  rw [regularizedRiemannZeta_of_ne_one hs1, hzeta, mul_zero]


/-- The finitely weighted divisor source is meromorphic everywhere. -/
theorem meromorphicAt_finiteDirichletDivisorSource
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (c s : ℂ) :
    MeromorphicAt (finiteDirichletDivisorSource a c) s := by
  have hp := (differentiable_finiteDirichletPolynomial a ha).analyticAt s
  have hs := (meromorphicAt_logDeriv_regularizedRiemannZeta s).neg.add
    (analyticAt_divisorSourceCorrection c s).meromorphicAt
  have hfun : finiteDirichletDivisorSource a c =
      (fun z => finiteDirichletPolynomial a z *
        (-logDeriv regularizedRiemannZeta z + (-dslope regularizedRiemannZeta 1 z + c))) := by
    ext z
    simp only [finiteDirichletDivisorSource, simplePrimeDivisorContinuedSource,
      add_sub_cancel_right]
    ring
  rw [hfun]
  exact hp.meromorphicAt.mul hs

/-- Finite Euler denominators are entire. -/
theorem differentiable_finitePrimeEulerDenominator (P : Finset Nat.Primes) :
    Differentiable ℂ (finitePrimeEulerDenominator P) := by
  intro s
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  exact (differentiable_const (1 : ℂ)).differentiableAt.sub
    (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast p.property.ne_zero)))

/-- Finite Euler denominators have no zero in the positive half-plane. -/
theorem finitePrimeEulerDenominator_ne_zero (P : Finset Nat.Primes) {s : ℂ}
    (hs : 0 < s.re) : finitePrimeEulerDenominator P s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact one_sub_primeCpow_neg_ne_zero hs p

/-- The candidate Mellin expression with the finite Euler denominator and the two
integration-clock factors retained. Equality with the literal source integral is separate. -/
def finiteDirichletDivisorMellin (a : ℕ →₀ ℂ) (P : Finset Nat.Primes) (c s : ℂ) : ℂ :=
  finiteDirichletDivisorSource a c (s - 1 / 2) /
    (finitePrimeEulerDenominator P (s - 1 / 2) * (2 * s * (s - 1 / 2)))

private lemma analyticAt_divisorMellinDenominator (P : Finset Nat.Primes) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ =>
      finitePrimeEulerDenominator P (z - 1 / 2) * (2 * z * (z - 1 / 2))) s := by
  have he := ((differentiable_finitePrimeEulerDenominator P).comp
    (differentiable_id.sub_const (1 / 2))).analyticAt s
  exact he.mul (by fun_prop)

private lemma divisorMellinDenominator_ne_zero (P : Finset Nat.Primes) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    finitePrimeEulerDenominator P (s - 1 / 2) * (2 * s * (s - 1 / 2)) ≠ 0 := by
  have hw : 0 < (s - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hw0 : s - 1 / 2 ≠ 0 := by intro h; exact (ne_of_gt hw) (by rw [h]; rfl)
  exact mul_ne_zero (finitePrimeEulerDenominator_ne_zero P hw)
    (mul_ne_zero (mul_ne_zero (by norm_num) hs0) hw0)

/-- A surviving divisor pole keeps its order after the actual Mellin shift and all
finite Euler and integration-clock denominators. -/
theorem meromorphicOrderAt_finiteDirichletDivisorMellin_eq_neg_one
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (P : Finset Nat.Primes) (c : ℂ) {s : ℂ}
    (hs : 1 / 2 < s.re)
    (hz : regularizedRiemannZeta (s - 1 / 2) = 0)
    (hp : finiteDirichletPolynomial a (s - 1 / 2) ≠ 0) :
    meromorphicOrderAt (finiteDirichletDivisorMellin a P c) s =
      ((-1 : ℤ) : WithTop ℤ) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  have hdshift : deriv (fun z : ℂ => z - 1 / 2) s ≠ 0 := by
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hnum : MeromorphicAt
      (fun z : ℂ => finiteDirichletDivisorSource a c (z - 1 / 2)) s :=
    (meromorphicAt_finiteDirichletDivisorSource a ha c _).comp_analyticAt hshift
  have hnumOrder : meromorphicOrderAt
      (fun z : ℂ => finiteDirichletDivisorSource a c (z - 1 / 2)) s =
      ((-1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z : ℂ => finiteDirichletDivisorSource a c (z - 1 / 2)) =
        finiteDirichletDivisorSource a c ∘ (fun z : ℂ => z - 1 / 2) by rfl,
      meromorphicOrderAt_comp_of_deriv_ne_zero hshift hdshift]
    exact meromorphicOrderAt_finiteDirichletDivisorSource_eq_neg_one a ha c hz hp
  have hden := analyticAt_divisorMellinDenominator P s
  have hdenOrder : meromorphicOrderAt (fun z : ℂ =>
      finitePrimeEulerDenominator P (z - 1 / 2) * (2 * z * (z - 1 / 2))) s = 0 := by
    rw [hden.meromorphicOrderAt_eq,
      hden.analyticOrderAt_eq_zero.mpr (divisorMellinDenominator_ne_zero P hs)]
    simp
  change meromorphicOrderAt (fun z : ℂ =>
    finiteDirichletDivisorSource a c (z - 1 / 2) /
      (finitePrimeEulerDenominator P (z - 1 / 2) * (2 * z * (z - 1 / 2)))) s = _
  rw [fun_meromorphicOrderAt_div hnum hden.meromorphicAt, hnumOrder, hdenOrder, sub_zero]

/-- The candidate Mellin transform has genuine poles of real part one beyond
every height, for every finite Euler aperture and every constant correction. -/
theorem exists_high_simpleCritical_finiteDirichletDivisorMellin_pole
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (hne : a ≠ 0) (P : Finset Nat.Primes) (c : ℂ) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 0 < t ∧ xi (linePt t) = 0 ∧
      (analyticOrderAt xi (linePt t)).toNat = 1 ∧
      meromorphicOrderAt (finiteDirichletDivisorMellin a P c) (linePt t + 1 / 2) =
        ((-1 : ℤ) : WithTop ℤ) := by
  obtain ⟨t, hT, ht, hz, ho, hp⟩ :=
    exists_high_simpleCritical_finiteDirichletPolynomial_ne_zero a ha hne T
  refine ⟨t, hT, ht, hz, ho, meromorphicOrderAt_finiteDirichletDivisorMellin_eq_neg_one
    a ha P c ?_ ?_ (by simpa only [add_sub_cancel_right] using hp)⟩
  · rw [add_re, linePt_re]
    norm_num
  · have hs1 : linePt t ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      rw [linePt_re] at hr
      norm_num at hr
    have hzeta : riemannZeta (linePt t) = 0 :=
      (xi_eq_zero_iff (by rw [linePt_re]; norm_num) hs1).mp hz
    rw [add_sub_cancel_right, regularizedRiemannZeta_of_ne_one hs1, hzeta, mul_zero]

/-- In the unconditional low-height zero-free strip the same Mellin expression
is analytic, including the cancelled arithmetic pole at `3/2`. -/
theorem analyticAt_finiteDirichletDivisorMellin_of_small_im
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (P : Finset Nat.Primes) (c : ℂ) {s : ℂ}
    (hs : 1 / 2 < s.re) (him : |s.im| ≤ 4) :
    AnalyticAt ℂ (finiteDirichletDivisorMellin a P c) s := by
  have hw : 0 < (s - 1 / 2).re := by simp only [sub_re]; norm_num; linarith
  have hwim : |(s - 1 / 2).im| ≤ 4 := by simpa using him
  have hu : regularizedRiemannZeta (s - 1 / 2) ≠ 0 :=
    zetaResidueUnit_ne_zero_of_re_pos_abs_im_le_four hw hwim
  have hbase : AnalyticAt ℂ simplePrimeDivisorContinuedSource s :=
    analyticAt_simplePrimeDivisorContinuedSource_of_regularizedZeta_ne_zero hu
  have hp := ((differentiable_finiteDirichletPolynomial a ha).comp
    (differentiable_id.sub_const (1 / 2))).analyticAt s
  have hnum := hp.mul (hbase.add (analyticAt_const (v := c)))
  have hden := analyticAt_divisorMellinDenominator P s
  have hresult : AnalyticAt ℂ (fun z : ℂ =>
      finiteDirichletPolynomial a (z - 1 / 2) *
        (simplePrimeDivisorContinuedSource z + c) /
        (finitePrimeEulerDenominator P (z - 1 / 2) * (2 * z * (z - 1 / 2)))) s :=
    hnum.div hden (divisorMellinDenominator_ne_zero P hs)
  unfold finiteDirichletDivisorMellin finiteDirichletDivisorSource
  simp only [sub_add_cancel]
  exact hresult


/-- The low-height strip supplies every closed ball required to transfer a
positive carrier centered at Mellin abscissa four down to abscissa one half. -/
theorem differentiableOn_finiteDirichletDivisorMellin_landau_ball
    (a : ℕ →₀ ℂ) (ha : a 0 = 0) (P : Finset Nat.Primes) (c : ℂ)
    {R : ℝ} (hR : R < 7 / 2) :
    DifferentiableOn ℂ (fun z : ℂ => finiteDirichletDivisorMellin a P c (4 - z))
      (Metric.closedBall 0 R) := by
  intro z hz
  have hn : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
  have hre : 1 / 2 < (4 - z).re := by
    have hb := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
    simp only [sub_re]
    norm_num
    linarith
  have him : |(4 - z).im| ≤ 4 := by
    have hb := Complex.abs_im_le_norm z
    simp only [sub_im]
    norm_num
    linarith
  have hbase := analyticAt_finiteDirichletDivisorMellin_of_small_im a ha P c hre him
  exact (hbase.comp (by fun_prop : AnalyticAt ℂ (fun w : ℂ => 4 - w) z)).differentiableAt.differentiableWithinAt

end RHTower
