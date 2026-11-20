import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.UnivariateSublevel
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.MeasureTheory.Integral.Pi

/-! # Small values of polynomials in independent Gaussian coefficients

Condition on all but one variable. The leading coefficient is a polynomial of
degree at most d−k if the remaining fiber has degree k. Iterating the root
interval estimate therefore costs at most 2dr in total.
-/
open MeasureTheory ProbabilityTheory Polynomial Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private abbrev consReal {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons x y

private abbrev gaussianCoordinates (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

private def smallPolynomialValues {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (a : ℝ) : Set (Fin n → ℝ) :=
  {x | ‖MvPolynomial.eval (fun i => (x i : ℂ)) f‖ < a}

private theorem measurable_smallPolynomialValues {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (a : ℝ) :
    MeasurableSet (smallPolynomialValues f a) := by
  have h : Continuous (fun x : Fin n → ℝ => fun i : Fin n => (x i : ℂ)) :=
    continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
  exact ((f.continuous_eval.comp h).norm.isOpen_preimage _ isOpen_Iio).measurableSet

/-- Integrate a one-coordinate estimate, charging the full mass of each
exceptional fiber. -/
private theorem gaussian_fibers_le {n : ℕ} (S : Set (Fin (n+1) → ℝ)) (hS : MeasurableSet S)
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) (a : ℝ≥0∞)
    (hf : ∀ y ∉ B, gaussianReal 0 1 {x : ℝ | consReal x y ∈ S} ≤ a) :
    gaussianCoordinates (n+1) S ≤ gaussianCoordinates n B + a := by
  classical
  let E := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hE := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) 0).symm
  have hpre : gaussianCoordinates (n+1) S =
      ((gaussianReal 0 1).prod (gaussianCoordinates n)) (E ⁻¹' S) :=
    (hE.measure_preimage hS.nullMeasurableSet).symm
  rw [hpre,Measure.prod_apply_symm (E.measurable hS)]
  let b := B.indicator fun _ => (1 : ℝ≥0∞)
  have hb : Measurable b := measurable_const.indicator hB
  calc
    _ ≤ ∫⁻ y, b y + a ∂gaussianCoordinates n := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ B
      · exact (prob_le_one).trans (by simp [b,hy])
      · have hc (x : ℝ) : E (x,y) = consReal x y := by
          simp [E,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero']
        change gaussianReal 0 1 {x : ℝ | E (x,y) ∈ S} ≤ b y + a
        rw [show b y = 0 from Set.indicator_of_notMem hy _,zero_add]
        simpa only [hc] using hf y hy
    _ = _ := by
      rw [lintegral_add_left hb,lintegral_indicator hB]
      simp

/-- The coefficient of the lexicographically leading monomial, obtained by
taking leading coefficients one variable at a time. -/
def lexHeadCoefficient : {n : ℕ} → MvPolynomial (Fin n) ℂ → ℂ
  | 0, f => f.coeff 0
  | n+1, f => lexHeadCoefficient ((MvPolynomial.finSuccEquiv ℂ n f).leadingCoeff)

/-- A nonzero polynomial has a nonzero lexicographically leading coefficient. -/
theorem lexHeadCoefficient_ne_zero {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0) :
    lexHeadCoefficient f ≠ 0 := by
  induction n with
  | zero =>
    intro h
    exact hf ((MvPolynomial.eq_C_of_isEmpty f).trans (by rw [show f.coeff 0 = 0 from h,map_zero]))
  | succ n ih =>
    apply ih
    exact Polynomial.leadingCoeff_ne_zero.mpr (fun h => hf ((MvPolynomial.finSuccEquiv ℂ n).injective (h.trans (map_zero _).symm)))

private theorem specialized_fiber_le {n : ℕ} (f : MvPolynomial (Fin (n+1)) ℂ)
    (y : Fin n → ℝ) (a r : ℝ) (hr : 0 ≤ r) :
    let P := MvPolynomial.finSuccEquiv ℂ n f
    let φ := MvPolynomial.eval (fun i => (y i : ℂ))
    φ P.leadingCoeff ≠ 0 → a ≤ ‖φ P.leadingCoeff‖*r^P.natDegree →
      gaussianReal 0 1 {x : ℝ | consReal x y ∈ smallPolynomialValues f a} ≤
        ENNReal.ofReal (2*P.natDegree*r) := by
  intro P φ hn ha
  have hd : (P.map φ).natDegree = P.natDegree := Polynomial.natDegree_map_eq_iff.mpr (Or.inl hn)
  have hl := Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero φ hn
  have he (x : ℝ) : MvPolynomial.eval (Complex.ofReal ∘ consReal x y) f = (P.map φ).eval (x:ℂ) := by
    rw [show Complex.ofReal ∘ consReal x y = Fin.cons (x:ℂ) (Complex.ofReal ∘ y)
      from Fin.comp_cons Complex.ofReal x y]
    exact MvPolynomial.eval_eq_eval_mv_eval' _ _ f
  have hsub : {x : ℝ | consReal x y ∈ smallPolynomialValues f a} ⊆
      {x : ℝ | ‖(P.map φ).eval (x:ℂ)‖ < ‖(P.map φ).leadingCoeff‖*r^(P.map φ).natDegree} := by
    intro x hx
    change ‖MvPolynomial.eval (Complex.ofReal ∘ consReal x y) f‖ < a at hx
    change ‖(P.map φ).eval (x:ℂ)‖ < ‖(P.map φ).leadingCoeff‖*r^(P.map φ).natDegree
    rw [he x] at hx
    rw [hl,hd]
    exact hx.trans_le ha
  apply (measure_mono hsub).trans
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal ((gaussian_polynomial_sublevel (P.map φ) r hr).trans_eq (by rw [hd]))

/-- At a fraction rᵈ of its lexicographically leading coefficient, a
degree-d polynomial has Gaussian sublevel probability at most 2dr,
uniformly in the number of variables. -/
private theorem sublevel_probability_le {n : ℕ} (f : MvPolynomial (Fin n) ℂ)
    (hf : f ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    gaussianCoordinates n (smallPolynomialValues f (‖lexHeadCoefficient f‖*r^f.totalDegree)) ≤
      ENNReal.ofReal (2*f.totalDegree*r) := by
  classical
  induction n with
  | zero =>
    have he := MvPolynomial.eq_C_of_isEmpty f
    have hempty : smallPolynomialValues f (‖lexHeadCoefficient f‖*r^f.totalDegree) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      change ‖MvPolynomial.eval _ f‖ < ‖f.coeff 0‖*r^f.totalDegree at hx
      conv at hx => lhs; rw [he,MvPolynomial.eval_C]
      exact (not_lt_of_ge (by simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hr.le hr' (n := f.totalDegree)) (norm_nonneg (f.coeff 0)))) hx
    simp [hempty]
  | succ n ih =>
    let P := MvPolynomial.finSuccEquiv ℂ n f
    let g := P.leadingCoeff
    let k := P.natDegree
    have hP : P ≠ 0 := fun h => hf ((MvPolynomial.finSuccEquiv ℂ n).injective (h.trans (map_zero _).symm))
    have hg : g ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
    have hlex : lexHeadCoefficient f = lexHeadCoefficient g := rfl
    have hd : g.totalDegree + k ≤ f.totalDegree :=
      MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le f k hg
    have hbad := ih g hg
    let B := smallPolynomialValues g (‖lexHeadCoefficient g‖*r^g.totalDegree)
    have hfiber (y : Fin n → ℝ) (hy : y ∉ B) :
        gaussianReal 0 1 {x : ℝ | consReal x y ∈ smallPolynomialValues f (‖lexHeadCoefficient f‖*r^f.totalDegree)} ≤
          ENNReal.ofReal (2*k*r) := by
      let yc (i : Fin n) : ℂ := y i
      let φ := MvPolynomial.eval yc
      have hl : ‖lexHeadCoefficient g‖*r^g.totalDegree ≤ ‖φ g‖ := le_of_not_gt hy
      have hn : φ g ≠ 0 := norm_pos_iff.mp ((mul_pos (norm_pos_iff.mpr (lexHeadCoefficient_ne_zero g hg)) (pow_pos hr _)).trans_le hl)
      have hthr : ‖lexHeadCoefficient f‖*r^f.totalDegree ≤ ‖φ g‖*r^k := by
        rw [hlex]
        refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr.le hr' hd) (norm_nonneg _)).trans ?_
        rw [pow_add,← mul_assoc]
        exact mul_le_mul_of_nonneg_right hl (pow_nonneg hr.le _)
      exact specialized_fiber_le f y _ r hr.le hn hthr
    have h := gaussian_fibers_le _ (measurable_smallPolynomialValues f _) B
      (measurable_smallPolynomialValues g _) _ hfiber
    refine h.trans ((add_le_add hbad le_rfl).trans ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd' : (g.totalDegree:ℝ)+k ≤ f.totalDegree := by exact_mod_cast hd
    linarith only [mul_le_mul_of_nonneg_right hd' hr.le]

/-- Under independent standard Gaussian coordinates a degree-d polynomial
falls strictly below rᵈ times its lexicographically leading coefficient with
probability at most 2dr. -/
theorem gaussian_mvPolynomial_sublevel {n : ℕ} (f : MvPolynomial (Fin n) ℂ) (hf : f ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {x | ‖MvPolynomial.eval (fun i => (x i : ℂ)) f‖ < ‖lexHeadCoefficient f‖*r^f.totalDegree} ≤
      ENNReal.ofReal (2*f.totalDegree*r) :=
  sublevel_probability_le f hf hr hr'

/-- The recursively selected leading coefficient occurs in the monomial expansion. -/
theorem lexHeadCoefficient_is_coeff {n : ℕ} (f : MvPolynomial (Fin n) ℂ) :
    ∃ m, f.coeff m = lexHeadCoefficient f := by
  induction n with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    let P := MvPolynomial.finSuccEquiv ℂ n f
    obtain ⟨m,hm⟩ := ih P.leadingCoeff
    exact ⟨m.cons P.natDegree,(MvPolynomial.finSuccEquiv_coeff_coeff m f P.natDegree).symm.trans hm⟩

/-- Integer polynomials require no coefficient normalization. Under independent
standard Gaussians the probability of absolute value below rᵈ is at most 2dr. -/
theorem gaussian_integerPolynomial_sublevel {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (hp : p ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {x | ‖MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (x i : ℂ)) p‖ < r^p.totalDegree} ≤
      ENNReal.ofReal (2*p.totalDegree*r) := by
  let ι := Int.castRingHom ℂ
  let f := MvPolynomial.map ι p
  have hinj : Function.Injective ι := Int.cast_injective
  have hf : f ≠ 0 := fun h => hp ((MvPolynomial.map_injective ι hinj) (h.trans (map_zero _).symm))
  have hd : f.totalDegree = p.totalDegree := by
    simp only [f,MvPolynomial.totalDegree,MvPolynomial.support_map_of_injective p hinj]
  obtain ⟨m,hm⟩ := lexHeadCoefficient_is_coeff f
  have he : ((p.coeff m : ℤ) : ℂ) = lexHeadCoefficient f := by
    simpa only [f,ι,MvPolynomial.coeff_map,Int.coe_castRingHom] using hm
  have hn : p.coeff m ≠ 0 := by
    intro h
    exact lexHeadCoefficient_ne_zero f hf (by rw [← he,h,Int.cast_zero])
  have hnorm : 1 ≤ ‖lexHeadCoefficient f‖ := by
    rw [← he,Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hn
  have h := gaussian_mvPolynomial_sublevel f hf hr hr'
  rw [hd] at h
  refine (measure_mono ?_).trans h
  intro x hx
  change ‖MvPolynomial.eval _ f‖ < _
  rw [show f = MvPolynomial.map ι p from rfl,MvPolynomial.eval_map]
  exact hx.trans_le (le_mul_of_one_le_left (pow_nonneg hr.le _) hnorm)

#print axioms gaussian_integerPolynomial_sublevel

#print axioms gaussian_mvPolynomial_sublevel
end
end GaloisForLFunctions.HTGeometry
