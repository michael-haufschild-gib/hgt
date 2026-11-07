import GaloisForLFunctions.HeckeKreinToeplitz.IntegerFamiliesCarryTheWholeIndex
import GaloisForLFunctions.ArithmeticPositiveDuality.TheTwoPrimeSplineOrbitIsABochnerProblemOnTheTorus
import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.TheExplicitSchedulesReachTheIndex
import GaloisForLFunctions.HTGeometry.PSDKernelOperations
import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.RHTower.WeilPaperPacketRealification
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The integer probes of the horizon

Over a curve the probes form a lattice, `y - x π`. Over `ℤ` the lattice is the integer combinations of the translates of one profile by `log n`:

  `f_a = Σ_i a_i B(· - log(i + 1))`,  `a ∈ ℤ^N`,

the Hecke orbit of the cubic spline. The Krein square of a probe is the quadratic form `Q(a) = W(f_a, f_a)`, up to the factor `e^{-τ/2}`.

* **RH is the positivity of the integer probes**: `Q(a) ≥ 0` for every integer vector (`riemannHypothesis_iff_integerProbes`). The Gram matrix is real, so
  a negative direction is a negative real direction, and by density and scaling a negative integer one (`posSemidef_of_integer_nonneg`).
* **The law holds without any input**: `Q` obeys the parallelogram law on the lattice (`integerProbe_parallelogram`), since it is a quadratic form.

This is the opposite position to a fake. On a fake the count is a count and is not quadratic (`TheCountLawOfTheProbes`). On `ℤ` the form is quadratic, and it is not known to
be a count; if it is one, then RH holds (`riemannHypothesis_of_count`). Only a curve has both. So the door of the programme over `ℤ` is exact: exhibit a count equal to
`Q`, a nonnegative quantity defined without the form.
-/

open Complex Finset Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open GaloisForLFunctions.HTGeometry Zeta23

/-! ### Integer positivity of a real matrix -/

/-- A vector of rationals is an integer vector over a common denominator. -/
theorem exists_common_denominator {n : ℕ} (q : Fin n → ℚ) :
    ∃ (D : ℕ) (a : Fin n → ℤ), 0 < D ∧ ∀ i, ((q i : ℚ) : ℝ) * D = a i := by
  refine ⟨∏ i, (q i).den, fun i => (q i).num * ((∏ j, (q j).den) / (q i).den : ℕ),
    Finset.prod_pos fun i _ => (q i).den_pos, fun i => ?_⟩
  obtain ⟨k, hk⟩ : (q i).den ∣ ∏ j, (q j).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  beta_reduce
  rw [hk, Nat.mul_div_cancel_left _ (q i).den_pos]
  have hden : ((q i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_ne_zero
  have hq : ((q i : ℚ) : ℝ) = ((q i).num : ℝ) / (q i).den := by
    exact_mod_cast (Rat.num_div_den (q i)).symm
  push_cast
  rw [hq]
  field_simp

/-- The real quadratic form of a matrix. -/
def realQuad {n : ℕ} (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * x j

theorem continuous_realQuad {n : ℕ} (A : Fin n → Fin n → ℝ) : Continuous (realQuad A) := by
  unfold realQuad
  fun_prop

/-- A real quadratic form nonnegative on integer vectors is nonnegative. -/
theorem realQuad_nonneg_of_integer {n : ℕ} {A : Fin n → Fin n → ℝ}
    (h : ∀ a : Fin n → ℤ, 0 ≤ realQuad A fun i => (a i : ℝ)) (x : Fin n → ℝ) : 0 ≤ realQuad A x := by
  have hdense : DenseRange fun q : Fin n → ℚ => fun i => ((q i : ℚ) : ℝ) :=
    DenseRange.piMap fun _ => Rat.denseRange_cast
  have hclosed : IsClosed {x : Fin n → ℝ | 0 ≤ realQuad A x} :=
    isClosed_le continuous_const (continuous_realQuad A)
  refine hdense.induction_on (p := fun x => 0 ≤ realQuad A x) x hclosed fun q => ?_
  obtain ⟨D, a, hD, ha⟩ := exists_common_denominator q
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hscale : realQuad A (fun i => (a i : ℝ)) = (D : ℝ) ^ 2 * realQuad A fun i => ((q i : ℚ) : ℝ) := by
    unfold realQuad
    simp only [← ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h0 := h a
  rw [hscale] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

/-- **Integer positivity is positivity.** A Hermitian matrix with real entries whose form is nonnegative on integer vectors is positive
semidefinite. -/
theorem posSemidef_of_integer_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hH : M.IsHermitian)
    (hreal : ∀ i j, (M i j).im = 0)
    (h : ∀ a : Fin n → ℤ, 0 ≤ hermQuad M fun i => (a i : ℂ)) : M.PosSemidef := by
  set A : Fin n → Fin n → ℝ := fun i j => (M i j).re with hA
  have hM (i j : Fin n) : M i j = (A i j : ℂ) := by
    apply Complex.ext
    · simp [hA]
    · simp [hreal]
  -- the form of a complex vector is the sum of the forms of its parts
  have hform (c : Fin n → ℂ) : (star c ⬝ᵥ M.mulVec c).re =
      realQuad A (fun i => (c i).re) + realQuad A (fun i => (c i).im) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum, realQuad,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hM]
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hint : ∀ a : Fin n → ℤ, 0 ≤ realQuad A fun i => (a i : ℝ) := by
    intro a
    have h0 := h a
    unfold hermQuad at h0
    rw [hform] at h0
    have e1 : (fun i => ((a i : ℂ)).re) = fun i => (a i : ℝ) := by
      funext i
      simp
    have e2 : realQuad A (fun i => ((a i : ℂ)).im) = 0 := by
      unfold realQuad
      simp
    rw [e1, e2, add_zero] at h0
    exact h0
  refine posSemidef_of_isHermitian_of_re_nonneg hH fun c => ?_
  rw [hform]
  exact add_nonneg (realQuad_nonneg_of_integer hint _) (realQuad_nonneg_of_integer hint _)

/-! ### The lattice of the horizon -/

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx weilGram)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)
open GaloisForLFunctions.HeckeKreinToeplitz

/-- The Gram matrix of the Hecke orbit of the spline on `1, …, N`. -/
def atomGram (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    fun i : Fin N => ArithmeticCastelnuovoSeveri.translate (Real.log ((i : ℝ) + 1)) (cx cubicSpline)

/-- **The Krein square of an integer probe.** -/
def integerProbe (N : ℕ) (a : Fin N → ℤ) : ℝ := hermQuad (atomGram N) fun i => (a i : ℂ)

theorem atomGram_eq (N : ℕ) : atomGram N =
    weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      fun i : Fin N => cx fun u => cubicSpline (u - Real.log ((i : ℝ) + 1)) := rfl

theorem atomGram_isHermitian (N : ℕ) : (atomGram N).IsHermitian := by
  rw [atomGram_eq]
  refine EffectiveArithmeticHodgeTheory.weilGram_cx_isHermitian (fun i => ?_) fun i => ?_
  · exact BiScaleUncertainty.ChebyshevGauge.contDiff_cubicSpline.comp (contDiff_id.sub contDiff_const)
  · exact BiScaleUncertainty.ChebyshevGauge.hasCompactSupport_cubicSpline.comp_homeomorph
      (Homeomorph.subRight (Real.log ((i : ℝ) + 1)))

/-- **The Gram matrix of the orbit is real**: the Weil functional is real on real tests. -/
theorem atomGram_im (N : ℕ) (i j : Fin N) : (atomGram N i j).im = 0 := by
  rw [atomGram_eq]
  unfold weilGram
  have e : EF.weilTest (cx fun u => cubicSpline (u - Real.log ((i : ℝ) + 1)))
      (cx fun u => cubicSpline (u - Real.log ((j : ℝ) + 1))) =
      fun y => (((∫ t, cubicSpline (t - Real.log ((i : ℝ) + 1)) *
        cubicSpline (t - y - Real.log ((j : ℝ) + 1)) : ℝ)) : ℂ) :=
    funext fun y => RHTower.weilTest_ofReal_ofReal_eq _ _ y
  rw [e]
  exact RHTower.WeilWorkPBAP.weilFullFunctional_ofReal_im _ _

/-- **RH is the positivity of the integer probes of the horizon.** -/
theorem riemannHypothesis_iff_integerProbes :
    RiemannHypothesis ↔ ∀ (N : ℕ) (a : Fin N → ℤ), 0 ≤ integerProbe N a := by
  rw [riemannHypothesis_iff_integerAtoms]
  constructor
  · intro h N a
    have hpsd := (ArithmeticPositiveDuality.hermNegIndex_eq_zero_iff_posSemidef'
      (atomGram_isHermitian N)).mp (h N)
    have h0 := hpsd.re_dotProduct_nonneg (fun i => (a i : ℂ))
    exact h0
  · intro h N
    exact (ArithmeticPositiveDuality.hermNegIndex_eq_zero_iff_posSemidef'
      (atomGram_isHermitian N)).mpr
      (posSemidef_of_integer_nonneg (atomGram_isHermitian N) (atomGram_im N) (h N))

/-- **The law holds on the lattice of `ℤ`**: the form is quadratic, whether or not it is positive. -/
theorem integerProbe_parallelogram (N : ℕ) (a b : Fin N → ℤ) :
    integerProbe N (a + b) + integerProbe N (a - b) = 2 * integerProbe N a + 2 * integerProbe N b := by
  unfold integerProbe hermQuad
  have e1 : (fun i => (((a + b) i : ℤ) : ℂ)) = (fun i => (a i : ℂ)) + fun i => (b i : ℂ) := by
    funext i
    simp
  have e2 : (fun i => (((a - b) i : ℤ) : ℂ)) = (fun i => (a i : ℂ)) - fun i => (b i : ℂ) := by
    funext i
    simp
  rw [e1, e2]
  set x : Fin N → ℂ := fun i => (a i : ℂ)
  set y : Fin N → ℂ := fun i => (b i : ℂ)
  rw [star_add, star_sub, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub,
    add_dotProduct, add_dotProduct, sub_dotProduct, sub_dotProduct]
  simp only [Complex.add_re, Complex.sub_re]
  ring

/-- **What a count would do.** If the Krein square of every integer probe is a count, then RH holds. -/
theorem riemannHypothesis_of_count (K : ∀ N, (Fin N → ℤ) → ℕ)
    (h : ∀ N a, integerProbe N a = K N a) : RiemannHypothesis :=
  riemannHypothesis_iff_integerProbes.mpr fun N a => by
    rw [h]
    positivity

end GaloisForLFunctions.ArithmeticScatteringHolography

end
