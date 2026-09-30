import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentDefect
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Polynomial coercivity of the actual theta score gaps

The signed coefficient quadratic form equals a sum of actual atom integrals
with the polynomial square retained inside each integral. The pointwise score
defect then yields a strict lower bound from the fixed first theta atom.
All moments use the raw normalization `R_j = 2 ∫ x^(2j) Φ(x) dx`.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators


namespace RHTower
noncomputable section

/-- The exact defect of the actual theta raw moment score recurrence. -/
def thetaCuspRawScoreGap (j : ℕ) : ℝ :=
  (32 * (j : ℝ) + 17) * thetaCuspRawEvenMoment j -
    303 * thetaCuspRawEvenMoment (j + 1)

/-- A finite coefficient quadratic form of raw theta score gaps. -/
def thetaCuspFiniteScoreGap {N : ℕ} (a : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * thetaCuspRawScoreGap ((i : ℕ) + (j : ℕ))

/-- Polynomial form of the actual raw score-gap Hankel family. -/
def thetaCuspPolynomialScoreGap (P : ℝ[X]) : ℝ :=
  thetaCuspFiniteScoreGap (fun i : Fin (P.natDegree + 1) => P.coeff i)

private def atomScoreGap (j n : ℕ) : ℝ :=
  (32 * (j : ℝ) + 17) * thetaCuspAtomRawEvenMoment j n -
    303 * thetaCuspAtomRawEvenMoment (j + 1) n

private def scoreDefect (n : ℕ) (x : ℝ) : ℝ :=
  1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2

private def coefficientObservable {N : ℕ} (a : Fin N → ℝ) (x : ℝ) : ℝ :=
  ∑ i, a i * x ^ (2 * (i : ℕ))

private theorem coefficientObservable_eq_eval {N : ℕ} (a : Fin N → ℝ) (x : ℝ) :
    coefficientObservable a x = (Polynomial.ofFn N a).eval (x ^ 2) := by
  rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial, coefficientObservable, pow_mul]

private theorem monomial_defect_integrable (j : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) * scoreDefect n x *
      thetaCuspBornWittenAmplitude n x ^ 2) (Ioi 0) := by
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) hn
  have h1 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j + 2) hn
  have hw := integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
    (2 * j + 1) hn
  have heq : (fun x : ℝ => x ^ (2 * j) * scoreDefect n x *
      thetaCuspBornWittenAmplitude n x ^ 2) =
      (fun x => x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ 2) +
        (fun x => 32 * (x ^ (2 * j + 1) * thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x ^ 2)) -
        (fun x => 303 * (x ^ (2 * j + 2) * thetaCuspBornWittenAmplitude n x ^ 2)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, scoreDefect, pow_add]
    ring
  rw [heq]
  exact (h0.add (hw.const_mul 32)).sub (h1.const_mul 303)

private theorem monomial_square_integrable (j : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) * (x - 1) ^ 2 *
      thetaCuspBornWittenAmplitude n x ^ 2) (Ioi 0) := by
  have h0 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) hn
  have h1 := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j + 2) hn
  have ho := integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j + 1) hn
  have heq : (fun x : ℝ => x ^ (2 * j) * (x - 1) ^ 2 *
      thetaCuspBornWittenAmplitude n x ^ 2) =
      (fun x => x ^ (2 * j + 2) * thetaCuspBornWittenAmplitude n x ^ 2) -
        (fun x => 2 * (x ^ (2 * j + 1) * thetaCuspBornWittenAmplitude n x ^ 2)) +
        (fun x => x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ 2) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, pow_add]
    ring
  rw [heq]
  exact (h1.sub (ho.const_mul 2)).add h0

private theorem square_expansion {N : ℕ} (a : Fin N → ℝ) (g : ℝ → ℝ) :
    (fun x => coefficientObservable a x ^ 2 * g x) =
      fun x => ∑ i, ∑ j, (a i * a j) * (x ^ (2 * ((i : ℕ) + (j : ℕ))) * g x) := by
  funext x
  simp only [coefficientObservable, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_add, pow_add]
  ring

private theorem square_integrable {N : ℕ} (a : Fin N → ℝ) (g : ℝ → ℝ)
    (hg : ∀ j : ℕ, IntegrableOn (fun x : ℝ => x ^ (2 * j) * g x) (Ioi 0)) :
    IntegrableOn (fun x : ℝ => coefficientObservable a x ^ 2 * g x) (Ioi 0) := by
  rw [square_expansion]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hg ((i : ℕ) + (j : ℕ))).const_mul (a i * a j)

private theorem atomScoreGap_eq_integral (j : ℕ) {n : ℕ} (hn : 0 < n) :
    atomScoreGap j n = 2 * Real.pi *
      ∫ x : ℝ in Ioi 0, x ^ (2 * j) * scoreDefect n x *
        thetaCuspBornWittenAmplitude n x ^ 2 := by
  unfold atomScoreGap
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
  unfold scoreDefect
  rw [← thetaCuspMorseBornMoment_scoreGap_eq_integral j hn]
  ring

private theorem atom_quadratic_eq_integral {N : ℕ} (a : Fin N → ℝ) (n : ℕ) :
    (∑ i, ∑ j, a i * a j * atomScoreGap ((i : ℕ) + (j : ℕ)) n) =
      2 * Real.pi * ∫ x : ℝ in Ioi 0,
        coefficientObservable a x ^ 2 * scoreDefect n x *
          thetaCuspBornWittenAmplitude n x ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [atomScoreGap, thetaCuspBornWittenAmplitude, thetaCuspMorseGroundState,
      thetaCuspMorseZeroMode]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have heq : (fun x : ℝ => coefficientObservable a x ^ 2 * scoreDefect n x *
      thetaCuspBornWittenAmplitude n x ^ 2) =
      fun x => ∑ i, ∑ j, (a i * a j) *
        (x ^ (2 * ((i : ℕ) + (j : ℕ))) * scoreDefect n x *
          thetaCuspBornWittenAmplitude n x ^ 2) := by
    simpa only [mul_assoc] using square_expansion a
      (fun x => scoreDefect n x * thetaCuspBornWittenAmplitude n x ^ 2)
  rw [heq, integral_finsetSum _ (fun (i : Fin N) _ =>
    integrable_finsetSum _ fun (j : Fin N) _ =>
      (monomial_defect_integrable ((i : ℕ) + (j : ℕ)) hnpos).const_mul (a i * a j)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun (j : Fin N) _ =>
    (monomial_defect_integrable ((i : ℕ) + (j : ℕ)) hnpos).const_mul (a i * a j)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, atomScoreGap_eq_integral _ hnpos]
  ring

private theorem atomRawEvenMoment_summable (j : ℕ) :
    Summable (thetaCuspAtomRawEvenMoment j) := by
  by_contra h
  have hz := tsum_eq_zero_of_not_summable h
  have heq := thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment j
  have hp := thetaCuspRawEvenMoment_pos j
  linarith

private theorem atomScoreGap_summable (j : ℕ) : Summable (atomScoreGap j) := by
  exact ((atomRawEvenMoment_summable j).mul_left (32 * (j : ℝ) + 17)).sub
    ((atomRawEvenMoment_summable (j + 1)).mul_left 303)

private theorem atomScoreGap_tsum (j : ℕ) :
    (∑' n, atomScoreGap j n) = thetaCuspRawScoreGap j := by
  unfold atomScoreGap thetaCuspRawScoreGap
  rw [Summable.tsum_sub ((atomRawEvenMoment_summable j).mul_left _)
    ((atomRawEvenMoment_summable (j + 1)).mul_left _),
    tsum_mul_left, tsum_mul_left, ← thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment,
    ← thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment]

private theorem atom_quadratic_summable {N : ℕ} (a : Fin N → ℝ) :
    Summable (fun n => ∑ i, ∑ j,
      a i * a j * atomScoreGap ((i : ℕ) + (j : ℕ)) n) := by
  exact summable_sum fun i _ => summable_sum fun j _ =>
    (atomScoreGap_summable _).mul_left (a i * a j)

private theorem atom_quadratic_tsum {N : ℕ} (a : Fin N → ℝ) :
    (∑' n, ∑ i, ∑ j, a i * a j * atomScoreGap ((i : ℕ) + (j : ℕ)) n) =
      thetaCuspFiniteScoreGap a := by
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ =>
    (atomScoreGap_summable _).mul_left (a i * a j))]
  simp_rw [Summable.tsum_finsetSum (fun j _ =>
    (atomScoreGap_summable _).mul_left _), tsum_mul_left, atomScoreGap_tsum]
  rfl

/-- Exact atom expansion of every finite signed coefficient quadratic form. -/
theorem thetaCuspFiniteScoreGap_eq_tsum_atomDefect {N : ℕ} (a : Fin N → ℝ) :
    thetaCuspFiniteScoreGap a =
      2 * Real.pi * ∑' n : ℕ, ∫ x : ℝ in Ioi 0,
        (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 *
          (1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2) *
          thetaCuspBornWittenAmplitude n x ^ 2 := by
  rw [← atom_quadratic_tsum a]
  simp_rw [atom_quadratic_eq_integral]
  rw [tsum_mul_left]
  rfl

private theorem observable_defect_integrable {N : ℕ} (a : Fin N → ℝ)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => coefficientObservable a x ^ 2 * scoreDefect n x *
      thetaCuspBornWittenAmplitude n x ^ 2) (Ioi 0) := by
  simpa only [mul_assoc] using square_integrable a
    (fun x => scoreDefect n x * thetaCuspBornWittenAmplitude n x ^ 2)
    (fun j => by simpa only [mul_assoc] using monomial_defect_integrable j hn)

private theorem observable_square_integrable {N : ℕ} (a : Fin N → ℝ)
    {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun x : ℝ => coefficientObservable a x ^ 2 * (x - 1) ^ 2 *
      thetaCuspBornWittenAmplitude n x ^ 2) (Ioi 0) := by
  simpa only [mul_assoc] using square_integrable a
    (fun x => (x - 1) ^ 2 * thetaCuspBornWittenAmplitude n x ^ 2)
    (fun j => by simpa only [mul_assoc] using monomial_square_integrable j hn)

private theorem atom_quadratic_ge_square {N : ℕ} (a : Fin N → ℝ)
    {n : ℕ} (hn : 0 < n) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      coefficientObservable a x ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude n x ^ 2) ≤
      ∑ i, ∑ j, a i * a j * atomScoreGap ((i : ℕ) + (j : ℕ)) n := by
  rw [atom_quadratic_eq_integral]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (observable_square_integrable a hn)
    (observable_defect_integrable a hn)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hs := thetaCuspBornWitten_scoreDefect_ge_square hn hx.le
  change (x - 1) ^ 2 ≤ scoreDefect n x at hs
  have hw : 0 ≤ coefficientObservable a x ^ 2 *
      thetaCuspBornWittenAmplitude n x ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hs hw

private theorem atom_quadratic_nonneg {N : ℕ} (a : Fin N → ℝ) (n : ℕ) :
    0 ≤ ∑ i, ∑ j, a i * a j * atomScoreGap ((i : ℕ) + (j : ℕ)) n := by
  cases n with
  | zero => simp [atomScoreGap]
  | succ n =>
      apply le_trans _ (atom_quadratic_ge_square a (Nat.succ_pos n))
      apply mul_nonneg (by positivity)
      apply integral_nonneg
      intro x
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

/-- The complete finite score-gap form retains the actual first theta atom's square. -/
theorem thetaCuspFiniteScoreGap_ge_firstAtomSquare {N : ℕ} (a : Fin N → ℝ) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      (∑ i, a i * x ^ (2 * (i : ℕ))) ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude 1 x ^ 2) ≤ thetaCuspFiniteScoreGap a := by
  have hfirst := (atom_quadratic_summable a).le_tsum 1
    (fun n _ => atom_quadratic_nonneg a n)
  rw [atom_quadratic_tsum] at hfirst
  exact (atom_quadratic_ge_square a (by norm_num : 0 < 1)).trans hfirst

private theorem polynomial_coefficientObservable (P : ℝ[X]) (x : ℝ) :
    coefficientObservable (fun i : Fin (P.natDegree + 1) => P.coeff i) x =
      P.eval (x ^ 2) := by
  rw [Polynomial.eval_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  simp only [coefficientObservable, pow_mul]

/-- Explicit finite signed coefficient quadratic form; no coefficient signs are assumed. -/
theorem thetaCuspPolynomialScoreGap_eq_coeff_sum (P : ℝ[X]) :
    thetaCuspPolynomialScoreGap P =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        ∑ j ∈ Finset.range (P.natDegree + 1),
          P.coeff i * P.coeff j * thetaCuspRawScoreGap (i + j) := by
  unfold thetaCuspPolynomialScoreGap thetaCuspFiniteScoreGap
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    ∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff i * P.coeff j * thetaCuspRawScoreGap (i + j)) (P.natDegree + 1)]
  apply Finset.sum_congr rfl
  intro i _
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    P.coeff i * P.coeff j * thetaCuspRawScoreGap ((i : ℕ) + j)) (P.natDegree + 1)

/-- Exact actual-source polynomial-square defect expansion with raw normalization `2π`. -/
theorem thetaCuspPolynomialScoreGap_eq_tsum_atomDefect (P : ℝ[X]) :
    thetaCuspPolynomialScoreGap P =
      2 * Real.pi * ∑' n : ℕ, ∫ x : ℝ in Ioi 0,
        P.eval (x ^ 2) ^ 2 *
          (1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2) *
          thetaCuspBornWittenAmplitude n x ^ 2 := by
  have h := thetaCuspFiniteScoreGap_eq_tsum_atomDefect
    (fun i : Fin (P.natDegree + 1) => P.coeff i)
  change thetaCuspPolynomialScoreGap P = 2 * Real.pi * ∑' n : ℕ,
    ∫ x : ℝ in Ioi 0,
      coefficientObservable (fun i : Fin (P.natDegree + 1) => P.coeff i) x ^ 2 *
        (1 + 32 * x * thetaCuspBornWittenSuperpotential n x - 303 * x ^ 2) *
          thetaCuspBornWittenAmplitude n x ^ 2 at h
  simpa only [polynomial_coefficientObservable] using h

/-- Coercivity against the genuine fixed first-atom density, at every polynomial degree. -/
theorem thetaCuspPolynomialScoreGap_ge_firstAtomSquare (P : ℝ[X]) :
    2 * Real.pi * (∫ x : ℝ in Ioi 0,
      P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 *
        thetaCuspBornWittenAmplitude 1 x ^ 2) ≤ thetaCuspPolynomialScoreGap P := by
  have h := thetaCuspFiniteScoreGap_ge_firstAtomSquare
    (fun i : Fin (P.natDegree + 1) => P.coeff i)
  change 2 * Real.pi * (∫ x : ℝ in Ioi 0,
      coefficientObservable (fun i : Fin (P.natDegree + 1) => P.coeff i) x ^ 2 *
        (x - 1) ^ 2 * thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
      thetaCuspPolynomialScoreGap P at h
  simpa only [polynomial_coefficientObservable] using h

/-- A nonzero polynomial has strictly positive first-atom square mass. -/
theorem integral_thetaCuspFirstAtom_polynomialSquare_pos {P : ℝ[X]} (hP : P ≠ 0) :
    0 < ∫ x : ℝ in Ioi 0, P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 *
      thetaCuspBornWittenAmplitude 1 x ^ 2 := by
  let f : ℝ → ℝ := fun x => P.eval (x ^ 2) ^ 2 * (x - 1) ^ 2 *
    thetaCuspBornWittenAmplitude 1 x ^ 2
  have hψ : Continuous (thetaCuspBornWittenAmplitude 1) := by
    unfold thetaCuspBornWittenAmplitude thetaCuspBornWittenWeight
      thetaCuspMorseSuperpotential thetaCuspMorseGroundState
      thetaCuspMorseZeroMode thetaCuspMorseScale
    fun_prop
  have hfcont : Continuous f := by
    exact (((P.continuous.comp (continuous_id.pow 2)).pow 2).mul
      ((continuous_id.sub continuous_const).pow 2)).mul (hψ.pow 2)
  have hfint : IntegrableOn f (Ioi 0) := by
    have h := observable_square_integrable
      (fun i : Fin (P.natDegree + 1) => P.coeff i) (by norm_num : 0 < 1)
    simpa only [polynomial_coefficientObservable, f] using h
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := Eventually.of_forall fun x =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  obtain ⟨b, hb⟩ := P.exists_max_root hP
  let x : ℝ := |b| + 3
  have hx : 2 < x := by dsimp [x]; linarith [abs_nonneg b]
  have hx2 : b < x ^ 2 := by
    dsimp [x]
    nlinarith [le_abs_self b, abs_nonneg b, sq_nonneg (|b|)]
  have hp : P.eval (x ^ 2) ≠ 0 := by
    intro hz
    have hr : P.IsRoot (x ^ 2) := hz
    exact (not_le.mpr hx2) (hb _ hr)
  refine ⟨x, ?_, (show 0 < x by linarith)⟩
  change f x ≠ 0
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hp)
    (pow_ne_zero 2 (by linarith : x - 1 ≠ 0)))
    (pow_ne_zero 2 (thetaCuspBornWittenAmplitude_pos (by norm_num : 0 < 1)
      (by linarith : 0 ≤ x)).ne')

/-- Every nonzero polynomial has a strictly positive actual raw score-gap form. -/
theorem thetaCuspPolynomialScoreGap_pos {P : ℝ[X]} (hP : P ≠ 0) :
    0 < thetaCuspPolynomialScoreGap P := by
  exact lt_of_lt_of_le (mul_pos (by positivity)
    (integral_thetaCuspFirstAtom_polynomialSquare_pos hP))
    (thetaCuspPolynomialScoreGap_ge_firstAtomSquare P)

/-- Every nonzero finite coefficient vector has a strictly positive score-gap form. -/
theorem thetaCuspFiniteScoreGap_pos {N : ℕ} {a : Fin N → ℝ} (ha : a ≠ 0) :
    0 < thetaCuspFiniteScoreGap a := by
  have hP : Polynomial.ofFn N a ≠ 0 := by
    intro hz
    apply ha
    apply Polynomial.injective_ofFn N
    rw [hz, Polynomial.ofFn_zero]
  have hfloor := integral_thetaCuspFirstAtom_polynomialSquare_pos hP
  simp only [← coefficientObservable_eq_eval] at hfloor
  exact lt_of_lt_of_le (mul_pos (by positivity) hfloor)
    (thetaCuspFiniteScoreGap_ge_firstAtomSquare a)

/-- Finite raw theta score-gap Hankel matrix. This is not a cumulant Hankel matrix. -/
def thetaCuspRawScoreGapHankelMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => thetaCuspRawScoreGap ((i : ℕ) + (j : ℕ))

/-- Actual source score-gap Hankel matrices are positive definite in every finite size. -/
theorem thetaCuspRawScoreGapHankelMatrix_posDef (N : ℕ) :
    (thetaCuspRawScoreGapHankelMatrix N).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, thetaCuspRawScoreGapHankelMatrix, add_comm]
  · intro a ha
    rw [star_trivial]
    have heq : a ⬝ᵥ (thetaCuspRawScoreGapHankelMatrix N).mulVec a =
        thetaCuspFiniteScoreGap a := by
      simp only [dotProduct, Matrix.mulVec, thetaCuspRawScoreGapHankelMatrix,
        Finset.mul_sum, thetaCuspFiniteScoreGap]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    exact thetaCuspFiniteScoreGap_pos ha

end
end RHTower
