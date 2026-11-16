import GaloisForLFunctions.HTGeometry.BirchTateIwasawaEvaluation
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite exceptional specializations of an Iwasawa series

Every nonzero integral p-adic power series is a nonzero scalar times a
distinguished polynomial times a unit. Its zeros in the open unit disc
are therefore exactly the roots of one monic polynomial. The scalar is
constructed from the least coefficient valuation; no primitiveness or
Weierstrass-factorization hypothesis is imposed on the input series.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.IwasawaSpecialization
open PowerSeries

variable (p : ℕ) [Fact p.Prime]

/-- Remove the common p-power from all coefficients, leaving a nonzero residue series. -/
theorem exists_primitive_factor {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ (k : ℕ) (g : PowerSeries ℤ_[p]),
      f = C ((p : ℤ_[p]) ^ k) * g ∧
      g.map (IsLocalRing.residue ℤ_[p]) ≠ 0 := by
  classical
  have hex : ∃ k, ∃ i, coeff i f ≠ 0 ∧ (coeff i f).valuation = k := by
    have hi : ∃ i, coeff i f ≠ 0 := by
      by_contra h
      apply hf
      ext i
      simpa using (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    exact ⟨_, i, hi, rfl⟩
  let k := Nat.find hex
  obtain ⟨i, hi, hik⟩ := Nat.find_spec hex
  have hmin (j : ℕ) (hj : coeff j f ≠ 0) : k ≤ (coeff j f).valuation :=
    Nat.find_min' hex ⟨j, hj, rfl⟩
  let g : PowerSeries ℤ_[p] := mk fun j =>
    if hj : coeff j f = 0 then 0
    else (PadicInt.unitCoeff hj : ℤ_[p]) * (p : ℤ_[p]) ^ ((coeff j f).valuation - k)
  refine ⟨k, g, ?_, ?_⟩
  · ext j
    simp only [coeff_C_mul, g, coeff_mk]
    split_ifs with hj
    · simp [hj]
    · calc
        coeff j f = (PadicInt.unitCoeff hj : ℤ_[p]) *
            (p : ℤ_[p]) ^ (coeff j f).valuation := PadicInt.unitCoeff_spec hj
        _ = (p : ℤ_[p]) ^ k * ((PadicInt.unitCoeff hj : ℤ_[p]) *
            (p : ℤ_[p]) ^ ((coeff j f).valuation - k)) := by
          rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le (hmin j hj)]
  · have hu : IsUnit (coeff i g) := by
      simp only [g, coeff_mk, dif_neg hi, hik, show Nat.find hex = k from rfl,
        Nat.sub_self, pow_zero, mul_one]
      exact Units.isUnit _
    intro hz
    have hc := congrArg (coeff i) hz
    rw [coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff] at hc
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hc

/-- Evaluation agrees with ordinary polynomial evaluation on a finite series. -/
theorem eval_polynomial {x : ℤ_[p]} (hx : ‖x‖ < 1) (P : Polynomial ℤ_[p]) :
    padicIntEval p hx (P : PowerSeries ℤ_[p]) = P.eval x := by
  rw [padicIntEval, PowerSeries.coe_eval₂Hom, eval₂_coe]
  rfl

/-- Every nonzero series has exactly a monic polynomial's zeros on the open unit disc. -/
theorem exists_polynomial_zero_locus {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    ∃ P : Polynomial ℤ_[p], P.Monic ∧
      ∀ (x : ℤ_[p]) (hx : ‖x‖ < 1),
        padicIntEval p hx f = 0 ↔ P.eval x = 0 := by
  obtain ⟨k, g, hfg, hg⟩ := exists_primitive_factor p hf
  obtain ⟨P, u, hP⟩ := g.exists_isWeierstrassFactorization hg
  refine ⟨P, hP.isDistinguishedAt.monic, ?_⟩
  intro x hx
  have hu : padicIntEval p hx u ≠ 0 := (hP.isUnit.map (padicIntEval p hx)).ne_zero
  have hp : (p : ℤ_[p]) ^ k ≠ 0 := pow_ne_zero _ (NeZero.ne _)
  rw [hfg, hP.eq_mul, map_mul, map_mul, padicIntEval_C, eval_polynomial]
  simp only [mul_eq_zero, hp, hu, or_false, false_or]

/-- Exceptional specialization points, with the convergence condition built into membership. -/
def zeroLocus (f : PowerSeries ℤ_[p]) : Set ℤ_[p] :=
  {x | ∃ hx : ‖x‖ < 1, padicIntEval p hx f = 0}

/-- A nonzero Iwasawa series has finitely many exceptional integral specializations. -/
theorem finite_zeroLocus {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    (zeroLocus p f).Finite := by
  obtain ⟨P, hP, hzero⟩ := exists_polynomial_zero_locus p hf
  apply (Polynomial.finite_setOf_isRoot hP.ne_zero).subset
  rintro x ⟨hx, hfx⟩
  exact (hzero x hx).mp hfx

/-- Unconditional dichotomy: the series is zero or its exceptional set is finite. -/
theorem zero_or_finite_specializations (f : PowerSeries ℤ_[p]) :
    f = 0 ∨ (zeroLocus p f).Finite := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (finite_zeroLocus p hf)

/-- Exceptional principal units for the existing Birch--Tate weight-two evaluation. -/
def weightTwoZeroLocus (f : PowerSeries ℤ_[p]) : Set ℤ_[p] :=
  {x | ∃ hx : ‖x - 1‖ < 1, padicIntWeightTwoEval p hx f = 0}

/-- The quadratic weight map still has only finitely many exceptional points. -/
theorem finite_weightTwoZeroLocus {f : PowerSeries ℤ_[p]} (hf : f ≠ 0) :
    (weightTwoZeroLocus p f).Finite := by
  obtain ⟨P, hP, hzero⟩ := exists_polynomial_zero_locus p hf
  let Q := P.comp (Polynomial.X ^ 2 - Polynomial.C (1 : ℤ_[p]))
  have hQ : Q.Monic := hP.comp (Polynomial.monic_X_pow_sub_C 1 (by simp))
    (by simp only [Polynomial.natDegree_X_pow_sub_C]; simp)
  apply (Polynomial.finite_setOf_isRoot hQ.ne_zero).subset
  rintro x ⟨hx, hfx⟩
  have hz := (hzero (x ^ 2 - 1) (norm_sq_sub_one_lt_one p hx)).mp hfx
  simpa [Q, Polynomial.IsRoot, Polynomial.eval_comp] using hz

/-- Unconditional finite-exception statement for weight-two specialization. -/
theorem zero_or_finite_weightTwo_specializations (f : PowerSeries ℤ_[p]) :
    f = 0 ∨ (weightTwoZeroLocus p f).Finite := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (finite_weightTwoZeroLocus p hf)

/-- A matrix over the Iwasawa algebra is formally singular or has only finitely many
singular specializations in the open unit disc. -/
theorem det_zero_or_finite_singular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (PowerSeries ℤ_[p])) :
    M.det = 0 ∨ Set.Finite {x : ℤ_[p] | ∃ hx : ‖x‖ < 1,
      (M.map (padicIntEval p hx)).det = 0} := by
  by_cases hM : M.det = 0
  · exact Or.inl hM
  · right
    apply (finite_zeroLocus p hM).subset
    rintro x ⟨hx, hdet⟩
    refine ⟨hx, ?_⟩
    rw [(padicIntEval p hx).map_det]
    exact hdet

/-- Every positive prime power lies in the convergence disc. -/
theorem norm_prime_pow_lt_one (n : ℕ) : ‖(p : ℤ_[p]) ^ (n + 1)‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) ?_ (Nat.succ_ne_zero n)
  rw [PadicInt.norm_p, inv_lt_one_iff₀]
  right
  exact_mod_cast (Fact.out : p.Prime).one_lt

private theorem prime_pow_injective :
    Function.Injective (fun n : ℕ => (p : ℤ_[p]) ^ (n + 1)) := by
  intro n m h
  have hv := congrArg PadicInt.valuation h
  simpa only [PadicInt.valuation_pow, PadicInt.valuation_p, mul_one, Nat.add_right_cancel_iff]
    using hv

/-- A fixed countable family of arithmetic specializations. -/
def specializationSequence (f : PowerSeries ℤ_[p]) (n : ℕ) : ℤ_[p] :=
  padicIntEval p (norm_prime_pow_lt_one p n) f

/-- The prime-power specializations jointly detect every coefficient of an Iwasawa series. -/
theorem specializationSequence_injective : Function.Injective (specializationSequence p) := by
  intro f g h
  apply sub_eq_zero.mp
  by_contra hfg
  have hf := finite_zeroLocus p hfg
  have hs : Set.range (fun n : ℕ => (p : ℤ_[p]) ^ (n + 1)) ⊆ zeroLocus p (f - g) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨norm_prime_pow_lt_one p n, ?_⟩
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun h n)
  exact hf.not_infinite ((Set.infinite_range_of_injective (prime_pow_injective p)).mono hs)

end GaloisForLFunctions.HTGeometry.IwasawaSpecialization

#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.exists_primitive_factor
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.exists_polynomial_zero_locus
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.zero_or_finite_specializations
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.zero_or_finite_weightTwo_specializations
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.det_zero_or_finite_singular
#print axioms GaloisForLFunctions.HTGeometry.IwasawaSpecialization.specializationSequence_injective

