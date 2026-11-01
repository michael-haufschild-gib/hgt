import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequencyFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.DilationPolynomialPolarization
import GaloisForLFunctions.HTGeometry.ExponentialSeriesSigmaSum

/-! Exact extraction of the highest polynomial degree from prime-atom exponential series.
Only absolute summability is used; no entire-series or global frequency-independence
hypothesis is imposed. -/

open Finset
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPolynomialCoefficients
open AlgebraicPrimeFrequency DilationPolynomialPolarization
noncomputable section
variable {ι : Type*} [Fintype ι]

def monomialAmplitude (b : ι → PrimeAtom → ℂ) (d : ι →₀ ℕ)
    (u : Fin (slotDegree d) → PrimeAtom) : ℂ :=
  ∏ j, b (monomialWord d j) (u j)

theorem summable_norm_monomialAmplitude (b : ι → PrimeAtom → ℂ)
    (hb : ∀ i, Summable fun x => ‖b i x‖) (d : ι →₀ ℕ) :
    Summable fun u => ‖monomialAmplitude b d u‖ :=
  summable_norm_prod_expSeries (slotDegree d) (fun j => b (monomialWord d j))
    (fun j => hb (monomialWord d j))

theorem monomial_expansion (b : ι → PrimeAtom → ℂ)
    (hb : ∀ i, Summable fun x => ‖b i x‖) (d : ι →₀ ℕ) (t : ℝ) :
    (∏ i, expSeriesCarrier (b i) (fun x => -atomFrequency x) t ^ d i) =
      expSeriesCarrier (monomialAmplitude b d) tuplePhase t := by
  rw [← prod_monomialWord d (fun i => expSeriesCarrier (b i) (fun x => -atomFrequency x) t)]
  change (∏ j, expSeriesCarrier (b (monomialWord d j))
    (fun x => -atomFrequency x) t) =
    expSeriesCarrier (fun u : Fin (slotDegree d) → PrimeAtom =>
      ∏ j, b (monomialWord d j) (u j)) (fun u => -∑ j, atomFrequency (u j)) t
  simpa only [sum_neg_distrib] using
    prod_expSeriesCarrier (slotDegree d) (fun j => b (monomialWord d j))
      (fun x => -atomFrequency x) (fun j => hb (monomialWord d j)) t

abbrev PolynomialAtoms (P : MvPolynomial ι ℂ) :=
  (d : P.support) × (Fin (slotDegree d.val) → PrimeAtom)

def polynomialAmplitude (P : MvPolynomial ι ℂ) (b : ι → PrimeAtom → ℂ)
    (x : PolynomialAtoms P) : ℂ := P.coeff x.1.val * monomialAmplitude b x.1.val x.2

def polynomialPhase (P : MvPolynomial ι ℂ) (x : PolynomialAtoms P) : ℝ := tuplePhase x.2

theorem summable_norm_polynomialAmplitude (P : MvPolynomial ι ℂ)
    (b : ι → PrimeAtom → ℂ) (hb : ∀ i, Summable fun x => ‖b i x‖) :
    Summable fun x => ‖polynomialAmplitude P b x‖ := by
  change Summable (fun x : PolynomialAtoms P =>
    ‖P.coeff x.1.val * monomialAmplitude b x.1.val x.2‖)
  apply summable_norm_sigma
    (κ := P.support) (J := fun d : P.support => Fin (slotDegree d.val) → PrimeAtom)
    (b := fun d u => P.coeff d.val * monomialAmplitude b d.val u)
  intro d
  simpa only [norm_mul] using
    (summable_norm_monomialAmplitude b hb d.val).mul_left ‖P.coeff d.val‖

/-- The actual polynomial evaluation is one absolutely convergent exponential series. -/
theorem polynomial_expansion (P : MvPolynomial ι ℂ)
    (b : ι → PrimeAtom → ℂ) (hb : ∀ i, Summable fun x => ‖b i x‖) (t : ℝ) :
    MvPolynomial.eval (fun i => expSeriesCarrier (b i) (fun x => -atomFrequency x) t) P =
      expSeriesCarrier (polynomialAmplitude P b) (polynomialPhase P) t := by
  rw [MvPolynomial.eval_eq']
  simp_rw [monomial_expansion b hb, const_mul_expSeriesCarrier]
  rw [← sum_coe_sort P.support]
  apply sum_expSeriesCarrier
  intro d
  simpa only [norm_mul] using
    (summable_norm_monomialAmplitude b hb d.val).mul_left ‖P.coeff d.val‖

/-- At a top-degree distinct-prime frequency, a monomial contributes its symmetrized row form. -/
theorem monomial_fiber (b : ι → PrimeAtom → ℂ) (d : ι →₀ ℕ) (D : ℕ)
    (hd : slotDegree d ≤ D) (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    fiberAmplitude (monomialAmplitude b d) tuplePhase (tuplePhase v) =
      symmetricDegreePiece D d (fun j i => b i (v j)) := by
  rcases lt_or_eq_of_le hd with hlt | he
  · rw [fiberAmplitude_eq_zero_of_shorter hlt _ v hv]
    simp only [symmetricDegreePiece,degreePiece,dif_neg (ne_of_lt hlt),
      _root_.sum_apply,MultilinearMap.domDomCongr_apply,_root_.zero_apply,sum_const_zero]
  · subst D
    rw [fiberAmplitude_eq_sum_permutations _ v hv]
    simp only [symmetricDegreePiece,_root_.sum_apply,MultilinearMap.domDomCongr_apply,
      degreePiece]
    apply sum_congr rfl
    intro e _
    rfl

/-- The whole top-degree coefficient is the polynomial's symmetric multilinear form. -/
theorem polynomial_fiber (P : MvPolynomial ι ℂ)
    (b : ι → PrimeAtom → ℂ) (hb : ∀ i, Summable fun x => ‖b i x‖)
    (D : ℕ) (hD : ∀ d ∈ P.support, slotDegree d ≤ D)
    (v : Fin D → PrimeAtom) (hv : Function.Injective (fun j => (v j).1)) :
    fiberAmplitude (polynomialAmplitude P b) (polynomialPhase P) (tuplePhase v) =
      polynomialMultilinear P D (fun j i => b i (v j)) := by
  have hsum : ∀ d : P.support, Summable fun u =>
      ‖P.coeff d.val * monomialAmplitude b d.val u‖ := by
    intro d
    simpa only [norm_mul] using
      (summable_norm_monomialAmplitude b hb d.val).mul_left ‖P.coeff d.val‖
  change fiberAmplitude
    (fun x : PolynomialAtoms P => P.coeff x.1.val * monomialAmplitude b x.1.val x.2)
    (fun x : PolynomialAtoms P => tuplePhase x.2) (tuplePhase v) = _
  rw [fiberAmplitude_sigma
    (J := fun d : P.support => Fin (slotDegree d.val) → PrimeAtom)
    (fun d u => P.coeff d.val * monomialAmplitude b d.val u)
    (fun _ u => tuplePhase u) hsum]
  simp_rw [fiberAmplitude_const_mul]
  simp only [polynomialMultilinear,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  rw [← sum_coe_sort P.support]
  apply sum_congr rfl
  intro d _
  rw [monomial_fiber b d.val D (hD d.val d.property) v hv]

/-- A vanishing polynomial relation annihilates its highest-degree form on distinct primes. -/
theorem polynomialMultilinear_eq_zero_on_atoms (P : MvPolynomial ι ℂ)
    (b : ι → PrimeAtom → ℂ) (hb : ∀ i, Summable fun x => ‖b i x‖)
    (D : ℕ) (hD : ∀ d ∈ P.support, slotDegree d ≤ D)
    (hzero : ∀ t, MvPolynomial.eval
      (fun i => expSeriesCarrier (b i) (fun x => -atomFrequency x) t) P = 0)
    (v : Fin D → PrimeAtom) (hv : Function.Injective (fun j => (v j).1)) :
    polynomialMultilinear P D (fun j i => b i (v j)) = 0 := by
  rw [← polynomial_fiber P b hb D hD v hv]
  apply fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero _ _
    (summable_norm_polynomialAmplitude P b hb)
  intro t
  rw [← polynomial_expansion P b hb t]
  exact hzero t

#print axioms monomial_expansion
#print axioms summable_norm_polynomialAmplitude
#print axioms polynomial_expansion
#print axioms monomial_fiber
#print axioms polynomial_fiber
#print axioms polynomialMultilinear_eq_zero_on_atoms
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicDilationPolynomialCoefficients
