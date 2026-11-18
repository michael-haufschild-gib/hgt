import GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementPolynomial

/-!
# Global zeta functions of polynomial counts

The Euler product of polynomial point counts factors into integral powers of
Riemann zeta shifts. Its rightmost nontrivial order detects the leading
coefficient.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Filter Topology Finset Complex ZeroForcingCalculus
noncomputable section

/-- Global product of Riemann zeta shifts corresponding to an integral counting polynomial. -/
def countGlobalZeta (P : Polynomial ℤ) (s : ℂ) : ℂ :=
  ∏ j ∈ P.support, riemannZeta (s-j) ^ P.coeff j

/-- Prime evaluation of the signed local factors. -/
def countPrimeZeta (P : Polynomial ℤ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  ∏ j ∈ P.support, ((1-((p:ℕ):ℂ)^(-(s-j)))⁻¹) ^ P.coeff j

private theorem signedPrime_hasProd (s : ℂ) (hs : 1 < s.re) (m : ℤ) :
    HasProd (fun p : Nat.Primes => ((1-((p:ℕ):ℂ)^(-s))⁻¹)^m) ((riemannZeta s)^m) := by
  cases m with
  | ofNat n => simpa only [Int.ofNat_eq_natCast,zpow_natCast] using (riemannZeta_eulerProduct_hasProd hs).pow n
  | negSucc n =>
    simpa only [zpow_negSucc,inv_pow,inv_inv] using (_root_.RHTower.hasProd_one_sub_primeCpow_neg hs).pow (n+1)

/-- Andrusov's local factors converge as a prime product to the shifted-zeta expression
throughout the absolute-convergence half-plane. -/
theorem countGlobalZeta_hasProd (P : Polynomial ℤ) (s : {z : ℂ // (P.natDegree:ℝ)+1 < z.re}) :
    HasProd (countPrimeZeta P s) (countGlobalZeta P s) := by
  let f := fun (j : ℕ) (p : Nat.Primes) => ((1-((p:ℕ):ℂ)^(-(s.val-j)))⁻¹)^P.coeff j
  let g := fun j : ℕ => riemannZeta (s.val-j)^P.coeff j
  have hall (S : Finset ℕ) (hS : S ⊆ P.support) :
      HasProd (fun p => ∏ j ∈ S, f j p) (∏ j ∈ S, g j) := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert j S hj ih =>
      have hdeg : (j:ℝ) ≤ P.natDegree := by
        exact_mod_cast Polynomial.le_natDegree_of_mem_supp j (hS (mem_insert_self _ _))
      have hs : 1 < (s.val-(j:ℂ)).re := by
        simp only [Complex.sub_re,Complex.natCast_re]
        linarith [s.property]
      simpa only [prod_insert hj] using (signedPrime_hasProd _ hs (P.coeff j)).mul
        (ih (fun i hi => hS (mem_insert_of_mem hi)))
  exact hall _ Subset.rfl

private theorem zetaShift_order (j : ℕ) (s : ℂ) :
    MeromorphicAt (fun z : ℂ => riemannZeta (z-j)) s ∧
      meromorphicOrderAt (fun z : ℂ => riemannZeta (z-j)) s = meromorphicOrderAt riemannZeta (s-j) := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z-j) s := analyticAt_id.sub analyticAt_const
  have hshift : HasDerivAt (fun z : ℂ => z-j) 1 s := (hasDerivAt_id s).sub_const (j:ℂ)
  have hd : deriv (fun z : ℂ => z-j) s ≠ 0 := hshift.deriv.trans_ne one_ne_zero
  exact ⟨(meromorphicAt_comp_iff_of_deriv_ne_zero ha hd).mpr (meromorphicAt_riemannZeta _),
    meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) ha hd⟩

/-- Every divisor multiplicity of the global count zeta is the signed
sum of the translated Riemann zeta multiplicities. -/
theorem countGlobalZeta_order (P : Polynomial ℤ) (s : ℂ) :
    meromorphicOrderAt (countGlobalZeta P) s =
      ∑ j ∈ P.support, (P.coeff j : WithTop ℤ) * meromorphicOrderAt riemannZeta (s-j) := by
  unfold countGlobalZeta
  rw [meromorphicOrderAt_fun_prod (f := fun (j : ℕ) (z : ℂ) => riemannZeta (z-j)^P.coeff j)
    (fun j (_ : j ∈ P.support) => ((zetaShift_order j s).1).fun_zpow (P.coeff j))]
  refine sum_congr rfl fun j _ => ?_
  change meromorphicOrderAt ((fun z : ℂ => riemannZeta (z-j))^P.coeff j) s = _
  rw [meromorphicOrderAt_zpow (zetaShift_order j s).1,(zetaShift_order j s).2]

/-- At the rightmost possible singularity the order is minus the leading
coefficient. Lower shifts are analytic units there. -/
theorem countGlobalZeta_leading_order (P : Polynomial ℤ) :
    meromorphicOrderAt (countGlobalZeta P) ((P.natDegree:ℂ)+1) = ((-P.leadingCoeff:ℤ):WithTop ℤ) := by
  rw [countGlobalZeta_order,sum_eq_single P.natDegree]
  · rw [show (P.natDegree:ℂ)+1-P.natDegree = 1 by ring,meromorphicOrderAt_riemannZeta_one,
      Polynomial.coeff_natDegree]
    exact_mod_cast mul_neg_one P.leadingCoeff
  · intro j hj hne
    have hj' : j < P.natDegree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp j hj) hne
    have hh : 1 < ((P.natDegree:ℂ)+1-j).re := by
      simp only [Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re]
      linarith only [show (j:ℝ) < P.natDegree by exact_mod_cast hj']
    have hn : (P.natDegree:ℂ)+1-j ≠ 1 := fun h => by rw [h,Complex.one_re] at hh; exact hh.false
    rw [meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (ZeroForcingCalculus.analyticAt_riemannZeta hn)
      (riemannZeta_ne_zero_of_one_le_re hh.le),mul_zero]
  · intro h
    have hz := Polynomial.notMem_support_iff.mp h
    rw [hz]
    simp

/-- Distinct integer shifts are multiplicatively independent: a finite signed
product which is identically one has every exponent zero. -/
theorem countGlobalZeta_eq_one_iff (P : Polynomial ℤ) : countGlobalZeta P = 1 ↔ P = 0 := by
  constructor
  · intro h
    have he := countGlobalZeta_leading_order P
    have horder : meromorphicOrderAt (1 : ℂ → ℂ) ((P.natDegree:ℂ)+1) = 0 :=
      meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (f := fun _ => (1:ℂ)) analyticAt_const one_ne_zero
    rw [h,horder] at he
    have hz : -P.leadingCoeff = 0 := by exact_mod_cast he.symm
    exact Polynomial.leadingCoeff_eq_zero.mp (neg_eq_zero.mp hz)
  · rintro rfl
    funext z
    simp [countGlobalZeta]

end
end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
