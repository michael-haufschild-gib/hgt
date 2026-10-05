import GaloisForLFunctions.RHTower.ChiRamanujanWeightedRationalTrace
/-!
# Full Mellin-weighted third-slot valuation shift

The distinguished third-prime shift changes the complete weighted local trace
by exactly three valuation pairs. This leaf retains both complex Mellin weights
and proves the full HasSum and its unconditional actual-prime specialization.
Other shifted slots, rational-source grouping and the growing physical signed
estimate remain separate obligations.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def weightedThirdShift (z x y : ℂ) (v : ℤ × ℤ) : ℂ :=
  complexCoefficient z v.1*complexCoefficient z v.2*
    complexCoefficient z (v.1+v.2+1)*x^v.1*y^v.2

theorem weightedThirdShift_decomposition (z x y : ℂ) (i j : ℤ) :
    weightedThirdShift z x y (i,j) = weightedLocal z x y (i,j) -
      (z/(1-z))^3*x⁻¹*y⁻¹*(complexAtom (-1) i*complexAtom (-1) j) -
      (z/(1-z))*(1+z/(1-z))*
        (x⁻¹*(complexAtom (-1) i*complexAtom 0 j)+
          y⁻¹*(complexAtom 0 i*complexAtom (-1) j)) := by
  by_cases hi : i < -1
  · simp [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom,
      show i ≠ -1 by omega,show ¬0 ≤ i by omega,show i ≠ 0 by omega]
  by_cases hj : j < -1
  · simp [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom,
      show j ≠ -1 by omega,show ¬0 ≤ j by omega,show j ≠ 0 by omega]
  by_cases hi1 : i = -1
  · subst i
    by_cases hj1 : j = -1
    · subst j
      norm_num [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom]
      ring
    by_cases hj0 : j=0
    · subst j
      norm_num [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom]
      ring
    have hjpos : 0 ≤ j := by omega
    have hjs : 0 ≤ -1+j := by omega
    simp [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom,
      hj1,hj0,hjpos,hjs,show -1+j ≠ -1 by omega]
  by_cases hj1 : j = -1
  · subst j
    by_cases hi0 : i=0
    · subst i
      norm_num [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom]
      ring
    have hipos : 0 ≤ i := by omega
    have his : 0 ≤ i + -1 := by omega
    simp [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom,
      hi1,hi0,hipos,his,show i + -1 ≠ -1 by omega]
  have hi0 : 0 ≤ i := by omega
  have hj0 : 0 ≤ j := by omega
  simp [weightedThirdShift,weightedLocal,complexCoefficient,complexAtom,
    hi1,hj1,hi0,hj0,show 0 ≤ i+j by omega,show i+j ≠ -1 by omega,
    show 0 ≤ i+j+1 by omega,show i+j+1 ≠ -1 by omega]

private lemma pair_atom (a b : ℤ) :
    HasSum (fun v : ℤ × ℤ => complexAtom a v.1*complexAtom b v.2) (1 : ℂ) := by
  simpa using (complexAtom_hasSum a).mul (complexAtom_hasSum b)
    (summable_mul_of_summable_norm (complexAtom_hasSum a).summable.norm
      (complexAtom_hasSum b).summable.norm)

theorem weightedThirdShift_hasSum (z : ℂ) {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    HasSum (weightedThirdShift z x y)
      (weightedEuler z x y-(z/(1-z))^3*x⁻¹*y⁻¹-
        (z/(1-z))*(1+z/(1-z))*(x⁻¹+y⁻¹)) := by
  have h := ((weightedLocal_hasSum z hx hy).sub
    ((pair_atom (-1) (-1)).mul_left ((z/(1-z))^3*x⁻¹*y⁻¹))).sub
      ((((pair_atom (-1) 0).mul_left x⁻¹).add
        ((pair_atom 0 (-1)).mul_left y⁻¹)).mul_left ((z/(1-z))*(1+z/(1-z))))
  simp only [mul_one] at h
  exact h.congr_fun (fun v => weightedThirdShift_decomposition z x y v.1 v.2)

theorem primeWeightedThirdShift_hasSum (p : Nat.Primes) (τ υ : ℝ) :
    let z := cubicPrimeBase p 1
    let x := cubicPrimeBase p (1+(τ : ℂ)*Complex.I)
    let y := cubicPrimeBase p (1+(υ : ℂ)*Complex.I)
    HasSum (weightedThirdShift z x y)
      (weightedEuler z x y-(z/(1-z))^3*x⁻¹*y⁻¹-
        (z/(1-z))*(1+z/(1-z))*(x⁻¹+y⁻¹)) := by
  have hnorm (t : ℝ) : ‖cubicPrimeBase p (1+(t : ℂ)*Complex.I)‖ < 1 := by
    rw [norm_cubicPrimeBase]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
    simp
  exact weightedThirdShift_hasSum _ (hnorm τ) (hnorm υ)

end RHTower.BAGTrace
