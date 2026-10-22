import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTwoAtomReflectedBounds

/-!
# Exact scale-polynomial model for the two retained theta atoms

The same derivative polynomial applies to every atom at its actual squared
frequency. The two-atom source and its reflected product become finite
polynomial expressions in q and exp(-3q), with exact original normalization.
-/
open Polynomial
open scoped ContDiff
namespace RHTower
noncomputable section
set_option maxHeartbeats 1500000

/-- Every atom's physical scale has the same logarithmic derivative law. -/
theorem hasDerivAt_thetaCuspSingleAtomReflectionScale (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspSingleAtomReflectionScale n)
      (2*thetaCuspSingleAtomReflectionScale n x) x := by
  unfold thetaCuspSingleAtomReflectionScale
  exact ((((Real.hasDerivAt_exp (2*x)).comp x
    ((hasDerivAt_id x).const_mul 2)).const_mul (Real.pi*(n : ℝ)^(2 : ℕ)))).congr_deriv (by ring)

private def atomProfile (n : ℕ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  Real.exp (x/2-thetaCuspSingleAtomReflectionScale n x)*P.eval (thetaCuspSingleAtomReflectionScale n x)

private theorem hasDerivAt_atomProfile (n : ℕ) (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (atomProfile n P) (atomProfile n (thetaCuspFirstAtomJetStep P) x) x := by
  have hq := hasDerivAt_thetaCuspSingleAtomReflectionScale n x
  have hs := ((hasDerivAt_id x).div_const 2 |>.sub hq).exp
  have hp := (P.hasDerivAt (thetaCuspSingleAtomReflectionScale n x)).comp x hq
  exact (hs.mul hp).congr_deriv (by
    simp only [atomProfile, thetaCuspFirstAtomJetStep, eval_add, eval_sub,
      eval_mul, eval_C, eval_X, id_eq, Function.comp_apply, Pi.sub_apply]
    ring)

private theorem sourceTerm_eq_atomProfile (n : ℕ) :
    (fun x : ℝ => thetaCuspSourceTerm x n) = atomProfile n (thetaCuspFirstAtomJetPolynomial 0) := by
  funext x
  have he : Real.exp (2*x) = Real.exp x^(2 : ℕ) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  simp only [thetaCuspSourceTerm, thetaCuspSeed, atomProfile, thetaCuspFirstAtomJetPolynomial,
    thetaCuspSingleAtomReflectionScale, eval_sub, eval_mul, eval_pow, eval_C, eval_X,
    he, Real.exp_sub, div_eq_mul_inv]
  rw [← Real.exp_neg]
  simp only [mul_pow]
  rw [show -Real.pi*((n : ℝ)^(2 : ℕ)*Real.exp x^(2 : ℕ)) = -(Real.pi*(n : ℝ)^(2 : ℕ)*Real.exp x^(2 : ℕ)) by ring]
  ring

/-- One exact polynomial recurrence gives all derivatives of every literal source atom. -/
theorem iteratedDeriv_thetaCuspAtom_eq_scale_polynomial (n m : ℕ) (x : ℝ) :
    iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y n) x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale n x)*
        (thetaCuspFirstAtomJetPolynomial m).eval (thetaCuspSingleAtomReflectionScale n x) := by
  have hf (m : ℕ) : iteratedDeriv m (fun y : ℝ => thetaCuspSourceTerm y n) =
      atomProfile n (thetaCuspFirstAtomJetPolynomial m) := by
    induction m with
    | zero => exact sourceTerm_eq_atomProfile n
    | succ m ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      exact (hasDerivAt_atomProfile n (thetaCuspFirstAtomJetPolynomial m) y).deriv
  exact congrFun (hf m) x

/-- The second atom is evaluated at exactly four times the first physical scale. -/
theorem thetaCuspSecondAtomScale_eq_four_mul (x : ℝ) :
    thetaCuspSingleAtomReflectionScale 2 x = 4*thetaCuspSingleAtomReflectionScale 1 x := by
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, Nat.cast_ofNat]
  ring

/-- Two-atom source derivative polynomial after extracting the common first Gaussian. -/
def thetaCuspTwoAtomScaleSourceJet (n : ℕ) (q z : ℝ) : ℝ :=
  (thetaCuspFirstAtomJetPolynomial n).eval q+z*(thetaCuspFirstAtomJetPolynomial n).eval (4*q)

/-- Exact common-Gaussian source formula at every derivative order. -/
theorem iteratedDeriv_thetaCuspTwoAtomSource_eq_scale (n : ℕ) (x : ℝ) :
    iteratedDeriv n thetaCuspTwoAtomSource x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        thetaCuspTwoAtomScaleSourceJet n (thetaCuspSingleAtomReflectionScale 1 x)
          (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  have h1 : ContDiffAt ℝ n (fun y : ℝ => thetaCuspSourceTerm y 1) x :=
    (contDiff_thetaCuspSourceAtom 1).contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  have h2 : ContDiffAt ℝ n (fun y : ℝ => thetaCuspSourceTerm y 2) x :=
    (contDiff_thetaCuspSourceAtom 2).contDiffAt.of_le
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  unfold thetaCuspTwoAtomSource
  rw [iteratedDeriv_fun_add h1 h2, iteratedDeriv_thetaCuspAtom_eq_scale_polynomial,
    iteratedDeriv_thetaCuspAtom_eq_scale_polynomial, thetaCuspSecondAtomScale_eq_four_mul]
  have he : Real.exp (x/2-4*thetaCuspSingleAtomReflectionScale 1 x) =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  unfold thetaCuspTwoAtomScaleSourceJet
  ring

/-- Exact reflected two-atom polynomial, including both unequal-atom cross terms. -/
def thetaCuspTwoAtomScaleReflectionJet (n : ℕ) (q z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(-1 : ℝ)^(n-i)*
    thetaCuspTwoAtomScaleSourceJet i q z*thetaCuspTwoAtomScaleSourceJet (n-i) q z

/-- The full retained reflection jet is its exact polynomial times the common Gaussian square. -/
theorem thetaCuspTwoAtomReflectionJet_eq_scale (n : ℕ) (x : ℝ) :
    thetaCuspTwoAtomReflectionJet n x =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)^(2 : ℕ)*
        thetaCuspTwoAtomScaleReflectionJet n (thetaCuspSingleAtomReflectionScale 1 x)
          (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  rw [thetaCuspTwoAtomReflectionJet_eq]
  simp only [iteratedDeriv_thetaCuspTwoAtomSource_eq_scale,
    thetaCuspTwoAtomScaleReflectionJet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Exact normalized two-atom Hankel input in the scale and the relative second Gaussian. -/
theorem thetaCuspTwoAtomScaledEvenJet_eq_scale (k : ℕ) (x : ℝ) :
    thetaCuspTwoAtomScaledEvenJet k x =
      (-1 : ℝ)^k*thetaCuspTwoAtomScaleReflectionJet (2*k)
        (thetaCuspSingleAtomReflectionScale 1 x) (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x))/
      ((thetaCuspFirstAtomJetPolynomial 0).eval (thetaCuspSingleAtomReflectionScale 1 x)^(2 : ℕ)*
        thetaCuspSingleAtomReflectionScale 1 x^k) := by
  have hseed : thetaCuspSourceTerm x 1 =
      Real.exp (x/2-thetaCuspSingleAtomReflectionScale 1 x)*
        (thetaCuspFirstAtomJetPolynomial 0).eval (thetaCuspSingleAtomReflectionScale 1 x) :=
    iteratedDeriv_thetaCuspAtom_eq_scale_polynomial 1 0 x
  unfold thetaCuspTwoAtomScaledEvenJet
  rw [thetaCuspTwoAtomReflectionJet_eq_scale, hseed, mul_pow]
  field_simp [Real.exp_ne_zero]

end
end RHTower
