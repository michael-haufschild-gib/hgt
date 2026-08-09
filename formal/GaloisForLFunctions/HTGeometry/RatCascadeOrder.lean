import GaloisForLFunctions.HTGeometry.RatCascadeLaw
import GaloisForLFunctions.HTGeometry.FieldJetIndependence
import GaloisForLFunctions.HTGeometry.CascadeExactOrderFromSeparation
import GaloisForLFunctions.HTGeometry.CascadeTranscendence

/-!
# The unit-cost law for rational first-order linear cascades

A cascade of transcendental entire maps, each solving a first-order linear equation with **rational**
coefficients, has differential order exactly its length — provided the leading coefficient has
nonnegative degree at infinity, which is exactly the condition under which the equation has a
transcendental entire solution at all.

By Malmquist's theorem this is the whole class of first-order equations solved for the derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

namespace RatAffineFam

variable (R : RatAffineFam) {h : ℕ → ℂ → ℂ}

/-! ## The cleared law of the cascade -/

theorem evalAt_denFac (Y : ℕ → ℂ → ℂ) (z : ℂ) (j : ℕ) :
    evalAt Y z (R.denFac j) = (R.ld j * R.cd j).eval (Y j z) :=
  evalAt_univFactor Y z _ j

theorem evalAt_numFac (Y : ℕ → ℂ → ℂ) (z : ℂ) (j : ℕ) :
    evalAt Y z (R.numFac j)
      = (R.ln j * R.cd j).eval (Y j z) * Y (j + 1) z + (R.cn j * R.ld j).eval (Y j z) := by
  rw [numFac, map_add, map_mul, evalAt_univFactor, evalAt_univFactor, evalAt_X]

theorem differentiable_ratCascade (hd : ∀ k, Differentiable ℂ (h k)) (k : ℕ) :
    Differentiable ℂ (entireCascade h k) := by
  induction k with
  | zero =>
      have hid : entireCascade h 0 = id := rfl
      rw [hid]
      exact differentiable_id
  | succ k ih =>
      have hstate : entireCascade h (k + 1) = fun z => h k (entireCascade h k z) := rfl
      rw [hstate]
      exact fun z => (hd k _).comp z (ih z)

/-- **The cleared product law of the cascade.** -/
theorem prod_denFac_mul_deriv (hd : ∀ k, Differentiable ℂ (h k))
    (hode : ∀ k z, (R.ld k * R.cd k).eval z * deriv (h k) z
      = (R.ln k * R.cd k).eval z * h k z + (R.cn k * R.ld k).eval z) (k : ℕ) (z : ℂ) :
    evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.denFac j)
        * deriv (entireCascade h k) z
      = evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.numFac j) := by
  induction k with
  | zero =>
      have hid : entireCascade h 0 = id := rfl
      rw [Finset.prod_range_zero, Finset.prod_range_zero, map_one, hid]
      simp
  | succ k ih =>
      have hstate : entireCascade h (k + 1) = fun z => h k (entireCascade h k z) := rfl
      have hinner : HasDerivAt (entireCascade h k) (deriv (entireCascade h k) z) z :=
        (differentiable_ratCascade hd k z).hasDerivAt
      have houter : HasDerivAt (h k) (deriv (h k) (entireCascade h k z))
          (entireCascade h k z) := (hd k _).hasDerivAt
      have hcomp : deriv (fun w => h k (entireCascade h k w)) z
          = deriv (h k) (entireCascade h k z) * deriv (entireCascade h k) z :=
        (houter.comp z hinner).deriv
      have hnext : h k (entireCascade h k z) = entireCascade h (k + 1) z := rfl
      rw [Finset.prod_range_succ, Finset.prod_range_succ, map_mul, map_mul, hstate, hcomp,
        R.evalAt_denFac, R.evalAt_numFac]
      rw [show evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.denFac j)
            * (R.ld k * R.cd k).eval (entireCascade h k z)
            * (deriv (h k) (entireCascade h k z) * deriv (entireCascade h k) z)
          = (evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.denFac j)
              * deriv (entireCascade h k) z)
            * ((R.ld k * R.cd k).eval (entireCascade h k z)
              * deriv (h k) (entireCascade h k z)) by ring,
        ih, hode k (entireCascade h k z), hnext]

/-- **The cleared law against the common denominator.** -/
theorem denTot_mul_deriv (hd : ∀ k, Differentiable ℂ (h k))
    (hode : ∀ k z, (R.ld k * R.cd k).eval z * deriv (h k) z
      = (R.ln k * R.cd k).eval z * h k z + (R.cn k * R.ld k).eval z)
    {N k : ℕ} (hk : k ≤ N) (z : ℂ) :
    evalAt (entireCascade h) z (R.denTot N) * deriv (entireCascade h k) z
      = evalAt (entireCascade h) z (R.clearedJet N k) := by
  have hsplit : R.denTot N
      = (∏ j ∈ Finset.range k, R.denFac j) * ∏ j ∈ Finset.Ico k N, R.denFac j := by
    rw [denTot, ← Finset.prod_range_mul_prod_Ico R.denFac hk]
  rw [hsplit, clearedJet, map_mul, map_mul]
  rw [show evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.denFac j)
        * evalAt (entireCascade h) z (∏ j ∈ Finset.Ico k N, R.denFac j)
        * deriv (entireCascade h k) z
      = (evalAt (entireCascade h) z (∏ j ∈ Finset.range k, R.denFac j)
          * deriv (entireCascade h k) z)
        * evalAt (entireCascade h) z (∏ j ∈ Finset.Ico k N, R.denFac j) by ring,
    R.prod_denFac_mul_deriv hd hode k z]

/-! ## The first-order equation of one map -/

theorem pderiv_aeval_X_zero {i : Fin 3} (hi : (0 : Fin 3) ≠ i) (q : Polynomial ℂ) :
    MvPolynomial.pderiv i
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℂ) q) = 0 := by
  induction q using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C]
      exact (MvPolynomial.pderiv i).map_algebraMap a
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, add_zero]
  | monomial n a _ =>
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Derivation.leibniz,
        Derivation.leibniz_pow, MvPolynomial.pderiv_X_of_ne hi]
      rw [(MvPolynomial.pderiv i).map_algebraMap]
      simp

theorem aeval_X_zero_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    (Polynomial.aeval (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℂ) q) ≠ 0 := by
  intro h0
  refine hq (Polynomial.funext fun t => ?_)
  have h := eval_aeval_X_zero (![t, 0, 0] : Fin 3 → ℂ) q
  rw [h0, map_zero] at h
  have hv : (![t, 0, 0] : Fin 3 → ℂ) 0 = t := rfl
  rw [hv] at h
  rw [Polynomial.eval_zero]
  exact h.symm

theorem differentiallyAlgebraicOfOrder_one_rat
    (hode : ∀ k z, (R.ld k * R.cd k).eval z * deriv (h k) z
      = (R.ln k * R.cd k).eval z * h k z + (R.cn k * R.ld k).eval z) (k : ℕ) :
    DifferentiallyAlgebraicOfOrder (h k) 1 := by
  classical
  refine ⟨(Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (R.ld k * R.cd k)) * MvPolynomial.X 2
      - (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (R.ln k * R.cd k)) * MvPolynomial.X 1
      - (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (R.cn k * R.ld k)), ?_, ?_⟩
  · intro h0
    have hz : (R.ld k * R.cd k) ≠ 0 := mul_ne_zero (R.ld_ne_zero k) (R.cd_ne_zero k)
    refine aeval_X_zero_ne_zero hz ?_
    have hd := congrArg (fun P => MvPolynomial.pderiv (2 : Fin 3) P) h0
    simp only [map_sub, Derivation.leibniz, smul_eq_mul,
      pderiv_aeval_X_zero (by decide : (0 : Fin 3) ≠ 2),
      MvPolynomial.pderiv_X_self,
      MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2), map_zero] at hd
    simpa using hd
  · intro z
    have h0 : iteratedDeriv 0 (h k) z = h k z := by simp [iteratedDeriv_zero]
    have h1 : iteratedDeriv 1 (h k) z = deriv (h k) z := by rw [iteratedDeriv_one]
    have hv0 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 0
        = z := rfl
    have hv1 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 1
        = iteratedDeriv 0 (h k) z := rfl
    have hv2 : (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ) 2
        = iteratedDeriv 1 (h k) z := rfl
    have hea : ∀ q : Polynomial ℂ, MvPolynomial.eval
        (Fin.cons z (fun j : Fin 2 => iteratedDeriv (j : ℕ) (h k) z) : Fin 3 → ℂ)
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) q) = q.eval z := by
      intro q
      rw [eval_aeval_X_zero, hv0]
    have hk := hode k z
    simp only [Polynomial.eval_mul] at hk
    simp only [map_sub, map_mul, MvPolynomial.eval_X, hea, hv1, hv2, h0, h1]
    linear_combination hk

/-! ## The capstone -/

/-- **The unit-cost law for a rational first-order linear cascade.**  A cascade of `m+1`
transcendental entire maps, each solving a first-order linear equation with rational coefficients
whose leading coefficient has nonnegative degree at infinity, has differential order exactly
`m+1`. -/
theorem exactDifferentialOrder_ratCascade
    (hent : ∀ k, TranscendentalEntire (h k))
    (hode : ∀ k z, (R.ld k * R.cd k).eval z * deriv (h k) z
      = (R.ln k * R.cd k).eval z * h k z + (R.cn k * R.ld k).eval z)
    (hdeg : ∀ j, (R.ld j).natDegree ≤ (R.ln j).natDegree) (m : ℕ) :
    ExactDifferentialOrder (entireCascade h (m + 1)) (m + 1) := by
  have hd : ∀ k, Differentiable ℂ (h k) := fun k => (hent k).1
  refine ⟨differentiallyAlgebraicOfOrder_entireCascade_of_transcendental' hent
    (fun k _ => R.differentiallyAlgebraicOfOrder_one_rat hode k), ?_⟩
  intro n hn hDA
  have htop : ¬ DifferentiallyAlgebraicOfOrder (entireCascade h (m + 1)) m := by
    refine not_differentiallyAlgebraicOfOrder_of_clearedModel
      (Y := entireCascade h)
      (fun k => differentiable_ratCascade hd k) rfl
      (δ := R.toAffineFam.toPairFam.law)
      (δp := MvPolynomial.mkDerivation ℂ (fun k => R.clearedJet (m + 1) k))
      (Dtot := R.denTot (m + 1))
      (R.denTot_ne_zero (m + 1)) (N := m + 1) (R.denTot_mem_lowPoly (m + 1))
      (fun k hk => by
        rw [MvPolynomial.mkDerivation_X]
        exact R.clearedJet_mem_lowPoly hk)
      (fun k hk z => by
        rw [MvPolynomial.mkDerivation_X]
        exact R.denTot_mul_deriv hd hode hk z)
      (fun k hk => by
        rw [MvPolynomial.mkDerivation_X, PairFam.law_fx]
        exact R.algebraMap_clearedJet hk)
      (fun Q hQ => exists_evalAt_ne_zero_of_transcendental hent hQ)
      ?_
    exact algebraicIndependent_cons_of_output (R.output_det_ne_zero hdeg m)
  exact htop (hDA.mono (by omega))

end RatAffineFam

end GaloisForLFunctions.HTGeometry
