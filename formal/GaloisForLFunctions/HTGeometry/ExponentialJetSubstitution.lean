import GaloisForLFunctions.HTGeometry.FamilyInversionJets

/-!
# The jets of an exponential

Every jet of `exp f` is `exp f` times a universal polynomial in the jets of `f`: the exponential
Bell polynomials, generated from `1` by the total jet derivation and multiplication by the first
jet.  The factor `exp f` never disappears, which is exactly why exponentiation is not a jet gauge —
a differential relation among exponentials is a relation whose coefficients are polynomials in the
jets of the exponents but whose terms carry independent exponential monomials.

This file provides the substitution itself, blockwise for a finite family.  It is the algebraic
half of the exponential step; the analytic half is the linear independence of the exponential
monomials, which is Ostrowski's theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The exponential Bell polynomials: `exp f` factored out of the jets of `exp f`. -/
def expJetNum : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (k + 1) => jetTotalDerivation (expJetNum k) + MvPolynomial.X 1 * expJetNum k

@[simp] theorem expJetNum_zero : expJetNum 0 = 1 := rfl

theorem expJetNum_succ (k : ℕ) :
    expJetNum (k + 1) = jetTotalDerivation (expJetNum k) + MvPolynomial.X 1 * expJetNum k := rfl

/-- The exponential Bell polynomials involve only the jets they may. -/
theorem expJetNum_mem_supported (k : ℕ) :
    expJetNum k ∈ MvPolynomial.supported ℂ (Set.Iic k) := by
  induction k with
  | zero =>
      rw [expJetNum_zero]
      exact Subalgebra.one_mem _
  | succ k ih =>
      rw [expJetNum_succ]
      have hmono : MvPolynomial.supported ℂ (Set.Iic k) ≤
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        refine MvPolynomial.supported_mono ?_
        intro j hj
        simp only [Set.mem_Iic] at hj ⊢
        omega
      have hX1 : (MvPolynomial.X 1 : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        rw [MvPolynomial.X_mem_supported]
        simp only [Set.mem_Iic]
        omega
      exact Subalgebra.add_mem _ (jetTotalDerivation_mem_supported ih)
        (Subalgebra.mul_mem _ hX1 (hmono ih))

/-- **The exponential jet formula.**  Every jet of `exp f` is `exp f` times a universal polynomial
in the jets of `f`. -/
theorem iteratedDeriv_exp_eq_expJetNum_mul {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k (fun w => Complex.exp (f w)) z
      = Complex.exp (f z) * MvPolynomial.eval (jetVec f z) (expJetNum k) := by
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, expJetNum_zero]
      simp
  | succ k ih =>
      intro z hz
      have hdf : DifferentiableAt ℂ f z := (hf z hz).differentiableAt (by simp)
      have hdexp : DifferentiableAt ℂ (fun w => Complex.exp (f w)) z :=
        (Complex.differentiableAt_exp).comp z hdf
      have hdnum : DifferentiableAt ℂ
          (fun w => MvPolynomial.eval (jetVec f w) (expJetNum k)) z :=
        differentiableAt_eval_jetVec hU hf hz (expJetNum k)
      have hEq : (fun w => iteratedDeriv k (fun u => Complex.exp (f u)) w)
          =ᶠ[nhds z] fun w =>
            Complex.exp (f w) * MvPolynomial.eval (jetVec f w) (expJetNum k) := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hEq.deriv_eq, deriv_fun_mul hdexp hdnum,
        deriv_eval_jetVec hU hf hz]
      have hdexpval : deriv (fun w => Complex.exp (f w)) z = Complex.exp (f z) * deriv f z :=
        deriv_cexp hdf
      rw [hdexpval, expJetNum_succ]
      have hX1 : MvPolynomial.eval (jetVec f z) (MvPolynomial.X 1) = deriv f z := by
        simp [jetVec, iteratedDeriv_one]
      simp only [map_add, map_mul, hX1]
      ring

/-- The blockwise exponential numerator in the family jet ring. -/
def familyExpJetNum (m n : ℕ) (i : Fin m) (k : ℕ) : MvPolynomial (FamilyJetIndex m n) ℂ :=
  MvPolynomial.rename (familyJetRename m n i) (expJetNum k)

/-- **The jets of an exponential family.**  Every jet of `exp (f i)` is `exp (f i)` times the
blockwise exponential numerator evaluated on the jets of the family. -/
theorem familyJetVec_exp_apply {m n : ℕ} {U : Set ℂ} (hU : IsOpen U) {f : Fin m → ℂ → ℂ}
    (hf : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (f i) w) {z : ℂ} (hz : z ∈ U) (i : Fin m)
    (k : Fin (n + 1)) :
    familyJetVec (n := n) (fun i w => Complex.exp (f i w)) z (Sum.inr (i, k))
      = Complex.exp (f i z)
        * MvPolynomial.eval (familyJetVec (n := n) f z) (familyExpJetNum m n i (k : ℕ)) := by
  have hjet : familyJetVec (n := n) (fun i w => Complex.exp (f i w)) z (Sum.inr (i, k))
      = iteratedDeriv (k : ℕ) (fun w => Complex.exp (f i w)) z := rfl
  rw [hjet, iteratedDeriv_exp_eq_expJetNum_mul hU (hf i) (k : ℕ) z hz, familyExpJetNum,
    eval_rename_familyJetRename (Nat.lt_succ_iff.mp k.2) i (expJetNum_mem_supported (k : ℕ)) f z]

/-- **Triangularity of the exponential Bell polynomials.**  `expJetNum (k+1)` is the top jet plus a
polynomial in the lower jets, so the exponential jet substitution can be inverted one jet at a
time. -/
theorem expJetNum_sub_X_mem_supported (k : ℕ) :
    expJetNum (k + 1) - MvPolynomial.X (k + 1) ∈ MvPolynomial.supported ℂ (Set.Iic k) := by
  induction k with
  | zero =>
      have hone : expJetNum 1 = MvPolynomial.X 1 := by
        rw [expJetNum_succ, expJetNum_zero, jetTotalDerivation.map_one_eq_zero, mul_one, zero_add]
      rw [hone, sub_self]
      exact Subalgebra.zero_mem _
  | succ k ih =>
      have hmono : ∀ a b : ℕ, a ≤ b → MvPolynomial.supported ℂ (Set.Iic a) ≤
          MvPolynomial.supported ℂ (Set.Iic b) := by
        intro a b hab
        refine MvPolynomial.supported_mono ?_
        intro j hj
        simp only [Set.mem_Iic] at hj ⊢
        omega
      have hsplit : expJetNum (k + 1) = MvPolynomial.X (k + 1)
          + (expJetNum (k + 1) - MvPolynomial.X (k + 1)) := by ring
      have hD : jetTotalDerivation (expJetNum (k + 1))
          = MvPolynomial.X (k + 2)
            + jetTotalDerivation (expJetNum (k + 1) - MvPolynomial.X (k + 1)) := by
        conv_lhs => rw [hsplit]
        rw [map_add, jetTotalDerivation_X]
      have hDlow : jetTotalDerivation (expJetNum (k + 1) - MvPolynomial.X (k + 1))
          ∈ MvPolynomial.supported ℂ (Set.Iic (k + 1)) := jetTotalDerivation_mem_supported ih
      have hX1 : (MvPolynomial.X 1 : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1)) := by
        rw [MvPolynomial.X_mem_supported]
        simp only [Set.mem_Iic]
        omega
      have hprod : MvPolynomial.X 1 * expJetNum (k + 1)
          ∈ MvPolynomial.supported ℂ (Set.Iic (k + 1)) :=
        Subalgebra.mul_mem _ hX1 (expJetNum_mem_supported (k + 1))
      have hval : expJetNum (k + 1 + 1) - MvPolynomial.X (k + 1 + 1)
          = jetTotalDerivation (expJetNum (k + 1) - MvPolynomial.X (k + 1))
            + MvPolynomial.X 1 * expJetNum (k + 1) := by
        rw [expJetNum_succ, hD]
        ring_nf
      rw [hval]
      exact Subalgebra.add_mem _ hDlow hprod

end

end GaloisForLFunctions.HTGeometry
