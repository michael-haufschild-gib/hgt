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

/-- The jet numerators of a solution of `E' = f^{(r)} E`, generated from `1` by the total jet
derivation and multiplication by the `r`-th jet. -/
def logJetNum (r : ℕ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (k + 1) => jetTotalDerivation (logJetNum r k) + MvPolynomial.X r * logJetNum r k

@[simp] theorem logJetNum_zero (r : ℕ) : logJetNum r 0 = 1 := rfl

theorem logJetNum_succ (r k : ℕ) :
    logJetNum r (k + 1) = jetTotalDerivation (logJetNum r k) + MvPolynomial.X r * logJetNum r k :=
  rfl

theorem supported_mono_Iic {a b : ℕ} (hab : a ≤ b) :
    MvPolynomial.supported ℂ (Set.Iic a) ≤ MvPolynomial.supported ℂ (Set.Iic b) := by
  refine MvPolynomial.supported_mono ?_
  intro j hj
  simp only [Set.mem_Iic] at hj ⊢
  omega

theorem logJetNum_one (r : ℕ) : logJetNum r 1 = MvPolynomial.X r := by
  rw [logJetNum_succ, logJetNum_zero, jetTotalDerivation.map_one_eq_zero, mul_one, zero_add]

/-- The jet numerators involve only the jets they may. -/
theorem logJetNum_mem_supported (r k : ℕ) :
    logJetNum r k ∈ MvPolynomial.supported ℂ (Set.Iic (k + r - 1)) := by
  induction k with
  | zero =>
      rw [logJetNum_zero]
      exact Subalgebra.one_mem _
  | succ k ih =>
      have hXr : (MvPolynomial.X r : MvPolynomial ℕ ℂ) ∈
          MvPolynomial.supported ℂ (Set.Iic (k + 1 + r - 1)) := by
        rw [MvPolynomial.X_mem_supported]
        simp only [Set.mem_Iic]
        omega
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [logJetNum_one]
        exact hXr
      · rw [logJetNum_succ]
        have hD : jetTotalDerivation (logJetNum r k) ∈
            MvPolynomial.supported ℂ (Set.Iic (k + 1 + r - 1)) :=
          supported_mono_Iic (a := k + r - 1 + 1) (b := k + 1 + r - 1) (by omega)
            (jetTotalDerivation_mem_supported ih)
        exact Subalgebra.add_mem _ hD
          (Subalgebra.mul_mem _ hXr
            (supported_mono_Iic (a := k + r - 1) (b := k + 1 + r - 1) (by omega) ih))

/-- **The jet formula for a logarithmic-derivative equation.**  If `E' = f^{(r)} E` on `U`, then
every jet of `E` is `E` times a universal polynomial in the jets of `f`. -/
theorem iteratedDeriv_eq_logJetNum_mul {f E : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w)
    (hE : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) E w) (r : ℕ)
    (hrel : ∀ w ∈ U, deriv E w = iteratedDeriv r f w * E w) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k E z
      = E z * MvPolynomial.eval (jetVec f z) (logJetNum r k) := by
  induction k with
  | zero =>
      intro z hz
      rw [iteratedDeriv_zero, logJetNum_zero]
      simp
  | succ k ih =>
      intro z hz
      have hdE : DifferentiableAt ℂ E z := (hE z hz).differentiableAt (by simp)
      have hdnum : DifferentiableAt ℂ
          (fun w => MvPolynomial.eval (jetVec f w) (logJetNum r k)) z :=
        differentiableAt_eval_jetVec hU hf hz (logJetNum r k)
      have hEq : (fun w => iteratedDeriv k E w)
          =ᶠ[nhds z] fun w => E w * MvPolynomial.eval (jetVec f w) (logJetNum r k) := by
        filter_upwards [hU.mem_nhds hz] with w hw
        exact ih w hw
      rw [iteratedDeriv_succ, hEq.deriv_eq, deriv_fun_mul hdE hdnum,
        deriv_eval_jetVec hU hf hz, hrel z hz, logJetNum_succ]
      have hXr : MvPolynomial.eval (jetVec f z) (MvPolynomial.X r) = iteratedDeriv r f z := by
        simp [jetVec]
      simp only [map_add, map_mul, hXr]
      ring

/-- The exponential Bell polynomials: `exp f` factored out of the jets of `exp f`. -/
def expJetNum : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (k + 1) => jetTotalDerivation (expJetNum k) + MvPolynomial.X 1 * expJetNum k

@[simp] theorem expJetNum_zero : expJetNum 0 = 1 := rfl

theorem expJetNum_succ (k : ℕ) :
    expJetNum (k + 1) = jetTotalDerivation (expJetNum k) + MvPolynomial.X 1 * expJetNum k := rfl

theorem expJetNum_eq_logJetNum (k : ℕ) : expJetNum k = logJetNum 1 k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [expJetNum_succ, logJetNum_succ, ih]

/-- The exponential Bell polynomials involve only the jets they may. -/
theorem expJetNum_mem_supported (k : ℕ) :
    expJetNum k ∈ MvPolynomial.supported ℂ (Set.Iic k) := by
  have h := logJetNum_mem_supported 1 k
  rw [← expJetNum_eq_logJetNum] at h
  simpa using h

/-- **The exponential jet formula.**  Every jet of `exp f` is `exp f` times a universal polynomial
in the jets of `f`. -/
theorem iteratedDeriv_exp_eq_expJetNum_mul {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f w) (k : ℕ) :
    ∀ z ∈ U, iteratedDeriv k (fun w => Complex.exp (f w)) z
      = Complex.exp (f z) * MvPolynomial.eval (jetVec f z) (expJetNum k) := by
  have hE : ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (fun u : ℂ => Complex.exp (f u)) w := by
    intro w hw
    exact Complex.contDiff_exp.contDiffAt.comp w (hf w hw)
  have hrel : ∀ w ∈ U, deriv (fun u : ℂ => Complex.exp (f u)) w
      = iteratedDeriv 1 f w * Complex.exp (f w) := by
    intro w hw
    rw [deriv_cexp ((hf w hw).differentiableAt (by simp)), iteratedDeriv_one]
    ring
  intro z hz
  rw [expJetNum_eq_logJetNum]
  exact iteratedDeriv_eq_logJetNum_mul hU hf hE 1 hrel k z hz

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
