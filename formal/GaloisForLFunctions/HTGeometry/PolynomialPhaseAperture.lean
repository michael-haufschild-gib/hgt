import GaloisForLFunctions.HTGeometry.AutonomousMinimalOrderBudget
import GaloisForLFunctions.HTGeometry.ImageSeparatingPolynomial
import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.TorusDerivationLeibniz
import GaloisForLFunctions.HTGeometry.LastVariableJetLift
import GaloisForLFunctions.HTGeometry.CoordDerivChainRule
import GaloisForLFunctions.HTGeometry.PhaseJetAlgebra
import GaloisForLFunctions.HTGeometry.AlgebraicIndependenceFromDifferentials
import GaloisForLFunctions.HTGeometry.MvLinearIrreducible
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier

open Complex Set Filter Topology Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

def diagonalPolynomialDerivation (omega : d → ℝ) (Q : MvPolynomial d ℂ) :
    MvPolynomial d ℂ :=
  ∑ i, MvPolynomial.C (Complex.I * (omega i : ℂ)) * MvPolynomial.X i *
    MvPolynomial.pderiv i Q

def polynomialPhaseObservable (Q : MvPolynomial d ℂ) : (d → ℂ) → ℂ :=
  fun z ↦ MvPolynomial.eval z Q

omit [DecidableEq d] in
theorem analyticOnNhd_polynomialPhaseObservable (Q : MvPolynomial d ℂ) (U : Set (d → ℂ)) :
    AnalyticOnNhd ℂ (polynomialPhaseObservable Q) U := by
  exact (AnalyticOnNhd.eval_mvPolynomial Q).mono (Set.subset_univ U)

theorem coordDeriv_polynomialPhaseObservable (Q : MvPolynomial d ℂ) (i : d) (z : d → ℂ) :
    coordDeriv (polynomialPhaseObservable Q) i z =
      MvPolynomial.eval z (MvPolynomial.pderiv i Q) := by
  let g : d → (d → ℂ) → ℂ := fun j w ↦ w j
  have hg : ∀ j, AnalyticOnNhd ℂ (g j) Set.univ := by
    intro j
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : d => ℂ) j).analyticOnNhd _
  have h := coordDeriv_eval_mvPolynomial (U := Set.univ) (g := g) hg Q i
    (z := z) (Set.mem_univ z)
  have hcoord : ∀ x, coordDeriv (g x) i z = if x = i then 1 else 0 := by
    intro x
    rw [coordDeriv]
    change (fderiv ℂ ((ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : d => ℂ) x : (d → ℂ) → ℂ)) z) (Pi.single i 1) = _
    rw [ContinuousLinearMap.fderiv, ContinuousLinearMap.proj_apply]
    by_cases hxi : x = i
    · simp [hxi]
    · simp [hxi]
  change coordDeriv (fun w : d → ℂ => MvPolynomial.eval w Q) i z = _
  rw [h]
  simp_rw [hcoord]
  rw [Finset.sum_eq_single i]
  · simp [g]
  · intro x hx hxi
    simp [hxi]
  · simp

theorem torusDerivation_polynomialPhaseObservable (omega : d → ℝ)
    (Q : MvPolynomial d ℂ) :
    torusDerivation omega (polynomialPhaseObservable Q) =
      polynomialPhaseObservable (diagonalPolynomialDerivation omega Q) := by
  funext z
  rw [torusDerivation, polynomialPhaseObservable, diagonalPolynomialDerivation,
    MvPolynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordDeriv_polynomialPhaseObservable, map_mul, map_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem phaseJet_polynomialPhaseObservable (omega : d → ℝ)
    (Q : MvPolynomial d ℂ) (j : ℕ) :
    phaseJet omega (polynomialPhaseObservable Q) j =
      polynomialPhaseObservable ((diagonalPolynomialDerivation omega)^[j] Q) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [phaseJet, Function.iterate_succ_apply', Function.iterate_succ_apply']
      change torusDerivation omega (phaseJet omega (polynomialPhaseObservable Q) j) = _
      rw [ih, torusDerivation_polynomialPhaseObservable]

theorem eval_zero_pderiv_diagonalPolynomialDerivation (omega : d → ℝ)
    (Q : MvPolynomial d ℂ) (i : d) :
    MvPolynomial.eval (0 : d → ℂ)
        (MvPolynomial.pderiv i (diagonalPolynomialDerivation omega Q)) =
      (Complex.I * (omega i : ℂ)) *
        MvPolynomial.eval 0 (MvPolynomial.pderiv i Q) := by
  classical
  rw [diagonalPolynomialDerivation, map_sum, MvPolynomial.eval_sum]
  rw [Finset.sum_eq_single i]
  · simp [Derivation.leibniz]
    ring
  · intro j hj hji
    simp [Derivation.leibniz, hji]
  · simp

theorem eval_zero_pderiv_iterate_diagonalPolynomialDerivation (omega : d → ℝ)
    (Q : MvPolynomial d ℂ) (i : d) (j : ℕ) :
    MvPolynomial.eval (0 : d → ℂ)
        (MvPolynomial.pderiv i ((diagonalPolynomialDerivation omega)^[j] Q)) =
      (Complex.I * (omega i : ℂ)) ^ j *
        MvPolynomial.eval 0 (MvPolynomial.pderiv i Q) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply',
        eval_zero_pderiv_diagonalPolynomialDerivation, ih, pow_succ]
      ring

def originPolynomialJetJacobian {k : ℕ} (omega : Fin k → ℝ)
    (Q : MvPolynomial (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  fun i j ↦ MvPolynomial.eval (0 : Fin k → ℂ)
    (MvPolynomial.pderiv i ((diagonalPolynomialDerivation omega)^[j] Q))

theorem originPolynomialJetJacobian_eq_weightedVandermonde {k : ℕ}
    (omega : Fin k → ℝ) (Q : MvPolynomial (Fin k) ℂ) :
    originPolynomialJetJacobian omega Q =
      Matrix.diagonal (fun i ↦ MvPolynomial.eval (0 : Fin k → ℂ)
        (MvPolynomial.pderiv i Q)) *
        Matrix.vandermonde (fun i ↦ Complex.I * (omega i : ℂ)) := by
  ext i j
  rw [originPolynomialJetJacobian, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, Matrix.vandermonde_apply,
      eval_zero_pderiv_iterate_diagonalPolynomialDerivation]
    ring
  · intro l hl hli
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hli), zero_mul]
  · simp

theorem originPolynomialJetJacobian_det_ne_zero {k : ℕ}
    (omega : Fin k → ℝ) (homega : Function.Injective omega)
    (Q : MvPolynomial (Fin k) ℂ)
    (hlinear : ∀ i, MvPolynomial.eval (0 : Fin k → ℂ)
      (MvPolynomial.pderiv i Q) ≠ 0) :
    (originPolynomialJetJacobian omega Q).det ≠ 0 := by
  rw [originPolynomialJetJacobian_eq_weightedVandermonde, Matrix.det_mul,
    Matrix.det_diagonal]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hlinear i
  · rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    have hcast : (omega i : ℂ) = (omega j : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hij
    apply homega
    exact_mod_cast hcast

theorem symbolicPolynomialJet_algebraicIndependent {k : ℕ}
    (omega : Fin k → ℝ) (homega : Function.Injective omega)
    (Q : MvPolynomial (Fin k) ℂ)
    (hlinear : ∀ i, MvPolynomial.eval (0 : Fin k → ℂ)
      (MvPolynomial.pderiv i Q) ≠ 0) :
    AlgebraicIndependent ℂ
      (fun j : Fin k ↦ (diagonalPolynomialDerivation omega)^[(j : ℕ)] Q) := by
  apply MvPolynomial.algebraicIndependent_of_jacobian_det_ne_zero
    (coordinate := id)
  intro hzero
  apply originPolynomialJetJacobian_det_ne_zero omega homega Q hlinear
  have hmatrix : originPolynomialJetJacobian omega Q =
      (MvPolynomial.polynomialJacobianMinor
        (fun j : Fin k ↦ (diagonalPolynomialDerivation omega)^[(j : ℕ)] Q) id).map
          (MvPolynomial.eval (0 : Fin k → ℂ)) := by
    ext i j
    rfl
  rw [hmatrix]
  change ((MvPolynomial.eval (0 : Fin k → ℂ)).mapMatrix
    (MvPolynomial.polynomialJacobianMinor
      (fun j : Fin k ↦ (diagonalPolynomialDerivation omega)^[(j : ℕ)] Q) id)).det = 0
  rw [← RingHom.map_det, hzero, map_zero]

theorem eval_aeval_polynomialFamily {ι κ : Type*} (z : κ → ℂ)
    (Phi : ι → MvPolynomial κ ℂ) (P : MvPolynomial ι ℂ) :
    MvPolynomial.eval z (MvPolynomial.aeval Phi P) =
      MvPolynomial.eval (fun i ↦ MvPolynomial.eval z (Phi i)) P := by
  change MvPolynomial.eval z (MvPolynomial.bind₁ Phi P) = _
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

def lastToFirstIndexEquiv (n : ℕ) : Fin (n + 1) ≃ Fin (n + 1) where
  toFun := Fin.lastCases 0 Fin.succ
  invFun := Fin.cases (Fin.last n) Fin.castSucc
  left_inv i := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp

@[simp] theorem lastToFirstIndexEquiv_last (n : ℕ) :
    lastToFirstIndexEquiv n (Fin.last n) = 0 := by
  simp [lastToFirstIndexEquiv]

@[simp] theorem lastToFirstIndexEquiv_castSucc {n : ℕ} (i : Fin n) :
    lastToFirstIndexEquiv n i.castSucc = i.succ := by
  simp [lastToFirstIndexEquiv]

theorem finSuccEquiv_rename_lastToFirst_lastVariableJetLift {R : Type*}
    [Field R] {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) R)) :
    MvPolynomial.finSuccEquiv R n
        (MvPolynomial.rename (lastToFirstIndexEquiv n) (lastVariableJetLift P)) = P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [jetLift_add, map_add, map_add, hp, hq]
  | monomial k a =>
      have hrename : MvPolynomial.rename (lastToFirstIndexEquiv n)
          (MvPolynomial.rename Fin.castSucc a) = MvPolynomial.rename Fin.succ a := by
        rw [MvPolynomial.rename_rename]
        have hfun : (lastToFirstIndexEquiv n : Fin (n + 1) → Fin (n + 1)) ∘
            Fin.castSucc = Fin.succ := by
          funext i
          exact lastToFirstIndexEquiv_castSucc i
        rw [hfun]
      rw [jetLift_monomial, map_mul, map_pow, MvPolynomial.rename_X,
        lastToFirstIndexEquiv_last, hrename, map_mul, map_pow,
        MvPolynomial.finSuccEquiv_X_zero, finSuccEquiv_rename_succ,
        Polynomial.C_mul_X_pow_eq_monomial]

theorem lastVariableJetLift_injective {R : Type*} [Field R] {n : ℕ} :
    Function.Injective
      (lastVariableJetLift : Polynomial (MvPolynomial (Fin n) R) →
        MvPolynomial (Fin (n + 1)) R) := by
  intro P Q h
  have h' := congrArg (fun H : MvPolynomial (Fin (n + 1)) R ↦
    MvPolynomial.finSuccEquiv R n
      (MvPolynomial.rename (lastToFirstIndexEquiv n) H)) h
  simpa [finSuccEquiv_rename_lastToFirst_lastVariableJetLift] using h'

theorem lastVariableJetLift_ne_zero {R : Type*} [Field R] {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) R)} (hP : P ≠ 0) :
    lastVariableJetLift P ≠ 0 := by
  intro h
  apply hP
  apply lastVariableJetLift_injective
  simpa [jetLift_zero] using h

theorem polynomialPhaseJetElem_algebraicIndependent {k : ℕ}
    {rho : Fin k → ℝ} (hrho : ∀ i, 0 < rho i)
    (omega : Fin k → ℝ) (homega : Function.Injective omega)
    (Q : MvPolynomial (Fin k) ℂ)
    (hlinear : ∀ i, MvPolynomial.eval (0 : Fin k → ℂ)
      (MvPolynomial.pderiv i Q) ≠ 0) :
    AlgebraicIndependent ℂ
      (fun j : Fin k ↦ phaseJetElem omega
        (analyticOnNhd_polynomialPhaseObservable Q (polyannulus rho)) (j : ℕ)) := by
  rw [algebraicIndependent_phaseJetElem_iff]
  intro P hP
  have hsymbolic := symbolicPolynomialJet_algebraicIndependent omega homega Q hlinear
  rw [algebraicIndependent_iff] at hsymbolic
  apply hsymbolic P
  obtain ⟨z0, hz0⟩ := nonempty_polyannulus hrho
  apply mvPolynomial_eq_zero_of_eqOn_zero_isOpen (z₀ := z0)
    (isOpen_polyannulus rho) hz0
  intro z hz
  have hzP := hP z hz
  rw [eval_aeval_polynomialFamily]
  simpa [phaseJet_polynomialPhaseObservable, polynomialPhaseObservable] using hzP

theorem exists_polynomialPhase_realAutonomousAnnihilator {k : ℕ}
    {rho : Fin k → ℝ} (hrho : ∀ i, 0 < rho i)
    (omega : Fin k → ℝ) (Q : MvPolynomial (Fin k) ℂ) :
    ∃ P : Polynomial (MvPolynomial (Fin k) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator
        (phaseFunction omega (polynomialPhaseObservable Q)) k P := by
  let Phi : Fin (k + 1) → MvPolynomial (Fin k) ℂ :=
    fun j ↦ (diagonalPolynomialDerivation omega)^[(j : ℕ)] Q
  obtain ⟨H, hH, hHsub⟩ := exists_ne_zero_aeval_eq_zero
    (Nat.lt_succ_self k) Phi
  refine ⟨jetUnlift H, jetUnlift_ne_zero hH, ?_⟩
  apply realAutonomousAnnihilator_of_phaseJetEval_eq_zero hrho
    (analyticOnNhd_polynomialPhaseObservable Q (polyannulus rho))
  intro z hz
  let a : Fin (k + 1) → ℂ :=
    fun j ↦ phaseJet omega (polynomialPhaseObservable Q) (j : ℕ) z
  have hlift : phaseJetEval omega (polynomialPhaseObservable Q) (jetUnlift H) z =
      MvPolynomial.eval a H := by
    rw [phaseJetEval]
    change Polynomial.eval₂ (MvPolynomial.eval fun j : Fin k ↦ a j.castSucc)
      (a (Fin.last k)) (jetUnlift H) = MvPolynomial.eval a H
    rw [← eval_jetLift a, lastVariableJetLift_jetUnlift]
  rw [hlift]
  have hzero := congrArg (MvPolynomial.eval z) hHsub
  rw [eval_aeval_polynomialFamily] at hzero
  simpa [Phi, a, phaseJet_polynomialPhaseObservable,
    polynomialPhaseObservable] using hzero

theorem autonomousMinimalOrder_eq_of_phaseJetElem_algebraicIndependent
    {d : Type} [Fintype d] [DecidableEq d]
    {rho omega : d → ℝ} (hrho : ∀ i, 0 < rho i)
    (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus rho))
    (k : ℕ)
    (hjets : AlgebraicIndependent ℂ
      (fun j : Fin k ↦ phaseJetElem omega hF (j : ℕ)))
    (hex : ∃ P : Polynomial (MvPolynomial (Fin k) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) k P) :
    autonomousMinimalOrder (phaseFunction omega F) = k := by
  apply le_antisymm (autonomousMinimalOrder_le hex)
  let m := autonomousMinimalOrder (phaseFunction omega F)
  obtain ⟨P, hP, hPann⟩ :=
    exists_realAutonomousAnnihilator_autonomousMinimalOrder hex
  by_contra hnot
  have hmk : m < k := by omega
  let inc : Fin (m + 1) → Fin k :=
    fun j ↦ ⟨(j : ℕ), lt_of_lt_of_le j.2 (Nat.succ_le_iff.mpr hmk)⟩
  have hinc : Function.Injective inc := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin k ↦ (x : ℕ)) hij
  have hsub : AlgebraicIndependent ℂ
      (fun j : Fin (m + 1) ↦ phaseJetElem omega hF (j : ℕ)) := by
    have := algebraicIndependent_comp_of_injective hjets inc hinc
    simpa [Function.comp_def, inc] using this
  rw [algebraicIndependent_phaseJetElem_iff] at hsub
  have hvan := phaseJetEval_eq_zero_of_realAutonomousAnnihilator
    hrho hindep hF hPann
  have hLiftZero : lastVariableJetLift P = 0 := by
    apply hsub
    intro z hz
    let a : Fin (m + 1) → ℂ := fun j ↦ phaseJet omega F (j : ℕ) z
    have hlift := eval_jetLift a P
    rw [hlift]
    simpa [phaseJetEval, a] using hvan z hz
  apply hP
  apply lastVariableJetLift_injective
  simpa [jetLift_zero] using hLiftZero

theorem autonomousMinimalOrder_polynomialPhase_eq {k : ℕ}
    {rho : Fin k → ℝ} (hrho : ∀ i, 0 < rho i)
    (omega : Fin k → ℝ) (hindep : RationallyIndependentFrequency omega)
    (homega : Function.Injective omega) (Q : MvPolynomial (Fin k) ℂ)
    (hlinear : ∀ i, MvPolynomial.eval (0 : Fin k → ℂ)
      (MvPolynomial.pderiv i Q) ≠ 0) :
    autonomousMinimalOrder
      (phaseFunction omega (polynomialPhaseObservable Q)) = k := by
  apply autonomousMinimalOrder_eq_of_phaseJetElem_algebraicIndependent
    hrho hindep
    (analyticOnNhd_polynomialPhaseObservable Q (polyannulus rho)) k
  · exact polynomialPhaseJetElem_algebraicIndependent
      hrho omega homega Q hlinear
  · exact exists_polynomialPhase_realAutonomousAnnihilator hrho omega Q

def eulerInverseAnchorPolynomial {k : ℕ} (c : Fin k → ℂ) :
    MvPolynomial (Fin k) ℂ :=
  ∏ i, (1 - MvPolynomial.C (c i) * MvPolynomial.X i)

theorem eval_zero_pderiv_eulerInverseAnchorPolynomial {k : ℕ}
    (c : Fin k → ℂ) (i : Fin k) :
    MvPolynomial.eval (0 : Fin k → ℂ)
        (MvPolynomial.pderiv i (eulerInverseAnchorPolynomial c)) = -c i := by
  classical
  have haux : ∀ s : Finset (Fin k),
      MvPolynomial.eval (0 : Fin k → ℂ)
          (MvPolynomial.pderiv i
            (∏ j ∈ s, (1 - MvPolynomial.C (c j) * MvPolynomial.X j))) =
        if i ∈ s then -c i else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Derivation.leibniz]
        simp only [smul_eq_mul]
        rw [map_add, map_mul, map_mul]
        rw [ih]
        by_cases hai : a = i
        · subst a
          simp [ha, Derivation.leibniz]
        · simp [hai, Ne.symm hai, Derivation.leibniz]
  simpa [eulerInverseAnchorPolynomial] using haux Finset.univ

theorem autonomousMinimalOrder_eulerInverseAnchorPhase_eq {k : ℕ}
    {rho : Fin k → ℝ} (hrho : ∀ i, 0 < rho i)
    (omega : Fin k → ℝ) (hindep : RationallyIndependentFrequency omega)
    (homega : Function.Injective omega) (c : Fin k → ℂ)
    (hc : ∀ i, c i ≠ 0) :
    autonomousMinimalOrder
      (phaseFunction omega
        (polynomialPhaseObservable (eulerInverseAnchorPolynomial c))) = k := by
  apply autonomousMinimalOrder_polynomialPhase_eq hrho omega hindep homega
  intro i
  rw [eval_zero_pderiv_eulerInverseAnchorPolynomial]
  exact neg_ne_zero.mpr (hc i)

theorem rationallyIndependentFrequency_of_linearIndependent_int
    {d : Type*} [Fintype d] [DecidableEq d] {omega : d → ℝ}
    (h : LinearIndependent ℤ omega) : RationallyIndependentFrequency omega := by
  intro n hn
  rw [linearIndependent_iff'] at h
  funext i
  apply h Finset.univ n
  · simpa [finiteTorusCharacterDetuning, zsmul_eq_mul] using hn
  · exact Finset.mem_univ i

def finitePrimeAt (S : Finset Nat.Primes) (i : Fin (Fintype.card ↥S)) : Nat.Primes :=
  ((Fintype.equivFin ↥S).symm i).1

def finitePrimeFrequency (S : Finset Nat.Primes) : Fin (Fintype.card ↥S) → ℝ :=
  fun i ↦ -Real.log (((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)

def finitePrimeDamping (S : Finset Nat.Primes) : Fin (Fintype.card ↥S) → ℂ :=
  fun i ↦ ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℂ))⁻¹

theorem finitePrimeAt_injective (S : Finset Nat.Primes) :
    Function.Injective (finitePrimeAt S) := by
  intro i j hij
  apply (Fintype.equivFin ↥S).symm.injective
  exact Subtype.ext hij

theorem finitePrimeFrequency_linearIndependent (S : Finset Nat.Primes) :
    LinearIndependent ℤ (finitePrimeFrequency S) := by
  have hlog : LinearIndependent ℤ
      (fun i : Fin (Fintype.card ↥S) ↦
        Real.log ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ))) :=
    GaloisForLFunctions.logPrime_linearIndependent_int.comp
      (finitePrimeAt S) (finitePrimeAt_injective S)
  have hneg := hlog.units_smul
    (fun _ : Fin (Fintype.card ↥S) ↦ (-1 : ℤˣ))
  have hfun : ((fun _ : Fin (Fintype.card ↥S) ↦ (-1 : ℤˣ)) •
      (fun i : Fin (Fintype.card ↥S) ↦
        Real.log ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)))) =
      finitePrimeFrequency S := by
    funext i
    simp [finitePrimeFrequency, Units.smul_def]
  rw [hfun] at hneg
  exact hneg

theorem finitePrimeFrequency_rationallyIndependent (S : Finset Nat.Primes) :
    RationallyIndependentFrequency (finitePrimeFrequency S) :=
  rationallyIndependentFrequency_of_linearIndependent_int
    (finitePrimeFrequency_linearIndependent S)

theorem finitePrimeFrequency_injective (S : Finset Nat.Primes) :
    Function.Injective (finitePrimeFrequency S) := by
  intro i j hij
  have hlog : Real.log ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) =
      Real.log ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) := neg_inj.mp hij
  have hi0 : 0 < ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) := by
    exact_mod_cast (finitePrimeAt S i).2.pos
  have hj0 : 0 < ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) := by
    exact_mod_cast (finitePrimeAt S j).2.pos
  have hcast : ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) =
      ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) := by
    calc
      ((((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) =
          Real.exp (Real.log (((finitePrimeAt S i : Nat.Primes) : ℕ) : ℝ)) :=
        (Real.exp_log hi0).symm
      _ = Real.exp (Real.log (((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) := by rw [hlog]
      _ = ((((finitePrimeAt S j : Nat.Primes) : ℕ) : ℝ)) := Real.exp_log hj0
  apply finitePrimeAt_injective S
  apply Subtype.ext
  exact_mod_cast hcast

theorem finitePrimeDamping_ne_zero (S : Finset Nat.Primes)
    (i : Fin (Fintype.card ↥S)) : finitePrimeDamping S i ≠ 0 := by
  apply inv_ne_zero
  exact_mod_cast (finitePrimeAt S i).2.ne_zero

theorem autonomousMinimalOrder_finiteEulerInverseAnchor_eq
    (S : Finset Nat.Primes) :
    autonomousMinimalOrder
      (phaseFunction (finitePrimeFrequency S)
        (polynomialPhaseObservable
          (eulerInverseAnchorPolynomial (finitePrimeDamping S)))) =
      Fintype.card ↥S := by
  apply autonomousMinimalOrder_eulerInverseAnchorPhase_eq
    (rho := fun _ ↦ 1) (fun _ ↦ zero_lt_one)
    (finitePrimeFrequency S)
    (finitePrimeFrequency_rationallyIndependent S)
    (finitePrimeFrequency_injective S)
    (finitePrimeDamping S)
    (finitePrimeDamping_ne_zero S)

end
end GaloisForLFunctions.HTGeometry
