import GaloisForLFunctions.HTGeometry.CollectiveQuantumFisherCorrelation
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordTwirlRange

/-!
# Exact finite-spin identities behind a discrete time-crystal protocol

This module isolates exact algebraic statements from the finite XXZ-chain protocol of
Formicola--Di Bello--de Candia--De Filippis--Perroni,
*Discrete time crystals in disordered anisotropic Heisenberg chains*, arXiv:2609.04037.

The paper's phase diagram is numerical and is not asserted here.  What is exact is that a global
Pauli-X half turn negates every longitudinal Pauli-Z observable and hence every weighted
longitudinal collective observable, including staggered imbalance.  The module also records the
period-two signal identities, order-parameter extraction, subharmonic frequency ladder, and the
collective-magnetization QFI/correlation formula.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pauli label for the simultaneous X half turn on every site. -/
def globalXPauliLabel (σ : Type*) : σ → Option (Fin 3) :=
  fun _ => some 0

/-- Pauli-Z label supported at one site. -/
def localZPauliLabel
    {σ : Type*} [DecidableEq σ] (i : σ) : σ → Option (Fin 3) :=
  fun j => if j = i then some 2 else none

/-- Pauli-X label supported at one site. -/
def localXPauliLabel
    {σ : Type*} [DecidableEq σ] (i : σ) : σ → Option (Fin 3) :=
  fun j => if j = i then some 0 else none

/-- Pauli-Y label supported at one site. -/
def localYPauliLabel
    {σ : Type*} [DecidableEq σ] (i : σ) : σ → Option (Fin 3) :=
  fun j => if j = i then some 1 else none

/-- Matrix of the phase-free global X kick. -/
def globalXPauliKick
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (globalXPauliLabel σ)

/-- Longitudinal Pauli-Z observable at one site. -/
def localZPauliObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (localZPauliLabel i)

/-- Transverse Pauli-X observable at one site. -/
def localXPauliObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (localXPauliLabel i)

/-- Transverse Pauli-Y observable at one site. -/
def localYPauliObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finitePauliMatrix (localYPauliLabel i)

/-- The phase-free global X kick is an involution. -/
theorem globalXPauliKick_mul_self
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    globalXPauliKick σ * globalXPauliKick σ = 1 := by
  exact finitePauliMatrix_mul_self (globalXPauliLabel σ)

/-- Global X commutes with every local X. -/
theorem finitePauliConjugationSign_globalX_localX
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    finitePauliConjugationSign (globalXPauliLabel σ) (localXPauliLabel i) = 1 := by
  rw [finitePauliConjugationSign]
  apply Finset.prod_eq_one
  intro j _hj
  by_cases hji : j = i
  · subst j
    simp [globalXPauliLabel, localXPauliLabel,
      boolPauliConjugationSign]
  · simp [globalXPauliLabel, localXPauliLabel, hji,
      boolPauliConjugationSign]

/-- Global X has odd conjugation character against every local Y. -/
theorem finitePauliConjugationSign_globalX_localY
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    finitePauliConjugationSign (globalXPauliLabel σ) (localYPauliLabel i) = -1 := by
  rw [finitePauliConjugationSign]
  refine (Finset.prod_eq_single i ?_ ?_).trans ?_
  · intro j _hj hji
    simp [globalXPauliLabel, localYPauliLabel, hji,
      boolPauliConjugationSign]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot
  · simp [globalXPauliLabel, localYPauliLabel,
      boolPauliConjugationSign]

/-- A perfect global X half turn fixes one local transverse X spin. -/
theorem globalXPauliKick_conj_localX
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXPauliKick σ * localXPauliObservable i * globalXPauliKick σ =
      localXPauliObservable i := by
  rw [globalXPauliKick, localXPauliObservable,
    finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localX]
  simp

/-- A perfect global X half turn flips one local transverse Y spin. -/
theorem globalXPauliKick_conj_localY
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXPauliKick σ * localYPauliObservable i * globalXPauliKick σ =
      -localYPauliObservable i := by
  rw [globalXPauliKick, localYPauliObservable,
    finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localY]
  simp

/-- Global X has odd conjugation character against every local Z. -/
theorem finitePauliConjugationSign_globalX_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    finitePauliConjugationSign (globalXPauliLabel σ) (localZPauliLabel i) = -1 := by
  rw [finitePauliConjugationSign]
  refine (Finset.prod_eq_single i ?_ ?_).trans ?_
  · intro j _hj hji
    simp [globalXPauliLabel, localZPauliLabel, hji,
      boolPauliConjugationSign]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot
  · simp [globalXPauliLabel, localZPauliLabel,
      boolPauliConjugationSign]

/-- A perfect global X half turn flips one local longitudinal spin. -/
theorem globalXPauliKick_conj_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXPauliKick σ * localZPauliObservable i * globalXPauliKick σ =
      -localZPauliObservable i := by
  rw [globalXPauliKick, localZPauliObservable,
    finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localZ]
  simp

/-- Conjugation by the involutive global X kick preserves multiplication. -/
theorem globalXPauliKick_conj_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A B : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) :
    globalXPauliKick σ * (A * B) * globalXPauliKick σ =
      (globalXPauliKick σ * A * globalXPauliKick σ) *
        (globalXPauliKick σ * B * globalXPauliKick σ) := by
  calc
    globalXPauliKick σ * (A * B) * globalXPauliKick σ =
        globalXPauliKick σ * A * B * globalXPauliKick σ := by
      simp only [Matrix.mul_assoc]
    _ =
        globalXPauliKick σ * A *
          (globalXPauliKick σ * globalXPauliKick σ) * B *
            globalXPauliKick σ := by
      rw [globalXPauliKick_mul_self]
      simp
    _ = (globalXPauliKick σ * A * globalXPauliKick σ) *
          (globalXPauliKick σ * B * globalXPauliKick σ) := by
      simp only [Matrix.mul_assoc]

/-- The global X kick preserves every two-site XX coupling. -/
theorem globalXPauliKick_conj_localXX
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i j : σ) :
    globalXPauliKick σ *
        (localXPauliObservable i * localXPauliObservable j) *
          globalXPauliKick σ =
      localXPauliObservable i * localXPauliObservable j := by
  rw [globalXPauliKick_conj_mul,
    globalXPauliKick_conj_localX, globalXPauliKick_conj_localX]

/-- The two local sign reversals cancel on every YY coupling. -/
theorem globalXPauliKick_conj_localYY
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i j : σ) :
    globalXPauliKick σ *
        (localYPauliObservable i * localYPauliObservable j) *
          globalXPauliKick σ =
      localYPauliObservable i * localYPauliObservable j := by
  rw [globalXPauliKick_conj_mul,
    globalXPauliKick_conj_localY, globalXPauliKick_conj_localY]
  simp

/-- The two local sign reversals cancel on every ZZ coupling. -/
theorem globalXPauliKick_conj_localZZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i j : σ) :
    globalXPauliKick σ *
        (localZPauliObservable i * localZPauliObservable j) *
          globalXPauliKick σ =
      localZPauliObservable i * localZPauliObservable j := by
  rw [globalXPauliKick_conj_mul,
    globalXPauliKick_conj_localZ, globalXPauliKick_conj_localZ]
  simp

/-- Heisenberg evolution under repeated perfect global X kicks, written recursively to expose
conjugation at every cycle. -/
def globalXKickHeisenbergIterate
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) :
    ℕ → Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ
  | 0 => A
  | n + 1 => globalXPauliKick σ * globalXKickHeisenbergIterate A n *
      globalXPauliKick σ

/-- A local longitudinal spin acquires exactly the alternating character after any number of
perfect kicks. -/
theorem globalXKickHeisenbergIterate_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) (n : ℕ) :
    globalXKickHeisenbergIterate (localZPauliObservable i) n =
      ((((-1 : ℝ) ^ n : ℝ) : ℂ) • localZPauliObservable i) := by
  induction n with
  | zero => simp [globalXKickHeisenbergIterate]
  | succ n ih =>
      rw [globalXKickHeisenbergIterate, ih,
        Matrix.mul_smul, Matrix.smul_mul,
        globalXPauliKick_conj_localZ, pow_succ]
      norm_num [smul_neg, neg_smul]

/-- Arbitrary weighted longitudinal collective observable. -/
def weightedLongitudinalObservable
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ i, c i • localZPauliObservable i

/-- A perfect global X half turn flips every weighted longitudinal collective observable. -/
theorem globalXPauliKick_conj_weightedLongitudinal
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) :
    globalXPauliKick σ * weightedLongitudinalObservable c * globalXPauliKick σ =
      -weightedLongitudinalObservable c := by
  classical
  unfold weightedLongitudinalObservable
  rw [Matrix.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul,
    globalXPauliKick_conj_localZ]
  simp

/-- Every weighted longitudinal observable has the same exact alternating Heisenberg orbit. -/
theorem globalXKickHeisenbergIterate_weightedLongitudinal
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) (n : ℕ) :
    globalXKickHeisenbergIterate (weightedLongitudinalObservable c) n =
      ((((-1 : ℝ) ^ n : ℝ) : ℂ) • weightedLongitudinalObservable c) := by
  induction n with
  | zero => simp [globalXKickHeisenbergIterate]
  | succ n ih =>
      rw [globalXKickHeisenbergIterate, ih,
        Matrix.mul_smul, Matrix.smul_mul,
        globalXPauliKick_conj_weightedLongitudinal, pow_succ]
      norm_num [smul_neg, neg_smul]

/-- Negating all longitudinal coefficients negates the weighted observable. -/
theorem weightedLongitudinalObservable_neg
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (c : σ → ℂ) :
    weightedLongitudinalObservable (fun i => -c i) =
      -weightedLongitudinalObservable c := by
  classical
  simp [weightedLongitudinalObservable]

/-- One anisotropic Heisenberg bond in Pauli normalization. -/
def finiteAnisotropicHeisenbergBond
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Jx Jy Jz : ℂ) (e : σ × σ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  Jx • (localXPauliObservable e.1 * localXPauliObservable e.2) +
    Jy • (localYPauliObservable e.1 * localYPauliObservable e.2) +
      Jz • (localZPauliObservable e.1 * localZPauliObservable e.2)

/-- A global X kick preserves a fully anisotropic Heisenberg bond. -/
theorem globalXPauliKick_conj_finiteAnisotropicHeisenbergBond
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Jx Jy Jz : ℂ) (e : σ × σ) :
    globalXPauliKick σ * finiteAnisotropicHeisenbergBond Jx Jy Jz e *
        globalXPauliKick σ =
      finiteAnisotropicHeisenbergBond Jx Jy Jz e := by
  unfold finiteAnisotropicHeisenbergBond
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, globalXPauliKick_conj_localXX,
    globalXPauliKick_conj_localYY, globalXPauliKick_conj_localZZ]

/-- Arbitrary finite-graph anisotropic Heisenberg exchange. -/
def finiteAnisotropicHeisenbergExchange
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jx Jy Jz : ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ e ∈ edges, finiteAnisotropicHeisenbergBond Jx Jy Jz e

/-- A global X kick preserves anisotropic exchange on every finite interaction graph. -/
theorem globalXPauliKick_conj_finiteAnisotropicHeisenbergExchange
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jx Jy Jz : ℂ) :
    globalXPauliKick σ * finiteAnisotropicHeisenbergExchange edges Jx Jy Jz *
        globalXPauliKick σ =
      finiteAnisotropicHeisenbergExchange edges Jx Jy Jz := by
  classical
  unfold finiteAnisotropicHeisenbergExchange
  rw [Matrix.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _he
  exact globalXPauliKick_conj_finiteAnisotropicHeisenbergBond Jx Jy Jz e

/-- Disordered anisotropic Heisenberg Hamiltonian on an arbitrary finite interaction graph. -/
def finiteDisorderedAnisotropicHeisenbergHamiltonian
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jx Jy Jz : ℂ) (h : σ → ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteAnisotropicHeisenbergExchange edges Jx Jy Jz +
    weightedLongitudinalObservable h

/-- Perfect global X conjugation fixes exchange and reverses the complete disorder field. -/
theorem globalXPauliKick_conj_finiteDisorderedAnisotropicHeisenbergHamiltonian
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jx Jy Jz : ℂ) (h : σ → ℂ) :
    globalXPauliKick σ *
        finiteDisorderedAnisotropicHeisenbergHamiltonian edges Jx Jy Jz h *
          globalXPauliKick σ =
      finiteDisorderedAnisotropicHeisenbergHamiltonian edges Jx Jy Jz
        (fun i => -h i) := by
  unfold finiteDisorderedAnisotropicHeisenbergHamiltonian
  rw [Matrix.mul_add, Matrix.add_mul,
    globalXPauliKick_conj_finiteAnisotropicHeisenbergExchange,
    globalXPauliKick_conj_weightedLongitudinal,
    weightedLongitudinalObservable_neg]

/-- Paper's disordered XXZ chain in Pauli normalization:
`S^a = σ^a/2`, so the transverse and longitudinal exchange coefficients are
`J⊥/4` and `Jz/4`, while the field coefficient is `h/2`. -/
def finiteDisorderedXXZHamiltonian
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteDisorderedAnisotropicHeisenbergHamiltonian edges
    (Jperp / 4) (Jperp / 4) (Jz / 4) (fun i => h i / 2)

/-- The exact XXZ Hamiltonian identity underlying the perfect-pulse spin echo. -/
theorem globalXPauliKick_conj_finiteDisorderedXXZHamiltonian
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) :
    globalXPauliKick σ *
        finiteDisorderedXXZHamiltonian edges Jperp Jz h *
          globalXPauliKick σ =
      finiteDisorderedXXZHamiltonian edges Jperp Jz (fun i => -h i) := by
  unfold finiteDisorderedXXZHamiltonian
  rw [globalXPauliKick_conj_finiteDisorderedAnisotropicHeisenbergHamiltonian]
  congr 2
  funext i
  ring

attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

/-- Conjugation by the global-X involution transports an arbitrary finite matrix exponential. -/
theorem globalXPauliKick_conj_exp
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Matrix (FiniteQubitConfiguration σ)
      (FiniteQubitConfiguration σ) ℂ) :
    globalXPauliKick σ * NormedSpace.exp A * globalXPauliKick σ =
      NormedSpace.exp
        (globalXPauliKick σ * A * globalXPauliKick σ) := by
  let _ : NormedAlgebra ℚ
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :=
    .restrictScalars ℚ ℂ
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
  have hsemiconj : SemiconjBy (globalXPauliKick σ) A
      (globalXPauliKick σ * A * globalXPauliKick σ) := by
    calc
      globalXPauliKick σ * A = globalXPauliKick σ * A * 1 := by simp
      _ = globalXPauliKick σ * A *
          (globalXPauliKick σ * globalXPauliKick σ) := by
        rw [globalXPauliKick_mul_self]
      _ = (globalXPauliKick σ * A * globalXPauliKick σ) *
          globalXPauliKick σ := by
        simp only [Matrix.mul_assoc]
  have hexp := hsemiconj.exp_right
  change globalXPauliKick σ * NormedSpace.exp A =
    NormedSpace.exp
        (globalXPauliKick σ * A * globalXPauliKick σ) *
      globalXPauliKick σ at hexp
  calc
    globalXPauliKick σ * NormedSpace.exp A * globalXPauliKick σ =
        NormedSpace.exp
            (globalXPauliKick σ * A * globalXPauliKick σ) *
          globalXPauliKick σ * globalXPauliKick σ := by
      rw [hexp]
    _ = NormedSpace.exp
        (globalXPauliKick σ * A * globalXPauliKick σ) := by
      rw [Matrix.mul_assoc, globalXPauliKick_mul_self]
      simp

/-- Exact free evolution generated by the disordered XXZ Hamiltonian. -/
def finiteDisorderedXXZFreeEvolution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) (T : ℝ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  NormedSpace.exp
    (((-Complex.I * (T : ℂ)) : ℂ) •
      finiteDisorderedXXZHamiltonian edges Jperp Jz h)

/-- Perfect global X conjugation transports free evolution from disorder `h` to `-h`. -/
theorem globalXPauliKick_conj_finiteDisorderedXXZFreeEvolution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) (T : ℝ) :
    globalXPauliKick σ *
        finiteDisorderedXXZFreeEvolution edges Jperp Jz h T *
          globalXPauliKick σ =
      finiteDisorderedXXZFreeEvolution edges Jperp Jz (fun i => -h i) T := by
  rw [finiteDisorderedXXZFreeEvolution, finiteDisorderedXXZFreeEvolution,
    globalXPauliKick_conj_exp]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul,
    globalXPauliKick_conj_finiteDisorderedXXZHamiltonian]

/-- One-cycle perfect-pulse Floquet propagator, with free evolution followed by global X. -/
def finiteDisorderedXXZPerfectFloquet
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) (T : ℝ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteDisorderedXXZFreeEvolution edges Jperp Jz h T * globalXPauliKick σ

/-- Two perfect-pulse Floquet cycles factor into free evolutions with opposite disorder fields. -/
theorem finiteDisorderedXXZPerfectFloquet_sq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (edges : Finset (σ × σ)) (Jperp Jz : ℂ) (h : σ → ℂ) (T : ℝ) :
    finiteDisorderedXXZPerfectFloquet edges Jperp Jz h T *
        finiteDisorderedXXZPerfectFloquet edges Jperp Jz h T =
      finiteDisorderedXXZFreeEvolution edges Jperp Jz h T *
        finiteDisorderedXXZFreeEvolution edges Jperp Jz (fun i => -h i) T := by
  unfold finiteDisorderedXXZPerfectFloquet
  calc
    (finiteDisorderedXXZFreeEvolution edges Jperp Jz h T * globalXPauliKick σ) *
        (finiteDisorderedXXZFreeEvolution edges Jperp Jz h T * globalXPauliKick σ) =
      finiteDisorderedXXZFreeEvolution edges Jperp Jz h T *
        (globalXPauliKick σ *
          finiteDisorderedXXZFreeEvolution edges Jperp Jz h T *
            globalXPauliKick σ) := by
      simp only [Matrix.mul_assoc]
    _ = finiteDisorderedXXZFreeEvolution edges Jperp Jz h T *
        finiteDisorderedXXZFreeEvolution edges Jperp Jz (fun i => -h i) T := by
      rw [globalXPauliKick_conj_finiteDisorderedXXZFreeEvolution]

/-- Staggered longitudinal imbalance on an `N`-site chain, with totalized normalization at
`N = 0`. -/
def finiteSpinStaggeredImbalance (N : ℕ) :
    Matrix (FiniteQubitConfiguration (Fin N))
      (FiniteQubitConfiguration (Fin N)) ℂ :=
  weightedLongitudinalObservable fun i =>
    (((N : ℝ)⁻¹ * (-1 : ℝ) ^ (i.val + 1) : ℝ) : ℂ)

/-- The ideal global half turn negates staggered imbalance exactly. -/
theorem globalXPauliKick_conj_finiteSpinStaggeredImbalance (N : ℕ) :
    globalXPauliKick (Fin N) * finiteSpinStaggeredImbalance N *
        globalXPauliKick (Fin N) =
      -finiteSpinStaggeredImbalance N := by
  exact globalXPauliKick_conj_weightedLongitudinal _

/-- Repeated ideal kicks make the full staggered imbalance alternate with exact period two. -/
theorem globalXKickHeisenbergIterate_finiteSpinStaggeredImbalance
    (N n : ℕ) :
    globalXKickHeisenbergIterate (finiteSpinStaggeredImbalance N) n =
      ((((-1 : ℝ) ^ n : ℝ) : ℂ) • finiteSpinStaggeredImbalance N) := by
  exact globalXKickHeisenbergIterate_weightedLongitudinal _ n

/-- Strict product-Clifford implementation of the global X half turn. -/
def globalXCliffordHalfTurnGate
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  finiteProductCliffordGate
    (finitePauliHalfTurnCode (globalXPauliLabel σ))

/-- The strict sitewise half-turn pulse carries only the global phase `I^(number of sites)`. -/
theorem finitePauliHalfTurnPhase_globalX
    (σ : Type*) [Fintype σ] :
    finitePauliHalfTurnPhase (globalXPauliLabel σ) =
      Complex.I ^ Fintype.card σ := by
  simp [finitePauliHalfTurnPhase, globalXPauliLabel,
    cliffordPauliHalfTurnPhase]

/-- Exact phase relation between the strict global pulse and phase-free Pauli-X kick. -/
theorem globalXCliffordHalfTurnGate_eq_phase_smul_globalXPauliKick
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    globalXCliffordHalfTurnGate σ =
      (Complex.I ^ Fintype.card σ) • globalXPauliKick σ := by
  rw [globalXCliffordHalfTurnGate,
    finiteProductCliffordGate_pauliHalfTurn,
    finitePauliHalfTurnPhase_globalX]
  rfl

/-- The strict Clifford half-turn implementation flips every local Z after its global phase
cancels against the adjoint. -/
theorem globalXCliffordHalfTurnGate_conj_localZ
    {σ : Type*} [Fintype σ] [DecidableEq σ] (i : σ) :
    globalXCliffordHalfTurnGate σ * localZPauliObservable i *
        (globalXCliffordHalfTurnGate σ)ᴴ =
      -localZPauliObservable i := by
  rw [globalXCliffordHalfTurnGate,
    finiteProductCliffordGate_pauliHalfTurn]
  rw [Matrix.conjTranspose_smul,
    finitePauliMatrix_isHermitian]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  simp only [localZPauliObservable]
  rw [finitePauliMatrix_conj,
    finitePauliConjugationSign_globalX_localZ]
  rw [mul_comm, finitePauliHalfTurnPhase_mul_conj]
  simp

/-- Strict global X half turn flips the full staggered imbalance. -/
theorem globalXCliffordHalfTurnGate_conj_finiteSpinStaggeredImbalance
    (N : ℕ) :
    globalXCliffordHalfTurnGate (Fin N) * finiteSpinStaggeredImbalance N *
        (globalXCliffordHalfTurnGate (Fin N))ᴴ =
      -finiteSpinStaggeredImbalance N := by
  classical
  unfold finiteSpinStaggeredImbalance weightedLongitudinalObservable
  rw [Matrix.mul_sum, Finset.sum_mul]
  simp_rw [Matrix.mul_smul, Matrix.smul_mul,
    globalXCliffordHalfTurnGate_conj_localZ]
  simp

/-- Exact period-doubled scalar response with amplitude `a`. -/
def periodDoubledSignal (a : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * a

@[simp] theorem periodDoubledSignal_zero (a : ℝ) :
    periodDoubledSignal a 0 = a := by
  simp [periodDoubledSignal]

/-- Every cycle reverses an exact period-doubled signal. -/
theorem periodDoubledSignal_succ (a : ℝ) (n : ℕ) :
    periodDoubledSignal a (n + 1) = -periodDoubledSignal a n := by
  rw [periodDoubledSignal, periodDoubledSignal, pow_succ]
  ring

/-- Two cycles restore an exact period-doubled signal. -/
theorem periodDoubledSignal_add_two (a : ℝ) (n : ℕ) :
    periodDoubledSignal a (n + 2) = periodDoubledSignal a n := by
  rw [show n + 2 = (n + 1) + 1 by omega,
    periodDoubledSignal_succ, periodDoubledSignal_succ]
  simp only [neg_neg]

/-- Finite-window DTC indicator, using a manifestly nonempty window of `N + 1` cycles. -/
def finiteDTCIndicator (N : ℕ) (signal : ℕ → ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * signal n

/-- Finite-window localization-memory indicator. -/
def finiteMBLIndicator (N : ℕ) (signal : ℕ → ℝ) : ℝ :=
  ((N + 1 : ℕ) : ℝ)⁻¹ *
    ∑ n ∈ Finset.range (N + 1), |signal n|

/-- At every finite window, subharmonic DTC order is bounded by unsigned memory. -/
theorem abs_finiteDTCIndicator_le_finiteMBLIndicator
    (N : ℕ) (signal : ℕ → ℝ) :
    |finiteDTCIndicator N signal| ≤ finiteMBLIndicator N signal := by
  unfold finiteDTCIndicator finiteMBLIndicator
  have hinv : 0 ≤ (((N + 1 : ℕ) : ℝ))⁻¹ := by positivity
  rw [abs_mul, abs_of_nonneg hinv]
  apply mul_le_mul_of_nonneg_left _ hinv
  calc
    |∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * signal n| ≤
        ∑ n ∈ Finset.range (N + 1), |(-1 : ℝ) ^ n * signal n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.range (N + 1), |signal n| := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [abs_mul, abs_pow]
      simp

/-- DTC demodulation recovers the exact amplitude of a period-doubled signal. -/
theorem finiteDTCIndicator_periodDoubledSignal (N : ℕ) (a : ℝ) :
    finiteDTCIndicator N (periodDoubledSignal a) = a := by
  unfold finiteDTCIndicator periodDoubledSignal
  have hterm : ∀ n : ℕ,
      (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * a) = a := by
    intro n
    rw [← mul_assoc, ← mul_pow]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The memory indicator of an exact period-doubled signal is its absolute amplitude. -/
theorem finiteMBLIndicator_periodDoubledSignal (N : ℕ) (a : ℝ) :
    finiteMBLIndicator N (periodDoubledSignal a) = |a| := by
  unfold finiteMBLIndicator periodDoubledSignal
  have hterm : ∀ n : ℕ, |(-1 : ℝ) ^ n * a| = |a| := by
    intro n
    rw [abs_mul, abs_pow]
    simp
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- Angular drive frequency. -/
def discreteDriveFrequency (T : ℝ) : ℝ :=
  2 * Real.pi / T

/-- Fundamental period-doubled subharmonic frequency. -/
def discreteTimeCrystalFrequency (T : ℝ) : ℝ :=
  Real.pi / T

/-- Period doubling halves the drive frequency, including under Lean's totalized division at
`T = 0`. -/
theorem discreteTimeCrystalFrequency_eq_drive_div_two (T : ℝ) :
    discreteTimeCrystalFrequency T = discreteDriveFrequency T / 2 := by
  unfold discreteTimeCrystalFrequency discreteDriveFrequency
  ring

/-- Odd harmonic ladder of a period-doubled response. -/
def discreteTimeCrystalOddHarmonic (T : ℝ) (m : ℕ) : ℝ :=
  (2 * (m : ℝ) + 1) * Real.pi / T

@[simp] theorem discreteTimeCrystalOddHarmonic_zero (T : ℝ) :
    discreteTimeCrystalOddHarmonic T 0 = discreteTimeCrystalFrequency T := by
  simp [discreteTimeCrystalOddHarmonic, discreteTimeCrystalFrequency]

/-- Adjacent odd harmonics differ by one drive frequency. -/
theorem discreteTimeCrystalOddHarmonic_succ (T : ℝ) (m : ℕ) :
    discreteTimeCrystalOddHarmonic T (m + 1) =
      discreteTimeCrystalOddHarmonic T m + discreteDriveFrequency T := by
  unfold discreteTimeCrystalOddHarmonic discreteDriveFrequency
  push_cast
  ring

/-- Connected longitudinal spin correlation. -/
def longitudinalSpinConnectedCorrelation
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (i j : σ) : ℝ :=
  QuantumAlg.qCov ψ (localZPauliObservable i) (localZPauliObservable j)

/-- Connected two-time autocorrelation from Eq. (11), specialized to perfect global-X kick
evolution. -/
def pureKickLongitudinalConnectedAutocorrelation
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (i : σ) (n : ℕ) : ℝ :=
  QuantumAlg.qCov ψ
    (globalXKickHeisenbergIterate (localZPauliObservable i) n)
    (localZPauliObservable i)

/-- Under the ideal kick, every connected local autocorrelation alternates exactly with its
initial covariance. -/
theorem pureKickLongitudinalConnectedAutocorrelation_eq_periodDoubled
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (i : σ) (n : ℕ) :
    pureKickLongitudinalConnectedAutocorrelation ψ i n =
      periodDoubledSignal
        (longitudinalSpinConnectedCorrelation ψ i i) n := by
  rw [pureKickLongitudinalConnectedAutocorrelation,
    globalXKickHeisenbergIterate_localZ,
    QuantumAlg.qCov_ofReal_smul_left]
  rfl

/-- Consequently the finite-window DTC demodulator returns the exact local connected variance
for every window length. -/
theorem finiteDTCIndicator_pureKickLongitudinalConnectedAutocorrelation
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) (i : σ) (N : ℕ) :
    finiteDTCIndicator N
        (pureKickLongitudinalConnectedAutocorrelation ψ i) =
      longitudinalSpinConnectedCorrelation ψ i i := by
  have hsignal : pureKickLongitudinalConnectedAutocorrelation ψ i =
      periodDoubledSignal (longitudinalSpinConnectedCorrelation ψ i i) := by
    funext n
    exact pureKickLongitudinalConnectedAutocorrelation_eq_periodDoubled ψ i n
  rw [hsignal]
  exact finiteDTCIndicator_periodDoubledSignal N _

/-- Connected two-time autocorrelation of the complete staggered imbalance. -/
def pureKickStaggeredImbalanceConnectedAutocorrelation
    (sites : ℕ) (ψ : FiniteQubitConfiguration (Fin sites) → ℂ)
    (n : ℕ) : ℝ :=
  QuantumAlg.qCov ψ
    (globalXKickHeisenbergIterate (finiteSpinStaggeredImbalance sites) n)
    (finiteSpinStaggeredImbalance sites)

/-- The ideal staggered connected autocorrelation is exactly period doubled. -/
theorem pureKickStaggeredImbalanceConnectedAutocorrelation_eq_periodDoubled
    (sites : ℕ) (ψ : FiniteQubitConfiguration (Fin sites) → ℂ) (n : ℕ) :
    pureKickStaggeredImbalanceConnectedAutocorrelation sites ψ n =
      periodDoubledSignal
        (QuantumAlg.qCov ψ (finiteSpinStaggeredImbalance sites)
          (finiteSpinStaggeredImbalance sites)) n := by
  rw [pureKickStaggeredImbalanceConnectedAutocorrelation,
    globalXKickHeisenbergIterate_finiteSpinStaggeredImbalance,
    QuantumAlg.qCov_ofReal_smul_left]
  rfl

/-- Every finite observation window recovers the full initial staggered connected variance. -/
theorem finiteDTCIndicator_pureKickStaggeredImbalanceConnectedAutocorrelation
    (sites cycles : ℕ)
    (ψ : FiniteQubitConfiguration (Fin sites) → ℂ) :
    finiteDTCIndicator cycles
        (pureKickStaggeredImbalanceConnectedAutocorrelation sites ψ) =
      QuantumAlg.qCov ψ (finiteSpinStaggeredImbalance sites)
        (finiteSpinStaggeredImbalance sites) := by
  have hsignal : pureKickStaggeredImbalanceConnectedAutocorrelation sites ψ =
      periodDoubledSignal
        (QuantumAlg.qCov ψ (finiteSpinStaggeredImbalance sites)
          (finiteSpinStaggeredImbalance sites)) := by
    funext n
    exact pureKickStaggeredImbalanceConnectedAutocorrelation_eq_periodDoubled sites ψ n
  rw [hsignal]
  exact finiteDTCIndicator_periodDoubledSignal cycles _

/-- Uniform-magnetization QFI per spin. -/
def uniformMagnetizationQuantumFisherPerSite
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) : ℝ :=
  finiteHalfCollectiveQuantumFisherPerSite ψ
    (fun i : σ => localZPauliObservable i)

/-- Uniform-magnetization QFI per spin equals normalized sum of longitudinal connected
correlations. -/
theorem uniformMagnetizationQuantumFisherPerSite_eq_correlationSum
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ψ : FiniteQubitConfiguration σ → ℂ) :
    uniformMagnetizationQuantumFisherPerSite ψ =
      (Fintype.card σ : ℝ)⁻¹ *
        ∑ i, ∑ j, longitudinalSpinConnectedCorrelation ψ i j := by
  exact finiteHalfCollectiveQuantumFisherPerSite_eq_correlationSum ψ _

end

end GaloisForLFunctions.HTGeometry
