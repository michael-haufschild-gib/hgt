import GaloisForLFunctions.HTGeometry.FiniteUnitaryAdjointAutocorrelationLaw

/-!
# Energy-matched eigenframe source memory

Instead of squaring every Pauli-transfer entry before aggregation, contract the transfer matrix
against the Hamiltonian coefficient vector first.  Signed product-eigenframe extraction realizes
that contraction as one forward-query mean.  Every conserved coefficient vector then gives its
exact inverse-participation ratio, uniformly in time.
-/

open scoped BigOperators Matrix
open Matrix NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- `ℓ¹` mass of a finite real coefficient vector. -/
def finiteCoefficientL1Mass [Fintype ι] (h : ι → ℝ) : ℝ :=
  ∑ i, |h i|

/-- A nonzero finite coefficient vector has strictly positive `ℓ¹` mass. -/
theorem finiteCoefficientL1Mass_pos [Fintype ι]
    (h : ι → ℝ) (hh : h ≠ 0) :
    0 < finiteCoefficientL1Mass h := by
  obtain ⟨i, hi⟩ : ∃ i, h i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hh
  unfold finiteCoefficientL1Mass
  apply Finset.sum_pos'
  · exact fun j _hj => abs_nonneg (h j)
  · exact ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩

/-- Signed, coefficient-matched product-eigenframe statistic.  Absolute coefficient products,
normalized by `‖h‖₁²`, are the trial probabilities; coefficient signs and the prepared output
eigenvalue are included in the bounded trial outcome. -/
def energyMatchedEigenframeAmplitude [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) : ℝ :=
  (∑ output : ι, ∑ input : ι,
      h output * h input *
        ((∑ b : σ → Bool,
            pauliEigenframeSign (label output) b *
              pauliEigenframeExpectation U (label input) (label output) b) /
          (Fintype.card (σ → Bool) : ℝ))) /
    (finiteCoefficientL1Mass h) ^ (2 : ℕ)

/-- Signed eigenframe extraction turns the physical randomized mean into the coefficient quadratic
form of the exact Pauli-transfer compression. -/
theorem energyMatchedEigenframeAmplitude_eq_transfer [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    energyMatchedEigenframeAmplitude label h U =
      (∑ output : ι, ∑ input : ι,
        h output * h input * dictionaryPauliTransfer label U output input) /
        (finiteCoefficientL1Mass h) ^ (2 : ℕ) := by
  unfold energyMatchedEigenframeAmplitude dictionaryPauliTransfer
  simp_rw [average_pauliEigenframeExpectation_eq_transfer]

/-- A fixed transfer coordinate makes the energy-matched statistic equal exactly to the
coefficient inverse-participation ratio. -/
theorem energyMatchedEigenframeAmplitude_eq_of_fixed [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hfix : dictionaryPauliTransfer label U *ᵥ h = h) :
    energyMatchedEigenframeAmplitude label h U =
      (∑ i, (h i) ^ (2 : ℕ)) / (finiteCoefficientL1Mass h) ^ (2 : ℕ) := by
  rw [energyMatchedEigenframeAmplitude_eq_transfer]
  congr 1
  calc
    (∑ output : ι, ∑ input : ι,
        h output * h input * dictionaryPauliTransfer label U output input) =
        ∑ output : ι, h output *
          (dictionaryPauliTransfer label U *ᵥ h) output := by
            apply Finset.sum_congr rfl
            intro output _houtput
            rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro input _hinput
            ring
    _ = ∑ output : ι, h output * h output := by rw [hfix]
    _ = ∑ output : ι, (h output) ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro output _houtput
      ring

/-- Finite-dimensional Cauchy: the coefficient inverse-participation ratio is at least inverse
support cardinality.  Equality is attained by equal-magnitude coefficients. -/
theorem one_div_card_le_coefficientL2Sq_div_l1Sq
    [Fintype ι] [Nonempty ι] (h : ι → ℝ) (hh : h ≠ 0) :
    1 / (Fintype.card ι : ℝ) ≤
      (∑ i, (h i) ^ (2 : ℕ)) / (finiteCoefficientL1Mass h) ^ (2 : ℕ) := by
  have hl1pos : 0 < finiteCoefficientL1Mass h := finiteCoefficientL1Mass_pos h hh
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι => (1 : ℝ)) (fun j => |h j|)
  have hCS' : (finiteCoefficientL1Mass h) ^ (2 : ℕ) ≤
      (Fintype.card ι : ℝ) * ∑ j, (h j) ^ (2 : ℕ) := by
    simpa [finiteCoefficientL1Mass, sq_abs] using hCS
  apply (div_le_div_iff₀ hcard (sq_pos_of_pos hl1pos)).2
  simpa [mul_comm] using hCS'

/-- Every nonzero fixed transfer coordinate produces an inverse-dictionary one-query mean. -/
theorem energyMatchedEigenframeAmplitude_ge_card_inv_of_fixed
    [Fintype ι] [Nonempty ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ) (hh : h ≠ 0)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (hfix : dictionaryPauliTransfer label U *ᵥ h = h) :
    1 / (Fintype.card ι : ℝ) ≤ energyMatchedEigenframeAmplitude label h U := by
  rw [energyMatchedEigenframeAmplitude_eq_of_fixed label h U hfix]
  exact one_div_card_le_coefficientL2Sq_div_l1Sq h hh

/-- Exact autonomous value for every finite Pauli dictionary containing the Hamiltonian support. -/
theorem autonomous_energyMatchedEigenframeAmplitude_eq
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) =
      (∑ P, (pauliDictionaryEnergyCoordinates p H P) ^ (2 : ℕ)) /
        (finiteCoefficientL1Mass (pauliDictionaryEnergyCoordinates p H)) ^ (2 : ℕ) := by
  apply energyMatchedEigenframeAmplitude_eq_of_fixed
  exact autonomousDictionaryPauliTransfer_fixes_energy p H hsupport t

/-- Permanent arbitrary-dictionary lower bound for every nonzero autonomous Hamiltonian. -/
theorem autonomous_energyMatchedEigenframeAmplitude_ge
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    1 / (Fintype.card {P // p P} : ℝ) ≤
      energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) := by
  apply energyMatchedEigenframeAmplitude_ge_card_inv_of_fixed
  · exact pauliDictionaryEnergyCoordinates_ne_zero p H hH hsupport
  · exact autonomousDictionaryPauliTransfer_fixes_energy p H hsupport t

/-- Fixed-body Majorana specialization: the permanent signed mean pays one inverse dictionary,
`binom(2n,q)⁻¹`, rather than its square and no Jordan--Wigner weight factor. -/
theorem autonomous_majoranaQBody_energyMatchedEigenframeAmplitude_ge
    {n q : ℕ} (hq : q ≤ 2 * n)
    (c : MajoranaQBodyIndex n q → ℝ) (hc : c ≠ 0) (t : ℝ) :
    1 / (Nat.choose (2 * n) q : ℝ) ≤
      energyMatchedEigenframeAmplitude
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (pauliDictionaryEnergyCoordinates (MajoranaQBodyDictionary n q)
          (majoranaQBodyHamiltonian c))
        (exp (t • ((-Complex.I) •
          ((majoranaQBodyHamiltonian c : selfAdjoint
            (Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hq
  rw [← majoranaQBodyDictionary_card]
  exact autonomous_energyMatchedEigenframeAmplitude_ge
    (MajoranaQBodyDictionary n q) (majoranaQBodyHamiltonian c)
    (majoranaQBodyHamiltonian_ne_zero c hc)
    (majoranaQBodyHamiltonian_hasDictionarySupport c) t

def finiteQubitPairConfigurationEquiv
    {σ : Type*} :
    (σ → Bool × Bool) ≃
      (FiniteQubitConfiguration σ × FiniteQubitConfiguration σ) where
  toFun xy := (finiteQubitPairRow xy, finiteQubitPairColumn xy)
  invFun rc := fun s => (rc.1 s, rc.2 s)
  left_inv xy := by
    funext s
    exact Prod.ext rfl rfl
  right_inv rc := by
    exact Prod.ext (funext fun _ => rfl) (funext fun _ => rfl)

theorem finitePauliHilbertSchmidt_eq_sum_entries
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    finitePauliHilbertSchmidt P Q =
      ∑ x : FiniteQubitConfiguration σ,
        ∑ y : FiniteQubitConfiguration σ,
          star (finitePauliMatrix P x y) * finitePauliMatrix Q x y := by
  rw [finitePauliHilbertSchmidt]
  calc
    (∑ xy : σ → Bool × Bool,
      ∏ s, star (boolPauliOptionEntry (P s) (xy s)) *
        boolPauliOptionEntry (Q s) (xy s)) =
      ∑ rc : FiniteQubitConfiguration σ × FiniteQubitConfiguration σ,
        ∏ s, star (boolPauliOptionEntry (P s) (rc.1 s, rc.2 s)) *
          boolPauliOptionEntry (Q s) (rc.1 s, rc.2 s) := by
      exact Fintype.sum_equiv finiteQubitPairConfigurationEquiv _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      change
        (∏ s, star (boolPauliOptionEntry (P s) (x s, y s)) *
          boolPauliOptionEntry (Q s) (x s, y s)) =
        star (∏ s, boolPauliOptionEntry (P s) (x s, y s)) *
          ∏ s, boolPauliOptionEntry (Q s) (x s, y s)
      rw [Finset.prod_mul_distrib]
      congr 1
      exact (map_prod (starRingEnd ℂ)
        (fun s => boolPauliOptionEntry (P s) (x s, y s)) Finset.univ).symm

theorem trace_star_finitePauliMatrix_mul
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    Matrix.trace (star (finitePauliMatrix P) * finitePauliMatrix Q) =
      if P = Q then (2 : ℂ) ^ Fintype.card σ else 0 := by
  rw [← finitePauliHilbertSchmidt_eq]
  rw [finitePauliHilbertSchmidt_eq_sum_entries, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
  rw [Finset.sum_comm]

theorem trace_finitePauliMatrix_mul_conjugation_re
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (P Q : σ → Option (Fin 3)) :
    (Matrix.trace
      (finitePauliMatrix Q * star U * finitePauliMatrix P * U)).re =
      ((2 : ℝ) ^ Fintype.card σ) * pauliConjugationTransfer U Q P := by
  have hstarQ : star (finitePauliMatrix Q) = finitePauliMatrix Q := by
    rw [Matrix.star_eq_conjTranspose]
    exact finitePauliMatrix_isHermitian Q
  have hortho (R : σ → Option (Fin 3)) :
      Matrix.trace (finitePauliMatrix Q * finitePauliMatrix R) =
        if Q = R then (2 : ℂ) ^ Fintype.card σ else 0 := by
    rw [← hstarQ]
    exact trace_star_finitePauliMatrix_mul Q R
  calc
    (Matrix.trace
      (finitePauliMatrix Q * star U * finitePauliMatrix P * U)).re =
        (Matrix.trace
          (finitePauliMatrix Q * (star U * finitePauliMatrix P * U))).re := by
      congr 2
      noncomm_ring
    _ = ∑ R : σ → Option (Fin 3),
        (Matrix.trace (finitePauliMatrix Q *
          (pauliConjugationTransfer U R P • finitePauliMatrix R))).re := by
      rw [conjugation_finitePauliMatrix_expansion, Finset.mul_sum, Matrix.trace_sum]
      rw [← Complex.reCLM_apply, _root_.map_sum]
      rfl
    _ = ∑ R : σ → Option (Fin 3),
        pauliConjugationTransfer U R P *
          (if Q = R then (2 : ℝ) ^ Fintype.card σ else 0) := by
      apply Finset.sum_congr rfl
      intro R _hR
      rw [Matrix.mul_smul, Matrix.trace_smul, hortho]
      by_cases hQR : Q = R
      · subst R
        simp only [ite_true]
        change
          (pauliConjugationTransfer U Q P •
            ((2 : ℂ) ^ Fintype.card σ)).re =
          pauliConjugationTransfer U Q P *
            ((2 : ℝ) ^ Fintype.card σ)
        have hpow : (2 : ℂ) ^ Fintype.card σ =
            (((2 : ℝ) ^ Fintype.card σ : ℝ) : ℂ) := by norm_cast
        rw [Complex.real_smul, hpow, ← Complex.ofReal_mul, Complex.ofReal_re]
      · simp only [if_neg hQR]
        change
          (pauliConjugationTransfer U R P • (0 : ℂ)).re =
            pauliConjugationTransfer U R P * (0 : ℝ)
        simp
    _ = ((2 : ℝ) ^ Fintype.card σ) * pauliConjugationTransfer U Q P := by
      rw [Finset.sum_eq_single Q]
      · simp [mul_comm]
      · intro R _hR hRQ
        simp [hRQ.symm]
      · simp

def pauliDictionaryHamiltonian
    {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ) :
    Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ :=
  ∑ i, h i • finitePauliMatrix (label i)

theorem pauliDictionaryHamiltonian_expansion
    {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    pauliDictionaryHamiltonian label h * star U *
        pauliDictionaryHamiltonian label h * U =
      ∑ output, ∑ input,
        (h output * h input) •
          (finitePauliMatrix (label input) * star U *
            finitePauliMatrix (label output) * U) := by
  unfold pauliDictionaryHamiltonian
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro output _houtput
  apply Finset.sum_congr rfl
  intro input _hinput
  rw [smul_smul]

theorem pauliDictionaryHamiltonian_energy_transfer
    {σ ι : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    (Matrix.trace
      (pauliDictionaryHamiltonian label h * star U *
        pauliDictionaryHamiltonian label h * U)).re =
      ((2 : ℝ) ^ Fintype.card σ) *
        ∑ output, ∑ input,
          h output * h input * dictionaryPauliTransfer label U output input := by
  have hterm (output input : ι) :
      (Matrix.trace
        ((h output * h input) •
          (finitePauliMatrix (label input) * star U *
            finitePauliMatrix (label output) * U))).re =
        (h output * h input) * ((2 : ℝ) ^ Fintype.card σ) *
          dictionaryPauliTransfer label U input output := by
    rw [Matrix.trace_smul]
    change
      ((h output * h input) •
        Matrix.trace (finitePauliMatrix (label input) * star U *
          finitePauliMatrix (label output) * U)).re = _
    rw [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero,
      trace_finitePauliMatrix_mul_conjugation_re]
    rw [dictionaryPauliTransfer]
    ring
  calc
    (Matrix.trace
      (pauliDictionaryHamiltonian label h * star U *
        pauliDictionaryHamiltonian label h * U)).re =
      (Matrix.trace
        (∑ output, ∑ input,
          ((h output * h input) •
            (finitePauliMatrix (label input) * star U *
              finitePauliMatrix (label output) * U)))).re := by
        rw [pauliDictionaryHamiltonian_expansion]
    _ = ∑ output, ∑ input,
        (Matrix.trace
          ((h output * h input) •
            (finitePauliMatrix (label input) * star U *
              finitePauliMatrix (label output) * U))).re := by
      rw [Matrix.trace_sum]
      simp_rw [Matrix.trace_sum]
      rw [← Complex.reCLM_apply, _root_.map_sum]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Complex.reCLM_apply, ← Complex.reCLM_apply, _root_.map_sum]
      rfl
    _ = ∑ output, ∑ input,
        (h output * h input) * ((2 : ℝ) ^ Fintype.card σ) *
          dictionaryPauliTransfer label U input output := by
      apply Finset.sum_congr rfl
      intro output _houtput
      apply Finset.sum_congr rfl
      intro input _hinput
      exact hterm output input
    _ = ((2 : ℝ) ^ Fintype.card σ) *
        ∑ output, ∑ input,
          h output * h input * dictionaryPauliTransfer label U output input := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _houtput
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      ring

theorem pauliDictionaryHamiltonian_energyCoordinates_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H) :
    pauliDictionaryHamiltonian (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H) =
      (H : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) := by
  classical
  let c : (σ → Option (Fin 3)) → ℝ :=
    (finitePauliSelfAdjointBasis σ).repr H
  have hself := (finitePauliSelfAdjointBasis σ).sum_repr H
  have hmat := congrArg (selfAdjointValLinear (FiniteQubitConfiguration σ)) hself
  have hfull :
      (∑ P : σ → Option (Fin 3), c P • finitePauliMatrix P) =
        (H : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) := by
    rw [map_sum] at hmat
    have hmapTerm (P : σ → Option (Fin 3)) :
        selfAdjointValLinear (FiniteQubitConfiguration σ)
            (c P • finitePauliSelfAdjointBasis σ P) =
          c P • finitePauliMatrix P := by
      rw [map_smul, finitePauliSelfAdjointBasis_apply]
      rfl
    change (∑ P : σ → Option (Fin 3),
      selfAdjointValLinear (FiniteQubitConfiguration σ)
        (c P • finitePauliSelfAdjointBasis σ P)) =
      selfAdjointValLinear (FiniteQubitConfiguration σ) H at hmat
    simp_rw [hmapTerm] at hmat
    change (∑ P : σ → Option (Fin 3), c P • finitePauliMatrix P) =
      (H : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) at hmat
    exact hmat
  have hout :
      (∑ P : {P : σ → Option (Fin 3) // ¬ p P},
        c P.1 • finitePauliMatrix P.1) = 0 := by
    apply Finset.sum_eq_zero
    intro P _hP
    rw [show c P.1 = 0 from hsupport P.1 P.2]
    simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun P : σ → Option (Fin 3) => c P • finitePauliMatrix P)
  rw [hout, add_zero] at hsplit
  unfold pauliDictionaryHamiltonian pauliDictionaryEnergyCoordinates
    vectorCoordinateRestriction
  rw [show (finitePauliSelfAdjointBasis σ).repr H = c from rfl]
  exact hsplit.trans hfull


/-! ## Generator-matched Haar separation -/

/-- Unnormalized Hilbert--Schmidt autocorrelation of a source with its conjugate. -/
def matrixEnergyAdjointAutocorrelation
    {κ : Type*} [Fintype κ]
    (H U : Matrix κ κ ℂ) : ℝ :=
  (Matrix.trace (H * star U * H * U)).re

/-- The literal coefficient-matched eigenframe mean is exactly normalized Hilbert--Schmidt source
autocorrelation. -/
theorem energyMatchedEigenframeAmplitude_eq_energyAutocorrelation
    {ι : Type*} [Fintype ι]
    (label : ι → σ → Option (Fin 3)) (h : ι → ℝ)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    energyMatchedEigenframeAmplitude label h U =
      matrixEnergyAdjointAutocorrelation (pauliDictionaryHamiltonian label h) U /
        (((2 : ℝ) ^ Fintype.card σ) * (finiteCoefficientL1Mass h) ^ (2 : ℕ)) := by
  rw [energyMatchedEigenframeAmplitude_eq_transfer]
  have henergy := pauliDictionaryHamiltonian_energy_transfer label h U
  unfold matrixEnergyAdjointAutocorrelation
  rw [henergy]
  have hD : (2 : ℝ) ^ Fintype.card σ ≠ 0 := by positivity
  symm
  exact mul_div_mul_left _ _ hD

/-- Under dictionary support, the same operational mean is the normalized autocorrelation of the
actual Hamiltonian, not merely of a formal Pauli reconstruction. -/
theorem energyMatchedEigenframeAmplitude_eq_energyAutocorrelation_of_support
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H)
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H) U =
      matrixEnergyAdjointAutocorrelation
          (H : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) U /
        (((2 : ℝ) ^ Fintype.card σ) *
          (finiteCoefficientL1Mass (pauliDictionaryEnergyCoordinates p H)) ^ (2 : ℕ)) := by
  rw [energyMatchedEigenframeAmplitude_eq_energyAutocorrelation]
  rw [pauliDictionaryHamiltonian_energyCoordinates_eq p H hsupport]

/-- Every conjugation fixing `H` retains its full spectral energy. -/
theorem matrixEnergyAdjointAutocorrelation_eq_trace_mul_self_of_fixed
    {κ : Type*} [Fintype κ]
    (H U : Matrix κ κ ℂ) (hfix : star U * H * U = H) :
    matrixEnergyAdjointAutocorrelation H U = (Matrix.trace (H * H)).re := by
  calc
    matrixEnergyAdjointAutocorrelation H U =
        (Matrix.trace (H * (star U * H * U))).re := by
      unfold matrixEnergyAdjointAutocorrelation
      congr 2
      noncomm_ring
    _ = (Matrix.trace (H * H)).re := by rw [hfix]

/-- Every conjugation fixing `H` retains its full spectral energy. -/
theorem matrixEnergyAdjointAutocorrelation_eq_sum_sq_eigenvalues_of_fixed
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H U : Matrix κ κ ℂ) (hH : H.IsHermitian)
    (hfix : star U * H * U = H) :
    matrixEnergyAdjointAutocorrelation H U =
      ∑ i, (hH.eigenvalues i) ^ (2 : ℕ) := by
  calc
    matrixEnergyAdjointAutocorrelation H U = (Matrix.trace (H * H)).re :=
      matrixEnergyAdjointAutocorrelation_eq_trace_mul_self_of_fixed H U hfix
    _ = _ := trace_mul_self_re_eq_sum_sq_eigenvalues H hH

/-- Autonomous Schrödinger evolution retains full generator autocorrelation at every real time. -/
theorem autonomous_matrixEnergyAdjointAutocorrelation_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : selfAdjoint (Matrix κ κ ℂ)) (t : ℝ) :
    matrixEnergyAdjointAutocorrelation (H : Matrix κ κ ℂ)
        (exp (t • ((-Complex.I) • (H : Matrix κ κ ℂ)))) =
      (Matrix.trace ((H : Matrix κ κ ℂ) * (H : Matrix κ κ ℂ))).re := by
  apply matrixEnergyAdjointAutocorrelation_eq_trace_mul_self_of_fixed
  exact congrArg Subtype.val (finiteMatrixSelfAdjointConjugation_fixes_energy H t)

/-- Exact normalized source autocorrelation realized by the literal coefficient-sampled
eigenframe protocol at every autonomous time. -/
theorem autonomous_energyMatchedEigenframeAmplitude_eq_trace_normalized
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
        (pauliDictionaryEnergyCoordinates p H)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) =
      (Matrix.trace
        ((H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ) *
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ))).re /
        (((2 : ℝ) ^ Fintype.card σ) *
          (finiteCoefficientL1Mass (pauliDictionaryEnergyCoordinates p H)) ^ (2 : ℕ)) := by
  rw [energyMatchedEigenframeAmplitude_eq_energyAutocorrelation_of_support
    p H hsupport]
  rw [autonomous_matrixEnergyAdjointAutocorrelation_eq H t]

/-- The Haar integrand is the square of the literal matrix energy autocorrelation. -/
theorem finiteUnitaryAdjointAutocorrelationIntegrand_eq_energy_sq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (H : Matrix κ κ ℂ) (U : Matrix.unitaryGroup κ ℂ) :
    finiteUnitaryAdjointAutocorrelationIntegrand H U =
      matrixEnergyAdjointAutocorrelation H (U : Matrix κ κ ℂ) ^ (2 : ℕ) := by
  rfl

/-- **Permanent autonomous-source versus Haar separation on qubits.** Every nonzero traceless
autonomous Hamiltonian retains its entire generator autocorrelation at every time, whereas a Haar
unitary retains even half that amplitude with probability at most `4 / (D² - 1)`, `D = 2ⁿ`.
The tail has no spectral-gap or dictionary-size hypothesis. -/
theorem autonomous_full_energy_and_haar_half_energy_separation
    {n : ℕ} (hn : 1 ≤ n)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (htrace : (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ).trace = 0)
    (hzero : H ≠ 0) (t : ℝ) :
    matrixEnergyAdjointAutocorrelation
        (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)))) =
        (Matrix.trace
          ((H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) *
            (H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ))).re ∧
      (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
          {U | ((Matrix.trace
              ((H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ) *
                (H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))).re / 2) ^ (2 : ℕ) ≤
            finiteUnitaryAdjointAutocorrelationIntegrand
              (H : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) U} ≤
        4 / ((((2 ^ n : ℕ) : ℝ) ^ (2 : ℕ)) - 1) := by
  have hpow : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ (1 : ℕ) := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard :
      Fintype.card (FiniteQubitConfiguration (Fin n)) =
        Fintype.card (Fin 2 ⊕ Fin (2 ^ n - 2)) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_sum]
    omega
  let e : FiniteQubitConfiguration (Fin n) ≃ Fin 2 ⊕ Fin (2 ^ n - 2) :=
    Fintype.equivOfCardEq hcard
  constructor
  · exact autonomous_matrixEnergyAdjointAutocorrelation_eq H t
  · have hHmatrix :
        (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) ≠ 0 := by
      intro h
      apply hzero
      exact Subtype.ext h
    have hHherm :
        (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ).IsHermitian := by
      rw [Matrix.IsHermitian, ← Matrix.star_eq_conjTranspose]
      exact H.prop
    have htail := haar_measureReal_half_traceEnergy_adjointAutocorrelation_le
      (2 ^ n - 2) e
      (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)
      hHherm htrace hHmatrix
    have hdim : 2 ^ n - 2 + 2 = 2 ^ n := Nat.sub_add_cancel hpow
    simpa only [hdim] using htail

/-- **Operational dictionary-free Haar tail.** For a nonzero traceless Hamiltonian supported on
any Pauli dictionary, the literal signed product-eigenframe mean of a Haar unitary reaches at least
half the autonomous all-time value with probability at most `4 / (D² - 1)`.  Dictionary size and
minimum spectral gaps are absent from the bound. -/
theorem haar_measureReal_half_autonomous_energyMatchedAmplitude_le
    {n : ℕ} (hn : 1 ≤ n)
    (p : (Fin n → Option (Fin 3)) → Prop) [DecidablePred p]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hzero : H ≠ 0) (hsupport : HasPauliDictionarySupport p H)
    (htrace : (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ).trace = 0) :
    (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
        {U | (((Matrix.trace
              ((H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ) *
                (H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))).re /
              (((2 ^ n : ℕ) : ℝ) *
                (finiteCoefficientL1Mass
                  (pauliDictionaryEnergyCoordinates p H)) ^ (2 : ℕ))) / 2) ^ (2 : ℕ) ≤
          (energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
            (pauliDictionaryEnergyCoordinates p H)
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) ^ (2 : ℕ)} ≤
      4 / ((((2 ^ n : ℕ) : ℝ) ^ (2 : ℕ)) - 1) := by
  let h := pauliDictionaryEnergyCoordinates p H
  let S : ℝ := (Matrix.trace
    ((H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) *
      (H : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))).re
  let c : ℝ := ((2 ^ n : ℕ) : ℝ) * (finiteCoefficientL1Mass h) ^ (2 : ℕ)
  have hh : h ≠ 0 := pauliDictionaryEnergyCoordinates_ne_zero p H hzero hsupport
  have hL : 0 < finiteCoefficientL1Mass h := finiteCoefficientL1Mass_pos h hh
  have hD : 0 < ((2 ^ n : ℕ) : ℝ) := by positivity
  have hc : 0 < c := mul_pos hD (sq_pos_of_pos hL)
  have htail := (autonomous_full_energy_and_haar_half_energy_separation
    hn H htrace hzero 0).2
  have hset :
      {U : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ |
        ((S / c) / 2) ^ (2 : ℕ) ≤
          (energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1) h
            (U : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)) ^ (2 : ℕ)} =
      {U | (S / 2) ^ (2 : ℕ) ≤
        finiteUnitaryAdjointAutocorrelationIntegrand
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) U} := by
    ext U
    simp only [Set.mem_setOf_eq]
    rw [show h = pauliDictionaryEnergyCoordinates p H from rfl,
      energyMatchedEigenframeAmplitude_eq_energyAutocorrelation_of_support p H hsupport,
      finiteUnitaryAdjointAutocorrelationIntegrand_eq_energy_sq]
    simp only [Fintype.card_fin]
    have hdimreal : (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) := by norm_cast
    rw [hdimreal]
    change ((S / c) / 2) ^ (2 : ℕ) ≤
        (matrixEnergyAdjointAutocorrelation
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) U / c) ^ (2 : ℕ) ↔
      (S / 2) ^ (2 : ℕ) ≤
        matrixEnergyAdjointAutocorrelation
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) U ^ (2 : ℕ)
    rw [show S / c / 2 = (S / 2) / c by ring,
      div_pow (S / 2) c 2,
      div_pow (matrixEnergyAdjointAutocorrelation
        (H : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) U) c 2]
    exact div_le_div_iff_of_pos_right (sq_pos_of_pos hc)
  change (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
      {U | ((S / c) / 2) ^ (2 : ℕ) ≤
        (energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1) h
          (U : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)) ^ (2 : ℕ)} ≤ _
  rw [hset]
  exact htail

/-- Local-dictionary specialization combining the permanent one-query inverse-participation signal
with dimension-only Haar anti-concentration for the same Hamiltonian source. -/
theorem autonomous_dictionary_energyMatched_and_haar_separation
    {n : ℕ} (hn : 1 ≤ n)
    (p : (Fin n → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hzero : H ≠ 0) (hsupport : HasPauliDictionarySupport p H)
    (htrace : (H : Matrix (FiniteQubitConfiguration (Fin n))
      (FiniteQubitConfiguration (Fin n)) ℂ).trace = 0)
    (t : ℝ) :
    1 / (Fintype.card {P // p P} : ℝ) ≤
        energyMatchedEigenframeAmplitude (fun P : {P // p P} => P.1)
          (pauliDictionaryEnergyCoordinates p H)
          (exp (t • ((-Complex.I) •
            (H : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))) ∧
      (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
          {U | ((Matrix.trace
              ((H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ) *
                (H : Matrix (FiniteQubitConfiguration (Fin n))
                  (FiniteQubitConfiguration (Fin n)) ℂ))).re / 2) ^ (2 : ℕ) ≤
            finiteUnitaryAdjointAutocorrelationIntegrand
              (H : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ) U} ≤
        4 / ((((2 ^ n : ℕ) : ℝ) ^ (2 : ℕ)) - 1) := by
  constructor
  · exact autonomous_energyMatchedEigenframeAmplitude_ge p H hzero hsupport t
  · exact (autonomous_full_energy_and_haar_half_energy_separation
      hn H htrace hzero t).2

end

end GaloisForLFunctions.HTGeometry
