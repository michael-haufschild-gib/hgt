import GaloisForLFunctions.HTGeometry.LiteralTwoQueryHaarBenchmark
import GaloisForLFunctions.HTGeometry.TracelessLocalPauliTransferConservationLaw
import GaloisForLFunctions.QuantumAlg.Primitives.QNN.Algebras.TFIM

/-!
# Adaptive eigenframe two-query source memory

For a Pauli dictionary, sample an input word `P`, an output word `Q`, and one uniformly random
product eigenstate of `Q`.  Apply the same unknown unitary to two copies and measure `P` on both.
The resulting score dominates the squared Frobenius mass of the dictionary compression of the
Pauli-transfer matrix without a penalty depending on Pauli weight.

This removes the `3^{-q}` loss of a dictionary-independent product-stabilizer test.  The preparation
is instead adapted to the sampled output word.  It is still a product-state, two-forward-query
experiment.
-/

open Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Topology
open NormedSpace
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ ι : Type*} [Fintype σ] [DecidableEq σ]

/-- Entrywise domination aggregates to domination of the normalized squared matrix mean. -/
theorem twoQueryLocalRetentionMean_le_of_entrywise
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (C E : Matrix κ κ ℝ) (h : ∀ i j, (C i j) ^ 2 ≤ E i j) :
    twoQueryLocalRetentionMean C ≤
      (∑ i, ∑ j, E i j) / (Fintype.card κ : ℝ) ^ 2 := by
  rw [twoQueryLocalRetentionMean]
  have hden : 0 < (Fintype.card κ : ℝ) ^ 2 := by positivity
  exact (div_le_div_iff_of_pos_right hden).2
    (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j)

/-- Stabilizer sample whose local axis is adapted to a Pauli label.  Identity sites use an arbitrary
fixed axis; their signed spectral resolution is the ordinary resolution of the identity. -/
def pauliEigenframeSample (P : σ → Option (Fin 3)) (b : σ → Bool) :
    σ → Fin 3 × Bool :=
  fun s => (match P s with | none => 0 | some a => a, b s)

/-- Eigenvalue sign of `P` on its product eigenstate indexed by `b`. -/
def pauliEigenframeSign (P : σ → Option (Fin 3)) (b : σ → Bool) : ℝ :=
  ∏ s, stabilizerAxisExpectation (pauliEigenframeSample P b s) (P s)

/-- One-site signed eigenframe twirl. -/
def localPauliEigenframeTwirl (p q : Option (Fin 3)) : ℝ :=
  (∑ b : Bool,
      stabilizerAxisExpectation
          ((match p with | none => 0 | some a => a), b) p *
        stabilizerAxisExpectation
          ((match p with | none => 0 | some a => a), b) q) / 2

/-- The signed eigenframe of one Pauli coordinate extracts exactly that coordinate. -/
theorem localPauliEigenframeTwirl_eq (p q : Option (Fin 3)) :
    localPauliEigenframeTwirl p q = if p = q then 1 else 0 := by
  fin_cases p <;> fin_cases q <;>
    norm_num [localPauliEigenframeTwirl, stabilizerAxisExpectation, Fintype.sum_bool] <;>
    simp

/-- Product signed eigenframe twirl. -/
def pauliEigenframeTwirl (P Q : σ → Option (Fin 3)) : ℝ :=
  ∏ s, localPauliEigenframeTwirl (P s) (Q s)

/-- Product eigenframes retain one Pauli word and annihilate every other word. -/
theorem pauliEigenframeTwirl_eq (P Q : σ → Option (Fin 3)) :
    pauliEigenframeTwirl P Q = if P = Q then 1 else 0 := by
  classical
  by_cases hPQ : P = Q
  · subst Q
    simp [pauliEigenframeTwirl, localPauliEigenframeTwirl_eq]
  · obtain ⟨s, hs⟩ : ∃ s, P s ≠ Q s := by
      simpa only [Function.ne_iff] using hPQ
    rw [if_neg hPQ]
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    rw [localPauliEigenframeTwirl_eq, if_neg hs]

/-- The normalized product sum factorizes into the signed eigenframe twirl. -/
theorem average_pauliEigenframe_character
    (P Q : σ → Option (Fin 3)) :
    (∑ b : σ → Bool,
        pauliEigenframeSign P b *
          ∏ s, stabilizerAxisExpectation (pauliEigenframeSample P b s) (Q s)) /
        (Fintype.card (σ → Bool) : ℝ) = pauliEigenframeTwirl P Q := by
  classical
  have hterm : ∀ b : σ → Bool,
      pauliEigenframeSign P b *
          (∏ s, stabilizerAxisExpectation (pauliEigenframeSample P b s) (Q s)) =
        ∏ s,
          (stabilizerAxisExpectation (pauliEigenframeSample P b s) (P s) *
            stabilizerAxisExpectation (pauliEigenframeSample P b s) (Q s)) :=
    fun b => Finset.prod_mul_distrib.symm
  simp only [hterm]
  have hcard : (Fintype.card (σ → Bool) : ℝ) = ∏ _s : σ, (2 : ℝ) := by simp
  rw [pauliEigenframeTwirl]
  simp_rw [localPauliEigenframeTwirl]
  rw [hcard, Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_univ_sum (fun _ : σ => (Finset.univ : Finset Bool))
    (fun s b =>
      stabilizerAxisExpectation
          ((match P s with | none => 0 | some a => a), b) (P s) *
        stabilizerAxisExpectation
          ((match P s with | none => 0 | some a => a), b) (Q s)),
    Fintype.piFinset_univ]
  rfl

/-- Expectation of an evolved Pauli word in one adapted product eigenstate. -/
def pauliEigenframeExpectation
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (input output : σ → Option (Fin 3)) (b : σ → Bool) : ℝ :=
  (Matrix.trace
    (productStabilizerDensity (pauliEigenframeSample output b) *
      (star U * finitePauliMatrix input * U))).re

/-- Signed eigenframe averaging extracts one exact Pauli-transfer coefficient. -/
theorem average_pauliEigenframeExpectation_eq_transfer
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (input output : σ → Option (Fin 3)) :
    (∑ b : σ → Bool,
        pauliEigenframeSign output b *
          pauliEigenframeExpectation U input output b) /
        (Fintype.card (σ → Bool) : ℝ) =
      pauliConjugationTransfer U output input := by
  classical
  simp only [pauliEigenframeExpectation,
    trace_productStabilizerDensity_mul_conjugation]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]
  have hfactor : ∀ Q : σ → Option (Fin 3),
      (∑ b : σ → Bool,
          pauliEigenframeSign output b *
            (pauliConjugationTransfer U Q input *
              ∏ s, stabilizerAxisExpectation
                (pauliEigenframeSample output b s) (Q s))) /
          (Fintype.card (σ → Bool) : ℝ) =
        pauliConjugationTransfer U Q input * pauliEigenframeTwirl output Q := by
    intro Q
    have hreorder :
        (∑ b : σ → Bool,
            pauliEigenframeSign output b *
              (pauliConjugationTransfer U Q input *
                ∏ s, stabilizerAxisExpectation
                  (pauliEigenframeSample output b s) (Q s))) =
          pauliConjugationTransfer U Q input *
            ∑ b : σ → Bool,
              pauliEigenframeSign output b *
                ∏ s, stabilizerAxisExpectation
                  (pauliEigenframeSample output b s) (Q s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    rw [hreorder, mul_div_assoc, average_pauliEigenframe_character]
  rw [Finset.sum_congr rfl fun Q _ => hfactor Q]
  rw [Finset.sum_eq_single output]
  · rw [pauliEigenframeTwirl_eq, if_pos rfl, mul_one]
  · intro Q _hQ hQout
    rw [pauliEigenframeTwirl_eq, if_neg (Ne.symm hQout), mul_zero]
  · simp

/-- Every adapted eigenvalue sign has square one. -/
theorem pauliEigenframeSign_sq (P : σ → Option (Fin 3)) (b : σ → Bool) :
    (pauliEigenframeSign P b) ^ 2 = 1 := by
  classical
  rw [pauliEigenframeSign, pow_two, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro s _hs
  cases hP : P s with
  | none => simp [pauliEigenframeSample, hP, stabilizerAxisExpectation]
  | some a =>
      cases hb : b s <;>
        simp [pauliEigenframeSample, hP, hb, stabilizerAxisExpectation]

/-- Cauchy--Schwarz: one squared transfer coefficient is bounded by the mean squared physical
expectation over the adapted product eigenframe. -/
theorem pauliConjugationTransfer_sq_le_eigenframeMean
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (input output : σ → Option (Fin 3)) :
    (pauliConjugationTransfer U output input) ^ 2 ≤
      (∑ b : σ → Bool, (pauliEigenframeExpectation U input output b) ^ 2) /
        (Fintype.card (σ → Bool) : ℝ) := by
  classical
  let N : ℝ := Fintype.card (σ → Bool)
  have hN : 0 < N := by positivity
  have hsign : (∑ b : σ → Bool, (pauliEigenframeSign output b) ^ 2) = N := by
    simp_rw [pauliEigenframeSign_sq]
    simp [N]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (pauliEigenframeSign output)
    (pauliEigenframeExpectation U input output)
  rw [hsign] at hCS
  have hextract := average_pauliEigenframeExpectation_eq_transfer U input output
  change (∑ b, pauliEigenframeSign output b *
      pauliEigenframeExpectation U input output b) / N =
    pauliConjugationTransfer U output input at hextract
  rw [← hextract]
  rw [div_pow]
  have hN0 : N ≠ 0 := ne_of_gt hN
  change
    (∑ b, pauliEigenframeSign output b * pauliEigenframeExpectation U input output b) ^ 2 /
        N ^ 2 ≤
      (∑ b, pauliEigenframeExpectation U input output b ^ 2) / N
  apply (div_le_div_iff₀ (sq_pos_of_pos hN) hN).2
  nlinarith [mul_nonneg hN.le (sub_nonneg.mpr hCS)]

/-- Mean squared output expectation for one ordered pair of dictionary words. -/
def dictionaryEigenframeMean [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    Matrix ι ι ℝ :=
  fun output input =>
    (∑ b : σ → Bool,
        (pauliEigenframeExpectation U (label input) (label output) b) ^ 2) /
      (Fintype.card (σ → Bool) : ℝ)

/-- Literal adaptive product-eigenframe, two-query score. -/
def adaptiveEigenframeTwoQueryScore [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) : ℝ :=
  (∑ output : ι, ∑ input : ι, dictionaryEigenframeMean label U output input) /
    (Fintype.card ι : ℝ) ^ 2

/-- Every dictionary-eigenframe mean is nonnegative. -/
theorem dictionaryEigenframeMean_nonneg [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (output input : ι) :
    0 ≤ dictionaryEigenframeMean label U output input := by
  unfold dictionaryEigenframeMean
  positivity

/-- The complete adaptive two-query score is nonnegative. -/
theorem adaptiveEigenframeTwoQueryScore_nonneg [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    0 ≤ adaptiveEigenframeTwoQueryScore label U := by
  unfold adaptiveEigenframeTwoQueryScore
  apply div_nonneg
  · exact Finset.sum_nonneg fun output _ =>
      Finset.sum_nonneg fun input _ => dictionaryEigenframeMean_nonneg label U output input
  · positivity

/-- Dictionary compression of the exact Pauli-transfer matrix. -/
def dictionaryPauliTransfer [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    Matrix ι ι ℝ :=
  fun output input => pauliConjugationTransfer U (label output) (label input)

/-- Coordinate form of the adaptive-eigenframe domination, packaged at dictionary level to avoid
expanding the full Pauli basis during finite-sum aggregation. -/
theorem dictionaryPauliTransfer_sq_le_eigenframeMean [Fintype ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (input output : ι) :
    (dictionaryPauliTransfer label U output input) ^ 2 ≤
      dictionaryEigenframeMean label U output input :=
  pauliConjugationTransfer_sq_le_eigenframeMean U (label input) (label output)

/-- The physical adaptive-eigenframe score dominates the complete squared transfer mass retained
by the dictionary. -/
theorem twoQueryLocalRetentionMean_le_adaptiveEigenframeScore
    [Fintype ι] [Nonempty ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ) :
    twoQueryLocalRetentionMean (dictionaryPauliTransfer label U) ≤
      adaptiveEigenframeTwoQueryScore label U := by
  classical
  change twoQueryLocalRetentionMean (dictionaryPauliTransfer label U) ≤
    (∑ output, ∑ input, dictionaryEigenframeMean label U output input) /
      (Fintype.card ι : ℝ) ^ 2
  exact twoQueryLocalRetentionMean_le_of_entrywise
    (dictionaryPauliTransfer label U) (dictionaryEigenframeMean label U)
    (fun output input => dictionaryPauliTransfer_sq_le_eigenframeMean label U input output)

/-- Any nonzero conserved dictionary coordinate forces inverse-dictionary-squared physical score,
uniformly in time and independently of Pauli weight. -/
theorem adaptiveEigenframeTwoQueryScore_ge_card_sq_inv
    [Fintype ι] [Nonempty ι]
    (label : ι → σ → Option (Fin 3))
    (U : Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)
    (h : ι → ℝ) (hh : h ≠ 0)
    (hfix : dictionaryPauliTransfer label U *ᵥ h = h) :
    1 / (Fintype.card ι : ℝ) ^ 2 ≤ adaptiveEigenframeTwoQueryScore label U := by
  exact (twoQueryLocalRetentionMean_ge_card_sq_inv _ h hh hfix).trans
    (twoQueryLocalRetentionMean_le_adaptiveEigenframeScore label U)

/-! ## Exact Haar benchmark -/

/-- One dictionary-eigenframe mean varies continuously with the unitary oracle. -/
theorem continuous_dictionaryEigenframeMean
    {n : ℕ} [Fintype ι]
    (label : ι → Fin n → Option (Fin 3)) (output input : ι) :
    Continuous fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
      dictionaryEigenframeMean label
        (V : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) output input := by
  unfold dictionaryEigenframeMean
  apply Continuous.div_const
  apply continuous_finset_sum
  intro b _hb
  simpa [pauliEigenframeExpectation] using
    (continuous_sq_trace_conj
      (productStabilizerDensity (pauliEigenframeSample (label output) b))
      (finitePauliMatrix (label input)))

/-- The complete adaptive score is continuous on the compact unitary group. -/
theorem continuous_adaptiveEigenframeTwoQueryScore
    {n : ℕ} [Fintype ι]
    (label : ι → Fin n → Option (Fin 3)) :
    Continuous fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
      adaptiveEigenframeTwoQueryScore label
        (V : Matrix (FiniteQubitConfiguration (Fin n))
          (FiniteQubitConfiguration (Fin n)) ℂ) := by
  unfold adaptiveEigenframeTwoQueryScore
  apply Continuous.div_const
  apply continuous_finset_sum
  intro output _houtput
  apply continuous_finset_sum
  intro input _hinput
  exact continuous_dictionaryEigenframeMean label output input

/-- The adaptive score is Haar-integrable. -/
theorem integrable_adaptiveEigenframeTwoQueryScore
    {n : ℕ} [Fintype ι]
    (label : ι → Fin n → Option (Fin 3)) :
    Integrable
      (fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
        adaptiveEigenframeTwoQueryScore label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ))
      (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) :=
  integrable_finiteUnitaryHaar_of_continuous _
    (continuous_adaptiveEigenframeTwoQueryScore label)

/-- Every fixed adaptive-eigenframe trial has exact Haar mean square `1 / (2^n + 1)`. -/
theorem haar_sq_pauliEigenframeExpectation_eq
    {n : ℕ} (hn : 1 ≤ n)
    (input output : Fin n → Option (Fin 3))
    (hinput : input ≠ pauliIdentityLabel n)
    (b : Fin n → Bool) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        (pauliEigenframeExpectation
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) input output b) ^ 2
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
      1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  have hcard : Fintype.card (FiniteQubitConfiguration (Fin n)) =
      Fintype.card (Fin 2 ⊕ Fin (2 ^ n - 2)) := by
    have hpow : 2 ≤ 2 ^ n := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simp only [FiniteQubitConfiguration, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_sum]
    omega
  let e : FiniteQubitConfiguration (Fin n) ≃ Fin 2 ⊕ Fin (2 ^ n - 2) :=
    Fintype.equivOfCardEq hcard
  change
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
      (Matrix.trace
        (productStabilizerDensity (pauliEigenframeSample output b) *
          (star (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) * finitePauliMatrix input *
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))).re ^ 2
      ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) = _
  rw [haar_sq_trace_pure_state_conjugation (2 ^ n - 2) e
    (productStabilizerDensity_isHermitian (pauliEigenframeSample output b))
    (productStabilizerDensity_mul_self (pauliEigenframeSample output b))
    (trace_productStabilizerDensity (pauliEigenframeSample output b))
    (finitePauliMatrix_isHermitian input)
    (finitePauliMatrix_trace_eq_zero_of_ne_identity input hinput)
    (finitePauliMatrix_mul_self input)]
  have hpow : 2 ≤ 2 ^ n := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hd3 : ((2 ^ n - 2 : ℕ) : ℝ) + 3 = ((2 ^ n + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpow]
    push_cast
    ring
  rw [hd3, one_div]

/-- One ordered dictionary pair has exact adaptive-eigenframe Haar mean `(2^n+1)^{-1}`. -/
theorem haar_dictionaryEigenframeMean_eq
    {n : ℕ} (hn : 1 ≤ n) [Fintype ι]
    (label : ι → Fin n → Option (Fin 3))
    (hlabel : ∀ i, label i ≠ pauliIdentityLabel n)
    (output input : ι) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        dictionaryEigenframeMean label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) output input
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
      1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  have hcont : ∀ b : Fin n → Bool,
      Continuous fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
        (pauliEigenframeExpectation
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          (label input) (label output) b) ^ 2 := by
    intro b
    simpa [pauliEigenframeExpectation] using
      (continuous_sq_trace_conj
        (productStabilizerDensity (pauliEigenframeSample (label output) b))
        (finitePauliMatrix (label input)))
  change
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
      (∑ b : Fin n → Bool,
        (pauliEigenframeExpectation
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
          (label input) (label output) b) ^ 2) /
        (Fintype.card (Fin n → Bool) : ℝ)
      ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) = _
  rw [integral_div,
    integral_finsetSum _ (fun b _ =>
      integrable_finiteUnitaryHaar_of_continuous _ (hcont b))]
  rw [Finset.sum_congr rfl fun b _ =>
    haar_sq_pauliEigenframeExpectation_eq hn (label input) (label output) (hlabel input) b]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcfg : (Fintype.card (Fin n → Bool) : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Exact Haar law for the complete adaptive two-query experiment.** Every finite dictionary of
nonidentity Pauli words has Haar expectation exactly `1 / (2^n + 1)`, independently of word weight
and dictionary size. -/
theorem haar_adaptiveEigenframeTwoQueryScore_eq
    {n : ℕ} (hn : 1 ≤ n) [Fintype ι] [Nonempty ι]
    (label : ι → Fin n → Option (Fin 3))
    (hlabel : ∀ i, label i ≠ pauliIdentityLabel n) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        adaptiveEigenframeTwoQueryScore label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
      1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  have hint : ∀ output input : ι,
      Integrable
        (fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
          dictionaryEigenframeMean label
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ) output input)
        (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) := by
    intro output input
    apply Integrable.div_const
    apply integrable_finsetSum
    intro b _hb
    apply integrable_finiteUnitaryHaar_of_continuous
    simpa [pauliEigenframeExpectation] using
      (continuous_sq_trace_conj
        (productStabilizerDensity (pauliEigenframeSample (label output) b))
        (finitePauliMatrix (label input)))
  change
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
      (∑ output : ι, ∑ input : ι,
        dictionaryEigenframeMean label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ) output input) /
        (Fintype.card ι : ℝ) ^ 2
      ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) = _
  rw [integral_div,
    integral_finsetSum _ (fun output _ =>
      integrable_finsetSum _ (fun input _ => hint output input))]
  rw [Finset.sum_congr rfl fun output _ =>
    integral_finsetSum _ (fun input _ => hint output input)]
  rw [Finset.sum_congr rfl fun output _ =>
    Finset.sum_congr rfl fun input _ =>
      haar_dictionaryEigenframeMean_eq hn label hlabel output input]
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hM : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp
  simp

/-- **Haar high-score tail law.** Markov's inequality upgrades the exact mean into a probability
bound for every positive score threshold. -/
theorem haar_measureReal_adaptiveEigenframeScore_ge_le
    {n : ℕ} (hn : 1 ≤ n) [Fintype ι] [Nonempty ι]
    (label : ι → Fin n → Option (Fin 3))
    (hlabel : ∀ i, label i ≠ pauliIdentityLabel n)
    {ε : ℝ} (hε : 0 < ε) :
    (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
        {V | ε ≤ adaptiveEigenframeTwoQueryScore label
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)} ≤
      (1 / ((2 ^ n + 1 : ℕ) : ℝ)) / ε := by
  let f := fun V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ =>
    adaptiveEigenframeTwoQueryScore label
      (V : Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ)
  have hnonneg : 0 ≤ᵐ[finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))] f :=
    Filter.Eventually.of_forall fun V => adaptiveEigenframeTwoQueryScore_nonneg label V
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg
    (integrable_adaptiveEigenframeTwoQueryScore label) ε
  rw [haar_adaptiveEigenframeTwoQueryScore_eq hn label hlabel] at hmarkov
  exact (le_div_iff₀ hε).2 (by simpa [f, mul_comm] using hmarkov)

/-- At the conserved dictionary floor `M⁻²`, Haar high-score probability is at most
`M²/(2^n+1)`. -/
theorem haar_measureReal_adaptiveEigenframeScore_ge_card_inv_le
    {n : ℕ} (hn : 1 ≤ n) [Fintype ι] [Nonempty ι]
    (label : ι → Fin n → Option (Fin 3))
    (hlabel : ∀ i, label i ≠ pauliIdentityLabel n) :
    (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
        {V | 1 / (Fintype.card ι : ℝ) ^ 2 ≤
          adaptiveEigenframeTwoQueryScore label
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)} ≤
      (Fintype.card ι : ℝ) ^ 2 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  have hM : 0 < (Fintype.card ι : ℝ) ^ 2 := by positivity
  have h := haar_measureReal_adaptiveEigenframeScore_ge_le hn label hlabel
    (one_div_pos.mpr hM)
  convert h using 1 <;> field_simp

/-! ## Autonomous Hamiltonians supported on an arbitrary Pauli dictionary -/

/-- A self-adjoint Hamiltonian has Pauli support inside predicate `p`. -/
def HasPauliDictionarySupport
    (p : (σ → Option (Fin 3)) → Prop)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)) : Prop :=
  ∀ P, ¬p P →
    ((finitePauliSelfAdjointBasis σ).repr H :
      (σ → Option (Fin 3)) → ℝ) P = 0

/-- Hamiltonian coordinates restricted to an arbitrary Pauli dictionary. -/
def pauliDictionaryEnergyCoordinates
    (p : (σ → Option (Fin 3)) → Prop)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ)) :
    {P // p P} → ℝ :=
  vectorCoordinateRestriction p
    ((finitePauliSelfAdjointBasis σ).repr H :
      (σ → Option (Fin 3)) → ℝ)

/-- Exact autonomous conservation survives compression to every dictionary containing the full
Pauli support of the Hamiltonian. -/
theorem autonomousDictionaryPauliTransfer_fixes_energy
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    dictionaryPauliTransfer (fun P : {P // p P} => P.1)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) *ᵥ
      pauliDictionaryEnergyCoordinates p H = pauliDictionaryEnergyCoordinates p H := by
  change
    matrixCoordinateCompression p
      (LinearMap.toMatrix
        (finitePauliSelfAdjointBasis σ) (finitePauliSelfAdjointBasis σ)
        (finiteMatrixSelfAdjointConjugationLinearMap
          (exp (t • ((-Complex.I) •
            (H : Matrix (FiniteQubitConfiguration σ)
              (FiniteQubitConfiguration σ) ℂ)))))) *ᵥ
        vectorCoordinateRestriction p
          ((finitePauliSelfAdjointBasis σ).repr H :
            (σ → Option (Fin 3)) → ℝ) =
      vectorCoordinateRestriction p
        ((finitePauliSelfAdjointBasis σ).repr H :
          (σ → Option (Fin 3)) → ℝ)
  apply matrixCoordinateCompression_mulVec_restriction_eq_of_fixed_of_support
  · exact linearMap_toMatrix_mulVec_repr_eq_of_fixed
      (finitePauliSelfAdjointBasis σ)
      (finiteMatrixSelfAdjointConjugationLinearMap
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ))))) H
      (finiteMatrixSelfAdjointConjugation_fixes_energy H t)
  · exact hsupport

/-- Restricting a nonzero Hamiltonian to a dictionary containing its support remains nonzero. -/
theorem pauliDictionaryEnergyCoordinates_ne_zero
    (p : (σ → Option (Fin 3)) → Prop)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport p H) :
    pauliDictionaryEnergyCoordinates p H ≠ 0 := by
  apply vectorCoordinateRestriction_ne_zero_of_ne_zero_of_support
  · intro hzero
    apply hH
    apply (finitePauliSelfAdjointBasis σ).repr.injective
    exact Finsupp.ext fun P => by simpa using congrFun hzero P
  · exact hsupport

/-- **Permanent adaptive-eigenframe source-memory law.** Every nonzero autonomous Hamiltonian whose
Pauli support lies in a nonempty finite dictionary has physical two-query score at least the inverse
square of dictionary cardinality, at every real time, with no Pauli-weight factor. -/
theorem autonomous_adaptiveEigenframeTwoQueryScore_ge
    (p : (σ → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration σ) (FiniteQubitConfiguration σ) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport p H) (t : ℝ) :
    1 / (Fintype.card {P // p P} : ℝ) ^ 2 ≤
      adaptiveEigenframeTwoQueryScore (fun P : {P // p P} => P.1)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration σ)
            (FiniteQubitConfiguration σ) ℂ)))) := by
  exact adaptiveEigenframeTwoQueryScore_ge_card_sq_inv
    (fun P : {P // p P} => P.1) _
    (pauliDictionaryEnergyCoordinates p H)
    (pauliDictionaryEnergyCoordinates_ne_zero p H hH hsupport)
    (autonomousDictionaryPauliTransfer_fixes_energy p H hsupport t)

/-- If dictionary cardinality squared is below Hilbert dimension plus one, the permanent static
score is strictly larger than the exact Haar score. -/
theorem autonomous_adaptiveEigenframeTwoQueryScore_gt_haar
    {n : ℕ}
    (p : (Fin n → Option (Fin 3)) → Prop) [DecidablePred p]
    [Nonempty {P // p P}]
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport p H) (t : ℝ)
    (hsep : Fintype.card {P // p P} ^ 2 < 2 ^ n + 1) :
    1 / ((2 ^ n + 1 : ℕ) : ℝ) <
      adaptiveEigenframeTwoQueryScore (fun P : {P // p P} => P.1)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  have hM : 0 < (Fintype.card {P // p P} : ℝ) ^ 2 := by positivity
  have hsepR : (Fintype.card {P // p P} : ℝ) ^ 2 < ((2 ^ n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsep
  have hinv : 1 / ((2 ^ n + 1 : ℕ) : ℝ) <
      1 / (Fintype.card {P // p P} : ℝ) ^ 2 :=
    one_div_lt_one_div_of_lt hM hsepR
  exact hinv.trans_le
    (autonomous_adaptiveEigenframeTwoQueryScore_ge p H hH hsupport t)

/-! ## Fixed-cardinality Majorana dictionaries

The Jordan--Wigner image of a fixed-`q` Majorana monomial can have Pauli weight linear in system
size.  The adaptive eigenframe law nevertheless pays only for the number `choose (2n,q)` of source
monomials.  The algebraic core is a fixed-cardinality injectivity theorem for every Pauli-Majorana
frame: pairing with an index in a symmetric difference distinguishes the two monomials.
-/

/-- Pauli labels bundled with XOR as their additive law. -/
@[ext] structure MajoranaXorLabel (n : ℕ) where
  val : Fin n → Fin 4

instance {n : ℕ} : Zero (MajoranaXorLabel n) := ⟨⟨0⟩⟩

instance {n : ℕ} : Add (MajoranaXorLabel n) :=
  ⟨fun x y => ⟨QuantumAlg.pauliXor x.val y.val⟩⟩

instance {n : ℕ} : AddCommMonoid (MajoranaXorLabel n) where
  add_assoc x y z := by
    apply MajoranaXorLabel.ext
    funext k
    exact QuantumAlg.xor4_assoc _ _ _
  zero_add x := by
    apply MajoranaXorLabel.ext
    funext k
    exact QuantumAlg.xor4_zero_left _
  add_zero x := by
    apply MajoranaXorLabel.ext
    funext k
    exact QuantumAlg.xor4_zero_right _
  add_comm x y := by
    apply MajoranaXorLabel.ext
    funext k
    exact QuantumAlg.xor4_comm _ _
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl

/-- Symplectic pairing is additive for the XOR monoid. -/
def majoranaOmegaHom {n : ℕ} (a : Fin n → Fin 4) :
    MajoranaXorLabel n →+ ZMod 2 where
  toFun x := QuantumAlg.pauliOmega a x.val
  map_zero' := by
    change QuantumAlg.pauliOmega a (0 : Fin n → Fin 4) = 0
    rw [QuantumAlg.pauliOmega_comm, QuantumAlg.pauliOmega_zero_left]
  map_add' x y := QuantumAlg.pauliOmega_xor_right _ _ _

/-- Phase-free Pauli label of a product of distinct Majorana generators. -/
def majoranaWordFinFour {n : ℕ} (F : QuantumAlg.PauliMajoranaFrame n)
    (S : Finset (Fin (2 * n))) : Fin n → Fin 4 :=
  (∑ a ∈ S, (⟨F.v a⟩ : MajoranaXorLabel n)).val

/-- Pairing a generator with a Majorana word counts all other generators modulo two. -/
theorem majoranaOmega_wordFinFour {n : ℕ} (F : QuantumAlg.PauliMajoranaFrame n)
    (a : Fin (2 * n)) (S : Finset (Fin (2 * n))) :
    QuantumAlg.pauliOmega (F.v a) (majoranaWordFinFour F S) =
      ∑ b ∈ S, if a = b then 0 else 1 := by
  change (majoranaOmegaHom (F.v a))
      (∑ b ∈ S, (⟨F.v b⟩ : MajoranaXorLabel n)) = _
  rw [_root_.map_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  simp only [majoranaOmegaHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact F.omega a b

/-- Equivalent cardinal form of the Majorana-word pairing law. -/
theorem majoranaOmega_wordFinFour_eq_card_erase {n : ℕ}
    (F : QuantumAlg.PauliMajoranaFrame n) (a : Fin (2 * n))
    (S : Finset (Fin (2 * n))) :
    QuantumAlg.pauliOmega (F.v a) (majoranaWordFinFour F S) = (S.erase a).card := by
  rw [majoranaOmega_wordFinFour]
  calc
    (∑ b ∈ S, if a = b then (0 : ZMod 2) else 1) =
        ∑ b ∈ S, if b ≠ a then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hab : a = b <;> simp [hab, ne_comm]
    _ = (S.erase a).card := by rw [Finset.sum_boole, Finset.filter_ne']

/-- **Fixed-cardinality Majorana independence.** Distinct `q`-subsets have distinct phase-free
Pauli labels in every representation by pairwise anticommuting Pauli words. -/
theorem majoranaWordFinFour_injective_fixedCard {n q : ℕ}
    (F : QuantumAlg.PauliMajoranaFrame n) :
    Function.Injective
      (fun S : {S : Finset (Fin (2 * n)) // S.card = q} =>
        majoranaWordFinFour F S.1) := by
  intro S T hlabel
  apply Subtype.ext
  by_contra hST
  have hnotSubset : ¬S.1 ⊆ T.1 := by
    intro hsub
    apply hST
    exact Finset.eq_of_subset_of_card_le hsub (by simpa [S.2, T.2])
  simp only [Finset.not_subset] at hnotSubset
  obtain ⟨a, haS, haT⟩ := hnotSubset
  have homega := congrArg (fun P => QuantumAlg.pauliOmega (F.v a) P) hlabel
  rw [majoranaOmega_wordFinFour_eq_card_erase,
    majoranaOmega_wordFinFour_eq_card_erase, Finset.card_erase_of_mem haS,
    Finset.erase_eq_of_notMem haT, S.2, T.2] at homega
  have hqpos : 0 < q := by
    rw [← S.2, Finset.card_pos]
    exact ⟨a, haS⟩
  have hqsplit : q = q - 1 + 1 := by omega
  have homega' : ((q - 1 : ℕ) : ZMod 2) =
      ((q - 1 : ℕ) : ZMod 2) + 1 := by
    calc
      ((q - 1 : ℕ) : ZMod 2) = (q : ZMod 2) := homega
      _ = ((q - 1 + 1 : ℕ) : ZMod 2) := by rw [← hqsplit]
      _ = ((q - 1 : ℕ) : ZMod 2) + 1 := by norm_num
  have hzero_one : (0 : ZMod 2) = 1 := by
    apply add_left_cancel (a := ((q - 1 : ℕ) : ZMod 2))
    simpa only [add_zero] using homega'
  exact zero_ne_one hzero_one

/-- Inverse of the conventional `none, X, Y, Z` encoding by `0,1,2,3`. -/
def finFourPauliOption (a : Fin 4) : Option (Fin 3) :=
  if a = 0 then none
  else if a = 1 then some 0
  else if a = 2 then some 1
  else some 2

theorem finFourPauliOption_injective : Function.Injective finFourPauliOption := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [finFourPauliOption] at h ⊢

@[simp] theorem finFourPauliOption_zero : finFourPauliOption 0 = none := rfl

/-- Index type of `q`-body Majorana monomials on `n` qubits. -/
abbrev MajoranaQBodyIndex (n q : ℕ) :=
  {S : Finset (Fin (2 * n)) // S.card = q}

/-- Jordan--Wigner Pauli label of a fixed-`q` Majorana monomial. -/
def majoranaQBodyPauliLabel (n q : ℕ) (S : MajoranaQBodyIndex n q) :
    Fin n → Option (Fin 3) :=
  fun k => finFourPauliOption (majoranaWordFinFour (QuantumAlg.TFIM.frame n) S.1 k)

/-- Fixed-`q` Jordan--Wigner Majorana labels remain injective despite their long Pauli strings. -/
theorem majoranaQBodyPauliLabel_injective (n q : ℕ) :
    Function.Injective (majoranaQBodyPauliLabel n q) := by
  intro S T h
  apply majoranaWordFinFour_injective_fixedCard (QuantumAlg.TFIM.frame n)
  funext k
  apply finFourPauliOption_injective
  exact congrFun h k

/-- Predicate selecting the complete fixed-`q` Majorana dictionary. -/
def MajoranaQBodyDictionary (n q : ℕ) (P : Fin n → Option (Fin 3)) : Prop :=
  ∃ S : MajoranaQBodyIndex n q, majoranaQBodyPauliLabel n q S = P

noncomputable instance majoranaQBodyDictionaryDecidablePred (n q : ℕ) :
    DecidablePred (MajoranaQBodyDictionary n q) := Classical.decPred _

/-- Fixed-`q` source monomials and their Jordan--Wigner labels are equivalent finite types. -/
noncomputable def majoranaQBodyDictionaryEquiv (n q : ℕ) :
    MajoranaQBodyIndex n q ≃ {P // MajoranaQBodyDictionary n q P} where
  toFun S := ⟨majoranaQBodyPauliLabel n q S, ⟨S, rfl⟩⟩
  invFun P := Classical.choose P.2
  left_inv S := majoranaQBodyPauliLabel_injective n q
    (Classical.choose_spec
      (show MajoranaQBodyDictionary n q (majoranaQBodyPauliLabel n q S) from ⟨S, rfl⟩))
  right_inv P := by
    apply Subtype.ext
    exact Classical.choose_spec P.2

/-- Dictionary size is exactly the number of fixed-cardinality Majorana monomials. -/
theorem majoranaQBodyDictionary_card (n q : ℕ) :
    Fintype.card {P // MajoranaQBodyDictionary n q P} = Nat.choose (2 * n) q := by
  let e : {S : Finset (Fin (2 * n)) // S.card = q} ≃
      {S : Finset (Fin (2 * n)) //
        S ∈ (Finset.univ : Finset (Fin (2 * n))).powersetCard q} :=
    Equiv.subtypeEquivRight fun S => by simp [Finset.mem_powersetCard]
  rw [← Fintype.card_congr (majoranaQBodyDictionaryEquiv n q),
    Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard]
  simp

/-- Every admissible fixed-`q` Majorana dictionary is nonempty. -/
theorem majoranaQBodyDictionary_nonempty {n q : ℕ} (hq : q ≤ 2 * n) :
    Nonempty {P // MajoranaQBodyDictionary n q P} := by
  classical
  obtain ⟨S, _hSuniv, hScard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin (2 * n)))) (by simpa using hq)
  exact ⟨⟨majoranaQBodyPauliLabel n q ⟨S, hScard⟩, ⟨⟨S, hScard⟩, rfl⟩⟩⟩

/-- A nonempty even Majorana monomial never maps to the identity Pauli word. -/
theorem majoranaQBodyPauliLabel_ne_identity {n q : ℕ}
    (hqpos : 0 < q) (hqeven : Even q) (S : MajoranaQBodyIndex n q) :
    majoranaQBodyPauliLabel n q S ≠ pauliIdentityLabel n := by
  classical
  obtain ⟨a, ha⟩ : S.1.Nonempty := Finset.card_pos.mp (by simpa [S.2] using hqpos)
  have hword : majoranaWordFinFour (QuantumAlg.TFIM.frame n) S.1 ≠ 0 := by
    intro hzero
    have homega : QuantumAlg.pauliOmega ((QuantumAlg.TFIM.frame n).v a)
        (majoranaWordFinFour (QuantumAlg.TFIM.frame n) S.1) = 0 := by
      rw [hzero, QuantumAlg.pauliOmega_comm, QuantumAlg.pauliOmega_zero_left]
    rw [majoranaOmega_wordFinFour_eq_card_erase,
      Finset.card_erase_of_mem ha, S.2] at homega
    obtain ⟨k, hk⟩ := hqeven
    have hkpos : 0 < k := by omega
    have hodd : Odd (q - 1) := ⟨k - 1, by omega⟩
    have hone : ((q - 1 : ℕ) : ZMod 2) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr hodd
    rw [hone] at homega
    exact one_ne_zero homega
  intro hid
  apply hword
  funext k
  apply finFourPauliOption_injective
  simpa [majoranaQBodyPauliLabel, pauliIdentityLabel] using congrFun hid k

/-- Coefficient-parametrized Hermitian fixed-`q` Majorana Hamiltonian.  Physical phase conventions
are absorbed into the arbitrary real coefficients. -/
def majoranaQBodyHamiltonian {n q : ℕ} (c : MajoranaQBodyIndex n q → ℝ) :
    selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ) :=
  ∑ S, c S • finitePauliSelfAdjoint (majoranaQBodyPauliLabel n q S)

/-- The constructed Hamiltonian has support in exactly the declared fixed-`q` Majorana
dictionary. -/
theorem majoranaQBodyHamiltonian_hasDictionarySupport {n q : ℕ}
    (c : MajoranaQBodyIndex n q → ℝ) :
    HasPauliDictionarySupport (MajoranaQBodyDictionary n q)
      (majoranaQBodyHamiltonian c) := by
  intro P hP
  rw [majoranaQBodyHamiltonian, _root_.map_sum]
  simp only [map_smul]
  simp_rw [← finitePauliSelfAdjointBasis_apply,
    (finitePauliSelfAdjointBasis (Fin n)).repr_self]
  have hfun := Finsupp.coe_finsetSum Finset.univ
    (fun S : MajoranaQBodyIndex n q =>
      c S • Finsupp.single (majoranaQBodyPauliLabel n q S) (1 : ℝ))
  rw [show
    (∑ S : MajoranaQBodyIndex n q,
      c S • Finsupp.single (majoranaQBodyPauliLabel n q S) (1 : ℝ)) P =
      ∑ S : MajoranaQBodyIndex n q,
        (c S • Finsupp.single (majoranaQBodyPauliLabel n q S) (1 : ℝ)) P by
    have happ := congrFun hfun P
    simpa using happ]
  apply Finset.sum_eq_zero
  intro S _hS
  have hne : majoranaQBodyPauliLabel n q S ≠ P := fun h => hP ⟨S, h⟩
  simp [hne]

/-- Injectivity of Majorana labels makes the Hamiltonian nonzero exactly when its coefficient
vector is nonzero. -/
theorem majoranaQBodyHamiltonian_ne_zero {n q : ℕ}
    (c : MajoranaQBodyIndex n q → ℝ) (hc : c ≠ 0) :
    majoranaQBodyHamiltonian c ≠ 0 := by
  have hLI : LinearIndependent ℝ
      (fun S : MajoranaQBodyIndex n q =>
        finitePauliSelfAdjoint (majoranaQBodyPauliLabel n q S)) :=
    (finitePauliSelfAdjoint_linearIndependent (σ := Fin n)).comp
      (majoranaQBodyPauliLabel n q) (majoranaQBodyPauliLabel_injective n q)
  intro hzero
  apply hc
  funext S
  exact Fintype.linearIndependent_iff.mp hLI c hzero S

/-- Exact Haar benchmark for the complete even fixed-`q` Majorana eigenframe experiment. -/
theorem haar_majoranaQBody_adaptiveEigenframeScore_eq
    {n q : ℕ} (hn : 1 ≤ n) (hqpos : 0 < q) (hqeven : Even q) (hqle : q ≤ 2 * n) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        adaptiveEigenframeTwoQueryScore (majoranaQBodyPauliLabel n q)
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
      1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  letI : Nonempty (MajoranaQBodyIndex n q) := by
    obtain ⟨P⟩ := majoranaQBodyDictionary_nonempty hqle
    exact ⟨(majoranaQBodyDictionaryEquiv n q).symm P⟩
  exact haar_adaptiveEigenframeTwoQueryScore_eq hn (majoranaQBodyPauliLabel n q)
    (majoranaQBodyPauliLabel_ne_identity hqpos hqeven)

/-- Exact Haar benchmark on the image dictionary used by autonomous support compression. -/
theorem haar_majoranaQBodyDictionary_adaptiveEigenframeScore_eq
    {n q : ℕ} (hn : 1 ≤ n) (hqpos : 0 < q) (hqeven : Even q) (hqle : q ≤ 2 * n) :
    (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
        adaptiveEigenframeTwoQueryScore
          (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
          (V : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)
        ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
      1 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hqle
  apply haar_adaptiveEigenframeTwoQueryScore_eq hn
  intro P
  obtain ⟨S, hS⟩ := P.2
  rw [← hS]
  exact majoranaQBodyPauliLabel_ne_identity hqpos hqeven S

/-- **Permanent Majorana source-memory law.** Every nonzero autonomous Hamiltonian supported on
fixed even `q` Majorana monomials retains adaptive two-query score at least
`choose(2n,q)⁻²` at every real time, while Haar gives exactly `(2^n+1)⁻¹`. -/
theorem autonomous_majoranaQBody_adaptiveEigenframeScore_ge
    {n q : ℕ} (hqle : q ≤ 2 * n)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport (MajoranaQBodyDictionary n q) H)
    (t : ℝ) :
    1 / (Nat.choose (2 * n) q : ℝ) ^ 2 ≤
      adaptiveEigenframeTwoQueryScore
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  classical
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hqle
  simpa [majoranaQBodyDictionary_card] using
    (autonomous_adaptiveEigenframeTwoQueryScore_ge
      (MajoranaQBodyDictionary n q) H hH hsupport t)

/-- Coefficient-level form: no separate support or nonzero-Hamiltonian premise remains. -/
theorem autonomous_majoranaQBodyHamiltonian_adaptiveEigenframeScore_ge
    {n q : ℕ} (hqle : q ≤ 2 * n) (c : MajoranaQBodyIndex n q → ℝ) (hc : c ≠ 0)
    (t : ℝ) :
    1 / (Nat.choose (2 * n) q : ℝ) ^ 2 ≤
      adaptiveEigenframeTwoQueryScore
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (exp (t • ((-Complex.I) •
          (majoranaQBodyHamiltonian c :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))) :=
  autonomous_majoranaQBody_adaptiveEigenframeScore_ge hqle
    (majoranaQBodyHamiltonian c) (majoranaQBodyHamiltonian_ne_zero c hc)
    (majoranaQBodyHamiltonian_hasDictionarySupport c) t

/-- When the fixed-`q` Majorana source dictionary is smaller than the square root of Hilbert
dimension, its conserved physical score is permanently strictly above the Haar value. -/
theorem autonomous_majoranaQBody_adaptiveEigenframeScore_gt_haar
    {n q : ℕ} (hqle : q ≤ 2 * n)
    (H : selfAdjoint
      (Matrix (FiniteQubitConfiguration (Fin n))
        (FiniteQubitConfiguration (Fin n)) ℂ))
    (hH : H ≠ 0) (hsupport : HasPauliDictionarySupport (MajoranaQBodyDictionary n q) H)
    (t : ℝ) (hsep : Nat.choose (2 * n) q ^ 2 < 2 ^ n + 1) :
    1 / ((2 ^ n + 1 : ℕ) : ℝ) <
      adaptiveEigenframeTwoQueryScore
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (exp (t • ((-Complex.I) •
          (H : Matrix (FiniteQubitConfiguration (Fin n))
            (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  classical
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hqle
  apply autonomous_adaptiveEigenframeTwoQueryScore_gt_haar
    (p := MajoranaQBodyDictionary n q) (H := H) hH hsupport t
  simpa [majoranaQBodyDictionary_card] using hsep

/-- Coefficient-level strict Haar separation for every nonzero fixed-`q` Majorana Hamiltonian. -/
theorem autonomous_majoranaQBodyHamiltonian_adaptiveEigenframeScore_gt_haar
    {n q : ℕ} (hqle : q ≤ 2 * n) (c : MajoranaQBodyIndex n q → ℝ) (hc : c ≠ 0)
    (t : ℝ) (hsep : Nat.choose (2 * n) q ^ 2 < 2 ^ n + 1) :
    1 / ((2 ^ n + 1 : ℕ) : ℝ) <
      adaptiveEigenframeTwoQueryScore
        (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
        (exp (t • ((-Complex.I) •
          (majoranaQBodyHamiltonian c :
            Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)))) :=
  autonomous_majoranaQBody_adaptiveEigenframeScore_gt_haar hqle
    (majoranaQBodyHamiltonian c) (majoranaQBodyHamiltonian_ne_zero c hc)
    (majoranaQBodyHamiltonian_hasDictionarySupport c) t hsep

/-- For every fixed body order, the squared Majorana dictionary is eventually smaller than Hilbert
dimension.  This is an unconditional polynomial-versus-exponential theorem. -/
theorem eventually_majoranaQBodyDictionary_sq_lt_two_pow (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nat.choose (2 * n) q ^ 2 < 2 ^ n := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * q) / (2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt (2 * q) (by norm_num)
  have hsmall := hlim.eventually_lt_const
    (show (0 : ℝ) < 1 / (2 : ℝ) ^ (2 * q) by positivity)
  filter_upwards [hsmall] with n hn
  have hpolyR : (((2 * n) ^ (2 * q) : ℕ) : ℝ) < ((2 ^ n : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_pow, Nat.cast_pow,
      Nat.cast_ofNat]
    rw [div_lt_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) n)
      (pow_pos (by norm_num : (0 : ℝ) < 2) (2 * q))] at hn
    nlinarith
  have hchoose : Nat.choose (2 * n) q ≤ (2 * n) ^ q := Nat.choose_le_pow _ _
  calc
    Nat.choose (2 * n) q ^ 2 ≤ ((2 * n) ^ q) ^ 2 := by gcongr
    _ = (2 * n) ^ (2 * q) := by rw [← pow_mul]; congr 1; omega
    _ < 2 ^ n := by exact_mod_cast hpolyR

/-- Haar probability that a fixed-`q` Majorana dictionary reaches its conserved autonomous floor is
at most `choose(2n,q)^2/(2^n+1)`. -/
theorem haar_measureReal_majoranaQBody_score_ge_floor_le
    {n q : ℕ} (hn : 1 ≤ n) (hqpos : 0 < q) (hqeven : Even q) (hqle : q ≤ 2 * n) :
    (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
        {V | 1 / (Nat.choose (2 * n) q : ℝ) ^ 2 ≤
          adaptiveEigenframeTwoQueryScore
            (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)} ≤
      (Nat.choose (2 * n) q : ℝ) ^ 2 / ((2 ^ n + 1 : ℕ) : ℝ) := by
  classical
  letI : Nonempty {P // MajoranaQBodyDictionary n q P} :=
    majoranaQBodyDictionary_nonempty hqle
  have hlabel : ∀ P : {P // MajoranaQBodyDictionary n q P},
      P.1 ≠ pauliIdentityLabel n := by
    intro P
    obtain ⟨S, hS⟩ := P.2
    rw [← hS]
    exact majoranaQBodyPauliLabel_ne_identity hqpos hqeven S
  simpa [majoranaQBodyDictionary_card] using
    (haar_measureReal_adaptiveEigenframeScore_ge_card_inv_le hn
      (fun P : {P // MajoranaQBodyDictionary n q P} => P.1) hlabel)

/-- The Haar high-score upper bound vanishes for every fixed body order. -/
theorem tendsto_majoranaQBody_haarHighScoreBound_zero (q : ℕ) :
    Tendsto (fun n : ℕ =>
      (Nat.choose (2 * n) q : ℝ) ^ 2 / ((2 ^ n + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 * q) / (2 : ℝ) ^ n)
      atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt (2 * q) (by norm_num)
  have hmajorant : Tendsto (fun n : ℕ =>
      (((2 * n) ^ (2 * q) : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) atTop (nhds 0) := by
    have hmul := hbase.const_mul ((2 : ℝ) ^ (2 * q))
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_pow, mul_div_assoc,
      mul_zero] using hmul
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => by positivity
  · filter_upwards with n
    have hchoose : Nat.choose (2 * n) q ^ 2 ≤ (2 * n) ^ (2 * q) := by
      calc
        Nat.choose (2 * n) q ^ 2 ≤ ((2 * n) ^ q) ^ 2 := by
          gcongr
          exact Nat.choose_le_pow _ _
        _ = (2 * n) ^ (2 * q) := by rw [← pow_mul]; congr 1; omega
    have hchooseR : (Nat.choose (2 * n) q : ℝ) ^ 2 ≤
        (((2 * n) ^ (2 * q) : ℕ) : ℝ) := by exact_mod_cast hchoose
    have hpowpos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
    calc
      (Nat.choose (2 * n) q : ℝ) ^ 2 / ((2 ^ n + 1 : ℕ) : ℝ) ≤
          (((2 * n) ^ (2 * q) : ℕ) : ℝ) / ((2 ^ n + 1 : ℕ) : ℝ) := by
            exact div_le_div_of_nonneg_right hchooseR (by positivity)
      _ ≤ (((2 * n) ^ (2 * q) : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hpowpos (by norm_num)
  · exact hmajorant

/-- For fixed positive even `q`, Haar probability of imitating the permanent autonomous source
floor is eventually below every prescribed positive error probability. -/
theorem eventually_haar_majoranaQBody_score_ge_floor_measure_lt
    (q : ℕ) (hqpos : 0 < q) (hqeven : Even q) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))).real
          {V | 1 / (Nat.choose (2 * n) q : ℝ) ^ 2 ≤
            adaptiveEigenframeTwoQueryScore
              (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
              (V : Matrix (FiniteQubitConfiguration (Fin n))
                (FiniteQubitConfiguration (Fin n)) ℂ)} < δ := by
  have hratio := (tendsto_majoranaQBody_haarHighScoreBound_zero q).eventually_lt_const hδ
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop q, hratio]
    with n hn hnq hbound
  have hqle : q ≤ 2 * n := by omega
  exact (haar_measureReal_majoranaQBody_score_ge_floor_le
    hn hqpos hqeven hqle).trans_lt hbound

/-- **Asymptotic fixed-body Majorana/Haar separation.** For every fixed positive even body order,
all sufficiently large qubit counts simultaneously have the exact Haar score and permanent strict
separation for every nonzero autonomous Hamiltonian with that Majorana support, at every time. -/
theorem eventually_every_autonomous_majoranaQBody_score_gt_haar
    (q : ℕ) (hqpos : 0 < q) (hqeven : Even q) :
    ∀ᶠ n : ℕ in atTop,
      (∫ V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin n)) ℂ,
          adaptiveEigenframeTwoQueryScore
            (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
            (V : Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)
          ∂finiteUnitaryHaar (FiniteQubitConfiguration (Fin n))) =
          1 / ((2 ^ n + 1 : ℕ) : ℝ) ∧
        ∀ (H : selfAdjoint
            (Matrix (FiniteQubitConfiguration (Fin n))
              (FiniteQubitConfiguration (Fin n)) ℂ)),
          H ≠ 0 → HasPauliDictionarySupport (MajoranaQBodyDictionary n q) H →
          ∀ t : ℝ,
            1 / ((2 ^ n + 1 : ℕ) : ℝ) <
              adaptiveEigenframeTwoQueryScore
                (fun P : {P // MajoranaQBodyDictionary n q P} => P.1)
                (exp (t • ((-Complex.I) •
                  (H : Matrix (FiniteQubitConfiguration (Fin n))
                    (FiniteQubitConfiguration (Fin n)) ℂ)))) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop q,
    eventually_majoranaQBodyDictionary_sq_lt_two_pow q] with n hn hnq hsep
  have hqle : q ≤ 2 * n := by omega
  constructor
  · exact haar_majoranaQBodyDictionary_adaptiveEigenframeScore_eq
      hn hqpos hqeven hqle
  · intro H hH hsupport t
    exact autonomous_majoranaQBody_adaptiveEigenframeScore_gt_haar
      hqle H hH hsupport t (hsep.trans_le (Nat.le_add_right _ _))

end

end GaloisForLFunctions.HTGeometry
