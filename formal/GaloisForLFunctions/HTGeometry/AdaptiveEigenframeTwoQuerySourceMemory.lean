import GaloisForLFunctions.HTGeometry.LiteralTwoQueryHaarBenchmark
import GaloisForLFunctions.HTGeometry.TracelessLocalPauliTransferConservationLaw

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

open MeasureTheory MeasureTheory.Measure TopologicalSpace
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
  rw [pauliEigenframeExpectation]
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
  rw [dictionaryEigenframeMean, integral_div,
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
  rw [adaptiveEigenframeTwoQueryScore, integral_div,
    integral_finsetSum _ (fun output _ =>
      integrable_finsetSum _ (fun input _ => hint output input))]
  rw [Finset.sum_congr rfl fun output _ =>
    integral_finsetSum _ (fun input _ => hint output input)]
  rw [Finset.sum_congr rfl fun output _ =>
    Finset.sum_congr rfl fun input _ =>
      haar_dictionaryEigenframeMean_eq hn label hlabel output input]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
    nsmul_eq_mul, nsmul_eq_mul]
  have hM : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  field_simp

end

end GaloisForLFunctions.HTGeometry
