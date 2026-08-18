import GaloisForLFunctions.RHTower.RouteBDyadicCore
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells

namespace RHTower.Sieve

/-- A two-factor dyadic amplitude cell. -/
noncomputable def matomakiTeravainenAmplitudeCell
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) {J₁ J₂ : ℕ} (ij : Fin J₁ × Fin J₂) : Finset α :=
  S.filter fun q =>
    (2 : ℝ) ^ (ij.1 : ℕ) * V₁ ≤ F₁ q ∧
    F₁ q < (2 : ℝ) ^ ((ij.1 : ℕ) + 1) * V₁ ∧
    (2 : ℝ) ^ (ij.2 : ℕ) * V₂ ≤ F₂ q ∧
    F₂ q < (2 : ℝ) ^ ((ij.2 : ℕ) + 1) * V₂

/-- Logarithmic exponent of the lower edge of one dyadic amplitude cell. -/
noncomputable def matomakiTeravainenAmplitudeSigma
    (M V : ℝ) {J : ℕ} (i : Fin J) : ℝ :=
  -maynardAmplitude 0 M ((2 : ℝ) ^ (i : ℕ) * V)

theorem rpow_neg_matomakiTeravainenAmplitudeSigma
    {M V : ℝ} (hM : 1 < M) (hV : 0 < V) {J : ℕ} (i : Fin J) :
    M ^ (-matomakiTeravainenAmplitudeSigma M V i) =
      (2 : ℝ) ^ (i : ℕ) * V := by
  have hlevel : 0 < (2 : ℝ) ^ (i : ℕ) * V := by positivity
  simpa [matomakiTeravainenAmplitudeSigma] using
    (rpow_maynardAmplitude_sub_abscissa (c := (0 : ℝ)) hM hlevel)

/-- Every amplitude in a cell lies below twice its exact logarithmic lower edge. -/
theorem matomakiTeravainenAmplitudeCell_upper
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ : ℝ} (hM₁ : 1 < M₁) (hM₂ : 1 < M₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ} (ij : Fin J₁ × Fin J₂)
    {q : α} (hq : q ∈ matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij) :
    F₁ q ≤ 2 * M₁ ^ (-matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) ∧
      F₂ q ≤ 2 * M₂ ^ (-matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) := by
  rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hq
  rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₁ hV₁,
    rpow_neg_matomakiTeravainenAmplitudeSigma hM₂ hV₂]
  constructor
  · calc
      F₁ q ≤ (2 : ℝ) ^ ((ij.1 : ℕ) + 1) * V₁ := hq.2.2.1.le
      _ = 2 * ((2 : ℝ) ^ (ij.1 : ℕ) * V₁) := by rw [pow_succ]; ring
  · calc
      F₂ q ≤ (2 : ℝ) ^ ((ij.2 : ℕ) + 1) * V₂ := hq.2.2.2.2.le
      _ = 2 * ((2 : ℝ) ^ (ij.2 : ℕ) * V₂) := by rw [pow_succ]; ring

/-- The product of the two finite dyadic grids covers every point whose amplitudes lie between
their base thresholds and terminal dyadic caps. -/
theorem subset_biUnion_matomakiTeravainenAmplitudeCell
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {V₁ V₂ : ℝ} (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ}
    (hlow₁ : ∀ q ∈ S, V₁ ≤ F₁ q) (hlow₂ : ∀ q ∈ S, V₂ ≤ F₂ q)
    (hhigh₁ : ∀ q ∈ S, F₁ q < (2 : ℝ) ^ J₁ * V₁)
    (hhigh₂ : ∀ q ∈ S, F₂ q < (2 : ℝ) ^ J₂ * V₂) :
    S ⊆ (Finset.univ : Finset (Fin J₁ × Fin J₂)).biUnion
      (matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂) := by
  classical
  intro q hq
  have hratio₁ : 1 ≤ F₁ q / V₁ := (le_div_iff₀ hV₁).2 (by simpa using hlow₁ q hq)
  have hratio₂ : 1 ≤ F₂ q / V₂ := (le_div_iff₀ hV₂).2 (by simpa using hlow₂ q hq)
  have hratioHigh₁ : F₁ q / V₁ < (2 : ℝ) ^ J₁ :=
    (div_lt_iff₀ hV₁).2 (by simpa [mul_comm] using hhigh₁ q hq)
  have hratioHigh₂ : F₂ q / V₂ < (2 : ℝ) ^ J₂ :=
    (div_lt_iff₀ hV₂).2 (by simpa [mul_comm] using hhigh₂ q hq)
  obtain ⟨i, hiJ, hiLow, hiHigh⟩ :=
    _root_.RHTower.Sublevel.exists_dyadic_cover hratio₁ hratioHigh₁
  obtain ⟨j, hjJ, hjLow, hjHigh⟩ :=
    _root_.RHTower.Sublevel.exists_dyadic_cover hratio₂ hratioHigh₂
  let ij : Fin J₁ × Fin J₂ := (⟨i, hiJ⟩, ⟨j, hjJ⟩)
  rw [Finset.mem_biUnion]
  refine ⟨ij, Finset.mem_univ _, ?_⟩
  rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter]
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ hV₁).1 hiLow
  · exact (div_lt_iff₀ hV₁).1 hiHigh
  · exact (le_div_iff₀ hV₂).1 hjLow
  · exact (div_lt_iff₀ hV₂).1 hjHigh

/-- Indices of nonempty amplitude cells. Empty cells are discarded before uniform exponent bounds
are imposed. -/
noncomputable def matomakiTeravainenActiveAmplitudeIndices
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) (J₁ J₂ : ℕ) : Finset (Fin J₁ × Fin J₂) :=
  Finset.univ.filter fun ij =>
    (matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij).Nonempty

theorem subset_biUnion_matomakiTeravainenActiveAmplitudeIndices
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {V₁ V₂ : ℝ} (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ}
    (hlow₁ : ∀ q ∈ S, V₁ ≤ F₁ q) (hlow₂ : ∀ q ∈ S, V₂ ≤ F₂ q)
    (hhigh₁ : ∀ q ∈ S, F₁ q < (2 : ℝ) ^ J₁ * V₁)
    (hhigh₂ : ∀ q ∈ S, F₂ q < (2 : ℝ) ^ J₂ * V₂) :
    S ⊆ (matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂).biUnion
      (matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂) := by
  classical
  intro q hq
  have hcover := subset_biUnion_matomakiTeravainenAmplitudeCell hV₁ hV₂
    hlow₁ hlow₂ hhigh₁ hhigh₂ hq
  rw [Finset.mem_biUnion] at hcover ⊢
  obtain ⟨ij, _hij, hqij⟩ := hcover
  refine ⟨ij, ?_, hqij⟩
  simp only [matomakiTeravainenActiveAmplitudeIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨q, hqij⟩

/-- A factor exceeding `M^{-sigma₀}` in a cell below `2 M^{-sigma}` forces `sigma` to
lie within one logarithmic dyadic step of `sigma₀`. -/
theorem sigma_lt_add_log_two_div_log_of_rpow_lt_two_rpow
    {M sigma₀ sigma : ℝ} (hM : 1 < M)
    (h : M ^ (-sigma₀) < 2 * M ^ (-sigma)) :
    sigma < sigma₀ + Real.log 2 / Real.log M := by
  have hM0 : 0 < M := lt_trans zero_lt_one hM
  have hleft0 : 0 < M ^ (-sigma₀) := Real.rpow_pos_of_pos hM0 _
  have hrightFactor0 : 0 < M ^ (-sigma) := Real.rpow_pos_of_pos hM0 _
  have hlog := Real.log_lt_log hleft0 h
  rw [Real.log_rpow hM0, Real.log_mul (by norm_num) hrightFactor0.ne',
    Real.log_rpow hM0] at hlog
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hdiff : (sigma - sigma₀) * Real.log M < Real.log 2 := by linarith
  have hquot : sigma - sigma₀ < Real.log 2 / Real.log M :=
    (lt_div_iff₀ hlogM).2 hdiff
  linarith

/-- Every active cell inherits the paper's `min sigma_j` cap from the large-factor alternative,
with the exact dyadic logarithmic correction for each base. -/
theorem min_matomakiTeravainenAmplitudeSigma_le
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ sigma₀ : ℝ} (hM₁ : 1 < M₁) (hM₂ : 1 < M₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ}
    (hlarge : ∀ q ∈ S, M₁ ^ (-sigma₀) ≤ F₁ q ∨ M₂ ^ (-sigma₀) ≤ F₂ q)
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂) :
    min (matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1)
        (matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) ≤
      sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) := by
  rw [matomakiTeravainenActiveAmplitudeIndices, Finset.mem_filter] at hij
  obtain ⟨q, hqcell⟩ := hij.2
  have hqS : q ∈ S := by
    rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
    exact hqcell.1
  rcases hlarge q hqS with hlarge1 | hlarge2
  · have hstrict : M₁ ^ (-sigma₀) <
        2 * M₁ ^ (-matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) := by
      calc
        M₁ ^ (-sigma₀) ≤ F₁ q := hlarge1
        _ < (2 : ℝ) ^ ((ij.1 : ℕ) + 1) * V₁ := by
          rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
          exact hqcell.2.2.1
        _ = 2 * M₁ ^ (-matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) := by
          rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₁ hV₁, pow_succ]
          ring
    have hsigma := sigma_lt_add_log_two_div_log_of_rpow_lt_two_rpow hM₁ hstrict
    calc
      min (matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1)
          (matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2)
          ≤ matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 := min_le_left _ _
      _ ≤ sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) := by
        linarith [le_max_left (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂)]
  · have hstrict : M₂ ^ (-sigma₀) <
        2 * M₂ ^ (-matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) := by
      calc
        M₂ ^ (-sigma₀) ≤ F₂ q := hlarge2
        _ < (2 : ℝ) ^ ((ij.2 : ℕ) + 1) * V₂ := by
          rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
          exact hqcell.2.2.2.2
        _ = 2 * M₂ ^ (-matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) := by
          rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₂ hV₂, pow_succ]
          ring
    have hsigma := sigma_lt_add_log_two_div_log_of_rpow_lt_two_rpow hM₂ hstrict
    calc
      min (matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1)
          (matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2)
          ≤ matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 := min_le_right _ _
      _ ≤ sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂) := by
        linarith [le_max_right (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂)]

theorem matomakiTeravainenAmplitudeSigma_nonneg_of_level_le_one
    {M V : ℝ} (hM : 1 < M) (hV : 0 < V) {J : ℕ} (i : Fin J)
    (hlevel : (2 : ℝ) ^ (i : ℕ) * V ≤ 1) :
    0 ≤ matomakiTeravainenAmplitudeSigma M V i := by
  have hlevel0 : 0 < (2 : ℝ) ^ (i : ℕ) * V := by positivity
  have hloglevel : Real.log ((2 : ℝ) ^ (i : ℕ) * V) ≤ 0 :=
    Real.log_nonpos hlevel0.le hlevel
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hquot : Real.log ((2 : ℝ) ^ (i : ℕ) * V) / Real.log M ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hloglevel hlogM.le
  simp only [matomakiTeravainenAmplitudeSigma, maynardAmplitude, zero_add]
  linarith

theorem active_matomakiTeravainenAmplitudeSigma_nonneg
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ : ℝ} (hM₁ : 1 < M₁) (hM₂ : 1 < M₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ}
    (hF₁one : ∀ q ∈ S, F₁ q ≤ 1) (hF₂one : ∀ q ∈ S, F₂ q ≤ 1)
    {ij : Fin J₁ × Fin J₂}
    (hij : ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂) :
    0 ≤ matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1 ∧
      0 ≤ matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2 := by
  rw [matomakiTeravainenActiveAmplitudeIndices, Finset.mem_filter] at hij
  obtain ⟨q, hqcell⟩ := hij.2
  rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hqcell
  constructor
  · exact matomakiTeravainenAmplitudeSigma_nonneg_of_level_le_one hM₁ hV₁ ij.1
      (hqcell.2.1.trans (hF₁one q hqcell.1))
  · exact matomakiTeravainenAmplitudeSigma_nonneg_of_level_le_one hM₂ hV₂ ij.2
      (hqcell.2.2.2.1.trans (hF₂one q hqcell.1))

/-- Actual dyadic-cover form of the `T₂` estimate. The only analytic premise left is the Huxley
cardinality estimate on each explicitly constructed active cell; all covering, amplitude,
minimum-exponent, comparable-scale, and loss-absorption steps are discharged here. -/
theorem matomakiTeravainen_typeII_T2_dyadic_cover_power_saving
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {T M₁ M₂ K V₁ V₂ sigma₀ delta C : ℝ} {J₁ J₂ : ℕ}
    (hT0 : 0 < T) (hM₁ : 1 < M₁) (hM₂ : 1 < M₂) (hK : 1 ≤ K)
    (hT : T ≤ K * (M₁ * M₂))
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂)
    (hF₁0 : ∀ q, 0 ≤ F₁ q) (hF₂0 : ∀ q, 0 ≤ F₂ q)
    (hF₁one : ∀ q ∈ S, F₁ q ≤ 1) (hF₂one : ∀ q ∈ S, F₂ q ≤ 1)
    (hlow₁ : ∀ q ∈ S, V₁ ≤ F₁ q) (hlow₂ : ∀ q ∈ S, V₂ ≤ F₂ q)
    (hhigh₁ : ∀ q ∈ S, F₁ q < (2 : ℝ) ^ J₁ * V₁)
    (hhigh₂ : ∀ q ∈ S, F₂ q < (2 : ℝ) ^ J₂ * V₂)
    (hlarge : ∀ q ∈ S, M₁ ^ (-sigma₀) ≤ F₁ q ∨ M₂ ^ (-sigma₀) ≤ F₂ q)
    (hC : 0 ≤ C)
    (hcount : ∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂,
      ((matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij).card : ℝ) ≤
        C * T ^ (2 * min (matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1)
          (matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) - delta))
    (hbudget :
      ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂).card : ℝ) *
          (16 * C * K ^ (2 * (sigma₀ +
            max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂)))) ≤
        T ^ (delta / 2)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(delta / 2)) := by
  let I := matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V₁ V₂ J₁ J₂
  let cells : (Fin J₁ × Fin J₂) → Finset α := fun ij =>
    matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij
  let sigma₁ : Fin J₁ × Fin J₂ → ℝ := fun ij =>
    matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1
  let sigma₂ : Fin J₁ × Fin J₂ → ℝ := fun ij =>
    matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2
  let mu := sigma₀ + max (Real.log 2 / Real.log M₁) (Real.log 2 / Real.log M₂)
  have hcover : S ⊆ I.biUnion cells :=
    subset_biUnion_matomakiTeravainenActiveAmplitudeIndices hV₁ hV₂
      hlow₁ hlow₂ hhigh₁ hhigh₂
  have hsigma₁ : ∀ ij ∈ I, 0 ≤ sigma₁ ij := by
    intro ij hij
    exact (active_matomakiTeravainenAmplitudeSigma_nonneg hM₁ hM₂ hV₁ hV₂
      hF₁one hF₂one hij).1
  have hsigma₂ : ∀ ij ∈ I, 0 ≤ sigma₂ ij := by
    intro ij hij
    exact (active_matomakiTeravainenAmplitudeSigma_nonneg hM₁ hM₂ hV₁ hV₂
      hF₁one hF₂one hij).2
  have hmu : ∀ ij ∈ I, min (sigma₁ ij) (sigma₂ ij) ≤ mu := by
    intro ij hij
    exact min_matomakiTeravainenAmplitudeSigma_le hM₁ hM₂ hV₁ hV₂ hlarge hij
  have hamp₁ : ∀ ij ∈ I, ∀ q ∈ cells ij, F₁ q ≤ 2 * M₁ ^ (-sigma₁ ij) := by
    intro ij _hij q hq
    exact (matomakiTeravainenAmplitudeCell_upper hM₁ hM₂ hV₁ hV₂ ij hq).1
  have hamp₂ : ∀ ij ∈ I, ∀ q ∈ cells ij, F₂ q ≤ 2 * M₂ ^ (-sigma₂ ij) := by
    intro ij _hij q hq
    exact (matomakiTeravainenAmplitudeCell_upper hM₁ hM₂ hV₁ hV₂ ij hq).2
  apply matomakiTeravainen_typeII_covered_amplitude_cells_power_saving
    (I := I) (cells := cells) (S := S) (F₁ := F₁) (F₂ := F₂)
    (T := T) (M₁ := M₁) (M₂ := M₂) (K := K) (delta := delta) (C := C)
    (mu := mu) (sigma₁ := sigma₁) (sigma₂ := sigma₂)
    hcover hT0 hM₁.le hM₂.le hK hT hsigma₁ hsigma₂ hmu hC
  · exact hcount
  · exact hF₁0
  · exact hF₂0
  · exact hamp₁
  · exact hamp₂
  · exact hbudget

end RHTower.Sieve
