/-
# Chen--Gupta--Li Lemma 4.5 fibrewise zero-mode row bound

Carries out the closed character case split for a single zero-frequency
off-diagonal row triple.  Character orthogonality makes every unequal-character
configuration vanish exactly.  In the surviving configuration, the existing
fibrewise separation theorem supplies arbitrary reciprocal decay on one time
difference, while the other two coordinates receive the order-zero bound.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45FibreZeroMode

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- Three row indices with all consecutive row characters equal. -/
def CGLLemma45EqualCharacterRowTriple (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :=
  {rst : Fin R × Fin R × Fin R //
    (rows rst.1).character = (rows rst.2.1).character ∧
      (rows rst.2.1).character = (rows rst.2.2).character}

/-- Three row indices whose first character pair agrees and second does not. -/
def CGLLemma45SecondCharacterUnequalRowTriple (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :=
  {rst : Fin R × Fin R × Fin R //
    (rows rst.1).character = (rows rst.2.1).character ∧
      (rows rst.2.1).character ≠ (rows rst.2.2).character}

/-- Three row indices whose first character pair does not agree. -/
def CGLLemma45FirstCharacterUnequalRowTriple (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value) :=
  {rst : Fin R × Fin R × Fin R //
    (rows rst.1).character ≠ (rows rst.2.1).character}

/-- Exact value of a zero-mode row term in the only nonvanishing character
configuration. -/
theorem cglLemma45ZeroModeRowTerm_eq_totient_cube_mul
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (u : CGLLemma45EqualCharacterRowTriple Q R rows) :
    cglLemma45ZeroModeRowTerm w N Q R rows u.1 =
      (Q.value.totient : ℂ) ^ (3 : ℕ) *
        cglLemma45ZeroModeTripleAnalyticAmplitude w N Q
          ((rows u.1.1).time - (rows u.1.2.1).time)
          ((rows u.1.2.1).time - (rows u.1.2.2).time)
          ((rows u.1.2.2).time - (rows u.1.1).time) := by
  have h31 : (rows u.1.2.2).character = (rows u.1.1).character :=
    u.2.2.symm.trans u.2.1.symm
  unfold cglLemma45ZeroModeRowTerm
  rw [cglLemma45ZeroModeTripleCharacterFactor_eq_indicator]
  unfold cglLemma45ZeroModeTripleCharacterIndicator
  rw [if_pos u.2.1, if_pos u.2.2, if_pos h31]
  ring

/-- A row term vanishes when its second character pair is unequal. -/
theorem cglLemma45ZeroModeRowTerm_eq_zero_of_second_character_ne
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (u : CGLLemma45SecondCharacterUnequalRowTriple Q R rows) :
    cglLemma45ZeroModeRowTerm w N Q R rows u.1 = 0 := by
  unfold cglLemma45ZeroModeRowTerm
  rw [cglLemma45ZeroModeTripleCharacterFactor_eq_indicator]
  unfold cglLemma45ZeroModeTripleCharacterIndicator
  rw [if_pos u.2.1, if_neg u.2.2]
  ring

/-- A row term vanishes when its first character pair is unequal. -/
theorem cglLemma45ZeroModeRowTerm_eq_zero_of_first_character_ne
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (Q : CGLPositiveModulus) (R : ℕ)
    (rows : Fin R → CGLCharacterDyadicRowData Q.value)
    (u : CGLLemma45FirstCharacterUnequalRowTriple Q R rows) :
    cglLemma45ZeroModeRowTerm w N Q R rows u.1 = 0 := by
  unfold cglLemma45ZeroModeRowTerm
  rw [cglLemma45ZeroModeTripleCharacterFactor_eq_indicator]
  unfold cglLemma45ZeroModeTripleCharacterIndicator
  rw [if_neg u.2]
  ring

/-- Exact surviving-character rewrite for a fibrewise packet row triple. -/
theorem cglLemma45FibreEqualCharacterRowTerm_eq
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (u : CGLLemma45FibreEqualCharacterOffDiagonalTriple P) :
    cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) u.1 =
      ((cglLemma45FibreModulus q).value.totient : ℂ) ^ (3 : ℕ) *
        cglLemma45ZeroModeTripleAnalyticAmplitude w N (cglLemma45FibreModulus q)
          (P.ordinate u.1.1 - P.ordinate u.1.2.1)
          (P.ordinate u.1.2.1 - P.ordinate u.1.2.2)
          (P.ordinate u.1.2.2 - P.ordinate u.1.1) := by
  rcases u with ⟨rst, hnot, h12, h23⟩
  have h12rows : (cglLemma45FibreRows P rst.1).character =
      (cglLemma45FibreRows P rst.2.1).character := h12
  have h23rows : (cglLemma45FibreRows P rst.2.1).character =
      (cglLemma45FibreRows P rst.2.2).character := h23
  let v : CGLLemma45EqualCharacterRowTriple (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) := ⟨rst, h12rows, h23rows⟩
  simpa only [cglLemma45FibreRows] using
    cglLemma45ZeroModeRowTerm_eq_totient_cube_mul w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) v

/-- A non-all-equal finite row triple. -/
def CGLLemma45FibreOffDiagonalTriple (R : ℕ) :=
  {rst : Fin R × Fin R × Fin R // ¬ (rst.1 = rst.2.1 ∧ rst.2.1 = rst.2.2)}

/-- A fixed finite enumeration of the certified off-diagonal row triples. -/
@[reducible] noncomputable def cglLemma45FibreOffDiagonalTripleFintype (R : ℕ) :
    Fintype (CGLLemma45FibreOffDiagonalTriple R) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Cardinality of the certified off-diagonal cubic-row carrier. -/
noncomputable def cglLemma45FibreOffDiagonalTripleCard (R : ℕ) : ℕ :=
  @Fintype.card (CGLLemma45FibreOffDiagonalTriple R)
    (cglLemma45FibreOffDiagonalTripleFintype R)

/-- The non-all-equal cubic-row carrier injects into all `R³` row triples. -/
theorem cglLemma45FibreOffDiagonalTriple_card_le (R : ℕ) :
    cglLemma45FibreOffDiagonalTripleCard R ≤ R ^ (3 : ℕ) := by
  letI : Fintype (CGLLemma45FibreOffDiagonalTriple R) :=
    cglLemma45FibreOffDiagonalTripleFintype R
  change Fintype.card (CGLLemma45FibreOffDiagonalTriple R) ≤ R ^ (3 : ℕ)
  calc
    Fintype.card (CGLLemma45FibreOffDiagonalTriple R) ≤
        Fintype.card (Fin R × Fin R × Fin R) :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = R ^ (3 : ℕ) := by simp [pow_three]

/-- Explicit bound for one zero-frequency row term after three complete
character sums. -/
def cglLemma45FibreZeroModeRowBound {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) : ℝ :=
  ((cglLemma45FibreModulus q).value.totient : ℝ) ^ (3 : ℕ) *
    cglLemma45FibreTripleDecayBudget P w N n

/-- The explicit zero-mode row budget is nonnegative. -/
theorem cglLemma45FibreZeroModeRowBound_nonneg
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    0 ≤ cglLemma45FibreZeroModeRowBound P w N n := by
  unfold cglLemma45FibreZeroModeRowBound cglLemma45FibreTripleDecayBudget
  apply mul_nonneg
  · positivity
  · apply mul_nonneg
    · exact mul_nonneg
        (mul_nonneg (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
          (div_nonneg (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump n)
            (pow_nonneg P.spacing_pos.le _)))
        (mul_nonneg (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
          (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0))
    · exact mul_nonneg
        (cglAffineFourierScale_pos N (cglLemma45FibreModulus q)).le
        (cglLogFourierAmplitudeAllOrderBudget_nonneg w.toCGLSmoothBump 0)

/-- **CGL Lemma 4.5, fibrewise zero-mode row bound.** Every non-all-equal
row triple is either killed by character orthogonality or has equal characters;
in the latter case the fibre separation supplies arbitrary reciprocal decay. -/
theorem norm_cglLemma45FibreOffDiagonalZeroModeRow_le
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ)
    (u : CGLLemma45FibreOffDiagonalTriple R) :
    ‖cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) u.1‖ ≤
      cglLemma45FibreZeroModeRowBound P w N n := by
  rcases u with ⟨rst, hnot⟩
  have hboundnonneg : 0 ≤ cglLemma45FibreZeroModeRowBound P w N n :=
    cglLemma45FibreZeroModeRowBound_nonneg P w N n
  by_cases h12 : P.character rst.1 = P.character rst.2.1
  · by_cases h23 : P.character rst.2.1 = P.character rst.2.2
    · let v : CGLLemma45FibreEqualCharacterOffDiagonalTriple P := ⟨rst, hnot, h12, h23⟩
      rw [cglLemma45FibreEqualCharacterRowTerm_eq P w N v, norm_mul, norm_pow, norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_cglLemma45FibreEqualCharacterOffDiagonalTriple_analytic_le P w N n v) (by positivity)
    · have h12rows : (cglLemma45FibreRows P rst.1).character =
          (cglLemma45FibreRows P rst.2.1).character := h12
      have h23rows : (cglLemma45FibreRows P rst.2.1).character ≠
          (cglLemma45FibreRows P rst.2.2).character := h23
      let v : CGLLemma45SecondCharacterUnequalRowTriple (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) := ⟨rst, h12rows, h23rows⟩
      have hzero : cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) rst = 0 :=
        cglLemma45ZeroModeRowTerm_eq_zero_of_second_character_ne w N
          (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) v
      rw [hzero]
      simpa using hboundnonneg
  · have h12rows : (cglLemma45FibreRows P rst.1).character ≠
        (cglLemma45FibreRows P rst.2.1).character := h12
    let v : CGLLemma45FirstCharacterUnequalRowTriple (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) := ⟨rst, h12rows⟩
    have hzero : cglLemma45ZeroModeRowTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) rst = 0 :=
      cglLemma45ZeroModeRowTerm_eq_zero_of_first_character_ne w N
        (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) v
    rw [hzero]
    simpa using hboundnonneg

end RHTower
