import GaloisForLFunctions.RHTower.MobiusDivisorParityDefectTransport

/-!
# Transverse compensation when only the retained head has reversed sign

If a prime merger preserves every nonempty retained orientation, contraction
of the complete geometric parity certificate is equivalent to one transverse
overlap comparison. The negative head cancels from that comparison. Every
nonempty prime-free label is retained in the complete transverse field.
The existence of a prime satisfying these conditions is not asserted.
-/

noncomputable section
open Finset
namespace RHTower

/-- Square root of the complete geometric parity certificate. -/
def mobiusDivisorParityRadius (M : ℕ) (P : Finset ℕ) : ℝ :=
  Real.sqrt (mobiusDivisorParityGoodEnergy M P) +
    Real.sqrt (mobiusDivisorParityDefectEnergy M P)

/-- All nonempty retained labels not containing the proposed next prime. -/
def mobiusDivisorTransverseLabels (M q : ℕ) : Finset (Finset ℕ) :=
  ((mobiusDivisorSelectionPrimes M).erase q).powerset.erase ∅

/-- Complete squared transverse field after the proposed prime differences. -/
def mobiusDivisorTransverseResidualEnergy (M : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ R ∈ mobiusDivisorTransverseLabels M q,
    (mobiusDivisorOrientedFibre M P R - mobiusDivisorOrientedFibre M P (insert q R))^2

/-- Complete inner product of the nonempty prime-free field and its prime partners. -/
def mobiusDivisorTransverseOverlap (M : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ R ∈ mobiusDivisorTransverseLabels M q,
    mobiusDivisorOrientedFibre M P R * mobiusDivisorOrientedFibre M P (insert q R)

private lemma transverse_mem {M q : ℕ} (hq : q ∈ mobiusDivisorSelectionPrimes M)
    {R : Finset ℕ} (hR : R ∈ mobiusDivisorTransverseLabels M q) :
    R ≠ ∅ ∧ q ∉ R ∧ R ∈ (mobiusDivisorSelectionPrimes M).powerset ∧
      insert q R ∈ (mobiusDivisorSelectionPrimes M).powerset := by
  obtain ⟨hne, hsub⟩ := mem_erase.mp hR
  have hs := mem_powerset.mp hsub
  have hqR : q ∉ R := fun h => (mem_erase.mp (hs h)).1 rfl
  have hsU : R ⊆ mobiusDivisorSelectionPrimes M := fun _ h => (mem_erase.mp (hs h)).2
  exact ⟨hne, hqR, mem_powerset.mpr hsU,
    mem_powerset.mpr (insert_subset hq hsU)⟩

private lemma sum_labels_head_pair (M q : ℕ) (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (f : Finset ℕ → ℝ) :
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, f R) =
      f ∅ + f {q} + ∑ R ∈ mobiusDivisorTransverseLabels M q, (f R + f (insert q R)) := by
  let U := (mobiusDivisorSelectionPrimes M).erase q
  have he : ∅ ∈ U.powerset := mem_powerset.mpr (empty_subset U)
  have h0 := sum_erase_add U.powerset f he
  have h1 := sum_erase_add U.powerset (fun R => f (insert q R)) he
  have hs : (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, f R) =
      (∑ R ∈ U.powerset, f R) + ∑ R ∈ U.powerset, f (insert q R) := by
    conv_lhs => rw [← insert_erase hq]
    exact sum_powerset_insert (notMem_erase q _) f
  rw [hs, ← h0, ← h1, insert_empty_eq, sum_add_distrib]
  dsimp [U, mobiusDivisorTransverseLabels]
  ring

/-- The radius squares to the complete energy plus its geometric parity reserve. -/
theorem mobiusDivisorParityRadius_sq (M : ℕ) (P : Finset ℕ) :
    (mobiusDivisorParityRadius M P)^2 = mobiusDivisorSelectionEnergy M P +
      2 * Real.sqrt (mobiusDivisorParityGoodEnergy M P) *
        Real.sqrt (mobiusDivisorParityDefectEnergy M P) := by
  have hg := Real.sq_sqrt (mobiusDivisorParityGoodEnergy_nonneg M P)
  have hd := Real.sq_sqrt (mobiusDivisorParityDefectEnergy_nonneg M P)
  have he := mobiusDivisorParityGoodEnergy_add_defect M P
  unfold mobiusDivisorParityRadius
  nlinarith

/-- Nonempty partner domination preserves a nonpositive head and all nonempty
orientations under an actual prime merger. -/
theorem mobiusDivisorHeadDefect_insert_preserves (M : ℕ) (P : Finset ℕ) (q : ℕ)
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hh : mobiusDivisorOrientedFibre M P ∅ ≤ 0)
    (hpos : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
      0 ≤ mobiusDivisorOrientedFibre M P R)
    (htrans : ∀ R ∈ mobiusDivisorTransverseLabels M q,
      mobiusDivisorOrientedFibre M P (insert q R) ≤ mobiusDivisorOrientedFibre M P R) :
    mobiusDivisorOrientedFibre M (insert q P) ∅ ≤ 0 ∧
      ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
        0 ≤ mobiusDivisorOrientedFibre M (insert q P) R := by
  have ha := hpos {q} (mem_powerset.mpr (singleton_subset_iff.mpr hq)) (singleton_ne_empty q)
  constructor
  · rw [mobiusDivisorOrientedFibre_insert M P ∅ q (notMem_empty q), insert_empty_eq]
    linarith
  · intro R hR hne
    by_cases hqR : q ∈ R
    · simp [mobiusDivisorOrientedFibre, mobiusDivisorSelectionFibre_insert, hqR]
    · have ht : R ∈ mobiusDivisorTransverseLabels M q := by
        apply mem_erase.mpr
        refine ⟨hne, mem_powerset.mpr ?_⟩
        intro r hr
        exact mem_erase.mpr ⟨fun he => hqR (he ▸ hr), mem_powerset.mp hR hr⟩
      rw [mobiusDivisorOrientedFibre_insert M P R q hqR]
      exact sub_nonneg.mpr (htrans R ht)

private lemma head_defect_decomposition (M : ℕ) (P : Finset ℕ) (q : ℕ)
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hh : mobiusDivisorOrientedFibre M P ∅ ≤ 0)
    (hpos : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
      0 ≤ mobiusDivisorOrientedFibre M P R)
    (htrans : ∀ R ∈ mobiusDivisorTransverseLabels M q,
      mobiusDivisorOrientedFibre M P (insert q R) ≤ mobiusDivisorOrientedFibre M P R) :
    let h := mobiusDivisorOrientedFibre M P ∅
    let a := mobiusDivisorOrientedFibre M P {q}
    let T := mobiusDivisorTransverseResidualEnergy M P q
    let C := mobiusDivisorTransverseOverlap M P q
    mobiusDivisorParityGoodEnergy M P = a^2 + T + 2*C ∧
    mobiusDivisorParityDefectEnergy M P = h^2 ∧
    mobiusDivisorParityGoodEnergy M (insert q P) = T ∧
    mobiusDivisorParityDefectEnergy M (insert q P) = (h-a)^2 := by
  dsimp only
  have ha := hpos {q} (mem_powerset.mpr (singleton_subset_iff.mpr hq)) (singleton_ne_empty q)
  have hnext := mobiusDivisorHeadDefect_insert_preserves M P q hq hh hpos htrans
  have hzero (R : Finset ℕ) : mobiusDivisorOrientedFibre M (insert q P) (insert q R) = 0 := by
    simp [mobiusDivisorOrientedFibre, mobiusDivisorSelectionFibre_insert]
  have hhead : mobiusDivisorOrientedFibre M (insert q P) ∅ =
      mobiusDivisorOrientedFibre M P ∅ - mobiusDivisorOrientedFibre M P {q} := by
    rw [mobiusDivisorOrientedFibre_insert M P ∅ q (notMem_empty q), insert_empty_eq]
  have hqzero : mobiusDivisorOrientedFibre M (insert q P) {q} = 0 := by
    simpa using hzero ∅
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mobiusDivisorParityGoodEnergy
    rw [sum_labels_head_pair M q hq, max_eq_right hh, max_eq_left ha]
    simp only [zero_pow (by omega : 2 ≠ 0), zero_add]
    unfold mobiusDivisorTransverseResidualEnergy mobiusDivisorTransverseOverlap
    rw [mul_sum, add_assoc, ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro R hR
    obtain ⟨hne, _, hRU, hqRU⟩ := transverse_mem hq hR
    have hins : insert q R ≠ ∅ := insert_ne_empty q R
    rw [max_eq_left (hpos R hRU hne), max_eq_left (hpos _ hqRU hins)]
    ring
  · unfold mobiusDivisorParityDefectEnergy
    rw [sum_labels_head_pair M q hq, max_eq_left (neg_nonneg.mpr hh),
      max_eq_right (neg_nonpos.mpr ha)]
    have hz : (∑ R ∈ mobiusDivisorTransverseLabels M q,
        ((max (-mobiusDivisorOrientedFibre M P R) 0)^2 +
        (max (-mobiusDivisorOrientedFibre M P (insert q R)) 0)^2)) = 0 := by
      apply sum_eq_zero
      intro R hR
      obtain ⟨hne, _, hRU, hqRU⟩ := transverse_mem hq hR
      rw [max_eq_right (neg_nonpos.mpr (hpos R hRU hne)),
        max_eq_right (neg_nonpos.mpr (hpos _ hqRU (insert_ne_empty q R)))]
      ring
    rw [hz]
    ring
  · unfold mobiusDivisorParityGoodEnergy
    rw [sum_labels_head_pair M q hq, max_eq_right hnext.1, hqzero]
    simp only [max_self, zero_pow (by omega : 2 ≠ 0), zero_add]
    apply sum_congr rfl
    intro R hR
    obtain ⟨hne, hqR, hRU, _⟩ := transverse_mem hq hR
    rw [max_eq_left (hnext.2 R hRU hne), hzero R]
    simp only [max_self, zero_pow (by omega : 2 ≠ 0), add_zero]
    rw [mobiusDivisorOrientedFibre_insert M P R q hqR]
  · unfold mobiusDivisorParityDefectEnergy
    rw [sum_labels_head_pair M q hq, max_eq_left (neg_nonneg.mpr hnext.1), hqzero]
    have hz : (∑ R ∈ mobiusDivisorTransverseLabels M q,
        ((max (-mobiusDivisorOrientedFibre M (insert q P) R) 0)^2 +
        (max (-mobiusDivisorOrientedFibre M (insert q P) (insert q R)) 0)^2)) = 0 := by
      apply sum_eq_zero
      intro R hR
      obtain ⟨hne, _, hRU, _⟩ := transverse_mem hq hR
      rw [max_eq_right (neg_nonpos.mpr (hnext.2 R hRU hne)), hzero R]
      norm_num
    rw [hz, hhead]
    simp
    ring

/-- Exact source comparison for contraction of the geometric parity certificate.
Only transverse overlap, residual energy and the selected singleton remain;
the magnitude of the nonpositive head cancels. -/
theorem mobiusDivisorHeadDefect_compensation_iff (M : ℕ) (P : Finset ℕ) (q : ℕ)
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hh : mobiusDivisorOrientedFibre M P ∅ ≤ 0)
    (hpos : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
      0 ≤ mobiusDivisorOrientedFibre M P R)
    (htrans : ∀ R ∈ mobiusDivisorTransverseLabels M q,
      mobiusDivisorOrientedFibre M P (insert q R) ≤ mobiusDivisorOrientedFibre M P R) :
    mobiusDivisorParityRadius M (insert q P) ≤ mobiusDivisorParityRadius M P ↔
      mobiusDivisorOrientedFibre M P {q} *
        Real.sqrt (mobiusDivisorTransverseResidualEnergy M P q) ≤
          mobiusDivisorTransverseOverlap M P q := by
  obtain ⟨hg, hd, hgn, hdn⟩ := head_defect_decomposition M P q hq hh hpos htrans
  have ha := hpos {q} (mem_powerset.mpr (singleton_subset_iff.mpr hq)) (singleton_ne_empty q)
  have hn : 0 ≤ mobiusDivisorTransverseResidualEnergy M P q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hsn := Real.sq_sqrt hn
  have hsg := Real.sq_sqrt (mobiusDivisorParityGoodEnergy_nonneg M P)
  have hr : 0 ≤ mobiusDivisorOrientedFibre M P {q} +
      Real.sqrt (mobiusDivisorTransverseResidualEnergy M P q) := add_nonneg ha (Real.sqrt_nonneg _)
  unfold mobiusDivisorParityRadius
  rw [hd, hgn, hdn, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonpos (show mobiusDivisorOrientedFibre M P ∅ -
      mobiusDivisorOrientedFibre M P {q} ≤ 0 by linarith), abs_of_nonpos hh]
  have hs : Real.sqrt (mobiusDivisorTransverseResidualEnergy M P q) -
      (mobiusDivisorOrientedFibre M P ∅ - mobiusDivisorOrientedFibre M P {q}) ≤
      Real.sqrt (mobiusDivisorParityGoodEnergy M P) - mobiusDivisorOrientedFibre M P ∅ ↔
      mobiusDivisorOrientedFibre M P {q} + Real.sqrt (mobiusDivisorTransverseResidualEnergy M P q) ≤
        Real.sqrt (mobiusDivisorParityGoodEnergy M P) := by constructor <;> intro h <;> linarith
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, hs, ← sq_le_sq₀ hr (Real.sqrt_nonneg _)]
  constructor <;> intro h <;> nlinarith only [h, hg, hsn, hsg]

end RHTower
