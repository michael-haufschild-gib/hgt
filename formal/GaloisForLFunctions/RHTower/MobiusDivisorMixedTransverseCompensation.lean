import GaloisForLFunctions.RHTower.MobiusDivisorHeadDefectCompensation

/-!
# Compensation retaining the newly created nonempty defects

An initially nonpositive head and nonnegative nonempty field need not keep
all nonempty signs under a prime merger. The complete positive and negative
transverse residuals give an exact replacement for that restriction.
The resulting comparison is a source identity, not a proof that suitable
mergers exist along a complete order.
-/

noncomputable section
open Finset
namespace RHTower

/-- Positive part of the complete nonempty transverse difference field. -/
def mobiusDivisorTransverseGoodEnergy (M : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ R ∈ mobiusDivisorTransverseLabels M q,
    (max (mobiusDivisorOrientedFibre M P R -
      mobiusDivisorOrientedFibre M P (insert q R)) 0)^2

/-- Negative part of the complete nonempty transverse difference field. -/
def mobiusDivisorTransverseDefectEnergy (M : ℕ) (P : Finset ℕ) (q : ℕ) : ℝ :=
  ∑ R ∈ mobiusDivisorTransverseLabels M q,
    (max (mobiusDivisorOrientedFibre M P (insert q R) -
      mobiusDivisorOrientedFibre M P R) 0)^2

private lemma transverse_mem {M q : ℕ} (hq : q ∈ mobiusDivisorSelectionPrimes M)
    {R : Finset ℕ} (hR : R ∈ mobiusDivisorTransverseLabels M q) :
    R ≠ ∅ ∧ q ∉ R ∧ R ∈ (mobiusDivisorSelectionPrimes M).powerset ∧
      insert q R ∈ (mobiusDivisorSelectionPrimes M).powerset := by
  obtain ⟨hne, hsub⟩ := mem_erase.mp hR
  have hs := mem_powerset.mp hsub
  have hqR : q ∉ R := fun h => (mem_erase.mp (hs h)).1 rfl
  have hsU : R ⊆ mobiusDivisorSelectionPrimes M := fun _ h => (mem_erase.mp (hs h)).2
  exact ⟨hne, hqR, mem_powerset.mpr hsU, mem_powerset.mpr (insert_subset hq hsU)⟩

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

private lemma split_difference_sq (x y : ℝ) :
    (max (x-y) 0)^2+(max (y-x) 0)^2+2*x*y=x^2+y^2 := by
  rcases le_total x y with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring

/-- Exact complete energy split, allowing arbitrary new nonempty sign defects. -/
theorem mobiusDivisorMixedTransverse_decomposition (M : ℕ) (P : Finset ℕ) (q : ℕ)
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hh : mobiusDivisorOrientedFibre M P ∅ ≤ 0)
    (hpos : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
      0 ≤ mobiusDivisorOrientedFibre M P R) :
    let h := mobiusDivisorOrientedFibre M P ∅
    let a := mobiusDivisorOrientedFibre M P {q}
    let T := mobiusDivisorTransverseGoodEnergy M P q
    let U := mobiusDivisorTransverseDefectEnergy M P q
    let C := mobiusDivisorTransverseOverlap M P q
    mobiusDivisorParityGoodEnergy M P = a^2+T+U+2*C ∧
    mobiusDivisorParityDefectEnergy M P = h^2 ∧
    mobiusDivisorParityGoodEnergy M (insert q P) = T ∧
    mobiusDivisorParityDefectEnergy M (insert q P) = (h-a)^2+U := by
  dsimp only
  have ha := hpos {q} (mem_powerset.mpr (singleton_subset_iff.mpr hq)) (singleton_ne_empty q)
  have hzero (R : Finset ℕ) : mobiusDivisorOrientedFibre M (insert q P) (insert q R) = 0 := by
    simp [mobiusDivisorOrientedFibre, mobiusDivisorSelectionFibre_insert]
  have hhead : mobiusDivisorOrientedFibre M (insert q P) ∅ =
      mobiusDivisorOrientedFibre M P ∅ - mobiusDivisorOrientedFibre M P {q} := by
    rw [mobiusDivisorOrientedFibre_insert M P ∅ q (notMem_empty q), insert_empty_eq]
  have hqzero : mobiusDivisorOrientedFibre M (insert q P) {q} = 0 := by
    simpa using hzero ∅
  have hheadneg : mobiusDivisorOrientedFibre M (insert q P) ∅ ≤ 0 := by
    rw [hhead]
    linarith only [hh,ha]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mobiusDivisorParityGoodEnergy
    rw [sum_labels_head_pair M q hq, max_eq_right hh, max_eq_left ha]
    simp only [zero_pow (by omega : 2 ≠ 0), zero_add]
    unfold mobiusDivisorTransverseGoodEnergy mobiusDivisorTransverseDefectEnergy
      mobiusDivisorTransverseOverlap
    rw [mul_sum]
    calc
      _ = (mobiusDivisorOrientedFibre M P {q})^2 +
          ∑ R ∈ mobiusDivisorTransverseLabels M q,
            ((max (mobiusDivisorOrientedFibre M P R-
              mobiusDivisorOrientedFibre M P (insert q R)) 0)^2+
             (max (mobiusDivisorOrientedFibre M P (insert q R)-
              mobiusDivisorOrientedFibre M P R) 0)^2+
             2*(mobiusDivisorOrientedFibre M P R*mobiusDivisorOrientedFibre M P (insert q R))) := by
        congr 1
        apply sum_congr rfl
        intro R hR
        obtain ⟨hne, _, hRU, hqRU⟩ := transverse_mem hq hR
        rw [max_eq_left (hpos R hRU hne), max_eq_left (hpos _ hqRU (insert_ne_empty q R))]
        nlinarith only [split_difference_sq (mobiusDivisorOrientedFibre M P R)
          (mobiusDivisorOrientedFibre M P (insert q R))]
      _ = _ := by rw [sum_add_distrib, sum_add_distrib]; ring
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
  · unfold mobiusDivisorParityGoodEnergy mobiusDivisorTransverseGoodEnergy
    rw [sum_labels_head_pair M q hq, max_eq_right hheadneg, hqzero]
    simp only [max_self, zero_pow (by omega : 2 ≠ 0), zero_add]
    apply sum_congr rfl
    intro R hR
    have hqR := (transverse_mem hq hR).2.1
    rw [hzero R, mobiusDivisorOrientedFibre_insert M P R q hqR]
    simp
  · unfold mobiusDivisorParityDefectEnergy mobiusDivisorTransverseDefectEnergy
    rw [sum_labels_head_pair M q hq, max_eq_left (neg_nonneg.mpr hheadneg), hqzero, hhead]
    simp only [neg_zero, max_self, zero_pow (by omega : 2 ≠ 0), add_zero, neg_sq]
    congr 1
    apply sum_congr rfl
    intro R hR
    have hqR := (transverse_mem hq hR).2.1
    rw [hzero R, mobiusDivisorOrientedFibre_insert M P R q hqR]
    simp only [neg_sub, neg_zero, max_self, zero_pow (by omega : 2 ≠ 0), add_zero]

/-- Exact head-dependent threshold for contraction, retaining every newly
created nonempty defect. No transverse partner-domination hypothesis is used. -/
theorem mobiusDivisorMixedTransverse_compensation_iff (M : ℕ) (P : Finset ℕ) (q : ℕ)
    (hq : q ∈ mobiusDivisorSelectionPrimes M)
    (hh : mobiusDivisorOrientedFibre M P ∅ ≤ 0)
    (hpos : ∀ R ∈ (mobiusDivisorSelectionPrimes M).powerset, R ≠ ∅ →
      0 ≤ mobiusDivisorOrientedFibre M P R) :
    let a := mobiusDivisorOrientedFibre M P {q}
    let b := -mobiusDivisorOrientedFibre M P ∅
    let T := mobiusDivisorTransverseGoodEnergy M P q
    let C := mobiusDivisorTransverseOverlap M P q
    let v := Real.sqrt (mobiusDivisorParityGoodEnergy M P)-Real.sqrt T
    mobiusDivisorParityRadius M (insert q P) ≤ mobiusDivisorParityRadius M P ↔
      Real.sqrt T*v-C ≤ b*(v-a) := by
  dsimp only
  obtain ⟨hg,hd,hgn,hdn⟩ := mobiusDivisorMixedTransverse_decomposition M P q hq hh hpos
  have hT : 0 ≤ mobiusDivisorTransverseGoodEnergy M P q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hU : 0 ≤ mobiusDivisorTransverseDefectEnergy M P q := sum_nonneg (fun _ _ => sq_nonneg _)
  have hC : 0 ≤ mobiusDivisorTransverseOverlap M P q := by
    apply sum_nonneg
    intro R hR
    obtain ⟨hne, _, hRU, hqRU⟩ := transverse_mem hq hR
    exact mul_nonneg (hpos R hRU hne) (hpos _ hqRU (insert_ne_empty q R))
  have hTle : mobiusDivisorTransverseGoodEnergy M P q ≤ mobiusDivisorParityGoodEnergy M P := by
    nlinarith only [hg,hU,hC,sq_nonneg (mobiusDivisorOrientedFibre M P {q})]
  have hst := Real.sqrt_le_sqrt hTle
  have hs := Real.sq_sqrt (mobiusDivisorParityGoodEnergy_nonneg M P)
  have ht := Real.sq_sqrt hT
  have hu := Real.sq_sqrt (show 0 ≤
      (mobiusDivisorOrientedFibre M P ∅-mobiusDivisorOrientedFibre M P {q})^2+
        mobiusDivisorTransverseDefectEnergy M P q by positivity)
  unfold mobiusDivisorParityRadius
  rw [hd,hgn,hdn,Real.sqrt_sq_eq_abs,abs_of_nonpos hh]
  have hright : 0 ≤ Real.sqrt (mobiusDivisorParityGoodEnergy M P)-
      Real.sqrt (mobiusDivisorTransverseGoodEnergy M P q)-mobiusDivisorOrientedFibre M P ∅ := by
    linarith only [hst,hh]
  have hmove :
      Real.sqrt (mobiusDivisorTransverseGoodEnergy M P q)+
        Real.sqrt ((mobiusDivisorOrientedFibre M P ∅-mobiusDivisorOrientedFibre M P {q})^2+
          mobiusDivisorTransverseDefectEnergy M P q) ≤
            Real.sqrt (mobiusDivisorParityGoodEnergy M P)+ -mobiusDivisorOrientedFibre M P ∅ ↔
      Real.sqrt ((mobiusDivisorOrientedFibre M P ∅-mobiusDivisorOrientedFibre M P {q})^2+
          mobiusDivisorTransverseDefectEnergy M P q) ≤
        Real.sqrt (mobiusDivisorParityGoodEnergy M P)-
          Real.sqrt (mobiusDivisorTransverseGoodEnergy M P q)-mobiusDivisorOrientedFibre M P ∅ := by
    constructor <;> intro h <;> linarith only [h]
  rw [hmove, ← sq_le_sq₀ (Real.sqrt_nonneg _) hright]
  constructor <;> intro h <;> nlinarith only [h,hg,hs,ht,hu]

private lemma exists_head_shift_iff (a U v : ℝ) (ha : 0≤a) (hU : 0≤U) (hv : 0≤v) :
    (∃ b : ℝ, 0≤b ∧ Real.sqrt ((a+b)^2+U)≤b+v) ↔
      a<v ∨ (U=0 ∧ a≤v) := by
  constructor
  · rintro ⟨b,hb,h⟩
    have hs := Real.sq_sqrt (show 0≤(a+b)^2+U by positivity)
    have hr := Real.sqrt_nonneg ((a+b)^2+U)
    have hav : a≤v := by
      by_contra hn
      have hlt : v<a := lt_of_not_ge hn
      nlinarith only [h,hs,hr,hb,ha,hv,hlt,hU]
    rcases lt_or_eq_of_le hav with hlt | he
    · exact Or.inl hlt
    · right
      refine ⟨?_,hav⟩
      rw [← he] at h
      nlinarith only [h,hs,hr,hb,ha,hU]
  · rintro (hlt | ⟨rfl,hav⟩)
    · let b := (a^2+U)/(2*(v-a))
      have hb : 0≤b := div_nonneg (by positivity) (by linarith)
      have he : 2*b*(v-a)=a^2+U := by
        dsimp [b]
        field_simp [(sub_pos.mpr hlt).ne']
      refine ⟨b,hb,?_⟩
      have hs := Real.sq_sqrt (show 0≤(a+b)^2+U by positivity)
      have hr := Real.sqrt_nonneg ((a+b)^2+U)
      nlinarith only [hs,hr,hb,hv,he,sq_nonneg v]
    · refine ⟨0,le_rfl,?_⟩
      simpa only [add_zero,zero_add,Real.sqrt_sq ha] using hav

/-- Sharp classification of a frozen transverse field's capacity for head repair.
A positive new transverse defect requires a strict overlap margin; equality
cannot be paid by any finite nonpositive head. This does not assert that an
arithmetic prime schedule can choose the head independently of the field. -/
theorem mixedTransverseHeadRepair_iff (a T U C : ℝ)
    (ha : 0≤a) (hT : 0≤T) (hU : 0≤U) (hC : 0≤C) :
    (∃ b : ℝ, 0≤b ∧ Real.sqrt T+Real.sqrt ((a+b)^2+U)≤
      b+Real.sqrt (a^2+T+U+2*C)) ↔
      2*a*Real.sqrt T<U+2*C ∨ (U=0 ∧ a*Real.sqrt T≤C) := by
  let s := Real.sqrt (a^2+T+U+2*C)
  let t := Real.sqrt T
  have hs : s^2=a^2+T+U+2*C := Real.sq_sqrt (by positivity)
  have ht : t^2=T := Real.sq_sqrt hT
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hts : t ≤ s := Real.sqrt_le_sqrt (by nlinarith only [hU,hC,sq_nonneg a])
  have he : (∃ b : ℝ, 0≤b ∧ Real.sqrt T+Real.sqrt ((a+b)^2+U)≤
      b+Real.sqrt (a^2+T+U+2*C)) ↔
      (∃ b : ℝ, 0≤b ∧ Real.sqrt ((a+b)^2+U)≤b+(s-t)) := by
    change (∃ b : ℝ, 0≤b ∧ t+Real.sqrt ((a+b)^2+U)≤b+s) ↔ _
    constructor <;> rintro ⟨b,hb,h⟩ <;> refine ⟨b,hb,?_⟩ <;> linarith only [h]
  rw [he,exists_head_shift_iff a U (s-t) ha hU (sub_nonneg.mpr hts)]
  have hstrict : a < s-t ↔ 2*a*t<U+2*C := by
    constructor <;> intro h <;> nlinarith only [h,hs,ht,hs0,ht0,ha]
  have hequal : (U=0 ∧ a ≤ s-t) ↔ (U=0 ∧ a*t≤C) := by
    constructor <;> rintro ⟨hzero,h⟩ <;> refine ⟨hzero,?_⟩ <;>
      nlinarith only [h,hs,ht,hs0,ht0,ha,hzero]
  exact or_congr hstrict hequal

end RHTower
