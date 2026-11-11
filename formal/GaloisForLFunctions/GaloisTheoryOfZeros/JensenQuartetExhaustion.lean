import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros
import GaloisForLFunctions.FiniteFreeProbability.BulkHyperbolicity

/-!
# Quartet exhaustion of the off-line divisor

The centered Jensen equations inherit conjugation and negation. Positivity of
the Riemann-kernel moments excludes nonzero imaginary roots, so every non-real
root belongs to a four-point orbit, with its full algebraic multiplicity.

Counting one open quadrant therefore divides the non-real census by four at
every degree. These quadrant counts are monotone and exhaust the entire
off-line divisor, including the case of infinitely many off-line zeros.
-/

noncomputable section

open Polynomial Complex Filter Topology
open FiniteFreeProbability RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The moment polynomial is strictly positive at every positive argument. -/
theorem centered_jensenMass_pos (d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < jensenMass (xiMoment (1 / 2)) d t := by
  have hterm : ∀ k ∈ Finset.range (d + 1),
      0 ≤ (d.choose k : ℝ) * t ^ (d - k) * xiMoment (1 / 2) k := by
    intro k _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.le _))
      (xiMoment_nonneg le_rfl k)
  have hle := Finset.single_le_sum hterm (Finset.mem_range.mpr (Nat.succ_pos d) :
    0 ∈ Finset.range (d + 1))
  have hpos : 0 < t ^ d * xiMoment (1 / 2) 0 :=
    mul_pos (pow_pos ht _) (xiMoment_zero_pos _)
  have hle' : t ^ d * xiMoment (1 / 2) 0 ≤
      jensenMass (xiMoment (1 / 2)) d t := by
    simpa only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
      ← jensenMass] using hle
  exact hpos.trans_le hle'

/-- No centered Jensen equation has a nonzero purely imaginary root. -/
theorem centered_jensen_no_imaginary_root (d : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (xiJensen (1 / 2) d).eval (I * t) ≠ 0 := by
  have hpos : ∀ u : ℝ, 0 < u → (xiJensen (1 / 2) d).eval (I * u) ≠ 0 := by
    intro u hu
    rw [eval_xiJensen_I_mul]
    exact mul_ne_zero (pow_ne_zero _ I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (centered_jensenMass_pos d hu).ne')
  rcases lt_or_gt_of_ne ht with ht | ht
  · intro hz
    apply hpos (-t) (neg_pos.mpr ht)
    rw [Complex.ofReal_neg, mul_neg, eval_xiJensen_half_neg, hz, mul_zero]
  · exact hpos t ht

private theorem centered_roots_conj (d : ℕ) :
    (xiJensen (1 / 2) d).roots.map (starRingEnd ℂ) =
      (xiJensen (1 / 2) d).roots := by
  have hpoly : (xiJensen (1 / 2) d).map (starRingEnd ℂ) =
      xiJensen (1 / 2) d := by
    rw [xiJensen, mk_xiShiftCoeff_half, jensenRev_xiSeries, Polynomial.map_map]
    congr 1
    ext x
    exact Complex.conj_ofReal x
  rw [← Polynomial.roots_map (IsAlgClosed.splits _) (starRingEnd ℂ), hpoly]

private theorem centered_root_re_ne_zero (d : ℕ) {z : ℂ}
    (hz : z ∈ (xiJensen (1 / 2) d).roots) (him : z.im ≠ 0) : z.re ≠ 0 := by
  intro hre
  have heq : z = I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  exact centered_jensen_no_imaginary_root d him
    (by rw [← heq]; exact (Polynomial.mem_roots'.mp hz).2)

/-- One representative, with multiplicity, from each non-real symmetry orbit. -/
def jensenQuartetCount (d : ℕ) : ℕ :=
  ((xiJensen (1 / 2) d).roots.filter fun z => 0 < z.re ∧ 0 < z.im).card

/-- The full non-real census is exactly four times the quadrant census. -/
theorem jensenNonrealCount_eq_four_mul (d : ℕ) :
    jensenNonrealCount d = 4 * jensenQuartetCount d := by
  classical
  let M := (xiJensen (1 / 2) d).roots
  have hconj : M.map (starRingEnd ℂ) = M := centered_roots_conj d
  have hneg : M.map (fun z => -z) = M := roots_xiJensen_half_map_neg d
  have hhor : M.map (fun z => -(starRingEnd ℂ) z) = M := by
    rw [← Multiset.map_map, hconj, hneg]
  have hv : (M.filter fun z => z.im < 0).card =
      (M.filter fun z => 0 < z.im).card := by
    conv_lhs => rw [← hconj]
    rw [Multiset.filter_map, Multiset.card_map]
    simp only [Function.comp_apply, Complex.conj_im, neg_lt_zero]
  have hh : (M.filter fun z => z.re < 0 ∧ 0 < z.im).card =
      (M.filter fun z => 0 < z.re ∧ 0 < z.im).card := by
    conv_lhs => rw [← hhor]
    rw [Multiset.filter_map, Multiset.card_map]
    simp only [Function.comp_apply, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im, neg_neg, neg_lt_zero]
  have hsplit : M.filter (fun z => z.im ≠ 0) =
      M.filter (fun z => 0 < z.im) + M.filter (fun z => z.im < 0) := by
    ext z
    rcases lt_trichotomy z.im 0 with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, h.ne', not_lt_of_ge h.le]
  have hupper : M.filter (fun z => 0 < z.im) =
      M.filter (fun z => 0 < z.re ∧ 0 < z.im) +
        M.filter (fun z => z.re < 0 ∧ 0 < z.im) := by
    ext z
    by_cases hz : z ∈ M
    · by_cases hi : 0 < z.im
      · have hr := centered_root_re_ne_zero d hz hi.ne'
        rcases lt_or_gt_of_ne hr with hr | hr
        · simp [hi, hr, not_lt_of_ge hr.le]
        · simp [hi, hr, not_lt_of_ge hr.le]
      · simp [hi]
    · simp [Multiset.count_eq_zero_of_notMem hz]
  have hc := congrArg Multiset.card hsplit
  have hu := congrArg Multiset.card hupper
  simp only [Multiset.card_add, hv, hh] at hc hu
  rw [jensenNonrealCount, jensenQuartetCount, ← mk_xiShiftCoeff_half]
  change (M.filter fun z => z.im ≠ 0).card =
    4 * (M.filter fun z => 0 < z.re ∧ 0 < z.im).card
  omega

/-- Conjugate-pair parity is identically even at every degree. -/
theorem even_jensen_conjugate_pair_count (d : ℕ) :
    Even (jensenNonrealCount d / 2) := by
  rw [jensenNonrealCount_eq_four_mul]
  exact ⟨jensenQuartetCount d, by omega⟩

/-- The parity character used in the discriminant sign is always trivial. -/
theorem jensen_conjugation_parity (d : ℕ) :
    (-1 : ℤ) ^ (jensenNonrealCount d / 2) = 1 :=
  (even_jensen_conjugate_pair_count d).neg_one_pow

/-- Quotienting the symmetry keeps an increasing census. -/
theorem jensenQuartetCount_mono : Monotone jensenQuartetCount := by
  intro d e hde
  have h := jensenNonrealCount_mono hde
  rw [jensenNonrealCount_eq_four_mul, jensenNonrealCount_eq_four_mul] at h
  omega

/-- The quartet counts exhaust the full divisor, with infinity retained. -/
theorem iSup_four_mul_jensenQuartetCount :
    (⨆ d, ((4 * jensenQuartetCount d : ℕ) : ℕ∞)) =
      {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard := by
  simp only [← jensenNonrealCount_eq_four_mul]
  exact iSup_jensenNonrealCount

/-- Any finite bound on the quartet census is exactly a bound on the full divisor. -/
theorem offLine_count_le_iff_quartet_count (m : ℕ) :
    {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard ≤ (4 * m : ℕ) ↔
      ∀ d, jensenQuartetCount d ≤ m := by
  rw [encard_offLine_le_iff_forall]
  simp only [jensenNonrealCount_eq_four_mul]
  constructor <;> intro h d <;> have hd := h d <;> omega

/-- An infinite off-line divisor forces the quadrant counts to diverge. -/
theorem jensenQuartetCount_tendsto_of_infinite
    (h : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite) :
    Tendsto jensenQuartetCount atTop atTop := by
  apply tendsto_atTop.2
  intro m
  filter_upwards [(tendsto_jensenNonrealCount_of_infinite h).eventually_ge_atTop (4 * m)]
    with d hd
  rw [jensenNonrealCount_eq_four_mul] at hd
  omega

/-- The complete census either stabilizes at a finite number of quartets or
diverges to infinity. Conjugate-pair parity is trivial in both alternatives. -/
theorem quartet_exhaustion_dichotomy :
    (∀ d, (-1 : ℤ) ^ (jensenNonrealCount d / 2) = 1) ∧
    ((∃ m : ℕ,
        {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.encard = (4 * m : ℕ) ∧
        ∀ᶠ d in atTop, jensenQuartetCount d = m) ∨
      ({q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Infinite ∧
        Tendsto jensenQuartetCount atTop atTop)) := by
  refine ⟨jensen_conjugation_parity, ?_⟩
  by_cases hfin : {q : XiZeroCopy | (xiSpectralPoint q).im ≠ 0}.Finite
  · left
    obtain ⟨d₀, hd₀⟩ := (eventually_jensenNonrealCount_eq_of_finite hfin).exists
    have hcard : hfin.toFinset.card = 4 * jensenQuartetCount d₀ := by
      rw [← hd₀, jensenNonrealCount_eq_four_mul]
    refine ⟨jensenQuartetCount d₀, ?_, ?_⟩
    · rw [hfin.encard_eq_coe_toFinset_card, hcard]
    · filter_upwards [eventually_jensenNonrealCount_eq_of_finite hfin] with d hd
      rw [jensenNonrealCount_eq_four_mul, hcard] at hd
      omega
  · exact Or.inr ⟨hfin, jensenQuartetCount_tendsto_of_infinite hfin⟩

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.jensenNonrealCount_eq_four_mul
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.jensen_conjugation_parity
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.iSup_four_mul_jensenQuartetCount
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.quartet_exhaustion_dichotomy
