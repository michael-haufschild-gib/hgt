import GaloisForLFunctions.ArithmeticElectrostatics.TheVirialLawsOfAFiniteConfiguration

/-!
# Transverse equilibrium is the critical line

A finite configuration is **reflection-closed** when an involution `σ` of the index set sends each
charge `z_j` to its reflection partner `1 − z̄_j` with the same positive multiplicity: the shape of
the zero divisor of a completed `L`-function, and of the battery models. For such configurations:

* **Equilibrium is the critical line** (`critical_iff_equilibrium`): every transverse field
  vanishes iff every charge lies on `Re s = ½`. The proof is the transverse virial: zero work means
  zero transverse energy, which on the complete graph of charges forces all real parts to agree,
  and the reflection pins the common value to `½`.
* **One scalar suffices** (`critical_iff_work_nonpos`): nonpositive total work
  `Σ_j m_j (Re z_j − ½) Re E_j ≤ 0` is already criticality.
* **Quantization** (`pairQuanta_le_transverseEnergy`): the segment from an off-line charge to its
  partner is horizontal, so it contributes exactly `m_j m_{σ j}` to the transverse energy at every
  depth. With multiplicities at least `1` the energy is `0` or at least `1`
  (`critical_iff_transverseEnergy_lt_one`): criticality has a gap form.
* **Maximum principle** (`exists_outward_and_inward_of_not_critical`): off the critical line the
  deepest charge feels an outward and the shallowest an inward transverse field.

Equilibrium and quantization are identities about computed quantities; what no identity supplies
is an upper bound for the field below the quantum.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticElectrostatics

open GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {ι : Type*}

/-- A **reflection-closed** configuration: positive multiplicities, distinct charges, and an
index involution `σ` realizing `z ↦ 1 − z̄` with equal multiplicities. -/
structure IsReflectionClosed (m : ι → ℝ) (z : ι → ℂ) (σ : ι → ι) : Prop where
  pos : ∀ j, 0 < m j
  inj : Function.Injective z
  refl : ∀ j, z (σ j) = 1 - starRingEnd ℂ (z j)
  mult : ∀ j, m (σ j) = m j

namespace IsReflectionClosed

variable {m : ι → ℝ} {z : ι → ℂ} {σ : ι → ι}

theorem re_refl (h : IsReflectionClosed m z σ) (j : ι) : (z (σ j)).re = 1 - (z j).re := by
  rw [h.refl, Complex.sub_re, Complex.one_re, Complex.conj_re]

/-- An off-line charge is not its own partner. -/
theorem refl_ne (h : IsReflectionClosed m z σ) {j : ι} (hj : (z j).re ≠ 1 / 2) : σ j ≠ j := by
  intro hc
  have := h.re_refl j
  rw [hc] at this
  exact hj (by linarith)

/-- The segment to the partner is horizontal of length `|2 Re z_j − 1|`. -/
theorem sub_refl (h : IsReflectionClosed m z σ) (j : ι) :
    z j - z (σ j) = ((2 * (z j).re - 1 : ℝ) : ℂ) := by
  rw [h.refl]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.ofReal_re]; ring
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im, Complex.ofReal_im]; ring

end IsReflectionClosed

/-! ### Zero transverse energy -/

variable [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The pair summand of the transverse energy. -/
private theorem pairTerm_nonneg {m : ι → ℝ} (hm : ∀ j, 0 < m j) (z : ι → ℂ) (j k : ι) :
    0 ≤ m j * m k * ((z j).re - (z k).re) ^ 2 / Complex.normSq (z j - z k) :=
  div_nonneg (mul_nonneg (mul_pos (hm j) (hm k)).le (sq_nonneg _)) (Complex.normSq_nonneg _)

/-- With positive multiplicities the transverse energy vanishes iff all real parts agree. -/
theorem transverseEnergy_eq_zero_iff {m : ι → ℝ} (hm : ∀ j, 0 < m j) {z : ι → ℂ}
    (hz : Function.Injective z) :
    transverseEnergy m z = 0 ↔ ∀ j k, (z j).re = (z k).re := by
  rw [transverseEnergy, div_eq_zero_iff, or_iff_left (two_ne_zero' ℝ),
    sum_eq_zero_iff_of_nonneg fun j _ => sum_nonneg fun k _ => pairTerm_nonneg hm z j k]
  constructor
  · intro h j k
    by_cases hjk : k = j
    · rw [hjk]
    have hterm := (sum_eq_zero_iff_of_nonneg fun k _ => pairTerm_nonneg hm z j k).mp
      (h j (mem_univ j)) k (mem_erase.mpr ⟨hjk, mem_univ k⟩)
    have hd : z j - z k ≠ 0 := sub_ne_zero.mpr fun hc => hjk (hz hc).symm
    have hn : Complex.normSq (z j - z k) ≠ 0 := Complex.normSq_eq_zero.not.mpr hd
    rw [div_eq_zero_iff, or_iff_left hn, mul_eq_zero, or_iff_right
      (mul_pos (hm j) (hm k)).ne', sq_eq_zero_iff, sub_eq_zero] at hterm
    exact hterm
  · intro h j _
    refine sum_eq_zero fun k _ => ?_
    rw [h j k, sub_self]
    simp

variable {m : ι → ℝ} {z : ι → ℂ} {σ : ι → ι}

omit [Fintype ι] [DecidableEq ι] in
/-- On a reflection-closed configuration, equal real parts means criticality. -/
theorem critical_iff_re_eq (h : IsReflectionClosed m z σ) :
    (∀ j, (z j).re = 1 / 2) ↔ ∀ j k, (z j).re = (z k).re := by
  constructor
  · intro hc j k
    rw [hc j, hc k]
  · intro he j
    have := h.re_refl j
    rw [he (σ j) j] at this
    linarith

theorem critical_iff_transverseEnergy_eq_zero (h : IsReflectionClosed m z σ) :
    (∀ j, (z j).re = 1 / 2) ↔ transverseEnergy m z = 0 := by
  rw [critical_iff_re_eq h, transverseEnergy_eq_zero_iff h.pos h.inj]

/-! ### Equilibrium and work -/

/-- The **total transverse work** `Σ_j m_j (Re z_j − ½) Re E_j`. -/
noncomputable def transverseWork (m : ι → ℝ) (z : ι → ℂ) : ℝ :=
  ∑ j, ((z j).re - 1 / 2) * m j * (fieldAt (fun k => (m k : ℂ)) z j).re

theorem transverseWork_eq (m : ι → ℝ) (z : ι → ℂ) : transverseWork m z = transverseEnergy m z :=
  sum_mul_re_fieldAt_eq_transverseEnergy m z (1 / 2)

/-- **One scalar decides**: nonpositive total work is criticality. -/
theorem critical_iff_work_nonpos (h : IsReflectionClosed m z σ) :
    (∀ j, (z j).re = 1 / 2) ↔ transverseWork m z ≤ 0 := by
  rw [transverseWork_eq, critical_iff_transverseEnergy_eq_zero h]
  exact ⟨le_of_eq, fun hle => le_antisymm hle (transverseEnergy_nonneg (fun j => (h.pos j).le) z)⟩

/-- **Equilibrium is the critical line.** -/
theorem critical_iff_equilibrium (h : IsReflectionClosed m z σ) :
    (∀ j, (z j).re = 1 / 2) ↔ ∀ j, (fieldAt (fun k => (m k : ℂ)) z j).re = 0 := by
  constructor
  · intro hc j
    exact re_fieldAt_eq_zero_of_critical _ z (fun k => Complex.ofReal_im _) hc j
  · intro he
    rw [critical_iff_work_nonpos h, transverseWork]
    simp [he]

/-- Only off-line charges do work: the work is a sum over the off-line part. -/
theorem transverseWork_eq_sum_offLine (m : ι → ℝ) (z : ι → ℂ) :
    transverseWork m z = ∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2),
      ((z j).re - 1 / 2) * m j * (fieldAt (fun k => (m k : ℂ)) z j).re := by
  rw [transverseWork, sum_filter]
  refine sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · rw [not_not.mp hj, sub_self, zero_mul, zero_mul]

/-! ### Quantization -/

omit [Fintype ι] [DecidableEq ι] in
/-- **The quantum of a reflection pair**: the partner term of the transverse energy is
`m_j m_{σ j}`, whatever the depth. -/
theorem pairTerm_refl (h : IsReflectionClosed m z σ) {j : ι} (hj : (z j).re ≠ 1 / 2) :
    m j * m (σ j) * ((z j).re - (z (σ j)).re) ^ 2 / Complex.normSq (z j - z (σ j)) =
      m j * m (σ j) := by
  have hd : 2 * (z j).re - 1 ≠ 0 := fun hc => hj (by linarith)
  rw [h.sub_refl, Complex.normSq_ofReal, h.re_refl,
    show (z j).re - (1 - (z j).re) = 2 * (z j).re - 1 by ring]
  field_simp

/-- **Quantization**: the transverse energy is at least half the sum of the pair quanta over the
off-line charges. -/
theorem pairQuanta_le_transverseEnergy (h : IsReflectionClosed m z σ) :
    (∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2), m j * m (σ j)) / 2 ≤ transverseEnergy m z := by
  rw [transverseEnergy]
  refine div_le_div_of_nonneg_right ?_ zero_le_two
  calc ∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2), m j * m (σ j)
      = ∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2),
          m j * m (σ j) * ((z j).re - (z (σ j)).re) ^ 2 / Complex.normSq (z j - z (σ j)) :=
        sum_congr rfl fun j hj => (pairTerm_refl h (mem_filter.mp hj).2).symm
    _ ≤ ∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2), ∑ k ∈ univ.erase j,
          m j * m k * ((z j).re - (z k).re) ^ 2 / Complex.normSq (z j - z k) :=
        sum_le_sum fun j hj => single_le_sum (f := fun k =>
          m j * m k * ((z j).re - (z k).re) ^ 2 / Complex.normSq (z j - z k))
          (fun k _ => pairTerm_nonneg h.pos z j k)
          (mem_erase.mpr ⟨h.refl_ne (mem_filter.mp hj).2, mem_univ _⟩)
    _ ≤ ∑ j, ∑ k ∈ univ.erase j,
          m j * m k * ((z j).re - (z k).re) ^ 2 / Complex.normSq (z j - z k) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun j _ _ => sum_nonneg fun k _ => pairTerm_nonneg h.pos z j k

/-- **The gap**: with multiplicities at least `1`, a non-critical reflection-closed configuration
has transverse energy at least `1`. -/
theorem one_le_transverseEnergy (h : IsReflectionClosed m z σ) (hm1 : ∀ j, 1 ≤ m j)
    {j₀ : ι} (hj₀ : (z j₀).re ≠ 1 / 2) : 1 ≤ transverseEnergy m z := by
  refine le_trans ?_ (pairQuanta_le_transverseEnergy h)
  have hσ₀ : (z (σ j₀)).re ≠ 1 / 2 := by
    rw [h.re_refl]; intro hc; exact hj₀ (by linarith)
  have hmem : ∀ j, (z j).re ≠ 1 / 2 → j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2) :=
    fun j hj => mem_filter.mpr ⟨mem_univ j, hj⟩
  have hone : ∀ j, 1 ≤ m j * m (σ j) := fun j => one_le_mul_of_one_le_of_one_le (hm1 j) (hm1 _)
  have hpair : m j₀ * m (σ j₀) + m (σ j₀) * m (σ (σ j₀)) ≤
      ∑ j ∈ univ.filter (fun j => (z j).re ≠ 1 / 2), m j * m (σ j) := by
    rw [← sum_pair (f := fun j => m j * m (σ j)) (h.refl_ne hj₀).symm]
    exact sum_le_sum_of_subset_of_nonneg
      (insert_subset (hmem _ hj₀) (singleton_subset_iff.mpr (hmem _ hσ₀)))
      fun j _ _ => mul_nonneg (h.pos j).le (h.pos _).le
  linarith [hone j₀, hone (σ j₀)]

/-- **Criticality has a gap form**: with multiplicities at least `1`, a reflection-closed
configuration is critical iff its transverse energy is below `1`. -/
theorem critical_iff_transverseEnergy_lt_one (h : IsReflectionClosed m z σ)
    (hm1 : ∀ j, 1 ≤ m j) :
    (∀ j, (z j).re = 1 / 2) ↔ transverseEnergy m z < 1 := by
  constructor
  · intro hc
    rw [(critical_iff_transverseEnergy_eq_zero h).mp hc]
    exact one_pos
  · intro hlt j
    by_contra hj
    exact absurd (one_le_transverseEnergy h hm1 hj) (not_le.mpr hlt)

/-! ### Maximum principle -/

/-- A charge of maximal real part feels a nonnegative transverse field, positive as soon as some
charge lies strictly to its left. -/
theorem re_fieldAt_pos_of_max (hm : ∀ j, 0 < m j) (hz : Function.Injective z) {j : ι}
    (hmax : ∀ k, (z k).re ≤ (z j).re) {k₀ : ι} (hk₀ : (z k₀).re < (z j).re) :
    0 < (fieldAt (fun k => (m k : ℂ)) z j).re := by
  rw [re_fieldAt]
  have hk₀j : k₀ ≠ j := fun hc => by rw [hc] at hk₀; exact lt_irrefl _ hk₀
  have hterm : ∀ k ∈ univ.erase j,
      0 ≤ m k * ((z j).re - (z k).re) / Complex.normSq (z j - z k) := fun k _ =>
    div_nonneg (mul_nonneg (hm k).le (by linarith [hmax k])) (Complex.normSq_nonneg _)
  refine lt_of_lt_of_le ?_ (single_le_sum hterm (mem_erase.mpr ⟨hk₀j, mem_univ k₀⟩))
  have hd : z j - z k₀ ≠ 0 := sub_ne_zero.mpr fun hc => hk₀j (hz hc).symm
  exact div_pos (mul_pos (hm k₀) (by linarith)) (Complex.normSq_pos.mpr hd)

/-- A charge of minimal real part feels a negative transverse field as soon as some charge lies
strictly to its right. -/
theorem re_fieldAt_neg_of_min (hm : ∀ j, 0 < m j) (hz : Function.Injective z) {j : ι}
    (hmin : ∀ k, (z j).re ≤ (z k).re) {k₀ : ι} (hk₀ : (z j).re < (z k₀).re) :
    (fieldAt (fun k => (m k : ℂ)) z j).re < 0 := by
  rw [re_fieldAt, ← neg_pos, ← sum_neg_distrib]
  have hk₀j : k₀ ≠ j := fun hc => by rw [hc] at hk₀; exact lt_irrefl _ hk₀
  have hterm : ∀ k ∈ univ.erase j,
      0 ≤ -(m k * ((z j).re - (z k).re) / Complex.normSq (z j - z k)) := fun k _ => by
    rw [← neg_div, ← mul_neg]
    exact div_nonneg (mul_nonneg (hm k).le (by linarith [hmin k])) (Complex.normSq_nonneg _)
  refine lt_of_lt_of_le ?_ (single_le_sum hterm (mem_erase.mpr ⟨hk₀j, mem_univ k₀⟩))
  have hd : z j - z k₀ ≠ 0 := sub_ne_zero.mpr fun hc => hk₀j (hz hc).symm
  rw [← neg_div, ← mul_neg]
  exact div_pos (mul_pos (hm k₀) (by linarith)) (Complex.normSq_pos.mpr hd)

/-- **Outward at the deepest, inward at the shallowest.** A non-critical reflection-closed
configuration has a charge right of the line with outward field and a charge left of the line
with inward field. -/
theorem exists_outward_and_inward_of_not_critical (h : IsReflectionClosed m z σ)
    {j₀ : ι} (hj₀ : (z j₀).re ≠ 1 / 2) :
    (∃ j, 1 / 2 < (z j).re ∧ 0 < (fieldAt (fun k => (m k : ℂ)) z j).re) ∧
      ∃ j, (z j).re < 1 / 2 ∧ (fieldAt (fun k => (m k : ℂ)) z j).re < 0 := by
  obtain ⟨jmax, -, hjmax⟩ := exists_max_image univ (fun j => (z j).re) ⟨j₀, mem_univ j₀⟩
  obtain ⟨jmin, -, hjmin⟩ := exists_min_image univ (fun j => (z j).re) ⟨j₀, mem_univ j₀⟩
  have hmax : ∀ k, (z k).re ≤ (z jmax).re := fun k => hjmax k (mem_univ k)
  have hmin : ∀ k, (z jmin).re ≤ (z k).re := fun k => hjmin k (mem_univ k)
  -- the extremes straddle the line strictly
  have hgt : 1 / 2 < (z jmax).re := by
    rcases lt_or_gt_of_ne hj₀ with hlt | hgt
    · have := hmax (σ j₀); rw [h.re_refl] at this; linarith
    · linarith [hmax j₀]
  have hlt : (z jmin).re < 1 / 2 := by
    have := hmin (σ jmax); rw [h.re_refl] at this; linarith
  exact ⟨⟨jmax, hgt, re_fieldAt_pos_of_max h.pos h.inj hmax (k₀ := jmin) (by linarith)⟩,
    jmin, hlt, re_fieldAt_neg_of_min h.pos h.inj hmin (k₀ := jmax) (by linarith)⟩

end GaloisForLFunctions.ArithmeticElectrostatics
