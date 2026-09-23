import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# A smooth phase detector concentrated at a prescribed graph point

The normalized squared modulus of the Dirichlet sum of all frequencies in a coordinate box, shifted
to a prescribed centre, is a trigonometric polynomial with values in the unit interval which equals
one exactly at the centre.  Its frequencies are the differences of box frequencies, so every
coefficient has the same modulus and every frequency is bounded by the resolution.

Counting the pairs of coincident difference frequencies crudely — a difference frequency and three
of the four box indices determine the fourth — bounds every completed mean square of the detector
and of its iterated coordinate derivatives by the resolution power that decays with the phase
dimension.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance phaseGraphDetectorMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance phaseGraphDetectorIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance phaseGraphDetectorIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section FrequencyBox

/-- The coordinate box of frequencies below a resolution. -/
def freqBox (d : Type*) [Fintype d] [DecidableEq d] (N : ℕ) : Finset (d → ℤ) :=
  Fintype.piFinset fun _ : d => Finset.Icc (0 : ℤ) (N : ℤ)

theorem card_freqBox (N : ℕ) : (freqBox d N).card = (N + 1) ^ Fintype.card d := by
  rw [freqBox, Fintype.card_piFinset]
  have hcard : ∀ _i : d, (Finset.Icc (0 : ℤ) (N : ℤ)).card = N + 1 := by
    intro _i
    rw [Int.card_Icc]
    simp
  rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_const, Finset.card_univ]

theorem mem_freqBox_iff {N : ℕ} {J : d → ℤ} :
    J ∈ freqBox d N ↔ ∀ i, 0 ≤ J i ∧ J i ≤ (N : ℤ) := by
  simp [freqBox, Fintype.mem_piFinset, Finset.mem_Icc]

theorem abs_diff_le_of_mem_freqBox {N : ℕ} {J L : d → ℤ} (hJ : J ∈ freqBox d N)
    (hL : L ∈ freqBox d N) (i : d) : |(J - L) i| ≤ (N : ℤ) := by
  rw [mem_freqBox_iff] at hJ hL
  rw [Pi.sub_apply, abs_le]
  constructor
  · have := (hJ i).1
    have := (hL i).2
    omega
  · have := (hJ i).2
    have := (hL i).1
    omega

/-- The difference frequency of a pair of box frequencies. -/
def diffFreq (pq : (d → ℤ) × (d → ℤ)) : d → ℤ := pq.1 - pq.2

/-- The pair box of a resolution. -/
def pairBox (d : Type*) [Fintype d] [DecidableEq d] (N : ℕ) : Finset ((d → ℤ) × (d → ℤ)) :=
  freqBox d N ×ˢ freqBox d N

theorem card_pairBox (N : ℕ) : (pairBox d N).card = ((N + 1) ^ Fintype.card d) ^ (2 : ℕ) := by
  rw [pairBox, Finset.card_product, card_freqBox, sq]

/-- **Crude coincidence count.**  A difference frequency and three of the four box indices
determine the fourth. -/
theorem card_matching_pairs_le (N : ℕ) :
    (((pairBox d N ×ˢ pairBox d N).filter fun z => diffFreq z.1 = diffFreq z.2).card : ℝ) ≤
      ((N + 1) ^ Fintype.card d) ^ (3 : ℕ) := by
  classical
  have hcard : (((pairBox d N ×ˢ pairBox d N).filter fun z => diffFreq z.1 = diffFreq z.2).card) ≤
      ((freqBox d N ×ˢ freqBox d N) ×ˢ freqBox d N).card := by
    refine Finset.card_le_card_of_injOn
      (fun z => ((z.1.1, z.1.2), z.2.1)) ?_ ?_
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz
      obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
      rw [pairBox, Finset.mem_product] at hz1 hz2
      exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hz1.1, hz1.2⟩, hz2.1⟩
    · intro z hz w hw hzw
      rw [Finset.coe_filter, Set.mem_setOf_eq] at hz hw
      obtain ⟨-, hzd⟩ := hz
      obtain ⟨-, hwd⟩ := hw
      simp only [Prod.mk.injEq] at hzw
      obtain ⟨⟨h1, h2⟩, h3⟩ := hzw
      have h4 : z.2.2 = w.2.2 := by
        have hz2 : diffFreq z.2 = diffFreq w.2 := by
          rw [← hzd, ← hwd, Prod.ext h1 h2]
        rw [diffFreq, diffFreq, h3] at hz2
        have h6 : w.2.1 - (w.2.1 - z.2.2) = w.2.1 - (w.2.1 - w.2.2) := by rw [hz2]
        rwa [sub_sub_cancel, sub_sub_cancel] at h6
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  have hprod : (((freqBox d N ×ˢ freqBox d N) ×ˢ freqBox d N).card : ℝ) =
      ((N + 1) ^ Fintype.card d) ^ (3 : ℕ) := by
    rw [Finset.card_product, Finset.card_product, card_freqBox]
    push_cast
    ring
  calc (((pairBox d N ×ˢ pairBox d N).filter fun z => diffFreq z.1 = diffFreq z.2).card : ℝ)
      ≤ (((freqBox d N ×ˢ freqBox d N) ×ˢ freqBox d N).card : ℝ) := by exact_mod_cast hcard
    _ = ((N + 1) ^ Fintype.card d) ^ (3 : ℕ) := hprod

theorem card_diagonal_pairBox (N : ℕ) :
    ((pairBox d N).filter fun pq => diffFreq pq = 0).card = (N + 1) ^ Fintype.card d := by
  classical
  have hset : (pairBox d N).filter (fun pq => diffFreq pq = 0) =
      (freqBox d N).image fun J => (J, J) := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_image, pairBox, Finset.mem_product, diffFreq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨pq.1, h1, by rw [Prod.ext_iff]; exact ⟨rfl, sub_eq_zero.mp h3⟩⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨⟨hJ, hJ⟩, sub_self J⟩
  rw [hset, Finset.card_image_of_injective _ fun J K h => (Prod.ext_iff.mp h).1, card_freqBox]

end FrequencyBox

section Detector

/-- The resolution scale of the detector. -/
def detectorScale (d : Type*) [Fintype d] [DecidableEq d] (N : ℕ) : ℝ :=
  ((N : ℝ) + 1) ^ Fintype.card d

theorem detectorScale_pos (N : ℕ) : 0 < detectorScale d N := by
  rw [detectorScale]
  positivity

/-- The coefficients of the phase detector centred at a prescribed point. -/
def detectorCoeff (N : ℕ) (a : d → ℝ) (pq : (d → ℤ) × (d → ℤ)) : ℂ :=
  (((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ)⁻¹ * charLift (diffFreq pq) (-a)

theorem norm_detectorCoeff (N : ℕ) (a : d → ℝ) (pq : (d → ℤ) × (d → ℤ)) :
    ‖detectorCoeff N a pq‖ = ((detectorScale d N) ^ (2 : ℕ))⁻¹ := by
  rw [detectorCoeff, norm_mul, norm_charLift, mul_one, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

/-- The phase detector of resolution `N` centred at `a`. -/
def phaseDetector (N : ℕ) (a : d → ℝ) : (d → ℝ) → ℂ :=
  trigLift (pairBox d N) diffFreq (detectorCoeff N a)

/-- The Dirichlet sum of all box frequencies, shifted to the centre. -/
def phaseGraphDirichletShift (N : ℕ) (a : d → ℝ) (x : d → ℝ) : ℂ :=
  ∑ J ∈ freqBox d N, charLift J (x - a)

theorem norm_phaseGraphDirichletShift_le (N : ℕ) (a x : d → ℝ) :
    ‖phaseGraphDirichletShift N a x‖ ≤ detectorScale d N := by
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ J ∈ freqBox d N, ‖charLift J (x - a)‖ ≤ 1 :=
    fun J _ => le_of_eq (norm_charLift J (x - a))
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_freqBox, detectorScale]
  norm_cast

theorem phaseGraphDirichletShift_self (N : ℕ) (a : d → ℝ) :
    phaseGraphDirichletShift N a a = (detectorScale d N : ℂ) := by
  rw [phaseGraphDirichletShift]
  have hterm : ∀ J ∈ freqBox d N, charLift J (a - a) = 1 := by
    intro J _
    rw [sub_self, charLift_apply_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one, card_freqBox,
    detectorScale]
  push_cast
  ring

/-- **The detector is the normalized squared modulus of the shifted Dirichlet sum.** -/
theorem phaseDetector_eq (N : ℕ) (a x : d → ℝ) :
    phaseDetector N a x =
      ((‖phaseGraphDirichletShift N a x‖ ^ (2 : ℕ) / (detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  have hmulconj : ((‖phaseGraphDirichletShift N a x‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      phaseGraphDirichletShift N a x * (starRingEnd ℂ) (phaseGraphDirichletShift N a x) := by
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.sq_norm _
  have hexpand : phaseGraphDirichletShift N a x * (starRingEnd ℂ) (phaseGraphDirichletShift N a x) =
      ∑ pq ∈ pairBox d N, charLift (diffFreq pq) x * charLift (diffFreq pq) (-a) := by
    rw [phaseGraphDirichletShift, map_sum, Finset.sum_mul_sum, pairBox, Finset.sum_product]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun L _ => ?_
    rw [← charLift_neg_index, ← charLift_add_index, ← sub_eq_add_neg, ← charLift_sub_right]
    rfl
  rw [Complex.ofReal_div, hmulconj, hexpand, phaseDetector, trigLift, Complex.ofReal_pow,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [detectorCoeff, Complex.ofReal_pow]
  field_simp

theorem phaseDetector_nonneg (N : ℕ) (a x : d → ℝ) :
    0 ≤ (phaseDetector N a x).re := by
  rw [phaseDetector_eq, Complex.ofReal_re]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem phaseDetector_le_one (N : ℕ) (a x : d → ℝ) :
    (phaseDetector N a x).re ≤ 1 := by
  rw [phaseDetector_eq, Complex.ofReal_re, div_le_one (pow_pos (detectorScale_pos (d := d) N) 2)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseGraphDirichletShift_le N a x) 2

theorem phaseDetector_im (N : ℕ) (a x : d → ℝ) : (phaseDetector N a x).im = 0 := by
  rw [phaseDetector_eq, Complex.ofReal_im]

/-- **The detector equals one at its centre.** -/
theorem phaseDetector_self (N : ℕ) (a : d → ℝ) : phaseDetector N a a = 1 := by
  rw [phaseDetector_eq, phaseGraphDirichletShift_self, Complex.norm_real,
    Real.norm_of_nonneg (detectorScale_pos (d := d) N).le,
    div_self (pow_pos (detectorScale_pos (d := d) N) 2).ne', Complex.ofReal_one]

end Detector


section Estimates

theorem trigLift_sub {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (w : ι → ℂ) (a x : d → ℝ) :
    trigLift P ν w (x - a) = trigLift P ν (fun p => w p * charLift (ν p) (-a)) x := by
  rw [trigLift, trigLift]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [charLift_sub_right]
  ring

theorem norm_list_prod_map (l : List d) (f : d → ℂ) :
    ‖(l.map f).prod‖ = (l.map fun i => ‖f i‖).prod := by
  induction l with
  | nil => simp
  | cons i t ih => simp [ih]

theorem list_prod_map_le_pow {g : d → ℝ} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ i, 0 ≤ g i)
    (hb : ∀ i, g i ≤ C) : ∀ l : List d, (l.map g).prod ≤ C ^ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons i t ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
      refine mul_le_mul (hb i) ih ?_ hC
      exact List.prod_nonneg fun y hy => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
        exact hg j

/-- **Completed mean of the detector.**  Only the diagonal frequencies survive. -/
theorem integral_box_phaseDetector (N : ℕ) (a : d → ℝ) :
    (∫ x in torusBox d, phaseDetector N a x) = (((detectorScale d N)⁻¹ : ℝ) : ℂ) := by
  classical
  rw [phaseDetector, integral_box_trigLift]
  have hterm : ∀ pq ∈ (pairBox d N).filter (fun pq => diffFreq pq = 0),
      detectorCoeff N a pq = ((((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ))⁻¹ := by
    intro pq hpq
    rw [Finset.mem_filter] at hpq
    rw [detectorCoeff, hpq.2, charLift_zero_index, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_diagonal_pairBox, nsmul_eq_mul]
  have hscale : (((N + 1) ^ Fintype.card d : ℕ) : ℂ) = ((detectorScale d N : ℝ) : ℂ) := by
    rw [detectorScale]
    push_cast
    ring
  rw [hscale, Complex.ofReal_pow, Complex.ofReal_inv]
  have hne : ((detectorScale d N : ℝ) : ℂ) ≠ 0 := by
    simpa using (detectorScale_pos (d := d) N).ne'
  field_simp

/-- The iterated coordinate derivatives of the detector are the same combination with the
frequencies multiplied in. -/
theorem pderivList_phaseDetector (N : ℕ) (a : d → ℝ) (l : List d) :
    pderivList l (phaseDetector N a) =
      trigLift (pairBox d N) diffFreq
        (fun pq => (l.map fun i => (2 * Real.pi * I * ((diffFreq pq) i : ℂ))).prod *
          detectorCoeff N a pq) :=
  pderivList_trigLift _ _ _ l

theorem norm_pderivCoeff_le (N : ℕ) (a : d → ℝ) (l : List d) {pq : (d → ℤ) × (d → ℤ)}
    (hpq : pq ∈ pairBox d N) :
    ‖(l.map fun i => (2 * Real.pi * I * ((diffFreq pq) i : ℂ))).prod * detectorCoeff N a pq‖ ≤
      (2 * Real.pi * (N : ℝ)) ^ l.length * ((detectorScale d N) ^ (2 : ℕ))⁻¹ := by
  rw [pairBox, Finset.mem_product] at hpq
  rw [norm_mul, norm_detectorCoeff, norm_list_prod_map]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine list_prod_map_le_pow (by positivity) (fun i => norm_nonneg _) (fun i => ?_) l
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_intCast]
  have hb : |(diffFreq pq) i| ≤ (N : ℤ) := abs_diff_le_of_mem_freqBox hpq.1 hpq.2 i
  have hb' : |((diffFreq pq) i : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hb
  exact mul_le_mul_of_nonneg_left hb' (by positivity)

/-- **Sobolev decay of the detector.**  Every completed mean square of an iterated coordinate
derivative decays like the reciprocal resolution power of the phase dimension. -/
theorem integral_box_normSq_pderivList_phaseDetector_le (N : ℕ) (a : d → ℝ) (l : List d) :
    (∫ x in torusBox d, ‖pderivList l (phaseDetector N a) x‖ ^ (2 : ℕ)) ≤
      ((2 * Real.pi * (N : ℝ)) ^ l.length) ^ (2 : ℕ) / ((N : ℝ) + 1) ^ Fintype.card d := by
  classical
  rw [pderivList_phaseDetector]
  refine le_trans (integral_box_normSq_trigLift_le (pairBox d N) diffFreq _
    (M := (2 * Real.pi * (N : ℝ)) ^ l.length * ((detectorScale d N) ^ (2 : ℕ))⁻¹)
    (by positivity) (fun pq hpq => norm_pderivCoeff_le N a l hpq)) ?_
  have hcount := card_matching_pairs_le (d := d) N
  have hscale : detectorScale d N = ((N : ℝ) + 1) ^ Fintype.card d := rfl
  have hpos : (0 : ℝ) < detectorScale d N := detectorScale_pos N
  calc ((2 * Real.pi * (N : ℝ)) ^ l.length * ((detectorScale d N) ^ (2 : ℕ))⁻¹) ^ (2 : ℕ) *
        ((((pairBox d N ×ˢ pairBox d N).filter fun z => diffFreq z.1 = diffFreq z.2).card : ℝ))
      ≤ ((2 * Real.pi * (N : ℝ)) ^ l.length * ((detectorScale d N) ^ (2 : ℕ))⁻¹) ^ (2 : ℕ) *
        ((N + 1) ^ Fintype.card d) ^ (3 : ℕ) := by
        refine mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((2 * Real.pi * (N : ℝ)) ^ l.length) ^ (2 : ℕ) / ((N : ℝ) + 1) ^ Fintype.card d := by
        rw [← hscale]
        field_simp

/-- **Translation invariance.**  The completed mean squares of the detector's derivatives do not
depend on the centre. -/
theorem integral_box_normSq_pderivList_phaseDetector_eq (N : ℕ) (a : d → ℝ) (l : List d) :
    (∫ x in torusBox d, ‖pderivList l (phaseDetector N a) x‖ ^ (2 : ℕ)) =
      ∫ x in torusBox d, ‖pderivList l (phaseDetector N (0 : d → ℝ)) x‖ ^ (2 : ℕ) := by
  classical
  have key : ∀ b : d → ℝ,
      ((∫ x in torusBox d, ‖pderivList l (phaseDetector N b) x‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑ p ∈ pairBox d N, ∑ q ∈ pairBox d N,
        if diffFreq p = diffFreq q then
          ((l.map fun i => (2 * Real.pi * I * ((diffFreq p) i : ℂ))).prod *
            ((((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ))⁻¹) *
          (starRingEnd ℂ) ((l.map fun i => (2 * Real.pi * I * ((diffFreq q) i : ℂ))).prod *
            ((((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ))⁻¹)
        else 0 := by
    intro b
    rw [pderivList_phaseDetector, ofReal_integral_box_normSq_trigLift]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases h : diffFreq p = diffFreq q
    · have hpq : detectorCoeff N b p = detectorCoeff N b q := by
        rw [detectorCoeff, detectorCoeff, h]
      rw [if_pos h, if_pos h, hpq, h]
      have hconj : charLift (diffFreq q) (-b) *
          (starRingEnd ℂ) (charLift (diffFreq q) (-b)) = 1 := by
        rw [Complex.mul_conj]
        norm_cast
        rw [← Complex.sq_norm, norm_charLift, one_pow]
      have hcoef : detectorCoeff N b q * (starRingEnd ℂ) (detectorCoeff N b q) =
          ((((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ))⁻¹ *
            (starRingEnd ℂ) (((((detectorScale d N) ^ (2 : ℕ) : ℝ) : ℂ))⁻¹) := by
        rw [detectorCoeff, map_mul, mul_mul_mul_comm, hconj, mul_one]
      rw [map_mul, map_mul, mul_mul_mul_comm, hcoef, ← mul_mul_mul_comm]
    · rw [if_neg h, if_neg h]
  have h1 := key a
  have h2 := key (0 : d → ℝ)
  have := h1.trans h2.symm
  exact_mod_cast this

end Estimates

section Smoothness

theorem contDiff_charLift (n : d → ℤ) : ContDiff ℝ ⊤ (charLift (d := d) n) :=
  Complex.contDiff_exp.comp (charPhase n).contDiff

theorem contDiff_trigLift {ι : Type*} (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    ContDiff ℝ ⊤ (trigLift P ν a) := by
  have hfun : trigLift P ν a = fun x : d → ℝ => ∑ p ∈ P, a p * charLift (ν p) x := rfl
  rw [hfun]
  exact ContDiff.sum fun p _ => contDiff_const.mul (contDiff_charLift (ν p))

/-- **The detector is smooth in the phase variable.** -/
theorem contDiff_phaseDetector (N : ℕ) (a : d → ℝ) : ContDiff ℝ ⊤ (phaseDetector N a) :=
  contDiff_trigLift _ _ _

end Smoothness

end GaloisForLFunctions.HTGeometry
