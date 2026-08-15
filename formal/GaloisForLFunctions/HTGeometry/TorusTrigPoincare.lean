import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# The spectral gap of the unit torus

Grouping the coefficients of a character combination by frequency turns every frequency-diagonal
quadratic form into a nonnegative sum of fibre squares.  The mean square, the mean, and the mean
square of each partial derivative are all such forms, and the derivative weight is the squared
Euclidean length of the frequency.  Since a nonzero integer frequency has length at least one, the
variance of a character combination is at most the sum of the mean squares of its partial
derivatives, divided by the squared circle circumference.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance torusTrigPoincareMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance torusTrigPoincareIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance torusTrigPoincareIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section Fibre

variable {ι : Type*}

/-- The total coefficient carried by one frequency. -/
def freqBlock (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) (n : d → ℤ) : ℂ :=
  ∑ p ∈ P with ν p = n, a p

theorem freqBlock_eq_zero_of_notMem_image {P : Finset ι}
    {ν : ι → (d → ℤ)} (a : ι → ℂ) {n : d → ℤ} (hn : n ∉ P.image ν) :
    freqBlock P ν a n = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp => ?_
  exact absurd ((Finset.mem_filter.mp hp).2 ▸ Finset.mem_image_of_mem ν
    (Finset.mem_filter.mp hp).1) hn

/-- **Frequency-diagonal quadratic forms are nonnegative fibre sums.**  Any weight depending only
on the shared frequency reassembles into the weighted squares of the fibre coefficient sums. -/
theorem sum_ite_freq_eq_sum_freqBlock (P : Finset ι) (ν : ι → (d → ℤ))
    (a : ι → ℂ) (g : (d → ℤ) → ℝ) :
    (∑ p ∈ P, ∑ q ∈ P,
        if ν p = ν q then ((g (ν p) : ℝ) : ℂ) * (a p * (starRingEnd ℂ) (a q)) else 0) =
      ((∑ n ∈ P.image ν, g n * ‖freqBlock P ν a n‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (t := P.image ν)
      (fun p hp => Finset.mem_image_of_mem ν hp)]
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  have hinner : ∀ p ∈ P.filter fun p => ν p = n,
      (∑ q ∈ P, if ν p = ν q then ((g (ν p) : ℝ) : ℂ) * (a p * (starRingEnd ℂ) (a q)) else 0) =
        ((g n : ℝ) : ℂ) * (a p * (starRingEnd ℂ) (freqBlock P ν a n)) := by
    intro p hp
    have hpn : ν p = n := (Finset.mem_filter.mp hp).2
    have hL : (∑ q ∈ P,
          if ν p = ν q then ((g (ν p) : ℝ) : ℂ) * (a p * (starRingEnd ℂ) (a q)) else 0) =
        ∑ q ∈ P with ν q = n, ((g n : ℝ) : ℂ) * (a p * (starRingEnd ℂ) (a q)) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : ν q = n
      · rw [if_pos (by rw [hpn, h]), if_pos h, hpn]
      · rw [if_neg (by rw [hpn]; exact fun hcon => h hcon.symm), if_neg h]
    rw [hL, ← Finset.mul_sum, ← Finset.mul_sum, ← map_sum, freqBlock]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [show (∑ p ∈ P with ν p = n, a p) = freqBlock P ν a n from rfl]
  have hconj : (freqBlock P ν a n) * (starRingEnd ℂ) (freqBlock P ν a n) =
      ((‖freqBlock P ν a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [hconj]
  push_cast
  ring

/-- The Haar mean square of a character combination is the sum of its squared fibre
coefficients. -/
theorem integral_box_normSq_trigLift_eq_sum_freqBlock (P : Finset ι)
    (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) =
      ∑ n ∈ P.image ν, ‖freqBlock P ν a n‖ ^ 2 := by
  classical
  have hpars := ofReal_integral_box_normSq_trigLift P ν a
  have hone := sum_ite_freq_eq_sum_freqBlock P ν a (fun _ => (1 : ℝ))
  simp only [Complex.ofReal_one, one_mul] at hone
  rw [hone] at hpars
  exact_mod_cast hpars

/-- The Haar mean of a character combination is its zero-frequency fibre coefficient. -/
theorem integral_box_trigLift_eq_freqBlock_zero (P : Finset ι) (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    (∫ x in torusBox d, trigLift P ν a x) = freqBlock P ν a 0 := by
  classical
  rw [integral_box_trigLift, freqBlock]

end Fibre

section Gap

/-- The squared Euclidean length of an integer frequency. -/
def freqNormSq (n : d → ℤ) : ℝ := ∑ j, ((n j : ℝ)) ^ 2

theorem freqNormSq_nonneg (n : d → ℤ) : 0 ≤ freqNormSq n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **The torus spectral gap.**  A nonzero integer frequency has length at least one. -/
theorem one_le_freqNormSq {n : d → ℤ} (hn : n ≠ 0) : 1 ≤ freqNormSq n := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra hcon
    exact hn (funext fun j => by simpa using not_exists.mp hcon j)
  have hone : (1 : ℝ) ≤ ((n j : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (n j) ^ 2 := by
      rcases lt_or_gt_of_ne hj with h | h <;> nlinarith
    have : ((1 : ℤ) : ℝ) ≤ (((n j) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    exact this
  exact le_trans hone (Finset.single_le_sum (f := fun i : d => ((n i : ℝ)) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ j))

variable {ι : Type*}

/-- The mean square of one partial derivative is the frequency-weighted fibre sum. -/
theorem integral_box_normSq_pderiv_trigLift (P : Finset ι)
    (ν : ι → (d → ℤ)) (a : ι → ℂ) (j : d) :
    (∫ x in torusBox d, ‖pderiv j (trigLift P ν a) x‖ ^ 2) =
      ∑ n ∈ P.image ν, (2 * Real.pi) ^ 2 * ((n j : ℝ)) ^ 2 * ‖freqBlock P ν a n‖ ^ 2 := by
  classical
  rw [pderiv_trigLift]
  have hpars := ofReal_integral_box_normSq_trigLift P ν
    (fun p => (2 * Real.pi * I * ((ν p) j : ℂ)) * a p)
  have hg := sum_ite_freq_eq_sum_freqBlock P ν a
    (fun n => (2 * Real.pi) ^ 2 * ((n j : ℝ)) ^ 2)
  have hterm : ∀ p ∈ P, ∀ q ∈ P,
      (if ν p = ν q then
        ((2 * Real.pi * I * ((ν p) j : ℂ)) * a p) *
          (starRingEnd ℂ) ((2 * Real.pi * I * ((ν q) j : ℂ)) * a q) else 0) =
      (if ν p = ν q then
        ((((2 * Real.pi) ^ 2 * ((ν p) j : ℝ) ^ 2 : ℝ)) : ℂ) *
          (a p * (starRingEnd ℂ) (a q)) else 0) := by
    intro p _ q _
    by_cases h : ν p = ν q
    · rw [if_pos h, if_pos h, h]
      simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal, map_intCast]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [if_neg h, if_neg h]
  rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hterm p hp q hq, hg]
    at hpars
  exact_mod_cast hpars

/-- **Poincaré inequality on the unit torus.**  The variance of a character combination is at most
the total mean square of its partial derivatives, divided by the squared circumference. -/
theorem variance_trigLift_le_sum_integral_normSq_pderiv (P : Finset ι)
    (ν : ι → (d → ℤ)) (a : ι → ℂ) :
    (∫ x in torusBox d, ‖trigLift P ν a x‖ ^ 2) -
        ‖∫ x in torusBox d, trigLift P ν a x‖ ^ 2 ≤
      ((2 * Real.pi) ^ 2)⁻¹ *
        ∑ j : d, ∫ x in torusBox d, ‖pderiv j (trigLift P ν a) x‖ ^ 2 := by
  classical
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  have hderiv : (∑ j : d, ∫ x in torusBox d, ‖pderiv j (trigLift P ν a) x‖ ^ 2) =
      (2 * Real.pi) ^ 2 * ∑ n ∈ P.image ν, freqNormSq n * ‖freqBlock P ν a n‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun j _ => integral_box_normSq_pderiv_trigLift P ν a j,
      Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [freqNormSq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hderiv, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpi), one_mul,
    integral_box_normSq_trigLift_eq_sum_freqBlock P ν a,
    integral_box_trigLift_eq_freqBlock_zero P ν a]
  have hzero : ‖freqBlock P ν a 0‖ ^ 2 =
      ∑ n ∈ P.image ν, if n = 0 then ‖freqBlock P ν a n‖ ^ 2 else 0 := by
    by_cases h0 : (0 : d → ℤ) ∈ P.image ν
    · rw [Finset.sum_ite_eq' (P.image ν) (0 : d → ℤ) fun n => ‖freqBlock P ν a n‖ ^ 2]
      rw [if_pos h0]
    · rw [freqBlock_eq_zero_of_notMem_image a h0, norm_zero,
        show ((0 : ℝ) ^ 2) = 0 from by norm_num]
      refine (Finset.sum_eq_zero fun n hn => ?_).symm
      rw [if_neg]
      intro hcon
      exact h0 (hcon ▸ hn)
  have hterm : ∀ n ∈ P.image ν, ‖freqBlock P ν a n‖ ^ 2 ≤
      freqNormSq n * ‖freqBlock P ν a n‖ ^ 2 +
        (if n = 0 then ‖freqBlock P ν a n‖ ^ 2 else 0) := by
    intro n _
    by_cases hn : n = 0
    · rw [if_pos hn]
      have := mul_nonneg (freqNormSq_nonneg n) (sq_nonneg ‖freqBlock P ν a n‖)
      linarith
    · rw [if_neg hn, add_zero]
      have hge := one_le_freqNormSq (d := d) hn
      nlinarith [sq_nonneg ‖freqBlock P ν a n‖]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  rw [hzero]
  linarith

end Gap

end GaloisForLFunctions.HTGeometry
