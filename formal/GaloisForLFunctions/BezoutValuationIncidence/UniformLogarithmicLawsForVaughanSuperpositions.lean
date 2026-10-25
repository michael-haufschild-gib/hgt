import GaloisForLFunctions.BezoutValuationIncidence.VaughanPacketGramIdentities
import GaloisForLFunctions.BezoutValuationIncidence.UniformVaughanGramsFollowTheirSmoothRankOneTerm

/-!
Uniform logarithmic laws for Vaughan superpositions, homogeneous in the
absolute coefficient sum. They control packet remainders, norms and energies,
including bounded moving coefficients at independently diverging scales.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The packet remainder is exactly the weighted sum of the five row remainders. -/
theorem pmPronicVaughanCentredPacket_sub_smooth_eq (ε : ℝ) (U V : ℕ)
    (w : Fin 5 → ℝ) (n : ℕ) :
    pmPronicVaughanCentredPacket ε U V w n -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
          (w 3 - w 2)) * (n : ℝ) ^ (1 - ε) =
      ∑ i : Fin 5, w i * pmPronicVaughanSmoothRemainder ε U V n i := by
  rw [pmPronicVaughanCentredPacket_eq_sum]
  simp only [pmPronicVaughanSmoothRemainder, mul_sub, sum_sub_distrib]
  congr 1
  rw [← mul_sub, ← sum_mul_pmPronicVaughanSmoothSigns w, mul_sum, sum_mul]
  exact sum_congr rfl fun i _ => by ring

/-- The common logarithmic row bound is uniform over all coefficient vectors after their absolute sum is included. -/
theorem exists_uniform_pmPronicVaughanPacket_smoothRemainder_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ w : Fin 5 → ℝ,
      pronicNorm (fun n => pmPronicVaughanCentredPacket ε U V w n -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
          (w 3 - w 2)) * (n : ℝ) ^ (1 - ε)) T ≤
        C * (∑ i : Fin 5, |w i|) * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) /
          Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hR⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_log_rate hε hε2 q
  refine ⟨C, hC, hR.mono fun T hT U V w => ?_⟩
  simp_rw [pmPronicVaughanCentredPacket_sub_smooth_eq]
  calc
    _ ≤ ∑ i : Fin 5, pronicNorm
        (fun n => w i * pmPronicVaughanSmoothRemainder ε U V n i) T := pronicNorm_sum_le univ _ _
    _ ≤ ∑ i : Fin 5, |w i| *
        (C * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q) := by
      apply sum_le_sum
      intro i _
      rw [pronicNorm_smul]
      exact mul_le_mul_of_nonneg_left (hT U V i) (abs_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- The reverse triangle inequality transfers the row remainder bound to the packet norm itself. -/
theorem exists_uniform_pmPronicVaughanPacket_norm_smooth_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ w : Fin 5 → ℝ,
      |pronicNorm (pmPronicVaughanCentredPacket ε U V w) T -
        |subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
          (w 3 - w 2)| * pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T| ≤
        C * (∑ i : Fin 5, |w i|) * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) /
          Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hR⟩ := exists_uniform_pmPronicVaughanPacket_smoothRemainder_log_rate hε hε2 q
  refine ⟨C, hC, hR.mono fun T hT U V w => ?_⟩
  have h := abs_pronicNorm_sub_le (pmPronicVaughanCentredPacket ε U V w)
    (fun n => (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      (w 3 - w 2)) * (n : ℝ) ^ (1 - ε)) T
  rw [pronicNorm_smul
    (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * (w 3 - w 2))
    (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T] at h
  exact h.trans (hT U V w)

/-- Equal convolution coefficients remove the smooth term at every cutoff and horizon. -/
theorem exists_uniform_pmPronicVaughanPacket_log_rate_of_equal_convolution_coefficients
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ w : Fin 5 → ℝ, w 2 = w 3 →
      pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ≤
        C * (∑ i : Fin 5, |w i|) * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) /
          Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hR⟩ := exists_uniform_pmPronicVaughanPacket_smoothRemainder_log_rate hε hε2 q
  refine ⟨C, hC, hR.mono fun T hT U V w hw => ?_⟩
  simpa only [hw, sub_self, mul_zero, zero_mul, sub_zero] using hT U V w

/-- The uniform Gram error controls every real superposition with the square of its absolute coefficient sum. -/
theorem exists_uniform_pmPronicVaughanPacket_energy_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ w : Fin 5 → ℝ,
      |pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
          (T : ℝ) ^ (1 - 2 * ε) -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          (w 3 - w 2) ^ 2 / (1 - 2 * ε)| ≤
        C * (∑ i : Fin 5, |w i|) ^ 2 / Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hG⟩ := exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate hε hε2 q
  refine ⟨C, hC, hG.mono fun T hT U V w => ?_⟩
  let k : ℝ := (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2
  let E : Fin 5 → Fin 5 → ℝ := fun i j =>
    pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) -
      k * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε)
  have hsmooth : (∑ i : Fin 5, ∑ j : Fin 5, w i * w j *
      (k * pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε))) =
        k * (w 3 - w 2) ^ 2 / (1 - 2 * ε) := by
    rw [← sum_mul_pmPronicVaughanSmoothSigns w, pow_two]
    simp only [mul_sum, sum_mul, sum_div]
    apply sum_congr rfl
    intro i _
    exact sum_congr rfl fun j _ => by ring
  have heq : pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
      (T : ℝ) ^ (1 - 2 * ε) - k * (w 3 - w 2) ^ 2 / (1 - 2 * ε) =
        ∑ i : Fin 5, ∑ j : Fin 5, w i * w j * E i j := by
    rw [sq_pronicNorm_pmPronicVaughanCentredPacket_eq_gram, ← hsmooth]
    simp only [E, mul_sub, sum_sub_distrib, sum_div, mul_div_assoc]
  change |pronicNorm (pmPronicVaughanCentredPacket ε U V w) T ^ 2 /
    (T : ℝ) ^ (1 - 2 * ε) - k * (w 3 - w 2) ^ 2 / (1 - 2 * ε)| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5, |w i * w j * E i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 5, ∑ j : Fin 5,
        |w i| * |w j| * (C / Real.log (T : ℝ) ^ q) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hT U V i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by
      rw [pow_two]
      simp only [mul_sum, sum_mul, sum_div]
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl fun j _ => by ring

/-- Every row norm vanishes at its trivial scale when the horizon and cutoff product diverge separately. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPiece_of_horizon_and_product
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hUV : Tendsto (fun t => U t * V t) atTop atTop)
    (i : Fin 5) :
    Tendsto (fun t => pronicNorm (fun n => pmPronicVaughanCentredPiece ε (U t) (V t) n i)
      (H t) / Real.sqrt ((H t : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  have h := (tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product
    hε hε2 H U V hH hUV i i).sqrt
  simpa only [← sq_pronicNorm_pmPronicVaughanCentredPiece,
    Real.sqrt_div' _ (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    Real.sqrt_sq (pronicNorm_nonneg _ _), Real.sqrt_zero] using h

/-- Bounded moving coefficient vectors preserve the zero packet limit at independent divergent scales. -/
theorem tendsto_pronicNorm_pmPronicVaughanCentredPacket_of_horizon_and_product
    {ε B : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hUV : Tendsto (fun t => U t * V t) atTop atTop)
    (w : ℕ → Fin 5 → ℝ) (hw : ∀ t i, |w t i| ≤ B) :
    Tendsto (fun t => pronicNorm (pmPronicVaughanCentredPacket ε (U t) (V t) (w t))
      (H t) / Real.sqrt ((H t : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
  let f : ℕ → Fin 5 → ℕ → ℝ := fun t i n => pmPronicVaughanCentredPiece ε (U t) (V t) n i
  have hi (i : Fin 5) : Tendsto (fun t => pronicNorm (f t i) (H t) /
      Real.sqrt ((H t : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) :=
    tendsto_pronicNorm_pmPronicVaughanCentredPiece_of_horizon_and_product hε hε2 H U V hH hUV i
  have hlim : Tendsto (fun t => B * ∑ i : Fin 5, pronicNorm (f t i) (H t) /
      Real.sqrt ((H t : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
    have hsum (s : Finset (Fin 5)) : Tendsto (fun t =>
        ∑ i ∈ s, pronicNorm (f t i) (H t) /
          Real.sqrt ((H t : ℝ) ^ (1 - 2 * ε))) atTop (𝓝 0) := by
      induction s using Finset.induction_on with
      | empty =>
          simpa only [sum_empty] using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      | @insert i s his ih =>
          simpa only [sum_insert his, add_zero] using (hi i).add ih
    simpa only [mul_zero] using (hsum univ).const_mul B
  apply squeeze_zero' (Eventually.of_forall fun t =>
    div_nonneg (pronicNorm_nonneg _ _) (Real.sqrt_nonneg _)) ?_ hlim
  refine Eventually.of_forall fun t => ?_
  have heq : pmPronicVaughanCentredPacket ε (U t) (V t) (w t) =
      fun n => ∑ i : Fin 5, w t i * f t i n := funext
        (pmPronicVaughanCentredPacket_eq_sum ε (U t) (V t) (w t))
  rw [heq]
  have hnorm : pronicNorm (fun n => ∑ i : Fin 5, w t i * f t i n) (H t) ≤
      B * ∑ i : Fin 5, pronicNorm (f t i) (H t) := by
    calc
      _ ≤ ∑ i : Fin 5, pronicNorm (fun n => w t i * f t i n) (H t) := pronicNorm_sum_le univ _ _
      _ ≤ ∑ i : Fin 5, B * pronicNorm (f t i) (H t) := by
        apply sum_le_sum
        intro i _
        rw [pronicNorm_smul]
        exact mul_le_mul_of_nonneg_right (hw t i) (pronicNorm_nonneg _ _)
      _ = _ := (mul_sum _ _ _).symm
  simpa only [sum_div, mul_div_assoc] using
    div_le_div_of_nonneg_right hnorm (Real.sqrt_nonneg ((H t : ℝ) ^ (1 - 2 * ε)))

#print axioms tendsto_pronicNorm_pmPronicVaughanCentredPiece_of_horizon_and_product
#print axioms tendsto_pronicNorm_pmPronicVaughanCentredPacket_of_horizon_and_product
#print axioms exists_uniform_pmPronicVaughanPacket_energy_log_rate
#print axioms pmPronicVaughanCentredPacket_sub_smooth_eq
#print axioms exists_uniform_pmPronicVaughanPacket_smoothRemainder_log_rate
#print axioms exists_uniform_pmPronicVaughanPacket_norm_smooth_log_rate
#print axioms exists_uniform_pmPronicVaughanPacket_log_rate_of_equal_convolution_coefficients
end GaloisForLFunctions.BezoutValuationIncidence
