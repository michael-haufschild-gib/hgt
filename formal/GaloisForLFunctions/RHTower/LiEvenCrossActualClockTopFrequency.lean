import GaloisForLFunctions.RHTower.XiDivisorSupportedMetric
import Mathlib.Data.Finset.Max
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite isolation of the maximal reciprocal-frequency growth rate

Square summability makes every positive upper level finite.  A positive witness therefore
produces an attained maximum with finitely many ties and a strict gap below those ties.
The actual Xi instance retains every analytic multiplicity copy in the top packet.
-/

open scoped Topology

open Filter

namespace RHTower
noncomputable section

/-- Every positive upper level of a square-summable real family is finite. -/
theorem finite_upper_level_of_summable_sq {ι : Type*} (f : ι → ℝ)
    (hs : Summable (fun i => f i^2)) {a : ℝ} (ha : 0 < a) :
    {i | a ≤ f i}.Finite := by
  have ht := hs.tendsto_cofinite_zero.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < a^2))
  rw [Filter.eventually_cofinite] at ht
  apply ht.subset
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  exact not_lt_of_ge (pow_le_pow_left₀ ha.le hi 2)

/-- A positive square-summable family value supplies a finite attained top and a strict lower gap. -/
theorem exists_finite_positive_top_with_gap_of_summable_sq {ι : Type*}
    (f : ι → ℝ) (hs : Summable (fun i => f i^2)) (hp : ∃ i, 0 < f i) :
    ∃ b : ℝ, 0 < b ∧ {i | f i = b}.Finite ∧ {i | f i = b}.Nonempty ∧
      (∀ i, f i ≤ b) ∧ ∃ b₂ : ℝ, 0 ≤ b₂ ∧ b₂ < b ∧
        ∀ i, f i ≠ b → f i ≤ b₂ := by
  classical
  obtain ⟨i₀, hi₀⟩ := hp
  let a : ℝ := f i₀ / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hF := finite_upper_level_of_summable_sq f hs ha
  let F := hF.toFinset
  have hi₀F : i₀ ∈ F := by
    apply hF.mem_toFinset.mpr
    dsimp [a]
    linarith
  let V := F.image f
  have hV : V.Nonempty := ⟨f i₀, Finset.mem_image.mpr ⟨i₀, hi₀F, rfl⟩⟩
  let b := V.max' hV
  have hbase : f i₀ ≤ b := V.le_max' _ (Finset.mem_image.mpr ⟨i₀, hi₀F, rfl⟩)
  have hab : a < b := by dsimp [a]; linarith
  have hb : 0 < b := hi₀.trans_le hbase
  have hsmall : ∀ i, i ∉ F → f i < a := by
    intro i hi
    have hnot : ¬a ≤ f i := by simpa [F] using hi
    exact lt_of_not_ge hnot
  have hbound : ∀ i, f i ≤ b := by
    intro i
    by_cases hi : i ∈ F
    · exact V.le_max' _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact (hsmall i hi).le.trans hab.le
  have hbmem : b ∈ F.image f := V.max'_mem hV
  obtain ⟨i₁, hi₁, hi₁b⟩ := Finset.mem_image.mp hbmem
  have htopfinite : {i | f i = b}.Finite := by
    apply hF.subset
    intro i hi
    change a ≤ f i
    change f i = b at hi
    rw [hi]
    exact hab.le
  let G := F.filter (fun i => f i ≠ b)
  let U := insert a (G.image f)
  have hU : U.Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  let b₂ := U.max' hU
  have hab₂ : a ≤ b₂ := U.le_max' _ (Finset.mem_insert_self _ _)
  have hb₂ : 0 ≤ b₂ := ha.le.trans hab₂
  have hgap : b₂ < b := by
    have hmem : b₂ ∈ insert a (G.image f) := U.max'_mem hU
    rcases Finset.mem_insert.mp hmem with heq | hmem
    · simpa only [heq] using hab
    · obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hmem
      have hne : f i ≠ b := (Finset.mem_filter.mp hi).2
      have hlt : f i < b := lt_of_le_of_ne (hbound i) hne
      simpa only [hfi] using hlt
  refine ⟨b, hb, htopfinite, ⟨i₁, hi₁b⟩, hbound, b₂, hb₂, hgap, ?_⟩
  intro i hne
  by_cases hi : i ∈ F
  · have hiG : i ∈ G := Finset.mem_filter.mpr ⟨hi, hne⟩
    exact U.le_max' _ (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨i, hiG, rfl⟩))
  · exact (hsmall i hi).le.trans hab₂

/-- The absolute imaginary reciprocal frequency of one actual Xi multiplicity copy. -/
def liEvenCrossActualClockReciprocalGrowthRate (q : XiZeroCopy) : ℝ :=
  |((xiSpectralPoint q)⁻¹).im|

/-- The full multiplicity-copy fiber of one reciprocal growth rate. -/
def liEvenCrossActualClockTopPacket (b : ℝ) : Set XiZeroCopy :=
  {q | liEvenCrossActualClockReciprocalGrowthRate q = b}

/-- Reciprocal growth rates are nonnegative. -/
theorem liEvenCrossActualClockReciprocalGrowthRate_nonneg (q : XiZeroCopy) :
    0 ≤ liEvenCrossActualClockReciprocalGrowthRate q := abs_nonneg _

/-- Imaginary reciprocal frequencies inherit the complete reciprocal-square source mass. -/
theorem summable_liEvenCrossActualClockReciprocalGrowthRate_sq :
    Summable (fun q : XiZeroCopy => liEvenCrossActualClockReciprocalGrowthRate q^2) := by
  have hn : Summable (fun q : XiZeroCopy => ‖(xiSpectralPoint q)⁻¹‖^2) := by
    simpa [norm_inv, one_div, inv_pow] using xiSpectralPoint_inv_sq_summable
  apply Summable.of_nonneg_of_le (fun q => sq_nonneg _) _ hn
  intro q
  exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2

/-- Only finitely many actual Xi multiplicity copies exceed a positive reciprocal growth threshold. -/
theorem finite_liEvenCrossActualClockReciprocalGrowthRate_ge {a : ℝ} (ha : 0 < a) :
    {q | a ≤ liEvenCrossActualClockReciprocalGrowthRate q}.Finite :=
  finite_upper_level_of_summable_sq liEvenCrossActualClockReciprocalGrowthRate
    summable_liEvenCrossActualClockReciprocalGrowthRate_sq ha

/-- Failure of RH supplies a nonreal reciprocal source frequency. -/
theorem exists_liEvenCrossActualClockReciprocalGrowthRate_pos_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    ∃ q : XiZeroCopy, 0 < liEvenCrossActualClockReciprocalGrowthRate q := by
  by_contra hno
  have hz : ∀ q, liEvenCrossActualClockReciprocalGrowthRate q = 0 := by
    intro q
    apply le_antisymm
    · exact le_of_not_gt (fun hp => hno ⟨q, hp⟩)
    · exact liEvenCrossActualClockReciprocalGrowthRate_nonneg q
  apply hnot
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have him : ((xiSpectralPoint q)⁻¹).im = 0 := abs_eq_zero.mp (hz q)
  have hinv : (xiSpectralPoint q)⁻¹ = (((xiSpectralPoint q)⁻¹).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  refine ⟨((xiSpectralPoint q)⁻¹).re⁻¹, ?_⟩
  simpa only [inv_inv, ← Complex.ofReal_inv] using
    congrArg (fun z : ℂ => z⁻¹) hinv

/-- Failure of RH gives a nonempty finite maximal packet and a strict gap for every remaining copy. -/
theorem exists_liEvenCrossActualClockTopPacket_of_not_rh (hnot : ¬RiemannHypothesis) :
    ∃ b : ℝ, 0 < b ∧ (liEvenCrossActualClockTopPacket b).Finite ∧
      (liEvenCrossActualClockTopPacket b).Nonempty ∧
      (∀ q, liEvenCrossActualClockReciprocalGrowthRate q ≤ b) ∧
      ∃ b₂ : ℝ, 0 ≤ b₂ ∧ b₂ < b ∧ ∀ q, q ∉ liEvenCrossActualClockTopPacket b →
        liEvenCrossActualClockReciprocalGrowthRate q ≤ b₂ := by
  simpa only [liEvenCrossActualClockTopPacket, Set.mem_setOf_eq] using
    exists_finite_positive_top_with_gap_of_summable_sq
      liEvenCrossActualClockReciprocalGrowthRate
      summable_liEvenCrossActualClockReciprocalGrowthRate_sq
      (exists_liEvenCrossActualClockReciprocalGrowthRate_pos_of_not_rh hnot)

end
end RHTower
