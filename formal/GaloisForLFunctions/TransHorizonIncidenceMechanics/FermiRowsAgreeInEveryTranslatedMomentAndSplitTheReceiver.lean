import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipOfTheFermiSquarefreeWeightBreaksTheReceiver

/-!
# The Fermi rows agree in every translated moment and split the receiver

At horizon `N` take the Fermi row `F_N = F · 1_{≤N}` and its even flip `F_N^♭`, the row whose
Selberg coordinates are `σ₂(e) Y_N(e)` (`σ₂(e) = −1` exactly on even `e`).

* The rows are squarefree, so by the even-flip law **every translated moment of every degree and
  every shift agrees**: no additive observable of any degree separates `F_N` from `F_N^♭`, at any
  horizon.
* The rows vanish on multiples of four, so the Fermi transform gives `F_N^♭ = F_N + c_e ⋆ (δ₁ − 2δ₂)`,
  and `F_N^♭(d) = F^♭(d)` once `N ≥ 2d` (step `N ↦ N + 1` stabilises every coordinate).

Hence at every fixed cutoff `T` the receiver energies of the rows converge to those of `F` and `F^♭`:
the Fermi rows stay below one bound at every cutoff, while for every `C` the flipped rows exceed `C`
at all large horizons. The trans-horizon receiver is the observable that separates the pair; it
sees the dilation `k ↦ 2k` through the pole of the odd squarefree weight.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

theorem fermiWeight_eq_zero_of_not_squarefree (ε : ℝ) {d : ℕ} (hd : ¬ Squarefree d) :
    fermiWeight ε d = 0 := by
  rcases eq_or_ne d 0 with rfl | hd0
  · exact fermiWeight_zero ε
  have ho : ∀ n, ¬ Squarefree n → oddSqfWeight ε n = 0 := fun n hn => by
    simp [oddSqfWeight, dampedSignWeight, oddSqfAF_apply, hn]
  rw [fermiWeight_apply ε hd0, ho d hd]
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left m two_pos]
    by_cases hm : ¬ 2 ∣ m ∧ Squarefree m
    · exfalso
      refine hd (Nat.squarefree_mul_iff.mpr ⟨Nat.coprime_two_left.mpr ?_, Nat.squarefree_two, hm.2⟩)
      exact Nat.odd_iff.mpr (by omega)
    · rw [show oddSqfWeight ε m = 0 by
        simp only [oddSqfWeight, dampedSignWeight, oddSqfAF_apply, if_neg hm, zero_mul]]
      ring
  · ring

/-- The Fermi row at horizon `N`. -/
def fermiRow (ε : ℝ) (N d : ℕ) : ℝ := if d ≤ N then fermiWeight ε d else 0

theorem selbergMultiplesCoord_fermiRow_of_not_squarefree (ε : ℝ) (N : ℕ) {e : ℕ}
    (he : ¬ Squarefree e) : selbergMultiplesCoord N (fermiRow ε N) e = 0 := by
  unfold selbergMultiplesCoord
  refine sum_eq_zero fun d hd => ?_
  have hed := (mem_filter.mp hd).2
  have hsq : ¬ Squarefree d := fun h => he (Squarefree.squarefree_of_dvd hed h)
  simp [fermiRow, fermiWeight_eq_zero_of_not_squarefree ε hsq]

/-- **No translated moment of any degree separates the rows.** -/
theorem translatedMoment_evenFlipRow_fermiRow (ε : ℝ) (N : ℕ) {m : ℕ} (v : Fin m → ℕ) :
    SieveMoments.translatedMoment N (evenFlipRow N (fermiRow ε N)) v =
      SieveMoments.translatedMoment N (fermiRow ε N) v :=
  translatedMoment_evenFlipRow N _ (fun _ he => selbergMultiplesCoord_fermiRow_of_not_squarefree ε N he) v

/-- The flipped rows stabilise: `F_N^♭(d) = F^♭(d)` for `N ≥ 2d`. -/
theorem evenFlipRow_fermiRow_eq (ε : ℝ) {N d : ℕ} (hN : 2 * d ≤ N) :
    evenFlipRow N (fermiRow ε N) d = fermiFlipWeight ε d := by
  rw [evenFlipRow_eq N _ (fun d hd => by simp [fermiRow, show ¬ d ≤ N by omega])
    (fun d h4 => by simp [fermiRow, fermiWeight_of_four_dvd ε h4]), fermiFlipWeight_eq]
  have hpart : ∀ x, x ≤ d → evenPartWeight (fermiRow ε N) x = evenPartWeight (fermiWeight ε) x :=
    fun x hx => by simp [evenPartWeight, fermiRow, show 2 * x ≤ N by omega]
  simp only [localFactorWeight]
  rw [hpart d le_rfl, hpart (d / 2) (Nat.div_le_self d 2)]
  simp [fermiRow, show d ≤ N by omega]

theorem selbergMultiplesCoord_one_evenFlipRow_fermiRow (ε : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    selbergMultiplesCoord N (evenFlipRow N (fermiRow ε N)) 1 =
      selbergMultiplesCoord N (fermiRow ε N) 1 := by
  rw [evenFlipRow, selbergMultiplesCoord_scaledSelbergRow _ _ (mem_Icc.mpr ⟨le_rfl, hN⟩)]
  simp [evenSign]

theorem tendsto_selbergMultiplesCoord_one_fermiRow {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => selbergMultiplesCoord N (fermiRow ε N) 1) atTop
      (𝓝 (∑' d : ℕ, fermiWeight ε d / d)) := by
  have hs := summable_div_of_dampedClass hε (fermiWeight_mem_dampedClass ε)
  refine ((hs.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).congr fun N => ?_
  simp only [Function.comp_apply, selbergMultiplesCoord]
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  simp only [Nat.cast_zero, div_zero, zero_add, one_dvd, filter_true_of_mem fun _ _ => trivial]
  exact sum_congr rfl fun d hd => by simp [fermiRow, (mem_Icc.mp hd).2]

/-- The means of the pair agree: `W_{F^♭}(1) = W_F(1)`. -/
theorem tsum_fermiFlipWeight_div {ε : ℝ} (hε : 0 < ε) :
    ∑' d : ℕ, fermiFlipWeight ε d / d = ∑' d : ℕ, fermiWeight ε d / d := by
  have h := weightRamanujanCoeff_fermiFlipWeight hε 1
  simpa [weightRamanujanCoeff, evenSign] using h

/-- **The Fermi parity rows.** For `0 < ε ≤ 1/2`: at every horizon the Fermi row and its even flip
have the same translated moments of every degree; at every cutoff the rows' receiver energies stay,
for all large horizons, below one bound; and for every `C` the flipped rows' energies exceed `C` at
all large horizons. -/
theorem fermi_parityRows {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ N m (v : Fin m → ℕ), SieveMoments.translatedMoment N (evenFlipRow N (fermiRow ε N)) v =
        SieveMoments.translatedMoment N (fermiRow ε N) v) ∧
    (∃ E : ℝ, ∀ T : ℕ, ∀ᶠ N in atTop, horizonPronicEnergy N (fermiRow ε N) T ≤ E) ∧
    (∀ C : ℝ, ∀ᶠ N in atTop, ∃ T, C < horizonPronicEnergy N (evenFlipRow N (fermiRow ε N)) T) := by
  have hmean := tendsto_selbergMultiplesCoord_one_fermiRow hε
  refine ⟨fun N _ v => translatedMoment_evenFlipRow_fermiRow ε N v, ?_, fun C => ?_⟩
  · obtain ⟨E, hE⟩ := receiverBounded_fermiWeight hε
    refine ⟨E + 1, fun T => ?_⟩
    have hrow : ∀ d, Tendsto (fun N => fermiRow ε N d) atTop (𝓝 (fermiWeight ε d)) := fun d =>
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop d] with N hN
        simp [fermiRow, hN])
    have hconv := tendsto_weightPronicEnergy_of_pointwise hrow hmean T
    filter_upwards [hconv.eventually (gt_mem_nhds (show weightPronicEnergy (fermiWeight ε)
      (∑' d : ℕ, fermiWeight ε d / d) T < E + 1 by linarith [hE T]))] with N hN
    exact hN.le
  · have hflip := not_receiverBounded_fermiFlipWeight hε hε2
    unfold ReceiverBounded at hflip
    push Not at hflip
    obtain ⟨T, hT⟩ := hflip C
    rw [tsum_fermiFlipWeight_div hε] at hT
    have hrow : ∀ d, Tendsto (fun N => evenFlipRow N (fermiRow ε N) d) atTop
        (𝓝 (fermiFlipWeight ε d)) := fun d =>
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop (2 * d)] with N hN
        exact (evenFlipRow_fermiRow_eq ε hN).symm)
    have hmean' : Tendsto (fun N => selbergMultiplesCoord N (evenFlipRow N (fermiRow ε N)) 1) atTop
        (𝓝 (∑' d : ℕ, fermiWeight ε d / d)) :=
      hmean.congr' (by
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact (selbergMultiplesCoord_one_evenFlipRow_fermiRow ε hN).symm)
    have hconv := tendsto_weightPronicEnergy_of_pointwise hrow hmean' T
    filter_upwards [hconv.eventually (lt_mem_nhds hT)] with N hN
    exact ⟨T, hN⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
