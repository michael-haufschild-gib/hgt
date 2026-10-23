import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths

/-!
# The degree filtration of the Hodge defect

Degree on the scaling surface is aperture. The **Hodge defect at degree `a`**
(`hodgeDefectAt Z a`) is the largest number of negative squares of the Weil form on a finite
family of `C²` tests supported in `[−a, a]`, in `ℕ∞`. It is a metrology of the off-line zeros:

* it is nondecreasing in the degree (`hodgeDefectAt_mono`) and bounded by the number of zeros
  right of the line (`hodgeDefectAt_le`);
* it exhausts them: `⨆_a hodgeDefectAt Z a = #{Re ρ > ½}` for every tempered configuration
  (`iSup_hodgeDefectAt`), the degree form of the Pontryagin law;
* for `ζ` it vanishes through degree `3/10` (`zeta_hodgeDefectAt_eq_zero`), by the unconditional
  positivity of the Weil form of `ζ` at small aperture.

No off-line zero of `ζ` is visible below degree `3/10`, and every finite set of them is visible at
some finite degree. Quantitative horizons for the `ε`-negative index at level `a` are in
`RHTower.zeta_weil_inertia_law`.
-/

open Complex Set
open scoped ComplexConjugate
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig
  exists_radius_of_hasCompactSupport zetaZeroConfig_re_W_nonneg_of_aperture_le_threeTenths)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The Hodge defect at degree `a`: the largest number of negative squares of the Weil form on a
finite family of `C²` tests supported in `[−a, a]`. -/
def hodgeDefectAt (Z : ZeroConfig) (a : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (f : Fin n → ℝ → ℂ) (_ : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a),
    (hermNegIndex (zeroGram Z f) : ℕ∞)

theorem le_hodgeDefectAt (Z : ZeroConfig) {a : ℝ} {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a) :
    (hermNegIndex (zeroGram Z f) : ℕ∞) ≤ hodgeDefectAt Z a :=
  le_iSup₂_of_le n f (le_iSup_of_le hf le_rfl)

/-- The Hodge defect is nondecreasing in the degree. -/
theorem hodgeDefectAt_mono (Z : ZeroConfig) : Monotone (hodgeDefectAt Z) := fun a b hab =>
  iSup₂_mono fun n f => iSup_le fun hf => le_hodgeDefectAt Z f fun i =>
    ⟨(hf i).1, (hf i).2.trans (Icc_subset_Icc (neg_le_neg hab) hab)⟩

/-- The Hodge defect at any degree is at most the number of zeros right of the line. -/
theorem hodgeDefectAt_le (Z : ZeroConfig) (hZ : TemperedConfig Z) (a : ℝ) :
    hodgeDefectAt Z a ≤ (rightZeros Z).encard :=
  iSup₂_le fun n f => iSup_le fun hf => negIndex_zeroGram_le_of_tempered Z hZ f
    (fun i => (hf i).1)
    (fun i => isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2)

/-- A finite family of compactly supported tests lives in some `[−a, a]`. -/
theorem exists_aperture {n : ℕ} (f : Fin n → ℝ → ℂ) (hfc : ∀ i, HasCompactSupport (f i)) :
    ∃ a : ℝ, ∀ i, tsupport (f i) ⊆ Icc (-a) a := by
  choose A hA0 hA using fun i => exists_radius_of_hasCompactSupport (hfc i)
  refine ⟨∑ i, A i, fun i => ?_⟩
  have hle : A i ≤ ∑ j, A j :=
    Finset.single_le_sum (fun j _ => hA0 j) (Finset.mem_univ i)
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  have hlt : A i < |u| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hout
    rcases hout with h | h
    · rw [abs_of_neg (by linarith [hA0 i])]; linarith
    · rw [abs_of_pos (by linarith [hA0 i])]; linarith
  exact hu (hA i u hlt)

/-- **The degree filtration exhausts the zeros right of the line.** -/
theorem iSup_hodgeDefectAt (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    ⨆ a, hodgeDefectAt Z a = (rightZeros Z).encard := by
  refine le_antisymm (iSup_le (hodgeDefectAt_le Z hZ)) ?_
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  obtain ⟨f, hf, hfc, hle⟩ := (pontryagin_law Z hZ n).mpr hn
  obtain ⟨a, ha⟩ := exists_aperture f hfc
  calc (n : ℕ∞) ≤ hermNegIndex (zeroGram Z f) := ENat.coe_le_coe.mpr hle
    _ ≤ hodgeDefectAt Z a := le_hodgeDefectAt Z f fun i => ⟨hf i, ha i⟩
    _ ≤ ⨆ a, hodgeDefectAt Z a := le_iSup _ a

/-- **No off-line zero of `ζ` is visible below degree `3/10`.** -/
theorem zeta_hodgeDefectAt_eq_zero {a : ℝ} (ha : a ≤ 3 / 10) :
    hodgeDefectAt zetaZeroConfig a = 0 := by
  refine le_antisymm (iSup₂_le fun n f => iSup_le fun hf => ?_) (zero_le _)
  have hfc : ∀ i, HasCompactSupport (f i) := fun i =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hf i).2
  rw [negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_, Nat.cast_zero]
  rw [hermQuad_zeroGram_of_tempered zetaZeroConfig temperedConfig_zetaZeroConfig f
    (fun i => (hf i).1) hfc]
  refine zetaZeroConfig_re_W_nonneg_of_aperture_le_threeTenths
    (contDiff_sum_smul f (fun i => (hf i).1) _) (closure_minimal (fun u hu => ?_) isClosed_Icc)
  by_contra hout
  apply hu
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have : f i u = 0 := image_eq_zero_of_notMem_tsupport fun h => hout
    (Icc_subset_Icc (by linarith) ha ((hf i).2 h))
  simp [this]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
