import GaloisForLFunctions.HodgeTheoryOfAFixedPart.RobustCombIndexCreatesNoExtraZeros
import GaloisForLFunctions.HodgeTheoryOfAFixedPart.FiniteCombSamplingGrams
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFiniteStratumIsThePacketIndexDichotomy
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheSignIsCarriedByTheContacts

/-!
# The robust finite-comb index counts the right zeros

Every finite negative Weil family is sampled, after one common translation,
with a fixed negative mass margin. Conversely, block compression and
smoothing rule out any additional negative squares with such a margin.
-/

noncomputable section

open Finset Filter Topology Matrix Zeta23

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open HTGeometry AbsoluteGeometryOfSpecZ ArithmeticIndexDescent ArithmeticCastelnuovoSeveri
open ArithmeticOrientationGeometry SquareRootThreshold

/-- A single translation puts a finite packet family inside a sampling
window and preserves every Weil entry. -/
theorem exists_sampling_window_same_WeilGram {n : ℕ} (f : Fin n → realTests) :
    ∃ (K : ℕ) (g : Fin n → realTests), 1 ≤ K ∧
      (∀ i u, u ≤ Real.log 3 ∨ Real.log K ≤ u → (g i).1 u = 0) ∧
      complexWeilMixed g g = complexWeilMixed f f := by
  obtain ⟨R, _, B, _, hs⟩ := LogCells.exists_common_logCell_window (fun i => (f i).1)
    (fun i => (f i).2.1) (fun i => (f i).2.2)
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (Real.log B + Real.log 3 + 1))
  have hK0 : (0 : ℝ) < K := (Real.exp_pos _).trans hK
  have hK1 : 1 ≤ K := by exact_mod_cast hK0
  have hlog : Real.log B + Real.log 3 + 1 < Real.log K := by
    have h := Real.log_lt_log (Real.exp_pos _) hK
    simpa only [Real.log_exp] using h
  let a := R + Real.log 3 + 1
  let g : Fin n → realTests := fun i =>
    ⟨fun u => (f i).1 (u - a), (f i).2.1.comp (contDiff_id.sub contDiff_const),
      (f i).2.2.comp_homeomorph (Homeomorph.subRight a)⟩
  refine ⟨K, g, hK1, ?_, ?_⟩
  · intro i u hu
    apply hs i (u - a)
    rcases hu with hu | hu
    · left
      dsimp [a]
      linarith only [hu]
    · right
      dsimp [a]
      linarith only [hu, hlog]
  · rw [← realPolarGram_zeroSum g, ← realPolarGram_zeroSum f]
    ext i j
    change (((zeroSum (fun u => (f i).1 (u - a)) +
      zeroSum (fun u => (f j).1 (u - a)) -
      zeroSum (fun u => (f j - f i).1 (u - a))) / 2 : ℝ) : ℂ) = _
    rw [zeroSum_translate (f i).2.1 (f i).2.2,
      zeroSum_translate (f j).2.1 (f j).2.2,
      zeroSum_translate (f j - f i).2.1 (f j - f i).2.2]
    rfl

/-- The distinct right-zero count is exactly the number of negative comb
directions that can persist on a fixed window with a fixed mass margin. -/
theorem nat_le_rightZeros_iff_eventual_robustCombIndex (r : ℕ) :
    (r : ℕ∞) ≤ (ArithmeticCastelnuovoSeveri.rightZeros zetaZeroConfig).encard ↔
      ∃ K : ℕ, 1 ≤ K ∧ ∃ η : ℝ, 0 < η ∧
        ∀ᶠ N : ℕ in atTop, (r : ℕ∞) ≤ robustCombIndex (Ioc N (N + 3 * K * N)) η := by
  constructor
  · intro hr
    obtain ⟨f, hf, hfc, hneg⟩ :=
      (pontryagin_law zetaZeroConfig temperedConfig_zetaZeroConfig r).mpr hr
    obtain ⟨m, g, hg, hgc, hindex⟩ := exists_real_packets_negIndex_ge f hf hfc
    let F : Fin m → realTests := fun i => ⟨g i, hg i, hgc i⟩
    have hF : r ≤ hermNegIndex (complexWeilMixed F F) := by
      rw [complexWeilMixed_eq_weilGram F]
      exact hneg.trans hindex
    obtain ⟨K, G, hK, hs, hGram⟩ := exists_sampling_window_same_WeilGram F
    obtain ⟨η, hη, hev⟩ := exists_margin_eventually_packet_index_le_robustCombIndex G hK hs
    refine ⟨K, hK, η, hη, ?_⟩
    filter_upwards [hev] with N hN
    rw [hGram] at hN
    exact (ENat.coe_le_coe.mpr hF).trans hN
  · rintro ⟨K, _, η, hη, hev⟩
    obtain ⟨N, hN, hupper⟩ := (hev.and (eventually_robustCombIndex_le_rightZeros K hη)).exists
    exact hN.trans hupper

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
