import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilsFormIsContinuousUnderPacketSmoothing
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheHodgeIndexOfThePairingOfTheDegreePoints
import GaloisForLFunctions.ArithmeticIndexDescent.TheCompleteCellsCaptureEveryFiniteIndex

/-!
# Bounded packets create no extra negative squares

Finite-energy bounded packets admit simultaneous smoothing in every mixed
Weil entry. Every negative subspace therefore survives in a smooth family,
whose index is bounded by the number of distinct right zeros.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry ArithmeticCastelnuovoSeveri ArithmeticIndexDescent SpacingScaleHarmonicAnalysis

/-- The complex Gram matrix obtained by real polarization of the full
bounded-packet form. -/
def packetFormGram {ι : Type*} (Q : ℕ) (f : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => (((packetForm Q (f i + f j) - packetForm Q (f i - f j)) / 4 : ℝ) : ℂ)

private theorem zeroSum_eq_weilQuad_realTest (f : realTests) :
    zeroSum f.1 = weilQuad f.1 := by
  rw [LogCells.weilQuad_eq_zetaW f.2.1 f.2.2]
  rfl

private theorem negIndex_complexWeilMixed_le {n : ℕ} (f : Fin n → realTests) :
    (hermNegIndex (complexWeilMixed f f) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  rw [complexWeilMixed_eq_weilGram f]
  exact negIndex_defect_packets_le (fun i => (f i).2.1) (fun i => (f i).2.2)

/-- The index bound extends from smooth tests to bounded finite-energy
packets. All pair sums and differences are smoothed by the same bump. -/
theorem negIndex_packetFormGram_le_rightZeros {n Q : ℕ} (f : Fin n → ℝ → ℝ)
    (hfm : ∀ i, Measurable (f i)) {M : Fin n → ℝ} (hfb : ∀ i u, |f i u| ≤ M i)
    {l r : ℝ} (hs : ∀ i u, f i u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJadd : ∀ i j, IntegrableOn (levyJump (f i + f j)) (Set.Ioi 0))
    (hJsub : ∀ i j, IntegrableOn (levyJump (f i - f j)) (Set.Ioi 0)) :
    (hermNegIndex (packetFormGram Q f) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  let F : ℕ → Fin n → realTests := fun k i =>
    ⟨mollify (shrinkingBump k) (f i),
      contDiff_mollify (shrinkingBump k) (hfm i) (hfb i) (hs i),
      hasCompactSupport_mollify (shrinkingBump k) (hs i)⟩
  have hvanish : ∀ i u, ¬ (l ≤ u ∧ u ≤ r) → f i u = 0 := by
    intro i u hu
    by_contra hne
    exact hu (hs i u hne)
  have hplus : ∀ i j u, |(f i + f j) u| ≤ M i + M j := by
    intro i j u
    have hi := abs_le.mp (hfb i u)
    have hj := abs_le.mp (hfb j u)
    apply abs_le.mpr
    constructor <;> change _ ≤ _ <;> dsimp only [Pi.add_apply] <;>
      linarith only [hi.1, hi.2, hj.1, hj.2]
  have hminus : ∀ i j u, |(f i - f j) u| ≤ M i + M j := by
    intro i j u
    have hi := abs_le.mp (hfb i u)
    have hj := abs_le.mp (hfb j u)
    apply abs_le.mpr
    constructor <;> dsimp only [Pi.sub_apply] <;>
      linarith only [hi.1, hi.2, hj.1, hj.2]
  have hsplus : ∀ i j u, (f i + f j) u ≠ 0 → l ≤ u ∧ u ≤ r := by
    intro i j u hne
    by_contra hu
    exact hne (by simp only [Pi.add_apply, hvanish i u hu, hvanish j u hu, add_zero])
  have hsminus : ∀ i j u, (f i - f j) u ≠ 0 → l ≤ u ∧ u ≤ r := by
    intro i j u hne
    by_contra hu
    exact hne (by simp only [Pi.sub_apply, hvanish i u hu, hvanish j u hu, sub_self])
  have hconv : ∀ i j,
      Tendsto (fun k => complexWeilMixed (F k) (F k) i j) atTop
        (𝓝 (packetFormGram Q f i j)) := by
    intro i j
    have hp := tendsto_zeroSum_mollify ((hfm i).add (hfm j)) (hplus i j)
      (hsplus i j) hQ (hJadd i j)
    have hm := tendsto_zeroSum_mollify ((hfm i).sub (hfm j)) (hminus i j)
      (hsminus i j) hQ (hJsub i j)
    have ht := (Complex.continuous_ofReal.tendsto _).comp ((hp.sub hm).div_const 4)
    refine ht.congr' (Eventually.of_forall fun k => ?_)
    change (((zeroSum (mollify (shrinkingBump k) (f i + f j)) -
      zeroSum (mollify (shrinkingBump k) (f i - f j))) / 4 : ℝ) : ℂ) =
        (realWeilForm (F k i) (F k j) : ℂ)
    rw [mollify_add_bounded _ (hfm i) (hfm j) (hfb i) (hfb j),
      mollify_sub_bounded _ (hfm i) (hfm j) (hfb i) (hfb j)]
    change (((zeroSum (F k i + F k j).1 - zeroSum (F k i - F k j).1) / 4 : ℝ) : ℂ) = _
    rw [zeroSum_eq_weilQuad_realTest, zeroSum_eq_weilQuad_realTest]
    exact congrArg Complex.ofReal (completeCell_limit_pair (F k i) (F k j))
  obtain ⟨k, hk⟩ := (eventually_negIndex_limit_le
    (fun k => complexWeilMixed (F k) (F k)) (packetFormGram Q f) hconv).exists
  exact (ENat.coe_le_coe.mpr hk).trans (negIndex_complexWeilMixed_le (F k))

/-- The elementary Gram of any finite nested-window family has no more
negative squares than there are distinct right zeros. -/
theorem negIndex_nested_packetFormGram_le_rightZeros {n Q x₀ X : ℕ}
    (hx₀ : 1 ≤ x₀) (hQ₀ : 1 ≤ Q) (x : Fin n → ℕ)
    (hx : ∀ i, x₀ ≤ x i ∧ x i ≤ X) (hQ : X ≤ Q * x₀) :
    (hermNegIndex (packetFormGram Q (fun i => flatPacket x₀ (x i))) : ℕ∞) ≤
      (rightZeros zetaZeroConfig).encard := by
  have hx₀' : (0 : ℝ) < x₀ := by exact_mod_cast hx₀
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ₀
  have hs : ∀ i u, flatPacket (x₀ : ℝ) (x i) u ≠ 0 →
      Real.log x₀ ≤ u ∧ u ≤ Real.log x₀ + Real.log Q := by
    intro i u hne
    have hm : u ∈ Set.Ioc (Real.log x₀) (Real.log (x i)) := by
      by_contra hu
      exact hne (by simp only [flatPacket]; exact Set.indicator_of_notMem hu _)
    have hxi : (0 : ℝ) < x i := hx₀'.trans_le (by exact_mod_cast (hx i).1)
    have hlog : Real.log (x i) ≤ Real.log x₀ + Real.log Q := by
      rw [add_comm, ← Real.log_mul hQ'.ne' hx₀'.ne']
      exact Real.log_le_log hxi (by exact_mod_cast (hx i).2.trans hQ)
    exact ⟨hm.1.le, hm.2.trans hlog⟩
  apply negIndex_packetFormGram_le_rightZeros (fun i => flatPacket x₀ (x i))
    (fun i => measurable_flatPacket _ _) (fun i u => abs_flatPacket_le _ _ _) hs
    (by rw [add_sub_cancel_left]; exact Real.log_lt_log hQ' (by linarith))
  · intro i j
    change IntegrableOn (levyJump (fun u => flatPacket (x₀ : ℝ) (x i) u +
      flatPacket (x₀ : ℝ) (x j) u)) (Set.Ioi 0)
    have hxx : ∀ k ∈ (Finset.univ : Finset (Fin 2)), x₀ ≤ (![x i, x j] : Fin 2 → ℕ) k := by
      intro k _
      fin_cases k
      · exact (hx i).1
      · exact (hx j).1
    simpa [Fin.sum_univ_two] using
      (integrableOn_levyJump_step hx₀ hxx (fun _ : Fin 2 => (1 : ℝ)))
  · intro i j
    change IntegrableOn (levyJump (fun u => flatPacket (x₀ : ℝ) (x i) u -
      flatPacket (x₀ : ℝ) (x j) u)) (Set.Ioi 0)
    have hxx : ∀ k ∈ (Finset.univ : Finset (Fin 2)), x₀ ≤ (![x i, x j] : Fin 2 → ℕ) k := by
      intro k _
      fin_cases k
      · exact (hx i).1
      · exact (hx j).1
    simpa [Fin.sum_univ_two, sub_eq_add_neg] using
      (integrableOn_levyJump_step hx₀ hxx (![1, -1] : Fin 2 → ℝ))

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
