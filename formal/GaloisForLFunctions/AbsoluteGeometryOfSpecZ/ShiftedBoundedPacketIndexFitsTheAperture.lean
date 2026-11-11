import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ShiftedSmoothPacketGrams

/-!
# Bounded packet index fits every strictly wider aperture

Simultaneous smoothing preserves the complete Weil form and physical mass.
A common translation centers the support without changing either Gram.
Thus a bounded finite-energy family cannot exceed the restricted index
at any strictly wider aperture, even after an arbitrary real mass shift.
-/

noncomputable section

open MeasureTheory Filter Topology Matrix

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry ArithmeticIndexDescent ArithmeticCastelnuovoSeveri
open _root_.RHTower _root_.RHTower.PaperRestrictedWeil

/-- Polar Gram of the bounded packet form minus physical mass. -/
def shiftedPacketGram {ι : Type*} (Q : ℕ) (E : ℝ) (f : ι → ℝ → ℝ) : Matrix ι ι ℂ :=
  fun i j => ((((packetForm Q (f i + f j) - E * packetAutocorr (f i + f j) 0) -
    (packetForm Q (f i - f j) - E * packetAutocorr (f i - f j) 0)) / 4 : ℝ) : ℂ)

/-- The full shifted bounded-packet index is controlled by the native
aperture operator; no sign assumption is imposed on that operator. -/
theorem hermNegIndex_shiftedPacketGram_le {n Q : ℕ} (E : ℝ) (f : Fin n → ℝ → ℝ)
    (hfm : ∀ i, Measurable (f i)) {M : Fin n → ℝ} (hfb : ∀ i u, |f i u| ≤ M i)
    {l r : ℝ} (hs : ∀ i u, f i u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJadd : ∀ i j, IntegrableOn (levyJump (f i + f j)) (Set.Ioi 0))
    (hJsub : ∀ i j, IntegrableOn (levyJump (f i - f j)) (Set.Ioi 0))
    {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1) :
    hermNegIndex (shiftedPacketGram Q E f) ≤ negativeRank A E := by
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
    constructor <;> dsimp only [Pi.add_apply] <;> linarith only [hi.1, hi.2, hj.1, hj.2]
  have hminus : ∀ i j u, |(f i - f j) u| ≤ M i + M j := by
    intro i j u
    have hi := abs_le.mp (hfb i u)
    have hj := abs_le.mp (hfb j u)
    apply abs_le.mpr
    constructor <;> dsimp only [Pi.sub_apply] <;> linarith only [hi.1, hi.2, hj.1, hj.2]
  have hsplus : ∀ i j u, (f i + f j) u ≠ 0 → l ≤ u ∧ u ≤ r := by
    intro i j u hne
    by_contra hu
    exact hne (by simp only [Pi.add_apply, hvanish i u hu, hvanish j u hu, add_zero])
  have hsminus : ∀ i j u, (f i - f j) u ≠ 0 → l ≤ u ∧ u ≤ r := by
    intro i j u hne
    by_contra hu
    exact hne (by simp only [Pi.sub_apply, hvanish i u hu, hvanish j u hu, sub_self])
  have hconv : ∀ i j, Tendsto (fun k => shiftedRealTestGram E (F k) i j) atTop
      (𝓝 (shiftedPacketGram Q E f i j)) := by
    intro i j
    have hp := (tendsto_zeroSum_mollify ((hfm i).add (hfm j)) (hplus i j)
      (hsplus i j) hQ (hJadd i j)).sub
      ((tendsto_packetAutocorr_mollify ((hfm i).add (hfm j)) (hplus i j)
        (hsplus i j) 0).const_mul E)
    have hm := (tendsto_zeroSum_mollify ((hfm i).sub (hfm j)) (hminus i j)
      (hsminus i j) hQ (hJsub i j)).sub
      ((tendsto_packetAutocorr_mollify ((hfm i).sub (hfm j)) (hminus i j)
        (hsminus i j) 0).const_mul E)
    have ht := (Complex.continuous_ofReal.tendsto _).comp ((hp.sub hm).div_const 4)
    refine ht.congr' (Eventually.of_forall fun k => ?_)
    change ((((zeroSum (mollify (shrinkingBump k) (f i + f j)) -
        E * packetAutocorr (mollify (shrinkingBump k) (f i + f j)) 0) -
      (zeroSum (mollify (shrinkingBump k) (f i - f j)) -
        E * packetAutocorr (mollify (shrinkingBump k) (f i - f j)) 0)) / 4 : ℝ) : ℂ) = _
    rw [mollify_add_bounded _ (hfm i) (hfm j) (hfb i) (hfb j),
      mollify_sub_bounded _ (hfm i) (hfm j) (hfb i) (hfb j)]
    change ((((zeroSum (F k i + F k j).1 - E * packetAutocorr (F k i + F k j).1 0) -
      (zeroSum (F k i - F k j).1 - E * packetAutocorr (F k i - F k j).1 0)) / 4 : ℝ) : ℂ) =
      ((realWeilForm (F k i) (F k j) - E * packetMassPair (F k i).1 (F k j).1 : ℝ) : ℂ)
    rw [realWeilForm_eq_zeroSum_polarization]
    unfold packetMassPair
    congr 1
    ring
  let c := (l + r) / 2
  let G : ℕ → Fin n → realTests := fun k i => translatedPacketTest (-c) (F k i)
  have hconvG : ∀ i j, Tendsto (fun k => shiftedRealTestGram E (G k) i j) atTop
      (𝓝 (shiftedPacketGram Q E f i j)) := by
    intro i j
    simpa only [G, shiftedRealTestGram_translate] using hconv i j
  have hsmall : ∀ᶠ k : ℕ in atTop, (shrinkingBump k).rOut < A.1 - (r - l) / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds (by linarith only [hA]))
  obtain ⟨k, hk, hrad⟩ :=
    ((eventually_negIndex_limit_le (fun k => shiftedRealTestGram E (G k))
      (shiftedPacketGram Q E f) hconvG).and hsmall).exists
  apply hk.trans
  apply hermNegIndex_shiftedRealTestGram_le E (G k)
  · intro i
    exact (contDiff_top_mollify (shrinkingBump k) (hfm i) (hfb i) (hs i)).comp
      (contDiff_id.sub contDiff_const)
  · intro i
    have hclosed : tsupport (G k i).1 ⊆
        Set.Icc (l - (shrinkingBump k).rOut - c) (r + (shrinkingBump k).rOut - c) := by
      apply closure_minimal _ isClosed_Icc
      intro u hu
      have hb := mollify_ne_zero (shrinkingBump k) (hs i) (u - -c) hu
      constructor <;> linarith only [hb.1, hb.2]
    apply hclosed.trans
    intro u hu
    constructor <;> dsimp only [c] at * <;> linarith only [hu.1, hu.2, hrad]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
