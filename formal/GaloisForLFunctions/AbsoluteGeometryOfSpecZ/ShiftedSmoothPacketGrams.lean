import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.WeilGroundEnergyBoundsBoundedPackets
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.BoundedPacketIndexCountsNoExtraZeros
import GaloisForLFunctions.RHTower.FiniteSmoothWeilGramsAndRestrictedIndex

/-!
# Mass-shifted smooth packet Grams

Real polarization of packet mass is exactly the physical `L²` pairing.
Together with the full mixed Weil identity, this identifies mass-shifted
real packet matrices with the literal restricted operator Grams.
-/

noncomputable section

open MeasureTheory Matrix Zeta23

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HTGeometry ArithmeticIndexDescent ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis
open _root_.RHTower _root_.RHTower.PaperRestrictedWeil

/-- Polarization of the packet's squared physical mass. -/
def packetMassPair (f g : ℝ → ℝ) : ℝ :=
  (packetAutocorr (f + g) 0 - packetAutocorr (f - g) 0) / 4

theorem packetMassPair_realTests (f g : realTests) :
    packetMassPair f.1 g.1 = ∫ u, f.1 u * g.1 u := by
  have hp : Integrable (fun u => (f.1 u + g.1 u) * (f.1 u + g.1 u)) :=
    ((f + g).2.1.continuous.mul (f + g).2.1.continuous).integrable_of_hasCompactSupport
      (f + g).2.2.mul_right
  have hm : Integrable (fun u => (f.1 u - g.1 u) * (f.1 u - g.1 u)) :=
    ((f - g).2.1.continuous.mul (f - g).2.1.continuous).integrable_of_hasCompactSupport
      (f - g).2.2.mul_right
  have he : (fun u => (f.1 u + g.1 u) * (f.1 u + g.1 u) -
      (f.1 u - g.1 u) * (f.1 u - g.1 u)) = fun u => 4 * (f.1 u * g.1 u) := by
    funext u
    ring
  unfold packetMassPair packetAutocorr
  simp only [add_zero, Pi.add_apply, Pi.sub_apply]
  rw [← integral_sub hp hm, he, integral_const_mul]
  ring

/-- The real Weil bilinear form is the full zeta pairing, not merely its
real part. The imaginary part vanishes by the real explicit formula. -/
theorem realWeilForm_eq_zetaW (f g : realTests) :
    (realWeilForm f g : ℂ) = zetaZeroConfig.W (cx f.1) (cx g.1) := by
  rw [zeta_W_eq_weilFullFunctional_mixed (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)
    (cx_contDiff g.2.1) (cx_hasCompactSupport g.2.2)]
  apply Complex.ext
  · rfl
  · have hcorr : EF.weilTest (cx f.1) (cx g.1) =
        fun y => ((∫ t : ℝ, f.1 t * g.1 (t - y) : ℝ) : ℂ) := by
      funext y
      rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
      simp only [cx, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [hcorr]
    exact (WeilWorkPBAP.weilFullFunctional_ofReal_im _ _).symm

private theorem physical_inner_realSource {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (f g : realTests)
    (hu : ∀ x, u x = (f.1 x : ℂ)) (hv : ∀ x, v x = (g.1 x : ℂ)) :
    inner ℂ (ccmArchimedeanFormToAperture a u.toCCMFormVector)
      (ccmArchimedeanFormToAperture a v.toCCMFormVector) = (packetMassPair f.1 g.1 : ℂ) := by
  rw [packetMassPair_realTests]
  change inner ℂ (ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2)
    (ccmArchimedeanFormToAperture a v.toCCMFormVector : SoninL2) = _
  rw [L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn, v.toCCMFormVector_physical_coeFn]
    with x hx hy
  rw [hx, hy, hu, hv]
  simp only [RCLike.inner_apply, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

/-- A smooth real test supported strictly inside an aperture is a native
complex source in its closed form domain. -/
def smoothRealSource {a : SuzukiPositiveAperture} (f : realTests)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f.1) (hs : tsupport f.1 ⊆ Set.Ioo (-a.1) a.1) :
    CCMComplexSmoothInteriorSource a where
  toFun := cx f.1
  smooth := Complex.ofRealCLM.contDiff.comp hf
  hasCompactSupport := cx_hasCompactSupport f.2.2
  tsupport_subset := by
    have he : Function.support (cx f.1) = Function.support f.1 := by
      ext x
      change ((f.1 x : ℂ) ≠ 0) ↔ f.1 x ≠ 0
      exact not_congr Complex.ofReal_eq_zero
    change closure (Function.support (cx f.1)) ⊆ _
    rw [he]
    exact hs

/-- Real smooth Weil matrix with its physical mass shifted by `E`. -/
def shiftedRealTestGram {ι : Type*} (E : ℝ) (f : ι → realTests) : Matrix ι ι ℂ :=
  fun i j => ((realWeilForm (f i) (f j) - E * packetMassPair (f i).1 (f j).1 : ℝ) : ℂ)

theorem shiftedRealTestGram_zero {n : ℕ} (f : Fin n → realTests) :
    shiftedRealTestGram 0 f = complexWeilMixed f f := by
  ext i j
  change ((realWeilForm (f i) (f j) - 0 * packetMassPair (f i).1 (f j).1 : ℝ) : ℂ) =
    (realWeilForm (f i) (f j) : ℂ)
  rw [zero_mul, sub_zero]

theorem realWeilForm_eq_zeroSum_polarization (f g : realTests) :
    realWeilForm f g = (zeroSum (f + g).1 - zeroSum (f - g).1) / 4 := by
  have h := completeCell_limit_pair f g
  change (weilQuad (f + g).1 - weilQuad (f - g).1) / 4 = _ at h
  rw [LogCells.weilQuad_eq_zetaW (f + g).2.1 (f + g).2.2,
    LogCells.weilQuad_eq_zetaW (f - g).2.1 (f - g).2.2] at h
  exact h.symm

/-- Translation of a bundled compact real packet. -/
def translatedPacketTest (s : ℝ) (f : realTests) : realTests :=
  ⟨fun u => f.1 (u - s), f.2.1.comp (contDiff_id.sub contDiff_const),
    f.2.2.comp_homeomorph (Homeomorph.subRight s)⟩

/-- A common translation preserves both the Weil and mass Grams. -/
theorem shiftedRealTestGram_translate {ι : Type*} (E s : ℝ) (f : ι → realTests) :
    shiftedRealTestGram E (fun i => translatedPacketTest s (f i)) = shiftedRealTestGram E f := by
  ext i j
  have hw : realWeilForm (translatedPacketTest s (f i)) (translatedPacketTest s (f j)) =
      realWeilForm (f i) (f j) := by
    rw [realWeilForm_eq_zeroSum_polarization, realWeilForm_eq_zeroSum_polarization]
    change (zeroSum (fun u => (f i + f j).1 (u - s)) -
      zeroSum (fun u => (f i - f j).1 (u - s))) / 4 = _
    rw [zeroSum_translate (f i + f j).2.1 (f i + f j).2.2,
      zeroSum_translate (f i - f j).2.1 (f i - f j).2.2]
  have hm : packetMassPair (translatedPacketTest s (f i)).1 (translatedPacketTest s (f j)).1 =
      packetMassPair (f i).1 (f j).1 := by
    unfold packetMassPair
    change (packetAutocorr (fun u => (f i + f j).1 (u - s)) 0 -
      packetAutocorr (fun u => (f i - f j).1 (u - s)) 0) / 4 = _
    rw [packetAutocorr_translate, packetAutocorr_translate]
    rfl
  change ((realWeilForm _ _ - E * packetMassPair _ _ : ℝ) : ℂ) = _
  rw [hw, hm]
  rfl

theorem shiftedRealTestGram_eq_native {n : ℕ} {a : SuzukiPositiveAperture}
    (E : ℝ) (f : Fin n → realTests) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i).1)
    (hs : ∀ i, tsupport (f i).1 ⊆ Set.Ioo (-a.1) a.1) :
    shiftedRealTestGram E f = smoothShiftedWeilGram E
      (fun i => smoothRealSource (f i) (hf i) (hs i)) := by
  ext i j
  change ((realWeilForm (f i) (f j) - E * packetMassPair (f i).1 (f j).1 : ℝ) : ℂ) = _
  rw [Complex.ofReal_sub, Complex.ofReal_mul, realWeilForm_symm (f i) (f j),
    realWeilForm_eq_zetaW]
  unfold smoothShiftedWeilGram
  rw [physical_inner_realSource _ _ (f i) (f j) (fun _ => rfl) (fun _ => rfl)]
  rfl

/-- Strict-interior real packet Grams obey the literal shifted aperture index. -/
theorem hermNegIndex_shiftedRealTestGram_le {n : ℕ} {a : SuzukiPositiveAperture}
    (E : ℝ) (f : Fin n → realTests) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i).1)
    (hs : ∀ i, tsupport (f i).1 ⊆ Set.Ioo (-a.1) a.1) :
    hermNegIndex (shiftedRealTestGram E f) ≤ negativeRank a E := by
  rw [shiftedRealTestGram_eq_native E f hf hs]
  exact hermNegIndex_smoothShiftedWeilGram_le E _

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
