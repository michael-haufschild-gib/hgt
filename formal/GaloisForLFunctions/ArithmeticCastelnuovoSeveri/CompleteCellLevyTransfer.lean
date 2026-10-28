import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicStepProfiles
import GaloisForLFunctions.RHTower.CHMDBVUniformGraph
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The Gamma jump energy of complete logarithmic cells

The cell error has size `O(1/N)` and uniformly bounded variation. The finite first
moment of the Gamma Lévy measure therefore pays all its jumps, including the
arbitrarily small translations across cell boundaries.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.CHMDDoobGraph

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry

private theorem integrable_stationaryJump_bv {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Integrable (stationaryJump f) archBase := by
  have hm := measurable_of_boundedVariation_univ hf
  have hM : 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal := by positivity
  have hb : ∀ u, |f u| ≤ ‖f 0‖ + (eVariationOn f univ).toReal := fun u => by
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hf u
  exact integrable_stationaryJump hm hc (bounded_compact_memLp_volume hm hc hM hb)
    (bv_memLp_difference hf)

/-- Compact BV sources have the same stationary and iterated Lévy energies. -/
theorem stationaryEnergy_eq_levyEnergy {f : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    stationaryEnergy f = levyEnergy f :=
  stationaryEnergy_eq_iterated (integrable_stationaryJump_bv hf hc)

/-- The square-root density realizes the entire Lévy form in one fixed L² space. -/
def levyRoot (f : ℝ → ℝ) (e : ℝ × ℝ) : ℝ :=
  Real.sqrt (archLevyDensity e.1) * (f e.2 - f (e.2 + e.1))

theorem levyRoot_sq_ae (f : ℝ → ℝ) :
    (fun e => levyRoot f e ^ 2) =ᵐ[archBase] stationaryJump f := by
  have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [ht] with e he
  simp only [levyRoot, mul_pow, Real.sq_sqrt (archLevyDensity_pos he).le,
    stationaryJump, difference, left, right]

theorem memLp_levyRoot {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) : MemLp (levyRoot f) 2 archBase := by
  have hm := measurable_of_boundedVariation_univ hf
  have hj : Measurable (levyRoot f) :=
    (measurable_archLevyDensity.comp measurable_fst).sqrt.mul
      ((hm.comp measurable_snd).sub (hm.comp (measurable_snd.add measurable_fst)))
  exact (memLp_two_iff_integrable_sq hj.aestronglyMeasurable).mpr
    ((integrable_stationaryJump_bv hf hc).congr (levyRoot_sq_ae f).symm)

/-- The full jump vector of a compact BV source. -/
def levyVector (f : ℝ → ℝ) (hf : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    Lp ℝ 2 archBase := (memLp_levyRoot hf hc).toLp (levyRoot f)

theorem norm_levyVector_sq (f : ℝ → ℝ) (hf : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) : ‖levyVector f hf hc‖ ^ 2 = levyEnergy f := by
  rw [levyVector, _root_.RHTower.CHMDClosedJump.norm_toLp_sq,
    integral_congr_ae (levyRoot_sq_ae f)]
  exact stationaryEnergy_eq_levyEnergy hf hc

theorem levyRoot_sub (f g : ℝ → ℝ) :
    levyRoot (fun u => f u - g u) = levyRoot f - levyRoot g := by
  funext e
  simp only [levyRoot, Pi.sub_apply]
  ring

theorem norm_levyVector_sub_sq {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    ‖levyVector f hf hfc - levyVector g hg hgc‖ ^ 2 =
      levyEnergy (fun u => f u - g u) := by
  change ‖(memLp_levyRoot hf hfc).toLp (levyRoot f) -
    (memLp_levyRoot hg hgc).toLp (levyRoot g)‖ ^ 2 = _
  rw [← MemLp.toLp_sub, _root_.RHTower.CHMDClosedJump.norm_toLp_sq, ← levyRoot_sub,
    integral_congr_ae (levyRoot_sq_ae (fun u => f u - g u))]
  exact stationaryEnergy_eq_levyEnergy (boundedVariationOn_sub hf hg) (hfc.sub hgc)

/-- Uniform size and total variation pay the full archimedean jump integral. -/
theorem levyEnergy_bv_le {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ u, |f u| ≤ M) :
    levyEnergy f ≤ 4 * M * (eVariationOn f univ).toReal *
      ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := by
  rw [← stationaryEnergy_eq_levyEnergy hf hc]
  exact stationaryEnergy_bv_le_of_bound hf hc hM hb

/-- The actual discontinuous complete-cell error has vanishing Gamma energy. -/
theorem levyEnergy_logStep_sub_le {f : ℝ → ℝ} (hf : BoundedVariationOn f univ)
    (hc : HasCompactSupport f) {K : NNReal} (hK : LipschitzWith K f)
    (R : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    levyEnergy (fun u => logStep f R N u - f u) ≤
      (8 * (K : ℝ) * (eVariationOn f univ).toReal *
        ∫ t in Ioi (0 : ℝ), t * archLevyDensity t) / N := by
  have he := boundedVariationOn_sub (boundedVariationOn_logStep hf R hN) hf
  have hec : HasCompactSupport (fun u => logStep f R N u - f u) :=
    (hasCompactSupport_logStep R hN hB hs).sub hc
  have h := levyEnergy_bv_le he hec (by positivity : 0 ≤ (K : ℝ) / N)
    (abs_logStep_sub_le hK R hN (fun u hu => hs u (Or.inl hu)))
  have hJ : 0 ≤ ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (archLevyDensity_pos ht).le
  calc
    _ ≤ 4 * ((K : ℝ) / N) *
        (eVariationOn (fun u => logStep f R N u - f u) univ).toReal *
          ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := h
    _ ≤ 4 * ((K : ℝ) / N) * (2 * (eVariationOn f univ).toReal) *
          ∫ t in Ioi (0 : ℝ), t * archLevyDensity t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (variation_logStep_sub_le hf R hN) (by positivity)) hJ
    _ = _ := by ring

/-- Compact C² regularity supplies every bound needed for jump-energy convergence. -/
theorem exists_complete_cell_levy_rate {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ, 1 ≤ B ∧ ∃ D : ℝ, 0 ≤ D ∧
      (∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) ∧
      ∀ N : ℕ, 1 ≤ N → levyEnergy (fun u => logStep f R N u - f u) ≤ D / N := by
  obtain ⟨R, hR, B, hB, _, _, hs, _⟩ := exists_compact_logSamples_rate hf hf hc hc
  obtain ⟨K, hK⟩ := compact_source_lipschitz hf hc
  have hv := boundedVariationOn_of_contDiff_compact (hf.of_le (by norm_num)) hc
  have hJ : 0 ≤ ∫ t in Ioi (0 : ℝ), t * archLevyDensity t := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg ht.le (archLevyDensity_pos ht).le
  refine ⟨R, hR, B, hB,
    8 * (K : ℝ) * (eVariationOn f univ).toReal *
      ∫ t in Ioi (0 : ℝ), t * archLevyDensity t, by positivity,
    fun u hu => (hs u hu).1, fun N hN => ?_⟩
  exact levyEnergy_logStep_sub_le hv hc hK R hN hB (fun u hu => (hs u hu).1)

/-- Complete cells recover the full Gamma energy of every compact C² source. -/
theorem tendsto_logStep_levyEnergy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => levyEnergy (logStep f R (N + 1))) atTop
      (𝓝 (levyEnergy f)) := by
  have hv := boundedVariationOn_of_contDiff_compact (hf.of_le (by norm_num)) hc
  obtain ⟨K, hK⟩ := compact_source_lipschitz hf hc
  let v := levyVector f hv hc
  let vN := fun N : ℕ => levyVector (logStep f R (N + 1))
    (boundedVariationOn_logStep hv R (by omega))
    (hasCompactSupport_logStep R (by omega) hB hs)
  have hsq : Tendsto (fun N : ℕ => ‖vN N - v‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun N => ?_)
      ((tendsto_const_div_atTop_nhds_zero_nat
        (8 * (K : ℝ) * (eVariationOn f univ).toReal *
          ∫ t in Ioi (0 : ℝ), t * archLevyDensity t)).comp (tendsto_add_atTop_nat 1))
    dsimp only [vN, v]
    rw [norm_levyVector_sub_sq]
    exact levyEnergy_logStep_sub_le hv hc hK R (by omega) hB hs
  have hnorm : Tendsto (fun N : ℕ => ‖vN N - v‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt
  have hvec : Tendsto vN atTop (𝓝 v) := tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have henergy := hvec.norm.pow 2
  dsimp only [vN, v] at henergy
  simpa only [norm_levyVector_sq] using henergy

#print axioms levyEnergy_logStep_sub_le
#print axioms exists_complete_cell_levy_rate
#print axioms tendsto_logStep_levyEnergy

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
