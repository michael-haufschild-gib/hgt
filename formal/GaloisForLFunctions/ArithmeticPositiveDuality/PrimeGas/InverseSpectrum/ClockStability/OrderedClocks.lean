import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DetectorError
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.CompositionSamples

/-! # The compact family of ordered spectra observed by a composition clock -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

abbrev OrderedSpectrum (r : ℕ) := {b : SpectralBand r // Antitone (fun n => (b n).val)}

instance (r : ℕ) : CompactSpace (OrderedSpectrum r) := by
  apply (isCompact_iff_compactSpace (s := {b : SpectralBand r | Antitone (fun n => (b n).val)})).mp
  have he : {b : SpectralBand r | Antitone (fun n => (b n).val)} =
      ⋂ (i : ℕ) (j : ℕ) (_ : i ≤ j), {b : SpectralBand r | (b j).val ≤ (b i).val} := by
    ext b
    simp only [mem_setOf_eq,mem_iInter]
    exact ⟨fun h i j hij => h hij,fun h i j hij => h i j hij⟩
  have hv (n : ℕ) : Continuous (fun b : SpectralBand r => (b n).val) :=
    continuous_subtype_val.comp (continuous_apply n)
  rw [he]
  exact (isClosed_iInter fun (i : ℕ) => isClosed_iInter fun (j : ℕ) => isClosed_iInter fun (_ : i ≤ j) =>
    isClosed_le (hv j) (hv i)).isCompact

/-- Rank-bounded physical squares supply ordered spectra without any spectral-order assumption. -/
def orderedPhysical {q r : ℕ} (h : q ≤ r) (P : Projection) (hd : MissingDimension P q)
    (hc : Conserving (projected P)) : OrderedSpectrum r :=
  ⟨widenSpectrum h (physicalSpectrum P hd hc),_root_.RHTower.approxNumber_antitone _⟩

def clockReading {r : ℕ} (t : ℝ) (b : OrderedSpectrum r) (n : ℕ) : ℂ :=
  relativePartition b.val (compositionSample t n)

private theorem continuous_positive_cpow {X : Type*} [TopologicalSpace X] {x : X → ℝ} {z : X → ℂ}
    (hx : Continuous x) (hp : ∀ u, 0 < x u) (hz : Continuous z) : Continuous (fun u => (x u : ℂ)^(z u)) := by
  have he (u : X) : (x u : ℂ)^(z u) = Complex.exp ((Real.log (x u) : ℂ)*z u) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (hp u).ne'),Complex.ofReal_log (hp u).le]
  simp only [funext he]
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (hx.log (fun u => (hp u).ne'))).mul hz)

private theorem continuous_sample_height (n : ℕ) : Continuous (fun t => compositionSample t n) := by
  have he (t : ℝ) : compositionSample t n = (1/2 : ℂ) + ((t + occupationWeight n : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [compositionSample]
  rw [funext he]
  exact continuous_const.add ((Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).mul continuous_const)

abbrev ClockState (l u : ℝ) (r : ℕ) := Icc l u × OrderedSpectrum r

/-- The clock phase and the occupation sequence can both vary in the compact family. -/
theorem continuous_clockReading (l u : ℝ) (r n : ℕ) :
    Continuous (fun p : ClockState l u r => clockReading p.1.val p.2 n) := by
  let δ : GibbsExponent := ⟨1/2,show (0:ℝ) < 1/2 by norm_num⟩
  have hz : Continuous (fun p : ClockState l u r => compositionSample p.1.val n) :=
    (continuous_sample_height n).comp (continuous_subtype_val.comp continuous_fst)
  obtain ⟨M,hM⟩ := (isCompact_range hz.norm).bddAbove
  apply continuous_tsum (u := fun j => (M/δ.val) * spectralDrop (powerResponse δ) (coldEdge r) j)
  · intro j
    have hb : Continuous (fun p : ClockState l u r => (p.2.val j).val) :=
      continuous_subtype_val.comp ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
    exact (continuous_positive_cpow continuous_const (fun _ => occupationWeight_pos j) hz).sub
      (continuous_positive_cpow hb (fun p => band_pos p.2.val j) hz)
  · exact (hasSum_edge_drop (powerResponse δ) r).summable.mul_left _
  · intro j p
    have h := complexDrop_bound p.2.val j δ (z := compositionSample p.1.val n) le_rfl
    have hnorm := hM (mem_range_self p)
    exact h.trans (mul_le_mul (div_le_div_of_nonneg_right hnorm δ.property.le)
      (drop_le_edge _ _ _) (drop_nonneg _ _ _) (div_nonneg ((norm_nonneg _).trans hnorm) δ.property.le))

/-- Two distinct ordered spectra disagree at all sufficiently late clock samples. -/
theorem eventually_clockReading_ne {r : ℕ} (t : ℝ) {b c : OrderedSpectrum r} (hne : b ≠ c) :
    ∀ᶠ n in atTop, clockReading t b n ≠ clockReading t c n := by
  apply not_frequently.mp
  intro h
  have hval := levels_of_accumulating_agreement b.val c.val b.property c.property
    (z := (⟨1/2,t⟩ : ℂ)) (by change (0:ℝ) < 1/2; norm_num)
    (fun he => h ((tendsto_samples t).eventually he))
  exact hne (Subtype.ext (funext fun n => Subtype.ext (hval n)))

#print axioms orderedPhysical
#print axioms continuous_clockReading
#print axioms eventually_clockReading_ne

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
