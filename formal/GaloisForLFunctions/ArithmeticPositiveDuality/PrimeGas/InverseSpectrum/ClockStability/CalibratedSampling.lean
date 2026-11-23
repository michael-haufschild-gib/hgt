import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.OrderedClocks
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.FiniteSeparation

/-! # Finite critical-line sampling with clock and amplitude uncertainty

Clock height can vary throughout a closed bounded interval. Uniform
separation holds simultaneously for any two admissible spectra.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private def clockDiscrepancy {l u : ℝ} {r : ℕ} (n : ℕ)
    (p : ClockState l u r × ClockState l u r) : ℝ :=
  max |p.1.1.val - p.2.1.val| ‖clockReading p.1.1.val p.1.2 n - clockReading p.2.1.val p.2.2 n‖

private theorem continuous_clockDiscrepancy (l u : ℝ) (r n : ℕ) :
    Continuous (clockDiscrepancy (l := l) (u := u) (r := r) n) := by
  have ht : Continuous (fun p : ClockState l u r => p.1.val) := continuous_subtype_val.comp continuous_fst
  have hc := continuous_clockReading l u r n
  exact ((ht.comp continuous_fst).sub (ht.comp continuous_snd)).abs.max
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm

private theorem eventually_discrepancy_pos {l u : ℝ} {r : ℕ} (f : SpectralResponse)
    (p : ClockState l u r × ClockState l u r) (h : 0 < detectorError f p.1.2.val p.2.2.val) :
    ∀ᶠ n in atTop, 0 < clockDiscrepancy n p := by
  by_cases ht : p.1.1.val = p.2.1.val
  · have hne : p.1.2 ≠ p.2.2 := by
      intro he
      rw [he,detectorError_self] at h
      exact h.false
    filter_upwards [eventually_clockReading_ne p.1.1.val hne] with n hn
    have hn' : clockReading p.1.1.val p.1.2 n ≠ clockReading p.2.1.val p.2.2 n := by rw [← ht]; exact hn
    exact (norm_pos_iff.mpr (sub_ne_zero.mpr hn')).trans_le (le_max_right _ _)
  · exact Eventually.of_forall (fun _ => (abs_pos.mpr (sub_ne_zero.mpr ht)).trans_le (le_max_left _ _))

/-- After any starting index, agreement somewhere in each tested block forces small total spectral error. -/
theorem finite_clock_stability (r : ℕ) (l u : ℝ) (f : SpectralResponse) {ε : ℝ} (hε : 0 < ε)
    (start k : ℕ) :
    ∃ N : ℕ, ∀ p q : ClockState l u r, |p.1.val - q.1.val| ≤ occupationWeight N →
      (∀ m ≤ N, ∃ j ≤ k, ‖clockReading p.1.val p.2 (start+m+j) -
        clockReading q.1.val q.2 (start+m+j)‖ ≤ occupationWeight N) →
      detectorError f p.2.val q.2.val < ε := by
  let E (p : ClockState l u r × ClockState l u r) := detectorError f p.1.2.val p.2.2.val
  have hv : Continuous (fun p : ClockState l u r => p.2.val) := continuous_subtype_val.comp continuous_snd
  have he : Continuous E := (continuous_detectorError f r).comp
    ((hv.comp continuous_fst).prodMk (hv.comp continuous_snd))
  obtain ⟨N,hN⟩ := compact_block_separation E he clockDiscrepancy (continuous_clockDiscrepancy l u r)
    (eventually_discrepancy_pos f) hε start k
  refine ⟨N,fun p q ht hs => ?_⟩
  by_contra! h
  obtain ⟨m,hm,hblock⟩ := hN (p,q) h
  obtain ⟨j,hj,hclose⟩ := hs m hm
  exact (hblock j hj).not_ge (max_le ht hclose)

/-- The same finite precision works over all physical missing dimensions bounded by r. -/
theorem finite_physical_clock_stability (r : ℕ) (l u : ℝ) (f : SpectralResponse) {ε : ℝ} (hε : 0 < ε)
    (start k : ℕ) :
    ∃ N : ℕ, ∀ {i j : ℕ} (_ : i ≤ r) (_ : j ≤ r) (P Q : Projection)
      (hP : MissingDimension P i) (cP : Conserving (projected P))
      (hQ : MissingDimension Q j) (cQ : Conserving (projected Q)) (t w : Icc l u),
      |t.val-w.val| ≤ occupationWeight N →
      (∀ m ≤ N, ∃ a ≤ k, ‖relativePartition (physicalSpectrum P hP cP) (compositionSample t.val (start+m+a)) -
        relativePartition (physicalSpectrum Q hQ cQ) (compositionSample w.val (start+m+a))‖ ≤ occupationWeight N) →
      (∑' n, |f.value (_root_.RHTower.approxNumber ((projected P)^2) n) -
        f.value (_root_.RHTower.approxNumber ((projected Q)^2) n)|) < ε := by
  obtain ⟨N,hN⟩ := finite_clock_stability r l u f hε start k
  refine ⟨N,fun hi hj P Q hP cP hQ cQ t w ht hs => ?_⟩
  exact hN (t,orderedPhysical hi P hP cP) (w,orderedPhysical hj Q hQ cQ) ht hs

#print axioms finite_clock_stability
#print axioms finite_physical_clock_stability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
