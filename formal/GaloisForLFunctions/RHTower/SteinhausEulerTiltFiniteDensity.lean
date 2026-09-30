import GaloisForLFunctions.RHTower.SteinhausEulerTiltBarrier
import GaloisForLFunctions.HTGeometry.GaussianShiftInformation

/-!
# Exact finite Euler tilt and literal barrier mass

The first `N` coordinates of the actual infinite tilted product have the finite
product of the coordinate Poisson laws. Their density against the original
Steinhaus phase law is the product of the exact normalized Euler weights.
This proves change of measure for every nonnegative measurable head observable.

The literal finite-horizon barrier is such an observable whenever the density
cutoff contains all cutoffs tested by that barrier. Its weighted original mass
equals its tilted survival probability. Taking the maximum tested cutoff and
using the proved survival limit makes this restricted density mass tend to zero.
No global density of the infinite product, spatial estimate, or recurrence
hypothesis is used.
-/

open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
namespace RHTower
open SteinhausModel

/-- The actual normalized Euler density through the first `N` coordinates. -/
def steinhausEulerTiltFiniteDensity (N : ℕ) (ω : Omega) : ℝ≥0∞ :=
  ∏ i : Fin N, ENNReal.ofReal (steinhausEulerTiltWeight (steinhausCriticalPrimeRadius i) (ω i))

private theorem measurable_prime_weight (n : ℕ) :
    Measurable (fun x => ENNReal.ofReal (steinhausEulerTiltWeight (steinhausCriticalPrimeRadius n) x)) :=
  (continuous_steinhausEulerTiltWeight (steinhausCriticalPrimeRadius_nonneg n)
    (lt_of_le_of_lt (steinhausCriticalPrimeRadius_le n) (by norm_num))).measurable.ennreal_ofReal

theorem measurable_steinhausEulerTiltFiniteDensity (N : ℕ) :
    Measurable (steinhausEulerTiltFiniteDensity N) :=
  Finset.measurable_prod _ fun i _ => (measurable_prime_weight i).comp (measurable_pi_apply (i : ℕ))

/-- Exact distribution of the head under the actual tilted infinite product law. -/
theorem map_steinhausEulerTiltProductMeasure_head (N : ℕ) :
    steinhausEulerTiltProductMeasure.map (fun (ω : Omega) (i : Fin N) => ω i) =
      Measure.pi (fun i : Fin N => steinhausEulerTiltPrimeMeasure i) := by
  unfold steinhausEulerTiltProductMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

private theorem map_steinhausMeasure_head (N : ℕ) :
    steinhausMeasure.map (fun (ω : Omega) (i : Fin N) => ω i) =
      Measure.pi (fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  unfold steinhausMeasure
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- Change of measure for every nonnegative measurable finite-head observable. -/
theorem lintegral_steinhausEulerTiltFiniteDensity_mul (N : ℕ)
    (f : (Fin N → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, steinhausEulerTiltFiniteDensity N ω * f (fun i => ω i) ∂steinhausMeasure) =
      ∫⁻ ω, f (fun i => ω i) ∂steinhausEulerTiltProductMeasure := by
  let d : (Fin N → ℝ) → ℝ≥0∞ := fun x =>
    ∏ i : Fin N, ENNReal.ofReal (steinhausEulerTiltWeight (steinhausCriticalPrimeRadius i) (x i))
  have hd : Measurable d := Finset.measurable_prod _ fun i _ =>
    (measurable_prime_weight i).comp (measurable_pi_apply i)
  have hh : Measurable (fun ω : Omega => fun i : Fin N => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : ℕ)
  letI (i : Fin N) : IsProbabilityMeasure
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
        (fun x => ENNReal.ofReal (steinhausEulerTiltWeight (steinhausCriticalPrimeRadius i) x))) :=
    inferInstanceAs (IsProbabilityMeasure (steinhausEulerTiltPrimeMeasure i))
  have hwd : (Measure.pi (fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1))).withDensity d =
      Measure.pi (fun i : Fin N => steinhausEulerTiltPrimeMeasure i) := by
    exact GaloisForLFunctions.HTGeometry.pi_withDensity (n := N) (E := fun _ => ℝ)
      (fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1))
      (f := fun (i : Fin N) (x : ℝ) =>
        ENNReal.ofReal (steinhausEulerTiltWeight (steinhausCriticalPrimeRadius i) x))
      (fun i => measurable_prime_weight i)
  calc
    _ = ∫⁻ x, d x * f x ∂(Measure.pi (fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      rw [← map_steinhausMeasure_head N]
      have hm := lintegral_map (μ := steinhausMeasure) (hd.mul hf) hh
      simpa only [Pi.mul_apply, steinhausEulerTiltFiniteDensity, d] using hm.symm
    _ = ∫⁻ x, f x ∂(Measure.pi (fun i : Fin N => steinhausEulerTiltPrimeMeasure i)) := by
      rw [← hwd, lintegral_withDensity_eq_lintegral_mul _ hd hf]
      rfl
    _ = _ := by
      rw [← map_steinhausEulerTiltProductMeasure_head N, lintegral_map hf hh]

/-- The finite density is normalized under the original phase law. -/
theorem lintegral_steinhausEulerTiltFiniteDensity (N : ℕ) :
    ∫⁻ ω, steinhausEulerTiltFiniteDensity N ω ∂steinhausMeasure = 1 := by
  simpa using lintegral_steinhausEulerTiltFiniteDensity_mul N (fun _ => 1) measurable_const

/-- The literal finite barrier is a head event whenever all selected cutoffs lie in the head. -/
private theorem finiteBarrier_head_extension (u : ℕ → ℕ) (A : ℝ) (J N : ℕ)
    (hN : ∀ j < J, u j ≤ N) (ω : Omega) :
    (fun n => if h : n < N then ω (⟨n, h⟩ : Fin N) else 0) ∈
        steinhausEulerTiltFiniteBarrier u A J ↔
      ω ∈ steinhausEulerTiltFiniteBarrier u A J := by
  have hs : ∀ j < J,
      steinhausEulerTiltPrimeSum (Finset.range (u j))
        (fun n => if h : n < N then ω (⟨n, h⟩ : Fin N) else 0) =
      steinhausEulerTiltPrimeSum (Finset.range (u j)) ω := by
    intro j hj
    unfold steinhausEulerTiltPrimeSum
    apply Finset.sum_congr rfl
    intro n hn
    have hnN : n < N := lt_of_lt_of_le (Finset.mem_range.mp hn) (hN j hj)
    simp only [steinhausEulerTiltPrimeVariable, dif_pos hnN]
  constructor
  · intro h j hj
    simpa only [hs j hj] using h j hj
  · intro h j hj
    simpa only [hs j hj] using h j hj

/-- Weighting the original phase law on the actual finite barrier gives exactly its
probability under the tilted product law. -/
theorem setLIntegral_steinhausEulerTiltFiniteBarrier_density (u : ℕ → ℕ) (A : ℝ) (J N : ℕ)
    (hN : ∀ j < J, u j ≤ N) :
    (∫⁻ ω in steinhausEulerTiltFiniteBarrier u A J,
      steinhausEulerTiltFiniteDensity N ω ∂steinhausMeasure) =
      steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J) := by
  let e : (Fin N → ℝ) → Omega := fun x n => if h : n < N then x ⟨n, h⟩ else 0
  have he : Measurable e := by
    apply measurable_pi_iff.mpr
    intro n
    by_cases hn : n < N
    · simpa only [e, dif_pos hn] using (measurable_pi_apply (⟨n, hn⟩ : Fin N))
    · simpa only [e, dif_neg hn] using (measurable_const : Measurable (fun _ : Fin N → ℝ => (0 : ℝ)))
  let B := e ⁻¹' steinhausEulerTiltFiniteBarrier u A J
  have hbar := measurableSet_steinhausEulerTiltFiniteBarrier u A J
  have hB : MeasurableSet B := hbar.preimage he
  let f : (Fin N → ℝ) → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hB
  have hmem (ω : Omega) : (fun i : Fin N => ω i) ∈ B ↔
      ω ∈ steinhausEulerTiltFiniteBarrier u A J :=
    finiteBarrier_head_extension u A J N hN ω
  have hfval (ω : Omega) : f (fun i => ω i) =
      (steinhausEulerTiltFiniteBarrier u A J).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ steinhausEulerTiltFiniteBarrier u A J
    · simp only [f, Set.indicator_of_mem ((hmem ω).mpr hω), Set.indicator_of_mem hω]
    · have hn : (fun i : Fin N => ω i) ∉ B := fun h => hω ((hmem ω).mp h)
      simp only [f, Set.indicator_of_notMem hn, Set.indicator_of_notMem hω]
  calc
    _ = ∫⁻ ω, steinhausEulerTiltFiniteDensity N ω * f (fun i => ω i) ∂steinhausMeasure := by
      rw [← lintegral_indicator hbar]
      apply lintegral_congr
      intro ω
      rw [hfval]
      by_cases hω : ω ∈ steinhausEulerTiltFiniteBarrier u A J <;> simp [hω]
    _ = ∫⁻ ω, f (fun i => ω i) ∂steinhausEulerTiltProductMeasure :=
      lintegral_steinhausEulerTiltFiniteDensity_mul N f hf
    _ = _ := by
      simp_rw [hfval]
      rw [lintegral_indicator hbar]
      simp

/-- The finite density mass restricted to the literal selected-cutoff barrier tends to zero.
The head is the maximum cutoff used so far, so no monotonicity assumption is needed. -/
theorem tendsto_setLIntegral_steinhausEulerTiltFiniteBarrier_density (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (A : ℝ) :
    Tendsto (fun J => ∫⁻ ω in steinhausEulerTiltFiniteBarrier u A J,
      steinhausEulerTiltFiniteDensity ((Finset.range J).sup u) ω ∂steinhausMeasure)
      atTop (𝓝 0) := by
  have heq : (fun J => ∫⁻ ω in steinhausEulerTiltFiniteBarrier u A J,
      steinhausEulerTiltFiniteDensity ((Finset.range J).sup u) ω ∂steinhausMeasure) =
      (fun J => steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J)) := by
    funext J
    exact setLIntegral_steinhausEulerTiltFiniteBarrier_density u A J _
      (fun j hj => Finset.le_sup (Finset.mem_range.mpr hj))
  rw [heq]
  exact tendsto_measure_steinhausEulerTiltFiniteBarrier u hu A

end RHTower
