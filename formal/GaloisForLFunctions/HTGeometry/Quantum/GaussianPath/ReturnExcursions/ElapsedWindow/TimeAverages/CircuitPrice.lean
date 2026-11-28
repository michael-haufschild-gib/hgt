import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.TimeAverages.ReplicaMoment
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.LocalReadings

/-! # Averaged circuit tests at the original first return -/

open Finset MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool

/-- The contribution of a particular circuit after integrating the date
and the local Gaussian fields. Cancellation occurs before taking the norm. -/
def windowTwistSum {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ) (q : ℕ) (b m : ℝ) (V : ℝ≥0) : ℂ :=
  ∑ p ∈ Finset.univ.piAntidiag q, ∑ k ∈ Finset.univ.piAntidiag q,
      (fidelityReplicaMultiplicityWeight w p k:ℂ)*replicaMultiplicityTwist z p k *
        timeActionKernel m (replicaMultiplicityEnergy E p-replicaMultiplicityEnergy E k)
          (pairVariance v b p k) V

/-- Nonnegative moment price of one circuit. -/
def windowTwistPrice {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ) (q : ℕ) (b m : ℝ) (V : ℝ≥0) : ℝ :=
  ‖windowTwistSum E w v z q b m V‖

/-- Each signed sum is real and nonnegative because it averages a fidelity power. -/
theorem averaged_twist {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E w : I → ℝ) (v : J → I → ℝ) (z : I → ℂ) (q : ℕ) (b m : ℝ) (V : ℝ≥0) :
    (∫ t, ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g)
      (fun i => z i*Complex.exp (((E i*t:ℝ):ℂ)*Complex.I)) (t*b)^q
        ∂(Measure.pi fun _ : J => gaussianReal 0 1)‖ ∂gaussianReal m V) =
      windowTwistPrice E w v z q b m V ∧
      windowTwistSum E w v z q b m V = (windowTwistPrice E w v z q b m V : ℂ) := by
  let μ := Measure.pi fun _ : J => gaussianReal 0 1
  let Z (t : ℝ) (i : I) := z i*Complex.exp (((E i*t:ℝ):ℂ)*Complex.I)
  let f (t : ℝ) (g : J → ℝ) := ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (Z t) (t*b)‖^(2*q)
  have hf (t : ℝ) : 0 ≤ ∫ g, f t g ∂μ := integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)
  have hc (t : ℝ) :
      (∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (Z t) (t*b)^q ∂μ) =
        ((∫ g, f t g ∂μ : ℝ):ℂ) := by
    rw [←integral_complex_ofReal]
    apply integral_congr_ae
    exact ae_of_all _ fun g => by
      simp only [twistedFiniteSpectralFidelity,Complex.normSq_eq_norm_sq,f,pow_mul,Complex.ofReal_pow]
  let F (t : ℝ) := ∫ g, f t g ∂μ
  let ν := gaussianReal m V
  have hM : windowTwistSum E w v z q b m V = ((∫ t, F t ∂ν : ℝ):ℂ) := by
    unfold windowTwistSum
    rw [←time_field_replica_moment]
    change (∫ t, ∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (Z t) (t*b)^q ∂μ ∂ν) = _
    simp_rw [hc]
    exact integral_complex_ofReal
  have hreal : windowTwistPrice E w v z q b m V = ∫ t, F t ∂ν := by
    rw [windowTwistPrice,hM,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg hf)]
  refine ⟨?_,hM.trans (congrArg (fun x : ℝ => (x:ℂ)) hreal.symm)⟩
  rw [hreal]
  apply integral_congr_ae
  filter_upwards with t
  change ‖∫ g, twistedFiniteSpectralFidelity w (fieldEnergy v g) (Z t) (t*b)^q ∂μ‖ = F t
  rw [hc,Complex.norm_real,Real.norm_of_nonneg (hf t)]

/-- A finite sum of signed replica terms for the full circuit net on the
chosen energy ranks. It contains no integration over times or fields. -/
def averagedAffinePrice (n s : ℕ) (g : Coeff n) (R : Finset (Config (n+2))) (w : R → ℝ)
    (q : ℕ) (a b m : ℝ) (V : ℝ≥0) : ℝ :=
  let U := (generator g).2.isHermitian.eigenvectorUnitary
  let E (j : R) := a*(generator g).2.isHermitian.eigenvalues j.val
  let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 g) l j.val
  ∑ C : atMostQuarterCircuitNet (n+2) s, windowTwistPrice E w v
    (fun j => (U⁻¹*C.val*U).val j.val j.val) q b m V

/-- The integrated physical circuit test equals its explicit finite sum
for every choice of spectral weights and replica order. -/
theorem gaussian_average_affine_price (n s : ℕ) (g : Coeff n) (R : Finset (Config (n+2)))
    (w : R → ℝ) (q : ℕ) (a b m : ℝ) (V : ℝ≥0) :
    (∫ t, affineTracePrice n s g R w q a b t ∂gaussianReal m V) =
      averagedAffinePrice n s g R w q a b m V := by
  let U := (generator g).2.isHermitian.eigenvectorUnitary
  let E (j : R) := a*(generator g).2.isHermitian.eigenvalues j.val
  let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 g) l j.val
  let N := atMostQuarterCircuitNet (n+2) s
  let z (C : N) (j : R) := (U⁻¹*C.val*U).val j.val j.val
  unfold affineTracePrice averagedAffinePrice
  rw [integral_finsetSum _ (fun C _ => (integrable_time_field_moment E w v (z C) q b (gaussianReal m V)).norm)]
  exact sum_congr rfl fun C _ => (averaged_twist E w v (z C) q b m V).1

/-- If the finite sum lies below the threshold times the Gaussian mass of
a date window, at least one date in the window passes the circuit test. -/
theorem date_of_averaged_price (n s : ℕ) (g : Coeff n) (R : Finset (Config (n+2)))
    (w : R → ℝ) (q : ℕ) (a b m : ℝ) (V : ℝ≥0) {J : Set ℝ} (hJ : MeasurableSet J)
    {p : ℝ} (hprice : averagedAffinePrice n s g R w q a b m V < (gaussianReal m V).real J*p) :
    ∃ t ∈ J, affineTracePrice n s g R w q a b t ≤ p := by
  classical
  let μ := gaussianReal m V
  let S (t : ℝ) := affineTracePrice n s g R w q a b t
  have hS : Integrable S μ := by
    unfold S affineTracePrice
    apply integrable_finsetSum
    intro C _
    exact (integrable_time_field_moment _ _ _ _ _ _ μ).norm
  have hn (t : ℝ) : 0 ≤ S t := sum_nonneg fun _ _ => norm_nonneg _
  by_contra! h
  have hle (t : ℝ) : J.indicator (fun _ => p) t ≤ S t := by
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]; exact (h t ht).le
    · rw [indicator_of_notMem ht]; exact hn t
  have hi := integral_mono ((integrable_const p).indicator hJ) hS hle
  rw [integral_indicator hJ,setIntegral_const,smul_eq_mul] at hi
  exact hprice.not_ge (hi.trans_eq (gaussian_average_affine_price n s g R w q a b m V))

#print axioms gaussian_average_affine_price
#print axioms date_of_averaged_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
