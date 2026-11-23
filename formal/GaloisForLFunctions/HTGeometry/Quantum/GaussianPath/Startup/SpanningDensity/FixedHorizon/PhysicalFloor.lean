import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.PrescribedFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Fixed-error spanning cost at prescribed physical times -/
open MeasureTheory Set Filter Matrix GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
open OrdinaryTwoLocalGaussianHarmonicChoiGrowthLaw
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- An operator-norm fit up to phase gives a lower bound for the
absolute normalized Choi overlap of the two unitaries. -/
theorem overlap_of_fit {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U V : Matrix ι ι ℂ) (hU : U∈unitary _) (hV : V∈unitary _) (z : ℂ) (hz : ‖z‖=1)
    {ε : ℝ} (he : ‖U-z • V‖ ≤ ε) :
    1-ε^2/2 ≤ ‖inner ℂ (choiVector U) (choiVector V)‖ := by
  let x := choiVector U
  let y := choiVector V
  have hx : ‖x‖=1 := norm_choiVector_eq_one Fintype.card_pos (Unitary.mem_iff.mp hU).1
  have hy : ‖y‖=1 := norm_choiVector_eq_one Fintype.card_pos (Unitary.mem_iff.mp hV).1
  have hd : x-z • y=choiVector (U-z • V) := by
    ext p
    simp [x,y,choiVector,sub_div,smul_eq_mul,mul_div_assoc]
  have hh : ‖x-z • y‖ ≤ ε := by
    rw [hd]
    exact (norm_choiVector_le_l2_opNorm _).trans he
  have hs := (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hh)).mpr hh
  rw [norm_sub_sq (𝕜:=ℂ),hx,norm_smul,hz,hy,one_mul] at hs
  have h := Complex.re_le_norm (inner ℂ x (z • y))
  rw [inner_smul_right,norm_mul,hz,one_mul] at h
  rw [inner_smul_right] at hs
  change 1-ε^2/2 ≤ ‖inner ℂ x y‖
  change (z*inner ℂ x y).re ≤ _ at h
  change 1^2-2*(z*inner ℂ x y).re+1^2 ≤ ε^2 at hs
  linarith only [hs,h]

theorem overlap_threshold_pos {ε : ℝ} (hε : 0≤ε) (hε' : ε<Real.sqrt 2) :
    0<1-ε^2/2 := by
  have h := (sq_lt_sq₀ hε (Real.sqrt_nonneg _)).mpr hε'
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at h
  linarith only [h]

/-- For each fixed positive time interval and fixed error below √2, the
chance of fitting any circuit below density 1−η tends to zero, uniformly
in the prescribed observation date. -/
theorem gaussian_prescribed_gate_floor {a T η ε β : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | ∃ s : ℕ, (s:ℝ) ≤ (1-η)*(n+1:ℕ) ∧ HasProjectiveCircuitApproximation (n+2) ε s
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} ≤ β := by
  let κ := 1-ε^2/2
  have hκ : 0<κ := overlap_threshold_pos hε hε'
  filter_upwards [gaussian_prescribed_overlap (T:=T) ha hη hκ hβ] with n hn
  intro t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (hn t ht)
  rintro ω ⟨s,hs,z,hz,C,hC,hfit⟩
  exact ⟨C,(Nat.cast_le.mpr hC).trans hs,overlap_of_fit _ _ (unitaryEvolution_mem_unitary
    (isSelfAdjoint_pathHamiltonian _) t) C.eval.property z hz hfit⟩

#print axioms gaussian_prescribed_gate_floor

/-- The same positive lag separates all pairs of affordable dates,
including a lag measured from a disorder-dependent return. -/
theorem gaussian_prescribed_lag_floor {a T η ε β : ℝ} (ha : 0<a) (hη : 0<η)
    (hε : 0≤ε) (hε' : ε<Real.sqrt 2) (hβ : 0<β) :
    ∀ᶠ n : ℕ in atTop, ∀ t∈Icc a T, pathPauliDisorderLaw.real
      {ω | let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∃ v : ℝ, ∃ j s : ℕ, ∃ δ θ : ℝ, δ+θ≤ε ∧ ((j+s:ℕ):ℝ)≤(1-η)*(n+1:ℕ) ∧
          HasProjectiveCircuitApproximation (n+2) δ j (unitaryEvolution H v) ∧
          HasProjectiveCircuitApproximation (n+2) θ s (unitaryEvolution H (v+t))} ≤ β := by
  filter_upwards [gaussian_prescribed_gate_floor (T:=T) ha hη hε hε' hβ] with n hn
  intro t ht
  apply (measureReal_mono (μ:=pathPauliDisorderLaw) ?_ (measure_ne_top _ _)).trans (hn t ht)
  rintro ω ⟨v,j,s,δ,θ,herr,hsize,hv,hend⟩
  let H : selfAdjoint (Matrix (Fin (n+2) → Bool) (Fin (n+2) → Bool) ℂ) :=
    ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  change HasProjectiveCircuitApproximation (n+2) δ j (unitaryEvolution H.val v) at hv
  change HasProjectiveCircuitApproximation (n+2) θ s (unitaryEvolution H.val (v+t)) at hend
  have h := affordable_add_time H (x := -v) (y := v+t) (i := j) (j := s) (hv.neg_time H) hend
  rw [neg_add_cancel_left] at h
  obtain ⟨z,hz,C,hC,hfit⟩ := h
  exact ⟨j+s,hsize,z,hz,C,hC,hfit.trans herr⟩

#print axioms gaussian_prescribed_lag_floor
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
