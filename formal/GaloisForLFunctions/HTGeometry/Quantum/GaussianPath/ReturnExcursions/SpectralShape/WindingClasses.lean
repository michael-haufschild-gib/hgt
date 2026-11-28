import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.TemplateFit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.PhysicalSublevel
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.GaussianVariance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.DateTail

/-! # Late winding fits with a prescribed cubic spectral shape -/

open Finset MeasureTheory Filter Set Real WithLp
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields
open private continuous_skew from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.PhysicalSublevel
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Some real template in the prescribed class fits all physical energy phases
at a single date after T. The template, phase and date can depend on the draw. -/
def classHit {n : ℕ} (c T x : ℝ) (h : PathShell n) : Prop :=
  ∃ b : (Fin (n+2)→Bool) → ℝ, shape (centered b)=c ∧
    ∃ t≥T, ∃ p : ℝ, ∀ i, |t*(isSelfAdjoint_pathHamiltonian h).isHermitian.eigenvalues i-b i-p|≤x

/-- Outside one variance event eventually absent along almost every frozen chain,
the probability of any fit after T costs at most 12r per specified cubic shape.
There is no upper endpoint on the observation time. -/
theorem physical_winding_classes :
    ∃ B : ℕ → Set PathPauliDisorder, (∀ n, MeasurableSet (B n)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉B n) ∧
      ∀ (n : ℕ) (F : Finset ℝ) (T x r : ℝ), let K : ℝ := (n+2:ℕ)
        0<T → 0≤x → 0<r → 16*x≤T*sqrt K →
        16000*x*(sqrt (13*K))^5<T*((2/3)*r^6) →
        pathPauliDisorderLaw.real ({ω | ∃ c∈F, classHit c T x (pathPauliDisorderShell ω n)} \ B n)
          ≤ (F.card:ℝ)*(12*r) := by
  classical
  let X (n : ℕ) (ω : PathPauliDisorder) : Coeff n := (pathPauliDisorderShell ω n).ofLp
  let K (n : ℕ) : ℝ := (n+2:ℕ)
  let V (n : ℕ) (h : Coeff n) := ∑ i, h i^2
  let B (n : ℕ) := X n ⁻¹' {h | V n h∉Icc (K n) (13*K n)}
  have hK (n) : 0<K n := by dsimp only [K]; positivity
  have hB (n) : MeasurableSet (B n) := by
    apply MeasurableSet.preimage _ (BlockDilations.prefix_measure n).measurable
    exact (measurableSet_Icc.preimage (Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).pow_const 2)).compl
  refine ⟨B,hB,?_,?_⟩
  · filter_upwards [SpectralGapMass.Bulk.gaussian_variance_per_site] with ω hw
    filter_upwards [hw.eventually_const_lt (by norm_num : (1:ℝ)<12),
      hw.eventually_lt_const (by norm_num : (12:ℝ)<13)] with n hl hu
    refine fun hh => hh ⟨?_,?_⟩
    · simpa only [one_mul] using ((lt_div_iff₀ (hK n)).mp hl).le
    · exact ((div_lt_iff₀ (hK n)).mp hu).le
  · intro n F T x r k hT hx hr hres hcut
    let A (c : ℝ) := {h : Coeff n | |skewConstraint c (toLp 2 h)|<(2/3)*r^6}
    have hA (c) : MeasurableSet (A c) := (measurableSet_lt (continuous_skew n c).abs.measurable
      measurable_const).preimage (MeasurableEquiv.toLp 2 (Coeff n)).measurable
    have hprice (c) : pathPauliDisorderLaw.real (X n ⁻¹' A c)≤12*r := by
      rw [(BlockDilations.prefix_measure n).measureReal_preimage (hA c).nullMeasurableSet]
      exact physical_skew_price n c r hr
    have hs : {ω | ∃ c∈F, classHit c T x (pathPauliDisorderShell ω n)} \ B n ⊆
        ⋃ c∈F, X n ⁻¹' A c := by
      rintro ω ⟨⟨c,hc,b,hb,t,ht,p,hfit⟩,hgood⟩
      refine mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,?_⟩⟩
      let h := pathPauliDisorderShell ω n
      have hbounds : ‖h‖^2∈Icc k (13*k) := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact not_not.mp hgood
      have hlo : sqrt k≤‖h‖ := (sqrt_le_iff.mpr ⟨norm_nonneg _,hbounds.1⟩)
      have hhi : ‖h‖ ≤ sqrt (13*k) := (le_sqrt (norm_nonneg _) (by positivity)).mpr hbounds.2
      have hp : 0<‖h‖ := (sqrt_pos.mpr (hK n)).trans_le hlo
      have ht' := hT.trans_le ht
      have hh := template_constraint h b (Equiv.refl _) ht' hp hx
        (hres.trans (mul_le_mul ht hlo (sqrt_nonneg _) ht'.le)) hfit
      rw [hb] at hh
      change |skewConstraint c h|<(2/3)*r^6
      apply lt_of_mul_lt_mul_left (a:=T) _ hT.le
      exact ((mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans hh).trans_lt
        ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhi 5) (by positivity)).trans_lt hcut)
    calc
      _ ≤ _ := measureReal_mono hs (measure_ne_top _ _)
      _ ≤ ∑ c∈F, pathPauliDisorderLaw.real (X n ⁻¹' A c) := measureReal_biUnion_finset_le ..
      _ ≤ ∑ _c∈F, (12*r) := sum_le_sum fun c _ => hprice c
      _ = _ := by simp

#print axioms physical_winding_classes
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
