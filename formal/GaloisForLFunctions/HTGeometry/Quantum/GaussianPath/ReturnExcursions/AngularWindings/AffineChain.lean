import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.ChainResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.WitnessPlane
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.WindingPrice

/-! # Winding probabilities for the physical chain's affine energy packet -/

open MeasureTheory ProbabilityTheory Finset Real Set Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
open Dephasing.PairedFields Dephasing.PairedFields.SpectralEdge Dephasing.PairedFields.ClockAdjustment
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
private abbrev Levels (n : ℕ) := Fin (n+2) → Bool

/-- Lower bound on the RMS response along the weaker of the radial and tangent inputs. -/
def responseScale (n : ℕ) (r : ℝ) := min 1 (r^3/sqrt ((172*13^3:ℝ)*((n+2:ℕ):ℝ)))

/-- All deterministic centers, lifted windings, and observation intervals for the
independent field on this base. Dates may be chosen after seeing the independent field. -/
def pricedWindings {n : ℕ} (h : Coeff n) (r : ℝ) : Prop :=
  ∀ (A b : Levels n → ℝ) (η x T U : ℝ), η≠0 → 0≤x → 0<T →
    (fieldLaw n).real {g | windingWindow (fun j => A j+η*localSlope h g j) b x T U}
      ≤ x/(T*|η| * responseScale n r)

private theorem price_of_response {n : ℕ} (h : Coeff n) (r : ℝ)
    (hr : 0<r) (hV : 0<∑ i, h i^2) (hresp : hasAngularResponse h r) : pricedWindings h r := by
  intro A b η x T U hη hx hT
  obtain ⟨f,hf,hperp,hsize⟩ := hresp
  let d := responseScale n r
  let V := ∑ i, h i^2
  let R := sqrt V
  let M := (172*13^3:ℝ)*((n+2:ℕ):ℝ)
  let D := (2:ℝ)^(n+2)
  let E := (generator h).2.isHermitian.eigenvalues
  let p (i : PathLabel n) := h i/R
  let Q := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h)
  have hM : 0<M := by dsimp only [M]; positivity
  have hR : 0<R := sqrt_pos.mpr hV
  have hD : 0<D := pow_pos (by norm_num) _
  have hd : 0<d := lt_min zero_lt_one (div_pos (pow_pos hr _) (sqrt_pos.mpr hM))
  have dim : (Fintype.card (Levels n):ℝ)=D := by
    simp only [Levels,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,D]
  have hR₂ : R^2=V := sq_sqrt hV.le
  have hp : (∑ i, p i^2)=1 := by
    simp only [p,div_pow,←sum_div,hR₂]
    exact div_self hV.ne'
  have hpf : (∑ i, p i*f i)=0 := by
    simp_rw [show ∀ i, p i*f i=(h i*f i)/R from fun i => by dsimp only [p]; ring]
    rw [←sum_div,hperp,zero_div]
  have hpr (j : Levels n) : localSlope h p j=E j/R := by
    have he : E j=localSlope h h j := FirstGate.energy_from_local_expectations (WithLp.toLp 2 h) j
    simp only [he,localSlope,p,sum_div]
    exact sum_congr rfl fun i _ => by ring
  have horth : (∑ j, localSlope h p j*localSlope h f j)=0 := by
    have hcov := (slope_traces h f).2
    change (∑ j, E j*localSlope h f j)=_ at hcov
    rw [hperp,mul_zero] at hcov
    simp_rw [hpr,div_mul_eq_mul_div,←sum_div]
    rw [hcov,zero_div]
  have hrad : (∑ j, localSlope h p j^2)=D := by
    have he := (FluxOccupation.path_spectral_moments (WithLp.toLp 2 h)).2
    change (∑ j, E j^2)=((2^(n+2):ℕ):ℝ)*V at he
    rw [Nat.cast_pow,Nat.cast_ofNat] at he
    simp only [hpr,div_pow,←sum_div,hR₂,he,D]
    exact mul_div_cancel_right₀ _ (show V≠0 from hV.ne')
  have h₁ : D*d^2 ≤ ∑ j, localSlope h p j^2 := by
    rw [hrad]
    have hd₁ : d≤1 := min_le_left ..
    simpa only [one_pow,mul_one] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.le hd₁ 2) hD.le
  have h₂ : D*d^2 ≤ ∑ j, localSlope h f j^2 := by
    have hg := hsize 0 0
    simp only [zero_mul,add_zero] at hg
    change D*r^6 ≤ M*(∑ j, localSlope h f j^2) at hg
    have hd₂ := pow_le_pow_left₀ hd.le (min_le_right 1 (r^3/sqrt M)) 2
    change d^2≤_ at hd₂
    rw [div_pow,sq_sqrt hM.le,show (r^3)^2=r^6 by ring] at hd₂
    apply (mul_le_mul_of_nonneg_left hd₂ hD.le).trans
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hM).mpr (by simpa only [mul_comm M] using hg)
  obtain ⟨w,hw,hb,hm,hs⟩ := winding_witness Q p f b d hd hp.le hf hpf (slope_traces h p).1
    (slope_traces h f).1 horth (by rw [dim]; exact h₁) (by rw [dim]; exact h₂)
  exact winding_price Q A b w η d x T U hη hd hx hT hw hb hm hs

/-- Outside a common, eventually absent exception, the probability over physical bases
that any fixed-winding price fails is at most 12r, uniformly in system size. -/
theorem gaussian_affine_winding_prices :
    ∃ B : ℕ → Set PathPauliDisorder, (∀ n, MeasurableSet (B n)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω∉B n) ∧
      ∀ (n : ℕ) (r : ℝ), 0<r →
        pathPauliDisorderLaw.real ({ω | ¬pricedWindings (fun i => pathPauliDisorderShell ω n i) r} \ B n) ≤ 12*r := by
  obtain ⟨B,hB,hevent,hprob⟩ := gaussian_collective_response
  let X (n : ℕ) (ω : PathPauliDisorder) : Coeff n := fun i => pathPauliDisorderShell ω n i
  let Z (n : ℕ) := X n ⁻¹' {h : Coeff n | (∑ i, h i^2)≤0}
  have hZ (n) : MeasurableSet (Z n) := by
    apply MeasurableSet.preimage _ (BlockDilations.prefix_measure n).measurable
    exact measurableSet_le (Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).pow_const 2) measurable_const
  refine ⟨fun n => B n∪Z n,fun n => (hB n).union (hZ n),?_,?_⟩
  · filter_upwards [hevent,SpectralGapMass.Bulk.gaussian_variance_per_site] with ω hb hv
    filter_upwards [hb,hv.eventually_const_lt (by norm_num : (0:ℝ)<12)] with n hn hvn
    exact fun hh => hh.elim hn (fun hz => hvn.not_ge (div_nonpos_of_nonpos_of_nonneg hz (by positivity)))
  · intro n r hr
    apply (measureReal_mono (s₂:={ω | ¬hasAngularResponse (X n ω) r} \ B n) ?_).trans (hprob n r hr)
    rintro ω ⟨hfail,hout⟩
    exact ⟨fun h => hfail (price_of_response _ r hr (lt_of_not_ge fun hz => hout (Or.inr hz)) h),
      fun hh => hout (Or.inl hh)⟩

#print axioms gaussian_affine_winding_prices
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
