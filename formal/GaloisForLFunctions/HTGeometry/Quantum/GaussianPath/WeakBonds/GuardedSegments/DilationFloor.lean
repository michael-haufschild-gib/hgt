import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.GuardedSegments.InverseSizeLag
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation

/-! # A uniform chance of spectral separation at every prescribed late date -/
open MeasureTheory ProbabilityTheory Filter Set Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
open PrescribedTimes
noncomputable section

private theorem dim_le (n : ℕ) : (Fintype.card (PrefixIndex n):ℝ) ≤ 16*((n+2:ℕ):ℝ) := by
  rw [Fintype.card_congr (pathCoeffEquiv n)]
  simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  push_cast
  linarith only [Nat.cast_nonneg (α:=ℝ) n]

private def hard (n : ℕ) (t : ℝ) : Set (PrefixIndex n → ℝ) :=
  {x | 1/3 < pathGateDistance n 0 x t}

private theorem hard_measurable (n : ℕ) (t : ℝ) : MeasurableSet (hard n t) :=
  (isOpen_lt continuous_const (continuous_distance_at_time n 0 t)).measurableSet

/-- Expanding the Gaussian by t/(t-h) sends the event at t-h to the
event at t. When h=B/N its Jacobian price is bounded independently of N. -/
private theorem lag_price (n : ℕ) {B t : ℝ} (hB : 0<B) (hN : 2*B ≤ ((n+2:ℕ):ℝ)) (ht : 1 ≤ t) :
    let μ := centredProductGaussian (PrefixIndex n) 1
    μ.real (hard n (t-B/(n+2:ℕ))) ≤ exp (32*B)*μ.real (hard n t) := by
  intro μ
  let N := n+2
  let h := B/(N:ℝ)
  have hNpos : 0<(N:ℝ) := by dsimp [N]; positivity
  have hh : 0<h := div_pos hB hNpos
  have hhalf : h ≤ 1/2 := (div_le_iff₀ hNpos).mpr (by linarith only [hN])
  have hden : 0<t-h := by linarith only [ht,hhalf]
  let a := t/(t-h)
  have ha : 1 ≤ a := (one_le_div₀ hden).mpr (by linarith only [hh])
  have hstep : a-1 ≤ 2*h := by
    have he : a-1=h/(t-h) := by dsimp only [a]; field_simp [hden.ne']; ring
    rw [he,div_le_iff₀ hden]
    have hp := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ t-h by linarith only [ht,hhalf]) hh.le
    linarith only [hp]
  let m := Fintype.card (PrefixIndex n)
  have hcost : (m:ℝ)*(a-1) ≤ 32*B := by
    apply (mul_le_mul (dim_le n) hstep (sub_nonneg.mpr ha) (by positivity)).trans_eq
    change 16*(N:ℝ)*(2*(B/N))=32*B
    field_simp [hNpos.ne']
    <;> ring
  have hpow : a^m ≤ exp (32*B) := by
    have he := Real.add_one_le_exp (a-1)
    rw [sub_add_cancel] at he
    exact (pow_le_pow_left₀ (zero_le_one.trans ha) he _).trans
      (by rw [←Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hcost)
  have hpre : (fun x : PrefixIndex n → ℝ => a • x) ⁻¹' hard n (t-h)=hard n t := by
    ext x
    change (1/3 < pathGateDistance n 0 (a • x) (t-h)) ↔ _
    rw [distance_dilate,show a*(t-h)=t from div_mul_cancel₀ _ hden.ne']
    rfl
  have hcomp := gaussian_dilation_comparison ha _ (hard_measurable n (t-h))
  rw [hpre] at hcomp
  exact hcomp.trans (mul_le_mul_of_nonneg_right hpow measureReal_nonneg)

/-- Uniformly for all t ≥ 1, a long independent Gaussian segment has
a fixed positive probability of projective scalar distance greater than 1/3. -/
theorem gaussian_segment_positive_probability :
    ∃ p>0, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, 1 ≤ t →
      p ≤ (centredProductGaussian (PrefixIndex n) 1).real {x | 1/3 < pathGateDistance n 0 x t} := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨B,hB,hlag⟩ := gaussian_segment_lag
  let h (n : ℕ) := B/((n+2:ℕ):ℝ)
  let F (n : ℕ) := {ω | pathGateDistance n 0 (segmentPoint n ω) (h n) ≤ 2/3}
  have hF (n : ℕ) : MeasurableSet (F n) :=
    (isClosed_le (continuous_distance_at_time n 0 (h n)) continuous_const).measurableSet.preimage
      (gaussian_pauli_prefix_coordinates_law n).measurable
  have hmiss : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω ∉ F n :=
    hlag.mono fun _ hw => hw.mono fun _ hn => hn.not_ge
  have hlim := ShortWindows.probability_vanishes pathPauliDisorderLaw F hF hmiss
  let c := 1+exp (32*B)
  have hc : 0<c := by dsimp [c]; positivity
  obtain ⟨K,hK⟩ := exists_nat_gt (2*B)
  refine ⟨(1/2)/c,div_pos (by norm_num) hc,?_⟩
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/2),eventually_ge_atTop K] with n hn hnK
  intro t ht
  let μ := centredProductGaussian (PrefixIndex n) 1
  let E (u : ℝ) := segmentPoint n ⁻¹' hard n u
  have hsub : (F n)ᶜ ⊆ E t ∪ E (t-h n) := fun ω hω =>
    one_hard_date n ω t (h n) (lt_of_not_ge hω)
  have hmeasure (u : ℝ) : pathPauliDisorderLaw.real (E u)=μ.real (hard n u) :=
    (gaussian_pauli_prefix_coordinates_law n).measureReal_preimage (hard_measurable n u).nullMeasurableSet
  have hsum := (measureReal_mono (μ:=pathPauliDisorderLaw) hsub).trans (measureReal_union_le _ _)
  rw [measureReal_compl (hF n),probReal_univ,hmeasure,hmeasure] at hsum
  have hp := lag_price n hB (hK.le.trans (Nat.cast_le.mpr (by omega))) ht
  apply (div_le_iff₀ hc).mpr
  change 1/2 ≤ μ.real (hard n t)*c
  dsimp only [c]
  change μ.real (hard n (t-h n)) ≤ _ at hp
  linarith only [hn,hsum,hp]

#print axioms gaussian_segment_positive_probability
end
end GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
