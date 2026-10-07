import GaloisForLFunctions.HTGeometry.CosineProductRepair

/-!
# Local return jets exclude projective periods of the product repair

The argument retains common basepoints. At a double source return, continuous
divided differences expose the next nonzero local coefficient. Integer fiber
labels and exact derivative identities then force the return to be the origin.
-/

namespace GaloisForLFunctions.HTGeometry.CosineProductAperiodic

open Complex Filter LabeledCosineDescent CosineProductRepair
open CosineBasepointRepair (divided divided_mul divided_entire source_deriv_zero_ne)
open scoped Topology ComplexConjugate

noncomputable section

theorem source_return_jet {w : ℂ} (h : source w = source 0) :
    ∃ n : ℤ, w = fiberPoint 1 n ∧ deriv source w * (18 * n + 1) = deriv source 0 := by
  have hf0 : fiberPoint 1 0 = 0 := by norm_num [fiberPoint]
  have hs0 : source 0 = fiberValue 1 := by simpa [hf0] using source_fiberPoint 1 0
  obtain ⟨n, hn⟩ := (source_eq_fiberValue_iff w 1).mp (h.trans hs0)
  refine ⟨n, hn, ?_⟩
  have hj := source_jet_identity 1 n
  have hj0 := source_jet_identity 1 0
  simp only [Int.cast_zero, mul_zero, zero_add, Int.cast_one, mul_one, hf0] at hj0
  simp only [← hn, Int.cast_one, mul_one] at hj
  exact hj.trans hj0.symm

theorem source_return_not_half_jet {w : ℂ} (h : source w = source 0) :
    2 * deriv source w ≠ deriv source 0 := by
  intro he
  obtain ⟨n, _, hn⟩ := source_return_jet h
  have hs : deriv source w ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hn
    exact source_deriv_zero_ne hn.symm
  have hm : (18 * (n : ℂ) + 1) = 2 := by
    apply mul_left_cancel₀ hs
    linear_combination hn - he
  have hi : 18 * n + 1 = 2 := by exact_mod_cast hm
  omega

theorem period_source_identity {τ : ℂ}
    (hper : ∀ w, numerator (w + τ) * denominator w = numerator w * denominator (w + τ))
    (w : ℂ) :
    (source (w + τ) - source (-(w + τ))) * w * divided w * divided (-w) +
      (source (w + τ) - source 0) * (source (-(w + τ)) - source 0) *
        (divided w + divided (-w)) = 0 := by
  have hs := scaled_coordinates (w + τ)
  have hp := hper w
  have he : (2 * I) *
      ((source (w + τ) - source (-(w + τ))) * w * divided w * divided (-w) +
      (source (w + τ) - source 0) * (source (-(w + τ)) - source 0) *
        (divided w + divided (-w))) = 0 := by
    dsimp [numerator, denominator] at hp hs
    linear_combination (w + τ) * hp -
      (divided w + divided (-w) + I * w * divided w * divided (-w)) * hs.1 +
      (divided w + divided (-w) - I * w * divided w * divided (-w)) * hs.2
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) I_ne_zero)

theorem period_source_product_zero {τ : ℂ}
    (hper : ∀ w, numerator (w + τ) * denominator w = numerator w * denominator (w + τ)) :
    (source τ - source 0) * (source (-τ) - source 0) = 0 := by
  have h := period_source_identity hper 0
  simp only [zero_add, mul_zero, zero_mul, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_right (by
    simpa [denominator] using denominator_zero_ne)

theorem period_first_return_jet {τ : ℂ}
    (hper : ∀ w, numerator (w + τ) * denominator w = numerator w * denominator (w + τ)) :
    deriv source 0 * (source τ - source (-τ)) +
      2 * (deriv source τ * (source (-τ) - source 0) -
        deriv source (-τ) * (source τ - source 0)) = 0 := by
  have hp : HasDerivAt (fun w : ℂ ↦ source (w + τ)) (deriv source τ) 0 := by
    simpa [Function.comp_def] using
      (source_entire (0 + τ)).hasDerivAt.comp (0 : ℂ) ((hasDerivAt_id 0).add_const τ)
  have hq : HasDerivAt (fun w : ℂ ↦ source (-(w + τ))) (-deriv source (-τ)) 0 := by
    simpa [Function.comp_def] using
      (source_entire (-(0 + τ))).hasDerivAt.comp (0 : ℂ) (((hasDerivAt_id 0).add_const τ).neg)
  have hb := (divided_entire (0 : ℂ)).hasDerivAt
  have hn : HasDerivAt (fun w : ℂ ↦ divided (-w)) (-deriv divided 0) 0 := by
    simpa only [Function.comp_def, neg_zero, mul_neg_one] using
      (divided_entire (-(0 : ℂ))).hasDerivAt.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have hd := ((((hp.sub hq).mul (hasDerivAt_id (0 : ℂ))).mul hb).mul hn).add
    (((hp.sub_const (source 0)).mul (hq.sub_const (source 0))).mul (hb.add hn))
  have heq : (fun w : ℂ ↦
      (source (w + τ) - source (-(w + τ))) * w * divided w * divided (-w) +
      (source (w + τ) - source 0) * (source (-(w + τ)) - source 0) *
        (divided w + divided (-w))) = fun _ ↦ 0 := funext (period_source_identity hper)
  change HasDerivAt (fun w : ℂ ↦
      (source (w + τ) - source (-(w + τ))) * w * divided w * divided (-w) +
      (source (w + τ) - source 0) * (source (-(w + τ)) - source 0) *
        (divided w + divided (-w))) _ 0 at hd
  rw [heq] at hd
  have hj := hd.unique (hasDerivAt_const (0 : ℂ) (0 : ℂ))
  simp [divided] at hj
  apply mul_left_cancel₀ source_deriv_zero_ne
  linear_combination hj

theorem period_double_return_jet {τ : ℂ}
    (hper : ∀ w, numerator (w + τ) * denominator w = numerator w * denominator (w + τ))
    (hp : source τ = source 0) (hq : source (-τ) = source 0) :
    deriv source 0 * (deriv source τ + deriv source (-τ)) =
      2 * deriv source τ * deriv source (-τ) := by
  let u (w : ℂ) := dslope source τ (w + τ)
  let v (w : ℂ) := dslope source (-τ) (-(w + τ))
  let F (w : ℂ) := (u w + v w) * divided w * divided (-w) -
    u w * v w * (divided w + divided (-w))
  have hu : ContinuousAt u 0 := by
    have hh : ContinuousAt (dslope source τ) ((0 : ℂ) + τ) := by
      simpa using continuousAt_dslope_same.mpr (source_entire τ)
    simpa [u, Function.comp_def] using hh.comp (f := fun w : ℂ ↦ w + τ)
      (by fun_prop : ContinuousAt (fun w : ℂ ↦ w + τ) 0)
  have hv : ContinuousAt v 0 := by
    have hh : ContinuousAt (dslope source (-τ)) (-((0 : ℂ) + τ)) := by
      simpa using continuousAt_dslope_same.mpr (source_entire (-τ))
    simpa [v, Function.comp_def] using hh.comp (f := fun w : ℂ ↦ -(w + τ))
      (by fun_prop : ContinuousAt (fun w : ℂ ↦ -(w + τ)) 0)
  have hb := (divided_entire (0 : ℂ)).continuousAt
  have hn : ContinuousAt (fun w : ℂ ↦ divided (-w)) 0 := by
    have hh : ContinuousAt divided (-(0 : ℂ)) := by simpa using hb
    exact hh.comp continuousAt_id.neg
  have hc : ContinuousAt F 0 :=
    (((hu.add hv).mul hb).mul hn).sub ((hu.mul hv).mul (hb.add hn))
  have he : ∀ w : ℂ, w ≠ 0 → F w = 0 := by
    intro w hw
    have hu' : source (w + τ) = w * u w + source 0 := by
      have h := sub_smul_dslope source τ (w + τ)
      simp only [add_sub_cancel_right, smul_eq_mul, hp] at h
      linear_combination -h
    have hv' : source (-(w + τ)) = -w * v w + source 0 := by
      have h := sub_smul_dslope source (-τ) (-(w + τ))
      simp only [smul_eq_mul, hq] at h
      linear_combination -h
    have h := period_source_identity hper w
    rw [hu', hv'] at h
    have hz : w ^ 2 * F w = 0 := by
      dsimp [F]
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hw)
  have he' : F =ᶠ[𝓝[≠] (0 : ℂ)] fun _ ↦ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact he w hw
  have hz : Tendsto F (𝓝[≠] (0 : ℂ)) (𝓝 0) := tendsto_const_nhds.congr' he'.symm
  have hh := tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) hz
  simp only [F, u, v, zero_add, dslope_same, neg_zero, divided] at hh
  apply mul_left_cancel₀ source_deriv_zero_ne
  linear_combination hh

theorem double_return_jet_rigid {τ : ℂ}
    (hp : source τ = source 0) (hq : source (-τ) = source 0)
    (hjet : deriv source 0 * (deriv source τ + deriv source (-τ)) =
      2 * deriv source τ * deriv source (-τ)) : τ = 0 := by
  obtain ⟨n, hn, hs⟩ := source_return_jet hp
  obtain ⟨m, hm, ht⟩ := source_return_jet hq
  have hsne : deriv source τ ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hs
    exact source_deriv_zero_ne hs.symm
  have htne : deriv source (-τ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at ht
    exact source_deriv_zero_ne ht.symm
  have hnm : (18 * (n : ℂ) + 1) + (18 * (m : ℂ) + 1) = 2 := by
    apply mul_left_cancel₀ (mul_ne_zero hsne htne)
    linear_combination deriv source (-τ) * hs + deriv source τ * ht + hjet
  have hi : n + m = 0 := by
    have hh : (n : ℂ) + m = 0 := by linear_combination (1 / 18 : ℂ) * hnm
    exact_mod_cast hh
  have hm' : m = -n := by omega
  subst m
  have hn0 : (n : ℂ) ^ 2 = 0 := by
    dsimp [fiberPoint] at hn hm
    push_cast at hn hm
    linear_combination (-1 / 54 : ℂ) * hn + (-1 / 54 : ℂ) * hm
  have hnZ : n = 0 := by exact_mod_cast (sq_eq_zero_iff.mp hn0)
  simpa [hnZ, fiberPoint] using hn

theorem projective_period_eq_zero {τ : ℂ}
    (hper : ∀ w, numerator (w + τ) * denominator w = numerator w * denominator (w + τ)) :
    τ = 0 := by
  have hj := period_first_return_jet hper
  by_cases hp : source τ = source 0
  · by_cases hq : source (-τ) = source 0
    · exact double_return_jet_rigid hp hq (period_double_return_jet hper hp hq)
    · exfalso
      apply source_return_not_half_jet hp
      apply mul_right_cancel₀ (sub_ne_zero.mpr hq)
      rw [hp] at hj
      linear_combination hj
  · have hq : source (-τ) = source 0 := sub_eq_zero.mp
      ((mul_eq_zero.mp (period_source_product_zero hper)).resolve_left (sub_ne_zero.mpr hp))
    exfalso
    apply source_return_not_half_jet hq
    apply mul_right_cancel₀ (sub_ne_zero.mpr hp)
    rw [hq] at hj
    linear_combination -hj

theorem reflected_lattice_aperiodic_certificate :
    Differentiable ℂ numerator ∧ Differentiable ℂ denominator ∧
    denominator 0 ≠ 0 ∧ repair 0 = 1 ∧ AnalyticAt ℂ repair 0 ∧ deriv repair 0 ≠ 0 ∧
    (∀ w, repair (-w) = (repair w)⁻¹) ∧
    (∀ w, repair (conj w) = (conj (repair w))⁻¹) ∧
    (∀ w, numerator w = denominator w → ∃ n : ℤ, w = 3 * n) ∧
    (∀ τ, (∀ w, numerator (w + τ) * denominator w =
      numerator w * denominator (w + τ)) → τ = 0) :=
  ⟨numerator_entire, denominator_entire, denominator_zero_ne, repair_zero,
    repair_analyticAt_zero, repair_deriv_zero_ne, repair_reciprocal, repair_conjugate,
    fun _ ↦ coordinates_equal_lattice, fun _ ↦ projective_period_eq_zero⟩

end

end GaloisForLFunctions.HTGeometry.CosineProductAperiodic
