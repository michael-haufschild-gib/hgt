import GaloisForLFunctions.HTGeometry.FinitePhasePacket
import GaloisForLFunctions.HTGeometry.L2TranslationExponentialIndependence

/-! # Exact nullspace of finite phase-packet energy -/

namespace GaloisForLFunctions.HTGeometry
open Filter Topology MeasureTheory Set
noncomputable section
open scoped Classical

theorem finitePhasePacket_zeros_countable {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (ω : ι → ℝ) (hω : Set.InjOn ω s)
    (ha : ∃ i ∈ s, a i ≠ 0) : {x : ℝ | finitePhasePacket s a ω x = 0}.Countable := by
  let e := (Fintype.equivFin s).symm
  let b := fun j => a (e j)
  let ν := fun j => ω (e j) / (2 * Real.pi)
  have hν : Function.Injective ν := by
    intro j k h
    apply e.injective
    apply Subtype.ext
    apply hω (e j).2 (e k).2
    exact (div_left_inj' (mul_ne_zero (by norm_num) Real.pi_ne_zero)).mp h
  have hb : b ≠ 0 := by
    intro h
    obtain ⟨i, hi, hai⟩ := ha
    have hz := congrFun h (e.symm ⟨i, hi⟩)
    apply hai
    simpa [b] using hz
  have he (x : ℝ) :
      (∑ j, b j * _root_.RHTower.MellinL2.fourierPhase (ν j) x) = finitePhasePacket s a ω x := by
    have hp (j) : _root_.RHTower.MellinL2.fourierPhase (ν j) x = paperRotationPhase (ω (e j) * x) := by
      rw [_root_.RHTower.MellinL2.fourierPhase, Real.fourierChar_apply]
      change Complex.exp _ = Complex.exp _
      congr 1
      dsimp only [ν]
      push_cast
      field_simp
    simp_rw [hp]
    rw [finitePhasePacket, ← Finset.sum_coe_sort s]
    exact e.sum_comp (fun i : s => a i * paperRotationPhase (ω i * x))
  simpa only [he] using fourierPhase_sum_zeros_countable ν hν b hb

theorem finitePhaseEnergy_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ω : ι → ℝ) :
    0 ≤ finitePhaseEnergy s a ω :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)

theorem finitePhaseEnergy_pos_iff {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) (hω : Set.InjOn ω s) :
    0 < finitePhaseEnergy s a ω ↔ ∃ i ∈ s, a i ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hz (x : ℝ) : finitePhasePacket s a ω x = 0 := by
      exact Finset.sum_eq_zero fun i hi => by simp [hn i hi]
    simp [finitePhaseEnergy, hz] at h
  · intro ha
    have hcount := finitePhasePacket_zeros_countable s a ω hω ha
    have hex : ∃ x ∈ Ioo (0 : ℝ) 1, finitePhasePacket s a ω x ≠ 0 := by
      by_contra h
      push Not at h
      have hc : (Ioo (0 : ℝ) 1).Countable := hcount.mono h
      have := Cardinal.Real.Ioo_countable_iff.mp hc
      norm_num at this
    obtain ⟨x, hx, hpx⟩ := hex
    have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f := fun _ : ℝ => 0) (g := fun x => ‖finitePhasePacket s a ω x‖ ^ 2)
      (by norm_num : (0 : ℝ) < 1) continuousOn_const
      (finitePhasePacket_energy_lipschitz s a ω).continuous.continuousOn
      (fun _ _ => sq_nonneg _) ⟨x, ⟨hx.1.le, hx.2.le⟩, sq_pos_of_pos (norm_pos_iff.mpr hpx)⟩
    simpa only [intervalIntegral.integral_zero, finitePhaseEnergy] using h

theorem finitePhaseEnergy_eq_zero_iff {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (ω : ι → ℝ) (hω : Set.InjOn ω s) :
    finitePhaseEnergy s a ω = 0 ↔ ∀ i ∈ s, a i = 0 := by
  constructor
  · intro hz i hi
    by_contra hn
    have hp := (finitePhaseEnergy_pos_iff s a ω hω).mpr ⟨i, hi, hn⟩
    linarith
  · intro h
    have hz (x : ℝ) : finitePhasePacket s a ω x = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [h i hi]
    simp [finitePhaseEnergy, hz]

end
end GaloisForLFunctions.HTGeometry
