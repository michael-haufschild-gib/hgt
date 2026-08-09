import GaloisForLFunctions.RHTower.BaezDuarteDetectorIndependence
import GaloisForLFunctions.RHTower.DetectorDuality

/-!
# Finite-section floors from detector combinations, with no zero of zeta

`BaezDuarteL2Carrier` produces a positive floor for the Báez-Duarte distance from a *single* detector, and
only at a zero of `ζ` off the critical line: there the detector annihilates every generator at once.  For a
finite section only finitely many generators must be annihilated, and that can be arranged by linear
algebra instead — a combination of detectors at *arbitrary* points of the strip `½ < Re ρ < 1`, no
vanishing of `ζ` involved.

This file assembles the pairings of such a combination:

* `detectorCombination` — `∑ⱼ aⱼ • bdDetector (1 − ρⱼ)`;
* `inner_detectorCombination_bdGen` — `∑ⱼ conj(aⱼ)·(−(θ^{ρⱼ} − θ)·ζ(ρⱼ)/ρⱼ)`, the annihilation condition
  as an explicit finite sum;
* `inner_detectorCombination_bdTarget` — `∑ⱼ conj(aⱼ)/ρⱼ`, the separating pairing;
* `inner_detectorCombination_self` — `∑ⱼ∑ₖ conj(aⱼ)aₖ/((ρⱼ − ½) + conj(ρₖ − ½))`, the Cauchy-kernel
  quadratic form that measures the combination;
* `bdDist_ge_of_detectorCombination` and `bdDist_pos_of_detectorCombination` — the resulting floor
  `‖∑ⱼ conj(aⱼ)/ρⱼ‖ ≤ ‖w‖ · d(θ)`, positive exactly when the separating pairing does not vanish.

The floor is unconditional and says nothing about zeros: what it needs is one vector in the kernel of the
`N` generator pairings that survives the target pairing.  Since the generator pairings factor as
`(θᵢ^{ρⱼ} − θᵢ)·ζ(ρⱼ)/ρⱼ`, the kernel condition is a Müntz-type linear condition on the coefficients and is
nonempty as soon as there are more detector points than generators.
-/

open MeasureTheory Set Complex Metric Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- A finite combination of detectors at points to the right of the critical line. -/
def detectorCombination {M : ℕ} (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re) (a : Fin M → ℂ) :
    BDCarrier :=
  ∑ j, a j • bdDetector (one_sub_re_lt (hρ j))

/-- **The annihilation condition, explicitly.**  The pairing of a detector combination with a generator is
a finite sum of values of `ζ` at the chosen points. -/
theorem inner_detectorCombination_bdGen {M : ℕ} (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) (a : Fin M → ℂ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    inner ℂ (detectorCombination ρ hρ a) (bdGen θ)
      = ∑ j, (starRingEnd ℂ) (a j) *
          (-(((θ : ℝ) : ℂ) ^ ρ j - ((θ : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) := by
  rw [detectorCombination, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_bdDetector_bdGen (hρ j) (hρ1 j) hθ0 hθ1]

/-- **The separating pairing.**  A detector combination pairs with the target at `∑ⱼ conj(aⱼ)/ρⱼ`. -/
theorem inner_detectorCombination_bdTarget {M : ℕ} (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (a : Fin M → ℂ) :
    inner ℂ (detectorCombination ρ hρ a) bdTarget
      = ∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j) := by
  rw [detectorCombination, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_bdDetector_bdTarget (hρ j)]

/-- **The measure of the combination.**  Its squared norm is the Cauchy-kernel quadratic form at the
centered points `ρⱼ − ½`. -/
theorem inner_detectorCombination_self {M : ℕ} (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (a : Fin M → ℂ) :
    inner ℂ (detectorCombination ρ hρ a) (detectorCombination ρ hρ a)
      = ∑ j, ∑ k, (starRingEnd ℂ) (a j) * a k *
          (1 / ((ρ j - 1 / 2) + (starRingEnd ℂ) (ρ k - 1 / 2))) := by
  rw [detectorCombination, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_bdDetector_bdDetector_zeros (hρ j) (hρ k)]
  ring

/-! ## The floor -/

/-- **The detector floor for a Báez-Duarte distance.**  Any carrier element orthogonal to every generator
of the family bounds the distance from below.  This is the family form of the Cauchy--Schwarz step, with the
distance on the right rather than a single approximant. -/
theorem norm_inner_le_norm_mul_bdDist {I : Type*} (θ : I → ℝ) (w : BDCarrier)
    (hw : ∀ i, inner ℂ w (bdGen (θ i)) = 0) :
    ‖inner ℂ w bdTarget‖ ≤ ‖w‖ * bdDist θ :=
  norm_inner_le_norm_mul_infDist_span _ _ w (by
    rintro _ ⟨i, rfl⟩
    exact hw i)

/-- **The finite-section floor from a detector combination.**  No zero of `ζ` is assumed: the combination
annihilates the section by a linear condition on its coefficients. -/
theorem bdDist_ge_of_detectorCombination {N M : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) (a : Fin M → ℂ)
    (hann : ∀ i, ∑ j, (starRingEnd ℂ) (a j) *
      (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) = 0) :
    ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖
      ≤ ‖detectorCombination ρ hρ a‖ * bdDist θ := by
  have hzero : ∀ i, inner ℂ (detectorCombination ρ hρ a) (bdGen (θ i)) = 0 := by
    intro i
    rw [inner_detectorCombination_bdGen ρ hρ hρ1 a (hθ i).1 (hθ i).2]
    exact hann i
  have h := norm_inner_le_norm_mul_bdDist θ (detectorCombination ρ hρ a) hzero
  rwa [inner_detectorCombination_bdTarget ρ hρ a] at h

/-- **The section is obstructed whenever the separating pairing survives.**  A nonvanishing
`∑ⱼ conj(aⱼ)/ρⱼ` forces a positive distance, with the explicit quotient as a floor. -/
theorem bdDist_pos_of_detectorCombination {N M : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) (a : Fin M → ℂ)
    (hann : ∀ i, ∑ j, (starRingEnd ℂ) (a j) *
      (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) = 0)
    (hsep : ∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j) ≠ 0) :
    0 < bdDist θ ∧
      ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖ / ‖detectorCombination ρ hρ a‖ ≤ bdDist θ := by
  have hle := bdDist_ge_of_detectorCombination θ hθ ρ hρ hρ1 a hann
  have hnum : 0 < ‖∑ j, (starRingEnd ℂ) (a j) * (1 / ρ j)‖ := norm_pos_iff.mpr hsep
  have hwne : detectorCombination ρ hρ a ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_mul] at hle
    exact absurd (le_antisymm hle (norm_nonneg _)) (ne_of_gt hnum)
  have hwpos : 0 < ‖detectorCombination ρ hρ a‖ := norm_pos_iff.mpr hwne
  refine ⟨?_, (div_le_iff₀ hwpos).2 ?_⟩
  · rcases le_or_gt (bdDist θ) 0 with hd | hd
    · rw [le_antisymm hd (bdDist_nonneg θ), mul_zero] at hle
      exact absurd (le_antisymm hle (norm_nonneg _)) (ne_of_gt hnum)
    · exact hd
  · rwa [mul_comm] at hle

/-! ## Annihilating combinations always exist -/

/-- More unknowns than equations: a rectangular homogeneous system has a nonzero solution. -/
theorem exists_ne_zero_mulVec_eq_zero {N M : ℕ} (hNM : N < M) (A : Matrix (Fin N) (Fin M) ℂ) :
    ∃ b : Fin M → ℂ, b ≠ 0 ∧ A.mulVec b = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    exact hcon x hx0 (by simpa using hx)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at hle
  omega

/-- At distinct points a nonzero coefficient vector gives a nonzero combination: the detectors are linearly
independent. -/
theorem detectorCombination_ne_zero {M : ℕ} (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hinj : Function.Injective ρ) {a : Fin M → ℂ} (ha : a ≠ 0) :
    detectorCombination ρ hρ a ≠ 0 := by
  intro h
  have hli := linearIndependent_bdDetector_zeros ρ hρ hinj
  rw [Fintype.linearIndependent_iff] at hli
  have hsum : ∑ j, a j • bdDetector (one_sub_re_lt (hρ j)) = 0 := h
  exact ha (funext fun j => hli a hsum j)

/-- **Annihilating detector combinations always exist.**  With more points of the strip than generators in
the section, a nonzero coefficient vector annihilating every generator exists by rank alone.  No zero of `ζ`
and no property of the points enters beyond `½ < Re ρ < 1`, where the detectors are carrier vectors.

Together with `bdDist_pos_of_detectorCombination` this isolates the whole content of a finite-section floor:
annihilation is free, and everything depends on whether some annihilating combination keeps a nonvanishing
pairing `∑ⱼ conj(aⱼ)/ρⱼ` with the target. -/
theorem exists_ne_zero_annihilating_detectorCombination {N M : ℕ} (hNM : N < M) (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (ρ : Fin M → ℂ) (hρ : ∀ j, 1 / 2 < (ρ j).re)
    (hρ1 : ∀ j, (ρ j).re < 1) :
    ∃ a : Fin M → ℂ, a ≠ 0 ∧ ∀ i, inner ℂ (detectorCombination ρ hρ a) (bdGen (θ i)) = 0 := by
  obtain ⟨b, hb0, hb⟩ := exists_ne_zero_mulVec_eq_zero hNM
    (Matrix.of fun (i : Fin N) (j : Fin M) =>
      -(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
  refine ⟨fun j => (starRingEnd ℂ) (b j), ?_, ?_⟩
  · intro h
    exact hb0 (funext fun j => star_eq_zero.mp (congrFun h j))
  · intro i
    rw [inner_detectorCombination_bdGen ρ hρ hρ1 _ (hθ i).1 (hθ i).2]
    have hrow : ∑ j, (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) * b j
        = 0 := by
      have h := congrFun hb i
      rwa [Matrix.mulVec_apply_eq_sum] at h
    simp only [RCLike.conj_conj]
    calc ∑ j, b j * (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j))
        = ∑ j, (-(((θ i : ℝ) : ℂ) ^ ρ j - ((θ i : ℝ) : ℂ)) * (riemannZeta (ρ j) / ρ j)) * b j :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
      _ = 0 := hrow

end RHTower

end
