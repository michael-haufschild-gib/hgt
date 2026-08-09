import GaloisForLFunctions.RHTower.FiniteSectionBorderDeterminant
import GaloisForLFunctions.RHTower.SamplingDeterminant

/-!
# Vanishing at every sample is a relation among the row functions

`FiniteSectionBorderDeterminant` shows that one nonvanishing bordered determinant certifies a positive
Báez-Duarte distance.  The remaining question is whether such a sample exists, and `SamplingDeterminant`
answers it in the only way available: a determinant vanishing at *every* sample is a linear relation among
the row functions.

The rows are the functions on the open strip

`Fᵢ(s) = −(θᵢ^s − θᵢ)·ζ(s)/s` for `i < N`,  `F_N(s) = 1/s`,

and `sampledBorderMatrix` is their evaluation matrix.  Hence

**`exists_relation_of_forall_det_eq_zero` — if every bordered determinant vanishes there are coefficients
`c`, not all zero, with `(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` at every point of the strip.**

Read forwards, the same independence is the reusable interface, and it is stated for an arbitrary family.
`exists_detectorCombination_floor_of_linearIndependent_pairings`: if the Mellin detectors pair with a finite
family `G` and a target `x` through linearly independent functions on the strip, then there are sample points
`y` in the strip and coefficients `a` whose detector combination annihilates `G`, pairs with `x` at exactly
`1`, and certifies two floors for `dist(x, span G)` — the sharp `1/‖w‖` and the elementary

`1 / ∑ⱼ ‖aⱼ‖/√(2 Re yⱼ − 1)`,

which mentions only the coefficients and the real parts of the sample points.  Sampling makes the pairing
matrix invertible, solving against the last basis vector produces `a`, the duality bound of `DetectorDuality`
turns the pairing into the first floor, and `norm_detectorCombination_le` turns it into the second.
`exists_detector_floor_of_linearIndependent_pairings` and `infDist_pos_of_linearIndependent_pairings` are the
weaker forms, and `bdDist_pos_of_linearIndependent_borderRowFun` the Báez-Duarte instance.

So a finite section escapes every determinant certificate only if the Müntz system `θ^s − θ` inverts `ζ` by
a *single* relation valid on the whole strip — not merely sample by sample. That is a rigid identity between
`ζ` and an entire function, which is what the next step contradicts.
-/

open Complex

noncomputable section

namespace RHTower

/-- The open strip `½ < Re s < 1`, as the domain of the row functions. -/
abbrev StripPoint := {s : ℂ // 1 / 2 < s.re ∧ s.re < 1}

/-- The row functions of the bordered matrix: the `N` generator pairings, then the target pairing. -/
def borderRowFun {N : ℕ} (θ : Fin N → ℝ) : Fin (N + 1) → (StripPoint → ℂ) :=
  (Fin.snoc
    (fun (i : Fin N) (s : StripPoint) =>
      -(((θ i : ℝ) : ℂ) ^ (s : ℂ) - ((θ i : ℝ) : ℂ)) * (riemannZeta (s : ℂ) / (s : ℂ)))
    (fun (s : StripPoint) => 1 / (s : ℂ)) : Fin (N + 1) → (StripPoint → ℂ))

theorem borderRowFun_castSucc {N : ℕ} (θ : Fin N → ℝ) (i : Fin N) (s : StripPoint) :
    borderRowFun θ i.castSucc s
      = -(((θ i : ℝ) : ℂ) ^ (s : ℂ) - ((θ i : ℝ) : ℂ)) * (riemannZeta (s : ℂ) / (s : ℂ)) := by
  simp [borderRowFun]

theorem borderRowFun_last {N : ℕ} (θ : Fin N → ℝ) (s : StripPoint) :
    borderRowFun θ (Fin.last N) s = 1 / (s : ℂ) := by
  simp [borderRowFun]

/-- The evaluation matrix of the row functions is the bordered matrix of sampled pairings. -/
theorem matrix_borderRowFun_eq_sampledBorderMatrix {N : ℕ} (θ : Fin N → ℝ)
    (x : Fin (N + 1) → StripPoint) :
    (Matrix.of fun i j => borderRowFun θ i (x j))
      = sampledBorderMatrix θ fun j => ((x j : ℂ)) := by
  refine Matrix.ext fun i j => ?_
  refine Fin.lastCases ?_ ?_ i
  · rw [Matrix.of_apply, borderRowFun_last, sampledBorderMatrix_last]
  · intro i'
    rw [Matrix.of_apply, borderRowFun_castSucc, sampledBorderMatrix_castSucc]

/-- If every bordered determinant vanishes, the row functions are linearly dependent. -/
theorem not_linearIndependent_borderRowFun {N : ℕ} (θ : Fin N → ℝ)
    (h : ∀ ρ : Fin (N + 1) → ℂ, (∀ j, 1 / 2 < (ρ j).re) → (∀ j, (ρ j).re < 1) →
      (sampledBorderMatrix θ ρ).det = 0) :
    ¬ LinearIndependent ℂ (borderRowFun θ) := by
  refine not_linearIndependent_of_forall_det_eq_zero _ fun x => ?_
  rw [matrix_borderRowFun_eq_sampledBorderMatrix θ x]
  exact h _ (fun j => (x j).2.1) (fun j => (x j).2.2)

/-- **A single relation on the whole strip.**  A linear dependence among the pairing functions is, after
clearing the `1/s`, one fixed coefficient vector inverting `ζ` against the Müntz system at every point of the
strip. -/
theorem muentz_relation_of_not_linearIndependent {N : ℕ} (θ : Fin N → ℝ)
    (h : ¬ LinearIndependent ℂ (borderRowFun θ)) :
    ∃ c : Fin (N + 1) → ℂ, (∃ i, c i ≠ 0) ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) * riemannZeta s
        = c (Fin.last N) := by
  obtain ⟨c, hrel, hne⟩ := Fintype.not_linearIndependent_iff.1 h
  refine ⟨c, hne, fun s hs hs1 => ?_⟩
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hs
    norm_num at hs
  -- evaluate the relation at the point `s`
  have hval : (∑ i : Fin N, c i.castSucc *
        (-(((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ)) * (riemannZeta s / s)))
      + c (Fin.last N) * (1 / s) = 0 := by
    have h0 := congrFun hrel ⟨s, hs, hs1⟩
    rw [Fin.sum_univ_castSucc] at h0
    simpa [Pi.add_apply, Finset.sum_apply, borderRowFun_castSucc, borderRowFun_last] using h0
  have hsum : ∑ i : Fin N, c i.castSucc *
        (-(((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ)) * (riemannZeta s / s))
      = (∑ i : Fin N, -(c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))))
          * (riemannZeta s / s) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum] at hval
  have hneg : (∑ i : Fin N, -(c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))))
      = -(∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) := by
    simp
  rw [hneg] at hval
  field_simp at hval
  linear_combination -hval

/-- If every bordered determinant vanishes, one fixed coefficient vector inverts `ζ` on the whole strip. -/
theorem exists_relation_of_forall_det_eq_zero {N : ℕ} (θ : Fin N → ℝ)
    (h : ∀ ρ : Fin (N + 1) → ℂ, (∀ j, 1 / 2 < (ρ j).re) → (∀ j, (ρ j).re < 1) →
      (sampledBorderMatrix θ ρ).det = 0) :
    ∃ c : Fin (N + 1) → ℂ, (∃ i, c i ≠ 0) ∧ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      (∑ i : Fin N, c i.castSucc * (((θ i : ℝ) : ℂ) ^ s - ((θ i : ℝ) : ℂ))) * riemannZeta s
        = c (Fin.last N) :=
  muentz_relation_of_not_linearIndependent θ (not_linearIndependent_borderRowFun θ h)

/-- **The abstract obstruction, for any family in the carrier.**  Suppose the Mellin detectors pair with a
finite family `G` and with a target `x` through functions `M` on the strip.  If those `N+1` functions are
linearly independent, the target is at positive distance from the span of the family.

Sampling makes the pairing matrix invertible, so the linear system whose right-hand side is the last basis
vector has a solution; the corresponding detector combination annihilates every member of the family while
pairing with the target at `1`, and the duality bound of `DetectorDuality` converts that into the floor
`1/‖w‖`.  A family other than Báez-Duarte's inherits the whole route by supplying this one hypothesis for its
own pairing functions. -/
theorem exists_detectorCombination_floor_of_linearIndependent_pairings {N : ℕ}
    (G : Fin N → BDCarrier) (x : BDCarrier) (M : Fin (N + 1) → (StripPoint → ℂ))
    (hM : ∀ (i : Fin N) (s : StripPoint),
      inner ℂ (bdDetector (one_sub_re_lt s.2.1)) (G i) = M i.castSucc s)
    (hMx : ∀ s : StripPoint, inner ℂ (bdDetector (one_sub_re_lt s.2.1)) x = M (Fin.last N) s)
    (hli : LinearIndependent ℂ M) :
    ∃ (y : Fin (N + 1) → StripPoint) (a : Fin (N + 1) → ℂ),
      (∀ i, inner ℂ (detectorCombination (fun j => ((y j : ℂ))) (fun j => (y j).2.1) a) (G i) = 0)
        ∧ inner ℂ (detectorCombination (fun j => ((y j : ℂ))) (fun j => (y j).2.1) a) x = 1
        ∧ 1 / ‖detectorCombination (fun j => ((y j : ℂ))) (fun j => (y j).2.1) a‖
            ≤ Metric.infDist x (Submodule.span ℂ (Set.range G) : Set BDCarrier)
        ∧ 1 / (∑ j, ‖a j‖ / Real.sqrt (2 * ((y j : ℂ)).re - 1))
            ≤ Metric.infDist x (Submodule.span ℂ (Set.range G) : Set BDCarrier) := by
  classical
  obtain ⟨y, hy⟩ := exists_det_ne_zero_of_linearIndependent M hli
  set A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.of fun i j => M i (y j) with hA
  set e : Fin (N + 1) → ℂ := fun i => if i = Fin.last N then 1 else 0 with he
  set b : Fin (N + 1) → ℂ := A⁻¹.mulVec e with hb
  have hsolve : A.mulVec b = e := by
    rw [hb, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hy),
      Matrix.one_mulVec]
  set a : Fin (N + 1) → ℂ := fun j => (starRingEnd ℂ) (b j) with ha
  set w : BDCarrier :=
    detectorCombination (fun j => ((y j : ℂ))) (fun j => (y j).2.1) a with hw
  have hrow : ∀ i : Fin (N + 1), ∑ j, b j * M i (y j) = e i := by
    intro i
    have h := congrFun hsolve i
    rw [Matrix.mulVec_apply_eq_sum] at h
    rw [← h, hA]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hwG : ∀ i : Fin N, inner ℂ w (G i) = 0 := by
    intro i
    have hterm : ∀ j : Fin (N + 1),
        inner ℂ ((starRingEnd ℂ) (b j) • bdDetector (one_sub_re_lt (y j).2.1)) (G i)
          = b j * M i.castSucc (y j) := by
      intro j
      rw [inner_smul_left, RCLike.conj_conj, hM i (y j)]
    rw [hw, detectorCombination, sum_inner, Finset.sum_congr rfl fun j _ => hterm j,
      hrow i.castSucc, he]
    simp [Fin.castSucc_ne_last i]
  have hwx : inner ℂ w x = 1 := by
    have hterm : ∀ j : Fin (N + 1),
        inner ℂ ((starRingEnd ℂ) (b j) • bdDetector (one_sub_re_lt (y j).2.1)) x
          = b j * M (Fin.last N) (y j) := by
      intro j
      rw [inner_smul_left, RCLike.conj_conj, hMx (y j)]
    rw [hw, detectorCombination, sum_inner, Finset.sum_congr rfl fun j _ => hterm j,
      hrow (Fin.last N), he]
    simp
  have hbound := norm_inner_le_norm_mul_infDist_span (Set.range G) x w (by
    rintro _ ⟨i, rfl⟩
    exact hwG i)
  rw [hwx, norm_one] at hbound
  have hwne : w ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hwx
    exact zero_ne_one hwx
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hfloor : 1 / ‖w‖ ≤ Metric.infDist x (Submodule.span ℂ (Set.range G) : Set BDCarrier) := by
    rw [div_le_iff₀ hwpos, mul_comm]
    exact hbound
  have htri : ‖w‖ ≤ ∑ j, ‖a j‖ / Real.sqrt (2 * ((y j : ℂ)).re - 1) := by
    rw [hw]
    exact norm_detectorCombination_le (fun j => ((y j : ℂ))) (fun j => (y j).2.1) a
  exact ⟨y, a, hwG, hwx, hfloor, le_trans (one_div_le_one_div_of_le hwpos htri) hfloor⟩

/-- The floor in terms of the combination itself. -/
theorem exists_detector_floor_of_linearIndependent_pairings {N : ℕ} (G : Fin N → BDCarrier)
    (x : BDCarrier) (M : Fin (N + 1) → (StripPoint → ℂ))
    (hM : ∀ (i : Fin N) (s : StripPoint),
      inner ℂ (bdDetector (one_sub_re_lt s.2.1)) (G i) = M i.castSucc s)
    (hMx : ∀ s : StripPoint, inner ℂ (bdDetector (one_sub_re_lt s.2.1)) x = M (Fin.last N) s)
    (hli : LinearIndependent ℂ M) :
    ∃ w : BDCarrier, (∀ i, inner ℂ w (G i) = 0) ∧ inner ℂ w x = 1 ∧
      1 / ‖w‖ ≤ Metric.infDist x (Submodule.span ℂ (Set.range G) : Set BDCarrier) := by
  obtain ⟨y, a, hwG, hwx, hfloor, -⟩ :=
    exists_detectorCombination_floor_of_linearIndependent_pairings G x M hM hMx hli
  exact ⟨_, hwG, hwx, hfloor⟩

/-- **The abstract obstruction.**  Independence of the pairing functions puts the target at positive distance
from the span. -/
theorem infDist_pos_of_linearIndependent_pairings {N : ℕ} (G : Fin N → BDCarrier) (x : BDCarrier)
    (M : Fin (N + 1) → (StripPoint → ℂ))
    (hM : ∀ (i : Fin N) (s : StripPoint),
      inner ℂ (bdDetector (one_sub_re_lt s.2.1)) (G i) = M i.castSucc s)
    (hMx : ∀ s : StripPoint, inner ℂ (bdDetector (one_sub_re_lt s.2.1)) x = M (Fin.last N) s)
    (hli : LinearIndependent ℂ M) :
    0 < Metric.infDist x (Submodule.span ℂ (Set.range G) : Set BDCarrier) := by
  obtain ⟨w, -, hwx, hfloor⟩ :=
    exists_detector_floor_of_linearIndependent_pairings G x M hM hMx hli
  have hwne : w ≠ 0 := by
    intro h
    rw [h, inner_zero_left] at hwx
    exact zero_ne_one hwx
  exact lt_of_lt_of_le (by positivity) hfloor

/-- **The Báez-Duarte instance.**  Linear independence of its pairing functions gives a positive distance. -/
theorem bdDist_pos_of_linearIndependent_borderRowFun {N : ℕ} (θ : Fin N → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (hli : LinearIndependent ℂ (borderRowFun θ)) :
    0 < bdDist θ :=
  infDist_pos_of_linearIndependent_pairings (fun i => bdGen (θ i)) bdTarget (borderRowFun θ)
    (fun i s => by
      rw [borderRowFun_castSucc, inner_bdDetector_bdGen s.2.1 s.2.2 (hθ i).1 (hθ i).2])
    (fun s => by rw [borderRowFun_last, inner_bdDetector_bdTarget s.2.1]) hli

end RHTower

end
