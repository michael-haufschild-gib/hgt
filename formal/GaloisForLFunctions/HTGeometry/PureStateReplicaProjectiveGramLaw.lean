import Mathlib

/-!
# Pure-state replica projective-Gram law

For a finite pure-state model, the horizontal tangent of an `r`-fold tensor
power is the sum of `r` mutually orthogonal slot tangents.  Its projective
Gram matrix is therefore exactly `r` times the one-copy Gram, and a rank-`v`
determinant is exactly `r^v` times the one-copy determinant.

At the same time, tensor-product fidelity is the `r`th power of one-copy
fidelity.  When the capture threshold is transported by the same power, every
target capture and the complete target union are unchanged.  Thus normalized
projective-Jacobian lower tails and matched approximate tubes compensate
exactly at every positive replica order.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate formula for the complex inner product on a finite pure-state
space. -/
def finiteComplexInner {α : Type*} [Fintype α]
    (u v : α → ℂ) : ℂ :=
  ∑ x, conj (u x) * v x

theorem finiteComplexInner_conj_symm
    {α : Type*} [Fintype α] (u v : α → ℂ) :
    finiteComplexInner u v = conj (finiteComplexInner v u) := by
  simp [finiteComplexInner, mul_comm]

/-- Coordinate realization of an `r`-fold pure tensor. -/
def finitePureTensorPower {α : Type*} [Fintype α]
    (r : ℕ) (ψ : α → ℂ) (x : Fin r → α) : ℂ :=
  ∏ a, ψ (x a)

/-- Tangent placed in one selected tensor slot. -/
def finitePureTensorTangentSlot {α : Type*} [Fintype α]
    (r : ℕ) (ψ u : α → ℂ) (a : Fin r) (x : Fin r → α) : ℂ :=
  ∏ b, if b = a then u (x b) else ψ (x b)

/-- Derivative of an `r`-fold pure tensor: sum of the `r` slot tangents. -/
def finitePureTensorTangent {α : Type*} [Fintype α]
    (r : ℕ) (ψ u : α → ℂ) (x : Fin r → α) : ℂ :=
  ∑ a, finitePureTensorTangentSlot r ψ u a x

/-- A finite sum over tensor-product coordinates factors into a product of
one-coordinate sums. -/
theorem sum_pi_prod_complex {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (f : ι → α → ℂ) :
    (∑ x : ι → α, ∏ i, f i (x i)) = ∏ i, ∑ a, f i a := by
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) f]

/-- Two tangents in the same replica slot retain their one-copy inner
product. -/
theorem finiteComplexInner_pureTensorTangentSlot_same
    {α : Type*} [Fintype α] (r : ℕ)
    (ψ u w : α → ℂ) (hψ : finiteComplexInner ψ ψ = 1)
    (a : Fin r) :
    finiteComplexInner (finitePureTensorTangentSlot r ψ u a)
      (finitePureTensorTangentSlot r ψ w a) =
        finiteComplexInner u w := by
  rw [finiteComplexInner]
  have hterm : ∀ x : Fin r → α,
      conj (finitePureTensorTangentSlot r ψ u a x) *
          finitePureTensorTangentSlot r ψ w a x =
        ∏ b, if b = a then conj (u (x b)) * w (x b)
          else conj (ψ (x b)) * ψ (x b) := by
    intro x
    simp only [finitePureTensorTangentSlot, map_prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro b hb
    by_cases hba : b = a
    · simp [hba]
    · simp [hba]
  rw [Finset.sum_congr rfl (fun x _ => hterm x),
    sum_pi_prod_complex (fun b z =>
      if b = a then conj (u z) * w z else conj (ψ z) * ψ z)]
  rw [Finset.prod_eq_single a]
  · simp [finiteComplexInner]
  · intro b hb hba
    simp only [if_neg hba]
    simpa [finiteComplexInner] using hψ
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

/-- If the first tangent is horizontal, tangents in distinct replica slots
are orthogonal. -/
theorem finiteComplexInner_pureTensorTangentSlot_ne
    {α : Type*} [Fintype α] (r : ℕ)
    (ψ u w : α → ℂ) (hψu : finiteComplexInner ψ u = 0)
    (a b : Fin r) (hab : a ≠ b) :
    finiteComplexInner (finitePureTensorTangentSlot r ψ u a)
      (finitePureTensorTangentSlot r ψ w b) = 0 := by
  rw [finiteComplexInner]
  have hterm : ∀ x : Fin r → α,
      conj (finitePureTensorTangentSlot r ψ u a x) *
          finitePureTensorTangentSlot r ψ w b x =
        ∏ i, conj (if i = a then u (x i) else ψ (x i)) *
          (if i = b then w (x i) else ψ (x i)) := by
    intro x
    simp only [finitePureTensorTangentSlot, map_prod]
    rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun x _ => hterm x),
    sum_pi_prod_complex (fun i z =>
      conj (if i = a then u z else ψ z) *
        (if i = b then w z else ψ z))]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp only [if_pos, if_neg hab]
  change finiteComplexInner u ψ = 0
  rw [finiteComplexInner_conj_symm, hψu, map_zero]

/-- Inner products distribute over two finite vector sums. -/
theorem finiteComplexInner_sum_sum
    {α A B : Type*} [Fintype α] [Fintype A] [Fintype B]
    (u : A → α → ℂ) (w : B → α → ℂ) :
    finiteComplexInner (fun x => ∑ a, u a x)
      (fun x => ∑ b, w b x) =
        ∑ a, ∑ b, finiteComplexInner (u a) (w b) := by
  unfold finiteComplexInner
  calc
    (∑ x : α, conj (∑ a, u a x) * (∑ b, w b x)) =
        ∑ x : α, ∑ a : A, ∑ b : B, conj (u a x) * w b x := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_comm
    _ = ∑ a : A, ∑ x : α, ∑ b : B, conj (u a x) * w b x :=
      Finset.sum_comm
    _ = ∑ a : A, ∑ b : B, ∑ x : α, conj (u a x) * w b x := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

/-- The horizontal `r`-copy tangent Gram is exactly `r` times the one-copy
tangent Gram. -/
theorem finiteComplexInner_pureTensorTangent
    {α : Type*} [Fintype α] (r : ℕ)
    (ψ u w : α → ℂ) (hψ : finiteComplexInner ψ ψ = 1)
    (hψu : finiteComplexInner ψ u = 0) :
    finiteComplexInner (finitePureTensorTangent r ψ u)
        (finitePureTensorTangent r ψ w) =
      (r : ℂ) * finiteComplexInner u w := by
  have hpair : ∀ a b : Fin r,
      finiteComplexInner (finitePureTensorTangentSlot r ψ u a)
          (finitePureTensorTangentSlot r ψ w b) =
        if a = b then finiteComplexInner u w else 0 := by
    intro a b
    by_cases hab : a = b
    · subst b
      rw [if_pos rfl]
      exact finiteComplexInner_pureTensorTangentSlot_same
        r ψ u w hψ a
    · rw [if_neg hab]
      exact finiteComplexInner_pureTensorTangentSlot_ne
        r ψ u w hψu a b hab
  unfold finitePureTensorTangent
  rw [finiteComplexInner_sum_sum]
  simp_rw [hpair]
  simp

/-- Horizontal representative of a one-copy projective tangent. -/
def finitePureStateHorizontalTangent
    {α : Type*} [Fintype α] (ψ u : α → ℂ) : α → ℂ :=
  fun x => u x - ψ x * finiteComplexInner ψ u

/-- Horizontalization is orthogonal to a normalized state. -/
theorem finiteComplexInner_horizontalTangent
    {α : Type*} [Fintype α] (ψ u : α → ℂ)
    (hψ : finiteComplexInner ψ ψ = 1) :
    finiteComplexInner ψ (finitePureStateHorizontalTangent ψ u) = 0 := by
  rw [finiteComplexInner]
  simp only [finitePureStateHorizontalTangent, mul_sub,
    Finset.sum_sub_distrib]
  rw [show
      (∑ x, conj (ψ x) * (ψ x * finiteComplexInner ψ u)) =
        (∑ x, conj (ψ x) * ψ x) * finiteComplexInner ψ u by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    ring]
  change finiteComplexInner ψ u -
    finiteComplexInner ψ ψ * finiteComplexInner ψ u = 0
  rw [hψ]
  ring

/-- Real projective/Fubini--Study Gram of selected one-copy tangent
directions. -/
def finitePureStateProjectiveGram
    {α : Type*} [Fintype α] {v : ℕ}
    (ψ : α → ℂ) (u : Fin v → α → ℂ) :
    Matrix (Fin v) (Fin v) ℝ :=
  fun i j => (finiteComplexInner
    (finitePureStateHorizontalTangent ψ (u i))
    (finitePureStateHorizontalTangent ψ (u j))).re

/-- Real projective/Fubini--Study Gram after `r` identical pure-state
replicas. -/
def finitePureStateReplicaProjectiveGram
    {α : Type*} [Fintype α] {v : ℕ} (r : ℕ)
    (ψ : α → ℂ) (u : Fin v → α → ℂ) :
    Matrix (Fin v) (Fin v) ℝ :=
  fun i j => (finiteComplexInner
    (finitePureTensorTangent r ψ
      (finitePureStateHorizontalTangent ψ (u i)))
    (finitePureTensorTangent r ψ
      (finitePureStateHorizontalTangent ψ (u j)))).re

/-- **Pure-state replica projective-Gram law.**  The pullback projective
metric of `r` identical copies is exactly `r` times the one-copy metric. -/
theorem finitePureStateReplicaProjectiveGram_eq_smul
    {α : Type*} [Fintype α] {v : ℕ} (r : ℕ)
    (ψ : α → ℂ) (u : Fin v → α → ℂ)
    (hψ : finiteComplexInner ψ ψ = 1) :
    finitePureStateReplicaProjectiveGram r ψ u =
      (r : ℝ) • finitePureStateProjectiveGram ψ u := by
  ext i j
  change (finiteComplexInner
      (finitePureTensorTangent r ψ
        (finitePureStateHorizontalTangent ψ (u i)))
      (finitePureTensorTangent r ψ
        (finitePureStateHorizontalTangent ψ (u j)))).re =
    (r : ℝ) *
      (finiteComplexInner
        (finitePureStateHorizontalTangent ψ (u i))
        (finitePureStateHorizontalTangent ψ (u j))).re
  rw [finiteComplexInner_pureTensorTangent r ψ _ _ hψ
    (finiteComplexInner_horizontalTangent ψ (u i) hψ)]
  simp

/-- A rank-`v` projective-Gram determinant acquires exactly the deterministic
factor `r^v`. -/
theorem det_finitePureStateReplicaProjectiveGram
    {α : Type*} [Fintype α] {v : ℕ} (r : ℕ)
    (ψ : α → ℂ) (u : Fin v → α → ℂ)
    (hψ : finiteComplexInner ψ ψ = 1) :
    (finitePureStateReplicaProjectiveGram r ψ u).det =
      (r : ℝ) ^ v * (finitePureStateProjectiveGram ψ u).det := by
  rw [finitePureStateReplicaProjectiveGram_eq_smul r ψ u hψ,
    Matrix.det_smul]
  simp

/-- The complex overlap of two tensor powers is the corresponding power of
the one-copy overlap. -/
theorem finiteComplexInner_pureTensorPower
    {α : Type*} [Fintype α] (r : ℕ) (ψ φ : α → ℂ) :
    finiteComplexInner (finitePureTensorPower r ψ)
        (finitePureTensorPower r φ) =
      finiteComplexInner ψ φ ^ r := by
  rw [finiteComplexInner]
  have hterm : ∀ x : Fin r → α,
      conj (finitePureTensorPower r ψ x) *
          finitePureTensorPower r φ x =
        ∏ i, conj (ψ (x i)) * φ (x i) := by
    intro x
    simp only [finitePureTensorPower, map_prod]
    rw [← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun x _ => hterm x),
    sum_pi_prod_complex (fun _ z => conj (ψ z) * φ z)]
  simp [finiteComplexInner]

/-- Squared pure-state fidelity in finite coordinates. -/
def finitePureStateFidelity
    {α : Type*} [Fintype α] (ψ φ : α → ℂ) : ℝ :=
  ‖finiteComplexInner ψ φ‖ ^ (2 : ℕ)

/-- Fidelity of `r` identical pure-state copies is the `r`th power of
one-copy fidelity. -/
theorem finitePureStateFidelity_tensorPower
    {α : Type*} [Fintype α] (r : ℕ) (ψ φ : α → ℂ) :
    finitePureStateFidelity (finitePureTensorPower r ψ)
        (finitePureTensorPower r φ) =
      finitePureStateFidelity ψ φ ^ r := by
  rw [finitePureStateFidelity, finiteComplexInner_pureTensorPower,
    norm_pow, finitePureStateFidelity]
  rw [← pow_mul]
  ring

/-- **Matched pure-state tube compensation.**  The complete target union for
`r` tensor copies, with its fidelity threshold raised to `r`, is exactly the
one-copy complete target union. -/
theorem completePureStateTargetUnion_tensorPower_set_eq
    {X C α : Type*} [Fintype α] {r : ℕ} (hr : r ≠ 0)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (state : X → α → ℂ) (target : C → α → ℂ) :
    {x | ∃ c,
      threshold ^ r ≤
        finitePureStateFidelity (finitePureTensorPower r (state x))
          (finitePureTensorPower r (target c))} =
      {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  ext x
  simp only [finitePureStateFidelity_tensorPower]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (pow_le_pow_iff_left₀ hthreshold (sq_nonneg _) hr).mp hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (pow_le_pow_iff_left₀ hthreshold (sq_nonneg _) hr).mpr hc⟩

/-- Under every parameter law, the matched complete pure-state replica tube
has exactly its one-copy probability. -/
theorem measure_completePureStateTargetUnion_tensorPower
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    {r : ℕ} (hr : r ≠ 0) (μ : Measure X)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold)
    (state : X → α → ℂ) (target : C → α → ℂ) :
    μ {x | ∃ c,
      threshold ^ r ≤
        finitePureStateFidelity (finitePureTensorPower r (state x))
          (finitePureTensorPower r (target c))} =
      μ {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  rw [completePureStateTargetUnion_tensorPower_set_eq hr threshold
    hthreshold state target]

/-- Exact lower-tail invariance for the physical pure-state replica
projective Gram. -/
theorem measure_det_finitePureStateReplicaProjectiveGram_le_scaled
    {X α : Type*} [MeasurableSpace X] [Fintype α] {v : ℕ}
    (μ : Measure X) (r : ℕ) (hr : 0 < r)
    (state : X → α → ℂ) (tangent : X → Fin v → α → ℂ)
    (hstate : ∀ x, finiteComplexInner (state x) (state x) = 1)
    (τ : ℝ) :
    μ {x |
      (finitePureStateReplicaProjectiveGram r (state x) (tangent x)).det ≤
        (r : ℝ) ^ v * τ} =
      μ {x |
        (finitePureStateProjectiveGram (state x) (tangent x)).det ≤ τ} := by
  congr 1
  ext x
  change
    (finitePureStateReplicaProjectiveGram r (state x) (tangent x)).det ≤
        (r : ℝ) ^ v * τ ↔
      (finitePureStateProjectiveGram (state x) (tangent x)).det ≤ τ
  rw [det_finitePureStateReplicaProjectiveGram r (state x) (tangent x)
    (hstate x)]
  exact mul_le_mul_iff_of_pos_left (by positivity : 0 < (r : ℝ) ^ v)

/-- **Pure-state replica compensation capstone.**  At every positive replica
order, the projective-Gram determinant gains exactly `r^v`, its normalized
lower-tail probability is unchanged, and the matched complete target tube is
the one-copy event. -/
theorem finitePureState_replicaObserverJacobian_compensationLaw
    {X C α : Type*} [MeasurableSpace X] [Fintype α] {v : ℕ}
    (μ : Measure X) (r : ℕ) (hr : 0 < r)
    (state : X → α → ℂ) (tangent : X → Fin v → α → ℂ)
    (hstate : ∀ x, finiteComplexInner (state x) (state x) = 1)
    (target : C → α → ℂ) (τ threshold : ℝ)
    (hthreshold : 0 ≤ threshold) :
    (∀ x,
      (finitePureStateReplicaProjectiveGram r
        (state x) (tangent x)).det =
          (r : ℝ) ^ v *
            (finitePureStateProjectiveGram
              (state x) (tangent x)).det) ∧
    μ {x |
      (finitePureStateReplicaProjectiveGram r
        (state x) (tangent x)).det ≤ (r : ℝ) ^ v * τ} =
      μ {x |
        (finitePureStateProjectiveGram
          (state x) (tangent x)).det ≤ τ} ∧
    μ {x | ∃ c,
      threshold ^ r ≤
        finitePureStateFidelity (finitePureTensorPower r (state x))
          (finitePureTensorPower r (target c))} =
      μ {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  refine ⟨fun x => det_finitePureStateReplicaProjectiveGram
      r (state x) (tangent x) (hstate x),
    measure_det_finitePureStateReplicaProjectiveGram_le_scaled
      μ r hr state tangent hstate τ, ?_⟩
  exact measure_completePureStateTargetUnion_tensorPower
    hr.ne' μ threshold hthreshold state target

end

end GaloisForLFunctions.HTGeometry
