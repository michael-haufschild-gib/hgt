import Mathlib

/-!
# The critical multiple of a second-order term

Along the critical curve a degenerating family, rescaled by its margin, converges to `J + K X`:
the limiting polarization `J` plus the multiple `K` of a second-order term `X`. This file is the
finite-dimensional calculus of that limit.

* **Admissible multiples** (`admissible_of_le`, `isClosed_admissible`): for `J ⪰ 0` the set of
  `K ≥ 0` with `J + K X ⪰ 0` is a closed initial segment of `[0, ∞)`.
* **Positive second-order terms** (`admissible_of_nonneg`, `admissible_mono`): a positive
  semidefinite `X` admits every multiple, and adding a positive semidefinite term to `X` never
  removes a multiple.
* **Persistence** (`neg_persists`): a negative direction at the multiple `K` is negative at every
  larger multiple.
* **Second-order dichotomy** (`eventually_pos_of_tendsto`, `eventually_not_nonneg_of_tendsto`):
  if the rescaled family converges entrywise to `J + K X`, positive definiteness of the limit is
  inherited by the family, and a negative direction of the limit is eventually a negative
  direction of the family.

The quadratic forms are written as `qform Q v = Σ_{i,j} v_i v_j Q_{ij}` on a finite index type.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

variable {ι : Type*} [Fintype ι]

/-- The quadratic form `Σ_{i,j} v_i v_j Q_{ij}`. -/
def qform (Q : ι → ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, ∑ j, v i * v j * Q i j

/-- Nonnegativity of a quadratic form. -/
def QNonneg (Q : ι → ι → ℝ) : Prop := ∀ v, 0 ≤ qform Q v

/-- The admissible multiples `{K ≥ 0 : J + K X ⪰ 0}`. -/
def admissible (J X : ι → ι → ℝ) : Set ℝ := {K | 0 ≤ K ∧ QNonneg (fun i j => J i j + K * X i j)}

theorem qform_add_smul (J X : ι → ι → ℝ) (K : ℝ) (v : ι → ℝ) :
    qform (fun i j => J i j + K * X i j) v = qform J v + K * qform X v := by
  simp only [qform, mul_add, sum_add_distrib, mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem continuous_qform (v : ι → ℝ) : Continuous fun Q : ι → ι → ℝ => qform Q v := by
  unfold qform; fun_prop

/-- The admissible multiples form an initial segment of `[0, ∞)`. -/
theorem admissible_of_le {J X : ι → ι → ℝ} (hJ : QNonneg J) {K K' : ℝ} (hK : K ∈ admissible J X)
    (hK'0 : 0 ≤ K') (hK' : K' ≤ K) : K' ∈ admissible J X := by
  refine ⟨hK'0, fun v => ?_⟩
  have h1 := hK.2 v
  rw [qform_add_smul] at h1 ⊢
  have hJv := hJ v
  rcases eq_or_lt_of_le hK'0 with h0 | hpos
  · rw [← h0, zero_mul, add_zero]; exact hJv
  · -- `J + K' X = (1 − t) J + t (J + K X)` with `t = K'/K`
    have hKpos : 0 < K := lt_of_lt_of_le hpos hK'
    have ht0 : 0 ≤ K' / K := div_nonneg hK'0 hKpos.le
    have ht1 : K' / K ≤ 1 := (div_le_one hKpos).mpr hK'
    have hcomb : qform J v + K' * qform X v =
        (1 - K' / K) * qform J v + K' / K * (qform J v + K * qform X v) := by
      field_simp; ring
    rw [hcomb]
    exact add_nonneg (mul_nonneg (by linarith) hJv) (mul_nonneg ht0 h1)

/-- The admissible multiples form a closed set. -/
theorem isClosed_admissible (J X : ι → ι → ℝ) : IsClosed (admissible J X) := by
  have : admissible J X = Set.Ici 0 ∩ ⋂ v : ι → ℝ, {K : ℝ | 0 ≤ qform J v + K * qform X v} := by
    ext K
    simp only [admissible, QNonneg, qform_add_smul, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_Ici, Set.mem_iInter]
  rw [this]
  exact isClosed_Ici.inter (isClosed_iInter fun v =>
    isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const)))

/-- A positive semidefinite second-order term admits every multiple. -/
theorem admissible_of_nonneg {J X : ι → ι → ℝ} (hJ : QNonneg J) (hX : QNonneg X) {K : ℝ}
    (hK : 0 ≤ K) : K ∈ admissible J X :=
  ⟨hK, fun v => by rw [qform_add_smul]; exact add_nonneg (hJ v) (mul_nonneg hK (hX v))⟩

theorem qform_add (P Q : ι → ι → ℝ) (v : ι → ℝ) :
    qform (fun i j => P i j + Q i j) v = qform P v + qform Q v := by
  simp only [qform, mul_add, sum_add_distrib]

/-- Adding a positive semidefinite term to the second-order term never removes a multiple. -/
theorem admissible_mono {J X P : ι → ι → ℝ} (hP : QNonneg P) :
    admissible J X ⊆ admissible J (fun i j => X i j + P i j) := by
  intro K hK
  refine ⟨hK.1, fun v => ?_⟩
  have h := hK.2 v
  rw [qform_add_smul] at h ⊢
  rw [qform_add]
  nlinarith [hP v, hK.1]

/-- **Negative directions persist.** Over a positive semidefinite polarization, a direction that is
negative at the multiple `K` stays negative at every larger multiple: the negative index of
`J + K X` is nondecreasing in `K`. -/
theorem neg_persists {J X : ι → ι → ℝ} (hJ : QNonneg J) {K K' : ℝ} (hK : 0 < K) (hKK' : K ≤ K')
    {v : ι → ℝ} (hv : qform (fun i j => J i j + K * X i j) v < 0) :
    qform (fun i j => J i j + K' * X i j) v < 0 := by
  rw [qform_add_smul] at hv ⊢
  have hX : qform X v < 0 := by
    by_contra h
    push Not at h
    nlinarith [hJ v]
  nlinarith

/-- Entrywise convergence of forms gives convergence of every quadratic value. -/
theorem tendsto_qform {α : Type*} {l : Filter α} {A : α → ι → ι → ℝ} {L : ι → ι → ℝ}
    (hA : ∀ i j, Tendsto (fun a => A a i j) l (𝓝 (L i j))) (v : ι → ℝ) :
    Tendsto (fun a => qform (A a) v) l (𝓝 (qform L v)) := by
  unfold qform
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (hA i j).const_mul (v i * v j)

/-- **Second-order dichotomy, failure half.** A negative direction of the limit is eventually a
negative direction of the family. -/
theorem eventually_not_nonneg_of_tendsto {α : Type*} {l : Filter α} {A : α → ι → ι → ℝ}
    {L : ι → ι → ℝ} (hA : ∀ i j, Tendsto (fun a => A a i j) l (𝓝 (L i j))) {v : ι → ℝ}
    (hv : qform L v < 0) : ∀ᶠ a in l, qform (A a) v < 0 :=
  (tendsto_qform hA v).eventually (gt_mem_nhds hv)

/-- `|qform P v − qform Q v| ≤ Σ |P − Q|` on the unit sup-sphere. -/
theorem abs_qform_sub_le {P Q : ι → ι → ℝ} {v : ι → ℝ} (hv : ‖v‖ ≤ 1) :
    |qform P v - qform Q v| ≤ ∑ i, ∑ j, |P i j - Q i j| := by
  unfold qform
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hi : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
  have hj : |v j| ≤ 1 := (norm_le_pi_norm v j).trans hv
  rw [← mul_sub, abs_mul, abs_mul]
  have : |v i| * |v j| ≤ 1 := by nlinarith [abs_nonneg (v i), abs_nonneg (v j)]
  nlinarith [abs_nonneg (P i j - Q i j), abs_nonneg (v i), abs_nonneg (v j)]

theorem qform_smul (Q : ι → ι → ℝ) (t : ℝ) (v : ι → ℝ) : qform Q (t • v) = t ^ 2 * qform Q v := by
  simp only [qform, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

/-- **Second-order dichotomy, inheritance half.** If the limit is positive definite, the family is
eventually positive definite. -/
theorem eventually_pos_of_tendsto {α : Type*} {l : Filter α} {A : α → ι → ι → ℝ}
    {L : ι → ι → ℝ} (hA : ∀ i j, Tendsto (fun a => A a i j) l (𝓝 (L i j)))
    (hL : ∀ v, v ≠ 0 → 0 < qform L v) : ∀ᶠ a in l, ∀ v, v ≠ 0 → 0 < qform (A a) v := by
  by_cases hι : IsEmpty ι
  · exact Eventually.of_forall fun a v hv => absurd (funext fun i => (hι.false i).elim) hv
  rw [not_isEmpty_iff] at hι
  -- the minimum of the limit on the unit sphere
  have hcpt : IsCompact (Metric.sphere (0 : ι → ℝ) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty := by
    classical
    obtain ⟨i⟩ := hι
    refine ⟨Pi.single i 1, ?_⟩
    rw [mem_sphere_zero_iff_norm, Pi.norm_single, norm_one]
  obtain ⟨v₀, hv₀, hmin⟩ := hcpt.exists_isMinOn hne (continuous_qform_left L).continuousOn
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hv₀; exact zero_ne_one hv₀
  set δ := qform L v₀ with hδ
  have hδpos : 0 < δ := hL v₀ hv₀ne
  -- eventually the entrywise error is below `δ`
  have herr : Tendsto (fun a => ∑ i, ∑ j, |A a i j - L i j|) l (𝓝 0) := by
    have := tendsto_finsetSum (univ : Finset ι) fun i _ =>
      tendsto_finsetSum (univ : Finset ι) fun j _ => ((hA i j).sub_const (L i j)).abs
    simpa using this
  filter_upwards [herr.eventually (gt_mem_nhds hδpos)] with a ha v hv
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set u := ‖v‖⁻¹ • v with hu
  have hu1 : ‖u‖ = 1 := by rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne']
  have hLu : δ ≤ qform L u := hmin (mem_sphere_zero_iff_norm.mpr hu1)
  have hdiff := abs_qform_sub_le (P := A a) (Q := L) hu1.le
  have hAu : 0 < qform (A a) u := by
    have := (abs_le.mp hdiff).1
    linarith
  have hv' : v = ‖v‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hnv.ne', one_smul]
  rw [hv', qform_smul]
  exact mul_pos (pow_pos hnv 2) hAu
where
  continuous_qform_left (L : ι → ι → ℝ) : Continuous fun v : ι → ℝ => qform L v := by
    unfold qform; fun_prop

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
