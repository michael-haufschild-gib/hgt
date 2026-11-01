import GaloisForLFunctions.ArithmeticLorentzianGeometry.LorentzianFormsAtDegreeTwo

/-!
# The Kähler package of a quadratic form

A **Kähler package** is a real symmetric form `W` on a finite index set together with a class `v`.
Primitive vectors are those with `x ⬝ᵥ v = 0`. In Weil's sign convention:

* **Hodge–Riemann** (`HodgeRiemann W v`): `W ≥ 0` on primitive vectors;
* **strict Hodge–Riemann** (`StrictHodgeRiemann W v`): `W > 0` on nonzero primitive vectors;
* **hard Lefschetz** (`HardLefschetz W v`): `W` is nondegenerate on the primitive part.

The two mechanisms by which Hodge–Riemann relations are proved without a variety are formal:

* **Strictness** (`strictHodgeRiemann_iff`): HR together with HL is strict HR. A vector of zero
  energy for a semidefinite form lies in its radical, and HL kills the radical.
* **Transport** (`hodgeRiemann_transport`): along a continuous family over a preconnected
  parameter space, HR at one point propagates to every point as soon as HL holds wherever HR holds.
  The HR locus is closed; on it HL makes it the strict HR locus, which is open by compactness of the
  primitive unit sphere. HL is needed only on the HR locus: this is the Liouville form of hard
  Lefschetz. The contrapositive (`exists_crossing_of_hodgeRiemann_of_not`) says that a family
  which loses HR has a parameter where HR holds and HL fails: a zero mode on the primitive part.

Hodge–Riemann is the Hodge index: `W ≥ 0` on a hyperplane means `−W` has at most one positive
square (`isHyperbolic_neg_of_hodgeRiemann`).
-/

noncomputable section

open Matrix Filter Topology Set
open GaloisForLFunctions.ArithmeticLorentzianGeometry

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

variable {ι : Type*} [Fintype ι]

/-- **Hodge–Riemann**: `W ≥ 0` on the primitive part `v^⊥`. -/
def HodgeRiemann (W : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, x ⬝ᵥ v = 0 → 0 ≤ qf W x

/-- **Strict Hodge–Riemann**: `W > 0` on nonzero primitive vectors. -/
def StrictHodgeRiemann (W : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, x ⬝ᵥ v = 0 → x ≠ 0 → 0 < qf W x

/-- **Hard Lefschetz**: the form is nondegenerate on the primitive part. -/
def HardLefschetz (W : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, x ⬝ᵥ v = 0 → (∀ y : ι → ℝ, y ⬝ᵥ v = 0 → bil W x y = 0) → x = 0

theorem StrictHodgeRiemann.hodgeRiemann {W : Matrix ι ι ℝ} {v : ι → ℝ}
    (h : StrictHodgeRiemann W v) : HodgeRiemann W v := by
  intro x hx
  by_cases h0 : x = 0
  · simp [h0, qf, bil]
  · exact (h x hx h0).le

/-- A primitive vector of zero energy for a form that is `≥ 0` on the primitive part pairs to zero
with every primitive vector. -/
theorem bil_eq_zero_of_hodgeRiemann {W : Matrix ι ι ℝ} (hW : W.IsSymm) {v : ι → ℝ}
    (h : HodgeRiemann W v) {x : ι → ℝ} (hx : x ⬝ᵥ v = 0) (hq : qf W x = 0) {y : ι → ℝ}
    (hy : y ⬝ᵥ v = 0) : bil W x y = 0 := by
  have hprim : ∀ t : ℝ, ((1 : ℝ) • x + t • y) ⬝ᵥ v = 0 := fun t => by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, hx, hy]; simp
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * bil W x y + t ^ 2 * qf W y := fun t => by
    have := h _ (hprim t)
    rw [qf_add_smul hW, hq] at this
    linarith
  by_contra hb
  have hqy := h y hy
  set b := bil W x y
  set a := qf W y
  -- Choose `t` with `2tb + t²a < 0`.
  have hb2 : 0 < b ^ 2 := by positivity
  rcases eq_or_lt_of_le hqy with ha | ha
  · have := hquad (-b)
    rw [← ha] at this
    nlinarith
  · have := hquad (-b / a)
    have hval : 2 * (-b / a) * b + (-b / a) ^ 2 * a = -(b ^ 2 / a) := by
      field_simp; ring
    rw [hval] at this
    have : 0 < b ^ 2 / a := div_pos hb2 ha
    linarith

/-- **Strictness.** Hodge–Riemann with hard Lefschetz is strict Hodge–Riemann. -/
theorem strictHodgeRiemann_iff {W : Matrix ι ι ℝ} (hW : W.IsSymm) {v : ι → ℝ} :
    StrictHodgeRiemann W v ↔ HodgeRiemann W v ∧ HardLefschetz W v := by
  refine ⟨fun h => ⟨h.hodgeRiemann, fun x hx hrad => ?_⟩, fun ⟨h, hL⟩ x hx hx0 => ?_⟩
  · by_contra hx0
    have := h x hx hx0
    rw [qf, hrad x hx] at this
    exact lt_irrefl 0 this
  · rcases eq_or_lt_of_le (h x hx) with hq | hq
    · exact absurd (hL x hx fun y hy => bil_eq_zero_of_hodgeRiemann hW h hx hq.symm hy) hx0
    · exact hq

/-- Hodge–Riemann on a hyperplane is the Hodge index: `−W` has at most one positive square. -/
theorem isHyperbolic_neg_of_hodgeRiemann {W : Matrix ι ι ℝ} (hW : W.IsSymm) {v : ι → ℝ}
    (h : HodgeRiemann W v) : IsHyperbolic (-W) := by
  refine isHyperbolic_of_nonpos_on_ker (by rw [Matrix.IsSymm, transpose_neg, hW.eq]) (dotLeft v)
    fun z hz => ?_
  have hz' : z ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hz
  have := h z hz'
  simp only [qf, bil, neg_mulVec, dotProduct_neg] at this ⊢
  linarith

/-! ### Transport along connected families -/

section Transport

variable {X : Type*} [TopologicalSpace X]

/-- The energy `(t, x) ↦ W(t)[x]` of a continuous family is jointly continuous. -/
theorem continuous_qf_family {W : X → Matrix ι ι ℝ} (hW : Continuous W) :
    Continuous fun p : X × (ι → ℝ) => qf (W p.1) p.2 :=
  Continuous.dotProduct continuous_snd
    (Continuous.matrix_mulVec (hW.comp continuous_fst) continuous_snd)

/-- The Hodge–Riemann locus of a continuous family is closed. -/
theorem isClosed_setOf_hodgeRiemann {W : X → Matrix ι ι ℝ} (hW : Continuous W) (v : ι → ℝ) :
    IsClosed {t | HodgeRiemann (W t) v} := by
  have : {t | HodgeRiemann (W t) v} = ⋂ x ∈ {x : ι → ℝ | x ⬝ᵥ v = 0}, {t | 0 ≤ qf (W t) x} := by
    ext t; simp [HodgeRiemann]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_le continuous_const
    ((continuous_qf_family hW).comp (Continuous.prodMk_left x))

/-- The primitive unit sphere is compact. -/
theorem isCompact_primitiveSphere (v : ι → ℝ) :
    IsCompact {x : ι → ℝ | x ⬝ᵥ v = 0 ∧ x ⬝ᵥ x = 1} := by
  classical
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_eq (continuous_id.dotProduct continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.dotProduct continuous_id) continuous_const)
  · refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨1, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hsq : x i ^ 2 ≤ x ⬝ᵥ x := by
      rw [dotProduct, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have : 0 ≤ ∑ j ∈ Finset.univ.erase i, x j * x j :=
        Finset.sum_nonneg fun j _ => mul_self_nonneg _
      nlinarith
    rw [hx.2] at hsq
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- The strict Hodge–Riemann locus of a continuous family is open. -/
theorem isOpen_setOf_strictHodgeRiemann {W : X → Matrix ι ι ℝ} (hW : Continuous W) (v : ι → ℝ) :
    IsOpen {t | StrictHodgeRiemann (W t) v} := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro t₀ ht₀
  have hpos : ∀ y ∈ {x : ι → ℝ | x ⬝ᵥ v = 0 ∧ x ⬝ᵥ x = 1},
      ∀ᶠ z : X × (ι → ℝ) in 𝓝 (t₀, y), 0 < qf (W z.1) z.2 := by
    intro y hy
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy; simpa using hy.2
    exact (continuous_qf_family hW).continuousAt.eventually
      (lt_mem_nhds (ht₀ y hy.1 hy0))
  have hev := IsCompact.eventually_forall_of_forall_eventually (X := X) (x₀ := t₀)
    (P := fun t x => 0 < qf (W t) x) (isCompact_primitiveSphere v) hpos
  filter_upwards [hev] with t ht x hx hx0
  have hn : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne (Finset.sum_nonneg fun j _ => mul_self_nonneg (x j))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hx0))
  set s := (Real.sqrt (x ⬝ᵥ x))⁻¹
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr hn)
  have hsx : s • x ∈ {x : ι → ℝ | x ⬝ᵥ v = 0 ∧ x ⬝ᵥ x = 1} := by
    refine ⟨by rw [smul_dotProduct, hx, smul_zero], ?_⟩
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq,
      inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']
  have := ht _ hsx
  have hscale : qf (W t) (s • x) = s ^ 2 * qf (W t) x := by
    simp only [qf, bil_smul_left, bil_smul_right]; ring
  rw [hscale] at this
  exact pos_of_mul_pos_right this (by positivity)

/-- **Transport of Hodge–Riemann.** On a preconnected parameter space, a continuous family with
Hodge–Riemann at one point and hard Lefschetz on its Hodge–Riemann locus satisfies Hodge–Riemann
everywhere. -/
theorem hodgeRiemann_transport [PreconnectedSpace X] {W : X → Matrix ι ι ℝ}
    (hW : Continuous W) (hsymm : ∀ t, (W t).IsSymm) (v : ι → ℝ)
    (hL : ∀ t, HodgeRiemann (W t) v → HardLefschetz (W t) v) {t₀ : X}
    (h₀ : HodgeRiemann (W t₀) v) (t : X) : HodgeRiemann (W t) v := by
  have heq : {t | HodgeRiemann (W t) v} = {t | StrictHodgeRiemann (W t) v} := by
    ext s
    exact ⟨fun h => (strictHodgeRiemann_iff (hsymm s)).mpr ⟨h, hL s h⟩,
      StrictHodgeRiemann.hodgeRiemann⟩
  have hclopen : IsClopen {t | HodgeRiemann (W t) v} :=
    ⟨isClosed_setOf_hodgeRiemann hW v, heq ▸ isOpen_setOf_strictHodgeRiemann hW v⟩
  have := hclopen.eq_univ ⟨t₀, h₀⟩
  rw [Set.eq_univ_iff_forall] at this
  exact this t

/-- **Transport on a preconnected set** of parameters. -/
theorem hodgeRiemann_transport_on {S : Set X} (hS : IsPreconnected S) {W : X → Matrix ι ι ℝ}
    (hW : ContinuousOn W S) (hsymm : ∀ t ∈ S, (W t).IsSymm) (v : ι → ℝ)
    (hL : ∀ t ∈ S, HodgeRiemann (W t) v → HardLefschetz (W t) v) {t₀ : X} (ht₀ : t₀ ∈ S)
    (h₀ : HodgeRiemann (W t₀) v) {t : X} (ht : t ∈ S) : HodgeRiemann (W t) v := by
  haveI := isPreconnected_iff_preconnectedSpace.mp hS
  exact hodgeRiemann_transport (W := fun s : S => W s) hW.restrict (fun s => hsymm s s.2) v
    (fun s => hL s s.2) (t₀ := ⟨t₀, ht₀⟩) h₀ ⟨t, ht⟩

/-- **A failure of Hodge–Riemann is a crossing.** If a continuous family over a preconnected set
has Hodge–Riemann at one parameter and not at another, some parameter has Hodge–Riemann without
hard Lefschetz: a nonzero primitive vector of zero energy in the radical of the primitive form. -/
theorem exists_crossing_of_hodgeRiemann_of_not {S : Set X} (hS : IsPreconnected S)
    {W : X → Matrix ι ι ℝ} (hW : ContinuousOn W S) (hsymm : ∀ t ∈ S, (W t).IsSymm)
    (v : ι → ℝ) {t₀ t₁ : X} (ht₀ : t₀ ∈ S) (ht₁ : t₁ ∈ S) (h₀ : HodgeRiemann (W t₀) v)
    (h₁ : ¬ HodgeRiemann (W t₁) v) :
    ∃ t ∈ S, HodgeRiemann (W t) v ∧ ¬ HardLefschetz (W t) v := by
  by_contra hno
  push Not at hno
  exact h₁ (hodgeRiemann_transport_on hS hW hsymm v hno ht₀ h₀ ht₁)

end Transport

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
