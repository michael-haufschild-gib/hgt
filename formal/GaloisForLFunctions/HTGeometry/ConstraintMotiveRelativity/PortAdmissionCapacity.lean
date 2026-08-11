import Mathlib

/-!
# Capacity is admission

A coefficient family `c : P → ℂ` defines an algebraic port on finitely supported source vectors,
`λ(l) = ∑ c p · l p`.  Realized in `ℓ²(P)` its total capacity is `C₀ = ∑ ‖c p‖²`.  The port
extends to a continuous functional on `ℓ²(P)` exactly when `C₀ < ∞`, and then the functional norm
squared is `C₀`.  When `C₀ = ∞` the algebraic kernel is dense, so Hausdorff reduction of the port
vanishes.
-/

open scoped ComplexConjugate

namespace HTGeometry.ConstraintMotiveRelativity

section Admission

variable {P : Type*} [DecidableEq P]

/-- The source Hilbert chart. -/
abbrev SourceL2 (P : Type*) : Type _ := lp (fun _ : P => ℂ) 2

/-- The coordinate vectors of the source chart. -/
noncomputable def srcBasis (p : P) : SourceL2 P := lp.single 2 p (1 : ℂ)

/-- Finitely supported source vectors. -/
noncomputable def srcEmb : (P →₀ ℂ) →ₗ[ℂ] SourceL2 P :=
  Finsupp.linearCombination ℂ srcBasis

theorem srcEmb_single (p : P) (t : ℂ) : srcEmb (Finsupp.single p t) = t • srcBasis p := by
  simp [srcEmb]

theorem srcBasis_apply (i j : P) : (srcBasis j : P → ℂ) i = if i = j then 1 else 0 := by
  rw [srcBasis, lp.single_apply]
  simp [Pi.single_apply]

theorem srcEmb_apply (l : P →₀ ℂ) (i : P) : (srcEmb l : P → ℂ) i = l i := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single p t =>
      rw [srcEmb_single]
      by_cases h : i = p
      · subst h
        simp [srcBasis_apply]
      · simp [srcBasis_apply, h]

end Admission

end HTGeometry.ConstraintMotiveRelativity

namespace HTGeometry.ConstraintMotiveRelativity

section AdmissionLaw

variable {P : Type*} [DecidableEq P]

omit [DecidableEq P] in
/-- Square-summability is membership in the source chart. -/
theorem memℓp_two_iff {f : P → ℂ} : Memℓp f 2 ↔ Summable (fun p => ‖f p‖ ^ 2) := by
  rw [memℓp_gen_iff (p := 2) (by norm_num)]
  norm_num [Real.rpow_natCast]

omit [DecidableEq P] in
/-- The squared chart norm is the total coordinate mass. -/
theorem norm_sq_eq_tsum (f : SourceL2 P) : ‖f‖ ^ 2 = ∑' p, ‖(f : P → ℂ) p‖ ^ 2 := by
  have h := lp.norm_eq_tsum_rpow (p := 2) (by norm_num) f
  have h2 : ∀ p : P, ‖(f : P → ℂ) p‖ ^ ((2 : ENNReal).toReal) = ‖(f : P → ℂ) p‖ ^ 2 := by
    intro p; norm_num [Real.rpow_natCast]
  rw [h, tsum_congr h2]
  have hnn : 0 ≤ ∑' p, ‖(f : P → ℂ) p‖ ^ 2 := tsum_nonneg fun p => by positivity
  norm_num
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn]
  norm_num

/-- The algebraic port `(CA.2)` on finitely supported source vectors. -/
noncomputable def portLin (c : P → ℂ) : (P →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ c

omit [DecidableEq P] in
theorem portLin_single (c : P → ℂ) (p : P) (t : ℂ) :
    portLin c (Finsupp.single p t) = t * c p := by
  simp [portLin]

theorem srcEmb_eq_sum (l : P →₀ ℂ) : srcEmb l = ∑ p ∈ l.support, lp.single 2 p (l p) := by
  rw [srcEmb, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [srcBasis, ← lp.single_smul]
  simp

/-- The chart norm of a finitely supported vector is its coordinate mass. -/
theorem norm_srcEmb_sq (l : P →₀ ℂ) : ‖srcEmb l‖ ^ 2 = ∑ p ∈ l.support, ‖l p‖ ^ 2 := by
  have h := lp.norm_sum_single (p := 2) (E := fun _ : P => ℂ) (by norm_num) (fun p => l p)
    l.support
  rw [srcEmb_eq_sum]
  have h2 : ∀ p ∈ l.support, ‖l p‖ ^ ((2 : ENNReal).toReal) = ‖l p‖ ^ 2 := by
    intro p _; norm_num [Real.rpow_natCast]
  rw [Finset.sum_congr rfl h2] at h
  rw [← h]
  norm_num [Real.rpow_natCast]

/-- The algebraic constraint of the port, realized inside the source chart. -/
noncomputable def portKer (c : P → ℂ) : Submodule ℂ (SourceL2 P) :=
  Submodule.map srcEmb (LinearMap.ker (portLin c))

theorem mem_portKer_of_ker {c : P → ℂ} {l : P →₀ ℂ} (hl : portLin c l = 0) :
    srcEmb l ∈ portKer c := ⟨l, hl, rfl⟩

/-! ### Capacity is admission -/

/-- **Continuous admission forces finite capacity.**  Testing a continuous extension against the
capacity-optimal apertures bounds every finite capacity by the squared functional norm. -/
theorem summable_of_continuous_port (c : P → ℂ) (L : SourceL2 P →L[ℂ] ℂ)
    (hL : ∀ l : P →₀ ℂ, L (srcEmb l) = portLin c l) :
    Summable (fun p => ‖c p‖ ^ 2) := by
  classical
  refine summable_of_sum_le (fun p => by positivity) (c := ‖L‖ ^ 2) fun F => ?_
  set l : P →₀ ℂ := ∑ p ∈ F, Finsupp.single p (starRingEnd ℂ (c p)) with hl
  have hlapp : ∀ q : P, l q = if q ∈ F then starRingEnd ℂ (c q) else 0 := by
    intro q
    rw [hl, Finsupp.finsetSum_apply]
    by_cases hq : q ∈ F
    · rw [Finset.sum_eq_single q]
      · simp [hq]
      · intro b _ hb
        simp [Ne.symm hb]
      · intro h; exact absurd hq h
    · rw [if_neg hq]
      refine Finset.sum_eq_zero fun b hb => ?_
      have : q ≠ b := fun h => hq (h ▸ hb)
      simp [this]
  have hsupp : l.support ⊆ F := by
    intro q hq
    by_contra hqF
    exact (Finsupp.mem_support_iff.1 hq) (by rw [hlapp q, if_neg hqF])
  have hval : portLin c l = ((∑ p ∈ F, ‖c p‖ ^ 2 : ℝ) : ℂ) := by
    rw [portLin, Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset l hsupp _
      (fun p _ => by simp)]
    push_cast
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hlapp p, if_pos hp, smul_eq_mul, mul_comm, Complex.mul_conj,
      Complex.normSq_eq_norm_sq (c p)]
    push_cast
    ring
  have hnorm : ‖srcEmb l‖ ^ 2 = ∑ p ∈ F, ‖c p‖ ^ 2 := by
    rw [norm_srcEmb_sq, Finset.sum_subset hsupp]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [hlapp p, if_pos hp]
      simp
    · intro p hp hnp
      rw [hlapp p, if_pos hp] at *
      simp at hnp ⊢
      simpa [Finsupp.mem_support_iff, hlapp p, if_pos hp] using hnp
  set S : ℝ := ∑ p ∈ F, ‖c p‖ ^ 2 with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
  have hbound : S ≤ ‖L‖ * ‖srcEmb l‖ := by
    have h1 : ‖L (srcEmb l)‖ ≤ ‖L‖ * ‖srcEmb l‖ := L.le_opNorm _
    rw [hL l, hval] at h1
    simpa [Complex.norm_real, abs_of_nonneg hSnn] using h1
  have hns : ‖srcEmb l‖ = Real.sqrt S := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [hns] at hbound
  nlinarith [Real.sq_sqrt hSnn, Real.sqrt_nonneg S, norm_nonneg L,
    sq_nonneg (Real.sqrt S - ‖L‖)]

end AdmissionLaw

end HTGeometry.ConstraintMotiveRelativity

namespace HTGeometry.ConstraintMotiveRelativity

section ContinuousPort

open scoped InnerProductSpace

variable {P : Type*} [DecidableEq P]

omit [DecidableEq P] in
theorem memℓp_conj_iff {c : P → ℂ} :
    Memℓp (fun p => (starRingEnd ℂ) (c p)) 2 ↔ Summable (fun p => ‖c p‖ ^ 2) := by
  rw [memℓp_two_iff]
  simp

/-- The Riesz vector of a square-summable coefficient family. -/
noncomputable def portVec (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) : SourceL2 P :=
  ⟨fun p => (starRingEnd ℂ) (c p), memℓp_conj_iff.2 h⟩

omit [DecidableEq P] in
@[simp] theorem portVec_apply (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) (p : P) :
    (portVec c h : P → ℂ) p = (starRingEnd ℂ) (c p) := rfl

/-- **The continuous port** determined by a square-summable coefficient family. -/
noncomputable def portCL (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) :
    SourceL2 P →L[ℂ] ℂ := innerSL ℂ (portVec c h)

theorem inner_srcEmb_single (p : P) (a : ℂ) (y : SourceL2 P) :
    ⟪srcEmb (Finsupp.single p a), y⟫_ℂ = (starRingEnd ℂ) a * (y : P → ℂ) p := by
  have h : srcEmb (Finsupp.single p a) = lp.single 2 p a := by
    rw [srcEmb_single, srcBasis, ← lp.single_smul]
    simp
  rw [h, lp.inner_single_left]
  simp only [RCLike.inner_apply]
  ring

theorem portCL_srcEmb (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) (l : P →₀ ℂ) :
    portCL c h (srcEmb l) = portLin c l := by
  classical
  rw [portCL]
  show ⟪portVec c h, srcEmb l⟫_ℂ = portLin c l
  rw [srcEmb_eq_sum, inner_sum, portLin, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [lp.inner_single_right]
  simp [RCLike.inner_apply, mul_comm]

omit [DecidableEq P] in
/-- The port norm squared is the total capacity `(CA.7)`. -/
theorem norm_portCL_sq (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) :
    ‖portCL c h‖ ^ 2 = ∑' p, ‖c p‖ ^ 2 := by
  rw [portCL, innerSL_apply_norm, norm_sq_eq_tsum]
  exact tsum_congr fun p => by simp

/-- **Theorem 2, `(CA.7)`: capacity is admission.**  The algebraic port extends to a continuous
functional on the source chart exactly when its total capacity is finite. -/
theorem port_admission_iff (c : P → ℂ) :
    (∃ L : SourceL2 P →L[ℂ] ℂ, ∀ l : P →₀ ℂ, L (srcEmb l) = portLin c l)
      ↔ Summable (fun p => ‖c p‖ ^ 2) := by
  constructor
  · rintro ⟨L, hL⟩
    exact summable_of_continuous_port c L hL
  · intro h
    exact ⟨portCL c h, portCL_srcEmb c h⟩

omit [DecidableEq P] in
/-- The admitted constraint is closed. -/
theorem isClosed_ker_portCL (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2)) :
    IsClosed ((LinearMap.ker (portCL c h : SourceL2 P →ₗ[ℂ] ℂ)) : Set (SourceL2 P)) :=
  (portCL c h).isClosed_ker

/-- The admitted constraint has codimension one as soon as the port is nonzero. -/
theorem quot_ker_portCL_equiv (c : P → ℂ) (h : Summable (fun p => ‖c p‖ ^ 2))
    {p₀ : P} (hp₀ : c p₀ ≠ 0) :
    Nonempty ((SourceL2 P ⧸ LinearMap.ker (portCL c h : SourceL2 P →ₗ[ℂ] ℂ)) ≃ₗ[ℂ] ℂ) := by
  have hv : portCL c h (srcEmb (Finsupp.single p₀ 1)) = c p₀ := by
    rw [portCL_srcEmb, portLin_single, one_mul]
  refine ⟨LinearMap.quotKerEquivOfSurjective _ ?_⟩
  intro z
  refine ⟨(z / c p₀) • srcEmb (Finsupp.single p₀ 1), ?_⟩
  simp only [ContinuousLinearMap.coe_coe, map_smul, hv, smul_eq_mul]
  exact div_mul_cancel₀ _ hp₀

end ContinuousPort

end HTGeometry.ConstraintMotiveRelativity

namespace HTGeometry.ConstraintMotiveRelativity

section DivergentCapacity

open scoped InnerProductSpace

variable {P : Type*} [DecidableEq P]

/-- **Divergent capacity annihilates the continuous annihilator of the constraint.** -/
theorem portKer_orthogonal_eq_bot (c : P → ℂ) (hns : ¬ Summable (fun p => ‖c p‖ ^ 2)) :
    (portKer c)ᗮ = ⊥ := by
  classical
  have hex : ∃ p, c p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hns (by simp [hcon])
  obtain ⟨p₀, hp₀⟩ := hex
  have hcp₀ : (starRingEnd ℂ) (c p₀) ≠ 0 := by simp [hp₀]
  rw [Submodule.eq_bot_iff]
  intro y hy
  set α : ℂ := (y : P → ℂ) p₀ / (starRingEnd ℂ) (c p₀) with hα
  have hcoord : ∀ p, (y : P → ℂ) p = α * (starRingEnd ℂ) (c p) := by
    intro p
    by_cases hpp : p = p₀
    · subst hpp
      rw [hα, div_mul_cancel₀ _ hcp₀]
    · have hker : portLin c (Finsupp.single p₀ (c p) - Finsupp.single p (c p₀)) = 0 := by
        rw [map_sub, portLin_single, portLin_single]
        ring
      have hmem := mem_portKer_of_ker hker
      have h0 := (Submodule.mem_orthogonal _ _).1 hy _ hmem
      rw [map_sub, inner_sub_left, inner_srcEmb_single, inner_srcEmb_single, sub_eq_zero] at h0
      rw [hα]
      field_simp
      linear_combination -h0
  by_cases hzero : α = 0
  · refine Submodule.mem_bot ℂ |>.2 ?_
    refine lp.ext (funext fun p => ?_)
    rw [hcoord p, hzero, zero_mul]
    rfl
  · exfalso
    apply hns
    have hy2 : Summable (fun p => ‖(y : P → ℂ) p‖ ^ 2) := memℓp_two_iff.1 y.2
    have hrw : ∀ p, ‖(y : P → ℂ) p‖ ^ 2 = ‖α‖ ^ 2 * ‖c p‖ ^ 2 := by
      intro p
      rw [hcoord p, norm_mul, mul_pow]
      simp
    have hs : Summable (fun p => ‖α‖ ^ 2 * ‖c p‖ ^ 2) := hy2.congr hrw
    have hαne : (‖α‖ ^ 2) ≠ 0 := by
      have : ‖α‖ ≠ 0 := norm_ne_zero_iff.2 hzero
      positivity
    exact (hs.mul_left (‖α‖ ^ 2)⁻¹).congr fun p => by field_simp

/-- **Theorem 2, divergent branch.**  When the total capacity diverges the algebraic constraint is
dense, so Hausdorff reduction of the port vanishes. -/
theorem portKer_topologicalClosure_eq_top (c : P → ℂ)
    (hns : ¬ Summable (fun p => ‖c p‖ ^ 2)) :
    (portKer c).topologicalClosure = ⊤ :=
  Submodule.topologicalClosure_eq_top_iff.2 (portKer_orthogonal_eq_bot c hns)

theorem dense_portKer (c : P → ℂ) (hns : ¬ Summable (fun p => ‖c p‖ ^ 2)) :
    Dense ((portKer c : Set (SourceL2 P))) := by
  have h := portKer_topologicalClosure_eq_top c hns
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact h

omit [DecidableEq P] in
/-- **Corollary 2.1, `(CA.8)`.**  Divergent capacity produces apertures of arbitrarily large
capacity. -/
theorem exists_aperture_capacity_gt (c : P → ℂ) (hns : ¬ Summable (fun p => ‖c p‖ ^ 2))
    (M : ℝ) : ∃ F : Finset P, M < ∑ p ∈ F, ‖c p‖ ^ 2 := by
  by_contra hcon
  push Not at hcon
  exact hns (summable_of_sum_le (fun p => by positivity) hcon)

omit [DecidableEq P] in
/-- Equivalently, the unit-port minimum filling energy `1 / C_F` becomes arbitrarily small. -/
theorem exists_aperture_minEnergy_lt (c : P → ℂ) (hns : ¬ Summable (fun p => ‖c p‖ ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset P, 0 < (∑ p ∈ F, ‖c p‖ ^ 2) ∧ 1 / (∑ p ∈ F, ‖c p‖ ^ 2) < ε := by
  obtain ⟨F, hF⟩ := exists_aperture_capacity_gt c hns (max 0 (1 / ε))
  have h0 : (0 : ℝ) < ∑ p ∈ F, ‖c p‖ ^ 2 := lt_of_le_of_lt (le_max_left _ _) hF
  refine ⟨F, h0, ?_⟩
  rw [div_lt_iff₀ h0]
  have h1 : 1 / ε < ∑ p ∈ F, ‖c p‖ ^ 2 := lt_of_le_of_lt (le_max_right _ _) hF
  rw [div_lt_iff₀ hε] at h1
  linarith

/-- Capacity divergence and vanishing unit-port energy are the same phase. -/
theorem tendsto_atTop_iff_tendsto_inv_zero {C : ℕ → ℝ} (hC : ∀ n, 0 < C n) :
    Filter.Tendsto C Filter.atTop Filter.atTop ↔
      Filter.Tendsto (fun n => (C n)⁻¹) Filter.atTop (nhds 0) := by
  constructor
  · intro h
    exact h.inv_tendsto_atTop
  · intro h
    have hpos : ∀ᶠ n in Filter.atTop, (C n)⁻¹ ∈ Set.Ioi (0 : ℝ) :=
      Filter.Eventually.of_forall fun n => inv_pos.2 (hC n)
    have h' : Filter.Tendsto (fun n => (C n)⁻¹) Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h hpos
    have := h'.inv_tendsto_nhdsGT_zero
    refine this.congr fun n => ?_
    simp [inv_inv]

end DivergentCapacity

end HTGeometry.ConstraintMotiveRelativity
