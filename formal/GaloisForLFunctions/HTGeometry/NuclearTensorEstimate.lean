import GaloisForLFunctions.HTGeometry.TensorContraction
import GaloisForLFunctions.HTGeometry.InjectiveTensorSubspace

/-!
# The nuclear estimate

A trace-class map `T x = ∑ φ_k(x) • y_k` with `∑ ‖φ_k‖‖y_k‖ < ∞` turns the projective tensor
seminorm into the injective one: tensoring `T` with the identity contracts the projective seminorm
of the image by the injective seminorm of the argument, with the trace norm as the constant,

`π((T ⊗ 1) z) ≤ (∑ ‖φ_k‖‖y_k‖) · ε(z)`.

The proof is the classical one: the partial sums of the expansion are finite sums of pure tensors
`y_k ⊗ (φ_k ⌟ z)`, each bounded by `‖y_k‖‖φ_k‖ ε(z)`, and the tail is bounded through the operator
norm by the projective seminorm, which is finite, so the tail contributes nothing in the limit.

* `traceClassPartial` : the partial sums of a trace-class expansion.
* `projTensorSeminorm_nuclear_le` : **the nuclear estimate `π(T ⊗ 1) ≤ trace-norm · ε`.**
-/

open scoped TensorProduct Topology
open Filter

noncomputable section

namespace GaloisForLFunctions

variable {𝕜 X Y F ι : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [AddCommGroup F] [Module 𝕜 F]

/-! ## Two elementary lemmas -/

theorem seminorm_finsetSum_le {G : Type*} [AddCommGroup G] [Module 𝕜 G] (r : Seminorm 𝕜 G)
    {κ : Type*} (s : Finset κ) (g : κ → G) : r (∑ k ∈ s, g k) ≤ ∑ k ∈ s, r (g k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (map_add_le_add r _ _) (by linarith)

theorem tensorMap_add_left (A B : X →ₗ[𝕜] Y) (z : X ⊗[𝕜] F) :
    TensorProduct.map (A + B) (LinearMap.id : F →ₗ[𝕜] F) z
      = TensorProduct.map A (LinearMap.id : F →ₗ[𝕜] F) z
        + TensorProduct.map B (LinearMap.id : F →ₗ[𝕜] F) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x f =>
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearMap.add_apply, TensorProduct.add_tmul]
  | add a b ha hb =>
    rw [map_add, map_add, map_add, ha, hb]
    abel

/-! ## The partial sums of a trace-class expansion -/

/-- The partial sum of a trace-class expansion. -/
def traceClassPartial (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y) (s : Finset ι) : X →ₗ[𝕜] Y :=
  ∑ k ∈ s, (φ k : X →ₗ[𝕜] 𝕜).smulRight (y k)

theorem traceClassPartial_apply (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y) (s : Finset ι) (x : X) :
    traceClassPartial φ y s x = ∑ k ∈ s, φ k x • y k := by
  rw [traceClassPartial, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.smulRight_apply]
  rfl

/-- Tensoring a partial sum gives a finite sum of pure tensors built from the contractions. -/
theorem map_traceClassPartial (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y) (s : Finset ι)
    (z : X ⊗[𝕜] F) :
    TensorProduct.map (traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z
      = ∑ k ∈ s, (y k) ⊗ₜ[𝕜] (tensorContract (φ k : X →ₗ[𝕜] 𝕜) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x f =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, traceClassPartial_apply,
      TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tensorContract_tmul]
    exact TensorProduct.smul_tmul _ _ _
  | add a b ha hb =>
    rw [map_add, ha, hb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, TensorProduct.tmul_add]

/-- **The nuclear estimate for a partial sum.** -/
theorem projTensorSeminorm_traceClassPartial_le (q : Seminorm 𝕜 F) (φ : ι → (X →L[𝕜] 𝕜))
    (y : ι → Y) (s : Finset ι) (z : X ⊗[𝕜] F) :
    projTensorSeminorm (normSeminorm 𝕜 Y) q
        (TensorProduct.map (traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ (∑ k ∈ s, ‖φ k‖ * ‖y k‖) * injTensorSeminorm (normSeminorm 𝕜 X) q z := by
  rw [map_traceClassPartial, Finset.sum_mul]
  refine le_trans (seminorm_finsetSum_le _ s _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  have hcontract : q (tensorContract (φ k : X →ₗ[𝕜] 𝕜) z)
      ≤ ‖φ k‖ * injTensorSeminorm (normSeminorm 𝕜 X) q z := by
    refine seminorm_tensorContract_le_mul (normSeminorm 𝕜 X) q _ (norm_nonneg _) ?_ z
    intro x
    exact (φ k).le_opNorm x
  have htmul : projTensorSeminorm (normSeminorm 𝕜 Y) q
      ((y k) ⊗ₜ[𝕜] tensorContract (φ k : X →ₗ[𝕜] 𝕜) z)
      ≤ ‖y k‖ * q (tensorContract (φ k : X →ₗ[𝕜] 𝕜) z) :=
    projTensorSeminorm_tmul_le (normSeminorm 𝕜 Y) q (y k) _
  have hynn : (0 : ℝ) ≤ ‖y k‖ := norm_nonneg _
  calc projTensorSeminorm (normSeminorm 𝕜 Y) q
        ((y k) ⊗ₜ[𝕜] tensorContract (φ k : X →ₗ[𝕜] 𝕜) z)
      ≤ ‖y k‖ * q (tensorContract (φ k : X →ₗ[𝕜] 𝕜) z) := htmul
    _ ≤ ‖y k‖ * (‖φ k‖ * injTensorSeminorm (normSeminorm 𝕜 X) q z) :=
        mul_le_mul_of_nonneg_left hcontract hynn
    _ = ‖φ k‖ * ‖y k‖ * injTensorSeminorm (normSeminorm 𝕜 X) q z := by ring

/-! ## The tail -/

theorem norm_sub_traceClassPartial_le (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y)
    (T : X →ₗ[𝕜] Y)
    (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x)) (s : Finset ι) (x : X) :
    ‖T x - traceClassPartial φ y s x‖
      ≤ (∑' k : {k : ι // k ∉ s}, ‖φ k‖ * ‖y k‖) * ‖x‖ := by
  classical
  have hlim : Tendsto (fun t : Finset ι => ∑ k ∈ t, φ k x • y k) atTop (𝓝 (T x)) := hT x
  have hnorm : Tendsto
      (fun t : Finset ι => ‖(∑ k ∈ t, φ k x • y k) - traceClassPartial φ y s x‖) atTop
      (𝓝 (‖T x - traceClassPartial φ y s x‖)) :=
    (hlim.sub tendsto_const_nhds).norm
  refine le_of_tendsto hnorm ?_
  filter_upwards [Filter.eventually_ge_atTop s] with t hts
  have hdiff : (∑ k ∈ t, φ k x • y k) - traceClassPartial φ y s x
      = ∑ k ∈ t \ s, φ k x • y k := by
    rw [traceClassPartial_apply, ← Finset.sum_sdiff hts]
    abel
  have hterm : ∀ k ∈ t \ s, ‖φ k x • y k‖ ≤ ‖φ k‖ * ‖y k‖ * ‖x‖ := by
    intro k _
    rw [norm_smul]
    have h1 : ‖φ k x‖ ≤ ‖φ k‖ * ‖x‖ := (φ k).le_opNorm x
    calc ‖φ k x‖ * ‖y k‖ ≤ (‖φ k‖ * ‖x‖) * ‖y k‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖φ k‖ * ‖y k‖ * ‖x‖ := by ring
  have hfin : (∑ k ∈ t \ s, ‖φ k‖ * ‖y k‖)
      ≤ ∑' k : {k : ι // k ∉ s}, ‖φ k‖ * ‖y k‖ := by
    have hfilter : (t \ s).filter (fun k => k ∉ s) = t \ s :=
      Finset.filter_true_of_mem fun k hk => (Finset.mem_sdiff.mp hk).2
    have hsub := Finset.sum_subtype_eq_sum_filter (s := t \ s)
      (fun j : ι => ‖φ j‖ * ‖y j‖) (p := fun k => k ∉ s)
    rw [hfilter] at hsub
    rw [← hsub]
    exact Summable.sum_le_tsum _ (fun k _ => by positivity) (hsum.subtype _)
  rw [hdiff]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hfin (norm_nonneg x)

/-! ## The nuclear estimate -/

/-- **The nuclear estimate**: a trace-class map contracts the projective tensor seminorm to the
injective one, with the trace norm as the constant. -/
theorem projTensorSeminorm_nuclear_le (q : Seminorm 𝕜 F) (T : X →ₗ[𝕜] Y)
    (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y) (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x)) (z : X ⊗[𝕜] F) :
    projTensorSeminorm (normSeminorm 𝕜 Y) q
        (TensorProduct.map T (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ (∑' k, ‖φ k‖ * ‖y k‖) * injTensorSeminorm (normSeminorm 𝕜 X) q z := by
  classical
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hπ : (0 : ℝ) ≤ projTensorSeminorm (normSeminorm 𝕜 X) q z := apply_nonneg _ _
  have htend : Tendsto
      (fun s : Finset ι => (∑' k : {k : ι // k ∉ s}, ‖φ k‖ * ‖y k‖)
        * projTensorSeminorm (normSeminorm 𝕜 X) q z) atTop (𝓝 0) := by
    have h := tendsto_tsum_compl_atTop_zero (fun k => ‖φ k‖ * ‖y k‖)
    have h2 := h.mul_const (projTensorSeminorm (normSeminorm 𝕜 X) q z)
    rw [zero_mul] at h2
    exact h2
  obtain ⟨s, hs⟩ := ((htend.eventually (gt_mem_nhds hε)).exists)
  have hdecomp : T = traceClassPartial φ y s + (T - traceClassPartial φ y s) := by
    abel
  have hmapsplit : TensorProduct.map T (LinearMap.id : F →ₗ[𝕜] F) z
      = TensorProduct.map (traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z
        + TensorProduct.map (T - traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z := by
    rw [← tensorMap_add_left, ← hdecomp]
  have hpartial := projTensorSeminorm_traceClassPartial_le q φ y s z
  have hsumle : (∑ k ∈ s, ‖φ k‖ * ‖y k‖) ≤ ∑' k, ‖φ k‖ * ‖y k‖ :=
    hsum.sum_le_tsum s (fun k _ => by positivity)
  have hεnn : (0 : ℝ) ≤ injTensorSeminorm (normSeminorm 𝕜 X) q z := apply_nonneg _ _
  have hpartial' : projTensorSeminorm (normSeminorm 𝕜 Y) q
      (TensorProduct.map (traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ (∑' k, ‖φ k‖ * ‖y k‖) * injTensorSeminorm (normSeminorm 𝕜 X) q z :=
    le_trans hpartial (mul_le_mul_of_nonneg_right hsumle hεnn)
  have htail : projTensorSeminorm (normSeminorm 𝕜 Y) q
      (TensorProduct.map (T - traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ (∑' k : {k : ι // k ∉ s}, ‖φ k‖ * ‖y k‖)
        * projTensorSeminorm (normSeminorm 𝕜 X) q z := by
    have hnn : (0 : ℝ) ≤ ∑' k : {k : ι // k ∉ s}, ‖φ k‖ * ‖y k‖ :=
      tsum_nonneg fun k => by positivity
    have hmap := projTensorSeminorm_map_le (normSeminorm 𝕜 X) q (normSeminorm 𝕜 Y) q
      (T - traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) hnn zero_le_one
      (fun x => norm_sub_traceClassPartial_le φ y T hsum hT s x)
      (fun f => by rw [LinearMap.id_apply, one_mul]) z
    rw [mul_one] at hmap
    exact hmap
  calc projTensorSeminorm (normSeminorm 𝕜 Y) q
        (TensorProduct.map T (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ projTensorSeminorm (normSeminorm 𝕜 Y) q
          (TensorProduct.map (traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z)
        + projTensorSeminorm (normSeminorm 𝕜 Y) q
          (TensorProduct.map (T - traceClassPartial φ y s) (LinearMap.id : F →ₗ[𝕜] F) z) := by
        rw [hmapsplit]
        exact map_add_le_add _ _ _
    _ ≤ (∑' k, ‖φ k‖ * ‖y k‖) * injTensorSeminorm (normSeminorm 𝕜 X) q z + ε := by
        have := hs
        linarith

/-! ## The estimate along a comparison map -/

/-- **The nuclear estimate along a comparison of seminorms**: if the canonical map to `Y`
factors through a trace-class map out of `X`, then the projective seminorm of the image is bounded
by the injective seminorm computed with the pulled-back seminorm of `X`. -/
theorem projTensorSeminorm_nuclear_comp_le {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (q : Seminorm 𝕜 F) (κX : E →ₗ[𝕜] X) (κY : E →ₗ[𝕜] Y) (T : X →ₗ[𝕜] Y)
    (hcomm : ∀ e, T (κX e) = κY e) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y)
    (hsum : Summable fun k => ‖φ k‖ * ‖y k‖)
    (hT : ∀ x, HasSum (fun k => φ k x • y k) (T x)) (z : E ⊗[𝕜] F) :
    projTensorSeminorm (normSeminorm 𝕜 Y) q
        (TensorProduct.map κY (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ (∑' k, ‖φ k‖ * ‖y k‖)
        * injTensorSeminorm ((normSeminorm 𝕜 X).comp κX) q z := by
  have hfactor : TensorProduct.map κY (LinearMap.id : F →ₗ[𝕜] F) z
      = TensorProduct.map T (LinearMap.id : F →ₗ[𝕜] F)
        (TensorProduct.map κX (LinearMap.id : F →ₗ[𝕜] F) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul e f =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
        LinearMap.id_apply, LinearMap.id_apply, hcomm e]
    | add a b ha hb =>
      rw [map_add, map_add, map_add, ha, hb]
  have hnn : (0 : ℝ) ≤ ∑' k, ‖φ k‖ * ‖y k‖ := tsum_nonneg fun k => by positivity
  have hstep := projTensorSeminorm_nuclear_le q T φ y hsum hT
    (TensorProduct.map κX (LinearMap.id : F →ₗ[𝕜] F) z)
  have hpull : injTensorSeminorm (normSeminorm 𝕜 X) q
      (TensorProduct.map κX (LinearMap.id : F →ₗ[𝕜] F) z)
      ≤ injTensorSeminorm ((normSeminorm 𝕜 X).comp κX) q z := by
    refine injTensorSeminorm_map_left_le ((normSeminorm 𝕜 X).comp κX) (normSeminorm 𝕜 X) q κX ?_ z
    intro e
    exact le_of_eq (Seminorm.comp_apply (normSeminorm 𝕜 X) κX e).symm
  rw [hfactor]
  exact le_trans hstep (mul_le_mul_of_nonneg_left hpull hnn)

end GaloisForLFunctions

end
