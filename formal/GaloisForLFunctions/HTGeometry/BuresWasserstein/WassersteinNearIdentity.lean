import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldContraction
import GaloisForLFunctions.HTGeometry.BuresWasserstein.WassersteinFieldCoercivity
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Existence and uniqueness of the Wasserstein barycentre near the identity

The Newton map `N(X) = X - 2 Φ(X)` of the Wasserstein vector field contracts on the closed
convex set of self-adjoint operators within distance `1/32` of the identity, provided the data
`Aᵢ` lie within `1/128` of the identity.  Banach's fixed point theorem then produces a unique
zero of `Φ`, that is, a unique Wasserstein barycentre.
-/

open scoped NNReal Ring BigOperators
open Set

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

/-- The twisted Lyapunov unit exists at every strictly positive pair. -/
lemma exists_twisted_unit {a X : A} (ha : IsStrictlyPositive a) (hX : IsStrictlyPositive X) :
    ∃ u : (A →L[ℝ] A)ˣ, (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ))).comp (saProj : A →L[ℝ] A)
        + ((1 : A →L[ℝ] A) - saProj) := by
  have hc : IsStrictlyPositive (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ) :=
    isStrictlyPositive_conjMap_rpow ha hX.ringInverse
  have hv : IsStrictlyPositive (CFC.sqrt (conjMap (a ^ (-(1/2) : ℝ)) X⁻¹ʳ)) := hc.sqrt _
  have h := isUnit_saSquare_fderiv hv.isSelfAdjoint
    (isUnit_lyapunov_of_isStrictlyPositive hv)
  exact ⟨h.unit, h.unit_spec⟩

/-- Evaluating the derivative of the Wasserstein vector field. -/
lemma wassFieldDeriv_apply (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A)
    (u : ι → (A →L[ℝ] A)ˣ) (P : A) :
    (∑ i ∈ s, w i • (-((((conjMap ((Av i) ^ (1/2 : ℝ))).comp
        ((↑(u i)⁻¹ : A →L[ℝ] A).comp (conjMap ((Av i) ^ (-(1/2) : ℝ))))).comp
      (-ContinuousLinearMap.mulLeftRight ℝ A X⁻¹ʳ X⁻¹ʳ))))) P
      = ∑ i ∈ s, w i • conjMap ((Av i) ^ (1/2 : ℝ)) ((↑(u i)⁻¹ : A →L[ℝ] A)
          (conjMap ((Av i) ^ (-(1/2) : ℝ)) (X⁻¹ʳ * P * X⁻¹ʳ))) := by
  simp [ContinuousLinearMap.mulLeftRight_apply]

/-- The Newton map of the Wasserstein vector field. -/
noncomputable def newtonMap (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A) : A :=
  X - (2 : ℝ) • wassField s w Av X

lemma newtonMap_eq_self_iff (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A) :
    newtonMap s w Av X = X ↔ wassField s w Av X = 0 := by
  unfold newtonMap
  constructor
  · intro h
    have h2 : (2 : ℝ) • wassField s w Av X = 0 := by
      have := sub_eq_self.mp h
      exact this
    have := smul_eq_zero.mp h2
    rcases this with h3 | h3
    · exact absurd h3 (by norm_num)
    · exact h3
  · intro h
    rw [h, smul_zero, sub_zero]

variable {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

/-- **The Newton map contracts near the identity.** -/
theorem norm_newtonMap_sub_le
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hAδ : ∀ i ∈ s, ‖Av i - 1‖ ≤ δ)
    {X Y : A} (hXsa : IsSelfAdjoint X) (hYsa : IsSelfAdjoint Y)
    (hXδ : ‖X - 1‖ ≤ δ) (hYδ : ‖Y - 1‖ ≤ δ) :
    ‖newtonMap s w Av Y - newtonMap s w Av X‖ ≤ newtonConst δ * ‖Y - X‖ := by
  classical
  have hPsa : IsSelfAdjoint (Y - X) := hYsa.sub hXsa
  -- the segment
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, IsSelfAdjoint (X + t • (Y - X))
      ∧ ‖X + t • (Y - X) - 1‖ ≤ δ := by
    intro t ht
    refine ⟨hXsa.add (IsSelfAdjoint.smul (star_trivial t) hPsa), ?_⟩
    have hid : X + t • (Y - X) - 1 = (1 - t) • (X - 1) + t • (Y - 1) := by
      module
    rw [hid]
    have h1 : ‖(1 - t) • (X - 1)‖ = (1 - t) * ‖X - 1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
    have h2 : ‖t • (Y - 1)‖ = t * ‖Y - 1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have := norm_add_le ((1 - t) • (X - 1)) (t • (Y - 1))
    rw [h1, h2] at this
    nlinarith [ht.1, ht.2, norm_nonneg (X - 1), norm_nonneg (Y - 1)]
  -- the derivative along the segment
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ z : A, ‖z‖ ≤ newtonConst δ * ‖Y - X‖
        ∧ HasDerivAt (fun r : ℝ => newtonMap s w Av (X + r • (Y - X))) z t := by
    intro t ht
    obtain ⟨htsa, htδ⟩ := hseg t ht
    set Xt : A := X + t • (Y - X) with hXt
    have hXtpos : IsStrictlyPositive Xt := isStrictlyPositive_of_norm_sub_one_le htsa hδ1 htδ
    have hex : ∀ i, ∃ v : (A →L[ℝ] A)ˣ, i ∈ s → (↑v : A →L[ℝ] A)
        = (lyapunov (CFC.sqrt (conjMap ((Av i) ^ (-(1/2) : ℝ)) Xt⁻¹ʳ))).comp
            (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj) := by
      intro i
      by_cases hi : i ∈ s
      · obtain ⟨v, hv⟩ := exists_twisted_unit (hA i hi) hXtpos
        exact ⟨v, fun _ => hv⟩
      · exact ⟨1, fun h => absurd h hi⟩
    choose u hu using hex
    have hc : ∀ i ∈ s, IsStrictlyPositive (conjMap ((Av i) ^ (-(1/2) : ℝ)) Xt⁻¹ʳ) :=
      fun i hi => isStrictlyPositive_conjMap_rpow (hA i hi) hXtpos.ringInverse
    have hΦ := (hasStrictFDerivAt_wassField (w := w) hXtpos hc hu).hasFDerivAt
    have hN : HasFDerivAt (newtonMap s w Av)
        (ContinuousLinearMap.id ℝ A - (2 : ℝ) • (∑ i ∈ s, w i • (-((((conjMap
            ((Av i) ^ (1/2 : ℝ))).comp
              ((↑(u i)⁻¹ : A →L[ℝ] A).comp (conjMap ((Av i) ^ (-(1/2) : ℝ))))).comp
          (-ContinuousLinearMap.mulLeftRight ℝ A Xt⁻¹ʳ Xt⁻¹ʳ)))))) Xt :=
      (hasFDerivAt_id Xt).sub (hΦ.const_smul (2 : ℝ))
    have hline : HasDerivAt (fun r : ℝ => X + r • (Y - X)) (Y - X) t := by
      simpa using ((hasDerivAt_id t).smul_const (Y - X)).const_add X
    have hcomp := hN.comp_hasDerivAt t hline
    refine ⟨_, ?_, hcomp⟩
    have happ : (ContinuousLinearMap.id ℝ A - (2 : ℝ) • (∑ i ∈ s, w i • (-((((conjMap
            ((Av i) ^ (1/2 : ℝ))).comp
              ((↑(u i)⁻¹ : A →L[ℝ] A).comp (conjMap ((Av i) ^ (-(1/2) : ℝ))))).comp
          (-ContinuousLinearMap.mulLeftRight ℝ A Xt⁻¹ʳ Xt⁻¹ʳ)))))) (Y - X)
        = (Y - X) - (2 : ℝ) • (∑ i ∈ s, w i • conjMap ((Av i) ^ (1/2 : ℝ))
            ((↑(u i)⁻¹ : A →L[ℝ] A)
              (conjMap ((Av i) ^ (-(1/2) : ℝ)) (Xt⁻¹ʳ * (Y - X) * Xt⁻¹ʳ)))) := by
      rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, wassFieldDeriv_apply]
    rw [happ]
    exact norm_newton_deriv_le hw hwsum hA hXtpos hPsa hδ0 hδ1 hAδ htδ hu
  choose z hz hzd using hderiv
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r : ℝ => newtonMap s w Av (X + r • (Y - X)))
    (f' := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then z t ht else 0)
    (C := newtonConst δ * ‖Y - X‖)
    (fun t ht => by rw [dif_pos ht]; exact (hzd t ht).hasDerivWithinAt)
    (fun t ht => by
      rw [dif_pos (Ico_subset_Icc_self ht)]
      exact hz t (Ico_subset_Icc_self ht)) 1 (right_mem_Icc.mpr zero_le_one)
  have h0 : X + (0 : ℝ) • (Y - X) = X := by simp
  have h1 : X + (1 : ℝ) • (Y - X) = Y := by
    rw [one_smul]; abel
  rw [h0, h1] at hmvt
  simpa using hmvt

/-! ### The Wasserstein field at the identity -/

/-- The Wasserstein field at the identity is the deviation of the mean of the square roots. -/
lemma wassField_one (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    wassField s w Av (1 : A) = ∑ i ∈ s, w i • ((1 : A) - CFC.sqrt (Av i)) := by
  unfold wassField
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 2
  rw [gmInvMap_eq_gm (isStrictlyPositive_one (A := A)), Ring.inverse_one,
    gm_one_right (hA i hi)]

/-- The Wasserstein field is small at the identity when the data are near the identity. -/
lemma norm_wassField_one_le (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) {δ : ℝ} (hAδ : ∀ i ∈ s, ‖Av i - 1‖ ≤ δ) :
    ‖wassField s w Av (1 : A)‖ ≤ δ := by
  rw [wassField_one hA]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ i ∈ s, ‖w i • ((1 : A) - CFC.sqrt (Av i))‖ ≤ w i * δ := by
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
    refine mul_le_mul_of_nonneg_left ?_ (hw i hi)
    rw [← norm_neg, neg_sub]
    exact (norm_cfcSqrt_sub_one_le (hA i hi).nonneg).trans (hAδ i hi)
  calc ∑ i ∈ s, ‖w i • ((1 : A) - CFC.sqrt (Av i))‖ ≤ ∑ i ∈ s, w i * δ :=
        Finset.sum_le_sum hterm
    _ = δ := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- The Wasserstein field takes self-adjoint values at strictly positive points. -/
lemma isSelfAdjoint_wassField {X : A} (hX : IsStrictlyPositive X) :
    IsSelfAdjoint (wassField s w Av X) := by
  unfold wassField
  show star _ = _
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : IsSelfAdjoint ((1 : A) - gmInvMap (Av i) X) := by
    rw [gmInvMap_eq_gm hX]
    exact (IsSelfAdjoint.one A).sub (gm_nonneg _ _).isSelfAdjoint
  exact (IsSelfAdjoint.smul (star_trivial (w i)) h).star_eq

/-! ### The fixed point -/

/-- **Theorem 3.5 (Kim–Mer–Pálfia).**  For weights summing to one and data within `1/128` of the
identity, the Wasserstein equation has a unique solution within `1/32` of the identity. -/
theorem existsUnique_isWassersteinPoint_near_one
    (hw : ∀ i ∈ s, 0 ≤ w i) (hwsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAδ : ∀ i ∈ s, ‖Av i - 1‖ ≤ 1/128) :
    ∃! X : A, ‖X - 1‖ ≤ 1/32 ∧ IsWassersteinPoint s w Av X := by
  classical
  have hδ0 : (0 : ℝ) ≤ 1/32 := by norm_num
  have hδ1 : (1 : ℝ)/32 < 1 := by norm_num
  have hAδ' : ∀ i ∈ s, ‖Av i - 1‖ ≤ 1/32 := fun i hi => (hAδ i hi).trans (by norm_num)
  set S : Set A := {x : A | IsSelfAdjoint x ∧ ‖x - 1‖ ≤ 1/32} with hSdef
  have hSpos : ∀ x ∈ S, IsStrictlyPositive x := fun x hx =>
    isStrictlyPositive_of_norm_sub_one_le hx.1 hδ1 hx.2
  -- contraction estimate on `S`
  have hcontr : ∀ x ∈ S, ∀ y ∈ S,
      ‖newtonMap s w Av y - newtonMap s w Av x‖ ≤ (1/2) * ‖y - x‖ := by
    intro x hx y hy
    refine (norm_newtonMap_sub_le hw hwsum hA hδ0 hδ1 hAδ' hx.1 hy.1 hx.2 hy.2).trans ?_
    exact mul_le_mul_of_nonneg_right newtonConst_thirtysecond (norm_nonneg _)
  -- `S` is invariant
  have hone : (1 : A) ∈ S := ⟨IsSelfAdjoint.one A, by simp⟩
  have hmaps : ∀ x ∈ S, newtonMap s w Av x ∈ S := by
    intro x hx
    have hxpos : IsStrictlyPositive x := hSpos x hx
    refine ⟨hx.1.sub (IsSelfAdjoint.smul (star_trivial (2 : ℝ))
      (isSelfAdjoint_wassField hxpos)), ?_⟩
    have hN1 : newtonMap s w Av (1 : A) - 1 = -((2 : ℝ) • wassField s w Av (1 : A)) := by
      unfold newtonMap; abel
    have hN1n : ‖newtonMap s w Av (1 : A) - 1‖ ≤ 2 * (1/128) := by
      rw [hN1, norm_neg, norm_smul, Real.norm_eq_abs]
      have := norm_wassField_one_le hw hwsum hA hAδ
      have habs : |(2 : ℝ)| = 2 := by norm_num
      rw [habs]
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    have hstep := hcontr (1 : A) hone x hx
    have htri : ‖newtonMap s w Av x - 1‖
        ≤ ‖newtonMap s w Av x - newtonMap s w Av (1 : A)‖
          + ‖newtonMap s w Av (1 : A) - 1‖ := by
      have := norm_add_le (newtonMap s w Av x - newtonMap s w Av (1 : A))
        (newtonMap s w Av (1 : A) - 1)
      simpa using this
    have hx1 : ‖x - 1‖ ≤ 1/32 := hx.2
    linarith
  haveI hScl : IsClosed S := by
    have h1 : IsClosed {x : A | IsSelfAdjoint x} := isClosed_eq continuous_star continuous_id
    have h2 : IsClosed {x : A | ‖x - 1‖ ≤ 1/32} := by
      have heq : {x : A | ‖x - 1‖ ≤ 1/32} = Metric.closedBall (1 : A) (1/32) := by
        ext x; simp [Metric.mem_closedBall, dist_eq_norm]
      rw [heq]; exact Metric.isClosed_closedBall
    exact h1.inter h2
  haveI : CompleteSpace S := hScl.completeSpace_coe
  haveI : Nonempty S := ⟨⟨1, hone⟩⟩
  set F : S → S := fun x => ⟨newtonMap s w Av x.1, hmaps x.1 x.2⟩ with hFdef
  have hlip : LipschitzWith (1/2 : ℝ≥0) F := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have h := hcontr y.1 y.2 x.1 x.2
    simpa using h
  have hcontracting : ContractingWith (1/2 : ℝ≥0) F := ⟨by norm_num, hlip⟩
  obtain ⟨y, hyfix, -, -⟩ := hcontracting.exists_fixedPoint ⟨1, hone⟩ (edist_ne_top _ _)
  have hy : newtonMap s w Av y.1 = y.1 := congrArg Subtype.val hyfix
  have hypos : IsStrictlyPositive y.1 := hSpos y.1 y.2
  have hyW : IsWassersteinPoint s w Av y.1 :=
    (wassField_eq_zero_iff hwsum hypos).mp ((newtonMap_eq_self_iff s w Av y.1).mp hy)
  refine ⟨y.1, ⟨y.2.2, hyW⟩, ?_⟩
  rintro z ⟨hz1, hzW⟩
  have hzS : z ∈ S := ⟨hzW.1.isSelfAdjoint, hz1⟩
  have hzfix : newtonMap s w Av z = z :=
    (newtonMap_eq_self_iff s w Av z).mpr ((wassField_eq_zero_iff hwsum hzW.1).mpr hzW)
  have hdist := hcontr z hzS y.1 y.2
  rw [hy, hzfix] at hdist
  have : ‖y.1 - z‖ = 0 := by
    have hnn : (0 : ℝ) ≤ ‖y.1 - z‖ := norm_nonneg _
    linarith
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

/-! ### Rescaling to a general Loewner interval -/

/-- A Loewner interval around the identity is contained in the corresponding norm ball. -/
lemma norm_sub_one_le_of_mem_Icc {a : A} (ha : IsSelfAdjoint a) {δ : ℝ} (hδ : 0 ≤ δ)
    (h1 : (1 - δ) • (1 : A) ≤ a) (h2 : a ≤ (1 + δ) • (1 : A)) : ‖a - 1‖ ≤ δ := by
  have hsa : IsSelfAdjoint (a - 1) := ha.sub (IsSelfAdjoint.one A)
  have hl : (-δ) • (1 : A) ≤ a - 1 := by
    have h := sub_le_sub_right h1 (1 : A)
    rwa [sub_smul, one_smul, sub_sub_cancel_left, ← neg_smul] at h
  have hr : a - 1 ≤ δ • (1 : A) := by
    have h := sub_le_sub_right h2 (1 : A)
    rwa [add_smul, one_smul, add_sub_cancel_left] at h
  have hmid := norm_sub_midpoint_le (by linarith : -δ ≤ δ) hsa hl hr
  have hzero : ((-δ + δ) / 2) • (1 : A) = 0 := by norm_num
  rw [hzero, sub_zero] at hmid
  calc ‖a - 1‖ ≤ (δ - -δ) / 2 := hmid
    _ = δ := by ring

/-- Rescaling a Loewner interval into the norm ball of radius `1/128`. -/
lemma norm_smul_sub_one_le_of_Icc {Z : A} (hZsa : IsSelfAdjoint Z) {α β c : ℝ}
    (hc : 0 < c) (hcα : (1 : ℝ) - 1/128 ≤ c * α) (hcβ : c * β ≤ 1 + 1/128)
    (h1 : α • (1 : A) ≤ Z) (h2 : Z ≤ β • (1 : A)) : ‖c • Z - 1‖ ≤ 1/128 := by
  refine norm_sub_one_le_of_mem_Icc (IsSelfAdjoint.smul (star_trivial c) hZsa)
    (by norm_num) ?_ ?_
  · refine le_trans (smul_le_smul_of_nonneg_right hcα (zero_le_one (α := A))) ?_
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left h1 hc.le
  · refine le_trans ?_ (smul_le_smul_of_nonneg_right hcβ (zero_le_one (α := A)))
    rw [mul_smul]
    exact smul_le_smul_of_nonneg_left h2 hc.le

/-- **Corollary 3.6 (Kim–Mer–Pálfia).**  If the data lie in a Loewner interval of ratio at most
`(1 + 1/128)²`, the Wasserstein equation has a unique solution. -/
theorem existsUnique_isWassersteinPoint_of_ratio
    (hw : ∀ i ∈ s, 0 < w i) (hwsum : ∑ i ∈ s, w i = 1)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hAα : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hAβ : ∀ i ∈ s, Av i ≤ β • (1 : A))
    (hratio : β ≤ α * ((1 + 1/128) * (1 + 1/128))) :
    ∃! X : A, IsWassersteinPoint s w Av X := by
  classical
  have hcpos : (0 : ℝ) < (α * (1 + 1/128))⁻¹ := by positivity
  have hαne : α ≠ 0 := ne_of_gt hα
  have hcα : (1 : ℝ) - 1/128 ≤ (α * (1 + 1/128))⁻¹ * α := by
    have h : (α * (1 + 1/128))⁻¹ * α = 128/129 := by field_simp; ring
    rw [h]; norm_num
  have hcβ : (α * (1 + 1/128))⁻¹ * β ≤ 1 + 1/128 := by
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity)]
    nlinarith [hratio, hα]
  have hB : ∀ i ∈ s, IsStrictlyPositive ((α * (1 + 1/128))⁻¹ • Av i) := fun i hi =>
    IsStrictlyPositive.smul hcpos (hA i hi)
  have hBδ : ∀ i ∈ s, ‖(α * (1 + 1/128))⁻¹ • Av i - 1‖ ≤ 1/128 := fun i hi =>
    norm_smul_sub_one_le_of_Icc (hA i hi).isSelfAdjoint hcpos hcα hcβ (hAα i hi) (hAβ i hi)
  obtain ⟨Y, ⟨hY1, hYW⟩, hYuniq⟩ :=
    existsUnique_isWassersteinPoint_near_one (fun i hi => (hw i hi).le) hwsum hB hBδ
  have hYpos : IsStrictlyPositive Y := hYW.1
  have hXpos : IsStrictlyPositive (((α * (1 + 1/128))⁻¹)⁻¹ • Y) :=
    IsStrictlyPositive.smul (inv_pos.mpr hcpos) hYpos
  have hXW : IsWassersteinPoint s w Av (((α * (1 + 1/128))⁻¹)⁻¹ • Y) := by
    have hiff := isWassersteinPoint_smul (w := w) (Av := Av)
      (X := ((α * (1 + 1/128))⁻¹)⁻¹ • Y) hcpos hXpos hA
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul] at hiff
    exact hiff.mp hYW
  refine ⟨((α * (1 + 1/128))⁻¹)⁻¹ • Y, hXW, ?_⟩
  intro Z hZ
  have hZpos : IsStrictlyPositive Z := hZ.1
  have hZi := IsWassersteinPoint.mem_Icc hα hβ hwsum hw hA hAα hAβ hZ
  have hcZ : IsWassersteinPoint s w (fun i => (α * (1 + 1/128))⁻¹ • Av i)
      ((α * (1 + 1/128))⁻¹ • Z) :=
    (isWassersteinPoint_smul hcpos hZpos hA).mpr hZ
  have hcZδ : ‖(α * (1 + 1/128))⁻¹ • Z - 1‖ ≤ 1/32 :=
    le_trans (norm_smul_sub_one_le_of_Icc hZpos.isSelfAdjoint hcpos hcα hcβ hZi.1 hZi.2)
      (by norm_num)
  have heq := hYuniq ((α * (1 + 1/128))⁻¹ • Z) ⟨hcZδ, hcZ⟩
  rw [← heq, smul_smul, inv_mul_cancel₀ (ne_of_gt hcpos), one_smul]

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
