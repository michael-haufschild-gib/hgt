import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperatorIdentity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# Compactness of the resolvent operators

* The difference kernel is bounded: `D_{a,s}(u) ≤ C (1 + u)^{−a}` (`exists_diffKernel_le`), so its
  automorphic kernel is bounded on `F × F` and `T_a − T_s` is Hilbert–Schmidt, hence compact
  (`isCompactOperator_diffOp`).
* A self-adjoint `T` with `T²` compact is compact (`isCompactOperator_of_comp_self`):
  `‖T v‖² = ⟨T² v, v⟩`, so a `ε²/2`-net of `T²(B)` pulls back to an `ε`-net of `T(B)`.
* `T_a² = T_a T_s + c T_a T_s T_a` with `T_a T_s = c⁻¹ (T_a − T_s)` compact, so every `T_a` is
  compact (`isCompactOperator_resOp`).
-/

open MeasureTheory Set Filter UpperHalfPlane Real Metric
open scoped ENNReal MatrixGroups Pointwise

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.SchurKernel

noncomputable section

/-- **Square roots of compact operators.**  A self-adjoint operator with compact square is compact. -/
theorem isCompactOperator_of_comp_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T)
    (h2 : IsCompactOperator (T ∘L T)) : IsCompactOperator T := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball (T : H →ₗ[ℂ] H) one_pos).mpr ?_
  have hK := (isCompactOperator_iff_isCompact_closure_image_ball ((T ∘L T) : H →ₗ[ℂ] H)
    one_pos).mp h2
  have htb : TotallyBounded ((T ∘L T) '' ball (0 : H) 1) := hK.totallyBounded.subset subset_closure
  refine (TotallyBounded.closure ?_).isCompact_of_isClosed isClosed_closure
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, hts, htf, hcover⟩ := totallyBounded_iff_subset.mp htb {p | dist p.1 p.2 < ε ^ 2 / 2}
    (Metric.dist_mem_uniformity (by positivity))
  have hpre : ∀ y ∈ t, ∃ x ∈ ball (0 : H) 1, (T ∘L T) x = y := fun y hy => hts hy
  choose g hg hgy using hpre
  haveI := htf.to_subtype
  refine ⟨Set.range fun y : t => T (g y.1 y.2), Set.finite_range _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmem : (T ∘L T) x ∈ (T ∘L T) '' ball (0 : H) 1 := ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hmem)
  simp only [mem_setOf_eq] at hxy
  refine mem_iUnion₂.mpr ⟨T (g y hy), ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  set v := x - g y hy
  have hv : ‖v‖ < 2 := by
    have h1 : ‖x‖ < 1 := by simpa using hx
    have h2 : ‖g y hy‖ < 1 := by simpa using hg y hy
    calc ‖v‖ ≤ ‖x‖ + ‖g y hy‖ := norm_sub_le _ _
      _ < 2 := by linarith
  have hT2v : ‖(T ∘L T) v‖ < ε ^ 2 / 2 := by
    rw [map_sub, hgy y hy, ← dist_eq_norm]; exact hxy
  have hsq : ‖T v‖ ^ 2 ≤ ‖(T ∘L T) v‖ * ‖v‖ := by
    have h1 : ‖T v‖ ^ 2 = RCLike.re (inner ℂ (T v) (T v)) := by
      rw [← inner_self_eq_norm_sq]
    have h2 : inner ℂ (T v) (T v) = inner ℂ ((T ∘L T) v) v := by
      rw [ContinuousLinearMap.comp_apply]; exact (hT.isSymmetric (T v) v).symm
    rw [h1, h2]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hlt : ‖T v‖ ^ 2 < ε ^ 2 := by
    calc ‖T v‖ ^ 2 ≤ ‖(T ∘L T) v‖ * ‖v‖ := hsq
      _ ≤ ‖(T ∘L T) v‖ * 2 := mul_le_mul_of_nonneg_left hv.le (norm_nonneg _)
      _ < ε ^ 2 / 2 * 2 := by nlinarith [norm_nonneg ((T ∘L T) v)]
      _ = ε ^ 2 := by ring
  have hTv : ‖T v‖ < ε := (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hlt
  show dist (T x) (T (g y hy)) < ε
  rw [dist_eq_norm, ← map_sub]
  exact hTv

/-- The difference kernel is bounded by `C (1 + u)^{−a}`. -/
theorem exists_diffKernel_le {a s : ℝ} (ha : 1 < a) (has : a ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → diffKernel a s u ≤ C * (1 + u) ^ (-a) := by
  have ha' : 1 / 2 < a := by linarith
  obtain ⟨C₁, hC₁, hC⟩ := exists_resKernel_le_rpow_neg ha'
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    (continuous_diffKernel ha' has).continuousOn
  have hM₀' : 0 ≤ M₀ := le_trans (diffKernel_nonneg has 0) (hM₀ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
  refine ⟨(M₀ + C₁) * 2 ^ a, by positivity, fun u hu => ?_⟩
  have hpos : 0 < (1 + u) ^ (-a) := Real.rpow_pos_of_pos (by linarith) _
  rcases le_total u 1 with h | h
  · have h1 : diffKernel a s u ≤ M₀ := hM₀ ⟨u, ⟨hu, h⟩, rfl⟩
    have h2 : 2 ^ (-a) ≤ (1 + u) ^ (-a) := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
      (by linarith)
    have h3 : (2 : ℝ) ^ a * 2 ^ (-a) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
    calc diffKernel a s u ≤ M₀ := h1
      _ = M₀ * 2 ^ a * 2 ^ (-a) := by rw [mul_assoc, h3, mul_one]
      _ ≤ (M₀ + C₁) * 2 ^ a * (1 + u) ^ (-a) := by
          have : M₀ * 2 ^ a ≤ (M₀ + C₁) * 2 ^ a := by
            have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) a; nlinarith
          calc M₀ * 2 ^ a * 2 ^ (-a) ≤ M₀ * 2 ^ a * (1 + u) ^ (-a) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
            _ ≤ (M₀ + C₁) * 2 ^ a * (1 + u) ^ (-a) := mul_le_mul_of_nonneg_right this hpos.le
  · have hu0 : 0 < u := by linarith
    have h1 := (ofReal_diffKernel_le ha' has hu0).trans (hC u hu0)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    have h2 : u ^ (-a) ≤ 2 ^ a * (1 + u) ^ (-a) := by
      have h3 := Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < 1 + u) (show 1 + u ≤ 2 * u by linarith)
        (show -a ≤ 0 by linarith)
      rw [Real.mul_rpow (by norm_num) hu0.le] at h3
      have h4 : (2 : ℝ) ^ a * 2 ^ (-a) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
      calc u ^ (-a) = 2 ^ a * (2 ^ (-a) * u ^ (-a)) := by rw [← mul_assoc, h4, one_mul]
        _ ≤ 2 ^ a * (1 + u) ^ (-a) := mul_le_mul_of_nonneg_left h3 (by positivity)
    calc diffKernel a s u ≤ C₁ * u ^ (-a) := h1
      _ ≤ C₁ * (2 ^ a * (1 + u) ^ (-a)) := mul_le_mul_of_nonneg_left h2 hC₁
      _ ≤ (M₀ + C₁) * 2 ^ a * (1 + u) ^ (-a) := by
          have : C₁ * 2 ^ a ≤ (M₀ + C₁) * 2 ^ a := by
            have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) a; nlinarith
          nlinarith

namespace CompactQuotient

variable (X : CompactQuotient)

/-- `T_a − T_s` is compact. -/
theorem isCompactOperator_diffOp {a s : ℝ} (ha : 1 < a) (has : a < s) :
    IsCompactOperator (X.diffOp ha has) := by
  obtain ⟨C, hC0, hC⟩ := exists_diffKernel_le ha has.le
  obtain ⟨M, hM, hle⟩ := X.cocompactFree.exists_autK_le ha
  have hb : ∀ z w : ℍ, autK X.Γ (diffProfile a s) z w ≤ ENNReal.ofReal C * M := fun z w =>
    hle (k := diffProfile a s) (C := C) (fun u hu => ENNReal.ofReal_le_ofReal (hC u hu)) z w
  refine ContinuousLinearMap.IsHilbertSchmidt.isCompactOperator (isHilbertSchmidt_op _ ?_)
  have hpt : ∀ z w : ℍ, ‖(X.profileKernel (measurable_diffProfile ha has)
      (lintegral_diffProfile_mass_lt_top ha has)).toFun z w‖ₑ ^ 2 ≤ (ENNReal.ofReal C * M) ^ 2 := by
    intro z w
    refine pow_le_pow_left₀ bot_le ?_ 2
    rw [profileKernel_toFun, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le.trans (hb z w)
  calc ∫⁻ z in X.F, ∫⁻ w in X.F, ‖(X.profileKernel (measurable_diffProfile ha has)
        (lintegral_diffProfile_mass_lt_top ha has)).toFun z w‖ₑ ^ 2
      ≤ ∫⁻ z in X.F, ∫⁻ w in X.F, (ENNReal.ofReal C * M) ^ 2 :=
        lintegral_mono fun z => lintegral_mono fun w => hpt z w
    _ = (ENNReal.ofReal C * M) ^ 2 * volume X.F * volume X.F := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM)) X.volume_F_lt_top) X.volume_F_lt_top

/-- **The resolvent operators are compact.** -/
theorem isCompactOperator_resOp {a : ℝ} (ha : 1 < a) : IsCompactOperator (X.resOp ha) := by
  set s := a + 1
  have has : a < s := by simp [s]
  have hs : 1 < s := lt_trans ha has
  set c : ℝ := s * (s - 1) - a * (a - 1)
  have hc : 0 < c := resConst_pos ha has
  have hcomp := X.resOp_comp ha has
  have hsub := X.resOp_sub ha has
  have hP : IsCompactOperator (X.resOp hs ∘L X.resOp ha) := by
    rw [hcomp, hsub]
    exact (X.isCompactOperator_diffOp ha has).smul (((1 / (s * (s - 1) - a * (a - 1)) : ℝ) : ℂ))
  have hP' : IsCompactOperator (X.resOp ha ∘L X.resOp hs) := by
    rw [X.resOp_comm ha has]; exact hP
  -- `T_a = T_s + c T_s T_a`
  have hTa : X.resOp ha = X.resOp hs + (c : ℂ) • (X.resOp hs ∘L X.resOp ha) := by
    rw [hcomp, smul_smul]
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have : (c : ℂ) * ((1 / c : ℝ) : ℂ) = 1 := by
      push_cast; field_simp
    rw [this, one_smul]; abel
  have hsq : IsCompactOperator (X.resOp ha ∘L X.resOp ha) := by
    have : X.resOp ha ∘L X.resOp ha =
        X.resOp ha ∘L X.resOp hs + (c : ℂ) • ((X.resOp ha ∘L X.resOp hs) ∘L X.resOp ha) := by
      conv_lhs => rw [show X.resOp ha ∘L X.resOp ha = X.resOp ha ∘L (X.resOp hs +
        (c : ℂ) • (X.resOp hs ∘L X.resOp ha)) from by rw [← hTa]]
      rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
      rfl
    rw [this]
    exact hP'.add ((hP'.comp_clm (X.resOp ha)).smul _)
  exact isCompactOperator_of_comp_self (X.isSelfAdjoint_resOp ha) hsq

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
