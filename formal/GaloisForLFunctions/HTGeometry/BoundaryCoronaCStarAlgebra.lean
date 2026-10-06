import GaloisForLFunctions.HTGeometry.BoundaryHistoryCorona
import GaloisForLFunctions.HTGeometry.CompactAdjoint

/-!
# The boundary-history corona is a C⋆-algebra

The compact operators `K(H)` form a non-unital C⋆-algebra (adjoints of compact operators are
compact), hence so do the bounded continuous aperture histories `C_b((0,1], K(H))`.  The histories
vanishing at the closing aperture form a closed two-sided `*`-ideal, so the boundary-history corona
`Q = C_b((0,1], K(H))/C_0((0,1], K(H))` inherits multiplication, scalars and adjoint.  Its quotient
norm is `‖[F]‖ = limsup_{ε → 0+} ‖F(ε)‖`, which gives submultiplicativity
(`limsup uv ≤ limsup u · limsup v` for nonnegative bounded `u, v`) and the C⋆-identity
(`limsup ‖F(ε)‖² = (limsup ‖F(ε)‖)²`).  Hence `Q` is a non-unital C⋆-algebra.
-/

set_option autoImplicit false

open Filter Topology Set ContinuousLinearMap
open scoped BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The C⋆-algebra of compact operators -/

namespace CompactOps

theorem op_injective : Function.Injective (op : CompactOps H → H →L[ℂ] H) :=
  Subtype.val_injective

theorem isCompactOperator_op (x : CompactOps H) : IsCompactOperator x.op := x.2

instance : Mul (CompactOps H) :=
  ⟨fun x y => mk (x.op * y.op) ((isCompactOperator_op x).comp_clm y.op)⟩

@[simp] theorem op_mul (x y : CompactOps H) : (x * y).op = x.op * y.op := rfl
@[simp] theorem op_zero : (0 : CompactOps H).op = 0 := rfl
@[simp] theorem op_add (x y : CompactOps H) : (x + y).op = x.op + y.op := rfl
@[simp] theorem op_neg (x : CompactOps H) : (-x).op = -x.op := rfl
@[simp] theorem op_sub' (x y : CompactOps H) : (x - y).op = x.op - y.op := rfl
@[simp] theorem op_smulC (c : ℂ) (x : CompactOps H) : (c • x).op = c • x.op := rfl
@[simp] theorem op_nsmul (n : ℕ) (x : CompactOps H) : (n • x).op = n • x.op := rfl
@[simp] theorem op_zsmul (n : ℤ) (x : CompactOps H) : (n • x).op = n • x.op := rfl

instance : NonUnitalRing (CompactOps H) where
  __ := (inferInstance : AddCommGroup (CompactOps H))
  left_distrib x y z := op_injective (by simp [mul_add])
  right_distrib x y z := op_injective (by simp [add_mul])
  zero_mul x := op_injective (by simp)
  mul_zero x := op_injective (by simp)
  mul_assoc x y z := op_injective (by simp [mul_assoc])

instance : NonUnitalNormedRing (CompactOps H) where
  __ := (inferInstance : NormedAddCommGroup (CompactOps H))
  __ := (inferInstance : NonUnitalRing (CompactOps H))
  norm_mul_le x y := norm_mul_le x.op y.op

instance : IsScalarTower ℂ (CompactOps H) (CompactOps H) :=
  ⟨fun c x y => op_injective (by simp)⟩

instance : SMulCommClass ℂ (CompactOps H) (CompactOps H) :=
  ⟨fun c x y => op_injective (by simp)⟩

variable [CompleteSpace H]

instance : Star (CompactOps H) :=
  ⟨fun x => mk (adjoint x.op) (isCompactOperator_adjoint_rectangular _ (isCompactOperator_op x))⟩

@[simp] theorem op_star (x : CompactOps H) : (star x).op = adjoint x.op := rfl

instance : StarRing (CompactOps H) where
  star_involutive x := op_injective (by simp)
  star_mul x y := op_injective (by simp [mul_def, adjoint_comp])
  star_add x y := op_injective (by simp)

instance : NormedStarGroup (CompactOps H) :=
  ⟨fun x => by simp only [CompactOps.norm_eq, op_star, LinearIsometryEquiv.norm_map, le_refl]⟩

instance : CStarRing (CompactOps H) :=
  ⟨fun x => by
    have h := CStarRing.norm_star_mul_self (x := x.op)
    simp only [CompactOps.norm_eq, op_mul, op_star, ← star_eq_adjoint]
    exact h.ge⟩

instance : StarModule ℂ (CompactOps H) :=
  ⟨fun c x => op_injective (by simp [← star_eq_adjoint, star_smul])⟩

instance : CompleteSpace (CompactOps H) :=
  (isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := H) (M₂ := H)).completeSpace_coe

instance : NonUnitalCStarAlgebra (CompactOps H) where

end CompactOps

/-! ## Histories and the corona -/

variable [CompleteSpace H]

theorem mem_vanishingHistories {F : ApertureHistory H} :
    F ∈ vanishingHistories H ↔ Tendsto (fun ε => ‖F ε‖) apertureClosing (𝓝 0) := Iff.rfl

theorem mul_mem_vanishingHistories_left (G : ApertureHistory H) {F : ApertureHistory H}
    (hF : F ∈ vanishingHistories H) : G * F ∈ vanishingHistories H := by
  refine squeeze_zero (fun _ => norm_nonneg _) (fun ε => ?_) (by simpa using hF.const_mul ‖G‖)
  calc ‖(G * F) ε‖ = ‖G ε * F ε‖ := rfl
    _ ≤ ‖G ε‖ * ‖F ε‖ := norm_mul_le _ _
    _ ≤ ‖G‖ * ‖F ε‖ := mul_le_mul_of_nonneg_right (norm_history_le G ε) (norm_nonneg _)

theorem mul_mem_vanishingHistories_right (G : ApertureHistory H) {F : ApertureHistory H}
    (hF : F ∈ vanishingHistories H) : F * G ∈ vanishingHistories H := by
  refine squeeze_zero (fun _ => norm_nonneg _) (fun ε => ?_) (by simpa using hF.mul_const ‖G‖)
  calc ‖(F * G) ε‖ = ‖F ε * G ε‖ := rfl
    _ ≤ ‖F ε‖ * ‖G ε‖ := norm_mul_le _ _
    _ ≤ ‖F ε‖ * ‖G‖ := mul_le_mul_of_nonneg_left (norm_history_le G ε) (norm_nonneg _)

theorem star_mem_vanishingHistories {F : ApertureHistory H} (hF : F ∈ vanishingHistories H) :
    star F ∈ vanishingHistories H := by
  have : (fun ε => ‖(star F) ε‖) = fun ε => ‖F ε‖ := funext fun ε => norm_star (F ε)
  rw [mem_vanishingHistories, this]; exact hF

theorem smul_mem_vanishingHistories (c : ℂ) {F : ApertureHistory H}
    (hF : F ∈ vanishingHistories H) : c • F ∈ vanishingHistories H := by
  have : (fun ε => ‖(c • F) ε‖) = fun ε => ‖c‖ * ‖F ε‖ := funext fun ε => norm_smul c (F ε)
  rw [mem_vanishingHistories, this]; simpa using hF.const_mul ‖c‖

instance isClosed_vanishingHistories :
    IsClosed (vanishingHistories H : Set (ApertureHistory H)) := by
  refine isClosed_of_closure_subset fun F hF => ?_
  change Tendsto (fun ε => ‖F ε‖) apertureClosing (𝓝 0)
  rw [Metric.tendsto_nhds]
  intro r hr
  obtain ⟨G, hG, hFG⟩ := Metric.mem_closure_iff.mp hF (r / 2) (half_pos hr)
  filter_upwards [(Metric.tendsto_nhds.mp (show G ∈ vanishingHistories H from hG)) (r / 2)
    (half_pos hr)] with ε hε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hε ⊢
  calc ‖F ε‖ ≤ ‖F ε - G ε‖ + ‖G ε‖ := norm_le_norm_sub_add _ _
    _ ≤ dist F G + ‖G ε‖ := by
        gcongr
        rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist ε
    _ < r / 2 + r / 2 := add_lt_add hFG hε
    _ = r := add_halves r

/-! ## Limits superior of products -/

section Limsup

variable {ι : Type*} {L : Filter ι} [L.NeBot] {u v : ι → ℝ}

theorem limsup_nonneg_of_nonneg (hu0 : ∀ i, 0 ≤ u i) (hub : L.IsBoundedUnder (· ≤ ·) u) :
    0 ≤ limsup u L :=
  le_limsup_of_frequently_le (Frequently.of_forall hu0) hub

theorem limsup_mul_le_mul_limsup (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i)
    (hub : L.IsBoundedUnder (· ≤ ·) u) (hvb : L.IsBoundedUnder (· ≤ ·) v) :
    limsup (fun i => u i * v i) L ≤ limsup u L * limsup v L := by
  set a := limsup u L
  set b := limsup v L
  have ha := limsup_nonneg_of_nonneg hu0 hub
  have hb := limsup_nonneg_of_nonneg hv0 hvb
  have hbound : ∀ δ > 0, limsup (fun i => u i * v i) L ≤ (a + δ) * (b + δ) := fun δ hδ => by
    have h1 := eventually_lt_of_limsup_lt (lt_add_of_pos_right a hδ) hub
    have h2 := eventually_lt_of_limsup_lt (lt_add_of_pos_right b hδ) hvb
    refine limsup_le_of_le (isCoboundedUnder_le_of_le L fun i => mul_nonneg (hu0 i) (hv0 i)) ?_
    filter_upwards [h1, h2] with i hi1 hi2
    exact mul_le_mul hi1.le hi2.le (hv0 i) (by linarith)
  have ht : Tendsto (fun δ : ℝ => (a + δ) * (b + δ)) (𝓝[>] 0) (𝓝 (a * b)) := by
    have := ((continuous_const.add continuous_id).mul
      (continuous_const.add continuous_id)).tendsto (0 : ℝ) (f := fun δ : ℝ => (a + δ) * (b + δ))
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hbound δ hδ)

theorem limsup_const_mul_of_nonneg {c : ℝ} (hc : 0 ≤ c)
    (hub : L.IsBoundedUnder (· ≤ ·) u) (hucb : L.IsCoboundedUnder (· ≤ ·) u) :
    limsup (fun i => c * u i) L = c * limsup u L := by
  have h := (Monotone.const_mul monotone_id hc).map_limsup_of_continuousAt u
    (continuous_const.mul continuous_id).continuousAt hub hucb
  simpa [Function.comp_def] using h.symm

theorem limsup_sq_of_nonneg (hu0 : ∀ i, 0 ≤ u i) (hub : L.IsBoundedUnder (· ≤ ·) u)
    (hucb : L.IsCoboundedUnder (· ≤ ·) u) :
    limsup (fun i => u i * u i) L = limsup u L * limsup u L := by
  have hmono : Monotone fun t : ℝ => max t 0 * max t 0 := fun x y hxy =>
    mul_le_mul (max_le_max hxy le_rfl) (max_le_max hxy le_rfl) (le_max_right _ _)
      (le_max_right _ _ |>.trans (max_le_max hxy le_rfl))
  have h := hmono.map_limsup_of_continuousAt u
    ((continuous_id.max continuous_const).mul (continuous_id.max continuous_const)).continuousAt
    hub hucb
  have hl := limsup_nonneg_of_nonneg hu0 hub
  simp only [max_eq_left hl] at h
  rw [h]
  congr 1
  funext i
  simp [max_eq_left (hu0 i)]

end Limsup

/-! ## Algebraic structure of the corona -/

namespace BoundaryCorona

/-- Products of histories respect the vanishing ideal on both sides. -/
theorem mul_rel_mem {a a' b b' : ApertureHistory H} (ha : -a + a' ∈ vanishingHistories H)
    (hb : -b + b' ∈ vanishingHistories H) : -(a * b) + a' * b' ∈ vanishingHistories H := by
  rw [mem_vanishingHistories] at ha hb ⊢
  have hpt : ∀ ε, ‖(-(a * b) + a' * b') ε‖ ≤
      ‖(-a + a') ε‖ * ‖b'‖ + ‖a‖ * ‖(-b + b') ε‖ := fun ε => by
    change ‖-(a ε * b ε) + a' ε * b' ε‖ ≤ ‖-a ε + a' ε‖ * ‖b'‖ + ‖a‖ * ‖-b ε + b' ε‖
    have e : -(a ε * b ε) + a' ε * b' ε = (-a ε + a' ε) * b' ε + a ε * (-b ε + b' ε) := by
      noncomm_ring
    rw [e]
    calc ‖(-a ε + a' ε) * b' ε + a ε * (-b ε + b' ε)‖
        ≤ ‖-a ε + a' ε‖ * ‖b' ε‖ + ‖a ε‖ * ‖-b ε + b' ε‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖-a ε + a' ε‖ * ‖b'‖ + ‖a‖ * ‖-b ε + b' ε‖ := by
          gcongr
          · exact norm_history_le b' ε
          · exact norm_history_le a ε
  refine squeeze_zero (fun _ => norm_nonneg _) hpt ?_
  simpa using (ha.mul_const ‖b'‖).add (hb.const_mul ‖a‖)

instance : Mul (BoundaryCorona H) where
  mul := Quotient.map₂ (· * ·) fun _ _ ha _ _ hb =>
    QuotientAddGroup.leftRel_apply.mpr (mul_rel_mem (QuotientAddGroup.leftRel_apply.mp ha)
      (QuotientAddGroup.leftRel_apply.mp hb))

instance : SMul ℂ (BoundaryCorona H) where
  smul c := Quotient.map (c • ·) fun a a' ha => by
    replace ha := QuotientAddGroup.leftRel_apply.mp ha
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    rw [show -(c • a) + c • a' = c • (-a + a') by rw [smul_add, smul_neg]]
    exact smul_mem_vanishingHistories c ha

instance : Star (BoundaryCorona H) where
  star := Quotient.map star fun a a' ha => by
    replace ha := QuotientAddGroup.leftRel_apply.mp ha
    refine QuotientAddGroup.leftRel_apply.mpr ?_
    rw [show -(star a) + star a' = star (-a + a') by rw [star_add, star_neg]]
    exact star_mem_vanishingHistories ha

theorem mk_mul (F G : ApertureHistory H) :
    ((F * G : ApertureHistory H) : BoundaryCorona H) = (F : BoundaryCorona H) * G := rfl

theorem mk_smul (c : ℂ) (F : ApertureHistory H) :
    ((c • F : ApertureHistory H) : BoundaryCorona H) = c • (F : BoundaryCorona H) := rfl

theorem mk_star (F : ApertureHistory H) :
    ((star F : ApertureHistory H) : BoundaryCorona H) = star (F : BoundaryCorona H) := rfl

theorem mk_surjective : Function.Surjective ((↑) : ApertureHistory H → BoundaryCorona H) :=
  QuotientAddGroup.mk_surjective

instance : NonUnitalRing (BoundaryCorona H) where
  __ := (inferInstance : AddCommGroup (BoundaryCorona H))
  left_distrib x y z := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    obtain ⟨K, rfl⟩ := mk_surjective z
    simp only [← QuotientAddGroup.mk_add, ← mk_mul, mul_add]
  right_distrib x y z := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    obtain ⟨K, rfl⟩ := mk_surjective z
    simp only [← QuotientAddGroup.mk_add, ← mk_mul, add_mul]
  zero_mul x := by
    obtain ⟨F, rfl⟩ := mk_surjective x
    rw [← QuotientAddGroup.mk_zero, ← mk_mul, zero_mul]
  mul_zero x := by
    obtain ⟨F, rfl⟩ := mk_surjective x
    rw [← QuotientAddGroup.mk_zero, ← mk_mul, mul_zero]
  mul_assoc x y z := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    obtain ⟨K, rfl⟩ := mk_surjective z
    simp only [← mk_mul, mul_assoc]

instance : Module ℂ (BoundaryCorona H) where
  one_smul x := by obtain ⟨F, rfl⟩ := mk_surjective x; rw [← mk_smul, one_smul]
  mul_smul a b x := by obtain ⟨F, rfl⟩ := mk_surjective x; simp only [← mk_smul, mul_smul]
  smul_zero a := by rw [← QuotientAddGroup.mk_zero, ← mk_smul, smul_zero]
  smul_add a x y := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    simp only [← QuotientAddGroup.mk_add, ← mk_smul, smul_add]
  add_smul a b x := by
    obtain ⟨F, rfl⟩ := mk_surjective x
    simp only [← QuotientAddGroup.mk_add, ← mk_smul, add_smul]
  zero_smul x := by obtain ⟨F, rfl⟩ := mk_surjective x; rw [← mk_smul, zero_smul]; rfl

instance : IsScalarTower ℂ (BoundaryCorona H) (BoundaryCorona H) :=
  ⟨fun c x y => by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    simp only [smul_eq_mul, ← mk_smul, ← mk_mul, smul_mul_assoc]⟩

instance : SMulCommClass ℂ (BoundaryCorona H) (BoundaryCorona H) :=
  ⟨fun c x y => by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    simp only [smul_eq_mul, ← mk_smul, ← mk_mul, mul_smul_comm]⟩

instance : StarRing (BoundaryCorona H) where
  star_involutive x := by obtain ⟨F, rfl⟩ := mk_surjective x; simp only [← mk_star, star_star]
  star_mul x y := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    rw [← mk_star, ← mk_star, ← mk_mul, ← mk_mul, ← mk_star]
    congr 1
    ext ε : 1
    change star (F ε * G ε) = star (G ε) * star (F ε)
    exact star_mul _ _
  star_add x y := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    simp only [← mk_star, ← QuotientAddGroup.mk_add, star_add]

instance : StarModule ℂ (BoundaryCorona H) :=
  ⟨fun c x => by
    obtain ⟨F, rfl⟩ := mk_surjective x
    simp only [← mk_star, ← mk_smul, star_smul]⟩

theorem norm_mk (F : ApertureHistory H) :
    ‖(F : BoundaryCorona H)‖ = limsup (fun ε => ‖F ε‖) apertureClosing :=
  norm_boundaryCorona_mk F

instance : NonUnitalNormedRing (BoundaryCorona H) where
  __ := (inferInstance : NormedAddCommGroup (BoundaryCorona H))
  __ := (inferInstance : NonUnitalRing (BoundaryCorona H))
  norm_mul_le x y := by
    obtain ⟨F, rfl⟩ := mk_surjective x; obtain ⟨G, rfl⟩ := mk_surjective y
    rw [← mk_mul, norm_mk, norm_mk, norm_mk]
    refine (limsup_le_limsup (Eventually.of_forall fun ε => ?_)
      (isCoboundedUnder_norm_history _) ?_).trans
      (limsup_mul_le_mul_limsup (fun ε => norm_nonneg (F ε)) (fun ε => norm_nonneg (G ε))
        (isBoundedUnder_norm_history F) (isBoundedUnder_norm_history G))
    · exact norm_mul_le (F ε) (G ε)
    · exact isBoundedUnder_of ⟨‖F‖ * ‖G‖, fun ε => mul_le_mul (norm_history_le F ε)
        (norm_history_le G ε) (norm_nonneg _) (norm_nonneg _)⟩

instance : NormedSpace ℂ (BoundaryCorona H) where
  norm_smul_le c x := by
    obtain ⟨F, rfl⟩ := mk_surjective x
    rw [← mk_smul, norm_mk, norm_mk]
    have : (fun ε => ‖(c • F) ε‖) = fun ε => ‖c‖ * ‖F ε‖ :=
      funext fun ε => norm_smul c (F ε)
    rw [this, limsup_const_mul_of_nonneg (norm_nonneg c)
      (isBoundedUnder_norm_history F) (isCoboundedUnder_norm_history F)]

instance : NormedStarGroup (BoundaryCorona H) :=
  ⟨fun x => by
    obtain ⟨F, rfl⟩ := mk_surjective x
    rw [← mk_star, norm_mk, norm_mk]
    have : (fun ε => ‖(star F) ε‖) = fun ε => ‖F ε‖ := funext fun ε => norm_star (F ε)
    rw [this]⟩

instance : CStarRing (BoundaryCorona H) :=
  ⟨fun x => by
    obtain ⟨F, rfl⟩ := mk_surjective x
    rw [← mk_star, ← mk_mul, norm_mk, norm_mk]
    have : (fun ε => ‖(star F * F) ε‖) = fun ε => ‖F ε‖ * ‖F ε‖ :=
      funext fun ε => CStarRing.norm_star_mul_self (x := F ε)
    rw [this, limsup_sq_of_nonneg (fun ε => norm_nonneg (F ε)) (isBoundedUnder_norm_history F)
      (isCoboundedUnder_norm_history F)]⟩

/-- **The boundary-history corona is a non-unital C⋆-algebra.** -/
instance : NonUnitalCStarAlgebra (BoundaryCorona H) where

end BoundaryCorona

end GaloisForLFunctions.HTGeometry
