import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Algebra.DualNumber
import Mathlib.Data.ZMod.Basic

/-!
# Functional-equation fixed responses as a reflection space

For an involutive automorphism `θ` of a group `G`, the twisted reversal `ρ(g) = θ(g⁻¹)` has fixed
set `Q_θ = {g : θ g = g⁻¹}`.

* `Q_θ` is closed under `x ▷ y = x y⁻¹ x`, which satisfies the reflection identities, while the
  ordinary product of fixed elements is reversed, `ρ(xy) = yx`; it is fixed exactly when the
  factors commute, measured by the exchange defect `Ξ(x, y) = (xy)⁻¹ yx`.
* The transvection `τ_x = s_x ∘ s_e : y ↦ xyx` has orbit `τ_x^n(e) = x^{2n}`; a length
  homogeneous on `⟨x⟩` has bounded transvection history exactly when it vanishes at `x`.
* For finitely many unitary involutions `Θ_j` of a Hilbert space, the joint reversal response
  `𝒜X = ((I + Θ_j)X)_j` satisfies `‖𝒜X‖² = ∑‖X + Θ_jX‖²`, `𝒜*𝒜 = 2∑(I + Θ_j)`,
  `ker 𝒜 = ker 𝒜*𝒜 = ⋂ ker(I + Θ_j)`.  The properness estimate `∑‖X + Θ_jX‖² ≥ α‖X‖²` holds for
  some `α > 0` exactly when `𝒜` is injective with closed range, and in finite dimension exactly
  when the common odd sector vanishes; under it, vanishing defects force convergence to zero.
* In characteristic two, `(1 + ε)² = 1` with `1 + ε ≠ 1`.
-/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-! ## The group-level reflection space -/

section Group

variable {G : Type*} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g)

/-- The twisted reversal `ρ(g) = θ(g⁻¹)`. -/
def twistedReversalGroup (g : G) : G := θ g⁻¹

/-- **(CRS.4)** `ρ(g) = g ⟺ θ(g) = g⁻¹`. -/
theorem twistedReversalGroup_eq_iff (g : G) : twistedReversalGroup θ g = g ↔ θ g = g⁻¹ := by
  rw [twistedReversalGroup, map_inv, inv_eq_iff_eq_inv]

/-- Reflection fusion `x ▷ y = x y⁻¹ x`. -/
def groupFusion (x y : G) : G := x * y⁻¹ * x

/-- **Theorem 2.1 (CRS.5)** `Q_θ` is closed under reflection fusion. -/
theorem groupFusion_mem {x y : G} (hx : θ x = x⁻¹) (hy : θ y = y⁻¹) :
    θ (groupFusion x y) = (groupFusion x y)⁻¹ := by
  simp only [groupFusion, map_mul, map_inv, hx, hy, mul_inv_rev, inv_inv, mul_assoc]

/-- **(CRS.6)** `x ▷ x = x` and `x ▷ (x ▷ y) = y`. -/
theorem groupFusion_self (x y : G) : groupFusion x x = x ∧ groupFusion x (groupFusion x y) = y := by
  constructor <;> simp only [groupFusion] <;> group

/-- **(CRS.7)** `x ▷ (y ▷ z) = (x ▷ y) ▷ (x ▷ z)`: every `s_x` is an automorphism of fusion. -/
theorem groupFusion_left_distrib (x y z : G) :
    groupFusion x (groupFusion y z) = groupFusion (groupFusion x y) (groupFusion x z) := by
  simp only [groupFusion]; group

/-- **(CRS.8)** `ρ(xy) = yx` for `x, y ∈ Q_θ`. -/
theorem twistedReversalGroup_mul {x y : G} (hx : θ x = x⁻¹) (hy : θ y = y⁻¹) :
    twistedReversalGroup θ (x * y) = y * x := by
  rw [twistedReversalGroup, mul_inv_rev, map_mul, map_inv, map_inv, hx, hy, inv_inv, inv_inv]

/-- **(CRS.9)** `xy ∈ Q_θ ⟺ xy = yx`. -/
theorem mul_mem_iff {x y : G} (hx : θ x = x⁻¹) (hy : θ y = y⁻¹) :
    θ (x * y) = (x * y)⁻¹ ↔ x * y = y * x := by
  rw [← twistedReversalGroup_eq_iff, twistedReversalGroup_mul θ hx hy]
  exact eq_comm

/-- The ordinary-formation exchange defect `Ξ(x, y) = (xy)⁻¹ ρ(xy)`. -/
def exchangeDefect (x y : G) : G := (x * y)⁻¹ * twistedReversalGroup θ (x * y)

/-- **(CRS.10)** `Ξ(x, y) = (xy)⁻¹ yx`, trivial exactly when `xy = yx`. -/
theorem exchangeDefect_eq {x y : G} (hx : θ x = x⁻¹) (hy : θ y = y⁻¹) :
    exchangeDefect θ x y = (x * y)⁻¹ * (y * x) ∧ (exchangeDefect θ x y = 1 ↔ x * y = y * x) := by
  have h := twistedReversalGroup_mul θ hx hy
  refine ⟨by rw [exchangeDefect, h], ?_⟩
  rw [exchangeDefect, h, inv_mul_eq_one]

/-! ## Transvections -/

/-- The transvection `τ_x = s_x ∘ s_e : y ↦ x y x`. -/
def groupTransvection (x : G) : Equiv.Perm G where
  toFun y := x * y * x
  invFun y := x⁻¹ * y * x⁻¹
  left_inv y := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]

/-- **(CRS.11)** `τ_x = s_x ∘ s_e`. -/
theorem transvection_eq_fusion (x y : G) :
    groupTransvection x y = groupFusion x (groupFusion 1 y) := by
  simp [groupTransvection, groupFusion]

theorem transvection_zpow_apply (x y : G) (n : ℤ) :
    (groupTransvection x ^ n) y = x ^ n * y * x ^ n := by
  induction n using Int.induction_on generalizing y with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.mul_apply, ih]
    simp only [groupTransvection, Equiv.coe_fn_mk]
    group
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.mul_apply, ih]
    simp only [groupTransvection, Equiv.Perm.inv_def, Equiv.coe_fn_symm_mk]
    group

/-- **Theorem 3.1 (CRS.12)** `τ_x^n(e) = x^{2n}`. -/
theorem transvection_zpow_one (x : G) (n : ℤ) : (groupTransvection x ^ n) 1 = x ^ (2 * n) := by
  rw [transvection_zpow_apply, mul_one, ← zpow_add, two_mul]

/-- **Theorem 3.1 (CRS.13)–(CRS.14)** For a nonnegative length homogeneous on `⟨x⟩`, the
transvection history is bounded exactly when the length of `x` vanishes. -/
theorem bddAbove_transvection_iff (L : G → ℝ) (hL0 : ∀ g, 0 ≤ L g) (x : G)
    (hL : ∀ n : ℤ, L (x ^ n) = |(n : ℝ)| * L x) :
    BddAbove (Set.range fun n : ℤ => L ((groupTransvection x ^ n) 1)) ↔ L x = 0 := by
  simp_rw [transvection_zpow_one, hL]
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have hpos : 0 < L x := lt_of_le_of_ne (hL0 x) (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_nat_gt (C / (2 * L x))
    have h := hC ⟨(n : ℤ), rfl⟩
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] at h
    rw [abs_of_nonneg (by positivity)] at h
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  · intro h
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    simp [h]

/-- **Theorem 3.1** If the length separates the identity on `Q_θ`, bounded transvection history
selects `x = e`. -/
theorem eq_one_of_bddAbove_transvection (L : G → ℝ) (hL0 : ∀ g, 0 ≤ L g) {x : G}
    (hx : θ x = x⁻¹) (hsep : ∀ y, θ y = y⁻¹ → L y = 0 → y = 1)
    (hL : ∀ n : ℤ, L (x ^ n) = |(n : ℝ)| * L x)
    (hb : BddAbove (Set.range fun n : ℤ => L ((groupTransvection x ^ n) 1))) : x = 1 :=
  hsep x hx ((bddAbove_transvection_iff L hL0 x hL).1 hb)

end Group

/-! ## The joint reversal Gramian -/

section Gramian

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] {J : Type*} [Fintype J]
variable (Θ : J → V →L[𝕜] V)

/-- **(CRS.31)** The joint reversal response `𝒜X = ((I + Θ_j)X)_j`. -/
def jointReversal : V →L[𝕜] PiLp 2 (fun _ : J => V) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : J => V)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => 1 + Θ j)

omit [CompleteSpace V] [Fintype J] in
theorem jointReversal_apply (X : V) (j : J) : (jointReversal Θ X).ofLp j = X + Θ j X := rfl

omit [CompleteSpace V] in
/-- **(CRS.33)** `‖𝒜X‖² = ∑_j ‖X + Θ_jX‖²`. -/
theorem norm_jointReversal_sq (X : V) : ‖jointReversal Θ X‖ ^ 2 = ∑ j, ‖X + Θ j X‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]; rfl

variable {Θ}
variable (hU : ∀ j, ContinuousLinearMap.adjoint (Θ j) ∘L Θ j = 1) (hI : ∀ j, Θ j ∘L Θ j = 1)

omit [Fintype J] in
include hU hI in
/-- A unitary involution is self-adjoint. -/
theorem adjoint_reversal_eq (j : J) : ContinuousLinearMap.adjoint (Θ j) = Θ j := by
  calc ContinuousLinearMap.adjoint (Θ j) = ContinuousLinearMap.adjoint (Θ j) ∘L (Θ j ∘L Θ j) := by
        rw [hI j]; rfl
    _ = (ContinuousLinearMap.adjoint (Θ j) ∘L Θ j) ∘L Θ j := rfl
    _ = Θ j := by rw [hU j]; rfl

include hU hI in
/-- **(CRS.34)** `𝒜*𝒜 = 2∑_j (I + Θ_j)`. -/
theorem adjoint_jointReversal_comp :
    ContinuousLinearMap.adjoint (jointReversal Θ) ∘L jointReversal Θ =
      (2 : 𝕜) • ∑ j, (1 + Θ j) := by
  refine ContinuousLinearMap.ext fun X => ext_inner_right 𝕜 fun Y => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  simp only [jointReversal_apply, smul_apply, sum_apply, inner_smul_left, sum_inner, add_apply,
    one_apply_eq_self, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsa := adjoint_reversal_eq hU hI j
  have h1 : inner 𝕜 (Θ j X) (Θ j Y) = inner 𝕜 X Y := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, hU j]; rfl
  have h2 : inner 𝕜 (Θ j X) Y = inner 𝕜 X (Θ j Y) := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa]
  rw [inner_add_left, inner_add_right, inner_add_right, h1, map_ofNat (starRingEnd 𝕜) 2,
    inner_add_left]
  rw [h2]
  ring

/-- **(CRS.35)** `ker 𝒜 = ker 𝒜*𝒜 = ⋂_j ker(I + Θ_j)`. -/
theorem jointReversal_kernel (X : V) :
    (jointReversal Θ X = 0 ↔
        (ContinuousLinearMap.adjoint (jointReversal Θ) ∘L jointReversal Θ) X = 0) ∧
      (jointReversal Θ X = 0 ↔ ∀ j, X + Θ j X = 0) := by
  constructor
  · constructor
    · intro h; rw [ContinuousLinearMap.comp_apply, h, map_zero]
    · intro h
      have hn : ‖jointReversal Θ X‖ ^ 2 = 0 := by
        rw [@norm_sq_eq_re_inner 𝕜, ← ContinuousLinearMap.adjoint_inner_left,
          ← ContinuousLinearMap.comp_apply, h, inner_zero_left, map_zero]
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn)
  · constructor
    · intro h j
      have := congrArg (fun Z : PiLp 2 (fun _ : J => V) => Z.ofLp j) h
      simpa [jointReversal_apply] using this
    · intro h
      ext j
      rw [jointReversal_apply, h j]; rfl

/-- **(CRS.36)** The properness estimate `∑_j ‖X + Θ_jX‖² ≥ α ‖X‖²`. -/
def ReversalProper (Θ : J → V →L[𝕜] V) (α : ℝ) : Prop :=
  ∀ X : V, α * ‖X‖ ^ 2 ≤ ∑ j, ‖X + Θ j X‖ ^ 2

omit [CompleteSpace V] in
/-- **Corollary 7.2 (CRS.37)** Under the properness estimate,
`‖X‖² ≤ α⁻¹ ∑_j ‖X + Θ_jX‖²`. -/
theorem norm_sq_le_of_reversalProper {α : ℝ} (hα : 0 < α) (hP : ReversalProper Θ α) (X : V) :
    ‖X‖ ^ 2 ≤ α⁻¹ * ∑ j, ‖X + Θ j X‖ ^ 2 := by
  rw [le_inv_mul_iff₀ hα]; exact hP X

omit [CompleteSpace V] in
/-- **Corollary 7.2** Under the properness estimate, a sequence whose reversal defects tend to
zero tends to zero. -/
theorem tendsto_zero_of_reversalProper {α : ℝ} (hα : 0 < α) (hP : ReversalProper Θ α)
    (X : ℕ → V) (hX : Tendsto (fun n => ∑ j, ‖X n + Θ j (X n)‖ ^ 2) atTop (𝓝 0)) :
    Tendsto X atTop (𝓝 0) := by
  have hsq : Tendsto (fun n => ‖X n‖ ^ 2) atTop (𝓝 0) := by
    have := hX.const_mul α⁻¹
    rw [mul_zero] at this
    exact squeeze_zero (fun n => sq_nonneg _) (fun n => norm_sq_le_of_reversalProper hα hP (X n))
      this
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hn
  refine tendsto_zero_iff_norm_tendsto_zero.2 (hn.congr fun n => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace V] in
theorem reversalProper_iff_bound {α : ℝ} :
    ReversalProper Θ α ↔ ∀ X, α * ‖X‖ ^ 2 ≤ ‖jointReversal Θ X‖ ^ 2 := by
  simp only [ReversalProper, norm_jointReversal_sq]

/-- **Theorem 7.1** The properness estimate holds for some `α > 0` exactly when the joint
response is injective with closed range. -/
theorem exists_reversalProper_iff :
    (∃ α > 0, ReversalProper Θ α) ↔
      Function.Injective (jointReversal Θ) ∧ IsClosed (Set.range (jointReversal Θ)) := by
  constructor
  · rintro ⟨α, hα, hP⟩
    rw [reversalProper_iff_bound] at hP
    have hbound : ∀ X, ‖X‖ ≤ (Real.sqrt α)⁻¹ * ‖jointReversal Θ X‖ := fun X => by
      have h := hP X
      have hs : Real.sqrt α * ‖X‖ ≤ ‖jointReversal Θ X‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (jointReversal Θ X)), ← Real.sqrt_sq (norm_nonneg X),
          ← Real.sqrt_mul hα.le]
        exact Real.sqrt_le_sqrt h
      rw [le_inv_mul_iff₀ (Real.sqrt_pos.2 hα)]; exact hs
    have hanti : AntilipschitzWith (Real.toNNReal (Real.sqrt α)⁻¹) (jointReversal Θ) :=
      AntilipschitzWith.of_le_mul_dist fun X Y => by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal _ (by positivity)]
        exact hbound (X - Y)
    exact ⟨hanti.injective, hanti.isClosed_range (jointReversal Θ).uniformContinuous⟩
  · rintro ⟨hinj, hcl⟩
    haveI : CompleteSpace (LinearMap.range (jointReversal Θ).toLinearMap) :=
      hcl.completeSpace_coe
    let f : V →L[𝕜] LinearMap.range (jointReversal Θ).toLinearMap :=
      (jointReversal Θ).codRestrict _ fun X => LinearMap.mem_range_self _ X
    have hf_inj : Function.Injective f := fun X Y h => hinj (congrArg Subtype.val h)
    have hf_surj : Function.Surjective f := fun ⟨Z, ⟨X, hX⟩⟩ => ⟨X, Subtype.ext hX⟩
    let e := ContinuousLinearEquiv.ofBijective f (LinearMap.ker_eq_bot.2 hf_inj)
      (LinearMap.range_eq_top.2 hf_surj)
    set C := ‖(e.symm : LinearMap.range (jointReversal Θ).toLinearMap →L[𝕜] V)‖
    refine ⟨((C + 1) ^ 2)⁻¹, by positivity, ?_⟩
    rw [reversalProper_iff_bound]
    intro X
    have hX : ‖X‖ ≤ (C + 1) * ‖jointReversal Θ X‖ := by
      calc ‖X‖ = ‖(e.symm : LinearMap.range (jointReversal Θ).toLinearMap →L[𝕜] V) (f X)‖ := by
            congr 1; exact (e.symm_apply_apply X).symm
        _ ≤ C * ‖f X‖ := ContinuousLinearMap.le_opNorm _ _
        _ = C * ‖jointReversal Θ X‖ := rfl
        _ ≤ (C + 1) * ‖jointReversal Θ X‖ := by
            gcongr; linarith
    have hpos : 0 < C + 1 := by positivity
    rw [inv_mul_le_iff₀ (by positivity)]
    calc ‖X‖ ^ 2 ≤ ((C + 1) * ‖jointReversal Θ X‖) ^ 2 := by gcongr
      _ = (C + 1) ^ 2 * ‖jointReversal Θ X‖ ^ 2 := by ring

/-- **Theorem 7.1, finite dimension.**  The properness estimate holds for some `α > 0` exactly
when the common odd sector `⋂_j ker(I + Θ_j)` is zero. -/
theorem exists_reversalProper_iff_finiteDimensional [FiniteDimensional 𝕜 V] :
    (∃ α > 0, ReversalProper Θ α) ↔ ∀ X : V, (∀ j, X + Θ j X = 0) → X = 0 := by
  constructor
  · rintro ⟨α, hα, hP⟩ X hX
    have h := hP X
    simp only [hX, norm_zero, zero_pow two_ne_zero, Finset.sum_const_zero] at h
    have : ‖X‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
  · intro hodd
    have hker : LinearMap.ker (jointReversal Θ).toLinearMap = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro X hX
      exact hodd X ((jointReversal_kernel X).2.1 hX)
    obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith _ hker
    refine (exists_reversalProper_iff).2 ⟨hanti.injective,
      hanti.isClosed_range (jointReversal Θ).uniformContinuous⟩

end Gramian

/-! ## Characteristic two -/

/-- **§10.3** In characteristic two there is a nontrivial element `1 + x` with `x² = 0` and
`(1 + x)² = 1`. -/
theorem char_two_square_one :
    ∃ x : DualNumber (ZMod 2), x ^ 2 = 0 ∧ (1 + x) ^ 2 = 1 ∧ 1 + x ≠ 1 := by
  refine ⟨DualNumber.eps, by rw [sq, DualNumber.eps_mul_eps], ?_, ?_⟩
  · rw [sq]
    ext
    · simp
    · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
        TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_one, DualNumber.snd_eps, DualNumber.fst_eps]
      decide
  · intro h
    have := congrArg TrivSqZeroExt.snd h
    simp at this

end GaloisForLFunctions.HTGeometry
