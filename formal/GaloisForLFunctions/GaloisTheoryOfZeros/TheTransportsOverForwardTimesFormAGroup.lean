import GaloisForLFunctions.GaloisTheoryOfZeros.NoZeroEscapesOverForwardTimes

/-!
# The transports over forward times form a group

A *forward path* is a path of times in the open half-plane `Re τ > 0` that avoids the branch
times of the heat cover. Along a forward path every zero continues, uniquely, to a zero over the
end of the path. This file gives the algebra of these transports.

* Transports compose along the concatenation of paths (`Transports.trans`), invert along the
  reversed path (`Transports.symm`), and are the identity along a constant path.
* They commute with the two symmetries of the family: `z ↦ −z` (`Transports.neg`) and the
  conjugation `(τ, z) ↦ (τ̄, z̄)` (`Transports.conj`).
* The end of a transport is determined by its start (`IsForwardPath.transports_unique`).

So the transports along the forward loops based at a time `τ` form a group of permutations of
the zeros of `H_τ`, the *forward monodromy group* `forwardMonodromy τ`, and every element of it
commutes with the reflection `z ↦ −z` of the fibre (`forwardMonodromy_commute_fibreNeg`): the
group consists of signed permutations of the pairs `{z, −z}`.

Any two forward times off the branch times are joined by a forward path
(`exists_isForwardPath`), and the transport along such a path conjugates the group at one end
onto the group at the other (`IsForwardPath.map_forwardMonodromy`). The group is therefore an
invariant of the heat cover (`nonempty_mulEquiv_forwardMonodromy`).
-/

open Complex Set
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Paths -/

/-- The concatenation of two paths parametrized by `[0, 1]`. -/
def pathJoin (γ₁ γ₂ : ℝ → ℂ) (s : ℝ) : ℂ := if s ≤ 1 / 2 then γ₁ (2 * s) else γ₂ (2 * s - 1)

/-- The reversed path. -/
def pathRev (γ : ℝ → ℂ) (s : ℝ) : ℂ := γ (1 - s)

theorem pathJoin_of_le {γ₁ γ₂ : ℝ → ℂ} {s : ℝ} (h : s ≤ 1 / 2) :
    pathJoin γ₁ γ₂ s = γ₁ (2 * s) := if_pos h

theorem pathJoin_of_lt {γ₁ γ₂ : ℝ → ℂ} {s : ℝ} (h : 1 / 2 < s) :
    pathJoin γ₁ γ₂ s = γ₂ (2 * s - 1) := if_neg (not_le.2 h)

theorem pathJoin_zero (γ₁ γ₂ : ℝ → ℂ) : pathJoin γ₁ γ₂ 0 = γ₁ 0 := by
  rw [pathJoin_of_le (by norm_num), mul_zero]

theorem pathJoin_one (γ₁ γ₂ : ℝ → ℂ) : pathJoin γ₁ γ₂ 1 = γ₂ 1 := by
  rw [pathJoin_of_lt (by norm_num)]
  norm_num

theorem pathRev_zero (γ : ℝ → ℂ) : pathRev γ 0 = γ 1 := by rw [pathRev, sub_zero]

theorem pathRev_one (γ : ℝ → ℂ) : pathRev γ 1 = γ 0 := by rw [pathRev, sub_self]

theorem mapsTo_double : MapsTo (fun s : ℝ => 2 * s) (Icc 0 (1 / 2)) (Icc 0 1) := fun s hs =>
  ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem mapsTo_double_sub_one : MapsTo (fun s : ℝ => 2 * s - 1) (Icc (1 / 2) 1) (Icc 0 1) :=
  fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem mapsTo_one_sub : MapsTo (fun s : ℝ => 1 - s) (Icc 0 1) (Icc 0 1) := fun s hs =>
  ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Two functions continuous on `[0, 1]` that match at the junction concatenate continuously. -/
theorem continuousOn_pathJoin {f g : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1))
    (hg : ContinuousOn g (Icc 0 1)) (hfg : f 1 = g 0) :
    ContinuousOn (pathJoin f g) (Icc 0 1) := by
  have h1 : ContinuousOn (fun s : ℝ => f (2 * s)) (Icc 0 (1 / 2)) :=
    hf.comp (continuous_const.mul continuous_id).continuousOn mapsTo_double
  have h2 : ContinuousOn (fun s : ℝ => g (2 * s - 1)) (Icc (1 / 2) 1) :=
    hg.comp ((continuous_const.mul continuous_id).sub continuous_const).continuousOn
      mapsTo_double_sub_one
  rw [← Icc_union_Icc_eq_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  refine ContinuousOn.union_of_isClosed (h1.congr fun s hs => pathJoin_of_le hs.2)
    (h2.congr fun s hs => ?_) isClosed_Icc isClosed_Icc
  rcases eq_or_lt_of_le hs.1 with h | h
  · show pathJoin f g s = g (2 * s - 1)
    rw [← h, pathJoin_of_le le_rfl, show (2 : ℝ) * (1 / 2) = 1 by norm_num, sub_self]
    exact hfg
  · exact pathJoin_of_lt h

theorem continuousOn_pathRev {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 1)) :
    ContinuousOn (pathRev f) (Icc 0 1) :=
  hf.comp (continuous_const.sub continuous_id).continuousOn mapsTo_one_sub

/-- A path of forward times off the branch times. -/
structure IsForwardPath (γ : ℝ → ℂ) : Prop where
  continuousOn : ContinuousOn γ (Icc 0 1)
  re_pos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re
  simple : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∉ branchTimes

theorem IsForwardPath.const {τ : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    IsForwardPath fun _ => τ :=
  ⟨continuousOn_const, fun _ _ => hτ, fun _ _ => hb⟩

theorem IsForwardPath.reverse {γ : ℝ → ℂ} (h : IsForwardPath γ) : IsForwardPath (pathRev γ) :=
  ⟨continuousOn_pathRev h.continuousOn, fun _ hs => h.re_pos _ (mapsTo_one_sub hs),
    fun _ hs => h.simple _ (mapsTo_one_sub hs)⟩

theorem IsForwardPath.join {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsForwardPath γ₁) (h₂ : IsForwardPath γ₂)
    (h : γ₁ 1 = γ₂ 0) : IsForwardPath (pathJoin γ₁ γ₂) := by
  have key : ∀ s ∈ Icc (0 : ℝ) 1, ∃ γ : ℝ → ℂ, IsForwardPath γ ∧
      ∃ u ∈ Icc (0 : ℝ) 1, pathJoin γ₁ γ₂ s = γ u := by
    intro s hs
    rcases le_or_gt s (1 / 2) with hle | hlt
    · exact ⟨γ₁, h₁, 2 * s, mapsTo_double ⟨hs.1, hle⟩, pathJoin_of_le hle⟩
    · exact ⟨γ₂, h₂, 2 * s - 1, mapsTo_double_sub_one ⟨hlt.le, hs.2⟩, pathJoin_of_lt hlt⟩
  refine ⟨continuousOn_pathJoin h₁.continuousOn h₂.continuousOn h, fun s hs => ?_,
    fun s hs => ?_⟩
  · obtain ⟨γ, hγ, u, hu, e⟩ := key s hs
    rw [e]
    exact hγ.re_pos u hu
  · obtain ⟨γ, hγ, u, hu, e⟩ := key s hs
    rw [e]
    exact hγ.simple u hu

/-! ## The algebra of transports -/

theorem Transports.zero_left {γ : ℝ → ℂ} {z₀ z₁ : ℂ} (h : Transports γ z₀ z₁) :
    complexHeat (γ 0) z₀ = 0 := by
  obtain ⟨z, hz, rfl, -⟩ := h
  exact hz.zero 0 ⟨le_rfl, zero_le_one⟩

theorem Transports.zero_right {γ : ℝ → ℂ} {z₀ z₁ : ℂ} (h : Transports γ z₀ z₁) :
    complexHeat (γ 1) z₁ = 0 := by
  obtain ⟨z, hz, -, rfl⟩ := h
  exact hz.zero 1 ⟨zero_le_one, le_rfl⟩

/-- Along a constant path every zero is transported to itself. -/
theorem Transports.refl {τ z₀ : ℂ} (h : complexHeat τ z₀ = 0) :
    Transports (fun _ => τ) z₀ z₀ :=
  ⟨fun _ => z₀, ⟨continuousOn_const, fun _ _ => h⟩, rfl, rfl⟩

/-- Transport along the reversed path is the inverse transport. -/
theorem Transports.symm {γ : ℝ → ℂ} {z₀ z₁ : ℂ} (h : Transports γ z₀ z₁) :
    Transports (pathRev γ) z₁ z₀ := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  exact ⟨pathRev z, ⟨continuousOn_pathRev hz.continuousOn,
    fun s hs => hz.zero _ (mapsTo_one_sub hs)⟩, pathRev_zero z, pathRev_one z⟩

/-- Transports compose along the concatenation of the paths. -/
theorem Transports.trans {γ₁ γ₂ : ℝ → ℂ} {z₀ z₁ z₂ : ℂ} (h₁ : Transports γ₁ z₀ z₁)
    (h₂ : Transports γ₂ z₁ z₂) : Transports (pathJoin γ₁ γ₂) z₀ z₂ := by
  obtain ⟨w₁, hw₁, rfl, rfl⟩ := h₁
  obtain ⟨w₂, hw₂, h20, rfl⟩ := h₂
  refine ⟨pathJoin w₁ w₂, ⟨continuousOn_pathJoin hw₁.continuousOn hw₂.continuousOn h20.symm,
    fun s hs => ?_⟩, pathJoin_zero w₁ w₂, pathJoin_one w₁ w₂⟩
  rcases le_or_gt s (1 / 2) with hle | hlt
  · rw [pathJoin_of_le hle, pathJoin_of_le hle]
    exact hw₁.zero _ (mapsTo_double ⟨hs.1, hle⟩)
  · rw [pathJoin_of_lt hlt, pathJoin_of_lt hlt]
    exact hw₂.zero _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)

/-- Transport commutes with the reflection `z ↦ −z`. -/
theorem Transports.neg {γ : ℝ → ℂ} {z₀ z₁ : ℂ} (h : Transports γ z₀ z₁) :
    Transports γ (-z₀) (-z₁) := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  exact ⟨fun s => -z s, ⟨hz.continuousOn.neg, fun s hs => by
    rw [complexHeat_neg]
    exact hz.zero s hs⟩, rfl, rfl⟩

/-- Transport along the conjugate path is the conjugate transport. -/
theorem Transports.conj {γ : ℝ → ℂ} {z₀ z₁ : ℂ} (h : Transports γ z₀ z₁) :
    Transports (fun s => starRingEnd ℂ (γ s)) (starRingEnd ℂ z₀) (starRingEnd ℂ z₁) := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  exact ⟨fun s => starRingEnd ℂ (z s),
    ⟨Complex.continuous_conj.comp_continuousOn hz.continuousOn, fun s hs => by
      rw [← complexHeat_conj, hz.zero s hs, map_zero]⟩, rfl, rfl⟩

/-- **The end of a transport is determined by its start.** -/
theorem IsForwardPath.transports_unique {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {z₀ z₁ z₁' : ℂ}
    (h : Transports γ z₀ z₁) (h' : Transports γ z₀ z₁') : z₁ = z₁' := by
  obtain ⟨z, hz, rfl, rfl⟩ := h
  obtain ⟨z', hz', h0, rfl⟩ := h'
  exact IsZeroLift.eqOn hγ.continuousOn hz hz' h0.symm (fun s hs =>
    deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hγ.simple s hs) (hz.zero s hs))
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)

/-- **Every zero is transported along a forward path.** -/
theorem IsForwardPath.exists_transports {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {z₀ : ℂ}
    (h0 : complexHeat (γ 0) z₀ = 0) : ∃ z₁, Transports γ z₀ z₁ := by
  obtain ⟨z, hz, hz0⟩ := exists_isZeroLift_of_re_pos hγ.continuousOn hγ.re_pos hγ.simple h0
  exact ⟨z 1, z, hz, hz0, rfl⟩

/-! ## The forward monodromy group -/

/-- **The forward monodromy group at the time `τ`.** The permutations of the zeros of `H_τ`
given by the transports along the loops of forward times, off the branch times, based at `τ`. -/
def forwardMonodromy (τ : ℂ) (hτ : 0 < τ.re) (hb : τ ∉ branchTimes) :
    Subgroup (Equiv.Perm {z : ℂ // complexHeat τ z = 0}) where
  carrier := {σ | ∃ γ, IsForwardPath γ ∧ γ 0 = τ ∧ γ 1 = τ ∧ ∀ p, Transports γ p.1 (σ p).1}
  mul_mem' := by
    rintro σ₁ σ₂ ⟨γ₁, h₁, h₁0, h₁1, ht₁⟩ ⟨γ₂, h₂, h₂0, h₂1, ht₂⟩
    exact ⟨pathJoin γ₂ γ₁, h₂.join h₁ (h₂1.trans h₁0.symm), by rw [pathJoin_zero, h₂0],
      by rw [pathJoin_one, h₁1], fun p => (ht₂ p).trans (ht₁ (σ₂ p))⟩
  one_mem' := ⟨fun _ => τ, IsForwardPath.const hτ hb, rfl, rfl, fun p => Transports.refl p.2⟩
  inv_mem' := by
    rintro σ ⟨γ, h, h0, h1, ht⟩
    refine ⟨pathRev γ, h.reverse, by rw [pathRev_zero, h1], by rw [pathRev_one, h0],
      fun p => ?_⟩
    have e : σ (σ⁻¹ p) = p := σ.apply_symm_apply p
    have := (ht (σ⁻¹ p)).symm
    rwa [e] at this

theorem mem_forwardMonodromy {τ : ℂ} {hτ : 0 < τ.re} {hb : τ ∉ branchTimes}
    {σ : Equiv.Perm {z : ℂ // complexHeat τ z = 0}} :
    σ ∈ forwardMonodromy τ hτ hb ↔
      ∃ γ, IsForwardPath γ ∧ γ 0 = τ ∧ γ 1 = τ ∧ ∀ p, Transports γ p.1 (σ p).1 :=
  Iff.rfl

/-- The reflection `z ↦ −z` of the fibre over `τ`. -/
def fibreNeg (τ : ℂ) : Equiv.Perm {z : ℂ // complexHeat τ z = 0} where
  toFun p := ⟨-p.1, by rw [complexHeat_neg]; exact p.2⟩
  invFun p := ⟨-p.1, by rw [complexHeat_neg]; exact p.2⟩
  left_inv p := Subtype.ext (neg_neg _)
  right_inv p := Subtype.ext (neg_neg _)

/-- **The forward monodromy commutes with the reflection.** Every element of the group is a
signed permutation of the pairs `{z, −z}` of the fibre. -/
theorem forwardMonodromy_commute_fibreNeg {τ : ℂ} {hτ : 0 < τ.re} {hb : τ ∉ branchTimes}
    {σ : Equiv.Perm {z : ℂ // complexHeat τ z = 0}} (hσ : σ ∈ forwardMonodromy τ hτ hb) :
    σ * fibreNeg τ = fibreNeg τ * σ := by
  obtain ⟨γ, h, -, -, ht⟩ := hσ
  refine Equiv.ext fun p => Subtype.ext ?_
  exact h.transports_unique (ht (fibreNeg τ p)) (ht p).neg

/-! ## Forward times off the branch times are joined by forward paths -/

/-- The arc from `τ` to `τ'` bent sideways by `η`. -/
def arcPath (τ τ' : ℂ) (η : ℝ) (s : ℝ) : ℂ :=
  τ + (τ' - τ) * ((s : ℂ) + I * ((η * (s * (1 - s)) : ℝ) : ℂ))

theorem arcPath_zero (τ τ' : ℂ) (η : ℝ) : arcPath τ τ' η 0 = τ := by simp [arcPath]

theorem arcPath_one (τ τ' : ℂ) (η : ℝ) : arcPath τ τ' η 1 = τ' := by simp [arcPath]

theorem continuous_arcPath (τ τ' : ℂ) (η : ℝ) : Continuous (arcPath τ τ' η) := by
  show Continuous fun s : ℝ => τ + (τ' - τ) * ((s : ℂ) + I * ((η * (s * (1 - s)) : ℝ) : ℂ))
  fun_prop

/-- Arcs with the same two ends meet only at equal parameters and equal heights. -/
theorem arcPath_inj {τ τ' : ℂ} (hne : τ ≠ τ') {η η' s s' : ℝ}
    (h : arcPath τ τ' η s = arcPath τ τ' η' s') :
    s = s' ∧ η * (s * (1 - s)) = η' * (s' * (1 - s')) := by
  unfold arcPath at h
  have hw := mul_left_cancel₀ (sub_ne_zero.2 (Ne.symm hne)) (add_left_cancel h)
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_mul_re, Complex.I_mul_im, neg_zero, add_zero, zero_add] at hre him
  exact ⟨hre, him⟩

/-- A low arc between two forward times stays in a box of forward times. -/
theorem arcPath_mem_box {τ τ' : ℂ} {η s m₀ : ℝ} (hτ : m₀ ≤ τ.re) (hτ' : m₀ ≤ τ'.re)
    (hη0 : 0 ≤ η) (hη : η * ‖τ' - τ‖ ≤ m₀ / 2) (hs : s ∈ Icc (0 : ℝ) 1) :
    m₀ / 2 ≤ (arcPath τ τ' η s).re ∧ ‖arcPath τ τ' η s‖ ≤ ‖τ‖ + ‖τ'‖ + m₀ / 2 := by
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hc0 : 0 ≤ s * (1 - s) := mul_nonneg hs.1 hs1
  have hc1 : s * (1 - s) ≤ 1 := by
    have := mul_le_mul hs.2 (by linarith [hs.1] : 1 - s ≤ 1) hs1 zero_le_one
    linarith
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = I * ((η * (s * (1 - s)) : ℝ) : ℂ) * (τ' - τ) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = ((1 - s : ℝ) : ℂ) * τ + (s : ℂ) * τ' := ⟨_, rfl⟩
  have heq : arcPath τ τ' η s = A + E := by
    rw [hA, hE, arcPath]
    push_cast
    ring
  have hEn : ‖E‖ ≤ m₀ / 2 := by
    rw [hE, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hη0 hc0)]
    have h1 : η * (s * (1 - s)) ≤ η := by
      have := mul_le_mul_of_nonneg_left hc1 hη0
      linarith
    have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (τ' - τ))
    linarith
  have hAre : m₀ ≤ A.re := by
    have h1 : A.re = (1 - s) * τ.re + s * τ'.re := by
      rw [hA]
      simp
    rw [h1]
    exact le_convexCombo hs.1 hs.2 hτ hτ'
  have hAn : ‖A‖ ≤ ‖τ‖ + ‖τ'‖ := by
    have h1 : ‖A‖ ≤ (1 - s) * ‖τ‖ + s * ‖τ'‖ := by
      rw [hA]
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hs1, abs_of_nonneg hs.1]
    have h2 := mul_le_of_le_one_left (norm_nonneg τ) (by linarith [hs.1] : 1 - s ≤ 1)
    have h3 := mul_le_of_le_one_left (norm_nonneg τ') hs.2
    linarith
  rw [heq]
  refine ⟨?_, (norm_add_le _ _).trans (by linarith)⟩
  rw [Complex.add_re]
  have h1 := neg_abs_le E.re
  have h2 := Complex.abs_re_le_norm E
  linarith

/-- **Two forward times off the branch times are joined by a forward path.** The arcs between
them meet only at their ends, and a box of forward times contains finitely many branch times,
so some arc avoids them all. -/
theorem exists_isForwardPath {τ τ' : ℂ} (hτ : 0 < τ.re) (hτ' : 0 < τ'.re)
    (hb : τ ∉ branchTimes) (hb' : τ' ∉ branchTimes) :
    ∃ γ, IsForwardPath γ ∧ γ 0 = τ ∧ γ 1 = τ' := by
  rcases eq_or_ne τ τ' with rfl | hne
  · exact ⟨fun _ => τ, IsForwardPath.const hτ hb, rfl, rfl⟩
  obtain ⟨m₀, hm₀, hm, hm'⟩ : ∃ m₀ : ℝ, 0 < m₀ ∧ m₀ ≤ τ.re ∧ m₀ ≤ τ'.re :=
    ⟨min τ.re τ'.re, lt_min hτ hτ', min_le_left _ _, min_le_right _ _⟩
  have hdn : 0 < ‖τ' - τ‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨η₀, hη₀, hη₀d⟩ : ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ * ‖τ' - τ‖ ≤ m₀ / 2 :=
    ⟨m₀ / 2 / ‖τ' - τ‖, by positivity, by rw [div_mul_cancel₀ _ hdn.ne']⟩
  have hbox : ∀ η ∈ Ioc (0 : ℝ) η₀, ∀ s ∈ Icc (0 : ℝ) 1,
      m₀ / 2 ≤ (arcPath τ τ' η s).re ∧ ‖arcPath τ τ' η s‖ ≤ ‖τ‖ + ‖τ'‖ + m₀ / 2 :=
    fun η hη s hs => arcPath_mem_box hm hm' hη.1.le
      ((mul_le_mul_of_nonneg_right hη.2 (norm_nonneg _)).trans hη₀d) hs
  have hfin := finite_branchTimes_box (t₀ := m₀ / 2) (‖τ‖ + ‖τ'‖ + m₀ / 2) (half_pos hm₀)
  have hex : ∃ η ∈ Ioc (0 : ℝ) η₀, ∀ s ∈ Icc (0 : ℝ) 1, arcPath τ τ' η s ∉ branchTimes := by
    by_contra hcon
    push Not at hcon
    choose! σ hσ using hcon
    have hmaps : MapsTo (fun η => arcPath τ τ' η (σ η)) (Ioc (0 : ℝ) η₀)
        {x : ℂ | x ∈ branchTimes ∧ m₀ / 2 ≤ x.re ∧ ‖x‖ ≤ ‖τ‖ + ‖τ'‖ + m₀ / 2} :=
      fun η hη => ⟨(hσ η hη).2, hbox η hη _ (hσ η hη).1⟩
    have hinj : InjOn (fun η => arcPath τ τ' η (σ η)) (Ioc (0 : ℝ) η₀) := by
      intro η hη η' _ hff
      obtain ⟨hs, hc⟩ := arcPath_inj hne hff
      rw [← hs] at hc
      have h2 : (η - η') * (σ η * (1 - σ η)) = 0 := by linear_combination hc
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exfalso
        have hmem := (hσ η hη).2
        rcases mul_eq_zero.1 h with h0 | h1
        · rw [h0, arcPath_zero] at hmem
          exact hb hmem
        · rw [show σ η = 1 by linarith, arcPath_one] at hmem
          exact hb' hmem
    exact Set.infinite_of_injOn_mapsTo hinj hmaps (Ioc_infinite hη₀) hfin
  obtain ⟨η, hη, hgood⟩ := hex
  exact ⟨arcPath τ τ' η, ⟨(continuous_arcPath τ τ' η).continuousOn,
    fun s hs => (half_pos hm₀).trans_le (hbox η hη s hs).1, hgood⟩,
    arcPath_zero τ τ' η, arcPath_one τ τ' η⟩

/-! ## The group does not depend on the base time -/

/-- The start of a transport is determined by its end. -/
theorem IsForwardPath.transports_injective {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {z₀ z₀' z₁ : ℂ}
    (h : Transports γ z₀ z₁) (h' : Transports γ z₀' z₁) : z₀ = z₀' :=
  hγ.reverse.transports_unique h.symm h'.symm

/-- The transport along a forward path from `τ` to `τ'` is a bijection of the fibres. -/
theorem IsForwardPath.exists_fibreEquiv {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {τ τ' : ℂ}
    (h0 : γ 0 = τ) (h1 : γ 1 = τ') :
    ∃ e : {z : ℂ // complexHeat τ z = 0} ≃ {z : ℂ // complexHeat τ' z = 0},
      ∀ p, Transports γ p.1 (e p).1 := by
  subst h0 h1
  exact exists_transport_equiv hγ.continuousOn hγ.re_pos hγ.simple

/-- Every forward loop based at `τ` defines an element of the forward monodromy group. -/
theorem IsForwardPath.exists_mem_forwardMonodromy {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {τ : ℂ}
    {hτ : 0 < τ.re} {hb : τ ∉ branchTimes} (h0 : γ 0 = τ) (h1 : γ 1 = τ) :
    ∃ σ ∈ forwardMonodromy τ hτ hb, ∀ p, Transports γ p.1 (σ p).1 := by
  obtain ⟨e, he⟩ := hγ.exists_fibreEquiv h0 h1
  exact ⟨e, ⟨γ, hγ, h0, h1, he⟩, he⟩

/-- Conjugation by the transport along a forward path carries the group at the start of the
path into the group at its end. -/
theorem IsForwardPath.permCongr_mem_forwardMonodromy {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {τ τ' : ℂ} {hτ : 0 < τ.re} {hb : τ ∉ branchTimes} {hτ' : 0 < τ'.re} {hb' : τ' ∉ branchTimes}
    (h0 : γ 0 = τ) (h1 : γ 1 = τ')
    {e : {z : ℂ // complexHeat τ z = 0} ≃ {z : ℂ // complexHeat τ' z = 0}}
    (he : ∀ p, Transports γ p.1 (e p).1) {σ : Equiv.Perm {z : ℂ // complexHeat τ z = 0}}
    (hσ : σ ∈ forwardMonodromy τ hτ hb) : e.permCongr σ ∈ forwardMonodromy τ' hτ' hb' := by
  obtain ⟨β, hβ, hβ0, hβ1, hT⟩ := hσ
  refine ⟨pathJoin (pathRev γ) (pathJoin β γ),
    hγ.reverse.join (hβ.join hγ (hβ1.trans h0.symm)) ?_, ?_, ?_, fun p => ?_⟩
  · rw [pathRev_one, pathJoin_zero, h0, hβ0]
  · rw [pathJoin_zero, pathRev_zero, h1]
  · rw [pathJoin_one, pathJoin_one, h1]
  · rw [Equiv.permCongr_apply]
    have h3 : Transports (pathRev γ) p.1 (e.symm p).1 := by
      have := (he (e.symm p)).symm
      rwa [Equiv.apply_symm_apply] at this
    exact h3.trans ((hT (e.symm p)).trans (he (σ (e.symm p))))

/-- **The forward monodromy groups at two base times are conjugate.** The transport along a
forward path from `τ` to `τ'` conjugates the group at `τ` onto the group at `τ'`. -/
theorem IsForwardPath.map_forwardMonodromy {γ : ℝ → ℂ} (hγ : IsForwardPath γ)
    {τ τ' : ℂ} {hτ : 0 < τ.re} {hb : τ ∉ branchTimes} {hτ' : 0 < τ'.re} {hb' : τ' ∉ branchTimes}
    (h0 : γ 0 = τ) (h1 : γ 1 = τ')
    {e : {z : ℂ // complexHeat τ z = 0} ≃ {z : ℂ // complexHeat τ' z = 0}}
    (he : ∀ p, Transports γ p.1 (e p).1) :
    (forwardMonodromy τ hτ hb).map
        (e.permCongrHom : Equiv.Perm {z : ℂ // complexHeat τ z = 0} →* _) =
      forwardMonodromy τ' hτ' hb' := by
  ext σ'
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact hγ.permCongr_mem_forwardMonodromy h0 h1 he hσ
  · intro hσ'
    have he' : ∀ p, Transports (pathRev γ) p.1 (e.symm p).1 := fun p => by
      have := (he (e.symm p)).symm
      rwa [Equiv.apply_symm_apply] at this
    refine ⟨e.symm.permCongr σ', hγ.reverse.permCongr_mem_forwardMonodromy
      (by rw [pathRev_zero, h1]) (by rw [pathRev_one, h0]) he' hσ', ?_⟩
    show e.permCongr (e.symm.permCongr σ') = σ'
    rw [← Equiv.permCongr_symm, Equiv.apply_symm_apply]

/-- **The forward monodromy group is an invariant of the heat cover.** Its isomorphism class
does not depend on the base time. -/
theorem nonempty_mulEquiv_forwardMonodromy {τ τ' : ℂ} (hτ : 0 < τ.re) (hb : τ ∉ branchTimes)
    (hτ' : 0 < τ'.re) (hb' : τ' ∉ branchTimes) :
    Nonempty (forwardMonodromy τ hτ hb ≃* forwardMonodromy τ' hτ' hb') := by
  obtain ⟨γ, hγ, h0, h1⟩ := exists_isForwardPath hτ hτ' hb hb'
  obtain ⟨e, he⟩ := hγ.exists_fibreEquiv h0 h1
  exact ⟨(e.permCongrHom.subgroupMap (forwardMonodromy τ hτ hb)).trans
    (MulEquiv.subgroupCongr (hγ.map_forwardMonodromy h0 h1 he))⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
