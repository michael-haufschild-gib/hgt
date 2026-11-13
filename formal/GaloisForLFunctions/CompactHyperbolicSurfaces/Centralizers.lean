import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements

/-!
# Centralizers of hyperbolic elements in a cocompact free group

Let `Γ` be cocompact and free with `|tr γ| > 2` for `γ ≠ 1`.  Write `γ = ±σ dil(N) σ⁻¹`.  An element
`δ` commuting with `γ` is `±σ dil(M_δ) σ⁻¹` (`inFrame_of_commute`), and `δ ↦ log M_δ` is an
injective homomorphism of the centralizer into `ℝ` (`−1 ∉ Γ`) whose values in a bounded set are
finitely many (`d(σi, δσi) = |log M_δ|`).  Hence the centralizer is infinite cyclic
(`exists_primitive_root`): `Z(γ) = ⟨γ₀⟩`, `γ = γ₀^m` with `m ≥ 1`, and
`γ₀ = ±σ' dil(e^{ℓ₀}) σ'⁻¹` with `ℓ₀ > 0`.
-/

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry RHTower

noncomputable section

theorem neg_one_ne_one_SL : (-1 : SL(2, ℝ)) ≠ 1 := by
  intro h
  have := congrArg (fun g : SL(2, ℝ) => g 0 0) h
  norm_num at this

theorem IsCocompactFree.neg_one_not_mem {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ) :
    (-1 : SL(2, ℝ)) ∉ Γ := by
  intro h
  have h1 := hΓ.eq_one_of_smul_eq ⟨-1, h⟩ I (by
    show (-1 : SL(2, ℝ)) • I = I
    rw [neg_smul_SL, one_smul])
  exact neg_one_ne_one_SL (congrArg Subtype.val h1)

/-! ### The frame of a hyperbolic element -/

/-- `δ` is `±σ dil(M) σ⁻¹` for some `M > 0`. -/
def InFrame (σ δ : SL(2, ℝ)) : Prop :=
  ∃ (M : ℝ) (hM : 0 < M), σ⁻¹ * δ * σ = dilSL M hM ∨ σ⁻¹ * δ * σ = -dilSL M hM

/-- The logarithmic coordinate `log ((σ⁻¹δσ)₀₀²)`. -/
def frameLog (σ δ : SL(2, ℝ)) : ℝ := Real.log (((σ⁻¹ * δ * σ : SL(2, ℝ)) 0 0) ^ 2)

theorem frameLog_eq {σ δ : SL(2, ℝ)} {M : ℝ} {hM : 0 < M}
    (h : σ⁻¹ * δ * σ = dilSL M hM ∨ σ⁻¹ * δ * σ = -dilSL M hM) : frameLog σ δ = Real.log M := by
  unfold frameLog
  rcases h with h | h <;> rw [h]
  · simp [dilSL_apply, Real.sq_sqrt hM.le]
  · simp [Matrix.SpecialLinearGroup.coe_neg, dilSL_apply, Real.sq_sqrt hM.le]

theorem inFrame_of_commute {σ γ δ : SL(2, ℝ)} {N : ℝ} {hN : 0 < N} (hN1 : N ≠ 1)
    (hγ : γ = σ * dilSL N hN * σ⁻¹ ∨ γ = -(σ * dilSL N hN * σ⁻¹)) (h : δ * γ = γ * δ) :
    InFrame σ δ := by
  have h' : δ * (σ * dilSL N hN * σ⁻¹) = (σ * dilSL N hN * σ⁻¹) * δ := by
    rcases hγ with rfl | rfl
    · exact h
    · simpa only [mul_neg, neg_mul, neg_inj] using h
  have hc : (σ⁻¹ * δ * σ) * dilSL N hN = dilSL N hN * (σ⁻¹ * δ * σ) :=
    calc (σ⁻¹ * δ * σ) * dilSL N hN = σ⁻¹ * (δ * (σ * dilSL N hN * σ⁻¹)) * σ := by group
      _ = σ⁻¹ * ((σ * dilSL N hN * σ⁻¹) * δ) * σ := by rw [h']
      _ = dilSL N hN * (σ⁻¹ * δ * σ) := by group
  obtain ⟨M, hM, hx⟩ := eq_dilSL_of_commute hN hN1 hc
  exact ⟨M, hM, hx⟩

theorem InFrame.mul {σ δ δ' : SL(2, ℝ)} (h : InFrame σ δ) (h' : InFrame σ δ') :
    InFrame σ (δ * δ') ∧ frameLog σ (δ * δ') = frameLog σ δ + frameLog σ δ' := by
  obtain ⟨M, hM, hx⟩ := h
  obtain ⟨M', hM', hx'⟩ := h'
  have e : σ⁻¹ * (δ * δ') * σ = (σ⁻¹ * δ * σ) * (σ⁻¹ * δ' * σ) := by group
  have hmul : σ⁻¹ * (δ * δ') * σ = dilSL (M * M') (mul_pos hM hM') ∨
      σ⁻¹ * (δ * δ') * σ = -dilSL (M * M') (mul_pos hM hM') := by
    rw [e]
    rcases hx with hx | hx <;> rcases hx' with hx' | hx' <;> rw [hx, hx'] <;>
      simp only [dilSL_mul, neg_mul, mul_neg, neg_neg, true_or, or_true]
  refine ⟨⟨_, _, hmul⟩, ?_⟩
  rw [frameLog_eq hmul, frameLog_eq hx, frameLog_eq hx', Real.log_mul hM.ne' hM'.ne']

theorem InFrame.eq_one_or_neg_one {σ δ : SL(2, ℝ)} (h : InFrame σ δ) (h0 : frameLog σ δ = 0) :
    δ = 1 ∨ δ = -1 := by
  obtain ⟨M, hM, hx⟩ := h
  rw [frameLog_eq hx] at h0
  have hM1 : M = 1 := by
    rcases Real.log_eq_zero.mp h0 with h | h | h
    · exact absurd h hM.ne'
    · exact h
    · linarith
  subst hM1
  rw [dilSL_one] at hx
  rcases hx with hx | hx
  · left
    calc δ = σ * (σ⁻¹ * δ * σ) * σ⁻¹ := by group
      _ = 1 := by rw [hx]; group
  · right
    calc δ = σ * (σ⁻¹ * δ * σ) * σ⁻¹ := by group
      _ = -1 := by rw [hx, mul_neg, neg_mul, mul_one, mul_inv_cancel]

theorem InFrame.dist_eq {σ δ : SL(2, ℝ)} (h : InFrame σ δ) :
    dist (σ • I) (δ • (σ • I)) = |frameLog σ δ| := by
  obtain ⟨M, hM, hx⟩ := h
  have e : δ • (σ • I) = σ • ((σ⁻¹ * δ * σ) • I) := by
    rw [← mul_smul, ← mul_smul]; congr 1; group
  rw [e, dist_smul, frameLog_eq hx]
  rcases hx with hx | hx <;> rw [hx]
  · exact dist_I_dilSL_smul_I hM
  · rw [neg_smul_SL]; exact dist_I_dilSL_smul_I hM

/-- `w = [[0, 1], [−1, 0]]` conjugates `dil(M)` to `dil(1/M)`. -/
def flipSL : SL(2, ℝ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem flip_conj_dilSL {M : ℝ} (hM : 0 < M) :
    flipSL⁻¹ * dilSL M hM * flipSL = dilSL M⁻¹ (inv_pos.mpr hM) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flipSL, dilSL_apply, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Real.sqrt_inv]

/-! ### The centralizer is infinite cyclic -/

variable {Γ : Subgroup SL(2, ℝ)} (hΓ : IsCocompactFree Γ)
  (hhyp : ∀ γ : Γ, γ ≠ 1 → 2 < |trSL γ|)
include hΓ hhyp

/-- **Primitive roots.**  For `γ ≠ 1` there are `γ₀`, `ℓ₀ > 0`, `m ≥ 1` with `γ = γ₀^m`, the
centralizer of `γ` equal to `⟨γ₀⟩`, and `γ₀ = ±σ dil(e^{ℓ₀}) σ⁻¹`. -/
theorem exists_primitive_root (γ : Γ) (hγ : γ ≠ 1) :
    ∃ (σ : SL(2, ℝ)) (γ₀ : Γ) (ℓ₀ : ℝ) (m : ℕ), 0 < ℓ₀ ∧ 0 < m ∧ γ = γ₀ ^ m ∧
      (∀ δ : Γ, δ * γ = γ * δ ↔ ∃ k : ℤ, δ = γ₀ ^ k) ∧
      ((γ₀ : SL(2, ℝ)) = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
        (γ₀ : SL(2, ℝ)) = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) := by
  obtain ⟨σ, N, hN, hN1, hγσ⟩ := exists_conj_dilSL (hhyp γ hγ)
  set C : Subgroup Γ := Subgroup.centralizer {γ}
  have memC : ∀ δ : Γ, δ ∈ C ↔ δ * γ = γ * δ := fun δ => by
    simp only [C, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact eq_comm
  have hframe : ∀ δ : C, InFrame σ ((δ : Γ) : SL(2, ℝ)) := fun δ =>
    inFrame_of_commute hN1 hγσ (by
      have := (memC δ).mp δ.2
      exact congrArg Subtype.val this)
  -- the logarithmic coordinate as a homomorphism on the centralizer
  let τ : C →* Multiplicative ℝ :=
    { toFun := fun δ => Multiplicative.ofAdd (frameLog σ ((δ : Γ) : SL(2, ℝ)))
      map_one' := by
        simp only [OneMemClass.coe_one, ofAdd_eq_one]
        have : frameLog σ 1 = Real.log 1 := frameLog_eq (M := 1) (hM := one_pos)
          (Or.inl (by rw [dilSL_one]; group))
        rw [this, Real.log_one]
      map_mul' := fun δ δ' => by
        simp only [Subgroup.coe_mul]
        rw [((hframe δ).mul (hframe δ')).2]
        rfl }
  have hτ : ∀ δ : C, Multiplicative.toAdd (τ δ) = frameLog σ ((δ : Γ) : SL(2, ℝ)) := fun _ => rfl
  have hτinj : ∀ δ : C, frameLog σ ((δ : Γ) : SL(2, ℝ)) = 0 → δ = 1 := by
    intro δ h0
    rcases (hframe δ).eq_one_or_neg_one h0 with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exact absurd (h ▸ ((δ : Γ)).2) hΓ.neg_one_not_mem
  have hzpow : ∀ (δ : C) (k : ℤ), frameLog σ (((δ ^ k : C) : Γ) : SL(2, ℝ)) =
      k * frameLog σ ((δ : Γ) : SL(2, ℝ)) := by
    intro δ k
    rw [← hτ, ← hτ, map_zpow, toAdd_zpow, zsmul_eq_mul]
  -- `γ` itself
  let γC : C := ⟨γ, (memC γ).mpr rfl⟩
  have hγlog : frameLog σ (γ : SL(2, ℝ)) = Real.log N := by
    apply frameLog_eq (hM := hN)
    rcases hγσ with h | h
    · left; rw [h]; group
    · right; rw [h, mul_neg, neg_mul]; congr 1; group
  set T := |Real.log N|
  have hT : 0 < T := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hN hN1)
  -- finitely many centralizer values in `[-T, T]`
  have hfin : {δ : C | |frameLog σ ((δ : Γ) : SL(2, ℝ))| ≤ T}.Finite := by
    have hb : Bornology.IsBounded ({σ • I} : Set ℍ) := Bornology.isBounded_singleton
    have h0 := hΓ.finite_near hb hb T
    refine Set.Finite.of_finite_image (f := fun δ : C => (δ : Γ)) (h0.subset ?_)
      (Subtype.val_injective.injOn)
    rintro _ ⟨δ, hδ, rfl⟩
    refine ⟨σ • I, rfl, σ • I, rfl, ?_⟩
    rw [(hframe δ).dist_eq]
    exact hδ
  set P := {r : ℝ | ∃ δ : C, frameLog σ ((δ : Γ) : SL(2, ℝ)) = r ∧ 0 < r ∧ r ≤ T}
  have hPfin : P.Finite := by
    refine (hfin.image fun δ : C => frameLog σ ((δ : Γ) : SL(2, ℝ))).subset ?_
    rintro r ⟨δ, hδ, hr0, hrT⟩
    exact ⟨δ, by simp only [Set.mem_setOf_eq]; rw [hδ, abs_of_pos hr0]; exact hrT, hδ⟩
  have hPne : P.Nonempty := by
    rcases lt_or_gt_of_ne (Real.log_ne_zero_of_pos_of_ne_one hN hN1) with h | h
    · refine ⟨-Real.log N, γC⁻¹, ?_, by linarith, by simp [T, abs_of_neg h]⟩
      have := hzpow γC (-1)
      simp only [zpow_neg, zpow_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at this
      rw [this]
      exact congrArg Neg.neg hγlog
    · exact ⟨Real.log N, γC, hγlog, h, by simp [T, abs_of_pos h]⟩
  set ℓ₀ := hPfin.toFinset.min' (by simpa using hPne)
  have hℓ₀P : ℓ₀ ∈ P := by
    have := hPfin.toFinset.min'_mem (by simpa using hPne)
    simpa using this
  obtain ⟨g₀, hg₀, hℓ₀pos, hℓ₀T⟩ := hℓ₀P
  have hmin : ∀ r ∈ P, ℓ₀ ≤ r := fun r hr => hPfin.toFinset.min'_le r (by simpa using hr)
  -- every centralizer element is a power of `g₀`
  have hgen : ∀ δ : C, ∃ k : ℤ, δ = g₀ ^ k := by
    intro δ
    set r := frameLog σ ((δ : Γ) : SL(2, ℝ))
    set k := ⌊r / ℓ₀⌋
    refine ⟨k, ?_⟩
    have hrem : frameLog σ (((δ * g₀ ^ (-k) : C) : Γ) : SL(2, ℝ)) = r - k * ℓ₀ := by
      rw [show (((δ * g₀ ^ (-k) : C) : Γ) : SL(2, ℝ)) =
        ((δ : Γ) : SL(2, ℝ)) * (((g₀ ^ (-k) : C) : Γ) : SL(2, ℝ)) from rfl,
        ((hframe δ).mul (hframe _)).2, hzpow, hg₀]
      push_cast; ring
    have hlo : 0 ≤ r - k * ℓ₀ := by
      have := Int.floor_le (r / ℓ₀)
      rw [le_div_iff₀ hℓ₀pos] at this; linarith
    have hhi : r - k * ℓ₀ < ℓ₀ := by
      have := Int.lt_floor_add_one (r / ℓ₀)
      rw [div_lt_iff₀ hℓ₀pos] at this; linarith
    have hz : r - k * ℓ₀ = 0 := by
      by_contra hne
      have hpos : 0 < r - k * ℓ₀ := lt_of_le_of_ne hlo (Ne.symm hne)
      have := hmin _ ⟨_, hrem, hpos, by linarith⟩
      linarith
    have h1 := hτinj _ (hrem.trans hz)
    rw [mul_eq_one_iff_eq_inv, zpow_neg, inv_inv] at h1
    exact h1
  -- `γ = g₀^{m₀}` with `m₀ ≠ 0`
  obtain ⟨m₀, hm₀⟩ := hgen γC
  have hm₀ne : m₀ ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hm₀
    exact hγ (congrArg Subtype.val hm₀)
  have hcomm : ∀ δ : Γ, δ * γ = γ * δ ↔ ∃ k : ℤ, δ = ((g₀ : Γ)) ^ k := by
    intro δ
    constructor
    · intro h
      obtain ⟨k, hk⟩ := hgen ⟨δ, (memC δ).mpr h⟩
      exact ⟨k, by rw [← Subgroup.coe_zpow, ← hk]⟩
    · rintro ⟨k, rfl⟩
      exact (memC _).mp (Subgroup.zpow_mem _ g₀.2 k)
  have hγeq : γ = (g₀ : Γ) ^ m₀ := by rw [← Subgroup.coe_zpow, ← hm₀]
  -- frame for `g₀`
  obtain ⟨M₀, hM₀, hx₀⟩ := hframe g₀
  have hlogM₀ : Real.log M₀ = ℓ₀ := by rw [← frameLog_eq hx₀, hg₀]
  have hM₀eq : M₀ = Real.exp ℓ₀ := by rw [← hlogM₀, Real.exp_log hM₀]
  have hrecon : ∀ x : SL(2, ℝ), σ⁻¹ * x * σ = dilSL M₀ hM₀ ∨ σ⁻¹ * x * σ = -dilSL M₀ hM₀ →
      (x = σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹ ∨
        x = -(σ * dilSL (Real.exp ℓ₀) (Real.exp_pos _) * σ⁻¹)) := by
    intro x hx
    subst hM₀eq
    rcases hx with hx | hx
    · left
      calc x = σ * (σ⁻¹ * x * σ) * σ⁻¹ := by group
        _ = _ := by rw [hx]
    · right
      calc x = σ * (σ⁻¹ * x * σ) * σ⁻¹ := by group
        _ = _ := by rw [hx, mul_neg, neg_mul]
  rcases lt_or_gt_of_ne hm₀ne with hneg | hpos
  · -- orient by `g₀⁻¹`, in the flipped frame
    refine ⟨σ * flipSL, (g₀ : Γ)⁻¹, ℓ₀, (-m₀).toNat, hℓ₀pos, by omega, ?_, ?_, ?_⟩
    · rw [inv_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg, inv_inv, hγeq]
    · intro δ
      rw [hcomm]
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨-k, by rw [zpow_neg, inv_zpow, inv_inv]⟩
      · rintro ⟨k, rfl⟩; exact ⟨-k, by rw [inv_zpow']⟩
    · show ((g₀ : Γ) : SL(2, ℝ))⁻¹ = _ ∨ ((g₀ : Γ) : SL(2, ℝ))⁻¹ = _
      have hinv : σ⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * σ = (dilSL M₀ hM₀)⁻¹ ∨
          σ⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * σ = -(dilSL M₀ hM₀)⁻¹ := by
        have e : σ⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * σ = (σ⁻¹ * ((g₀ : Γ) : SL(2, ℝ)) * σ)⁻¹ := by
          group
        rw [e]
        rcases hx₀ with h | h <;> rw [h]
        · left; rfl
        · right; rw [neg_inv]
      have hf : (σ * flipSL)⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * (σ * flipSL) =
          flipSL⁻¹ * (σ⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * σ) * flipSL := by group
      subst hM₀eq
      have key : (σ * flipSL)⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * (σ * flipSL) =
            dilSL (Real.exp ℓ₀) (Real.exp_pos _) ∨
          (σ * flipSL)⁻¹ * ((g₀ : Γ) : SL(2, ℝ))⁻¹ * (σ * flipSL) =
            -dilSL (Real.exp ℓ₀) (Real.exp_pos _) := by
        rw [hf]
        have e2 : flipSL⁻¹ * (dilSL (Real.exp ℓ₀) (Real.exp_pos _))⁻¹ * flipSL =
            dilSL (Real.exp ℓ₀) (Real.exp_pos _) := by
          rw [dilSL_inv, flip_conj_dilSL]; congr 1; exact inv_inv _
        rcases hinv with h | h <;> rw [h]
        · left; exact e2
        · right; rw [mul_neg, neg_mul, e2]
      rcases key with h | h
      · left
        calc ((g₀ : Γ) : SL(2, ℝ))⁻¹ = (σ * flipSL) * ((σ * flipSL)⁻¹ *
            ((g₀ : Γ) : SL(2, ℝ))⁻¹ * (σ * flipSL)) * (σ * flipSL)⁻¹ := by group
          _ = _ := by rw [h]
      · right
        calc ((g₀ : Γ) : SL(2, ℝ))⁻¹ = (σ * flipSL) * ((σ * flipSL)⁻¹ *
            ((g₀ : Γ) : SL(2, ℝ))⁻¹ * (σ * flipSL)) * (σ * flipSL)⁻¹ := by group
          _ = _ := by rw [h, mul_neg, neg_mul]
  · refine ⟨σ, (g₀ : Γ), ℓ₀, m₀.toNat, hℓ₀pos, by omega, ?_, hcomm, hrecon _ hx₀⟩
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), hγeq]

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
