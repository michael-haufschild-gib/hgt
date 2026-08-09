import GaloisForLFunctions.HTGeometry.FriedrichsAngle

/-!
# The closed-sum characterization of the Friedrichs angle

For two closed subspaces `U, V` of a Hilbert space, the sum `U + V` is closed exactly when the
Friedrichs cosine is strictly below one.

The proof runs through the generic parts `A = U ⊖ (U ⊓ V)` and `B = V ⊖ (U ⊓ V)`, which meet only
in zero.  A subunit cosine makes the sum map `(a, b) ↦ a + b` bounded below, hence of closed
range; conversely a closed range makes it bounded below, and rotating the second unit vector
against the first turns that bound into a strict cosine bound.  Finally `U + V = (U ⊓ V) ⊕ (A + B)`
is an orthogonal splitting, so it is closed exactly when `A + B` is.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- The sum map of two subspaces, as a continuous linear map from their product. -/
noncomputable def subspaceSum (A B : Submodule 𝕜 H) : (A × B) →L[𝕜] H :=
  A.subtypeL ∘L ContinuousLinearMap.fst 𝕜 A B + B.subtypeL ∘L ContinuousLinearMap.snd 𝕜 A B

omit [CompleteSpace H] in
@[simp] theorem subspaceSum_apply (A B : Submodule 𝕜 H) (z : A × B) :
    subspaceSum A B z = (z.1 : H) + (z.2 : H) := rfl

omit [CompleteSpace H] in
theorem range_subspaceSum (A B : Submodule 𝕜 H) :
    Set.range (subspaceSum A B) = ((A ⊔ B : Submodule 𝕜 H) : Set H) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact Submodule.mem_sup.mpr ⟨(z.1 : H), z.1.2, (z.2 : H), z.2.2, rfl⟩
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

omit [CompleteSpace H] in
theorem subspaceSum_injective {A B : Submodule 𝕜 H} (hAB : A ⊓ B = ⊥) :
    Function.Injective (subspaceSum A B) := by
  intro z w hzw
  have hsum : (z.1 : H) + (z.2 : H) = (w.1 : H) + (w.2 : H) := hzw
  have hdiff : (z.1 : H) - (w.1 : H) = (w.2 : H) - (z.2 : H) := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm ((w.2 : H)) ((w.1 : H))]
    exact hsum
  have hmemA : (z.1 : H) - (w.1 : H) ∈ A := Submodule.sub_mem _ z.1.2 w.1.2
  have hmemB : (z.1 : H) - (w.1 : H) ∈ B := by
    rw [hdiff]
    exact Submodule.sub_mem _ w.2.2 z.2.2
  have hzero : (z.1 : H) - (w.1 : H) = 0 := by
    have : (z.1 : H) - (w.1 : H) ∈ A ⊓ B := ⟨hmemA, hmemB⟩
    rw [hAB] at this
    simpa using this
  have h1 : z.1 = w.1 := Subtype.ext (sub_eq_zero.mp hzero)
  have h2 : z.2 = w.2 := by
    apply Subtype.ext
    have := hdiff
    rw [hzero] at this
    exact (sub_eq_zero.mp this.symm).symm
  exact Prod.ext h1 h2

section GenericParts

variable {U V : Submodule 𝕜 H} (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))

omit [CompleteSpace H] in
include hU in
theorem isClosed_genericPart : IsClosed ((U ⊓ (U ⊓ V)ᗮ : Submodule 𝕜 H) : Set H) := by
  have hcoe : ((U ⊓ (U ⊓ V)ᗮ : Submodule 𝕜 H) : Set H)
      = (U : Set H) ∩ (((U ⊓ V)ᗮ : Submodule 𝕜 H) : Set H) := rfl
  rw [hcoe]
  exact hU.inter (Submodule.isClosed_orthogonal _)

omit [CompleteSpace H] in
theorem genericParts_inf_eq_bot :
    (U ⊓ (U ⊓ V)ᗮ) ⊓ (V ⊓ (U ⊓ V)ᗮ) = (⊥ : Submodule 𝕜 H) := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hW : x ∈ (U ⊓ V : Submodule 𝕜 H) := ⟨hx.1.1, hx.2.1⟩
  have hWp : x ∈ ((U ⊓ V)ᗮ : Submodule 𝕜 H) := hx.1.2
  have hzero : ⟪x, x⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ x).mp hWp x hW
  exact (inner_self_eq_zero (𝕜 := 𝕜)).mp hzero

include hU hV in
/-- A subunit Friedrichs cosine makes the sum of the generic parts closed. -/
theorem isClosed_genericSum_of_friedrichsCosine_lt_one
    (hc : friedrichsCosine U V < 1) :
    IsClosed (((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ) : Submodule 𝕜 H) : Set H) := by
  set A : Submodule 𝕜 H := U ⊓ (U ⊓ V)ᗮ with hA
  set B : Submodule 𝕜 H := V ⊓ (U ⊓ V)ᗮ with hB
  haveI : CompleteSpace A := (isClosed_genericPart hU (V := V)).completeSpace_coe
  haveI : CompleteSpace B := by
    have hclosed : IsClosed ((V ⊓ (V ⊓ U)ᗮ : Submodule 𝕜 H) : Set H) :=
      isClosed_genericPart hV (V := U)
    have hUV : (V ⊓ U : Submodule 𝕜 H) = U ⊓ V := inf_comm V U
    rw [hUV] at hclosed
    exact hclosed.completeSpace_coe
  set c : ℝ := friedrichsCosine U V with hcdef
  have hcnn : 0 ≤ c := friedrichsCosine_nonneg U V
  have hbound : ∀ z : A × B, Real.sqrt (1 - c) * ‖z‖ ≤ ‖subspaceSum A B z‖ := by
    intro z
    have hab : ‖⟪(z.1 : H), (z.2 : H)⟫_𝕜‖ ≤ c * ‖(z.1 : H)‖ * ‖(z.2 : H)‖ :=
      norm_inner_le_friedrichsCosine U V z.1.2 z.2.2
    have hexp : ‖(z.1 : H) + (z.2 : H)‖ ^ 2
        = ‖(z.1 : H)‖ ^ 2 + 2 * RCLike.re (⟪(z.1 : H), (z.2 : H)⟫_𝕜) + ‖(z.2 : H)‖ ^ 2 :=
      norm_add_sq (𝕜 := 𝕜) _ _
    have hre : -(c * ‖(z.1 : H)‖ * ‖(z.2 : H)‖) ≤ RCLike.re (⟪(z.1 : H), (z.2 : H)⟫_𝕜) := by
      have h1 : |RCLike.re (⟪(z.1 : H), (z.2 : H)⟫_𝕜)| ≤ ‖⟪(z.1 : H), (z.2 : H)⟫_𝕜‖ :=
        RCLike.abs_re_le_norm _
      have h2 := abs_le.mp (le_trans h1 hab)
      exact h2.1
    have hsq : (1 - c) * ‖z‖ ^ 2 ≤ ‖(z.1 : H) + (z.2 : H)‖ ^ 2 := by
      have hznorm : ‖z‖ = max ‖(z.1 : H)‖ ‖(z.2 : H)‖ := rfl
      have h1 : ‖z‖ ^ 2 ≤ ‖(z.1 : H)‖ ^ 2 + ‖(z.2 : H)‖ ^ 2 := by
        rw [hznorm]
        rcases max_cases ‖(z.1 : H)‖ ‖(z.2 : H)‖ with ⟨h, _⟩ | ⟨h, _⟩ <;>
          rw [h] <;>
          nlinarith [sq_nonneg ‖(z.1 : H)‖, sq_nonneg ‖(z.2 : H)‖,
            norm_nonneg (z.1 : H), norm_nonneg (z.2 : H)]
      nlinarith [sq_nonneg (‖(z.1 : H)‖ - ‖(z.2 : H)‖), hcnn, norm_nonneg (z.1 : H),
        norm_nonneg (z.2 : H), hc.le]
    have hnn : 0 ≤ 1 - c := by linarith
    calc Real.sqrt (1 - c) * ‖z‖ = Real.sqrt ((1 - c) * ‖z‖ ^ 2) := by
          rw [Real.sqrt_mul hnn, Real.sqrt_sq (norm_nonneg z)]
      _ ≤ Real.sqrt (‖(z.1 : H) + (z.2 : H)‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖subspaceSum A B z‖ := by rw [Real.sqrt_sq (norm_nonneg _)]; rfl
  have hpos : (0 : ℝ) < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have hanti : AntilipschitzWith (Real.toNNReal (Real.sqrt (1 - c))⁻¹) (subspaceSum A B) := by
    refine AddMonoidHomClass.antilipschitz_of_bound _ ?_
    intro z
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le), inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hbound z
  have hcl := hanti.isClosed_range (subspaceSum A B).uniformContinuous
  rwa [range_subspaceSum] at hcl

include hU hV in
/-- A closed sum of the generic parts forces a subunit Friedrichs cosine. -/
theorem friedrichsCosine_lt_one_of_isClosed_genericSum
    (hcl : IsClosed (((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ) : Submodule 𝕜 H) : Set H)) :
    friedrichsCosine U V < 1 := by
  set A : Submodule 𝕜 H := U ⊓ (U ⊓ V)ᗮ with hA
  set B : Submodule 𝕜 H := V ⊓ (U ⊓ V)ᗮ with hB
  haveI : CompleteSpace A := (isClosed_genericPart hU (V := V)).completeSpace_coe
  haveI : CompleteSpace B := by
    have hclosed : IsClosed ((V ⊓ (V ⊓ U)ᗮ : Submodule 𝕜 H) : Set H) :=
      isClosed_genericPart hV (V := U)
    have hUV : (V ⊓ U : Submodule 𝕜 H) = U ⊓ V := inf_comm V U
    rw [hUV] at hclosed
    exact hclosed.completeSpace_coe
  rcases Set.eq_empty_or_nonempty (friedrichsCosineSet U V) with hempty | hne
  · rw [friedrichsCosine, hempty, Real.sSup_empty]
    norm_num
  · have hrange : IsClosed (Set.range (subspaceSum A B)) := by rwa [range_subspaceSum]
    obtain ⟨M, hM⟩ :=
      ((subspaceSum A B).isClosed_range_iff_antilipschitz_of_injective
        (subspaceSum_injective (genericParts_inf_eq_bot (U := U) (V := V)))).mp hrange
    have hMbound : ∀ z : A × B, ‖z‖ ≤ (M : ℝ) * ‖(z.1 : H) + (z.2 : H)‖ := by
      intro z
      have hd := hM.le_mul_dist z 0
      simpa [dist_eq_norm] using hd
    -- a rotated pair of unit vectors turns the lower bound into a cosine bound
    have hkey : ∀ r ∈ friedrichsCosineSet U V, r ≤ 1 - 1 / (2 * (M : ℝ) ^ 2) ∧ 1 ≤ 2 * (M : ℝ) ^ 2 := by
      rintro r ⟨u, hu, v, hv, hun, hvn, rfl⟩
      obtain ⟨θ, hθ, hθval⟩ : ∃ θ : 𝕜, ‖θ‖ = 1 ∧ θ * ⟪u, v⟫_𝕜 = -((‖⟪u, v⟫_𝕜‖ : ℝ) : 𝕜) := by
        rcases eq_or_ne (⟪u, v⟫_𝕜) 0 with h0 | h0
        · exact ⟨1, norm_one, by rw [h0, mul_zero, norm_zero, RCLike.ofReal_zero, neg_zero]⟩
        · refine ⟨-((‖⟪u, v⟫_𝕜‖ : ℝ) : 𝕜) * (⟪u, v⟫_𝕜)⁻¹, ?_, ?_⟩
          · rw [norm_mul, norm_neg, norm_inv, RCLike.norm_ofReal,
              abs_of_nonneg (norm_nonneg _), mul_inv_cancel₀ (norm_ne_zero_iff.mpr h0)]
          · field_simp
      set t : ℝ := ‖⟪u, v⟫_𝕜‖ with ht
      have htnn : 0 ≤ t := norm_nonneg _
      have hvmem : θ • v ∈ B := Submodule.smul_mem _ _ hv
      have hvnorm : ‖θ • v‖ = 1 := by rw [norm_smul, hθ, hvn, one_mul]
      have hinner : ⟪u, θ • v⟫_𝕜 = -((t : ℝ) : 𝕜) := by
        rw [inner_smul_right, hθval]
      have hsum : ‖u + θ • v‖ ^ 2 = 2 - 2 * t := by
        rw [norm_add_sq (𝕜 := 𝕜) u (θ • v), hun, hvnorm, hinner, map_neg, RCLike.ofReal_re]
        ring
      set z : A × B := (⟨u, hu⟩, ⟨θ • v, hvmem⟩) with hz
      have hzn : ‖z‖ = 1 := by
        have hzz : ‖z‖ = max ‖(⟨u, hu⟩ : A)‖ ‖(⟨θ • v, hvmem⟩ : B)‖ := rfl
        have h1 : ‖(⟨u, hu⟩ : A)‖ = 1 := hun
        have h2 : ‖(⟨θ • v, hvmem⟩ : B)‖ = 1 := hvnorm
        rw [hzz, h1, h2, max_self]
      have hMz : 1 ≤ (M : ℝ) * ‖u + θ • v‖ := by
        have := hMbound z
        rwa [hzn] at this
      have hnormle : ‖u + θ • v‖ ^ 2 ≤ 2 := by rw [hsum]; linarith
      have hMpos : (0 : ℝ) < M := by
        by_contra hcon
        push Not at hcon
        nlinarith [norm_nonneg (u + θ • v)]
      have hMsq : 1 ≤ (M : ℝ) ^ 2 * ‖u + θ • v‖ ^ 2 := by nlinarith [norm_nonneg (u + θ • v)]
      have h2M : 1 ≤ 2 * (M : ℝ) ^ 2 := by nlinarith
      refine ⟨?_, h2M⟩
      have hfinal : 1 / (M : ℝ) ^ 2 ≤ 2 - 2 * t := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hsum]
      have hhalf : 1 / (2 * (M : ℝ) ^ 2) = (1 / (M : ℝ) ^ 2) / 2 := by
        field_simp
      rw [le_sub_iff_add_le, hhalf]
      linarith [hfinal]
    obtain ⟨r0, hr0⟩ := hne
    obtain ⟨_, h2M⟩ := hkey r0 hr0
    have hb0 : (0 : ℝ) ≤ 1 - 1 / (2 * (M : ℝ) ^ 2) := by
      have hpos : (0 : ℝ) < 2 * (M : ℝ) ^ 2 := by nlinarith
      rw [sub_nonneg, div_le_one hpos]
      exact h2M
    have hMpos : (0 : ℝ) < (M : ℝ) ^ 2 := by nlinarith
    have hle : friedrichsCosine U V ≤ 1 - 1 / (2 * (M : ℝ) ^ 2) :=
      Real.sSup_le (fun r hr => (hkey r hr).1) hb0
    have : (0 : ℝ) < 1 / (2 * (M : ℝ) ^ 2) := by positivity
    linarith

end GenericParts

/-- An orthogonal summand can be split off without affecting closedness. -/
theorem isClosed_sup_orthogonal_iff {W M : Submodule 𝕜 H} (hW : IsClosed (W : Set H))
    (hM : M ≤ Wᗮ) :
    IsClosed ((W ⊔ M : Submodule 𝕜 H) : Set H) ↔ IsClosed ((M : Submodule 𝕜 H) : Set H) := by
  haveI : CompleteSpace W := hW.completeSpace_coe
  have heq : (M : Submodule 𝕜 H) = (W ⊔ M) ⊓ Wᗮ := by
    refine le_antisymm (le_inf le_sup_right hM) ?_
    intro x hx
    obtain ⟨w, hw, m, hm, rfl⟩ := Submodule.mem_sup.mp hx.1
    have hwperp : w ∈ Wᗮ := by
      have hsplit : w = (w + m) - m := by abel
      rw [hsplit]
      exact Submodule.sub_mem _ hx.2 (hM hm)
    have hw0 : w = 0 := by
      have hzero : ⟪w, w⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ w).mp hwperp w hw
      exact (inner_self_eq_zero (𝕜 := 𝕜)).mp hzero
    rw [hw0, zero_add]
    exact hm
  constructor
  · intro h
    have hcoe : ((M : Submodule 𝕜 H) : Set H)
        = ((W ⊔ M : Submodule 𝕜 H) : Set H) ∩ ((Wᗮ : Submodule 𝕜 H) : Set H) := by
      conv_lhs => rw [heq]
      rfl
    rw [hcoe]
    exact h.inter (Submodule.isClosed_orthogonal _)
  · intro hMcl
    haveI : CompleteSpace M := hMcl.completeSpace_coe
    have hbound : ∀ z : W × M, (1 : ℝ) * ‖z‖ ≤ ‖subspaceSum W M z‖ := by
      intro z
      have hperp : ⟪(z.1 : H), (z.2 : H)⟫_𝕜 = 0 :=
        (Submodule.mem_orthogonal _ _).mp (hM z.2.2) (z.1 : H) z.1.2
      have hexp : ‖(z.1 : H) + (z.2 : H)‖ ^ 2 = ‖(z.1 : H)‖ ^ 2 + ‖(z.2 : H)‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := 𝕜), hperp, map_zero]
        ring
      have hznorm : ‖z‖ = max ‖(z.1 : H)‖ ‖(z.2 : H)‖ := rfl
      have hsq : ‖z‖ ^ 2 ≤ ‖(z.1 : H) + (z.2 : H)‖ ^ 2 := by
        rw [hexp, hznorm]
        rcases max_cases ‖(z.1 : H)‖ ‖(z.2 : H)‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
          nlinarith [sq_nonneg ‖(z.1 : H)‖, sq_nonneg ‖(z.2 : H)‖]
      have hle : ‖z‖ ≤ ‖(z.1 : H) + (z.2 : H)‖ := by
        nlinarith [norm_nonneg z, norm_nonneg ((z.1 : H) + (z.2 : H))]
      rw [one_mul]
      exact hle
    have hanti : AntilipschitzWith 1 (subspaceSum W M) := by
      refine AddMonoidHomClass.antilipschitz_of_bound _ ?_
      intro z
      simpa using hbound z
    have hcl := hanti.isClosed_range (subspaceSum W M).uniformContinuous
    rwa [range_subspaceSum] at hcl

section MainEquivalence

variable {U V : Submodule 𝕜 H} (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))

include hU hV in
theorem sup_eq_inf_sup_genericSum :
    (U ⊔ V : Submodule 𝕜 H)
      = (U ⊓ V) ⊔ ((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ)) := by
  have hWcl : IsClosed ((U ⊓ V : Submodule 𝕜 H) : Set H) := hU.inter hV
  haveI : CompleteSpace (U ⊓ V : Submodule 𝕜 H) := hWcl.completeSpace_coe
  have h1 : (U ⊓ V) ⊔ (U ⊓ (U ⊓ V)ᗮ) = U := by
    have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (K₁ := (U ⊓ V : Submodule 𝕜 H)) (K₂ := U) inf_le_left
    rwa [inf_comm ((U ⊓ V : Submodule 𝕜 H)ᗮ) U] at h
  have h2 : (U ⊓ V) ⊔ (V ⊓ (U ⊓ V)ᗮ) = V := by
    have h := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
      (K₁ := (U ⊓ V : Submodule 𝕜 H)) (K₂ := V) inf_le_right
    rwa [inf_comm ((U ⊓ V : Submodule 𝕜 H)ᗮ) V] at h
  calc (U ⊔ V : Submodule 𝕜 H)
      = ((U ⊓ V) ⊔ (U ⊓ (U ⊓ V)ᗮ)) ⊔ ((U ⊓ V) ⊔ (V ⊓ (U ⊓ V)ᗮ)) := by rw [h1, h2]
    _ = ((U ⊓ V) ⊔ (U ⊓ V)) ⊔ ((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ)) := sup_sup_sup_comm _ _ _ _
    _ = (U ⊓ V) ⊔ ((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ)) := by rw [sup_idem]

include hU hV in
theorem isClosed_sup_iff_isClosed_genericSum :
    IsClosed ((U ⊔ V : Submodule 𝕜 H) : Set H) ↔
      IsClosed (((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ) : Submodule 𝕜 H) : Set H) := by
  have hWcl : IsClosed ((U ⊓ V : Submodule 𝕜 H) : Set H) := hU.inter hV
  have hle : ((U ⊓ (U ⊓ V)ᗮ) ⊔ (V ⊓ (U ⊓ V)ᗮ) : Submodule 𝕜 H) ≤ (U ⊓ V : Submodule 𝕜 H)ᗮ :=
    sup_le inf_le_right inf_le_right
  rw [sup_eq_inf_sup_genericSum hU hV]
  exact isClosed_sup_orthogonal_iff hWcl hle

include hU hV in
/-- **The closed-sum characterization of the Friedrichs angle.**  The sum of two closed subspaces
is closed exactly when their Friedrichs cosine is strictly below one. -/
theorem friedrichsCosine_lt_one_iff_isClosed_sup :
    friedrichsCosine U V < 1 ↔ IsClosed ((U ⊔ V : Submodule 𝕜 H) : Set H) := by
  rw [isClosed_sup_iff_isClosed_genericSum hU hV]
  exact ⟨isClosed_genericSum_of_friedrichsCosine_lt_one hU hV,
    friedrichsCosine_lt_one_of_isClosed_genericSum hU hV⟩

end MainEquivalence

end GaloisForLFunctions.HTGeometry
