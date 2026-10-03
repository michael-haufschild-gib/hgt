import GaloisForLFunctions.HTGeometry.TopologicallySimpleFormationIdempotenceDefect
import GaloisForLFunctions.HTGeometry.SchattenCubicMass
import GaloisForLFunctions.HTGeometry.BlockDiagonalSingularValues
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-!
# The compact operators form a topologically simple ring

On a complex Hilbert space `H` the compact operators `𝒦(H)` are a non-unital subring of `B(H)`.
Every nonzero closed two-sided ideal of `𝒦(H)` is all of `𝒦(H)`:

* if `T ≠ 0` and `Tv ≠ 0`, every rank-one operator factors as
  `|y⟩⟨x| = (‖Tv‖^{-2} |y⟩⟨Tv|) T |v⟩⟨x|`, so an ideal containing `T` contains all rank-one
  operators, hence all finite-rank operators (an orthonormal basis of a finite-dimensional range);
* compact operators are operator-norm limits of finite-rank ones (their approximation numbers tend
  to zero), so a closed ideal containing the finite-rank operators is everything.

The same holds for the matrix amplifications `M_n(𝒦(H))`: the entries of a closed ideal at a fixed
position form a closed ideal of `𝒦(H)`, which is nonzero by the rank-one factorization.

Consequently, for an injective compact `T` on an infinite-dimensional space the idempotence defect
`T - T²` is nonzero and generates `𝒦(H)` as a closed ideal.
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower InnerProductSpace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compact operators as a non-unital subring of `B(H)`. -/
def compactOperatorSubring : NonUnitalSubring (H →L[ℂ] H) where
  carrier := {T | IsCompactOperator T}
  add_mem' := fun ha hb => ha.add hb
  zero_mem' := isCompactOperator_zero
  neg_mem' := fun ha => ha.neg
  mul_mem' := fun {a b} ha _ => show IsCompactOperator (⇑a ∘ ⇑b) from ha.comp_clm b

/-- The compact-operator ring `𝒦(H)`. -/
abbrev CompactOperatorRing := ↥(compactOperatorSubring H)

variable {H}

omit [CompleteSpace H] in
theorem rankOne_mem_compactOperatorSubring (x y : H) :
    rankOne ℂ x y ∈ compactOperatorSubring H :=
  isCompactOperator_innerRankOne x y

omit [CompleteSpace H] in
/-- **Rank-one factorization.**  If `Tv ≠ 0` then `|y⟩⟨x| = (⟨Tv,Tv⟩^{-1}|y⟩⟨Tv|) T |v⟩⟨x|`. -/
theorem rankOne_eq_mul_mul {T : H →L[ℂ] H} {v : H} (hv : T v ≠ 0) (x y : H) :
    rankOne ℂ y x = ((⟪T v, T v⟫_ℂ)⁻¹ • rankOne ℂ y (T v)) * T * rankOne ℂ v x := by
  have hn : ⟪T v, T v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [mul_apply_eq_comp, smul_apply, rankOne_apply, map_smul, smul_smul]
  rw [inv_mul_cancel₀ hn, mul_one]

/-- Compact operators are operator-norm limits of finite-rank operators. -/
theorem exists_finiteRank_tendsto {S : H →L[ℂ] H} (hS : IsCompactOperator S) :
    ∃ F : ℕ → H →L[ℂ] H, (∀ m, ∃ n, HasRankLE (F m) n) ∧ Tendsto F atTop (𝓝 S) := by
  have hlim : Tendsto (approxNumber S) atTop (𝓝 0) := by
    have h := tendsto_rectApproxNumber_of_isCompactOperator hS
    exact h.congr fun n => (approxNumber_eq_rectApproxNumber S n).symm
  have hex : ∀ m : ℕ, ∃ F : H →L[ℂ] H, (∃ n, HasRankLE F n) ∧ ‖S - F‖ < 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity :
      (0 : ℝ) < 1 / ((m : ℝ) + 1)))).exists
    obtain ⟨F, hF, hFS⟩ := exists_hasRankLE_norm_sub_lt S n hn
    exact ⟨F, ⟨n, hF⟩, hFS⟩
  choose F hF hFS using hex
  refine ⟨F, hF, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [norm_sub_rev]
  exact (hFS m).le

/-- A finite-rank operator is a finite sum of rank-one operators `|b_i⟩⟨F^* b_i|`. -/
theorem exists_eq_sum_rankOne {F : H →L[ℂ] H} {n : ℕ} (hF : HasRankLE F n) :
    ∃ (ι : Type) (_ : Fintype ι) (b c : ι → H), F = ∑ i, rankOne ℂ (b i) (c i) := by
  obtain ⟨V, hfd, -, hmem⟩ := hF
  let e := stdOrthonormalBasis ℂ V
  refine ⟨Fin (Module.finrank ℂ V), inferInstance, fun i => (e i : H),
    fun i => ContinuousLinearMap.adjoint F (e i), ?_⟩
  refine ContinuousLinearMap.ext fun x => ?_
  rw [sum_apply]
  simp only [rankOne_apply, ContinuousLinearMap.adjoint_inner_left]
  have h := e.sum_repr' ⟨F x, hmem x⟩
  have h' := congrArg (Subtype.val : V → H) h
  rw [Submodule.coe_sum] at h'
  simpa only [Submodule.coe_smul, Submodule.coe_inner] using h'.symm

theorem twoSidedIdeal_sum_mem {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)
    {ι : Type*} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, f i ∈ I) : ∑ i ∈ s, f i ∈ I :=
  Finset.sum_induction f (· ∈ I) (fun _ _ ha hb => I.add_mem ha hb) I.zero_mem h

omit [CompleteSpace H] in
/-- An ideal of `𝒦(H)` containing a nonzero element contains every rank-one operator. -/
theorem rankOne_mem_of_mem {I : TwoSidedIdeal (CompactOperatorRing H)} {T : CompactOperatorRing H}
    (hT : T ∈ I) (hT0 : T ≠ 0) (x y : H) :
    (⟨rankOne ℂ y x, rankOne_mem_compactOperatorSubring y x⟩ : CompactOperatorRing H) ∈ I := by
  have hT0' : (T : H →L[ℂ] H) ≠ 0 := fun h => hT0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, (T : H →L[ℂ] H) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0' (ContinuousLinearMap.ext h)
  let A : CompactOperatorRing H := ⟨(⟪(T : H →L[ℂ] H) v, (T : H →L[ℂ] H) v⟫_ℂ)⁻¹ •
      rankOne ℂ y ((T : H →L[ℂ] H) v),
    show IsCompactOperator ((⟪(T : H →L[ℂ] H) v, (T : H →L[ℂ] H) v⟫_ℂ)⁻¹ •
        ⇑(rankOne ℂ y ((T : H →L[ℂ] H) v))) from
      (isCompactOperator_innerRankOne y ((T : H →L[ℂ] H) v)).smul _⟩
  let B : CompactOperatorRing H := ⟨rankOne ℂ v x, rankOne_mem_compactOperatorSubring v x⟩
  have hfac : (⟨rankOne ℂ y x, rankOne_mem_compactOperatorSubring y x⟩ : CompactOperatorRing H) =
      A * T * B := Subtype.ext (rankOne_eq_mul_mul hv x y)
  rw [hfac]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hT)

/-- **The compact operators form a topologically simple ring.** -/
instance : IsTopologicallySimpleRing (CompactOperatorRing H) where
  eq_bot_or_eq_top I hI := by
    by_cases hbot : I = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨T, hT, hT0⟩ : ∃ T ∈ I, T ≠ 0 := by
      by_contra h
      push Not at h
      exact hbot (TwoSidedIdeal.ext fun x => ⟨fun hx => by simpa using h x hx,
        fun hx => by rw [show x = 0 by simpa using hx]; exact I.zero_mem⟩)
    have hfin : ∀ S : CompactOperatorRing H, (∃ n, HasRankLE (S : H →L[ℂ] H) n) → S ∈ I := by
      rintro S ⟨n, hn⟩
      obtain ⟨ι, _, b, c, hS⟩ := exists_eq_sum_rankOne hn
      have hS' : S = ∑ i, (⟨rankOne ℂ (b i) (c i), rankOne_mem_compactOperatorSubring _ _⟩ :
          CompactOperatorRing H) := by
        apply Subtype.ext
        rw [hS]
        push_cast
        rfl
      rw [hS']
      exact twoSidedIdeal_sum_mem I _ _ fun i _ => rankOne_mem_of_mem hT hT0 (c i) (b i)
    have hall : ∀ S : CompactOperatorRing H, S ∈ I := by
      intro S
      obtain ⟨F, hF, hFS⟩ := exists_finiteRank_tendsto S.2
      let F' : ℕ → CompactOperatorRing H := fun m =>
        ⟨F m, by obtain ⟨n, hn⟩ := hF m; exact isCompactOperator_of_hasRankLE hn⟩
      refine hI.mem_of_tendsto ((tendsto_subtype_rng (f := F') (x := S)).2 hFS)
        (Eventually.of_forall fun m => ?_)
      exact hfin (F' m) (hF m)
    exact TwoSidedIdeal.ext fun S => ⟨fun _ => trivial, fun _ => hall S⟩

omit [CompleteSpace H] in
/-- A nonzero compact operator `T` admits compact `A, B` with `A T B ≠ 0`. -/
theorem exists_mul_mul_ne_zero {T : CompactOperatorRing H} (hT0 : T ≠ 0) :
    ∃ A B : CompactOperatorRing H, A * T * B ≠ 0 := by
  have hT0' : (T : H →L[ℂ] H) ≠ 0 := fun h => hT0 (Subtype.ext h)
  obtain ⟨v, hv⟩ : ∃ v, (T : H →L[ℂ] H) v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT0' (ContinuousLinearMap.ext h)
  set w := (T : H →L[ℂ] H) v
  refine ⟨⟨(⟪w, w⟫_ℂ)⁻¹ • rankOne ℂ w w,
      show IsCompactOperator ((⟪w, w⟫_ℂ)⁻¹ • ⇑(rankOne ℂ w w)) from
        (isCompactOperator_innerRankOne w w).smul _⟩,
    ⟨rankOne ℂ v w, rankOne_mem_compactOperatorSubring v w⟩, fun h => ?_⟩
  have h1 := congrArg (fun A : CompactOperatorRing H => (A : H →L[ℂ] H) w) h
  rw [show (((⟨(⟪w, w⟫_ℂ)⁻¹ • rankOne ℂ w w, _⟩ : CompactOperatorRing H) * T *
      ⟨rankOne ℂ v w, rankOne_mem_compactOperatorSubring v w⟩ : CompactOperatorRing H) :
        H →L[ℂ] H) = rankOne ℂ w w from (rankOne_eq_mul_mul hv w w).symm] at h1
  rw [rankOne_apply, ZeroMemClass.coe_zero, zero_apply, smul_eq_zero] at h1
  exact h1.elim (inner_self_ne_zero.2 hv) hv

/-! ## Matrix amplifications -/

theorem continuous_matrix_single {R : Type*} [TopologicalSpace R] [Zero R] {n : ℕ}
    (i j : Fin n) : Continuous fun S : R => Matrix.single i j S := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · have he : (fun S : R => Matrix.single i j S a b) = fun S => S :=
      funext fun S => by simp [h]
    rw [he]
    exact continuous_id
  · have he : (fun S : R => Matrix.single i j S a b) = fun _ => 0 :=
      funext fun S => by simp [h]
    rw [he]
    exact continuous_const

/-- **The matrix amplifications `M_n(𝒦(H))` are topologically simple.** -/
instance isTopologicallySimpleRing_matrix_compactOperatorRing (n : ℕ) :
    IsTopologicallySimpleRing (Matrix (Fin n) (Fin n) (CompactOperatorRing H)) where
  eq_bot_or_eq_top J hJ := by
    by_cases hbot : J = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨M, hM, hM0⟩ : ∃ M ∈ J, M ≠ 0 := by
      by_contra h
      push Not at h
      exact hbot (TwoSidedIdeal.ext fun x => ⟨fun hx => by simpa using h x hx,
        fun hx => by rw [show x = 0 by simpa using hx]; exact J.zero_mem⟩)
    obtain ⟨k, l, hkl⟩ : ∃ k l, M k l ≠ 0 := by
      by_contra h
      push Not at h
      exact hM0 (Matrix.ext h)
    have hsingle : ∀ i j (S : CompactOperatorRing H), Matrix.single i j S ∈ J := by
      intro i j
      let I : TwoSidedIdeal (CompactOperatorRing H) := TwoSidedIdeal.mk'
        {S | Matrix.single i j S ∈ J}
        (by simp [J.zero_mem])
        (fun {a b} ha hb => by
          simpa [Set.mem_setOf_eq, Matrix.single_add] using J.add_mem ha hb)
        (fun {a} ha => by
          simpa [Set.mem_setOf_eq, Matrix.single_neg] using J.neg_mem ha)
        (fun {a b} hb => by
          rw [Set.mem_setOf_eq, ← Matrix.single_mul_single_same a i i j b]
          exact J.mul_mem_left _ _ hb)
        (fun {a b} ha => by
          rw [Set.mem_setOf_eq, ← Matrix.single_mul_single_same a i j j b]
          exact J.mul_mem_right _ _ ha)
      have hIclosed : IsClosed (I : Set (CompactOperatorRing H)) := by
        rw [TwoSidedIdeal.coe_mk']
        exact hJ.preimage (continuous_matrix_single i j)
      have hmem : ∀ A B : CompactOperatorRing H, A * M k l * B ∈ I := fun A B => by
        rw [TwoSidedIdeal.mem_mk', Set.mem_setOf_eq, ← Matrix.single_mul_mul_single]
        exact J.mul_mem_right _ _ (J.mul_mem_left _ _ hM)
      have hIne : I ≠ ⊥ := by
        obtain ⟨A, B, hAB⟩ := exists_mul_mul_ne_zero hkl
        intro hI
        have h := hmem A B
        rw [hI] at h
        exact hAB (by simpa using h)
      have htop := (IsTopologicallySimpleRing.eq_bot_or_eq_top I hIclosed).resolve_left hIne
      intro S
      have hS : S ∈ I := by rw [htop]; trivial
      simpa [I, TwoSidedIdeal.mem_mk'] using hS
    refine TwoSidedIdeal.ext fun N => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [Matrix.matrix_eq_sum_single N]
    exact twoSidedIdeal_sum_mem J _ _ fun i _ =>
      twoSidedIdeal_sum_mem J _ _ fun j _ => hsingle i j (N i j)

/-! ## Faithful compact formation -/

omit [CompleteSpace H] in
/-- **(PHFI.4), nonvanishing.**  An injective compact operator on an infinite-dimensional space is
not idempotent: `T - T² ≠ 0`. -/
theorem formationIdempotenceDefect_ne_zero (hH : ¬ FiniteDimensional ℂ H)
    (T : CompactOperatorRing H) (hT : Function.Injective (T : H →L[ℂ] H)) :
    formationIdempotenceDefect T ≠ 0 := by
  intro h
  have hTT : ∀ x, (T : H →L[ℂ] H) ((T : H →L[ℂ] H) x) = (T : H →L[ℂ] H) x := fun x => by
    have h1 := congrArg (fun A : CompactOperatorRing H => (A : H →L[ℂ] H) x) h
    change ((T : H →L[ℂ] H) - (T : H →L[ℂ] H) * (T : H →L[ℂ] H)) x = (0 : H →L[ℂ] H) x at h1
    rw [sub_apply, mul_apply_eq_comp, zero_apply, sub_eq_zero] at h1
    exact h1.symm
  have hid : ⇑(T : H →L[ℂ] H) = id := funext fun x => hT (hTT x)
  apply hH
  have hc : IsCompactOperator (id : H → H) := hid ▸ T.2
  exact isCompactOperator_id_iff_finiteDimensional.1 hc

/-- **(PHFI.4), fullness.**  Every closed two-sided ideal of `𝒦(H)` containing `T - T²` is `𝒦(H)`. -/
theorem eq_top_of_formationIdempotenceDefect_mem (hH : ¬ FiniteDimensional ℂ H)
    (T : CompactOperatorRing H) (hT : Function.Injective (T : H →L[ℂ] H))
    (I : TwoSidedIdeal (CompactOperatorRing H)) (hI : IsClosed (I : Set (CompactOperatorRing H)))
    (hmem : formationIdempotenceDefect T ∈ I) : I = ⊤ :=
  (IsTopologicallySimpleRing.eq_bot_or_eq_top I hI).resolve_left fun hbot =>
    formationIdempotenceDefect_ne_zero hH T hT (by rw [hbot] at hmem; simpa using hmem)

end GaloisForLFunctions.HTGeometry
