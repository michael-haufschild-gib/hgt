/-
Classical nuclear-series bridge for the project Schatten-1 interface.

The project defines Schatten classes through approximation numbers.  This file supplies the
missing direct bridge from an operator-norm convergent rank-one expansion to that definition.
It is infrastructure, not a novelty claim: the only input beyond convergence is summability of
the operator-norm tails.
-/
import GaloisForLFunctions.RHTower.TraceNorm

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Rank bounds add under operator addition. -/
theorem HasRankLE.add {S T : H →L[ℂ] H} {m n : ℕ}
    (hS : HasRankLE S m) (hT : HasRankLE T n) : HasRankLE (S + T) (m + n) := by
  obtain ⟨V, hVfd, hVrank, hSV⟩ := hS
  obtain ⟨W, hWfd, hWrank, hTW⟩ := hT
  letI : FiniteDimensional ℂ V := hVfd
  letI : FiniteDimensional ℂ W := hWfd
  refine ⟨V ⊔ W, inferInstance, ?_, fun z => ?_⟩
  · have hdim := Submodule.finrank_sup_add_finrank_inf_eq V W
    omega
  · rw [_root_.add_apply]
    exact Submodule.add_mem (V ⊔ W)
      ((show V ≤ V ⊔ W from le_sup_left) (hSV z))
      ((show W ≤ V ⊔ W from le_sup_right) (hTW z))

omit [CompleteSpace H] in
/-- A sum of `n` operators of rank at most one has rank at most `n`. -/
theorem hasRankLE_sum_range_of_rankOne
    (A : ℕ → H →L[ℂ] H) (hA : ∀ k, HasRankLE (A k) 1) (n : ℕ) :
    HasRankLE (∑ k ∈ Finset.range n, A k) n := by
  induction n with
  | zero => simpa using hasRankLE_zero (H := H) 0
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simpa using ih.add (hA n)

omit [CompleteSpace H] in
/-- A sum of the first `n` rank-one operators has rank at most `n`. -/
theorem hasRankLE_sum_range_rankOne (x y : ℕ → H) (n : ℕ) :
    HasRankLE (∑ k ∈ Finset.range n, InnerProductSpace.rankOne ℂ (x k) (y k)) n := by
  classical
  refine ⟨Submodule.span ℂ
      ((((Finset.range n).image x : Finset H) : Set H)),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
  · exact (finrank_span_finset_le_card _).trans
      (Finset.card_image_le.trans (by simp))
  · intro z
    rw [_root_.sum_apply]
    refine Submodule.sum_mem _ fun k hk => ?_
    rw [InnerProductSpace.rankOne_apply]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hk)))

/-- Approximation-number tail bound for an arbitrary operator series whose individual terms have
rank at most one. -/
theorem approxNumber_tsum_rankOneTerms_le_tail
    (A : ℕ → H →L[ℂ] H) (hA : ∀ k, HasRankLE (A k) 1)
    (hnorm : Summable (fun k => ‖A k‖)) (n : ℕ) :
    approxNumber (∑' k, A k) n ≤ ∑' k, ‖A (k + n)‖ := by
  let F : H →L[ℂ] H := ∑ k ∈ Finset.range n, A k
  have hsum : Summable A := Summable.of_norm hnorm
  have hrank : HasRankLE F n := by
    simpa [F] using hasRankLE_sum_range_of_rankOne A hA n
  refine (approxNumber_le (∑' k, A k) n F hrank).trans ?_
  have htailNorm : Summable (fun k => ‖A (k + n)‖) :=
    (summable_nat_add_iff n).2 hnorm
  have hsplit : F + ∑' k, A (k + n) = ∑' k, A k := by
    simpa [F] using hsum.sum_add_tsum_nat_add n
  have hdiff : (∑' k, A k) - F = ∑' k, A (k + n) := by
    rw [← hsplit]
    abel
  rw [hdiff]
  exact norm_tsum_le_tsum_norm htailNorm

/-- Any absolutely convergent series of rank-at-most-one terms with summable norm tails defines a
Schatten-1 operator. -/
theorem memSchattenClass_one_tsum_rankOneTerms
    (A : ℕ → H →L[ℂ] H) (hA : ∀ k, HasRankLE (A k) 1)
    (hnorm : Summable (fun k => ‖A k‖))
    (htail : Summable (fun n => ∑' k, ‖A (k + n)‖)) :
    MemSchattenClass 1 (∑' k, A k) := by
  have happ : Summable (fun n => approxNumber (∑' k, A k) n) :=
    Summable.of_nonneg_of_le
      (fun n => approxNumber_nonneg _ n)
      (fun n => approxNumber_tsum_rankOneTerms_le_tail A hA hnorm n)
      htail
  exact happ.congr fun n => (Real.rpow_one _).symm

/-- The `n`-th approximation number of a convergent rank-one series is bounded by its
operator-norm tail after the first `n` terms. -/
theorem approxNumber_tsum_rankOne_le_tail
    (x y : ℕ → H)
    (hnorm : Summable (fun k =>
      ‖InnerProductSpace.rankOne ℂ (x k) (y k)‖))
    (n : ℕ) :
    approxNumber (∑' k, InnerProductSpace.rankOne ℂ (x k) (y k)) n ≤
      ∑' k, ‖InnerProductSpace.rankOne ℂ (x (k + n)) (y (k + n))‖ := by
  let A : ℕ → H →L[ℂ] H := fun k => InnerProductSpace.rankOne ℂ (x k) (y k)
  let F : H →L[ℂ] H := ∑ k ∈ Finset.range n, A k
  have hsum : Summable A := by
    apply Summable.of_norm
    simpa [A] using hnorm
  have hrank : HasRankLE F n := by
    simpa [A, F] using hasRankLE_sum_range_rankOne x y n
  refine (approxNumber_le (∑' k, A k) n F hrank).trans ?_
  have htailNorm : Summable (fun k => ‖A (k + n)‖) := by
    simpa [A] using (summable_nat_add_iff n).2 hnorm
  have hsplit : F + ∑' k, A (k + n) = ∑' k, A k := by
    simpa [F] using hsum.sum_add_tsum_nat_add n
  have hdiff : (∑' k, A k) - F = ∑' k, A (k + n) := by
    rw [← hsplit]
    abel
  rw [hdiff]
  exact norm_tsum_le_tsum_norm htailNorm

/-- **Nuclear rank-one series are Schatten-1.**  If the operator series converges and the
sequence of its operator-norm tails is summable, then its sum belongs to the project's genuine
Schatten `1` class. -/
theorem memSchattenClass_one_tsum_rankOne
    (x y : ℕ → H)
    (hnorm : Summable (fun k =>
      ‖InnerProductSpace.rankOne ℂ (x k) (y k)‖))
    (htail : Summable (fun n =>
      ∑' k, ‖InnerProductSpace.rankOne ℂ (x (k + n)) (y (k + n))‖)) :
    MemSchattenClass 1 (∑' k, InnerProductSpace.rankOne ℂ (x k) (y k)) := by
  have happ : Summable (fun n =>
      approxNumber (∑' k, InnerProductSpace.rankOne ℂ (x k) (y k)) n) :=
    Summable.of_nonneg_of_le
      (fun n => approxNumber_nonneg _ n)
      (fun n => approxNumber_tsum_rankOne_le_tail x y hnorm n)
      htail
  exact happ.congr fun n => (Real.rpow_one _).symm

/-- A weighted first moment controls the sum of all tails.  This is the discrete Tonelli
identity needed to turn factorial decay of a nuclear expansion into Schatten-1 summability. -/
theorem summable_tsum_nat_add_of_summable_succ_mul
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hw : Summable (fun n => ((n + 1 : ℕ) : ℝ) * a n)) :
    Summable (fun n => ∑' k, a (k + n)) := by
  let h : ℕ × ℕ → ℝ := fun p => if p.2 ≤ p.1 then a p.1 else 0
  have hh0 : 0 ≤ h := by
    intro p
    dsimp [h]
    split_ifs <;> simp [ha]
  have hh : Summable h := by
    rw [summable_prod_of_nonneg hh0]
    constructor
    · intro k
      apply summable_of_ne_finset_zero (s := Finset.range (k + 1))
      intro n hn
      have hkn : k < n := Nat.lt_of_not_ge (by simpa using hn)
      simp [h, Nat.not_le.mpr hkn]
    · convert hw using 1
      funext k
      rw [tsum_eq_sum (s := Finset.range (k + 1))]
      · rw [Finset.sum_congr rfl (fun n hn => if_pos
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))]
        simp [nsmul_eq_mul, Nat.cast_add]
      · intro n hn
        have hkn : k < n := Nat.lt_of_not_ge (by simpa using hn)
        simp [h, Nat.not_le.mpr hkn]
  let e : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.1)
  have he : Function.Injective e := by
    rintro ⟨n, j⟩ ⟨n', j'⟩ hp
    simp only [e, Prod.mk.injEq] at hp
    obtain ⟨hsum, hn⟩ := hp
    subst n'
    exact Prod.ext rfl (Nat.add_left_cancel hsum)
  have hp : Summable (fun p : ℕ × ℕ => a (p.2 + p.1)) := by
    have hc := hh.comp_injective he
    refine hc.congr fun p => ?_
    simp only [Function.comp_apply, h, e]
    rw [if_pos (Nat.le_add_right p.1 p.2), add_comm]
  exact (summable_prod_of_nonneg (fun p => ha _)).1 hp |>.2

section InvariantSubspace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (S : Submodule ℂ E) [S.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- Orthogonal compression cannot increase a finite-rank bound. -/
theorem HasRankLE.orthogonalCompression {F : E →L[ℂ] E} {n : ℕ}
    (hF : HasRankLE F n) :
    HasRankLE (S.orthogonalProjection ∘L F ∘L S.subtypeL) n := by
  obtain ⟨V, hVfd, hVrank, hFV⟩ := hF
  haveI : Module.Finite ℂ V := hVfd
  refine ⟨V.map S.orthogonalProjection.toLinearMap, inferInstance,
    (Submodule.finrank_map_le _ V).trans hVrank, ?_⟩
  intro x
  exact Submodule.mem_map_of_mem (hFV x)

omit [CompleteSpace E] in
/-- Restriction to an invariant closed subspace equals orthogonal compression. -/
theorem restrict_eq_orthogonalCompression
    (T : E →L[ℂ] E) (hmap : Set.MapsTo T S S) :
    T.restrict hmap = S.orthogonalProjection ∘L T ∘L S.subtypeL := by
  apply ContinuousLinearMap.ext
  intro x
  change (⟨T x, hmap x.property⟩ : S) = S.orthogonalProjection (T x)
  exact (S.orthogonalProjection_mem_subspace_eq_self
    (⟨T x, hmap x.property⟩ : S)).symm

omit [CompleteSpace E] in
/-- Orthogonal compression is contractive in operator norm. -/
theorem norm_orthogonalCompression_le (T : E →L[ℂ] E) :
    ‖S.orthogonalProjection ∘L T ∘L S.subtypeL‖ ≤ ‖T‖ := by
  apply (S.orthogonalProjection ∘L T ∘L S.subtypeL).opNorm_le_bound
    (norm_nonneg T)
  intro x
  change ‖S.orthogonalProjection (T (x : E))‖ ≤ ‖T‖ * ‖x‖
  exact (S.norm_orthogonalProjection_apply_le (T (x : E))).trans (T.le_opNorm x)

omit [CompleteSpace E] in
/-- Approximation numbers do not increase under restriction to an invariant closed subspace. -/
theorem approxNumber_restrict_le
    (T : E →L[ℂ] E) (hmap : Set.MapsTo T S S) (n : ℕ) :
    approxNumber (T.restrict hmap) n ≤ approxNumber T n := by
  refine le_csInf (approxNumber_set_nonempty T n) ?_
  rintro r ⟨F, hF, rfl⟩
  let G : S →L[ℂ] S := S.orthogonalProjection ∘L F ∘L S.subtypeL
  have hG : HasRankLE G n := hF.orthogonalCompression S
  refine (approxNumber_le (T.restrict hmap) n G hG).trans ?_
  rw [restrict_eq_orthogonalCompression S T hmap]
  have heq : S.orthogonalProjection ∘L T ∘L S.subtypeL - G =
      S.orthogonalProjection ∘L (T - F) ∘L S.subtypeL := by
    apply ContinuousLinearMap.ext
    intro x
    change S.orthogonalProjection (T x) - S.orthogonalProjection (F x) =
      S.orthogonalProjection (T x - F x)
    rw [map_sub]
  rw [heq]
  exact norm_orthogonalCompression_le S (T - F)

/-- Schatten-1 membership descends to every invariant closed Hilbert subspace. -/
theorem memSchattenClass_one_restrict
    (T : E →L[ℂ] E) (hmap : Set.MapsTo T S S)
    (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (T.restrict hmap) := by
  have hs : Summable (fun n => approxNumber T n) :=
    hT.congr fun n => Real.rpow_one _
  have hr : Summable (fun n => approxNumber (T.restrict hmap) n) :=
    Summable.of_nonneg_of_le (fun n => approxNumber_nonneg _ n)
      (fun n => approxNumber_restrict_le S T hmap n) hs
  exact hr.congr fun n => (Real.rpow_one _).symm

end InvariantSubspace

end RHTower
