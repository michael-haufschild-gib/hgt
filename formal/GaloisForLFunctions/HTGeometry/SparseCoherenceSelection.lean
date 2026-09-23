import GaloisForLFunctions.HTGeometry.CoherenceLocalTailSaturation
import Mathlib.Logic.Denumerable

/-!
# Sparse coherence selection

This module turns cofinal smallness of a weight into the explicit sparse
embedding needed by the coherence-local saturation theorem.  The construction
chooses fresh coordinates with geometrically decreasing square budget, then
transports the resulting natural-number embedding to the countable
prefix-function coordinate type.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

deriving instance Countable for PrefixFunctionCoordinate

instance prefixFunctionCoordinate_infinite : Infinite PrefixFunctionCoordinate := by
  apply Infinite.of_injective (fun n : ℕ => (⟨n, fun _ => false⟩ : PrefixFunctionCoordinate))
  intro m n h
  exact congrArg Sigma.fst h

noncomputable def prefixFunctionCoordinateEquivNat : PrefixFunctionCoordinate ≃ ℕ :=
  nonempty_equiv_of_countable.some

/-- An embedding is an equivalence onto its set-theoretic range. -/
noncomputable def embeddingEquivRange {Q P : Type*} [Nonempty Q] (e : Q ↪ P) :
    Q ≃ Set.range e where
  toFun q := ⟨e q, ⟨q, rfl⟩⟩
  invFun p := Function.invFun e p.1
  left_inv q := Function.leftInverse_invFun e.injective q
  right_inv p := by
    apply Subtype.ext
    exact Function.invFun_eq p.2

theorem summable_indicator_embedding_range_iff
    {Q P : Type*} [Nonempty Q] (e : Q ↪ P) (f : P → ℝ) :
    Summable ((Set.range e).indicator f) ↔ Summable (fun q => f (e q)) := by
  have heq : Summable (fun q => f (e q)) ↔
      Summable (fun z : Set.range e => f z.1) := by
    simpa [embeddingEquivRange, Function.comp_def] using
      ((embeddingEquivRange e).summable_iff
        (f := fun z : Set.range e => f z.1))
  rw [← summable_subtype_iff_indicator]
  exact heq.symm

theorem tsum_indicator_embedding_range
    {Q P : Type*} [Nonempty Q] (e : Q ↪ P) (f : P → ℝ) :
    (∑' p, (Set.range e).indicator f p) = ∑' q, f (e q) := by
  rw [← tsum_subtype]
  exact (Equiv.tsum_eq (embeddingEquivRange e) (fun z : Set.range e => f z.1)).symm

/-- Cofinal smallness outside finite sets produces a sparse embedded copy of
the prefix coordinates whose total weighted square budget is below `B`. -/
theorem exists_sparsePrefixEmbedding_of_cofinally_small
    {P : Type*} [DecidableEq P] (r : P → ℝ) (B : ℝ) (hB : 0 < B)
    (hsmall : ∀ (F : Finset P) (d : ℝ), 0 < d →
      ∃ p, p ∉ F ∧ 4 * r p ^ (2 : ℕ) < d) :
    ∃ e : PrefixFunctionCoordinate ↪ P,
      Summable ((Set.range e).indicator (fun p => 4 * r p ^ (2 : ℕ))) ∧
      sparseCoherenceBudget r e < B := by
  let Good : ℕ × P → Prop := fun y => 4 * r y.2 ^ (2 : ℕ) < B / 4 / 2 ^ y.1
  let LaterFresh : (ℕ × P) → (ℕ × P) → Prop :=
    fun x y => x.1 < y.1 ∧ x.2 ≠ y.2
  have hstep : ∀ s : Finset (ℕ × P), (∀ x ∈ s, Good x) →
      ∃ y, Good y ∧ ∀ x ∈ s, LaterFresh x y := by
    intro s _
    let N := s.sup Prod.fst + 1
    let F : Finset P := s.image Prod.snd
    have hd : 0 < B / 4 / 2 ^ N := by positivity
    obtain ⟨p, hpF, hp⟩ := hsmall F (B / 4 / 2 ^ N) hd
    refine ⟨(N, p), hp, ?_⟩
    intro x hx
    constructor
    · exact lt_of_le_of_lt (Finset.le_sup (f := Prod.fst) hx) (Nat.lt_succ_self _)
    · intro hxp
      apply hpF
      exact Finset.mem_image.mpr ⟨x, hx, hxp⟩
  obtain ⟨f, hfGood, hfFresh⟩ :=
    exists_seq_of_forall_finset_exists Good LaterFresh hstep
  let k : ℕ → ℕ := fun n => (f n).1
  let g : ℕ → P := fun n => (f n).2
  have hk : Function.Injective k := by
    intro m n hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · have hkn := (hfFresh m n hlt).1
      exact ((ne_of_lt hkn) hmn).elim
    · exact heq
    · have hkm := (hfFresh n m hgt).1
      exact ((ne_of_gt hkm) hmn).elim
  have hg : Function.Injective g := by
    intro m n hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact ((hfFresh m n hlt).2 hmn).elim
    · exact heq
    · exact ((hfFresh n m hgt).2 hmn.symm).elim
  let eNat : ℕ ↪ P := ⟨g, hg⟩
  let qNat : PrefixFunctionCoordinate ≃ ℕ := prefixFunctionCoordinateEquivNat
  let e : PrefixFunctionCoordinate ↪ P :=
    ⟨fun q => g (qNat q), fun _ _ h => qNat.injective (hg h)⟩
  let u : ℕ → ℝ := fun n => 4 * r (g n) ^ (2 : ℕ)
  let v : ℕ → ℝ := fun n => B / 4 / 2 ^ (k n)
  let geom : ℕ → ℝ := fun n => (B / 2) / 2 / 2 ^ n
  have huv : ∀ n, u n ≤ v n := fun n => (hfGood n).le
  have hgeom : Summable geom := by
    simpa only [geom] using summable_geometric_two' (B / 2)
  have hv : Summable v := by
    have hcomp := hgeom.comp_injective hk
    convert! hcomp using 1
    funext n
    simp only [v, geom, Function.comp_apply]
    ring
  have hu : Summable u :=
    Summable.of_nonneg_of_le (fun n => by simp only [u]; positivity) huv hv
  have htsum : (∑' n, u n) < B := by
    have huvsum : (∑' n, u n) ≤ ∑' n, v n := hu.tsum_le_tsum huv hv
    have hvgeom : (∑' n, v n) ≤ ∑' n, geom n := by
      apply Summable.tsum_le_tsum_of_inj k hk
      · intro n _
        simp only [geom]
        positivity
      · intro n
        simp only [v, geom]
        ring_nf
        exact le_rfl
      · exact hv
      · exact hgeom
    calc
      (∑' n, u n) ≤ ∑' n, v n := huvsum
      _ ≤ ∑' n, geom n := hvgeom
      _ = B / 2 := by simpa only [geom] using tsum_geometric_two' (B / 2)
      _ < B := by linarith
  refine ⟨e, ?_, ?_⟩
  · rw [summable_indicator_embedding_range_iff]
    have htransport := (qNat.summable_iff (f := u)).2 hu
    change Summable (u ∘ qNat)
    exact htransport
  · rw [sparseCoherenceBudget, tsum_indicator_embedding_range]
    have htransport := Equiv.tsum_eq qNat u
    change (∑' q, u (qNat q)) < B
    rw [htransport]
    exact htsum

/-- **Finite-rank local saturation.**  Every finite injective sequence family
can be embedded around an arbitrary base orientation with full tail rank while
all base and pairwise distances stay below the requested square budget. -/
theorem exists_coherenceLocalTailIndependentFamily_of_cofinally_small
    {I P : Type*} [Fintype I] [DecidableEq P]
    (r : P → ℝ) (B : ℝ) (hB : 0 < B)
    (hsmall : ∀ (F : Finset P) (d : ℝ), 0 < d →
      ∃ p, p ∉ F ∧ 4 * r p ^ (2 : ℕ) < d)
    (base : P → Bool) (x : I → ℕ → Bool) (hx : Function.Injective x) :
    ∃ e : PrefixFunctionCoordinate ↪ P,
      PrimeOrientationTailIndependent
        (fun i => basedSparsePrefixOrientation base e (x i)) ∧
      (∀ i, weightedOrientationDistanceSq r
        (basedSparsePrefixOrientation base e (x i)) base < B) ∧
      ∀ i j, weightedOrientationDistanceSq r
        (basedSparsePrefixOrientation base e (x i))
        (basedSparsePrefixOrientation base e (x j)) < B := by
  obtain ⟨e, hsum, hbudget⟩ :=
    exists_sparsePrefixEmbedding_of_cofinally_small r B hB hsmall
  refine ⟨e, basedSparsePrefixOrientation_tailIndependent base e x hx, ?_, ?_⟩
  · intro i
    exact basedSparsePrefixOrientation_distance_base_lt base e r (x i) B hsum hbudget
  · intro i j
    exact basedSparsePrefixOrientation_pair_distance_lt base e r (x i) (x j) B hsum hbudget

end

end GaloisForLFunctions.HTGeometry
