import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFrameGeneration

/-!
# The codimension of the horizon field of a span

The jet determinant of a covector span is a horizon observable of that span, so the jet coordinates
of the initial block are not free over the horizon field: they satisfy the determinant relation.
Solving that relation for one diagonal entry needs the corresponding cofactor to be nonzero, and it
is, because a specialisation of the jet coordinates turns the jet frame into the identity matrix and
the cofactor into `1`.

Removing that one coordinate from the block leaves `rN-1` jet coordinates which, together with the
horizon field, still generate the whole jet field.  This is the codimension asserted by `(11)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

/-! ## Determinants over an intermediate field -/

/-- A determinant of a matrix with entries in an intermediate field lies in that field. -/
theorem det_mem_intermediateField {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L E : Type*} [Field L] [Field E] [Algebra L E] {S : IntermediateField L E}
    {M : Matrix ι ι E} (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem S _) (prod_mem fun i _ => hM _ _)

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The jet frame before passing to the fraction field -/

/-- The jet frame of a span as a matrix of jet polynomials. -/
def jetFramePoly (t : Finset n) (K : Type*) [Field K] :
    Matrix ↥t ↥t (MvPolynomial (n × ℕ) K) :=
  Matrix.of fun m c => MvPolynomial.X (((m : n), jetOrder t c) : n × ℕ)

omit [Fintype n] [DecidableEq n] in
theorem jetFramePoly_apply (t : Finset n) (m c : ↥t) :
    jetFramePoly t K m c = MvPolynomial.X (((m : n), jetOrder t c) : n × ℕ) := rfl

/-- The specialisation of the jet coordinates which turns the jet frame of a span into the identity
matrix. -/
def frameSpecialization (t : Finset n) (K : Type*) [Field K] :
    MvPolynomial (n × ℕ) K →ₐ[K] K :=
  MvPolynomial.aeval fun p : n × ℕ =>
    if h : p.1 ∈ t then (if jetOrder t ⟨p.1, h⟩ = p.2 then (1 : K) else 0) else 0

omit [Fintype n] in
theorem frameSpecialization_jetFramePoly (t : Finset n) (m c : ↥t) :
    frameSpecialization t K (jetFramePoly t K m c) = (1 : Matrix ↥t ↥t K) m c := by
  rw [jetFramePoly_apply, frameSpecialization, MvPolynomial.aeval_X]
  show (if h : (m : n) ∈ t then
      (if jetOrder t ⟨(m : n), h⟩ = jetOrder t c then (1 : K) else 0) else 0) = _
  rw [dif_pos m.2, show (⟨(m : n), m.2⟩ : ↥t) = m from Subtype.ext rfl]
  rcases eq_or_ne m c with rfl | hmc
  · rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg fun h => hmc (jetOrder_injective t h), Matrix.one_apply_ne hmc]

/-! ## The diagonal cofactor of the jet frame -/

omit [Fintype n] in
/-- The diagonal cofactor of the jet frame is a nonzero jet polynomial: under the specialisation
that makes the frame the identity it becomes the determinant of the identity. -/
theorem det_updateRow_jetFramePoly_ne_zero (t : Finset n) (m₀ : ↥t) :
    ((jetFramePoly t K).updateRow m₀ (Pi.single m₀ 1)).det ≠ 0 := by
  intro hzero
  have hmap : ((jetFramePoly t K).updateRow m₀ (Pi.single m₀ 1)).map
      (frameSpecialization t K : MvPolynomial (n × ℕ) K →+* K) =
      (1 : Matrix ↥t ↥t K).updateRow m₀ (Pi.single m₀ 1) := by
    ext a b
    rcases eq_or_ne a m₀ with rfl | ha
    · rw [Matrix.map_apply, Matrix.updateRow_self, Matrix.updateRow_self, Pi.single_apply,
        Pi.single_apply]
      split
      · exact map_one _
      · exact map_zero _
    · rw [Matrix.map_apply, Matrix.updateRow_ne ha, Matrix.updateRow_ne ha]
      exact frameSpecialization_jetFramePoly t a b
  have hone : (1 : Matrix ↥t ↥t K).updateRow m₀ (Pi.single m₀ 1) = 1 := by
    have hrow : (1 : Matrix ↥t ↥t K) m₀ = Pi.single m₀ 1 := by
      funext j
      rw [Matrix.one_apply, Pi.single_apply]
      exact if_congr eq_comm rfl rfl
    rw [← hrow, Matrix.updateRow_eq_self]
  have hdet : (frameSpecialization t K : MvPolynomial (n × ℕ) K →+* K)
      (((jetFramePoly t K).updateRow m₀ (Pi.single m₀ 1)).det) = 1 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap, hone, Matrix.det_one]
  rw [hzero, map_zero] at hdet
  exact zero_ne_one hdet

omit [Fintype n] in
/-- The diagonal cofactor of the jet frame of a span is nonzero. -/
theorem adjugate_jetFrame_diag_ne_zero (t : Finset n) (m₀ : ↥t) :
    (jetFrame (K := K) t).adjugate m₀ m₀ ≠ 0 := by
  rw [Matrix.adjugate_apply]
  have hmap : (jetFrame (K := K) t).updateRow m₀ (Pi.single m₀ 1) =
      ((jetFramePoly t K).updateRow m₀ (Pi.single m₀ 1)).map
        (algebraMap (MvPolynomial (n × ℕ) K) (HomogeneousJetField n K)) := by
    ext a b
    rcases eq_or_ne a m₀ with rfl | ha
    · rw [Matrix.updateRow_self, Matrix.map_apply, Matrix.updateRow_self, Pi.single_apply,
        Pi.single_apply]
      split
      · exact (map_one _).symm
      · exact (map_zero _).symm
    · rw [Matrix.updateRow_ne ha, Matrix.map_apply, Matrix.updateRow_ne ha]
      rfl
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  intro hzero
  exact det_updateRow_jetFramePoly_ne_zero t m₀
    ((map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial (n × ℕ) K)
      (HomogeneousJetField n K))).1 hzero)

/-! ## The reduced block -/

/-- The initial block of a span with one diagonal jet coordinate removed. -/
def reducedJetBlock (t : Finset n) (m₀ : ↥t) (K : Type*) [Field K] :
    Set (HomogeneousJetField n K) :=
  (fun p : n × ↥t => freeCoordinate K (n × ℕ) (p.1, jetOrder t p.2)) ''
    {p : n × ↥t | p ≠ ((m₀ : n), m₀)}

omit [Fintype n] [DecidableEq n] in
theorem mem_reducedJetBlock {t : Finset n} {m₀ : ↥t} {k : n} {c : ↥t}
    (h : ((k, c) : n × ↥t) ≠ ((m₀ : n), m₀)) :
    freeCoordinate K (n × ℕ) (k, jetOrder t c) ∈ reducedJetBlock t m₀ K :=
  ⟨(k, c), h, rfl⟩

/-- The horizon field of a span together with the reduced block. -/
def reducedFrameGenerators (t : Finset n) (m₀ : ↥t) (K : Type*) [Field K] :
    Set (HomogeneousJetField n K) :=
  (horizonField (K := K) (↑t : Set n) : Set (HomogeneousJetField n K)) ∪ reducedJetBlock t m₀ K

/-- **The determinant relation solved.**  The one jet coordinate omitted from the reduced block is
recovered from the horizon field and the rest of the block, by solving the jet determinant relation
of the span for it. -/
theorem freeCoordinate_diag_mem_reducedAdjoin (t : Finset n) (m₀ : ↥t) :
    freeCoordinate K (n × ℕ) ((m₀ : n), jetOrder t m₀) ∈
      IntermediateField.adjoin K (reducedFrameGenerators t m₀ K) := by
  classical
  set S := IntermediateField.adjoin K (reducedFrameGenerators t m₀ K) with hS
  have hentry : ∀ a b : ↥t, ((a : n), b) ≠ ((m₀ : n), m₀) → jetFrame (K := K) t a b ∈ S := by
    intro a b h
    exact IntermediateField.subset_adjoin K _ (Or.inr (mem_reducedJetBlock h))
  have hcof : ∀ q : ↥t, (jetFrame (K := K) t).adjugate q m₀ ∈ S := by
    intro q
    rw [Matrix.adjugate_apply]
    refine det_mem_intermediateField ?_
    intro a b
    rcases eq_or_ne a m₀ with rfl | ha
    · rw [Matrix.updateRow_self, Pi.single_apply]
      split
      · exact one_mem S
      · exact zero_mem S
    · rw [Matrix.updateRow_ne ha]
      exact hentry a b fun hcon => ha (Subtype.ext (congrArg Prod.fst hcon))
  have hdet : jetDet (K := K) t ∈ S :=
    IntermediateField.subset_adjoin K _ (Or.inl (jetDet_mem_horizonField t))
  have hrel : ∑ q : ↥t, jetFrame (K := K) t m₀ q * (jetFrame (K := K) t).adjugate q m₀ =
      jetDet (K := K) t := by
    have h : ((jetFrame (K := K) t) * (jetFrame (K := K) t).adjugate) m₀ m₀ =
        ((jetFrame (K := K) t).det •
          (1 : Matrix ↥t ↥t (HomogeneousJetField n K))) m₀ m₀ := by
      rw [Matrix.mul_adjugate]
    rw [Matrix.mul_apply] at h
    rw [h, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rfl
  have hsplit : jetFrame (K := K) t m₀ m₀ * (jetFrame (K := K) t).adjugate m₀ m₀ =
      jetDet (K := K) t -
        ∑ q ∈ Finset.univ.erase m₀, jetFrame (K := K) t m₀ q *
          (jetFrame (K := K) t).adjugate q m₀ := by
    rw [← hrel, ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)]
    ring
  have hprod : jetFrame (K := K) t m₀ m₀ * (jetFrame (K := K) t).adjugate m₀ m₀ ∈ S := by
    rw [hsplit]
    refine sub_mem hdet (sum_mem fun q hq => mul_mem ?_ (hcof q))
    exact hentry m₀ q fun hcon => (Finset.ne_of_mem_erase hq) (congrArg Prod.snd hcon)
  have hbase : freeCoordinate K (n × ℕ) ((m₀ : n), jetOrder t m₀) =
      jetFrame (K := K) t m₀ m₀ := rfl
  have hval : freeCoordinate K (n × ℕ) ((m₀ : n), jetOrder t m₀) =
      (jetFrame (K := K) t m₀ m₀ * (jetFrame (K := K) t).adjugate m₀ m₀) /
        (jetFrame (K := K) t).adjugate m₀ m₀ := by
    rw [mul_div_assoc, div_self (adjugate_jetFrame_diag_ne_zero (K := K) t m₀), mul_one, hbase]
  rw [hval]
  exact div_mem hprod (hcof m₀)

/-- **The codimension of the horizon field of a span.**  The horizon field of a covector span of
rank `r` together with `rN-1` jet coordinates generates the whole jet field. -/
theorem reducedFrameGenerators_adjoin_eq_top [CharZero K] (t : Finset n) (m₀ : ↥t) :
    IntermediateField.adjoin K (reducedFrameGenerators t m₀ K) = ⊤ := by
  classical
  refine le_antisymm le_top ?_
  rw [← frameAdaptedGenerators_adjoin_eq_top (K := K) t, IntermediateField.adjoin_le_iff]
  rintro f (hf | ⟨⟨k, c⟩, rfl⟩)
  · exact IntermediateField.subset_adjoin K _ (Or.inl hf)
  · rcases eq_or_ne ((k, c) : n × ↥t) ((m₀ : n), m₀) with heq | hne
    · have hk : k = (m₀ : n) := congrArg Prod.fst heq
      have hc : c = m₀ := congrArg Prod.snd heq
      have hpt : (fun p : n × ↥t => freeCoordinate K (n × ℕ) (p.1, jetOrder t p.2)) (k, c) =
          freeCoordinate K (n × ℕ) ((m₀ : n), jetOrder t m₀) := by
        rw [hk, hc]
      rw [hpt]
      exact freeCoordinate_diag_mem_reducedAdjoin t m₀
    · exact IntermediateField.subset_adjoin K _ (Or.inr (mem_reducedJetBlock hne))

/-- The reduced block of a span of rank `r` in `N` directions has `rN-1` elements. -/
theorem card_reducedJetBlockIndex (t : Finset n) (m₀ : ↥t) :
    Nat.card {p : n × ↥t // p ≠ ((m₀ : n), m₀)} = Nat.card n * t.card - 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, card_initialJetBlock t]

end

end GaloisForLFunctions.HTGeometry
