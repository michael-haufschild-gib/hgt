import GaloisForLFunctions.HTGeometry.DirectionalProjectiveVarietyRealization

/-!
# Complete hypertranscendence realization of nonlinear projective horizons

The finite prefix-tree realization is extended by an infinite free tail behind every terminal
sector.  If all prescribed homogeneous law equations vanish, the collapse jet is zero.  Otherwise
every later jet occupies a fresh tail block, and the complete jet tower is algebraically
independent.  Thus arbitrary word-homogeneous projective zero loci occur as exact ordinary
differential-algebraicity horizons of a single observable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι] [Fintype η]

/-- Prefix states and equation-labelled infinite tail states. -/
abbrev ProjectiveCompleteGenerator (ι η : Type*) :=
  ProjectiveWordState ι ⊕ (η × ProjectiveWordState ι)

abbrev ProjectiveCompletePolynomial (K ι η : Type*) [Field K] :=
  MvPolynomial (ProjectiveCompleteGenerator ι η) K

abbrev ProjectiveCompleteField (K ι η : Type*) [Field K] :=
  FractionRing (ProjectiveCompletePolynomial K ι η)

def projectiveCompleteEmbedding :
    ProjectiveCompletePolynomial K ι η →ₐ[K] ProjectiveCompleteField K ι η :=
  IsScalarTower.toAlgHom K (ProjectiveCompletePolynomial K ι η)
    (ProjectiveCompleteField K ι η)

omit [Fintype ι] [Fintype η] in
theorem projectiveCompleteEmbedding_injective :
    Function.Injective (projectiveCompleteEmbedding (K := K) (ι := ι) (η := η)) :=
  IsFractionRing.injective (ProjectiveCompletePolynomial K ι η)
    (ProjectiveCompleteField K ι η)

omit [Fintype ι] [Fintype η] in
@[simp]
theorem projectiveCompleteEmbedding_apply (p : ProjectiveCompletePolynomial K ι η) :
    projectiveCompleteEmbedding (K := K) (ι := ι) (η := η) p =
      algebraMap (ProjectiveCompletePolynomial K ι η) (ProjectiveCompleteField K ι η) p := rfl

def projectiveCompleteAncestor (n : ℕ) (w : Fin n → ι) : ProjectiveCompleteField K ι η :=
  projectiveCompleteEmbedding (K := K) (ι := ι) (η := η)
    (MvPolynomial.X (Sum.inl ⟨n, w⟩))

def projectiveCompleteTail (j : η) (n : ℕ) (w : Fin n → ι) :
    ProjectiveCompleteField K ι η :=
  projectiveCompleteEmbedding (K := K) (ι := ι) (η := η)
    (MvPolynomial.X (Sum.inr (j, ⟨n, w⟩)))

def projectiveCompleteRoot : ProjectiveCompleteField K ι η :=
  projectiveCompleteAncestor (K := K) (η := η) 0 Fin.elim0

/-- The polynomial derivation propagates prefixes to depth `d`, collapses to the equation-labelled
tail roots, and then shifts each tail forever. -/
def projectiveCompletePolynomialDerivation
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) :
    Derivation K (ProjectiveCompletePolynomial K ι η) (ProjectiveCompleteField K ι η) :=
  MvPolynomial.mkDerivation K fun g ↦
    match g with
    | Sum.inl ⟨n, w⟩ =>
        if n + 1 < d then
          algebraMap (ProjectiveCompletePolynomial K ι η) (ProjectiveCompleteField K ι η)
            (MvPolynomial.X (Sum.inl ⟨n + 1, Fin.cons i w⟩))
        else if n + 1 = d then
          algebraMap (ProjectiveCompletePolynomial K ι η) (ProjectiveCompleteField K ι η)
            (∑ j, MvPolynomial.C (a j ⟨n + 1, Fin.cons i w⟩) *
              MvPolynomial.X (Sum.inr (j, ⟨0, Fin.elim0⟩)))
        else 0
    | Sum.inr (j, ⟨n, w⟩) =>
        algebraMap (ProjectiveCompletePolynomial K ι η) (ProjectiveCompleteField K ι η)
          (MvPolynomial.X (Sum.inr (j, ⟨n + 1, Fin.cons i w⟩)))

def projectiveCompleteDerivation
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (i : ι) :
    Derivation K (ProjectiveCompleteField K ι η) (ProjectiveCompleteField K ι η) :=
  fractionRingDerivation (projectiveCompletePolynomialDerivation a d i)

omit [Fintype ι] in
theorem projectiveCompleteDerivation_ancestor_of_lt
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (i : ι)
    (w : Fin n → ι) (h : n + 1 < d) :
    projectiveCompleteDerivation a d i (projectiveCompleteAncestor (K := K) (η := η) n w) =
      projectiveCompleteAncestor (K := K) (η := η) (n + 1) (Fin.cons i w) := by
  rw [projectiveCompleteDerivation, projectiveCompleteAncestor,
    projectiveCompleteEmbedding_apply, fractionRingDerivation_algebraMap,
    projectiveCompletePolynomialDerivation, MvPolynomial.mkDerivation_X]
  simp [h, projectiveCompleteAncestor]

omit [Fintype ι] in
theorem projectiveCompleteDerivation_ancestor_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (i : ι)
    (w : Fin n → ι) (h : n + 1 = d) :
    projectiveCompleteDerivation a d i (projectiveCompleteAncestor (K := K) (η := η) n w) =
      ∑ j, a j ⟨n + 1, Fin.cons i w⟩ •
        projectiveCompleteTail (K := K) j 0 Fin.elim0 := by
  rw [projectiveCompleteDerivation, projectiveCompleteAncestor,
    projectiveCompleteEmbedding_apply, fractionRingDerivation_algebraMap,
    projectiveCompletePolynomialDerivation, MvPolynomial.mkDerivation_X]
  simp [h, projectiveCompleteTail, Algebra.smul_def,
    IsScalarTower.algebraMap_apply K (ProjectiveCompletePolynomial K ι η)
      (ProjectiveCompleteField K ι η)]

omit [Fintype ι] in
theorem projectiveCompleteDerivation_tail
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (i : ι) (j : η)
    (w : Fin n → ι) :
    projectiveCompleteDerivation a d i (projectiveCompleteTail (K := K) j n w) =
      projectiveCompleteTail (K := K) j (n + 1) (Fin.cons i w) := by
  rw [projectiveCompleteDerivation, projectiveCompleteTail,
    projectiveCompleteEmbedding_apply, fractionRingDerivation_algebraMap,
    projectiveCompletePolynomialDerivation, MvPolynomial.mkDerivation_X]
  simp [projectiveCompleteTail]

omit [Fintype ι] in
theorem directionalWordDerivative_projectiveCompleteRoot_of_lt
    (a : η → ProjectiveWordState ι → K) (d : ℕ) :
    ∀ (n : ℕ) (_h : n < d) (w : Fin n → ι),
      directionalWordDerivative (projectiveCompleteDerivation a d)
          (projectiveCompleteRoot (K := K) (ι := ι) (η := η)) w =
        projectiveCompleteAncestor (K := K) (η := η) n w := by
  intro n
  induction n with
  | zero =>
      intro h w
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      simp [hw, directionalWordDerivative, projectiveCompleteRoot]
  | succ n ih =>
      intro h w
      rw [← Fin.cons_self_tail w, directionalWordDerivative_cons,
        ih (by omega) (Fin.tail w)]
      exact projectiveCompleteDerivation_ancestor_of_lt a d n (w 0) (Fin.tail w) h

omit [Fintype ι] in
theorem directionalWordDerivative_projectiveCompleteRoot_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n + 1 = d)
    (w : Fin (n + 1) → ι) :
    directionalWordDerivative (projectiveCompleteDerivation a d)
        (projectiveCompleteRoot (K := K) (ι := ι) (η := η)) w =
      ∑ j, a j ⟨n + 1, w⟩ • projectiveCompleteTail (K := K) j 0 Fin.elim0 := by
  rw [← Fin.cons_self_tail w, directionalWordDerivative_cons,
    directionalWordDerivative_projectiveCompleteRoot_of_lt a d n (by omega) (Fin.tail w),
    projectiveCompleteDerivation_ancestor_of_eq a d n (w 0) (Fin.tail w) h]

omit [Fintype ι] in
theorem directionalWordDerivative_projectiveCompleteTail
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (j : η) :
    ∀ (n : ℕ) (w : Fin n → ι),
      directionalWordDerivative (projectiveCompleteDerivation a d)
          (projectiveCompleteTail (K := K) j 0 Fin.elim0) w =
        projectiveCompleteTail (K := K) j n w := by
  intro n
  induction n with
  | zero =>
      intro w
      have hw : w = Fin.elim0 := Subsingleton.elim _ _
      simp [hw, directionalWordDerivative]
  | succ n ih =>
      intro w
      rw [← Fin.cons_self_tail w, directionalWordDerivative_cons, ih (Fin.tail w),
        projectiveCompleteDerivation_tail a d n (w 0) j (Fin.tail w)]

omit [Fintype ι] [Fintype η] in
theorem projectiveCompleteGenerator_algebraicIndependent :
    AlgebraicIndependent K
      (fun g : ProjectiveCompleteGenerator ι η ↦
        projectiveCompleteEmbedding (K := K) (ι := ι) (η := η) (MvPolynomial.X g)) := by
  simpa only [Function.comp_apply] using!
    (MvPolynomial.algebraicIndependent_X (ProjectiveCompleteGenerator ι η) K).map'
      (projectiveCompleteEmbedding_injective (K := K) (ι := ι) (η := η))

theorem directionalJet_projectiveCompleteRoot_of_lt
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n < d) (c : ι → K) :
    directionalJet (projectiveCompleteDerivation a d) c n
        (projectiveCompleteRoot (K := K) (ι := ι) (η := η)) =
      ∑ w : Fin n → ι, (∏ r, c (w r)) •
        projectiveCompleteAncestor (K := K) (η := η) n w := by
  rw [directionalJet_eq_sum_words]
  simp_rw [directionalWordDerivative_projectiveCompleteRoot_of_lt a d n h]

theorem directionalJet_projectiveCompleteRoot_of_eq
    (a : η → ProjectiveWordState ι → K) (d n : ℕ) (h : n + 1 = d) (c : ι → K) :
    directionalJet (projectiveCompleteDerivation a d) c (n + 1)
        (projectiveCompleteRoot (K := K) (ι := ι) (η := η)) =
      ∑ j, projectiveWordPolynomialValue a j c (n + 1) •
        projectiveCompleteTail (K := K) j 0 Fin.elim0 := by
  rw [directionalJet_eq_sum_words]
  simp_rw [directionalWordDerivative_projectiveCompleteRoot_of_eq a d n h,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  simp [projectiveWordPolynomialValue, smul_smul, Finset.sum_smul]

theorem directionalJet_projectiveCompleteTail
    (a : η → ProjectiveWordState ι → K) (d : ℕ) (c : ι → K) (j : η) (n : ℕ) :
    directionalJet (projectiveCompleteDerivation a d) c n
        (projectiveCompleteTail (K := K) j 0 Fin.elim0) =
      ∑ w : Fin n → ι, (∏ r, c (w r)) •
        projectiveCompleteTail (K := K) j n w := by
  rw [directionalJet_eq_sum_words]
  apply Finset.sum_congr rfl
  intro w hw
  rw [directionalWordDerivative_projectiveCompleteTail a d j n w]

/-- Every post-collapse root jet is the terminal polynomial vector propagated through the free
tail for the remaining number of derivatives. -/
theorem directionalJet_projectiveCompleteRoot_add
    (a : η → ProjectiveWordState ι → K) (n r : ℕ) (c : ι → K) :
    directionalJet (projectiveCompleteDerivation a (n + 1)) c (n + 1 + r)
        (projectiveCompleteRoot (K := K) (ι := ι) (η := η)) =
      ∑ j, projectiveWordPolynomialValue a j c (n + 1) •
        directionalJet (projectiveCompleteDerivation a (n + 1)) c r
          (projectiveCompleteTail (K := K) j 0 Fin.elim0) := by
  induction r with
  | zero =>
      simpa using directionalJet_projectiveCompleteRoot_of_eq a (n + 1) n rfl c
  | succ r ih =>
      rw [show n + 1 + (r + 1) = (n + 1 + r) + 1 by omega,
        directionalJet_succ, ih, map_sum]
      simp_rw [Derivation.map_smul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [directionalJet_succ]

/-- Reindex the complete root jet tower into the finite prefix and the infinite post-collapse
tail. -/
def projectiveCompleteJetPacket
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K) :
    Fin (n + 1) ⊕ ℕ → ProjectiveCompleteField K ι η
  | Sum.inl r => directionalJet (projectiveCompleteDerivation a (n + 1)) c r
      (projectiveCompleteRoot (K := K) (ι := ι) (η := η))
  | Sum.inr r => directionalJet (projectiveCompleteDerivation a (n + 1)) c (n + 1 + r)
      (projectiveCompleteRoot (K := K) (ι := ι) (η := η))

/-- If the law direction is nonzero and one terminal homogeneous polynomial survives, the
reindexed complete jet packet is algebraically independent. -/
theorem projectiveCompleteJetPacket_algebraicIndependent
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0)
    (hP : ∃ j, projectiveWordPolynomialValue a j c (n + 1) ≠ 0) :
    AlgebraicIndependent K (projectiveCompleteJetPacket a n c) := by
  classical
  let τ := Fin (n + 1) ⊕ ℕ
  let σ : τ → Type v :=
    Sum.elim (fun r : Fin (n + 1) ↦ Fin (r : ℕ) → ι)
      (fun r : ℕ ↦ η × (Fin r → ι))
  letI : ∀ t, Fintype (σ t) := fun t ↦ by
    cases t <;> dsimp [σ] <;> infer_instance
  letI : ∀ t, DecidableEq (σ t) := fun t ↦ by
    cases t <;> dsimp [σ] <;> infer_instance
  let prefixEmbedding :
      (Σ r : Fin (n + 1), Fin (r : ℕ) → ι) ↪ ProjectiveWordState ι :=
    ⟨Sigma.map (fun r : Fin (n + 1) ↦ (r : ℕ)) (fun _ w ↦ w),
      Fin.val_injective.sigma_map (fun _ ↦ fun _ _ h ↦ h)⟩
  let tailEquiv : (Σ r : ℕ, η × (Fin r → ι)) ≃ η × ProjectiveWordState ι :=
    (Equiv.sigmaCongrRight (fun r : ℕ ↦ Equiv.prodComm η (Fin r → ι))).trans
      ((Equiv.sigmaProdDistrib (fun r : ℕ ↦ Fin r → ι) η).symm.trans
        (Equiv.prodComm (ProjectiveWordState ι) η))
  let generatorEmbedding : (Σ t, σ t) ↪ ProjectiveCompleteGenerator ι η :=
    (Equiv.sumSigmaDistrib σ).toEmbedding.trans
      (Function.Embedding.sumMap prefixEmbedding tailEquiv.toEmbedding)
  let x : (Σ t, σ t) → ProjectiveCompleteField K ι η := fun p ↦
    match p with
    | ⟨Sum.inl r, w⟩ => projectiveCompleteAncestor (K := K) (η := η) r w
    | ⟨Sum.inr r, jw⟩ => projectiveCompleteTail (K := K) jw.1 r jw.2
  have hx : AlgebraicIndependent K x := by
    have hraw :=
      (projectiveCompleteGenerator_algebraicIndependent (K := K) (ι := ι) (η := η)).comp
        generatorEmbedding generatorEmbedding.injective
    have hxraw : x = fun p ↦
        projectiveCompleteEmbedding (K := K) (ι := ι) (η := η)
          (MvPolynomial.X (generatorEmbedding p)) := by
      funext p
      rcases p with ⟨t, s⟩
      cases t with
      | inl r => rfl
      | inr r =>
          rcases s with ⟨j, w⟩
          rfl
    rw [hxraw]
    simpa [Function.comp_def] using hraw
  let u : ∀ t, σ t → K := fun t ↦
    match t with
    | Sum.inl r => fun w ↦ ∏ q, c (w q)
    | Sum.inr r => fun jw ↦
        projectiveWordPolynomialValue a jw.1 c (n + 1) * ∏ q, c (jw.2 q)
  have hu : ∀ t, ∃ s, u t s ≠ 0 := by
    intro t
    obtain ⟨i, hi⟩ := hc
    cases t with
    | inl r =>
        refine ⟨fun _ ↦ i, ?_⟩
        simpa [u] using pow_ne_zero (r : ℕ) hi
    | inr r =>
        obtain ⟨j, hj⟩ := hP
        refine ⟨(j, fun _ ↦ i), ?_⟩
        simpa [u] using mul_ne_zero hj (pow_ne_zero r hi)
  have hforms := algebraicIndependent_disjointBlockLinearForms_arbitrary u hu x hx
  have hpacket :
      (fun t ↦ ∑ s, algebraMap K (ProjectiveCompleteField K ι η) (u t s) * x ⟨t, s⟩) =
        projectiveCompleteJetPacket a n c := by
    funext t
    cases t with
    | inl r =>
        simpa [projectiveCompleteJetPacket, σ, u, x, generatorEmbedding, prefixEmbedding,
          tailEquiv, Algebra.smul_def] using!
          (directionalJet_projectiveCompleteRoot_of_lt a (n + 1) (r : ℕ) r.isLt c).symm
    | inr r =>
        rw [projectiveCompleteJetPacket,
          directionalJet_projectiveCompleteRoot_add a n r c]
        simp_rw [directionalJet_projectiveCompleteTail a (n + 1) c]
        simp only [σ, u, x, Algebra.smul_def, map_mul, map_prod]
        let f : η × (Fin r → ι) → ProjectiveCompleteField K ι η := fun jw ↦
          algebraMap K (ProjectiveCompleteField K ι η)
              (projectiveWordPolynomialValue a jw.1 c (n + 1)) *
            (∏ q, algebraMap K (ProjectiveCompleteField K ι η) (c (jw.2 q))) *
              projectiveCompleteTail (K := K) jw.1 r jw.2
        change (∑ jw, f jw) = _
        rw [Fintype.sum_prod_type f]
        dsimp [f]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        ring
  rw [← hpacket]
  exact hforms

/-- **Complete nonlinear hypertranscendence horizon.**  At every nonzero direction, the root
observable is hypertranscendental exactly when at least one arbitrary homogeneous terminal law
polynomial is nonzero. -/
theorem projectiveCompleteJet_algebraicIndependent_iff
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    AlgebraicIndependent K
        (fun r : ℕ ↦ directionalJet (projectiveCompleteDerivation a (n + 1)) c r
          (projectiveCompleteRoot (K := K) (ι := ι) (η := η))) ↔
      ∃ j, projectiveWordPolynomialValue a j c (n + 1) ≠ 0 := by
  let jet : ℕ → ProjectiveCompleteField K ι η := fun r ↦
    directionalJet (projectiveCompleteDerivation a (n + 1)) c r
      (projectiveCompleteRoot (K := K) (ι := ι) (η := η))
  have hpacket : projectiveCompleteJetPacket a n c =
      jet ∘ finSumNatEquiv (n + 1) := by
    funext t
    cases t <;> rfl
  have hreindex : AlgebraicIndependent K (projectiveCompleteJetPacket a n c) ↔
      AlgebraicIndependent K jet := by
    rw [hpacket]
    exact algebraicIndependent_equiv (finSumNatEquiv (n + 1))
  change AlgebraicIndependent K jet ↔ _
  constructor
  · intro hindependent
    by_contra hnone
    push Not at hnone
    have htop : jet (n + 1) = 0 := by
      dsimp [jet]
      rw [directionalJet_projectiveCompleteRoot_of_eq a (n + 1) n rfl c]
      simp [hnone]
    exact hindependent.ne_zero (n + 1) htop
  · intro hsurvives
    exact hreindex.1
      (projectiveCompleteJetPacket_algebraicIndependent a n c hc hsurvives)

/-- Polynomial zero-locus form of the complete theorem. -/
theorem projectiveCompleteJet_dependent_iff_lawPolynomials_zero
    (a : η → ProjectiveWordState ι → K) (n : ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    (¬ AlgebraicIndependent K
        (fun r : ℕ ↦ directionalJet (projectiveCompleteDerivation a (n + 1)) c r
          (projectiveCompleteRoot (K := K) (ι := ι) (η := η)))) ↔
      ∀ j, MvPolynomial.eval c (projectiveWordLawPolynomial a j (n + 1)) = 0 := by
  rw [projectiveCompleteJet_algebraicIndependent_iff a n c hc]
  push Not
  simp

end

end GaloisForLFunctions.HTGeometry
