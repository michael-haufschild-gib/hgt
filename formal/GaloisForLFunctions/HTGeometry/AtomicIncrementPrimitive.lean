import GaloisForLFunctions.HTGeometry.MatroidNatRank
import GaloisForLFunctions.HTGeometry.AlgebraicMatroidGaussianModel
import GaloisForLFunctions.HTGeometry.DifferentialSemilinearAutomorphism

/-!
# Algebraic rank behind atomic-increment primitive transfer

Disjoint dependent copies of one finite packet force one algebraic-rank deficit per copy.  This is
the finite matroid count used to pass from algebraically independent consecutive increments to an
algebraically independent primitive orbit.
-/

namespace GaloisForLFunctions.MatroidGluing

open Finset

variable {Ω : Type*} [DecidableEq Ω]

namespace Rank

/-- If a finite packet contains `s.card` cardinally disjoint dependent blocks, its rank loses at
least one unit per block.  `hcard` is the exact cardinal-disjointness certificate. -/
theorem rank_add_card_le_of_dependent_blocks
    (R : Rank Ω) {ι : Type*} [DecidableEq ι]
    (V : Finset Ω) (s : Finset ι) (A : ι → Finset Ω)
    (hsub : s.biUnion A ⊆ V)
    (hcard : (s.biUnion A).card = ∑ i ∈ s, (A i).card)
    (hdep : ∀ i ∈ s, R.ρ (A i) < (A i).card) :
    R.ρ V + s.card ≤ V.card := by
  classical
  let U : Finset Ω := s.biUnion A
  let W : Finset Ω := V \ U
  have hzero : R.ρ (∅ : Finset Ω) = 0 := by
    exact Nat.eq_zero_of_le_zero (R.ρ_le_card ∅)
  have hVU : V = U ∪ W := by
    ext x
    simp only [U, W, mem_union, mem_biUnion, mem_sdiff]
    constructor
    · intro hx
      by_cases hxU : ∃ i ∈ s, x ∈ A i
      · exact Or.inl hxU
      · exact Or.inr ⟨hx, hxU⟩
    · rintro (hx | hx)
      · exact hsub (by simpa [U] using hx)
      · exact hx.1
  have hUW : U ∩ W = ∅ := by
    ext x
    simp [U, W]
  have hrankUnion : R.ρ V ≤ R.ρ U + R.ρ W := by
    have h := R.submodular U W
    rw [← hVU, hUW, hzero, add_zero] at h
    exact h
  have hrankBlocks : R.ρ U ≤ ∑ i ∈ s, R.ρ (A i) := by
    have h := R.relRank_biUnion_le (∅ : Finset Ω) s A
    simp only [empty_union, hzero, mul_zero, zero_add] at h
    simpa [U] using h
  have hsum : (∑ i ∈ s, R.ρ (A i)) + s.card ≤
      ∑ i ∈ s, (A i).card := by
    calc
      (∑ i ∈ s, R.ρ (A i)) + s.card =
          ∑ i ∈ s, (R.ρ (A i) + 1) := by
            rw [sum_add_distrib]
            simp
      _ ≤ ∑ i ∈ s, (A i).card :=
        sum_le_sum fun i hi => Nat.succ_le_iff.mpr (hdep i hi)
  have hcardVW : V.card = U.card + W.card := by
    rw [hVU, card_union_of_disjoint]
    exact disjoint_iff_inter_eq_empty.mpr hUW
  have hcardU : U.card = ∑ i ∈ s, (A i).card := by
    simpa [U] using hcard
  have hrankW : R.ρ W ≤ W.card := R.ρ_le_card W
  omega

/-- If consecutive increment packets always contribute full rank, then every primitive packet has
full rank.  `hseparate` is the sole geometric input: arbitrarily many equally spaced copies of a
finite packet can be chosen cardinally disjoint. -/
theorem indepSet_of_atomic_increment_lower_bound
    (R : Rank Ω) (sigma : Equiv.Perm Ω)
    (hsigma : sigma ∈ R.rankAutSubgroup)
    (hseparate : ∀ (S : Finset Ω) (B : ℕ), ∃ N : ℕ,
      ((Finset.range B).biUnion fun i =>
        S.image ⇑(sigma ^ (i * N : ℤ))).card = B * S.card)
    (hincrement : ∀ E : Finset Ω,
      E.card ≤ R.ρ (E ∪ E.image ⇑sigma)) :
    R.IndepSet Set.univ := by
  classical
  intro S _
  apply le_antisymm (R.ρ_le_card S)
  by_contra hnot
  have hdep : R.ρ S < S.card := by omega
  let B : ℕ := S.card + 1
  obtain ⟨N, hdisjoint⟩ := hseparate S B
  let T : ℕ := (B - 1) * N
  let A : ℕ → Finset Ω := fun i => S.image ⇑(sigma ^ (i * N : ℤ))
  let E : Finset Ω := (Finset.range T).biUnion fun n =>
    S.image ⇑(sigma ^ (n : ℤ))
  let V : Finset Ω := (Finset.range (T + 1)).biUnion fun n =>
    S.image ⇑(sigma ^ (n : ℤ))
  have hBpos : 0 < B := by simp [B]
  have hblocksSub : (Finset.range B).biUnion A ⊆ V := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_range, A, V] at hx ⊢
    obtain ⟨i, hiB, hxi⟩ := hx
    refine ⟨i * N, ?_, hxi⟩
    dsimp only [T]
    have hi : i ≤ B - 1 := Nat.le_sub_one_of_lt hiB
    exact Nat.lt_succ_of_le (Nat.mul_le_mul_right N hi)
  have hblocksCard :
      ((Finset.range B).biUnion A).card = ∑ i ∈ Finset.range B, (A i).card := by
    have hleft : ((Finset.range B).biUnion A).card = B * S.card := by
      simpa [A] using hdisjoint
    have hAcard : ∀ i, (A i).card = S.card := by
      intro i
      exact Finset.card_image_of_injective _ (sigma ^ (i * N : ℤ)).injective
    rw [hleft]
    simp only [hAcard, Finset.sum_const_nat, Finset.card_range]
  have hblocksDep : ∀ i ∈ Finset.range B, R.ρ (A i) < (A i).card := by
    intro i _
    change R.ρ (S.image ⇑(sigma ^ (i * N : ℤ))) <
      (S.image ⇑(sigma ^ (i * N : ℤ))).card
    rw [R.ρ_image_zpow hsigma (i * N : ℤ),
      Finset.card_image_of_injective _ (sigma ^ (i * N : ℤ)).injective]
    exact hdep
  have hrankUpper : R.ρ V + B ≤ V.card := by
    simpa using R.rank_add_card_le_of_dependent_blocks V (Finset.range B) A
      hblocksSub hblocksCard hblocksDep
  have hEV : E ⊆ V := by
    intro x hx
    simp only [E, V, Finset.mem_biUnion, Finset.mem_range] at hx ⊢
    obtain ⟨n, hn, hxn⟩ := hx
    exact ⟨n, Nat.lt_succ_of_lt hn, hxn⟩
  have hshiftEV : E.image ⇑sigma ⊆ V := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hyE, rfl⟩ := hx
    simp only [E, Finset.mem_biUnion, Finset.mem_range] at hyE
    obtain ⟨n, hn, hyn⟩ := hyE
    rw [Finset.mem_image] at hyn
    obtain ⟨z, hzS, rfl⟩ := hyn
    simp only [V, Finset.mem_biUnion, Finset.mem_range]
    refine ⟨n + 1, Nat.succ_lt_succ hn, ?_⟩
    rw [Finset.mem_image]
    refine ⟨z, hzS, ?_⟩
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, zpow_add_one]
    change ((sigma ^ (n : ℤ)) * sigma) z =
      (sigma * (sigma ^ (n : ℤ))) z
    exact congrArg (fun e : Equiv.Perm Ω => e z)
      (Commute.self_zpow sigma (n : ℤ)).eq.symm
  have hrankLower : E.card ≤ R.ρ V := by
    exact (hincrement E).trans (R.mono (Finset.union_subset hEV hshiftEV))
  have hVboundary : V ⊆ E ∪ S.image ⇑(sigma ^ (T : ℤ)) := by
    intro x hx
    simp only [V, Finset.mem_biUnion, Finset.mem_range] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    by_cases hnT : n < T
    · exact Finset.mem_union_left _ (by
        simp only [E, Finset.mem_biUnion, Finset.mem_range]
        exact ⟨n, hnT, hxn⟩)
    · have hnEq : n = T := by omega
      subst n
      exact Finset.mem_union_right _ hxn
  have hcardBoundary : V.card ≤ E.card + S.card := by
    calc
      V.card ≤ (E ∪ S.image ⇑(sigma ^ (T : ℤ))).card :=
        Finset.card_le_card hVboundary
      _ ≤ E.card + (S.image ⇑(sigma ^ (T : ℤ))).card := Finset.card_union_le _ _
      _ = E.card + S.card := by
        rw [Finset.card_image_of_injective _ (sigma ^ (T : ℤ)).injective]
  dsimp only [B] at hrankUpper
  omega

/-- Independent affine increments have cardinality at most the algebraic rank of their endpoint
primitive packet. -/
theorem algebraicFamilyRank_atomic_increment_lower_bound
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x y : Ω → L) (sigma : Equiv.Perm Ω) (c : Ω → K)
    (hy : AlgebraicIndependent K y)
    (hvalue : ∀ i, y i = x (sigma i) - x i - algebraMap K L (c i))
    (E : Finset Ω) :
    E.card ≤ (matroidRank
      (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)).ρ
      (E ∪ E.image ⇑sigma) := by
  classical
  let P : Finset Ω := E ∪ E.image ⇑sigma
  let M : Matroid L := AlgebraicIndependent.matroid K L
  have hyE : AlgebraicIndependent K (fun i : (↑E : Set Ω) => y (i : Ω)) :=
    hy.comp Subtype.val Subtype.val_injective
  have hyImage : AlgebraicIndependent K
      (fun z : y '' (↑E : Set Ω) => (z : L)) := hyE.image
  have hsignalIndep : M.Indep (y '' (↑E : Set Ω)) := by
    exact AlgebraicIndependent.matroid_indep_iff.mpr hyImage
  have hsignalCard : Set.encard (y '' (↑E : Set Ω)) = E.card := by
    rw [show y '' (↑E : Set Ω) = ↑(E.image y) by ext; simp]
    rw [Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injective _ hy.injective]
  have hsignalRank : (M.eRk (y '' (↑E : Set Ω))).toNat = E.card := by
    rw [hsignalIndep.eRk_eq_encard, hsignalCard]
    simp
  have hsignalClosure : y '' (↑E : Set Ω) ⊆ M.closure (x '' (↑P : Set Ω)) := by
    rintro z ⟨i, hiE, rfl⟩
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe,
      Subalgebra.mem_algebraicClosure]
    let A : Subalgebra K L := Algebra.adjoin K (x '' (↑P : Set Ω))
    have hxi : x i ∈ A := by
      apply Algebra.subset_adjoin
      exact ⟨i, by
        change i ∈ P
        exact Finset.mem_union_left _ (by exact_mod_cast hiE), rfl⟩
    have hxsigma : x (sigma i) ∈ A := by
      apply Algebra.subset_adjoin
      exact ⟨sigma i, by
        change sigma i ∈ P
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i, by exact_mod_cast hiE, rfl⟩), rfl⟩
    have hyA : y i ∈ A := by
      rw [hvalue]
      exact sub_mem (sub_mem hxsigma hxi) (A.algebraMap_mem (c i))
    let yi : A := ⟨y i, hyA⟩
    have hyalg : IsAlgebraic A yi := Algebra.IsAlgebraic.isAlgebraic yi
    have hymap := hyalg.algHom (IsScalarTower.toAlgHom A A L)
    simpa [A, yi] using hymap
  have hbaseSet : x '' (↑P : Set Ω) = ↑(P.image x) := by
    ext z
    simp
  have hrank : M.eRk (y '' (↑E : Set Ω)) ≤ M.eRk (x '' (↑P : Set Ω)) := by
    calc
      M.eRk (y '' (↑E : Set Ω)) ≤ M.eRk (M.closure (x '' (↑P : Set Ω))) :=
        M.eRk_mono hsignalClosure
      _ = M.eRk (x '' (↑P : Set Ω)) := M.eRk_closure_eq _
  have hrankNat : E.card ≤ (M.eRk (x '' (↑P : Set Ω))).toNat := by
    rw [← hsignalRank]
    exact ENat.toNat_le_toNat hrank
      (by rw [hbaseSet]; exact matroid_eRk_ne_top M (P.image x))
  simpa only [matroidRank_rho,
    GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid,
    Matroid.eRk_comap, P] using hrankNat

end Rank

/-- Translation by `+2` on complex shift labels, leaving jet order fixed. -/
noncomputable def complexJetEvenShift : Equiv.Perm (ℂ × ℕ) :=
  Equiv.prodCongr (Equiv.addRight (2 : ℂ)) (Equiv.refl ℕ)

@[simp]
theorem complexJetEvenShift_apply (h : ℂ) (k : ℕ) :
    complexJetEvenShift (h, k) = (h + 2, k) := rfl

/-- A nonnegative power of the even shift adds the corresponding even integer. -/
theorem complexJetEvenShift_zpow_nat (h : ℂ) (k n : ℕ) :
    (complexJetEvenShift ^ (n : ℤ)) (h, k) = (h + n * 2, k) := by
  rw [zpow_natCast]
  induction n with
  | zero => simp [complexJetEvenShift]
  | succ n ih =>
      rw [pow_succ']
      change complexJetEvenShift ((complexJetEvenShift ^ n) (h, k)) = _
      rw [ih]
      simp [complexJetEvenShift]
      ring

/-- Every finite complex-shift jet packet has arbitrarily many cardinally disjoint equally spaced
even translates. -/
theorem complexJetEvenShift_separates (S : Finset (ℂ × ℕ)) (B : ℕ) : ∃ N : ℕ,
    ((Finset.range B).biUnion fun i =>
      S.image ⇑(complexJetEvenShift ^ (i * N : ℤ))).card = B * S.card := by
  classical
  let M : ℕ := S.sup fun p => Nat.ceil |p.1.re|
  let N : ℕ := M + 1
  have hbound : ∀ p ∈ S, |p.1.re| ≤ (M : ℝ) := by
    intro p hp
    exact (Nat.le_ceil |p.1.re|).trans
      (mod_cast (Finset.le_sup (f := fun q : ℂ × ℕ => Nat.ceil |q.1.re|) hp))
  have hpair : (↑(Finset.range B) : Set ℕ).PairwiseDisjoint
      (fun i => S.image ⇑(complexJetEvenShift ^ (i * N : ℤ))) := by
    intro i _ j _ hij
    change Disjoint (S.image ⇑(complexJetEvenShift ^ (i * N : ℤ)))
      (S.image ⇑(complexJetEvenShift ^ (j * N : ℤ)))
    rw [Finset.disjoint_left]
    intro z hzi hzj
    rw [Finset.mem_image] at hzi hzj
    obtain ⟨p, hpS, hpz⟩ := hzi
    obtain ⟨q, hqS, hqz⟩ := hzj
    have heq : (complexJetEvenShift ^ (i * N : ℤ)) p =
        (complexJetEvenShift ^ (j * N : ℤ)) q := hpz.trans hqz.symm
    have hiCast : (i * N : ℤ) = ((i * N : ℕ) : ℤ) := by norm_num
    have hjCast : (j * N : ℤ) = ((j * N : ℕ) : ℤ) := by norm_num
    rw [hiCast, hjCast] at heq
    have hpform := show (complexJetEvenShift ^ ((i * N : ℕ) : ℤ)) p =
        (p.1 + (i * N) * 2, p.2) by
      simpa [Prod.eta, Nat.cast_mul] using
        complexJetEvenShift_zpow_nat p.1 p.2 (i * N)
    have hqform := show (complexJetEvenShift ^ ((j * N : ℕ) : ℤ)) q =
        (q.1 + (j * N) * 2, q.2) by
      simpa [Prod.eta, Nat.cast_mul] using
        complexJetEvenShift_zpow_nat q.1 q.2 (j * N)
    rw [hpform, hqform] at heq
    have hreal := congrArg (fun w : ℂ × ℕ => w.1.re) heq
    norm_num [Complex.add_re] at hreal
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hstepNat : i * N + N ≤ j * N := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt hijlt)
      have hstep : (i * N : ℝ) + N ≤ (j * N : ℝ) := by exact_mod_cast hstepNat
      have hp := hbound p hpS
      have hq := hbound q hqS
      have hN : (N : ℝ) = M + 1 := by simp [N]
      have hp' := abs_le.mp hp
      have hq' := abs_le.mp hq
      linarith
    · have hstepNat : j * N + N ≤ i * N := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right N (Nat.succ_le_of_lt hjilt)
      have hstep : (j * N : ℝ) + N ≤ (i * N : ℝ) := by exact_mod_cast hstepNat
      have hp := hbound p hpS
      have hq := hbound q hqS
      have hN : (N : ℝ) = M + 1 := by simp [N]
      have hp' := abs_le.mp hp
      have hq' := abs_le.mp hq
      linarith
  refine ⟨N, ?_⟩
  rw [Finset.card_biUnion hpair]
  calc
    (∑ x ∈ Finset.range B,
        (Finset.image ⇑(complexJetEvenShift ^ (↑x * ↑N)) S).card) =
        ∑ _x ∈ Finset.range B, S.card := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_image_of_injective _
        (complexJetEvenShift ^ (i * N : ℤ)).injective
    _ = B * S.card := by simp

/-- A semilinear ambient automorphism which realizes a permutation of a family preserves the
family's algebraic rank. -/
theorem algebraicFamilyRank_mem_rankAutSubgroup_of_semilinear
    {K L Ω : Type*} [Field K] [Field L] [Algebra K L]
    [Differential K] [Differential L] [DecidableEq Ω]
    (tau : GaloisForLFunctions.HTGeometry.DifferentialSemilinearEquiv K L)
    (x : Ω → L) (sigma : Equiv.Perm Ω)
    (hmap : ∀ i, tau.ambientEquiv (x i) = x (sigma i)) :
    sigma ∈
      (matroidRank
        (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)).rankAutSubgroup := by
  have hinvariant :
      GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K
          (fun i => tau.ambientEquiv (x i)) =
        GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x := by
    apply Matroid.ext_indep
    · simp
    · intro I _
      rw [GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid_indep_iff,
        GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid_indep_iff]
      constructor
      · intro hI
        have hback := tau.symm.algebraicIndependent_map hI
        simpa [GaloisForLFunctions.HTGeometry.DifferentialSemilinearEquiv.symm] using hback
      · exact tau.algebraicIndependent_map
  have hreindex :
      (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x).mapEquiv sigma.symm =
        GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K
          (fun i => x (sigma i)) := by
    apply Matroid.ext_indep
    · simp
    · intro I _
      rw [Matroid.mapEquiv_indep_iff,
        GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid_indep_iff,
        GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid_indep_iff]
      simp only [Equiv.symm_symm]
      let e : I ≃ {a // a ∈ sigma '' I} :=
        Equiv.Set.image sigma I sigma.injective
      constructor
      · intro hI
        have hcomp := hI.comp e e.injective
        simpa [e, Function.comp_def] using hcomp
      · intro hI
        have hcomp := hI.comp e.symm e.symm.injective
        convert hcomp using 1
        funext i
        congr 1
        exact (congrArg Subtype.val (e.apply_symm_apply i)).symm
  have hfamily : (fun i => x (sigma i)) = fun i => tau.ambientEquiv (x i) := by
    funext i
    exact (hmap i).symm
  rw [hfamily, hinvariant] at hreindex
  have hinv := matroidRank_mem_rankAutSubgroup_of_mapEquiv_eq _ _ hreindex
  have hback :=
    (matroidRank
      (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)).rankAutSubgroup.inv_mem hinv
  change sigma ∈
    (matroidRank
      (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)).rankAutSubgroup at hback
  exact hback

/-- **Atomic-increment primitive theorem for complex shift jets.**  If the complete affine
increment family is algebraically independent and the even shift normalizes primitive algebraic
rank, then the complete primitive family is algebraically independent. -/
theorem algebraicIndependent_primitive_of_evenShift_increments
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (x y : ℂ × ℕ → L) (c : ℂ × ℕ → K)
    (hy : AlgebraicIndependent K y)
    (hvalue : ∀ i, y i = x (complexJetEvenShift i) - x i - algebraMap K L (c i))
    (hshift : complexJetEvenShift ∈
      (matroidRank
        (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)).rankAutSubgroup) :
    AlgebraicIndependent K x := by
  classical
  let R := matroidRank
    (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid K x)
  have hincrement : ∀ E : Finset (ℂ × ℕ),
      E.card ≤ R.ρ (E ∪ E.image ⇑complexJetEvenShift) := by
    intro E
    exact Rank.algebraicFamilyRank_atomic_increment_lower_bound
      x y complexJetEvenShift c hy hvalue E
  have hIndepSet : R.IndepSet Set.univ :=
    Rank.indepSet_of_atomic_increment_lower_bound R complexJetEvenShift hshift
      complexJetEvenShift_separates hincrement
  apply algebraicIndependent_of_finite_type
  intro t ht
  letI : Fintype t := ht.fintype
  let s : Finset (ℂ × ℕ) := ht.toFinset
  have hrank := hIndepSet s (by simp)
  rw [matroidRank_rho_eq_card_iff] at hrank
  have hpacket :=
    (GaloisForLFunctions.HTGeometry.algebraicFamilyMatroid_indep_iff
      K x (↑s : Set (ℂ × ℕ))).mp hrank
  let e : {a // a ∈ s} ≃ t :=
    Equiv.subtypeEquivRight (fun a => Set.mem_toFinset)
  have htransport := hpacket.comp e.symm e.symm.injective
  simpa [s, e, Function.comp_def] using htransport

end GaloisForLFunctions.MatroidGluing
