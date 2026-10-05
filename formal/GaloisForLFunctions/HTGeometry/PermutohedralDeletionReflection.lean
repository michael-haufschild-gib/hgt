import GaloisForLFunctions.HTGeometry.PermutohedralAlternantFactorization
import GaloisForLFunctions.HTGeometry.PermutationAction

/-!
# Deletion–interpolation and complement reflection of the formation numerators

**Deletion.**  Splitting the schedules of `[r+1]` by their first letter `i` identifies the remaining
schedule with a schedule of the deleted alphabet `[r+1] ∖ {i}`, enumerated by `i.succAbove`, with
sign change `(-1)^i`.  The first suffix set is `[r+1]`, the others are images of suffix sets of the
deleted schedule, and the nonempty subsets of `[r+1]` split into `[r+1]`, the images of nonempty
subsets of the deleted alphabet, and the proper subsets containing `i`.  Hence
`N_{r+1} = Σ_i (-1)^i N_r(λ̂_i) E_{r+1,i}` with `E_{r+1,i} = Π_{i ∈ S ⊊ [r+1]} (z + λ_S)`,
`D_{r+1} = (z + A) D_r(λ̂_i) E_{r+1,i}` `(GFH.7)`, `Δ_{r+1} = (-1)^i V_i Δ_r(λ̂_i)` `(GFH.6)` with
`V_i = Π_{j ≠ i} (λ_i - λ_j)`, so `R_{r+1} = (z + A)⁻¹ Σ_i (-1)^i R_r(λ̂_i)` `(GFH.5)` and, for
distinct grades, `P_{r+1} = Σ_i P_r(λ̂_i) E_{r+1,i}/V_i` `(GFH.4)`.

**Reflection.**  The substitution `z ↦ -A - z` sends `z + λ_S` to `-(z + λ_{Sᶜ})`.  Complements of
the nonempty non-chain subsets of a schedule `π` are exactly the nonempty non-chain subsets of the
reversed schedule, and reversal has sign `(-1)^{r(r-1)/2}`; with `deg`-count `2^r - 1 - r` this
gives `N_r(-A-z) = (-1)^{r(r+1)/2 + 1} N_r(z)`, hence `P_r(-A - z) = (-1)^{r(r+1)/2+1} P_r(z)`
`(GFH.R1)`, `(z + A) D_r(-A-z) = -z D_r(z)` `(GFH.R5)`, and `2z + A` divides `P_r` when
`r(r+1)/2` is even `(GFH.R2)`.
-/

open MvPolynomial Finset Equiv

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace Permutohedral

/-! ### The first-letter decomposition of schedules -/

/-- The schedule with first letter `i` followed by `e` on the deleted alphabet. -/
def firstLetter {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  i.cycleRange.symm * Perm.decomposeFin.symm (0, e)

theorem firstLetter_zero {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) : firstLetter i e 0 = i := by
  simp [firstLetter, Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem firstLetter_succ {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) (j : Fin n) :
    firstLetter i e j.succ = i.succAbove (e j) := by
  simp [firstLetter, Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

theorem sign_firstLetter {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (firstLetter i e) = Perm.sign i.cycleRange * Perm.sign e := by
  rw [firstLetter, Perm.sign_mul, Perm.sign_symm, Perm.decomposeFin.symm_sign]
  simp only [↓reduceIte, one_mul]

theorem sign_cycleRange_cast {R : Type*} [CommRing R] {n : ℕ} (i : Fin n) :
    (((Perm.sign i.cycleRange : ℤˣ) : ℤ) : R) = (-1) ^ (i : ℕ) := by
  rw [Fin.sign_cycleRange, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  push_cast
  ring

theorem firstLetter_injective {n : ℕ} :
    Function.Injective fun p : Fin (n + 1) × Perm (Fin n) => firstLetter p.1 p.2 := by
  rintro ⟨i, e⟩ ⟨i', e'⟩ h
  simp only at h
  have hi : i = i' := by
    have := congrArg (fun σ : Perm (Fin (n + 1)) => σ 0) h
    simpa [firstLetter_zero] using this
  subst hi
  have h2 := mul_left_cancel h
  have := Perm.decomposeFin.symm.injective h2
  simp only [Prod.mk.injEq, true_and] at this
  rw [this]

theorem firstLetter_bijective {n : ℕ} :
    Function.Bijective fun p : Fin (n + 1) × Perm (Fin n) => firstLetter p.1 p.2 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨firstLetter_injective, ?_⟩
  simp [Fintype.card_perm, Nat.factorial_succ]

/-- Images of subsets of the deleted alphabet. -/
def liftSet {n : ℕ} (i : Fin (n + 1)) : Finset (Fin n) ↪ Finset (Fin (n + 1)) :=
  ⟨fun T => T.map (Fin.succAboveEmb i), map_injective _⟩

theorem suffixSet_firstLetter_zero {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) :
    suffixSet (firstLetter i e) 0 = univ := by
  rw [suffixSet, show Ici (0 : Fin (n + 1)) = univ by ext; simp, map_univ_equiv]

theorem suffixSet_firstLetter_succ {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) (k : Fin n) :
    suffixSet (firstLetter i e) k.succ = liftSet i (suffixSet e k) := by
  ext x
  simp only [suffixSet, liftSet, Function.Embedding.coeFn_mk, mem_map, mem_Ici,
    Fin.coe_succAboveEmb]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m : Fin n, j = m.succ := by
      refine ⟨j.pred (fun h => ?_), (Fin.succ_pred _ _).symm⟩
      rw [h] at hj
      exact absurd hj (by simp [Fin.succ_ne_zero])
    exact ⟨e m, ⟨m, Fin.succ_le_succ_iff.1 hj, rfl⟩, (firstLetter_succ i e m).symm⟩
  · rintro ⟨y, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m.succ, Fin.succ_le_succ_iff.2 hm, firstLetter_succ i e m⟩

theorem mem_map_liftSet_iff {n : ℕ} (i : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    S ∈ (subsets n).map (liftSet i) ↔ S.Nonempty ∧ i ∉ S := by
  constructor
  · rintro hS
    obtain ⟨T, hT, rfl⟩ := mem_map.1 hS
    refine ⟨(mem_filter.1 hT).2.map, fun h => ?_⟩
    obtain ⟨j, -, hj⟩ := mem_map.1 h
    exact Fin.succAbove_ne i j hj
  · rintro ⟨hne, hi⟩
    refine mem_map.2 ⟨univ.filter fun j => i.succAbove j ∈ S, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (fun h : x = i => hi (h ▸ hx))
      exact mem_filter.2 ⟨mem_univ _, j, by simpa using hx⟩
    · ext x
      simp only [liftSet, Function.Embedding.coeFn_mk, mem_map, mem_filter, mem_univ, true_and,
        Fin.coe_succAboveEmb]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hx
        obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (fun h : x = i => hi (h ▸ hx))
        exact ⟨j, hx, rfl⟩

/-- The proper subsets containing `i`. -/
def incSets {n : ℕ} (i : Fin (n + 1)) : Finset (Finset (Fin (n + 1))) :=
  univ.filter fun S => i ∈ S ∧ S ≠ univ

/-- The proper-subset incidence factor `E_{r,i} = Π_{i ∈ S ⊊ [r]} (z + λ_S)` `(GFH.3)`. -/
def incidence {n : ℕ} (i : Fin (n + 1)) : Poly (n + 1) := ∏ S ∈ incSets i, phase S

/-- Relabelling a polynomial of the deleted alphabet. -/
abbrev liftDel {n : ℕ} (i : Fin (n + 1)) : Poly n →ₐ[ℚ] Poly (n + 1) :=
  rename (Option.map i.succAbove)

theorem liftDel_phase {n : ℕ} (i : Fin (n + 1)) (T : Finset (Fin n)) :
    liftDel i (phase T) = phase (liftSet i T) := by
  simp [phase, liftSet, map_sum, rename_X, sum_map]

theorem not_mem_liftSet {n : ℕ} (i : Fin (n + 1)) (T : Finset (Fin n)) : i ∉ liftSet i T := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_map.1 h
  exact Fin.succAbove_ne i j hj

theorem subsets_succ_sdiff_chain {n : ℕ} (i : Fin (n + 1)) (e : Perm (Fin n)) :
    subsets (n + 1) \ chain (firstLetter i e) =
      incSets i ∪ (subsets n \ chain e).map (liftSet i) := by
  have hchain : chain (firstLetter i e) = insert univ ((chain e).map (liftSet i)) := by
    ext S
    simp only [chain, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_map]
    constructor
    · rintro ⟨k, rfl⟩
      refine Fin.cases (Or.inl (suffixSet_firstLetter_zero i e)) (fun k => Or.inr ?_) k
      exact ⟨suffixSet e k, ⟨k, rfl⟩, (suffixSet_firstLetter_succ i e k).symm⟩
    · rintro (rfl | ⟨T, ⟨k, rfl⟩, rfl⟩)
      · exact ⟨0, suffixSet_firstLetter_zero i e⟩
      · exact ⟨k.succ, suffixSet_firstLetter_succ i e k⟩
  ext S
  simp only [hchain, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union, Finset.mem_map,
    subsets, incSets, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hS⟩
    push Not at hS
    by_cases hi : i ∈ S
    · exact Or.inl ⟨hi, hS.1⟩
    · right
      obtain ⟨T, hT, rfl⟩ := Finset.mem_map.1 ((mem_map_liftSet_iff i S).2 ⟨hne, hi⟩)
      exact ⟨T, ⟨(Finset.mem_filter.1 hT).2, fun hc => hS.2 T hc rfl⟩, rfl⟩
  · rintro (⟨hi, hu⟩ | ⟨T, ⟨hT, hTc⟩, rfl⟩)
    · refine ⟨⟨i, hi⟩, ?_⟩
      rintro (h | ⟨a, -, rfl⟩)
      · exact hu h
      · exact not_mem_liftSet i a hi
    · refine ⟨hT.map, ?_⟩
      rintro (h | ⟨a, ha, h⟩)
      · exact not_mem_liftSet i T (h ▸ Finset.mem_univ i)
      · rw [(liftSet i).injective h] at ha
        exact hTc ha

theorem disjoint_incSets_map {n : ℕ} (i : Fin (n + 1)) (A : Finset (Finset (Fin n))) :
    Disjoint (incSets i) (A.map (liftSet i)) := by
  rw [disjoint_left]
  intro S hS h
  obtain ⟨T, -, rfl⟩ := mem_map.1 h
  obtain ⟨j, -, hj⟩ := mem_map.1 (mem_filter.1 hS).2.1
  exact Fin.succAbove_ne i j hj

/-- **The deletion law** `N_{r+1} = Σ_i (-1)^i N_r(λ̂_i) E_{r+1,i}`. -/
theorem numer_succ (n : ℕ) :
    numer (n + 1) =
      ∑ i : Fin (n + 1), ((-1) ^ (i : ℕ) : ℤ) • (liftDel i (numer n) * incidence i) := by
  rw [numer, ← (Equiv.ofBijective _ firstLetter_bijective).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [numer, map_sum, sum_mul, smul_sum]
  refine sum_congr rfl fun e _ => ?_
  simp only [Equiv.ofBijective_apply]
  rw [sign_firstLetter, subsets_succ_sdiff_chain, prod_union (disjoint_incSets_map i _),
    prod_map, map_zsmul, smul_mul_assoc, smul_smul, map_prod]
  simp only [liftDel_phase, incidence, Units.val_mul, zsmul_eq_mul, Int.cast_mul,
    sign_cycleRange_cast]
  push_cast
  ring

/-- **`(GFH.7)`**: `D_{r+1} = (z + A) D_r(λ̂_i) E_{r+1,i}`. -/
theorem denom_succ {n : ℕ} (i : Fin (n + 1)) :
    denom (n + 1) = phase univ * liftDel i (denom n) * incidence i := by
  have h : subsets (n + 1) = insert univ (incSets i ∪ (subsets n).map (liftSet i)) := by
    ext S
    simp only [mem_insert, mem_union]
    by_cases hi : i ∈ S
    · rw [mem_map_liftSet_iff]
      simp only [subsets, incSets, mem_filter, mem_univ, true_and]
      constructor
      · intro hS; by_cases hu : S = univ
        · exact Or.inl hu
        · exact Or.inr (Or.inl ⟨hi, hu⟩)
      · rintro (rfl | ⟨hi', -⟩ | ⟨-, h⟩)
        · exact univ_nonempty_iff.2 ⟨i⟩
        · exact ⟨i, hi'⟩
        · exact absurd hi h
    · rw [mem_map_liftSet_iff]
      simp only [subsets, incSets, mem_filter, mem_univ, true_and]
      constructor
      · intro hS; exact Or.inr (Or.inr ⟨hS, hi⟩)
      · rintro (rfl | ⟨hi', -⟩ | ⟨h, -⟩)
        · exact absurd (mem_univ i) hi
        · exact absurd hi' hi
        · exact h
  have hnot : univ ∉ incSets i ∪ (subsets n).map (liftSet i) := by
    rw [mem_union, not_or]
    refine ⟨fun h => (mem_filter.1 h).2.2 rfl, fun h => ?_⟩
    exact ((mem_map_liftSet_iff i univ).1 h).2 (mem_univ i)
  rw [denom, h, prod_insert hnot, prod_union (disjoint_incSets_map i _), prod_map, denom,
    map_prod]
  simp only [liftDel_phase, incidence]
  ring

/-! ### The Vandermonde boundary under deletion -/

theorem delta_succ {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R) :
    delta v = (∏ j : Fin n, (v 0 - v j.succ)) * delta (v ∘ Fin.succ) := by
  rw [delta, Fin.prod_univ_succ, prod_Ioi_zero_eq_prod_succ]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [prod_Ioi_succ_eq_prod_Ioi]
  rfl

theorem delta_comp_perm {R : Type*} [CommRing R] {n : ℕ} (v : Fin n → R) (σ : Perm (Fin n)) :
    delta (v ∘ σ) = (Perm.sign σ : ℤ) • delta v := by
  rw [delta_eq_neg_one_pow_mul, delta_eq_neg_one_pow_mul, vandermondeProd_comp, mul_smul_comm]

/-- **`(GFH.6)`**: `Δ_{r+1} = (-1)^i V_i Δ_r(λ̂_i)` with `V_i = Π_{j ≠ i} (λ_i - λ_j)`. -/
theorem delta_eq_succAbove {R : Type*} [CommRing R] {n : ℕ} (v : Fin (n + 1) → R)
    (i : Fin (n + 1)) :
    delta v = (-1) ^ (i : ℕ) * (∏ j : Fin n, (v i - v (i.succAbove j))) *
      delta (v ∘ i.succAbove) := by
  have h := delta_comp_perm v i.cycleRange.symm
  rw [delta_succ] at h
  have hs : (v ∘ i.cycleRange.symm) ∘ Fin.succ = v ∘ i.succAbove := by
    funext j; simp [Fin.cycleRange_symm_succ]
  have hprod : (∏ j : Fin n, ((v ∘ i.cycleRange.symm) 0 - (v ∘ i.cycleRange.symm) j.succ)) =
      ∏ j : Fin n, (v i - v (i.succAbove j)) :=
    prod_congr rfl fun j _ => by simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]
  have hu : (((Perm.sign i.cycleRange.symm : ℤˣ) : ℤ) : R) = (-1) ^ (i : ℕ) := by
    rw [Perm.sign_symm, sign_cycleRange_cast]
  rw [hprod, hs, zsmul_eq_mul, hu] at h
  have h2 : ((-1 : R) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc delta v = ((-1) ^ (i : ℕ) * (-1) ^ (i : ℕ)) * delta v := by rw [h2, one_mul]
    _ = (-1) ^ (i : ℕ) * ((-1) ^ (i : ℕ) * delta v) := by ring
    _ = (-1) ^ (i : ℕ) * (∏ j : Fin n, (v i - v (i.succAbove j))) *
        delta (v ∘ i.succAbove) := by rw [← h]; ring


/-! ### Evaluated deletion laws -/

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem aeval_liftDel {n : ℕ} (i : Fin (n + 1)) (z : K) (lam : Fin (n + 1) → K) (p : Poly n) :
    aeval (point z lam) (liftDel i p) = aeval (point z (lam ∘ i.succAbove)) p := by
  have h : point z lam ∘ Option.map i.succAbove = point z (lam ∘ i.succAbove) :=
    funext fun o => by cases o <;> rfl
  rw [liftDel, aeval_rename, h]

theorem aeval_incidence {n : ℕ} (i : Fin (n + 1)) (z : K) (lam : Fin (n + 1) → K) :
    aeval (point z lam) (incidence i) = ∏ S ∈ incSets i, (z + ∑ j ∈ S, lam j) := by
  rw [incidence, map_prod]
  exact prod_congr rfl fun S _ => aeval_phase z lam S

omit [Algebra ℚ K] in
theorem phases_succAbove {n : ℕ} (i : Fin (n + 1)) {z : K} {lam : Fin (n + 1) → K}
    (h : ∀ S ∈ subsets (n + 1), z + ∑ j ∈ S, lam j ≠ 0) :
    ∀ T ∈ subsets n, z + ∑ j ∈ T, (lam ∘ i.succAbove) j ≠ 0 := fun T hT => by
  have hmem : liftSet i T ∈ subsets (n + 1) :=
    mem_filter.2 ⟨mem_univ _, (mem_filter.1 hT).2.map⟩
  have := h _ hmem
  rw [show liftSet i T = T.map (Fin.succAboveEmb i) from rfl, sum_map] at this
  exact this

/-- **`(GFH.5)`**: `R_{r+1}(z;λ) = (z + A)⁻¹ Σ_i (-1)^i R_r(z; λ̂_i)`. -/
theorem alternant_succ {n : ℕ} (z : K) (lam : Fin (n + 1) → K)
    (h : ∀ S ∈ subsets (n + 1), z + ∑ j ∈ S, lam j ≠ 0) :
    alternant z lam = (z + ∑ j, lam j)⁻¹ *
      ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) * alternant z (lam ∘ i.succAbove) := by
  have hD := aeval_denom_ne_zero z lam h
  have hA : z + ∑ j, lam j ≠ 0 := h univ (mem_filter.2 ⟨mem_univ _, univ_nonempty_iff.2 ⟨0⟩⟩)
  have key := aeval_denom_mul_alternant z lam h
  rw [numer_succ, map_sum] at key
  rw [eq_inv_mul_iff_mul_eq₀ hA]
  refine mul_left_cancel₀ hD ?_
  rw [mul_left_comm, key, mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  have hDe : aeval (point z lam) (denom (n + 1)) = (z + ∑ j, lam j) *
      aeval (point z (lam ∘ i.succAbove)) (denom n) * aeval (point z lam) (incidence i) := by
    rw [denom_succ i, map_mul, map_mul, aeval_phase, aeval_liftDel]
  rw [map_zsmul, map_mul, aeval_liftDel, ← aeval_denom_mul_alternant z _ (phases_succAbove i h),
    hDe, zsmul_eq_mul]
  push_cast
  ring

/-- **Theorem 2.1, `(GFH.4)`**: for pairwise distinct grades,
`P_{r+1}(z;λ) = Σ_i P_r(z; λ̂_i) E_{r+1,i}(z;λ) / V_i`, `V_i = Π_{j ≠ i} (λ_i - λ_j)`. -/
theorem formNumer_succ {n : ℕ} (z : K) {lam : Fin (n + 1) → K} (hlam : Function.Injective lam) :
    aeval (point z lam) (formNumer (n + 1)) = ∑ i : Fin (n + 1),
      aeval (point z (lam ∘ i.succAbove)) (formNumer n) * aeval (point z lam) (incidence i) /
        ∏ j : Fin n, (lam i - lam (i.succAbove j)) := by
  have hΔ : delta lam ≠ 0 := by
    rw [delta]
    refine prod_ne_zero_iff.2 fun a _ => prod_ne_zero_iff.2 fun b hb => sub_ne_zero.2 ?_
    exact fun h => (ne_of_lt (mem_Ioi.1 hb)) (hlam h)
  have hV : ∀ i : Fin (n + 1), ∏ j : Fin n, (lam i - lam (i.succAbove j)) ≠ 0 := fun i =>
    prod_ne_zero_iff.2 fun j _ => sub_ne_zero.2 fun h => Fin.succAbove_ne i j (hlam h).symm
  have key := congrArg (aeval (point z lam)) (numer_succ n)
  rw [numer_eq, map_mul, aeval_deltaPoly, map_sum] at key
  refine mul_left_cancel₀ hΔ ?_
  rw [key, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_mul, aeval_liftDel, numer_eq, map_mul, aeval_deltaPoly,
    delta_eq_succAbove lam i, zsmul_eq_mul]
  have h1 : ((-1 : K) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  push_cast
  have hVi := hV i
  field_simp

/-! ### Complement reflection -/

/-- The reflection `z ↦ -A - z` of the spectral parameter, `A = Σ λ_i`. -/
def reflect (r : ℕ) : Poly r →ₐ[ℚ] Poly r :=
  aeval fun o : Option (Fin r) => o.elim (-X none - ∑ i, X (some i)) fun i => X (some i)

theorem reflect_phase {r : ℕ} (S : Finset (Fin r)) : reflect r (phase S) = -phase Sᶜ := by
  have h := sum_add_sum_compl S fun i => (X (some i) : Poly r)
  simp only [reflect, phase, map_add, map_sum, aeval_X, Option.elim_none, Option.elim_some]
  linear_combination h

theorem reflect_X_some {r : ℕ} (i : Fin r) : reflect r (X (some i)) = X (some i) := by
  simp [reflect]

theorem reflect_deltaPoly (r : ℕ) : reflect r (deltaPoly r) = deltaPoly r := by
  simp [deltaPoly, delta, map_prod, map_sub, reflect_X_some]

/-- The prefix set `{π(0), …, π(m-1)}`. -/
def prefixSet {r : ℕ} (π : Perm (Fin r)) (m : ℕ) : Finset (Fin r) :=
  (univ.filter fun j : Fin r => (j : ℕ) < m).map π.toEmbedding

theorem compl_suffixSet {r : ℕ} (π : Perm (Fin r)) (k : Fin r) :
    (suffixSet π k)ᶜ = prefixSet π k := by
  ext x
  simp only [mem_compl, mem_suffixSet, prefixSet, mem_map, mem_filter, mem_univ, true_and,
    Equiv.coe_toEmbedding, not_le]
  constructor
  · intro h; exact ⟨π.symm x, Fin.lt_def.1 h, π.apply_symm_apply x⟩
  · rintro ⟨j, hj, rfl⟩
    rw [π.symm_apply_apply]
    exact Fin.lt_def.2 hj

theorem suffixSet_mul_rev {r : ℕ} (π : Perm (Fin r)) (k : Fin r) :
    suffixSet (π * Fin.revPerm) k = prefixSet π (r - k) := by
  ext x
  simp only [suffixSet, prefixSet, mem_map, mem_Ici, mem_filter, mem_univ, true_and,
    Equiv.coe_toEmbedding, Perm.coe_mul, Function.comp_apply, Fin.revPerm_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.rev, ?_, rfl⟩
    have := Fin.val_rev j
    have hk := Fin.le_def.1 hj
    omega
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.rev, ?_, by simp⟩
    rw [Fin.le_def, Fin.val_rev]
    omega

theorem prefixSet_zero {r : ℕ} (π : Perm (Fin r)) : prefixSet π 0 = ∅ := by
  simp [prefixSet]

theorem prefixSet_self {r : ℕ} (π : Perm (Fin r)) : prefixSet π r = univ := by
  ext x
  simp only [prefixSet, mem_map, mem_filter, mem_univ, true_and, Equiv.coe_toEmbedding,
    iff_true]
  exact ⟨π.symm x, (π.symm x).2, π.apply_symm_apply x⟩

theorem mem_subsets_sdiff_chain {r : ℕ} (π : Perm (Fin r)) (S : Finset (Fin r)) :
    S ∈ subsets r \ chain π ↔ ∀ m ≤ r, Sᶜ ≠ prefixSet π m := by
  simp only [mem_sdiff, subsets, mem_filter, mem_univ, true_and, chain, mem_image]
  constructor
  · rintro ⟨hne, hS⟩ m hm h
    rcases lt_or_eq_of_le hm with hlt | rfl
    · refine hS ⟨⟨m, hlt⟩, ?_⟩
      rw [← compl_inj_iff, compl_suffixSet, h]
    · rw [prefixSet_self, compl_eq_univ_iff] at h
      exact hne.ne_empty h
  · intro h
    refine ⟨Finset.nonempty_iff_ne_empty.2 fun h0 => h r le_rfl ?_, ?_⟩
    · rw [h0, compl_empty, prefixSet_self]
    · rintro ⟨k, rfl⟩
      exact h k k.2.le (compl_suffixSet π k)

theorem mem_subsets_sdiff_chain_rev {r : ℕ} (π : Perm (Fin r)) (T : Finset (Fin r)) :
    T ∈ subsets r \ chain (π * Fin.revPerm) ↔ ∀ m ≤ r, T ≠ prefixSet π m := by
  simp only [mem_sdiff, subsets, mem_filter, mem_univ, true_and, chain, mem_image]
  constructor
  · rintro ⟨hne, hT⟩ m hm h
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [prefixSet_zero] at h; exact hne.ne_empty h
    · refine hT ⟨⟨r - m, by omega⟩, ?_⟩
      rw [suffixSet_mul_rev, h]
      congr 1
      simp only
      omega
  · intro h
    refine ⟨Finset.nonempty_iff_ne_empty.2 fun h0 => h 0 (Nat.zero_le _) (by rw [h0,
      prefixSet_zero]), ?_⟩
    rintro ⟨k, rfl⟩
    exact h (r - k) (Nat.sub_le _ _) (suffixSet_mul_rev π k)

/-- Complementation of subsets. -/
def complEmb (r : ℕ) : Finset (Fin r) ↪ Finset (Fin r) := ⟨compl, compl_injective⟩

theorem map_compl_sdiff_chain {r : ℕ} (π : Perm (Fin r)) :
    (subsets r \ chain π).map (complEmb r) = subsets r \ chain (π * Fin.revPerm) := by
  ext T
  rw [mem_subsets_sdiff_chain_rev, mem_map]
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact (mem_subsets_sdiff_chain π S).1 hS
  · intro h
    refine ⟨Tᶜ, (mem_subsets_sdiff_chain π _).2 fun m hm => ?_, compl_compl T⟩
    rw [compl_compl]
    exact h m hm

theorem card_subsets_sdiff_chain {r : ℕ} (π : Perm (Fin r)) :
    (subsets r \ chain π).card = 2 ^ r - 1 - r := by
  rw [card_sdiff_of_subset (chain_subset π), card_subsets, card_chain]

theorem reflect_prod_sdiff {r : ℕ} (π : Perm (Fin r)) :
    reflect r (∏ S ∈ subsets r \ chain π, phase S) =
      (-1) ^ (2 ^ r - 1 - r) * ∏ T ∈ subsets r \ chain (π * Fin.revPerm), phase T := by
  rw [map_prod, ← map_compl_sdiff_chain, prod_map, ← card_subsets_sdiff_chain π,
    ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun S _ => ?_
  rw [reflect_phase]
  simp [complEmb]

theorem card_finPairsLT (r : ℕ) : (Perm.finPairsLT r).card = r * (r - 1) / 2 := by
  rw [Perm.finPairsLT, card_sigma]
  simp only [card_attachFin, card_range]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, sum_range_id]

/-- The reversal of `[r]` has sign `(-1)^{r(r-1)/2}`. -/
theorem sign_revPerm_cast {R : Type*} [CommRing R] (r : ℕ) :
    (((Perm.sign (Fin.revPerm : Perm (Fin r)) : ℤˣ) : ℤ) : R) = (-1) ^ (r * (r - 1) / 2) := by
  have h : Perm.sign (Fin.revPerm : Perm (Fin r)) = ∏ _x ∈ Perm.finPairsLT r, (-1 : ℤˣ) := by
    rw [sign_eq_signAux, Perm.signAux]
    refine prod_congr rfl fun x hx => ?_
    rw [Perm.mem_finPairsLT] at hx
    rw [if_pos]
    simp only [Fin.revPerm_apply]
    exact (Fin.rev_lt_rev.2 hx).le
  rw [h, prod_const, card_finPairsLT, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  push_cast
  ring

/-- The reflection of the alternant numerator. -/
theorem reflect_numer (r : ℕ) :
    reflect r (numer r) = ((-1) ^ (2 ^ r - 1 - r) * (-1) ^ (r * (r - 1) / 2) : Poly r) *
      numer r := by
  rw [numer, map_sum, mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun π => ?_
  rw [map_zsmul, reflect_prod_sdiff, Equiv.coe_mulRight, zsmul_eq_mul, zsmul_eq_mul,
    Perm.sign_mul, Units.val_mul, Int.cast_mul, sign_revPerm_cast]
  have h1 : ((-1) ^ (r * (r - 1) / 2) : Poly r) * (-1) ^ (r * (r - 1) / 2) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  linear_combination (-((((Perm.sign π : ℤˣ) : ℤ) : Poly r) * (-1) ^ (2 ^ r - 1 - r) *
    ∏ T ∈ subsets r \ chain (π * Fin.revPerm), phase T)) * h1


/-- The reflection sign `(-1)^{2^r-1-r} (-1)^{r(r-1)/2} = (-1)^{r(r+1)/2+1}` for `r ≥ 1`. -/
theorem reflect_sign {R : Type*} [CommRing R] {r : ℕ} (hr : 1 ≤ r) :
    ((-1 : R) ^ (2 ^ r - 1 - r) * (-1) ^ (r * (r - 1) / 2)) = (-1) ^ (r * (r + 1) / 2 + 1) := by
  have hq : r * (r + 1) / 2 = r * (r - 1) / 2 + r := by
    rw [show r * (r + 1) = r * (r - 1) + r * 2 by
      obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring, Nat.add_mul_div_right _ _ two_pos]
  have h2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hle : r + 1 ≤ 2 ^ r := Nat.lt_two_pow_self
  have heven : Even ((2 ^ r - 1 - r) + r * (r - 1) / 2 + (r * (r + 1) / 2 + 1)) := by
    rw [hq]
    generalize r * (r - 1) / 2 = p at *
    rw [h2] at hle ⊢
    generalize 2 ^ (r - 1) = M at *
    exact ⟨M + p, by omega⟩
  rw [← pow_add]
  have h3 : ((-1 : R) ^ ((2 ^ r - 1 - r) + r * (r - 1) / 2)) *
      (-1) ^ (r * (r + 1) / 2 + 1) = 1 := by rw [← pow_add]; exact heven.neg_one_pow
  have h4 : ((-1 : R) ^ (r * (r + 1) / 2 + 1)) * (-1) ^ (r * (r + 1) / 2 + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc ((-1 : R) ^ ((2 ^ r - 1 - r) + r * (r - 1) / 2))
      = (-1) ^ ((2 ^ r - 1 - r) + r * (r - 1) / 2) * ((-1) ^ (r * (r + 1) / 2 + 1) *
          (-1) ^ (r * (r + 1) / 2 + 1)) := by rw [h4, mul_one]
    _ = (-1) ^ (r * (r + 1) / 2 + 1) := by rw [← mul_assoc, h3, one_mul]

/-- **Theorem 2.2, `(GFH.R1)`: complement reflection** `P_r(-A - z) = (-1)^{r(r+1)/2+1} P_r(z)`. -/
theorem reflect_formNumer {r : ℕ} (hr : 1 ≤ r) :
    reflect r (formNumer r) = (-1) ^ (r * (r + 1) / 2 + 1) * formNumer r := by
  have h := reflect_numer r
  rw [numer_eq, map_mul, reflect_deltaPoly, reflect_sign hr, mul_left_comm] at h
  exact mul_left_cancel₀ (deltaPoly_ne_zero r) h

theorem map_complEmb_subsets (r : ℕ) : (subsets r).map (complEmb r) = univ.erase univ := by
  ext T
  simp only [mem_map, mem_erase, mem_univ, and_true, subsets, mem_filter, true_and, complEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨S, hS, rfl⟩ h
    rw [compl_eq_univ_iff] at h
    exact hS.ne_empty h
  · intro h
    refine ⟨Tᶜ, Finset.nonempty_iff_ne_empty.2 fun h' => h ?_, compl_compl T⟩
    rw [← compl_compl T, h', compl_empty]

/-- **`(GFH.R5)`**: `(z + A) D_r(-A - z) = -z D_r(z)` for `r ≥ 1`. -/
theorem reflect_denom {r : ℕ} (hr : 1 ≤ r) :
    phase (univ : Finset (Fin r)) * reflect r (denom r) = -X none * denom r := by
  have h1 : reflect r (denom r) = (-1) ^ (2 ^ r - 1) * ∏ T ∈ univ.erase univ, phase T := by
    rw [denom, map_prod, ← map_complEmb_subsets, prod_map, ← card_subsets r, ← prod_const,
      ← prod_mul_distrib]
    refine prod_congr rfl fun S _ => ?_
    rw [reflect_phase]
    simp [complEmb]
  have h2 : (∏ T ∈ univ.erase univ, phase T) * phase (univ : Finset (Fin r)) =
      X none * denom r := by
    rw [prod_erase_mul _ _ (mem_univ _), denom, ← prod_erase_mul _ _ (mem_univ ∅),
      show (univ : Finset (Finset (Fin r))).erase ∅ = subsets r by ext; simp [subsets,
        Finset.nonempty_iff_ne_empty], phase, sum_empty, add_zero, mul_comm]
  have h3 : ((-1 : Poly r) ^ (2 ^ r - 1)) = -1 := by
    have : 2 ^ r - 1 = 2 * 2 ^ (r - 1) - 1 := by
      rw [← pow_succ']; congr 2; omega
    rw [this]
    have hpos : 1 ≤ 2 * 2 ^ (r - 1) := by have := Nat.one_le_two_pow (n := r - 1); omega
    obtain ⟨m, hm⟩ : ∃ m, 2 * 2 ^ (r - 1) - 1 = 2 * m + 1 := ⟨2 ^ (r - 1) - 1, by omega⟩
    rw [hm, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  rw [h1, h3, mul_comm, mul_assoc, h2]
  ring

/-- The reflection evaluates the polynomial at `z ↦ -A - z`. -/
theorem aeval_reflect {r : ℕ} (z : K) (lam : Fin r → K) (p : Poly r) :
    aeval (point z lam) (reflect r p) = aeval (point (-z - ∑ i, lam i) lam) p := by
  have h := congrArg (fun φ : Poly r →ₐ[ℚ] K => φ p) (comp_aeval
    (fun o : Option (Fin r) => o.elim (-X none - ∑ i, X (some i)) fun i => X (some i))
    (aeval (point z lam)))
  simp only [AlgHom.comp_apply] at h
  have hpt : (fun i : Option (Fin r) => aeval (point z lam)
      (i.elim (-X none - ∑ i, X (some i) : Poly r) fun i => X (some i))) =
        point (-z - ∑ i, lam i) lam :=
    funext fun o => by
      cases o
      · rw [Option.elim_none, map_sub, map_neg, map_sum]
        simp [point]
      · simp [point]
  rw [reflect, h, hpt]

/-- **`(GFH.R1)` evaluated; centered parity.**  With `x = z + A/2`, `P_r(-A/2 - x) =
(-1)^{r(r+1)/2+1} P_r(-A/2 + x)`. -/
theorem aeval_formNumer_reflect {r : ℕ} (hr : 1 ≤ r) (z : K) (lam : Fin r → K) :
    aeval (point (-z - ∑ i, lam i) lam) (formNumer r) =
      (-1) ^ (r * (r + 1) / 2 + 1) * aeval (point z lam) (formNumer r) := by
  rw [← aeval_reflect, reflect_formNumer hr, map_mul, map_pow, map_neg, map_one]

/-- **`(GFH.R4)`**: `R_r(-A - z) = (-1)^{r(r+1)/2} ((z + A)/z) R_r(z)`. -/
theorem alternant_reflect {r : ℕ} (hr : 1 ≤ r) {z : K} {lam : Fin r → K} (hz : z ≠ 0)
    (h : ∀ S ∈ subsets r, z + ∑ i ∈ S, lam i ≠ 0)
    (h' : ∀ S ∈ subsets r, (-z - ∑ i, lam i) + ∑ i ∈ S, lam i ≠ 0) :
    alternant (-z - ∑ i, lam i) lam =
      (-1) ^ (r * (r + 1) / 2) * ((z + ∑ i, lam i) / z) * alternant z lam := by
  have hD := congrArg (aeval (point z lam)) (reflect_denom (r := r) hr)
  rw [map_mul, map_mul, aeval_reflect, aeval_phase, map_neg, aeval_X] at hD
  simp only [point, Option.elim_none] at hD
  have hA : z + ∑ i, lam i ≠ 0 := h univ (mem_filter.2 ⟨mem_univ _, univ_nonempty_iff.2 ⟨⟨0, hr⟩⟩⟩)
  have hD0 := aeval_denom_ne_zero z lam h
  have hD1 := aeval_denom_ne_zero _ lam h'
  have hD' : aeval (point (-z - ∑ i, lam i) lam) (denom r) =
      -z * aeval (point z lam) (denom r) / (z + ∑ i, lam i) := by
    rw [eq_div_iff hA, mul_comm]; exact hD
  rw [alternant_eq _ _ h', alternant_eq _ _ h, aeval_formNumer_reflect hr, hD', pow_succ]
  field_simp

/-- **`(GFH.R2)`**: if `r(r+1)/2` is even, `2z + A` divides `P_r`. -/
theorem sub_dvd_sub_aeval_update {r : ℕ} (q : Poly r) (p : Poly r) :
    (X none - q) ∣ p - aeval (fun o : Option (Fin r) => o.elim q fun i => X (some i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p₁ p₂ h₁ h₂ =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add h₁ h₂
  | mul_X p o hp =>
    rw [map_mul, aeval_X]
    have : p * X o - aeval (fun o : Option (Fin r) => o.elim q fun i => X (some i)) p *
        o.elim q (fun i => X (some i)) =
        (p - aeval (fun o : Option (Fin r) => o.elim q fun i => X (some i)) p) * X o +
        aeval (fun o : Option (Fin r) => o.elim q fun i => X (some i)) p *
          (X o - o.elim q fun i => X (some i)) := by ring
    rw [this]
    refine dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right ?_ _)
    cases o
    · exact dvd_rfl
    · simp

theorem two_mul_X_add_dvd_formNumer {r : ℕ} (hr : 1 ≤ r) (heven : Even (r * (r + 1) / 2)) :
    (2 * X none + ∑ i, X (some i) : Poly r) ∣ formNumer r := by
  set q : Poly r := -(1 / 2 : ℚ) • ∑ i, X (some i)
  set φ : Poly r →ₐ[ℚ] Poly r := aeval fun o : Option (Fin r) => o.elim q fun i => X (some i)
  have hφr : φ.comp (reflect r) = φ := by
    refine MvPolynomial.algHom_ext fun o => ?_
    cases o
    · simp only [AlgHom.comp_apply, reflect, aeval_X, Option.elim_none, φ, map_sub, map_neg,
        map_sum, Option.elim_some, q]
      module
    · simp [φ, reflect]
  have hsign : (-1 : Poly r) ^ (r * (r + 1) / 2 + 1) = -1 := by
    rw [pow_succ, heven.neg_one_pow, one_mul]
  have hzero : φ (formNumer r) = 0 := by
    have h1 := congrArg (fun ψ : Poly r →ₐ[ℚ] Poly r => ψ (formNumer r)) hφr
    simp only [AlgHom.comp_apply] at h1
    rw [reflect_formNumer hr, hsign, neg_one_mul, map_neg] at h1
    have h2 : (2 : ℚ) • φ (formNumer r) = 0 := by
      rw [two_smul]; nth_rewrite 1 [← h1]; rw [neg_add_cancel]
    simpa using h2
  obtain ⟨k, hk⟩ := sub_dvd_sub_aeval_update q (formNumer r)
  rw [show aeval (fun o : Option (Fin r) => o.elim q fun i => X (some i)) (formNumer r) = 0
    from hzero, sub_zero] at hk
  refine ⟨C (1 / 2 : ℚ) * k, ?_⟩
  rw [hk]
  simp only [q, smul_eq_C_mul]
  rw [← mul_assoc]
  congr 1
  have h2 : (2 : Poly r) * C (1 / 2 : ℚ) = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  rw [C_neg]
  linear_combination (-(X none : Poly r)) * h2

end Permutohedral

end

end GaloisForLFunctions.HTGeometry
