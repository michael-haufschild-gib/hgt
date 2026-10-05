import GaloisForLFunctions.HTGeometry.AlternantVandermondeDivisibility
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# The permutohedral alternant and its formation numerator

For grades `λ_1, …, λ_r` and a spectral parameter `z`, a schedule `π ∈ S_r` has suffix sums
`S_k(π) = Σ_{j ≥ k} λ_{π(j)}` and the full schedule alternant is
`R_r(z;λ) = Σ_π sgn(π) Π_k (z + S_k(π))⁻¹`.  Every suffix set of `π` is a nonempty subset of
`[r]` and the suffix sets of `π` form a chain of `r` distinct subsets, so with
`D_r = Π_{S ≠ ∅} (z + λ_S)` the product `N_r = D_r R_r` is the polynomial
`N_r = Σ_π sgn(π) Π_{S ∉ chain(π)} (z + λ_S)`.  Relabelling the grades by `τ` maps the chain of `π`
to the chain of `τπ`, so `N_r` is alternating.  Antisymmetrising each monomial produces an
alternant `det(λ_i^{m_j})`, which the Vandermonde product divides; hence
`N_r = Δ_r P_r` with `Δ_r = Π_{i<j} (λ_i - λ_j)` and `P_r` symmetric in the grades, of total
degree at most `2^r - 1 - r(r+1)/2` `(PGE.23)`–`(PGE.26)`.  At the first grades
`P_1 = P_2 = 1` and `P_3 = 2z + λ_1 + λ_2 + λ_3` `(PGE.27)`.

Polynomials live in `ℚ[z, λ_1, …, λ_r]`, with variable `none` for `z` and `some i` for `λ_i`.
-/

open MvPolynomial Finset Equiv

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace Permutohedral

variable {r : ℕ}

/-- The polynomial ring `ℚ[z, λ_1, …, λ_r]`. -/
abbrev Poly (r : ℕ) := MvPolynomial (Option (Fin r)) ℚ

/-- The phase factor `z + λ_S`. -/
def phase (S : Finset (Fin r)) : Poly r := X none + ∑ i ∈ S, X (some i)

/-- The nonempty subsets of `[r]`. -/
def subsets (r : ℕ) : Finset (Finset (Fin r)) := univ.filter Finset.Nonempty

/-- The suffix set `{π(k), …, π(r-1)}` of a schedule. -/
def suffixSet (π : Perm (Fin r)) (k : Fin r) : Finset (Fin r) := (Ici k).map π.toEmbedding

/-- The suffix chain of a schedule. -/
def chain (π : Perm (Fin r)) : Finset (Finset (Fin r)) := univ.image (suffixSet π)

/-- The subset-phase denominator `D_r = Π_{S ≠ ∅} (z + λ_S)`. -/
def denom (r : ℕ) : Poly r := ∏ S ∈ subsets r, phase S

/-- The alternant numerator `N_r = Σ_π sgn(π) Π_{S ∉ chain(π)} (z + λ_S) = D_r R_r`. -/
def numer (r : ℕ) : Poly r :=
  ∑ π : Perm (Fin r), (Perm.sign π : ℤ) • ∏ S ∈ subsets r \ chain π, phase S

/-- The Vandermonde boundary `Δ_r = Π_{i<j} (λ_i - λ_j)` in a commutative ring. -/
def delta {R : Type*} [CommRing R] (lam : Fin r → R) : R :=
  ∏ i : Fin r, ∏ j ∈ Ioi i, (lam i - lam j)

/-- The Vandermonde boundary as a polynomial. -/
def deltaPoly (r : ℕ) : Poly r := delta fun i => (X (some i) : Poly r)

/-! ### Suffix sets and chains -/

theorem mem_suffixSet {π : Perm (Fin r)} {k : Fin r} {i : Fin r} :
    i ∈ suffixSet π k ↔ k ≤ π.symm i := by
  simp only [suffixSet, mem_map, mem_Ici, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨j, hj, rfl⟩; simpa using hj
  · intro h; exact ⟨π.symm i, h, by simp⟩

theorem card_suffixSet (π : Perm (Fin r)) (k : Fin r) : (suffixSet π k).card = r - k := by
  rw [suffixSet, card_map, Fin.card_Ici]

theorem suffixSet_nonempty (π : Perm (Fin r)) (k : Fin r) : (suffixSet π k).Nonempty :=
  ⟨π k, mem_suffixSet.2 (by simp)⟩

theorem suffixSet_injective (π : Perm (Fin r)) : Function.Injective (suffixSet π) := by
  intro k l h
  have := congrArg Finset.card h
  rw [card_suffixSet, card_suffixSet] at this
  exact Fin.ext (by omega)

theorem chain_subset (π : Perm (Fin r)) : chain π ⊆ subsets r := by
  intro S hS
  obtain ⟨k, -, rfl⟩ := mem_image.1 hS
  exact mem_filter.2 ⟨mem_univ _, suffixSet_nonempty π k⟩

theorem card_chain (π : Perm (Fin r)) : (chain π).card = r := by
  rw [chain, card_image_of_injective _ (suffixSet_injective π), card_univ, Fintype.card_fin]

theorem card_subsets (r : ℕ) : (subsets r).card = 2 ^ r - 1 := by
  have h : subsets r = univ.erase ∅ := by
    ext S
    simp [subsets, Finset.nonempty_iff_ne_empty]
  rw [h, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_finset, Fintype.card_fin]

theorem suffixSet_mul (τ π : Perm (Fin r)) (k : Fin r) :
    suffixSet (τ * π) k = (suffixSet π k).map τ.toEmbedding := by
  rw [suffixSet, suffixSet, map_map]
  rfl

/-! ### The evaluated alternant -/

/-- The suffix sum `S_k(π) = Σ_{j ≥ k} λ_{π(j)}`. -/
def suffixSum {K : Type*} [AddCommMonoid K] (lam : Fin r → K) (π : Perm (Fin r)) (k : Fin r) :
    K := ∑ j ∈ Ici k, lam (π j)

/-- The full schedule alternant `R_r(z;λ) = Σ_π sgn(π) Π_k (z + S_k(π))⁻¹` `(PGE.23)`. -/
def alternant {K : Type*} [Field K] (z : K) (lam : Fin r → K) : K :=
  ∑ π : Perm (Fin r), (Perm.sign π : ℤ) • ∏ k : Fin r, (z + suffixSum lam π k)⁻¹

/-- The evaluation point `(z, λ)`. -/
def point {K : Type*} (z : K) (lam : Fin r → K) : Option (Fin r) → K := fun o => o.elim z lam

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem aeval_phase (z : K) (lam : Fin r → K) (S : Finset (Fin r)) :
    aeval (point z lam) (phase S) = z + ∑ i ∈ S, lam i := by
  simp [phase, point, map_sum]

theorem aeval_phase_suffixSet (z : K) (lam : Fin r → K) (π : Perm (Fin r)) (k : Fin r) :
    aeval (point z lam) (phase (suffixSet π k)) = z + suffixSum lam π k := by
  rw [aeval_phase, suffixSet, sum_map]
  rfl

/-- **`D_r R_r = N_r`** at every point where no phase factor vanishes. -/
theorem aeval_denom_mul_alternant (z : K) (lam : Fin r → K)
    (h : ∀ S ∈ subsets r, z + ∑ i ∈ S, lam i ≠ 0) :
    aeval (point z lam) (denom r) * alternant z lam = aeval (point z lam) (numer r) := by
  rw [alternant, mul_sum, numer, map_sum]
  refine sum_congr rfl fun π _ => ?_
  rw [map_zsmul, mul_smul_comm, denom, map_prod, ← prod_sdiff (chain_subset π)]
  congr 1
  have hchain : ∏ S ∈ chain π, aeval (point z lam) (phase S) =
      ∏ k : Fin r, (z + suffixSum lam π k) := by
    rw [chain, prod_image fun k _ l _ hkl => suffixSet_injective π hkl]
    exact prod_congr rfl fun k _ => aeval_phase_suffixSet z lam π k
  have hinv : ∀ k : Fin r, (z + suffixSum lam π k) * (z + suffixSum lam π k)⁻¹ = 1 := fun k => by
    refine mul_inv_cancel₀ ?_
    rw [← aeval_phase_suffixSet, aeval_phase]
    exact h _ (chain_subset π (mem_image_of_mem _ (mem_univ k)))
  rw [hchain, map_prod, mul_assoc, ← prod_mul_distrib]
  simp only [hinv, prod_const_one, mul_one]


/-! ### The alternating law -/

/-- Relabelling the grades by a permutation `τ`. -/
abbrev relabel (τ : Perm (Fin r)) : Poly r →ₐ[ℚ] Poly r := rename (Option.map τ)

/-- The induced bijection `S ↦ τ(S)` on subsets. -/
def liftPerm (τ : Perm (Fin r)) : Finset (Fin r) ↪ Finset (Fin r) :=
  ⟨fun S => S.map τ.toEmbedding, map_injective _⟩

theorem relabel_phase (τ : Perm (Fin r)) (S : Finset (Fin r)) :
    relabel τ (phase S) = phase (liftPerm τ S) := by
  simp [phase, liftPerm, map_sum, rename_X, sum_map]

theorem map_liftPerm_subsets (τ : Perm (Fin r)) : (subsets r).map (liftPerm τ) = subsets r := by
  refine eq_of_subset_of_card_le (fun S hS => ?_) (by rw [card_map])
  obtain ⟨T, hT, rfl⟩ := mem_map.1 hS
  exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hT).2.map⟩

theorem map_liftPerm_chain (τ π : Perm (Fin r)) : (chain π).map (liftPerm τ) = chain (τ * π) := by
  rw [chain, chain, map_eq_image, image_image]
  refine image_congr fun k _ => ?_
  simp only [Function.comp_apply, liftPerm, Function.Embedding.coeFn_mk, suffixSet_mul]

theorem prod_relabel_sdiff (τ π : Perm (Fin r)) :
    relabel τ (∏ S ∈ subsets r \ chain π, phase S) = ∏ S ∈ subsets r \ chain (τ * π), phase S := by
  have h : subsets r \ chain (τ * π) = (subsets r \ chain π).map (liftPerm τ) := by
    rw [Finset.map_sdiff, map_liftPerm_subsets, map_liftPerm_chain]
  rw [h, prod_map, map_prod]
  exact prod_congr rfl fun S _ => relabel_phase τ S

/-- **`N_r` is alternating** in the grades. -/
theorem relabel_numer (τ : Perm (Fin r)) : relabel τ (numer r) = (Perm.sign τ : ℤ) • numer r := by
  rw [numer, map_sum, smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun π => ?_
  rw [map_zsmul, prod_relabel_sdiff, Equiv.coe_mulLeft, smul_smul, Perm.sign_mul,
    Units.val_mul, ← mul_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_mul]

/-! ### Vandermonde divisibility -/

theorem map_vandermondeProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (v : Fin r → R) : f (vandermondeProd v) = vandermondeProd (f ∘ v) := by
  simp [vandermondeProd, map_prod, map_sub]

theorem delta_eq_neg_one_pow_mul {R : Type*} [CommRing R] (v : Fin r → R) :
    delta v = (-1) ^ (∑ i : Fin r, (Ioi i).card) * vandermondeProd v := by
  rw [delta, vandermondeProd, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_neg]
  exact prod_congr rfl fun j _ => by ring

/-- The Vandermonde product of the grade variables. -/
def vdm (r : ℕ) : Poly r := vandermondeProd fun i => (X (some i) : Poly r)

theorem relabel_vdm (τ : Perm (Fin r)) : relabel τ (vdm r) = (Perm.sign τ : ℤ) • vdm r := by
  have h1 : relabel τ (vdm r) = vandermondeProd ((fun i => (X (some i) : Poly r)) ∘ τ) := by
    simp [vdm, vandermondeProd, map_prod, map_sub]
  rw [h1, vandermondeProd_comp]
  rfl

theorem deltaPoly_eq (r : ℕ) :
    deltaPoly r = (-1) ^ (∑ i : Fin r, (Ioi i).card) * vdm r := delta_eq_neg_one_pow_mul _

theorem relabel_deltaPoly (τ : Perm (Fin r)) :
    relabel τ (deltaPoly r) = (Perm.sign τ : ℤ) • deltaPoly r := by
  rw [deltaPoly_eq, map_mul, relabel_vdm, map_pow, map_neg, map_one, mul_smul_comm]

theorem vdm_ne_zero (r : ℕ) : vdm r ≠ 0 :=
  vandermondeProd_ne_zero fun _ _ h => Option.some_injective _ (X_injective h)

theorem deltaPoly_ne_zero (r : ℕ) : deltaPoly r ≠ 0 := by
  rw [deltaPoly_eq]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (vdm_ne_zero r)

/-- The antisymmetrisation `Σ_τ sgn(τ) τ·p`. -/
def antisym (p : Poly r) : Poly r := ∑ τ : Perm (Fin r), (Perm.sign τ : ℤ) • relabel τ p

theorem antisym_add (p q : Poly r) : antisym (p + q) = antisym p + antisym q := by
  simp only [antisym, map_add, smul_add, sum_add_distrib]

theorem antisym_sum {ι : Type*} (s : Finset ι) (p : ι → Poly r) :
    antisym (∑ i ∈ s, p i) = ∑ i ∈ s, antisym (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [antisym]
  | insert i s hi ih => rw [sum_insert hi, sum_insert hi, antisym_add, ih]

theorem monomial_eq_split (m : Option (Fin r) →₀ ℕ) (c : ℚ) :
    monomial m c = C c * (X none ^ m none * ∏ j : Fin r, X (some j) ^ m (some j)) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _, Fintype.prod_option]

theorem antisym_monomial (m : Option (Fin r) →₀ ℕ) (c : ℚ) :
    antisym (monomial m c) = C c * X none ^ m none *
      (Matrix.of fun i j : Fin r => (X (some i) : Poly r) ^ m (some j)).det := by
  rw [antisym, Matrix.det_apply, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [monomial_eq_split, map_mul, map_mul, map_pow, map_prod, algHom_C, rename_X]
  simp only [map_pow, rename_X, Option.map_some, Option.map_none, Matrix.of_apply, algebraMap_eq,
    Units.smul_def, zsmul_eq_mul]
  ring

/-- **An alternating polynomial is divisible by the Vandermonde product.** -/
theorem vdm_dvd_of_alternating {p : Poly r}
    (hp : ∀ τ : Perm (Fin r), relabel τ p = (Perm.sign τ : ℤ) • p) : vdm r ∣ p := by
  have hanti : antisym p = (r.factorial : ℚ) • p := by
    rw [antisym]
    simp_rw [hp, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
      sum_const, card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]
  have hdvd : vdm r ∣ antisym p := by
    rw [p.as_sum, antisym_sum]
    refine dvd_sum fun m _ => ?_
    rw [antisym_monomial]
    exact dvd_mul_of_dvd_right (vandermondeProd_dvd_det_pow _ _) _
  have hfac : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  have : p = C ((r.factorial : ℚ)⁻¹) * antisym p := by
    rw [hanti, smul_eq_C_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hfac, C_1, one_mul]
  rw [this]
  exact dvd_mul_of_dvd_right hdvd _

theorem deltaPoly_dvd_numer (r : ℕ) : deltaPoly r ∣ numer r := by
  obtain ⟨k, hk⟩ := vdm_dvd_of_alternating (relabel_numer (r := r))
  refine ⟨(-1) ^ (∑ i : Fin r, (Ioi i).card) * k, ?_⟩
  have hu : ((-1 : Poly r) ^ (∑ i : Fin r, (Ioi i).card)) * (-1) ^ (∑ i : Fin r, (Ioi i).card) =
      1 := by rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hk, deltaPoly_eq]
  linear_combination (-(vdm r * k)) * hu

/-! ### The formation numerator -/

/-- The formation numerator `P_r`, defined by `N_r = Δ_r P_r` `(PGE.25)`. -/
def formNumer (r : ℕ) : Poly r := Classical.choose (deltaPoly_dvd_numer r)

theorem numer_eq (r : ℕ) : numer r = deltaPoly r * formNumer r :=
  Classical.choose_spec (deltaPoly_dvd_numer r)

theorem formNumer_unique {r : ℕ} {Q : Poly r} (h : numer r = deltaPoly r * Q) :
    formNumer r = Q :=
  mul_left_cancel₀ (deltaPoly_ne_zero r) ((numer_eq r).symm.trans h)

/-- **`P_r` is symmetric** in the grades. -/
theorem relabel_formNumer (τ : Perm (Fin r)) : relabel τ (formNumer r) = formNumer r := by
  have h := relabel_numer (r := r) τ
  rw [numer_eq, map_mul, relabel_deltaPoly, smul_mul_assoc] at h
  have hu : ∀ x y : Poly r, (Perm.sign τ : ℤ) • x = (Perm.sign τ : ℤ) • y → x = y :=
      fun x y hxy => by
    have := congrArg (fun w => (Perm.sign τ : ℤ) • w) hxy
    simpa [smul_smul, ← Units.val_mul, Int.units_mul_self] using this
  exact mul_left_cancel₀ (deltaPoly_ne_zero r) (hu _ _ h)

theorem totalDegree_phase_le (S : Finset (Fin r)) : (phase S).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le (totalDegree_X _).le ?_)
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => (totalDegree_X _).le)

theorem totalDegree_numer_le (r : ℕ) : (numer r).totalDegree ≤ 2 ^ r - 1 - r := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun π _ => ?_)
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  calc ∑ S ∈ subsets r \ chain π, (phase S).totalDegree ≤ ∑ _S ∈ subsets r \ chain π, 1 :=
        sum_le_sum fun S _ => totalDegree_phase_le S
    _ = 2 ^ r - 1 - r := by
        rw [sum_const, smul_eq_mul, mul_one, card_sdiff_of_subset (chain_subset π), card_subsets,
          card_chain]

theorem isHomogeneous_deltaPoly (r : ℕ) :
    (deltaPoly r).IsHomogeneous (∑ i : Fin r, (Ioi i).card) := by
  rw [deltaPoly, delta]
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  have := IsHomogeneous.prod (Ioi i) (fun j => (X (some i) - X (some j) : Poly r)) (fun _ => 1)
    fun j _ => (isHomogeneous_X ℚ _).sub (isHomogeneous_X ℚ _)
  simpa using this

theorem sum_card_Ioi_add (r : ℕ) : (∑ i : Fin r, (Ioi i).card) + r = r * (r + 1) / 2 := by
  have h1 : ∀ i : Fin r, (Ioi i).card = r - 1 - i := fun i => Fin.card_Ioi i
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i), sum_range_reflect (fun j => j) r,
    sum_range_id, ← Nat.choose_two_right, mul_comm]
  have h2 : (r + 1) * r / 2 = (r + 1).choose 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel]
  rw [h2, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

/-- **`(PGE.26)`: `deg P_r ≤ 2^r - 1 - r(r+1)/2`.** -/
theorem totalDegree_formNumer_le (r : ℕ) :
    (formNumer r).totalDegree ≤ 2 ^ r - 1 - r * (r + 1) / 2 := by
  by_cases hP : formNumer r = 0
  · rw [hP, totalDegree_zero]; exact Nat.zero_le _
  have h := totalDegree_numer_le r
  rw [numer_eq, totalDegree_mul_of_isDomain (deltaPoly_ne_zero r) hP,
    (isHomogeneous_deltaPoly r).totalDegree (deltaPoly_ne_zero r)] at h
  have := sum_card_Ioi_add r
  omega


/-! ### The evaluated factorization `(PGE.25)` -/

theorem aeval_deltaPoly (z : K) (lam : Fin r → K) :
    aeval (point z lam) (deltaPoly r) = delta lam := by
  simp [deltaPoly, delta, map_prod, map_sub, point]

theorem aeval_denom (z : K) (lam : Fin r → K) :
    aeval (point z lam) (denom r) = ∏ S ∈ subsets r, (z + ∑ i ∈ S, lam i) := by
  rw [denom, map_prod]
  exact prod_congr rfl fun S _ => aeval_phase z lam S

theorem aeval_denom_ne_zero (z : K) (lam : Fin r → K)
    (h : ∀ S ∈ subsets r, z + ∑ i ∈ S, lam i ≠ 0) : aeval (point z lam) (denom r) ≠ 0 := by
  rw [aeval_denom]
  exact prod_ne_zero_iff.2 h

/-- **`(PGE.25)`: `R_r(z;λ) = Δ_r(λ) P_r(z;λ) / D_r(z;λ)`.** -/
theorem alternant_eq (z : K) (lam : Fin r → K) (h : ∀ S ∈ subsets r, z + ∑ i ∈ S, lam i ≠ 0) :
    alternant z lam =
      delta lam * aeval (point z lam) (formNumer r) / aeval (point z lam) (denom r) := by
  rw [eq_div_iff (aeval_denom_ne_zero z lam h), mul_comm (alternant z lam),
    aeval_denom_mul_alternant z lam h, numer_eq, map_mul, aeval_deltaPoly]

theorem phase_ne_zero (S : Finset (Fin r)) : phase S ≠ 0 := by
  intro h
  have := congrArg (aeval (point (1 : ℚ) fun _ => 0)) h
  rw [aeval_phase, map_zero] at this
  simp at this

theorem denom_ne_zero (r : ℕ) : denom r ≠ 0 := prod_ne_zero_iff.2 fun S _ => phase_ne_zero S

/-- `P_r` is determined by the values of the alternant off the phase hyperplanes. -/
theorem formNumer_eq_of_eval {Q : Poly r}
    (hQ : ∀ (z : ℚ) (lam : Fin r → ℚ), (∀ S ∈ subsets r, z + ∑ i ∈ S, lam i ≠ 0) →
      alternant z lam * aeval (point z lam) (denom r) = delta lam * aeval (point z lam) Q) :
    formNumer r = Q := by
  refine formNumer_unique ?_
  have h : (numer r - deltaPoly r * Q) * denom r = 0 := by
    refine MvPolynomial.funext fun x => ?_
    have e : ∀ p : Poly r, eval x p = aeval x p := fun p => by rw [← coe_aeval_eq_eval]; rfl
    have hx : point (x none) (fun i => x (some i)) = x := funext fun o => by cases o <;> rfl
    rw [e, e, map_zero, ← hx]
    by_cases hS : ∀ S ∈ subsets r, x none + ∑ i ∈ S, x (some i) ≠ 0
    · rw [map_mul, map_sub, map_mul, aeval_deltaPoly, ← aeval_denom_mul_alternant _ _ hS,
        mul_comm (aeval _ (denom r)), hQ _ _ hS, sub_self, zero_mul]
    · push Not at hS
      obtain ⟨S, hS, h0⟩ := hS
      rw [map_mul, aeval_denom, prod_eq_zero hS h0, mul_zero]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (denom_ne_zero r))

/-! ### The first formation numerators `(PGE.27)` -/

theorem subsets_one : subsets 1 = {{0}} := by decide

theorem subsets_two : subsets 2 = {{0}, {1}, {0, 1}} := by decide

theorem subsets_three :
    subsets 3 = {{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide

/-- `P_1 = 1`. -/
theorem formNumer_one : formNumer 1 = 1 := by
  refine formNumer_eq_of_eval fun z lam h => ?_
  have h0 : z + lam 0 ≠ 0 := by simpa [subsets_one] using h
  rw [alternant, aeval_denom, subsets_one, Fintype.sum_unique, prod_singleton, sum_singleton]
  simp [delta, suffixSum, show Ici (0 : Fin 1) = univ by decide]
  field_simp

/-- `P_2 = 1`. -/
theorem formNumer_two : formNumer 2 = 1 := by
  refine formNumer_eq_of_eval fun z lam h => ?_
  simp only [subsets_two, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
    sum_singleton] at h
  obtain ⟨h0, h1, h01⟩ := h
  rw [sum_pair (by decide)] at h01
  let M : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of fun j k => ![1, (z + lam j)⁻¹] k
  have hprod : ∀ π : Perm (Fin 2), (Perm.sign π : ℤ) • ∏ k : Fin 2, (z + suffixSum lam π k)⁻¹ =
      (z + (lam 0 + lam 1))⁻¹ * (Perm.sign π • ∏ k : Fin 2, M (π k) k) := fun π => by
    have hA : lam (π 0) + lam (π 1) = lam 0 + lam 1 := by
      have := Equiv.sum_comp π lam
      simpa [Fin.sum_univ_two] using this
    have s0 : suffixSum lam π 0 = lam 0 + lam 1 := by
      rw [suffixSum, show Ici (0 : Fin 2) = univ by decide, Fin.sum_univ_two, hA]
    have s1 : suffixSum lam π 1 = lam (π 1) := by
      rw [suffixSum, show Ici (1 : Fin 2) = {1} by decide, sum_singleton]
    rw [Units.smul_def, mul_smul_comm, Fin.prod_univ_two, Fin.prod_univ_two, s0, s1]
    simp [M]
  rw [alternant, sum_congr rfl fun π _ => hprod π, ← mul_sum, ← Matrix.det_apply,
    Matrix.det_fin_two]
  simp [M, aeval_denom, subsets_two, delta, show Ioi (0 : Fin 2) = {1} by decide,
    show Ioi (1 : Fin 2) = ∅ by decide]
  rw [prod_insert (by decide), prod_insert (by decide), prod_singleton, sum_singleton,
    sum_singleton, sum_pair (by decide)]
  field_simp
  ring

/-- `P_3 = 2z + λ_1 + λ_2 + λ_3` `(PGE.27)`; equivalently Theorem 3.1. -/
theorem formNumer_three :
    formNumer 3 = 2 * X none + (X (some 0) + X (some 1) + X (some 2)) := by
  refine formNumer_eq_of_eval fun z lam h => ?_
  simp only [subsets_three, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
    sum_singleton] at h
  obtain ⟨h0, h1, h2, h01, h02, h12, h012⟩ := h
  rw [sum_pair (by decide)] at h01 h02 h12
  rw [sum_insert (by decide), sum_pair (by decide)] at h012
  let A : ℚ := lam 0 + (lam 1 + lam 2)
  let M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun j k => ![(z + A - lam j)⁻¹, 1, (z + lam j)⁻¹] k
  have hprod : ∀ π : Perm (Fin 3), (Perm.sign π : ℤ) • ∏ k : Fin 3, (z + suffixSum lam π k)⁻¹ =
      (z + A)⁻¹ * (Perm.sign π • ∏ k : Fin 3, M (π k) k) := fun π => by
    have hA : lam (π 0) + lam (π 1) + lam (π 2) = A := by
      have := Equiv.sum_comp π lam
      simp only [Fin.sum_univ_three] at this
      rw [this]; ring
    have s0 : suffixSum lam π 0 = A := by
      rw [suffixSum, show Ici (0 : Fin 3) = univ by decide, Fin.sum_univ_three, hA]
    have s1 : suffixSum lam π 1 = A - lam (π 0) := by
      rw [suffixSum, show Ici (1 : Fin 3) = {1, 2} by decide, sum_pair (by decide), ← hA]
      ring
    have s2 : suffixSum lam π 2 = lam (π 2) := by
      rw [suffixSum, show Ici (2 : Fin 3) = {2} by decide, sum_singleton]
    rw [Units.smul_def, mul_smul_comm, Fin.prod_univ_three, Fin.prod_univ_three, s0, s1, s2]
    simp only [M, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    congr 1
    rw [add_sub_assoc]
    ring
  rw [alternant, sum_congr rfl fun π _ => hprod π, ← mul_sum, ← Matrix.det_apply,
    Matrix.det_fin_three]
  simp only [M, A, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, aeval_denom, subsets_three, delta,
    show Ioi (0 : Fin 3) = {1, 2} by decide, show Ioi (1 : Fin 3) = {2} by decide,
    show Ioi (2 : Fin 3) = ∅ by decide, Fin.prod_univ_three]
  have e0 : z + (lam 0 + (lam 1 + lam 2)) - lam 0 = z + (lam 1 + lam 2) := by ring
  have e1 : z + (lam 0 + (lam 1 + lam 2)) - lam 1 = z + (lam 0 + lam 2) := by ring
  have e2 : z + (lam 0 + (lam 1 + lam 2)) - lam 2 = z + (lam 0 + lam 1) := by ring
  rw [e0, e1, e2]
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton,
    sum_singleton, sum_singleton, sum_singleton, sum_pair (by decide), sum_pair (by decide),
    sum_pair (by decide), sum_insert (by decide), sum_pair (by decide)]
  simp only [map_add, map_mul, map_ofNat, aeval_X, point, Option.elim_none, Option.elim_some,
    prod_empty, mul_one, prod_singleton, prod_pair (show (1 : Fin 3) ≠ 2 by decide)]
  field_simp
  ring

end Permutohedral

end

end GaloisForLFunctions.HTGeometry
