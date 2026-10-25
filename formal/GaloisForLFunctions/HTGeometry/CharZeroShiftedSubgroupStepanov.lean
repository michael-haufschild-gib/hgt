import GaloisForLFunctions.HTGeometry.ShiftedSubgroupStepanov

/-!
# Unbounded-degree sparse root multiplicity and shifted-subgroup Stepanov in characteristic zero

`SparsePolynomialRootMultiplicity` and `ShiftedSubgroupStepanov` worked over a field of positive
characteristic `p` under the degree caps `f.natDegree < p` and `t B ≤ p`. Over a characteristic-zero
field (`[Field K] [CharZero K]`), the Euler derivation `f ↦ X f′ − e₀ f` multiplies the `n`-th
coefficient by `(n : K) − (e₀ : K)`, which is nonzero for every `n ≠ e₀` without any upper bound on
`n`.

Consequently, over every characteristic-zero field `K` (`ℚ`, `ℝ`, `ℂ`, `ℚ_p`):
* **Unbounded-degree sparse root-multiplicity bound** (`not_pow_dvd_of_card_support_le_charZero`,
  `rootMultiplicity_lt_card_support_of_ne_zero`): every nonzero polynomial `f ∈ K[X]` of arbitrary
  degree satisfies `f.rootMultiplicity r < #f.support` at every nonzero `r ∈ K`.
* **Characteristic-zero shifted-subgroup Stepanov** (`stepanov_shifted_count_charZero`,
  `card_shifted_lt_charZero`): for arbitrary `t, B ≥ 1` with `3t ≤ 2B³` and `2B ≤ t` and any nonzero
  shift `μ ∈ K`, any subset `S` of `{x ∉ {0, μ} | xᵗ = α ∧ (x − μ)ᵗ = β}` (such as the intersection
  `μ_t ∩ (μ_t + μ)` of shifted finite subgroups of roots of unity in `ℂˣ` of arbitrarily large order
  `t`) satisfies `#S < 4 B²` (`≪ t^{2/3}`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry.ShiftedSubgroup

open SparsePolynomial

variable {K : Type*} [Field K] [CharZero K]

/-! ### Unbounded-degree sparse root multiplicity in characteristic zero -/

/-- **Unbounded-degree sparse root-multiplicity obstruction in characteristic zero.**
Over a characteristic-zero field, a nonzero polynomial of arbitrary degree with at most `m` nonzero
terms is never divisible by `(X − r)^m` for `r ≠ 0`. -/
theorem not_pow_dvd_of_card_support_le_charZero {r : K} (hr : r ≠ 0) :
    ∀ (m : ℕ) {f : K[X]}, f ≠ 0 → f.support.card ≤ m → ¬ (X - C r) ^ m ∣ f := by
  intro m
  induction m with
  | zero =>
    intro f hf hm
    exact absurd (card_eq_zero.mp (Nat.le_zero.mp hm)) (by simpa using hf)
  | succ m ih =>
    intro f hf hm hdvd
    set e₀ := f.natTrailingDegree
    have he₀ : f.coeff e₀ ≠ 0 := by
      rw [show f.coeff e₀ = f.trailingCoeff from rfl]
      exact trailingCoeff_nonzero_iff_nonzero.mpr hf
    set g := euler e₀ f
    have hsupp : g.support ⊆ f.support.erase e₀ := by
      intro n hn
      rw [mem_support_iff, coeff_euler] at hn
      refine mem_erase.mpr ⟨fun h => hn (by rw [h]; ring), ?_⟩
      rw [mem_support_iff]
      intro h0
      exact hn (by rw [h0, zero_mul])
    have hcard : g.support.card ≤ m := by
      have := card_le_card hsupp
      rw [card_erase_of_mem (mem_support_iff.mpr he₀)] at this
      omega
    by_cases hg : g = 0
    · have hmono : f = C (f.coeff e₀) * X ^ e₀ := by
        ext n
        rw [coeff_C_mul_X_pow]
        split_ifs with hn
        · rw [hn]
        · by_contra hne
          have h1 : g.coeff n = 0 := by rw [hg, coeff_zero]
          rw [show g = euler e₀ f from rfl, coeff_euler] at h1
          have hne0 : (n : K) - (e₀ : K) ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hn)
          exact hne ((mul_eq_zero.mp h1).resolve_right hne0)
      have hroot : (X - C r) ∣ f := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hdvd
      rw [dvd_iff_isRoot, IsRoot, hmono] at hroot
      simp only [eval_mul, eval_C, eval_pow, eval_X] at hroot
      exact he₀ ((mul_eq_zero.mp hroot).resolve_right (pow_ne_zero _ hr))
    · exact ih hg hcard (pow_dvd_euler e₀ hdvd)

/-- **Hajós–Euler sparse root-multiplicity bound.** Over a characteristic-zero field, the
multiplicity of any nonzero root `r` of a nonzero polynomial `f` is strictly smaller than the number
of nonzero monomials `#f.support`, regardless of `deg f`. -/
theorem rootMultiplicity_lt_card_support_of_ne_zero {r : K} (hr : r ≠ 0) {f : K[X]} (hf : f ≠ 0) :
    f.rootMultiplicity r < f.support.card := by
  by_contra hge
  have hle : f.support.card ≤ f.rootMultiplicity r := not_lt.mp hge
  exact not_pow_dvd_of_card_support_le_charZero hr (f.rootMultiplicity r) hf hle
    (pow_rootMultiplicity_dvd f r)

/-! ### Characteristic-zero shifted-subgroup Stepanov -/

/-- **Linear independence of Stepanov's monomials in characteristic zero.**
For `μ ≠ 0` and `D B ≤ t` (with no upper bound on `t B`), the polynomials `X^{a+tb}(X − μ)^{tc}`
(`a < D`, `b, c < B`) are linearly independent over `K`. -/
theorem auxPoly_eq_zero_charZero {μ : K} (hμ : μ ≠ 0) {t D B : ℕ} (hDB : D * B ≤ t)
    (lam : Fin D × Fin B × Fin B → K) (h : auxPoly t D B μ lam = 0) :
    lam = 0 := by
  classical
  by_contra hne
  obtain ⟨⟨a, b, c⟩, habc⟩ : ∃ i, lam i ≠ 0 := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) b.isLt
  have hDt : D ≤ t := le_trans (Nat.le_mul_of_pos_right _ hB) hDB
  have hblock : ∀ c', block t D B lam c' = 0 → ∀ a' b', lam (a', b', c') = 0 := by
    intro c' h0 a' b'
    rw [← block_coeff hDt lam c' a' b', h0, coeff_zero]
  set T := (univ : Finset (Fin B)).filter (fun c' => block t D B lam c' ≠ 0)
  have hT : T.Nonempty := ⟨c, mem_filter.mpr ⟨mem_univ _, fun h0 => habc (hblock c h0 a b)⟩⟩
  set c₀ := T.min' hT
  have hc₀ : block t D B lam c₀ ≠ 0 := (mem_filter.mp (T.min'_mem hT)).2
  have hlow : ∀ c', c' < c₀ → block t D B lam c' = 0 := by
    intro c' hc'
    by_contra h0
    exact absurd (T.min'_le c' (mem_filter.mpr ⟨mem_univ _, h0⟩)) (not_le.mpr hc')
  have hrel : block t D B lam c₀ * (X - C μ) ^ (t * c₀) =
      -∑ c' ∈ univ.erase c₀, block t D B lam c' * (X - C μ) ^ (t * c') := by
    have := h
    unfold auxPoly at this
    rw [← Finset.add_sum_erase _ _ (mem_univ c₀)] at this
    exact eq_neg_of_add_eq_zero_left this
  have hdvd : (X - C μ) ^ (t * c₀) * (X - C μ) ^ t ∣
      (X - C μ) ^ (t * c₀) * block t D B lam c₀ := by
    rw [mul_comm ((X - C μ) ^ (t * c₀)) (block _ _ _ _ _), hrel, ← pow_add]
    refine dvd_neg.mpr (Finset.dvd_sum fun c' hc' => ?_)
    rcases lt_or_gt_of_ne (ne_of_mem_erase hc') with hlt | hgt
    · rw [hlow c' hlt, zero_mul]; exact dvd_zero _
    · refine dvd_mul_of_dvd_right (pow_dvd_pow _ ?_) _
      have : (c₀ : ℕ) + 1 ≤ c' := hgt
      nlinarith
  have hdvd' : (X - C μ) ^ t ∣ block t D B lam c₀ :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ (X_sub_C_ne_zero μ))).mp hdvd
  exact not_pow_dvd_of_card_support_le_charZero hμ t hc₀
    ((block_support_card_le t D B lam c₀).trans hDB) hdvd'

/-- **Stepanov's shifted-coset count in characteristic zero.**
For `μ ≠ 0`, `D B ≤ t`, and `Σ_{n<M}(D + n) < D B²` (with no characteristic restriction), any finite
set `S ⊆ {x ∉ {0, μ} | xᵗ = α ∧ (x − μ)ᵗ = β}` satisfies `M · #S ≤ (D − 1) + 2t(B − 1)`. -/
theorem stepanov_shifted_count_charZero {μ : K} (hμ : μ ≠ 0) {t D B M : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hDB : D * B ≤ t)
    (hdim : ∑ n ∈ range M, (D + n) < D * (B * B)) (α β : K) (S : Finset K)
    (hS : ∀ x ∈ S, x ≠ 0 ∧ x ≠ μ ∧ x ^ t = α ∧ (x - μ) ^ t = β) :
    M * S.card ≤ (D - 1) + t * (B - 1) + t * (B - 1) := by
  classical
  set ι := Fin D × Fin B × Fin B
  let W : Matrix (Σ n : Fin M, Fin (D + n)) ι K := fun nk i =>
    (C (α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ)) * stepT t μ i.1 i.2.1 i.2.2 nk.1).coeff nk.2
  have hrank : Module.finrank K ((Σ n : Fin M, Fin (D + n)) → K) < Module.finrank K (ι → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sigma]
    simp only [Fintype.card_fin, Fintype.card_prod, ι]
    rw [Fin.sum_univ_eq_sum_range (fun n => D + n)]
    exact hdim
  obtain ⟨lam, hlamK, hlam0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := W.mulVecLin) hrank)
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hlamK
  have hcond : ∀ n < M, condPoly t D B μ α β lam n = 0 := by
    intro n hn
    ext k
    rw [coeff_zero]
    by_cases hk : k < D + n
    · have := congrFun hlamK ⟨⟨n, hn⟩, ⟨k, hk⟩⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, W] at this
      rw [← this]
      unfold condPoly
      rw [finsetSum_coeff]
      refine sum_congr rfl fun i _ => ?_
      rw [show lam i * α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ) =
        lam i * (α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ)) by ring, C_mul, mul_assoc, coeff_C_mul,
        mul_comm]
    · exact coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (condPoly_natDegree_le hD μ α β lam n) (by omega))
  set Ψ := auxPoly t D B μ lam
  have hΨ : Ψ ≠ 0 := fun h0 => hlam0 (auxPoly_eq_zero_charZero hμ hDB lam h0)
  have hroot : ∀ x ∈ S, (X - C x) ^ M ∣ Ψ := by
    intro x hx
    obtain ⟨hx0, hxμ, hxα, hxβ⟩ := hS x hx
    refine RHTower.Stepanov.pow_dvd_of_hasseDeriv_eval_eq_zero fun n hn => ?_
    have hfac : x ^ n * (x - μ) ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ (sub_ne_zero.mpr hxμ))
    have hid : (hasseDeriv n Ψ).eval x * (x ^ n * (x - μ) ^ n) =
        (condPoly t D B μ α β lam n).eval x := by
      rw [show Ψ = auxPoly t D B μ lam from rfl, auxPoly_eq_sum, map_sum (hasseDeriv n),
        eval_finsetSum, sum_mul]
      unfold condPoly
      rw [eval_finsetSum]
      refine sum_congr rfl fun i _ => ?_
      rw [← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul, mul_assoc,
        hasseDeriv_stepMono_eval, hxα, hxβ, eval_mul, eval_C]
      ring
    rw [hcond n hn, eval_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_right hfac
  have hprod : (∏ x ∈ S, (X - C x) ^ M) ∣ Ψ := by
    apply Finset.prod_dvd_of_coprime
    · intro x _ y _ hxy
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hxy).isUnit).pow
    · exact hroot
  have hdegprod : (∏ x ∈ S, (X - C x) ^ M : K[X]).natDegree = M * S.card := by
    rw [natDegree_prod _ _ (fun x _ => pow_ne_zero _ (X_sub_C_ne_zero x))]
    simp [natDegree_pow, mul_comm]
  have hle := natDegree_le_of_dvd hprod hΨ
  rw [hdegprod] at hle
  exact hle.trans (auxPoly_natDegree_le hD hB μ lam)

/-- **Sub-linear `O(t^{2/3})` intersection bound for shifted finite subgroups / cosets in
characteristic zero.** For any `μ ≠ 0`, `B ≥ 1` with `3t ≤ 2B³` and `2B ≤ t` (arbitrarily large `t`),
every finite subset `S ⊆ {x ∉ {0, μ} | xᵗ = α ∧ (x − μ)ᵗ = β}` has `#S < 4 B²`. -/
theorem card_shifted_lt_charZero {μ : K} (hμ : μ ≠ 0) {t B : ℕ} (hB : 0 < B)
    (hB3 : 3 * t ≤ 2 * B ^ 3) (h2B : 2 * B ≤ t) (α β : K) (S : Finset K)
    (hS : ∀ x ∈ S, x ≠ 0 ∧ x ≠ μ ∧ x ^ t = α ∧ (x - μ) ^ t = β) :
    S.card < 4 * B ^ 2 := by
  set D := t / B with hDdef
  have hD2 : 2 ≤ D := (Nat.le_div_iff_mul_le hB).mpr (by linarith)
  have hDB : D * B ≤ t := Nat.div_mul_le_self t B
  have htlt : t < (D + 1) * B := by
    calc t < t / B * B + B := Nat.lt_div_mul_add hB
      _ = (D + 1) * B := by rw [hDdef]; ring
  have hdim : ∑ n ∈ range D, (D + n) < D * (B * B) := by
    have hsum : ∑ n ∈ range D, (D + n) * 2 = 2 * D * D + D * (D - 1) := by
      rw [← sum_mul, sum_add_distrib, sum_const, card_range, smul_eq_mul, add_mul,
        Finset.sum_range_id_mul_two]; ring
    have h3 : 3 * D ≤ 2 * (B * B) := by
      have : 3 * D * B ≤ 2 * (B * B) * B := by
        calc 3 * D * B = 3 * (D * B) := by ring
          _ ≤ 3 * t := Nat.mul_le_mul_left _ hDB
          _ ≤ 2 * B ^ 3 := hB3
          _ = 2 * (B * B) * B := by ring
      exact Nat.le_of_mul_le_mul_right this hB
    have : (∑ n ∈ range D, (D + n)) * 2 < D * (B * B) * 2 := by
      rw [sum_mul, hsum]
      obtain ⟨D', hD'⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      rw [hD', Nat.add_sub_cancel]
      rw [hD'] at h3
      nlinarith
    omega
  have hcount := stepanov_shifted_count_charZero hμ (by omega) hB hDB hdim α β S hS
  obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hcount
  have key : (t + 1) * (2 * B') ≤ (D + 1) * (B' + 1) * (2 * B') := Nat.mul_le_mul_right _ htlt
  have hDB2 : 2 * B' ^ 2 ≤ D * B' ^ 2 := Nat.mul_le_mul_right _ hD2
  have hlt : D * S.card < D * (4 * (B' + 1) ^ 2) := by
    refine lt_of_le_of_lt hcount ?_
    have : D - 1 ≤ D := Nat.sub_le _ _
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left hlt

end GaloisForLFunctions.HTGeometry.ShiftedSubgroup
