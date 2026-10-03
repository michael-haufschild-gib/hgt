import GaloisForLFunctions.HTGeometry.SparsePolynomialRootMultiplicity
import GaloisForLFunctions.RHTower.StepanovCount

/-!
# Stepanov's method for a shifted multiplicative coset

For `x` with `xᵗ = α` and `(x − μ)ᵗ = β` (a point of `ξH ∩ (ξ'H + μ)` for the subgroup `H` of order
`t`), the auxiliary polynomial

`Ψ = Σ_{a<D, b,c<B} λ_{abc} X^{a+tb} (X − μ)^{tc}`

satisfies `x^n (x−μ)^n D^{(n)}Ψ(x) = Σ λ_{abc} α^b β^c T_{abcn}(x)` with `deg T_{abcn} ≤ a + n`
(`hasseDeriv_stepMono_eval`), so `D + n` linear conditions per order `n` make `Ψ` vanish to order
`M` on the whole set.  The monomials are linearly independent when `DB ≤ t` and `tB ≤ p`
(`auxPoly_eq_zero`): grouping by `c`, the lowest nonzero group would be a polynomial with at most
`DB ≤ t` terms divisible by `(X − μ)ᵗ`, impossible by the sparse root-multiplicity lemma.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry.ShiftedSubgroup

open SparsePolynomial

variable {K : Type*} [Field K]

/-! ### The auxiliary polynomial and its independence -/

/-- The `c`-th group `Σ_{a<D, b<B} λ_{abc} X^{a+tb}`. -/
noncomputable def block (t D B : ℕ) (lam : Fin D × Fin B × Fin B → K) (c : Fin B) : K[X] :=
  ∑ b : Fin B, ∑ a : Fin D, C (lam (a, b, c)) * X ^ ((a : ℕ) + t * b)

/-- Stepanov's auxiliary polynomial `Σ_c block_c · (X − μ)^{tc}`. -/
noncomputable def auxPoly (t D B : ℕ) (μ : K) (lam : Fin D × Fin B × Fin B → K) : K[X] :=
  ∑ c : Fin B, block t D B lam c * (X - C μ) ^ (t * c)

theorem block_coeff {t D B : ℕ} (hDt : D ≤ t) (lam : Fin D × Fin B × Fin B → K) (c : Fin B)
    (a : Fin D) (b : Fin B) : (block t D B lam c).coeff ((a : ℕ) + t * b) = lam (a, b, c) := by
  have hinj : ∀ (a' : Fin D) (b' : Fin B),
      (a' : ℕ) + t * b' = (a : ℕ) + t * b → a' = a ∧ b' = b := by
    intro a' b' h
    have ha : (a : ℕ) < t := lt_of_lt_of_le a.isLt hDt
    have ha' : (a' : ℕ) < t := lt_of_lt_of_le a'.isLt hDt
    have h1 : ((a' : ℕ) + t * b') % t = ((a : ℕ) + t * b) % t := by rw [h]
    have h2 : ((a' : ℕ) + t * b') / t = ((a : ℕ) + t * b) / t := by rw [h]
    have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) ha
    rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt ha'] at h1
    rw [Nat.add_mul_div_left _ _ ht, Nat.add_mul_div_left _ _ ht, Nat.div_eq_of_lt ha,
      Nat.div_eq_of_lt ha'] at h2
    exact ⟨Fin.ext h1, Fin.ext (by omega)⟩
  unfold block
  rw [finsetSum_coeff, Finset.sum_eq_single b]
  · rw [finsetSum_coeff, Finset.sum_eq_single a]
    · rw [coeff_C_mul_X_pow, if_pos rfl]
    · intro a' _ ha'
      rw [coeff_C_mul_X_pow, if_neg]
      intro h; exact ha' (hinj a' b h.symm).1
    · simp
  · intro b' _ hb'
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun a' _ => ?_
    rw [coeff_C_mul_X_pow, if_neg]
    intro h; exact hb' (hinj a' b' h.symm).2
  · simp

theorem block_support_card_le (t D B : ℕ) (lam : Fin D × Fin B × Fin B → K) (c : Fin B) :
    (block t D B lam c).support.card ≤ D * B := by
  classical
  have hsub : (block t D B lam c).support ⊆
      (univ : Finset (Fin D × Fin B)).image (fun ab => (ab.1 : ℕ) + t * ab.2) := by
    intro n hn
    rw [mem_support_iff] at hn
    unfold block at hn
    rw [finsetSum_coeff] at hn
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    rw [finsetSum_coeff] at hb
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    rw [coeff_C_mul_X_pow] at ha
    split_ifs at ha with h
    · exact mem_image.mpr ⟨(a, b), mem_univ _, h.symm⟩
    · exact absurd rfl ha
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp

theorem block_natDegree_le {t D B : ℕ} (hD : 0 < D) (hB : 0 < B) (lam : Fin D × Fin B × Fin B → K)
    (c : Fin B) : (block t D B lam c).natDegree ≤ (D - 1) + t * (B - 1) := by
  unfold block
  refine natDegree_sum_le_of_forall_le _ _ fun b _ =>
    natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have ha := a.isLt; have hb := b.isLt
  have : t * (b : ℕ) ≤ t * (B - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **Independence of Stepanov's monomials.**  If `μ ≠ 0`, `DB ≤ t` and `tB ≤ p` (characteristic
`p`), the polynomials `X^{a+tb}(X − μ)^{tc}`, `a < D`, `b, c < B`, are linearly independent. -/
theorem auxPoly_eq_zero {p : ℕ} [CharP K p] {μ : K} (hμ : μ ≠ 0) {t D B : ℕ} (hDB : D * B ≤ t)
    (htB : t * B ≤ p) (lam : Fin D × Fin B × Fin B → K) (h : auxPoly t D B μ lam = 0) :
    lam = 0 := by
  classical
  by_contra hne
  obtain ⟨⟨a, b, c⟩, habc⟩ : ∃ i, lam i ≠ 0 := by
    by_contra hall; push Not at hall; exact hne (funext hall)
  have hD : 0 < D := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) b.isLt
  have hDt : D ≤ t := le_trans (Nat.le_mul_of_pos_right _ hB) hDB
  have hblock : ∀ c', block t D B lam c' = 0 → ∀ a' b', lam (a', b', c') = 0 := by
    intro c' h0 a' b'
    rw [← block_coeff hDt lam c' a' b', h0, coeff_zero]
  -- the lowest nonzero group
  set T := (univ : Finset (Fin B)).filter (fun c' => block t D B lam c' ≠ 0)
  have hT : T.Nonempty := ⟨c, mem_filter.mpr ⟨mem_univ _, fun h0 => habc (hblock c h0 a b)⟩⟩
  set c₀ := T.min' hT
  have hc₀ : block t D B lam c₀ ≠ 0 := (mem_filter.mp (T.min'_mem hT)).2
  have hlow : ∀ c', c' < c₀ → block t D B lam c' = 0 := by
    intro c' hc'
    by_contra h0
    exact absurd (T.min'_le c' (mem_filter.mpr ⟨mem_univ _, h0⟩)) (not_le.mpr hc')
  -- `(X − μ)^t` divides the lowest group
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
  have hdeg : (block t D B lam c₀).natDegree < p := by
    have := block_natDegree_le (t := t) hD hB lam c₀
    have : t * (B - 1) + t = t * B := by
      rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hB]
    omega
  exact not_pow_dvd_of_card_support_le hμ t hc₀ hdeg
    ((block_support_card_le t D B lam c₀).trans hDB) hdvd'

/-! ### Hasse derivatives on the coset intersection -/

/-- `T_{abcn} = X^a Σ_{i+j=n} C(a+tb, i) C(tc, j) X^j (X − μ)^i`. -/
noncomputable def stepT (t : ℕ) (μ : K) (a b c n : ℕ) : K[X] :=
  X ^ a * ∑ ij ∈ antidiagonal n,
    C (((a + t * b).choose ij.1 : K) * ((t * c).choose ij.2 : K)) * X ^ ij.2 * (X - C μ) ^ ij.1

theorem stepT_natDegree_le (t : ℕ) (μ : K) (a b c n : ℕ) :
    (stepT t μ a b c n).natDegree ≤ a + n := by
  unfold stepT
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  refine Nat.add_le_add_left (natDegree_sum_le_of_forall_le _ _ fun ij hij => ?_) _
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  refine natDegree_mul_le.trans ?_
  refine Nat.le_trans (Nat.add_le_add_right (natDegree_C_mul_X_pow_le _ _) _) ?_
  rw [natDegree_pow, natDegree_X_sub_C]
  omega

/-- **The Hasse derivatives of a Stepanov monomial.**
`D^{(n)}[X^{a+tb}(X−μ)^{tc}](x) · xⁿ(x−μ)ⁿ = (xᵗ)^b ((x−μ)ᵗ)^c T_{abcn}(x)`. -/
theorem hasseDeriv_stepMono_eval (t : ℕ) (μ x : K) (a b c n : ℕ) :
    (hasseDeriv n (X ^ (a + t * b) * (X - C μ) ^ (t * c))).eval x * (x ^ n * (x - μ) ^ n) =
      (x ^ t) ^ b * ((x - μ) ^ t) ^ c * (stepT t μ a b c n).eval x := by
  rw [← taylor_coeff, taylor_mul, taylor_pow, taylor_pow, taylor_X, map_sub, taylor_X, taylor_C,
    show X + C x - C μ = X + C (x - μ) by rw [C_sub]; ring, coeff_mul, sum_mul]
  unfold stepT
  simp only [eval_mul, eval_pow, eval_X, eval_finsetSum, eval_C, eval_sub, mul_sum]
  refine sum_congr rfl fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [coeff_X_add_C_pow, coeff_X_add_C_pow]
  by_cases hi : ij.1 ≤ a + t * b
  · by_cases hj : ij.2 ≤ t * c
    · have e1 : x ^ (a + t * b - ij.1) * x ^ n = x ^ a * (x ^ t) ^ b * x ^ ij.2 := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← pow_add, ← hij]; congr 1; omega
      have e2 : (x - μ) ^ (t * c - ij.2) * (x - μ) ^ n = ((x - μ) ^ t) ^ c * (x - μ) ^ ij.1 := by
        rw [← pow_mul, ← pow_add, ← pow_add, ← hij]; congr 1; omega
      linear_combination
        (((a + t * b).choose ij.1 : K) * ((t * c).choose ij.2 : K)) *
          ((x - μ) ^ (t * c - ij.2) * (x - μ) ^ n * e1 +
            x ^ a * (x ^ t) ^ b * x ^ ij.2 * e2)
    · rw [Nat.choose_eq_zero_of_lt (by omega : t * c < ij.2)]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : a + t * b < ij.1)]; simp

/-! ### Stepanov's count -/

/-- The auxiliary polynomial as a single sum over the index box. -/
theorem auxPoly_eq_sum (t D B : ℕ) (μ : K) (lam : Fin D × Fin B × Fin B → K) :
    auxPoly t D B μ lam = ∑ i : Fin D × Fin B × Fin B,
      C (lam i) * (X ^ ((i.1 : ℕ) + t * i.2.1) * (X - C μ) ^ (t * i.2.2)) := by
  set g : Fin D → Fin B → Fin B → K[X] := fun a b c =>
    C (lam (a, b, c)) * (X ^ ((a : ℕ) + t * b) * (X - C μ) ^ (t * c))
  calc auxPoly t D B μ lam = ∑ c : Fin B, ∑ b : Fin B, ∑ a : Fin D, g a b c := by
        unfold auxPoly block
        refine sum_congr rfl fun c _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun a _ => by simp only [g]; ring
    _ = ∑ b : Fin B, ∑ c : Fin B, ∑ a : Fin D, g a b c := Finset.sum_comm
    _ = ∑ b : Fin B, ∑ a : Fin D, ∑ c : Fin B, g a b c :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a : Fin D, ∑ b : Fin B, ∑ c : Fin B, g a b c := Finset.sum_comm
    _ = _ := by simp only [Fintype.sum_prod_type, g]

theorem auxPoly_natDegree_le {t D B : ℕ} (hD : 0 < D) (hB : 0 < B) (μ : K)
    (lam : Fin D × Fin B × Fin B → K) :
    (auxPoly t D B μ lam).natDegree ≤ (D - 1) + t * (B - 1) + t * (B - 1) := by
  unfold auxPoly
  refine natDegree_sum_le_of_forall_le _ _ fun c _ => natDegree_mul_le.trans ?_
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]
  have := block_natDegree_le (t := t) hD hB lam c
  have : t * (c : ℕ) ≤ t * (B - 1) := Nat.mul_le_mul_left _ (by have := c.isLt; omega)
  omega

/-- The condition polynomial of order `n`: `Σ λ_{abc} α^b β^c T_{abcn}`. -/
noncomputable def condPoly (t D B : ℕ) (μ α β : K) (lam : Fin D × Fin B × Fin B → K) (n : ℕ) :
    K[X] :=
  ∑ i : Fin D × Fin B × Fin B,
    C (lam i * α ^ (i.2.1 : ℕ) * β ^ (i.2.2 : ℕ)) * stepT t μ i.1 i.2.1 i.2.2 n

theorem condPoly_natDegree_le {t D B : ℕ} (hD : 0 < D) (μ α β : K)
    (lam : Fin D × Fin B × Fin B → K) (n : ℕ) :
    (condPoly t D B μ α β lam n).natDegree ≤ (D - 1) + n := by
  unfold condPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_C_mul_le _ _).trans ?_
  have := stepT_natDegree_le t μ i.1 i.2.1 i.2.2 n
  have := i.1.isLt
  omega

/-- **Stepanov's count for a shifted coset.**  Let `μ ≠ 0` and let `S` consist of points
`x ∉ {0, μ}` with `xᵗ = α`, `(x − μ)ᵗ = β`.  If `DB ≤ t`, `tB ≤ p` and `Σ_{n<M}(D + n) < DB²`, then
`M · |S| ≤ (D − 1) + 2t(B − 1)`. -/
theorem stepanov_shifted_count {p : ℕ} [CharP K p] {μ : K} (hμ : μ ≠ 0) {t D B M : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hDB : D * B ≤ t) (htB : t * B ≤ p)
    (hdim : ∑ n ∈ range M, (D + n) < D * (B * B)) (α β : K) (S : Finset K)
    (hS : ∀ x ∈ S, x ≠ 0 ∧ x ≠ μ ∧ x ^ t = α ∧ (x - μ) ^ t = β) :
    M * S.card ≤ (D - 1) + t * (B - 1) + t * (B - 1) := by
  classical
  set ι := Fin D × Fin B × Fin B
  -- 1. the linear system
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
  -- 2. the condition polynomials vanish
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
  -- 3. the auxiliary polynomial is nonzero
  set Ψ := auxPoly t D B μ lam
  have hΨ : Ψ ≠ 0 := fun h0 => hlam0 (auxPoly_eq_zero hμ hDB htB lam h0)
  -- 4. every point of `S` is a root of multiplicity `M`
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
  -- 5. counting degrees
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

/-- **Heath-Brown–Konyagin bound for a shifted coset.**  Let `μ ≠ 0` and let `S` consist of points
`x ∉ {0, μ}` with `xᵗ = α`, `(x − μ)ᵗ = β`.  For every `B ≥ 1` with `3t ≤ 2B³`, `2B ≤ t` and
`tB ≤ p`, `|S| < 4B²`; with `B ≈ (2t)^{1/3}` this is `|S| ≪ t^{2/3}` for `t ≪ p^{3/4}`. -/
theorem card_shifted_lt {p : ℕ} [CharP K p] {μ : K} (hμ : μ ≠ 0) {t B : ℕ} (hB : 0 < B)
    (hB3 : 3 * t ≤ 2 * B ^ 3) (h2B : 2 * B ≤ t) (htB : t * B ≤ p) (α β : K) (S : Finset K)
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
  have hcount := stepanov_shifted_count hμ (by omega) hB hDB htB hdim α β S hS
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
