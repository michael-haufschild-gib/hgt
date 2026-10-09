import GaloisForLFunctions.RHTower.ComplexFugacityLeeYangChain
import GaloisForLFunctions.RHTower.LeeYangRestrictionZeroCount

/-!
# Complex-fugacity chains are Lee–Yang data

The chain of `ComplexFugacityLeeYangChain` on the sites `0, …, N`, with complex wall fugacities
`α k` in the closed unit disc, is a polynomial in the fields `u_0, …, u_N`.

* `cChainPoly`: the chain polynomial over `Fin (N+1)`, built by the same transfer recursion as
  `cChainPair`; `eval_cChainPoly` identifies its values with `cChainZ`.
* `degreeOf_cChainPoly`: it is multi-affine, every variable with degree exactly one (the
  all-minus configuration contributes the top monomial `∏ u_j` with coefficient one).
* `dualPoly_cChainPoly`: it is self-dual, `P^♯ = P`.  This follows from the global spin flip
  (`cChainZ_reciprocal`) together with conjugation of the fugacities.
* `cChainDatum`: with any positive frequencies it is a `LeeYangDatum`, so every theorem proved for
  Lee–Yang data (zero counts, zero-gap law, field-density budget) applies to complex-fugacity
  chains.
-/

open MvPolynomial Complex Finset

namespace RHTower.LeeYangChain

noncomputable section

variable (N : ℕ)

/-- The field variable at site `k` (zero beyond the chain). -/
def chainVar (k : ℕ) : MvPolynomial (Fin (N + 1)) ℂ :=
  if h : k < N + 1 then X ⟨k, h⟩ else 0

/-- Extension of a field vector by zero. -/
def chainExt (w : Fin (N + 1) → ℂ) (k : ℕ) : ℂ := if h : k < N + 1 then w ⟨k, h⟩ else 0

/-- Extension of a field vector by one. -/
def chainExtOne (w : Fin (N + 1) → ℂ) (k : ℕ) : ℂ := if h : k < N + 1 then w ⟨k, h⟩ else 1

/-- The chain weights as polynomials in the fields. -/
def cChainPolyPair (α : ℕ → ℂ) : ℕ → MvPolynomial (Fin (N + 1)) ℂ × MvPolynomial (Fin (N + 1)) ℂ
  | 0 => (1, chainVar N 0)
  | k + 1 =>
      ((cChainPolyPair α k).1 + C (α k) * (cChainPolyPair α k).2,
        chainVar N (k + 1) * (C ((starRingEnd ℂ) (α k)) * (cChainPolyPair α k).1 +
          (cChainPolyPair α k).2))

/-- The chain polynomial. -/
def cChainPoly (α : ℕ → ℂ) : MvPolynomial (Fin (N + 1)) ℂ :=
  (cChainPolyPair N α N).1 + (cChainPolyPair N α N).2

theorem eval_chainVar (w : Fin (N + 1) → ℂ) (k : ℕ) :
    eval w (chainVar N k) = chainExt N w k := by
  unfold chainVar chainExt
  split_ifs <;> simp

theorem eval_cChainPolyPair (α : ℕ → ℂ) (w : Fin (N + 1) → ℂ) (k : ℕ) :
    eval w (cChainPolyPair N α k).1 = (cChainPair α (chainExt N w) k).1 ∧
      eval w (cChainPolyPair N α k).2 = (cChainPair α (chainExt N w) k).2 := by
  induction k with
  | zero => simp [cChainPolyPair, cChainPair, eval_chainVar]
  | succ k ih =>
    simp only [cChainPolyPair, cChainPair, map_add, map_mul, eval_C, eval_chainVar, ih.1, ih.2]
    exact ⟨trivial, trivial⟩

/-- The chain only sees the fields at the sites `0, …, k`. -/
theorem cChainPair_congr (α : ℕ → ℂ) {u v : ℕ → ℂ} {k : ℕ} (h : ∀ i ≤ k, u i = v i) :
    cChainPair α u k = cChainPair α v k := by
  induction k with
  | zero => simp [cChainPair, h 0 le_rfl]
  | succ k ih =>
    simp only [cChainPair]
    rw [ih fun i hi => h i (by omega), h (k + 1) le_rfl]

theorem eval_cChainPoly (α : ℕ → ℂ) (w : Fin (N + 1) → ℂ) :
    eval w (cChainPoly N α) = cChainZ α (chainExt N w) N := by
  rw [cChainPoly, map_add, (eval_cChainPolyPair N α w N).1, (eval_cChainPolyPair N α w N).2]
  rfl

/-- Conjugation of a chain conjugates fugacities and fields. -/
theorem conj_cChainPair (β u : ℕ → ℂ) (k : ℕ) :
    (starRingEnd ℂ) (cChainPair β u k).1 =
        (cChainPair (fun i => (starRingEnd ℂ) (β i)) (fun i => (starRingEnd ℂ) (u i)) k).1 ∧
      (starRingEnd ℂ) (cChainPair β u k).2 =
        (cChainPair (fun i => (starRingEnd ℂ) (β i)) (fun i => (starRingEnd ℂ) (u i)) k).2 := by
  induction k with
  | zero => simp [cChainPair]
  | succ k ih =>
    simp only [cChainPair, map_add, map_mul, ih.1, ih.2, Complex.conj_conj]
    exact ⟨trivial, trivial⟩

/-! ## Degrees -/

theorem degreeOf_chainVar_le (k : ℕ) (j : Fin (N + 1)) :
    degreeOf j (chainVar N k) ≤ if j.val = k then 1 else 0 := by
  unfold chainVar
  split_ifs with h hj hj
  · rw [degreeOf_X]; split_ifs <;> simp_all
  · rw [degreeOf_X, if_neg]; exact fun h' => hj (by rw [h'])
  · simp
  · simp

theorem degreeOf_cChainPolyPair_le (α : ℕ → ℂ) (j : Fin (N + 1)) (k : ℕ) :
    degreeOf j (cChainPolyPair N α k).1 ≤ (if j.val < k then 1 else 0) ∧
      degreeOf j (cChainPolyPair N α k).2 ≤ (if j.val ≤ k then 1 else 0) := by
  induction k with
  | zero =>
    refine ⟨by simp [cChainPolyPair], ?_⟩
    have h := degreeOf_chainVar_le N 0 j
    simp only [cChainPolyPair]
    refine h.trans ?_
    split_ifs <;> omega
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · simp only [cChainPolyPair]
      refine (degreeOf_add_le _ _ _).trans (max_le (h1.trans ?_) ?_)
      · split_ifs <;> omega
      · refine (degreeOf_mul_le _ _ _).trans ?_
        rw [degreeOf_C, zero_add]
        refine h2.trans ?_
        split_ifs <;> omega
    · simp only [cChainPolyPair]
      refine (degreeOf_mul_le _ _ _).trans ?_
      have hv := degreeOf_chainVar_le N (k + 1) j
      have hs : degreeOf j (C ((starRingEnd ℂ) (α k)) * (cChainPolyPair N α k).1 +
          (cChainPolyPair N α k).2) ≤ if j.val ≤ k then 1 else 0 := by
        refine (degreeOf_add_le _ _ _).trans (max_le ?_ h2)
        refine (degreeOf_mul_le _ _ _).trans ?_
        rw [degreeOf_C, zero_add]
        refine h1.trans ?_
        split_ifs <;> omega
      calc degreeOf j (chainVar N (k + 1)) + degreeOf j (C ((starRingEnd ℂ) (α k)) *
            (cChainPolyPair N α k).1 + (cChainPolyPair N α k).2)
          ≤ (if j.val = k + 1 then 1 else 0) + (if j.val ≤ k then 1 else 0) := add_le_add hv hs
        _ ≤ if j.val ≤ k + 1 then 1 else 0 := by split_ifs <;> omega

/-- The top exponent `∑_{j ≤ k} e_j`. -/
def chainTop (k : ℕ) : Fin (N + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if j.val ≤ k then 1 else 0

theorem chainTop_apply (k : ℕ) (j : Fin (N + 1)) : chainTop N k j = if j.val ≤ k then 1 else 0 :=
  rfl

theorem coeff_eq_zero_of_degreeOf_lt {P : MvPolynomial (Fin (N + 1)) ℂ} {m : Fin (N + 1) →₀ ℕ}
    (j : Fin (N + 1)) (h : degreeOf j P < m j) : coeff m P = 0 := by
  by_contra hne
  exact absurd (monomial_le_degreeOf j (mem_support_iff.mpr hne)) (not_le.mpr h)

theorem coeff_chainTop_cChainPolyPair (α : ℕ → ℂ) :
    ∀ k ≤ N, coeff (chainTop N k) (cChainPolyPair N α k).1 = 0 ∧
      coeff (chainTop N k) (cChainPolyPair N α k).2 = 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : (0 : ℕ) < N + 1 := by omega
    have htop : chainTop N 0 = Finsupp.single ⟨0, h0⟩ 1 := by
      ext j
      rw [chainTop_apply, Finsupp.single_apply]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (Fin.ext (by simp; omega)) h2
      · exact absurd (by rw [← h2]) h1
      · rfl
    simp only [cChainPolyPair, chainVar, dif_pos h0, htop]
    constructor
    · rw [coeff_one, if_neg]; intro h; have := congrArg (fun f => f ⟨0, h0⟩) h; simp at this
    · rw [coeff_X, if_pos rfl]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hk1 : k + 1 < N + 1 := by omega
    set j₀ : Fin (N + 1) := ⟨k + 1, hk1⟩
    have hsplit : chainTop N (k + 1) - Finsupp.single j₀ 1 = chainTop N k := by
      ext j
      rw [Finsupp.tsub_apply, chainTop_apply, chainTop_apply, Finsupp.single_apply]
      by_cases hj : j = j₀
      · subst hj; simp [j₀]
      · rw [if_neg (Ne.symm hj)]
        have : j.val ≠ k + 1 := fun h => hj (Fin.ext h)
        split_ifs <;> omega
    have hmem : j₀ ∈ (chainTop N (k + 1)).support := by
      rw [Finsupp.mem_support_iff, chainTop_apply]; simp [j₀]
    have hdegA := (degreeOf_cChainPolyPair_le N α j₀ k).1
    have hdegB := (degreeOf_cChainPolyPair_le N α j₀ k).2
    have hA0 : coeff (chainTop N (k + 1)) (cChainPolyPair N α k).1 = 0 := by
      refine coeff_eq_zero_of_degreeOf_lt N j₀ (lt_of_le_of_lt hdegA ?_)
      rw [chainTop_apply]; simp [j₀]
    have hB0 : coeff (chainTop N (k + 1)) (cChainPolyPair N α k).2 = 0 := by
      refine coeff_eq_zero_of_degreeOf_lt N j₀ (lt_of_le_of_lt hdegB ?_)
      rw [chainTop_apply]; simp [j₀]
    constructor
    · simp only [cChainPolyPair]
      rw [coeff_add, coeff_C_mul, hA0, hB0]; ring
    · simp only [cChainPolyPair, chainVar, dif_pos hk1]
      rw [coeff_X_mul', if_pos hmem, hsplit, coeff_add, coeff_C_mul, h1, h2]; ring

/-- **The chain polynomial is multi-affine with full degree.** -/
theorem degreeOf_cChainPoly (α : ℕ → ℂ) (j : Fin (N + 1)) : degreeOf j (cChainPoly N α) = 1 := by
  apply le_antisymm
  · obtain ⟨h1, h2⟩ := degreeOf_cChainPolyPair_le N α j N
    refine (degreeOf_add_le _ _ _).trans (max_le (h1.trans ?_) (h2.trans ?_)) <;>
      split_ifs <;> omega
  · obtain ⟨h1, h2⟩ := coeff_chainTop_cChainPolyPair N α N le_rfl
    have hc : coeff (chainTop N N) (cChainPoly N α) = 1 := by
      rw [cChainPoly, coeff_add, h1, h2, zero_add]
    have hmem : chainTop N N ∈ (cChainPoly N α).support := by
      rw [mem_support_iff, hc]; exact one_ne_zero
    have := monomial_le_degreeOf j hmem
    rw [chainTop_apply, if_pos (by omega)] at this
    exact this

/-! ## Self-duality -/

theorem prod_chainExtOne (u : Fin (N + 1) → ℂ) :
    ∏ i ∈ range (N + 1), chainExtOne N u i = ∏ j, u j := by
  rw [← Fin.prod_univ_eq_prod_range]
  refine prod_congr rfl fun j _ => ?_
  simp [chainExtOne, j.2]

/-- `P^♯(w) = P(w)` at every field vector with nonzero coordinates. -/
theorem eval_dualPoly_cChainPoly_of_ne_zero (α : ℕ → ℂ) {w : Fin (N + 1) → ℂ}
    (hw : ∀ j, w j ≠ 0) :
    eval w (LeeYangCount.dualPoly (cChainPoly N α)) = eval w (cChainPoly N α) := by
  set u : Fin (N + 1) → ℂ := fun j => ((starRingEnd ℂ) (w j))⁻¹ with hu
  have hu0 : ∀ j, u j ≠ 0 := fun j => inv_ne_zero ((map_ne_zero _).mpr (hw j))
  have hrefl := LeeYangCount.eval_eq_prod_mul_conj_dual (cChainPoly N α) hu0
  have hback : (fun j => ((starRingEnd ℂ) (u j))⁻¹) = w := by
    funext j; simp [hu]
  rw [hback] at hrefl
  simp only [degreeOf_cChainPoly, pow_one] at hrefl
  -- the left side through the spin flip
  have hZ : eval u (cChainPoly N α) = cChainZ α (chainExtOne N u) N := by
    rw [eval_cChainPoly, cChainZ, cChainZ,
      cChainPair_congr α (u := chainExt N u) (v := chainExtOne N u)
        (fun i hi => by simp [chainExt, chainExtOne, show i < N + 1 by omega])]
  have hne1 : ∀ k, chainExtOne N u k ≠ 0 := fun k => by
    unfold chainExtOne; split_ifs <;> simp [hu0]
  have hflip := cChainZ_reciprocal α hne1 N
  rw [prod_chainExtOne] at hflip
  have hinv : (fun i => (chainExtOne N u i)⁻¹) =
      fun i => (starRingEnd ℂ) (chainExtOne N w i) := by
    funext i; unfold chainExtOne; split_ifs <;> simp [hu]
  rw [hinv] at hflip
  have hconj := conj_cChainPair (fun i => (starRingEnd ℂ) (α i))
    (fun i => (starRingEnd ℂ) (chainExtOne N w i)) N
  simp only [Complex.conj_conj] at hconj
  have hZw : cChainZ α (chainExtOne N w) N = eval w (cChainPoly N α) := by
    rw [eval_cChainPoly, cChainZ, cChainZ,
      cChainPair_congr α (u := chainExtOne N w) (v := chainExt N w)
        (fun i hi => by simp [chainExt, chainExtOne, show i < N + 1 by omega])]
  have hprod0 : (∏ j, u j) ≠ 0 := prod_ne_zero_iff.mpr fun j _ => hu0 j
  have hkey : (starRingEnd ℂ) (eval w (LeeYangCount.dualPoly (cChainPoly N α))) =
      cChainZ (fun i => (starRingEnd ℂ) (α i))
        (fun i => (starRingEnd ℂ) (chainExtOne N w i)) N := by
    apply mul_left_cancel₀ hprod0
    rw [← hrefl, hZ, hflip]
  have hZconj : (starRingEnd ℂ) (cChainZ (fun i => (starRingEnd ℂ) (α i))
      (fun i => (starRingEnd ℂ) (chainExtOne N w i)) N) = cChainZ α (chainExtOne N w) N := by
    rw [cChainZ, cChainZ, map_add, hconj.1, hconj.2]
  rw [← hZw, ← hZconj, ← hkey, Complex.conj_conj]

/-- **Self-duality.** `P^♯ = P` for the chain polynomial. -/
theorem dualPoly_cChainPoly (α : ℕ → ℂ) :
    LeeYangCount.dualPoly (cChainPoly N α) = cChainPoly N α := by
  have hX : (∏ j : Fin (N + 1), (X j : MvPolynomial (Fin (N + 1)) ℂ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => X_ne_zero j
  apply mul_left_cancel₀ hX
  apply MvPolynomial.funext
  intro w
  rw [map_mul, map_mul, map_prod]
  simp only [eval_X]
  by_cases hw : ∀ j, w j ≠ 0
  · rw [eval_dualPoly_cChainPoly_of_ne_zero N α hw]
  · push Not at hw
    obtain ⟨j, hj⟩ := hw
    rw [prod_eq_zero (mem_univ j) hj, zero_mul, zero_mul]

/-- **The chain is a Lee–Yang datum.** -/
def cChainDatum (α : ℕ → ℂ) (hα : ∀ k, ‖α k‖ ≤ 1) (freq : Fin (N + 1) → ℝ)
    (hfreq : ∀ j, 0 < freq j) : LeeYangCount.LeeYangDatum (Fin (N + 1)) where
  P := cChainPoly N α
  freq := freq
  freq_pos := hfreq
  disk := fun w hw => by
    rw [eval_cChainPoly]
    refine cChainZ_ne_zero_of_norm_lt_one hα (fun k => ?_) N
    unfold chainExt; split_ifs
    · exact hw _
    · simp
  dualDisk := fun w hw => by
    rw [dualPoly_cChainPoly, eval_cChainPoly]
    refine cChainZ_ne_zero_of_norm_lt_one hα (fun k => ?_) N
    unfold chainExt; split_ifs
    · exact hw _
    · simp

theorem cChainDatum_degreeOf (α : ℕ → ℂ) (hα : ∀ k, ‖α k‖ ≤ 1) (freq : Fin (N + 1) → ℝ)
    (hfreq : ∀ j, 0 < freq j) (j : Fin (N + 1)) :
    (cChainDatum N α hα freq hfreq).P.degreeOf j = 1 :=
  degreeOf_cChainPoly N α j

end

end RHTower.LeeYangChain
