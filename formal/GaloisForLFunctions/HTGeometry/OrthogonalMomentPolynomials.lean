import GaloisForLFunctions.HTGeometry.MomentInnerProduct

/-!
# Monic orthogonal polynomials of a moment sequence

Gram--Schmidt applied to the monomial basis for the moment inner product of `MomentInnerProduct`.
The resulting family `monicOrtho s n` is monic of exact degree `n`, and for a positive definite
moment form it is orthogonal: `⟪monicOrtho s m, monicOrtho s n⟫_s = 0` whenever `m ≠ n`.

The degree and monicity statements need no positivity — the subtracted correction is a combination
of strictly lower degrees whatever the coefficients are — so they are proved unconditionally.
Positivity enters only for orthogonality, where it supplies the nonvanishing denominators.

Together with `momentInner_X_mul` this is the base for the three-term recurrence and hence for the
Jacobi matrix of an indeterminate Hamburger sequence.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- Subtraction in the left slot of the moment form. -/
theorem momentInner_sub_left (s : ℕ → ℝ) (p q r : Polynomial ℝ) :
    momentInner s (p - q) r = momentInner s p r - momentInner s q r := by
  have hpq : p - q = p + (-1 : ℝ) • q := by
    simp [sub_eq_add_neg]
  rw [hpq, momentInner_add_left, momentInner_smul_left]
  ring

/-- **Gram--Schmidt on the monomials.**  `monicOrtho s n` is `Xⁿ` corrected by its moment
projections onto all strictly earlier members. -/
noncomputable def monicOrtho (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ n - ∑ k : Fin n,
    (momentInner s (Polynomial.X ^ n) (monicOrtho s k.1) /
        momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1
termination_by n
decreasing_by exact k.isLt

theorem monicOrtho_eq (s : ℕ → ℝ) (n : ℕ) :
    monicOrtho s n = Polynomial.X ^ n - ∑ k : Fin n,
      (momentInner s (Polynomial.X ^ n) (monicOrtho s k.1) /
          momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1 := by
  rw [monicOrtho]

@[simp] theorem monicOrtho_zero (s : ℕ → ℝ) : monicOrtho s 0 = 1 := by
  rw [monicOrtho_eq]
  simp

/-! ## Exact degree and monicity -/

/-- The correction term has strictly smaller degree than `Xⁿ`. -/
theorem degree_monicOrtho_correction_lt (s : ℕ → ℝ) (n : ℕ)
    (ih : ∀ m, m < n → (monicOrtho s m).degree = (m : WithBot ℕ)) :
    (∑ k : Fin n,
        (momentInner s (Polynomial.X ^ n) (monicOrtho s k.1) /
            momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1).degree
      < (n : WithBot ℕ) := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k _ => by
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
    rw [ih k.1 k.isLt]
    exact WithBot.coe_lt_coe.mpr k.isLt

/-- The moment orthogonal polynomial of index `n` has exact degree `n`. -/
theorem monicOrtho_degree (s : ℕ → ℝ) (n : ℕ) :
    (monicOrtho s n).degree = (n : WithBot ℕ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [monicOrtho_eq]
    have hlt := degree_monicOrtho_correction_lt s n ih
    rw [← Polynomial.degree_X_pow (R := ℝ) n] at hlt
    rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]

theorem monicOrtho_monic (s : ℕ → ℝ) (n : ℕ) : (monicOrtho s n).Monic := by
  rw [monicOrtho_eq]
  have hlt := degree_monicOrtho_correction_lt s n fun m _ => monicOrtho_degree s m
  rw [← Polynomial.degree_X_pow (R := ℝ) n] at hlt
  exact (Polynomial.monic_X_pow n).sub_of_left hlt

theorem monicOrtho_ne_zero (s : ℕ → ℝ) (n : ℕ) : monicOrtho s n ≠ 0 :=
  (monicOrtho_monic s n).ne_zero

/-! ## Orthogonality -/

/-- Orthogonality to all strictly earlier members. -/
theorem monicOrtho_inner_lower {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    ∀ m < n, momentInner s (monicOrtho s n) (monicOrtho s m) = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm
    have hself : momentInner s (monicOrtho s m) (monicOrtho s m) ≠ 0 :=
      h.self_ne_zero (monicOrtho_ne_zero s m)
    rw [monicOrtho_eq s n, momentInner_sub_left, momentInner_sum_left]
    simp only [momentInner_smul_left]
    rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin n)]
    · rw [div_mul_cancel₀ _ hself, sub_self]
    · intro k _ hk
      have hkm : (k : ℕ) ≠ m := fun hEq => hk (Fin.ext hEq)
      have hzero : momentInner s (monicOrtho s k.1) (monicOrtho s m) = 0 := by
        rcases lt_or_gt_of_ne hkm with hlt | hgt
        · rw [momentInner_comm]
          exact ih m hm k.1 hlt
        · exact ih k.1 k.isLt m hgt
      rw [hzero, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ (⟨m, hm⟩ : Fin n)) hmem

/-- **The moment orthogonal family is orthogonal.** -/
theorem monicOrtho_inner_eq_zero {s : ℕ → ℝ} (h : PositiveMomentForm s) {m n : ℕ}
    (hmn : m ≠ n) : momentInner s (monicOrtho s m) (monicOrtho s n) = 0 := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · rw [momentInner_comm]
    exact monicOrtho_inner_lower h n m hlt
  · exact monicOrtho_inner_lower h m n hgt

/-- Each member has strictly positive moment norm. -/
theorem monicOrtho_inner_self_pos {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    0 < momentInner s (monicOrtho s n) (monicOrtho s n) :=
  h.pos_of_ne_zero _ (monicOrtho_ne_zero s n)

/-- The orthogonal family is linearly independent for the moment form. -/
theorem monicOrtho_coeff_eq_zero {s : ℕ → ℝ} (h : PositiveMomentForm s) (t : Finset ℕ)
    (c : ℕ → ℝ) (hzero : ∑ i ∈ t, c i • monicOrtho s i = 0) :
    ∀ i ∈ t, c i = 0 :=
  eq_zero_of_forall_momentOrthogonal h t (fun i => monicOrtho s i) c
    (fun _ _ _ _ hij => monicOrtho_inner_eq_zero h hij)
    (fun i _ => monicOrtho_ne_zero s i) hzero

/-! ## Orthogonality to all lower degrees, and tridiagonality -/

/-- **The defining property of orthogonal polynomials.**  `monicOrtho s n` is orthogonal to every
polynomial of degree `< n`, not merely to the earlier members of the family.  The induction rebuilds
an arbitrary `p` from its leading monomial, using `Xᵈ = monicOrtho s d + (correction of degree < d)`.
-/
theorem monicOrtho_inner_eq_zero_of_degree_lt {s : ℕ → ℝ} (h : PositiveMomentForm s) (n : ℕ) :
    ∀ m, m ≤ n → ∀ p : Polynomial ℝ, p.degree < (m : WithBot ℕ) →
      momentInner s (monicOrtho s n) p = 0 := by
  intro m
  induction m with
  | zero =>
      intro _ p hp
      have hbot : p.degree = ⊥ := Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
      rw [Polynomial.degree_eq_bot.mp hbot, momentInner_zero_right]
  | succ m ih =>
      intro hmn p hp
      rcases eq_or_ne p 0 with rfl | hp0
      · simp
      · have hmn' : m ≤ n := Nat.le_of_succ_le hmn
        have hdlt : p.natDegree < m + 1 :=
          (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
        have hdm : p.natDegree ≤ m := Nat.lt_succ_iff.mp hdlt
        have hdn : p.natDegree < n := lt_of_le_of_lt hdm (Nat.lt_of_succ_le hmn)
        have hc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
        have hqdeg : (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).degree
            = (p.natDegree : WithBot ℕ) := by
          rw [Polynomial.degree_C_mul_X_pow _ hc0]
        have hsub : (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).degree
            < (p.natDegree : WithBot ℕ) := by
          have hdegeq : p.degree
              = (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).degree := by
            rw [hqdeg, Polynomial.degree_eq_natDegree hp0]
          have hlc : p.leadingCoeff
              = (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).leadingCoeff := by
            rw [Polynomial.leadingCoeff_C_mul_X_pow]
          have := Polynomial.degree_sub_lt hdegeq hp0 hlc
          rwa [Polynomial.degree_eq_natDegree hp0] at this
        have hsplit : p = (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree)
            + Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree := by ring
        have hlow : momentInner s (monicOrtho s n)
            (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree) = 0 :=
          ih hmn' _ (lt_of_lt_of_le hsub (by exact_mod_cast hdm))
        have hcorr : (∑ k : Fin p.natDegree,
            (momentInner s (Polynomial.X ^ p.natDegree) (monicOrtho s k.1) /
                momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1).degree
              < (p.natDegree : WithBot ℕ) :=
          degree_monicOrtho_correction_lt s p.natDegree fun j _ => monicOrtho_degree s j
        have hxd : momentInner s (monicOrtho s n) (Polynomial.X ^ p.natDegree) = 0 := by
          have hxeq : (Polynomial.X : Polynomial ℝ) ^ p.natDegree
              = monicOrtho s p.natDegree + (∑ k : Fin p.natDegree,
                (momentInner s (Polynomial.X ^ p.natDegree) (monicOrtho s k.1) /
                    momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1) := by
            rw [monicOrtho_eq s p.natDegree]
            ring
          rw [hxeq, momentInner_add_right,
            monicOrtho_inner_eq_zero h (Nat.ne_of_gt hdn),
            ih hmn' _ (lt_of_lt_of_le hcorr (by exact_mod_cast hdm)), add_zero]
        have hlead : momentInner s (monicOrtho s n)
            (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree) = 0 := by
          have hsmul : Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree
              = p.leadingCoeff • (Polynomial.X : Polynomial ℝ) ^ p.natDegree := by
            simp [Polynomial.smul_eq_C_mul]
          rw [hsmul, momentInner_smul_right, hxd, mul_zero]
        conv_lhs => rw [hsplit]
        rw [momentInner_add_right, hlow, hlead, add_zero]

/-- **Tridiagonality of the Jacobi form.**  Multiplication by `X` connects `monicOrtho s n` only to
its two neighbours: everything at distance at least two is annihilated.  This is `momentInner_X_mul`
combined with orthogonality to lower degrees, and it is exactly the statement that the Jacobi matrix
of the moment sequence is tridiagonal. -/
theorem monicOrtho_X_mul_inner_eq_zero {s : ℕ → ℝ} (h : PositiveMomentForm s) {n k : ℕ}
    (hk : k + 1 < n) :
    momentInner s (Polynomial.X * monicOrtho s n) (monicOrtho s k) = 0 := by
  rw [momentInner_X_mul]
  refine monicOrtho_inner_eq_zero_of_degree_lt h n n le_rfl _ ?_
  have hdeg : (Polynomial.X * monicOrtho s k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_mul, Polynomial.degree_X, monicOrtho_degree s k]
    push_cast
    ring
  rw [hdeg]
  exact WithBot.coe_lt_coe.mpr hk

/-! ## Span and Fourier expansion -/

/-- The Gram--Schmidt correction subtracted from `Xⁿ`, named for reuse. -/
noncomputable def monicOrthoCorrection (s : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ k : Fin n,
    (momentInner s (Polynomial.X ^ n) (monicOrtho s k.1) /
        momentInner s (monicOrtho s k.1) (monicOrtho s k.1)) • monicOrtho s k.1

theorem X_pow_eq_monicOrtho_add_correction (s : ℕ → ℝ) (n : ℕ) :
    (Polynomial.X : Polynomial ℝ) ^ n = monicOrtho s n + monicOrthoCorrection s n := by
  rw [monicOrtho_eq s n, monicOrthoCorrection]
  ring

theorem degree_monicOrthoCorrection_lt (s : ℕ → ℝ) (n : ℕ) :
    (monicOrthoCorrection s n).degree < (n : WithBot ℕ) :=
  degree_monicOrtho_correction_lt s n fun m _ => monicOrtho_degree s m

/-- **The family spans by degree.**  Every polynomial of degree `< m` lies in the span of
`monicOrtho s 0, …, monicOrtho s (m-1)`. -/
theorem mem_span_monicOrtho {s : ℕ → ℝ} (m : ℕ) :
    ∀ p : Polynomial ℝ, p.degree < (m : WithBot ℕ) →
      p ∈ Submodule.span ℝ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m}) := by
  induction m with
  | zero =>
      intro p hp
      have hbot : p.degree = ⊥ := Nat.WithBot.lt_zero_iff.mp (by simpa using hp)
      rw [Polynomial.degree_eq_bot.mp hbot]
      exact Submodule.zero_mem _
  | succ m ih =>
      intro p hp
      have hmono : ((fun k => monicOrtho s k) ''' {k : ℕ | k < m})
          ⊆ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m + 1}) :=
        Set.image_subset _ fun k hk => Nat.lt_succ_of_lt hk
      rcases eq_or_ne p 0 with rfl | hp0
      · exact Submodule.zero_mem _
      · have hdlt : p.natDegree < m + 1 := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
        have hdm : p.natDegree ≤ m := Nat.lt_succ_iff.mp hdlt
        have hc0 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp0
        have hsub : (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).degree
            < (p.natDegree : WithBot ℕ) := by
          have hdegeq : p.degree
              = (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).degree := by
            rw [Polynomial.degree_C_mul_X_pow _ hc0, Polynomial.degree_eq_natDegree hp0]
          have hlc : p.leadingCoeff
              = (Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree).leadingCoeff := by
            rw [Polynomial.leadingCoeff_C_mul_X_pow]
          have hlt := Polynomial.degree_sub_lt hdegeq hp0 hlc
          rwa [Polynomial.degree_eq_natDegree hp0] at hlt
        have hcast : ((p.natDegree : ℕ) : WithBot ℕ) ≤ ((m : ℕ) : WithBot ℕ) := by
          exact_mod_cast hdm
        have hmem1 : (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree)
            ∈ Submodule.span ℝ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m + 1}) :=
          Submodule.span_mono hmono (ih _ (lt_of_lt_of_le hsub hcast))
        have hmem2 : monicOrthoCorrection s p.natDegree
            ∈ Submodule.span ℝ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m + 1}) :=
          Submodule.span_mono hmono
            (ih _ (lt_of_lt_of_le (degree_monicOrthoCorrection_lt s p.natDegree) hcast))
        have hmem3 : monicOrtho s p.natDegree
            ∈ Submodule.span ℝ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m + 1}) :=
          Submodule.subset_span ⟨p.natDegree, hdlt, rfl⟩
        have hpeq : p = (p - Polynomial.C p.leadingCoeff * Polynomial.X ^ p.natDegree)
            + p.leadingCoeff •
              (monicOrtho s p.natDegree + monicOrthoCorrection s p.natDegree) := by
          rw [← X_pow_eq_monicOrtho_add_correction s p.natDegree, Polynomial.smul_eq_C_mul]
          ring
        rw [hpeq]
        exact Submodule.add_mem _ hmem1
          (Submodule.smul_mem _ _ (Submodule.add_mem _ hmem3 hmem2))

/-- A polynomial orthogonal to every early member is orthogonal to their whole span. -/
theorem momentInner_eq_zero_of_mem_span {s : ℕ → ℝ} {r : Polynomial ℝ} {m : ℕ}
    (hr : ∀ k < m, momentInner s r (monicOrtho s k) = 0)
    {p : Polynomial ℝ}
    (hp : p ∈ Submodule.span ℝ ((fun k => monicOrtho s k) ''' {k : ℕ | k < m})) :
    momentInner s r p = 0 := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hr k hk
  | zero => simp
  | add x y _ _ hx hy => rw [momentInner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [momentInner_smul_right, hx, mul_zero]

/-- **Fourier expansion in the orthogonal family.**  A polynomial of degree `< m` is the sum of its
moment projections onto `monicOrtho s 0, …, monicOrtho s (m-1)`. -/
theorem monicOrtho_expansion {s : ℕ → ℝ} (h : PositiveMomentForm s) (m : ℕ)
    (p : Polynomial ℝ) (hp : p.degree < (m : WithBot ℕ)) :
    p = ∑ k ∈ Finset.range m,
      (momentInner s p (monicOrtho s k) / momentInner s (monicOrtho s k) (monicOrtho s k))
        • monicOrtho s k := by
  set q : Polynomial ℝ := ∑ k ∈ Finset.range m,
    (momentInner s p (monicOrtho s k) / momentInner s (monicOrtho s k) (monicOrtho s k))
      • monicOrtho s k with hq
  have hqdeg : q.degree < (m : WithBot ℕ) := by
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe m)).mpr fun k hk => ?_
    refine lt_of_le_of_lt (Polynomial.degree_smul_le _ _) ?_
    rw [monicOrtho_degree s k]
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk)
  have hproj : ∀ j < m, momentInner s q (monicOrtho s j) =
      momentInner s p (monicOrtho s j) := by
    intro j hj
    rw [hq, momentInner_sum_left]
    rw [Finset.sum_eq_single j]
    · rw [momentInner_smul_left,
        div_mul_cancel₀ _ (h.self_ne_zero (monicOrtho_ne_zero s j))]
    · intro k _ hkj
      rw [momentInner_smul_left, monicOrtho_inner_eq_zero h hkj, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr hj) hnot
  have hrortho : ∀ j < m, momentInner s (p - q) (monicOrtho s j) = 0 := by
    intro j hj
    rw [momentInner_sub_left, hproj j hj, sub_self]
  have hrdeg : (p - q).degree < (m : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hp hqdeg)
  have hrmem := mem_span_monicOrtho (s := s) m (p - q) hrdeg
  have hrr : momentInner s (p - q) (p - q) = 0 :=
    momentInner_eq_zero_of_mem_span hrortho hrmem
  have : p - q = 0 := h.eq_zero_of_self_eq_zero hrr
  linear_combination (norm := ring_nf) this

end HTGeometry
