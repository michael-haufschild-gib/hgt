import GaloisForLFunctions.RHTower.CCMSourceResponseDeterminantDichotomy

/-!
# The rank-one logarithmic Dirac completion and its regularized determinant

For a finite clock `d : n → ℂ`, the constant boundary `η = 1` and a vector `ξ` with `∑ ξ_i = 1`,
the CCM completion `A = D - |Dξ⟩⟨η|` (`ccmSourceCompletion`) kills `ξ`, and

`charpoly A = X · P_ξ`,   `P_ξ = ∑_i ξ_i ∏_{j ≠ i} (X - d_j)`,

with `P_ξ` monic of degree `|n| - 1`.  Thus `P_ξ` is the characteristic polynomial of `A` on
`ℂⁿ/ℂξ`, and off the clock `P_ξ(z) = ∏_j (z - d_j) · ∑_i ξ_i/(z - d_i)`.

If the free operator has spectral zeta function `Z₀`, replacing its block eigenvalues `d_i` by the
roots of `P_ξ` changes the zeta function by finitely many powers `c^{-s}`, whose derivatives at
`s = 0` are `-log c`.  The resulting ζ-regularized determinant is
`exp(-Z₀'(0)) · ∑_i ξ_i/(d_i - z)`.
-/

namespace RHTower

noncomputable section

open Polynomial Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The quotient characteristic polynomial -/

/-- Quotient characteristic polynomial `P_ξ = ∑_i ξ_i ∏_{j ≠ i} (X - d_j)`. -/
def ccmRankOneQuotientCharpoly (d ξ : n → ℂ) : ℂ[X] :=
  ∑ i, C (ξ i) * ∏ j ∈ Finset.univ.erase i, (X - C (d j))

theorem eval_ccmRankOneQuotientCharpoly (d ξ : n → ℂ) (z : ℂ) :
    (ccmRankOneQuotientCharpoly d ξ).eval z =
      ∑ i, ξ i * ∏ j ∈ Finset.univ.erase i, (z - d j) := by
  simp [ccmRankOneQuotientCharpoly, eval_finsetSum, eval_prod]

theorem eval_ccmRankOneQuotientCharpoly_eq_mul_resolvent (d ξ : n → ℂ) {z : ℂ}
    (hz : ∀ j, z - d j ≠ 0) :
    (ccmRankOneQuotientCharpoly d ξ).eval z = (∏ j, (z - d j)) * ∑ i, ξ i / (z - d i) := by
  rw [eval_ccmRankOneQuotientCharpoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_prod_erase Finset.univ (fun j => z - d j) (Finset.mem_univ i)]
  field_simp [hz i]

theorem ccmRankOneQuotientCharpoly_factor_monic (d : n → ℂ) (i : n) :
    (∏ j ∈ Finset.univ.erase i, (X - C (d j))).Monic :=
  monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (d j)

theorem ccmRankOneQuotientCharpoly_factor_natDegree (d : n → ℂ) (i : n) :
    (∏ j ∈ Finset.univ.erase i, (X - C (d j))).natDegree = Fintype.card n - 1 := by
  rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (d j)]
  simp [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

theorem ccmRankOneQuotientCharpoly_natDegree_le (d ξ : n → ℂ) :
    (ccmRankOneQuotientCharpoly d ξ).natDegree ≤ Fintype.card n - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [ccmRankOneQuotientCharpoly_factor_natDegree]

theorem ccmRankOneQuotientCharpoly_coeff_top (d ξ : n → ℂ) :
    (ccmRankOneQuotientCharpoly d ξ).coeff (Fintype.card n - 1) = ∑ i, ξ i := by
  rw [ccmRankOneQuotientCharpoly, finsetSum_coeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_C_mul, ← ccmRankOneQuotientCharpoly_factor_natDegree d i,
    (ccmRankOneQuotientCharpoly_factor_monic d i).coeff_natDegree, mul_one]

/-- With the normalization `∑ ξ_i = 1`, `P_ξ` is monic. -/
theorem ccmRankOneQuotientCharpoly_monic (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1) :
    (ccmRankOneQuotientCharpoly d ξ).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one _ (ccmRankOneQuotientCharpoly_natDegree_le d ξ)
    (by rw [ccmRankOneQuotientCharpoly_coeff_top, hξ])

theorem ccmRankOneQuotientCharpoly_natDegree (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1) :
    (ccmRankOneQuotientCharpoly d ξ).natDegree = Fintype.card n - 1 :=
  natDegree_eq_of_le_of_coeff_ne_zero (ccmRankOneQuotientCharpoly_natDegree_le d ξ)
    (by rw [ccmRankOneQuotientCharpoly_coeff_top, hξ]; exact one_ne_zero)

/-! ## The characteristic polynomial of the completion -/

omit [DecidableEq n] in
theorem ccm_prod_sub_eq_neg_one_pow_mul (d : n → ℂ) (z : ℂ) :
    ∏ j, (d j - z) = (-1) ^ Fintype.card n * ∏ j, (z - d j) := by
  rw [← Finset.card_univ, ← Finset.prod_neg]
  exact Finset.prod_congr rfl fun j _ => by ring

/-- **`charpoly A = X · P_ξ`** for the CCM completion `A = D - |Dξ⟩⟨1|`. -/
theorem charpoly_ccmSourceCompletion_diagonal (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1) :
    (ccmSourceCompletion (Matrix.diagonal d) ξ (fun _ => 1)).charpoly =
      X * ccmRankOneQuotientCharpoly d ξ := by
  apply eq_of_infinite_eval_eq
  have hfin : (Set.range d).Finite := Set.finite_range d
  refine (Set.Infinite.sdiff Set.infinite_univ hfin).mono fun z hz => ?_
  have hz' : ∀ j, z - d j ≠ 0 := fun j h => hz.2 ⟨j, (sub_eq_zero.mp h).symm⟩
  have hdz : ∀ j, d j - z ≠ 0 := fun j h => hz' j (by rw [← neg_sub, h, neg_zero])
  have hnorm : star (fun _ : n => (1 : ℂ)) ⬝ᵥ ξ = 1 := by
    simp [dotProduct, hξ]
  have hdiag : Matrix.diagonal d - z • (1 : Matrix n n ℂ) = Matrix.diagonal fun j => d j - z := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij]
  have hunit : IsUnit (Matrix.diagonal d - z • (1 : Matrix n n ℂ)).det := by
    rw [hdiag, Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hdz j).isUnit
  have hdet := ccmSourceCompletion_shift_det_eq_neg_mul_resolvent (Matrix.diagonal d) ξ
    (fun _ => 1) z hnorm hunit
  have hinv : (Matrix.diagonal d - z • (1 : Matrix n n ℂ))⁻¹ =
      Matrix.diagonal fun j => (d j - z)⁻¹ := by
    rw [hdiag]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (hdz j)
  have hres : star (fun _ : n => (1 : ℂ)) ⬝ᵥ
      ((Matrix.diagonal d - z • (1 : Matrix n n ℂ))⁻¹ *ᵥ ξ) = ∑ i, ξ i / (d i - z) := by
    rw [hinv]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, star_one, one_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv, mul_comm]
  simp only [Set.mem_setOf_eq]
  rw [Matrix.eval_charpoly, eval_mul, eval_X,
    eval_ccmRankOneQuotientCharpoly_eq_mul_resolvent d ξ hz']
  have hneg : Matrix.scalar n z - ccmSourceCompletion (Matrix.diagonal d) ξ (fun _ => 1) =
      -(ccmSourceCompletion (Matrix.diagonal d) ξ (fun _ => 1) - z • (1 : Matrix n n ℂ)) := by
    rw [neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [hneg, Matrix.det_neg, hdet, hres, hdiag, Matrix.det_diagonal,
    ccm_prod_sub_eq_neg_one_pow_mul]
  have hsum : ∑ i, ξ i / (d i - z) = -∑ i, ξ i / (z - d i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_sub, div_neg]
  rw [hsum]
  have hpow : ((-1 : ℂ) ^ Fintype.card n) * (-1) ^ Fintype.card n = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (z * (∏ j, (z - d j)) * ∑ i, ξ i / (z - d i)) * hpow

/-- Every root of `P_ξ` is a root of `charpoly A`. -/
theorem ccmRankOneQuotientCharpoly_eval_eq_zero_of_charpoly (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1)
    {z : ℂ} (hP : (ccmRankOneQuotientCharpoly d ξ).eval z = 0) :
    (ccmSourceCompletion (Matrix.diagonal d) ξ (fun _ => 1)).charpoly.eval z = 0 := by
  rw [charpoly_ccmSourceCompletion_diagonal d ξ hξ, eval_mul, hP, mul_zero]

/-- Real spectrum of the completion forces real roots of `P_ξ`. -/
theorem ccmRankOneQuotientCharpoly_root_im_eq_zero (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1)
    (hreal : ∀ z : ℂ,
      (ccmSourceCompletion (Matrix.diagonal d) ξ (fun _ => 1)).charpoly.eval z = 0 → z.im = 0)
    {z : ℂ} (hP : (ccmRankOneQuotientCharpoly d ξ).eval z = 0) : z.im = 0 := by
  exact hreal z (ccmRankOneQuotientCharpoly_eval_eq_zero_of_charpoly d ξ hξ hP)

/-! ## The finite modification of a spectral zeta function -/

/-- Spectral zeta function after replacing the block eigenvalues `d_i` of the free operator by the
roots of `P_ξ` (with multiplicity). -/
def ccmRankOneModifiedZeta (Z₀ : ℂ → ℂ) (d ξ : n → ℂ) (z s : ℂ) : ℂ :=
  Z₀ s - ∑ i, (d i - z) ^ (-s) +
    ((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => (μ - z) ^ (-s)).sum

theorem hasDerivAt_cpow_neg_zero {c : ℂ} (hc : c ≠ 0) :
    HasDerivAt (fun s : ℂ => c ^ (-s)) (-Complex.log c) 0 := by
  have h := (hasDerivAt_neg (0 : ℂ)).const_cpow (c := c) (Or.inl hc)
  simpa using h

theorem hasDerivAt_multiset_sum_cpow_neg {M : Multiset ℂ} {z : ℂ} (hM : ∀ μ ∈ M, μ - z ≠ 0) :
    HasDerivAt (fun s : ℂ => (M.map fun μ => (μ - z) ^ (-s)).sum)
      (-(M.map fun μ => Complex.log (μ - z)).sum) 0 := by
  induction M using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℂ) (0 : ℂ)
  | cons μ M ih =>
    have hμ := hasDerivAt_cpow_neg_zero (hM μ (Multiset.mem_cons_self μ M))
    have hrest := ih fun ν hν => hM ν (Multiset.mem_cons_of_mem hν)
    have hfun : (fun s : ℂ => ((μ ::ₘ M).map fun ν => (ν - z) ^ (-s)).sum) =
        fun s => (μ - z) ^ (-s) + (M.map fun ν => (ν - z) ^ (-s)).sum := by
      funext s
      simp
    rw [hfun]
    refine (hμ.add hrest).congr_deriv ?_
    simp only [Multiset.map_cons, Multiset.sum_cons]
    ring

theorem exp_multiset_sum_log {M : Multiset ℂ} (hM : ∀ c ∈ M, c ≠ 0) :
    Complex.exp (M.map Complex.log).sum = M.prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons c M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons, Complex.exp_add]
    rw [Complex.exp_log (hM c (Multiset.mem_cons_self c M)),
      ih fun x hx => hM x (Multiset.mem_cons_of_mem hx)]

/-- `∏_μ (μ - z) = (-1)^{deg} P_ξ(z)` over the roots of the monic `P_ξ`. -/
theorem prod_roots_sub_eq (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1) (z : ℂ) :
    ((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => μ - z).prod =
      (-1) ^ (Fintype.card n - 1) * (ccmRankOneQuotientCharpoly d ξ).eval z := by
  set P := ccmRankOneQuotientCharpoly d ξ
  have hmon := ccmRankOneQuotientCharpoly_monic d ξ hξ
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hfac := hsplit.eq_prod_roots_of_monic hmon
  have hcard : P.roots.card = Fintype.card n - 1 := by
    rw [← ccmRankOneQuotientCharpoly_natDegree d ξ hξ]
    exact splits_iff_card_roots.mp hsplit
  have heval : P.eval z = (P.roots.map fun μ => z - μ).prod := by
    conv_lhs => rw [hfac]
    rw [eval_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun μ _ => ?_
    simp
  have hneg : (P.roots.map fun μ => μ - z) = (P.roots.map fun μ => z - μ).map Neg.neg := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun μ _ => ?_
    simp
  rw [hneg, Multiset.prod_map_neg, Multiset.card_map, hcard, heval]

/-- **The ζ-regularized determinant of the rank-one completion.**  If the free zeta function
`Z₀` has derivative `Z₀'` at `0` and no block eigenvalue or root of `P_ξ` equals `z`, then
`exp(-Z'(0)) = exp(-Z₀') · ∑_i ξ_i/(d_i - z)` for the modified spectrum. -/
theorem exp_neg_deriv_ccmRankOneModifiedZeta {Z₀ : ℂ → ℂ} {Z₀' : ℂ} (hZ : HasDerivAt Z₀ Z₀' 0)
    (d ξ : n → ℂ) (hξ : ∑ i, ξ i = 1) (hn : 0 < Fintype.card n) {z : ℂ} (hd : ∀ i, d i - z ≠ 0)
    (hroots : ∀ μ ∈ (ccmRankOneQuotientCharpoly d ξ).roots, μ - z ≠ 0) :
    Complex.exp (-deriv (ccmRankOneModifiedZeta Z₀ d ξ z) 0) =
      Complex.exp (-Z₀') * ∑ i, ξ i / (d i - z) := by
  have hblock : HasDerivAt (fun s : ℂ => ∑ i, (d i - z) ^ (-s))
      (∑ i, -Complex.log (d i - z)) 0 :=
    HasDerivAt.fun_sum fun i _ => hasDerivAt_cpow_neg_zero (hd i)
  have hroot := hasDerivAt_multiset_sum_cpow_neg hroots
  have hmod : HasDerivAt (ccmRankOneModifiedZeta Z₀ d ξ z)
      (Z₀' - ∑ i, -Complex.log (d i - z) +
        -((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => Complex.log (μ - z)).sum) 0 :=
    (hZ.sub hblock).add hroot
  rw [hmod.deriv]
  have hsplit : -(Z₀' - ∑ i, -Complex.log (d i - z) +
      -((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => Complex.log (μ - z)).sum) =
      -Z₀' + -(∑ i, Complex.log (d i - z)) +
        ((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => Complex.log (μ - z)).sum := by
    rw [Finset.sum_neg_distrib]; ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_neg (∑ i, _), Complex.exp_sum]
  have hlogs : ∏ i, Complex.exp (Complex.log (d i - z)) = ∏ i, (d i - z) :=
    Finset.prod_congr rfl fun i _ => Complex.exp_log (hd i)
  have hroots' : Complex.exp
      (((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => Complex.log (μ - z)).sum) =
        ((ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => μ - z).prod := by
    have h := exp_multiset_sum_log (M := (ccmRankOneQuotientCharpoly d ξ).roots.map fun μ => μ - z)
      (by
        intro c hc
        obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hc
        exact hroots μ hμ)
    rw [Multiset.map_map] at h
    exact h
  rw [hlogs, hroots', prod_roots_sub_eq d ξ hξ z]
  have hz' : ∀ j, z - d j ≠ 0 := fun j h => hd j (by rw [← neg_sub, h, neg_zero])
  rw [eval_ccmRankOneQuotientCharpoly_eq_mul_resolvent d ξ hz', ccm_prod_sub_eq_neg_one_pow_mul]
  have hprod : ∏ j, (z - d j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hz' j
  have hsum : ∑ i, ξ i / (d i - z) = -∑ i, ξ i / (z - d i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← neg_sub, div_neg]
  rw [hsum]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card n = m + 1 := ⟨Fintype.card n - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, pow_succ]
  have hpow : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  field_simp

end

end RHTower
