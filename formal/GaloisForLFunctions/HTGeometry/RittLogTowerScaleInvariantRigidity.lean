import GaloisForLFunctions.HTGeometry.RittLogTowerDescent
import GaloisForLFunctions.HTGeometry.ConnectionJetGenerators
import GaloisForLFunctions.HTGeometry.PolynomialFamilyDerivations

/-!
# The scale-invariant residual of the affine logarithmic tower is impossible

A collapse of the affine logarithmic tower at order `n` that survives the weight descent is a
polynomial `F` in the jets `x_0,…,x_{n−1}`, weighted homogeneous of weight `n+1` for `w(x_j) = j+1`,
with shift-fixed coefficients, satisfying

`F ∘ A = ρ^{−(n+1)}·F + δ_n`,

where `A` is the affine tower substitution and `δ_n` the tower defect.  With the seed constant
`b₀ = −(dρ)/ρ²` this is impossible as soon as `b₀ ≠ 0` (the map is not affine) and
`b₁ ≠ b₀²/2`, `b₁ = ρ^{−1}·d b₀` (its Schwarzian is nonzero: the map is not Möbius).

Put `Φ = x_n − F(x_0,…,x_{n−1})`.  Conjugating the collapse by the weight scalings turns it into
`Φ ∘ M_ν = Φ` for every `ν ≠ 0`, where `M_ν` is the unipotent family

`M_ν(x_j) = ∑_{i ≤ j} ν^{j−i} ρ^{i+1} a_{j,i}·x_i + ν^{j+1} b_j`.

The `ν`-coefficient of the substitution is the derivation `b₀·ξ₁`, and the combination
`D₂ − ½D₁²` of the `ν²`-coefficient is `(b₁ − b₀²/2)·ξ₂`, where `ξ_k` is the action of `z^{k+1}∂` on
connection jets.  Both kill `Φ`, so `ξ₁Φ = ξ₂Φ = 0`, which no equation solved for its top jet
allows (`not_connectionGen_invariant_graph`).
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Weighted scalings -/

/-- **A weighted homogeneous polynomial scales by the weight.** -/
theorem aeval_weight_scaling {K σ : Type*} [Field K] (w : σ → ℕ) {F : MvPolynomial σ K} {m : ℕ}
    (hF : IsWeightedHomogeneous w F m) (c : K) :
    aeval (fun i => C (c ^ w i) * X i) F = C (c ^ m) * F := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight w d = m := hF (mem_support_iff.mp hd)
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  have hprod : (d.prod fun i k => (C (c ^ w i) * X i : MvPolynomial σ K) ^ k)
      = C (c ^ m) * d.prod fun i k => (X i : MvPolynomial σ K) ^ k := by
    simp only [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [← hw, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
    simp only [← map_pow, ← map_prod, ← pow_mul, smul_eq_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hprod]
  ring

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L)

theorem dK_natCast (m : ℕ) : Fr.dK (m : K) = 0 := by
  induction m with
  | zero => simpa using dK_zero Fr
  | succ m ih => rw [Nat.cast_succ, Fr.dK_add, ih, Fr.dK_one, add_zero]

theorem logConst_one (b : K) : Fr.logConst b 1 = Fr.ρ⁻¹ * Fr.dK b := rfl

/-! ### The first two subdiagonals in seed coordinates -/

/-- **First subdiagonal.**  `ρ^{k+1}·a_{k+1,k} = C(k+2,2)·b₀`. -/
theorem pow_mul_logCoeff_subdiag_seed {b : K} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (k : ℕ) :
    Fr.ρ ^ (k + 1) * Fr.logCoeff (k + 1) k = (((k + 2).choose 2 : ℕ) : K) * b := by
  have hρ := Fr.ρ_ne
  rw [Fr.logCoeff_subdiag, hb]
  field_simp
  ring

/-- **Second subdiagonal.**  `ρ^{k+1}·a_{k+2,k}` in terms of `b₀` and `b₁`. -/
theorem pow_mul_logCoeff_subsubdiag_seed [CharZero K] {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (k : ℕ) :
    Fr.ρ ^ (k + 1) * Fr.logCoeff (k + 2) k
      = ((k : K) + 3) * ((k : K) + 2) * ((k : K) + 1) / 6 * (Fr.logConst b 1 - b ^ 2 / 2)
        + ((k : K) + 3) * ((k : K) + 2) * ((k : K) + 2) * ((k : K) + 1) / 8 * b ^ 2 := by
  have hρ := Fr.ρ_ne
  have hdρ : Fr.dK Fr.ρ = -(Fr.ρ ^ 2 * b) := by
    rw [hb]
    field_simp
  have hdinv : Fr.dK Fr.ρ⁻¹ = b := by rw [Fr.dK_inv hρ, hb]
  have hdb : Fr.dK b = Fr.ρ * Fr.logConst b 1 := by
    rw [logConst_one]
    field_simp
  induction k with
  | zero =>
      have h10 : Fr.logCoeff 1 0 = Fr.ρ⁻¹ * b := by
        rw [logCoeff_succ_zero, logCoeff_zero_zero, hdinv]
      rw [show (0 : ℕ) + 2 = 1 + 1 from rfl, logCoeff_succ_zero, h10, Fr.dK_mul, hdinv, hdb]
      push_cast
      field_simp
      ring
  | succ k ih =>
      have hsub : Fr.logCoeff (k + 2) (k + 1)
          = (((k + 3).choose 2 : ℕ) : K) * b / Fr.ρ ^ (k + 2) := by
        have h := Fr.pow_mul_logCoeff_subdiag_seed hb (k + 1)
        rw [eq_div_iff (pow_ne_zero _ hρ)]
        linear_combination h
      have hk : Fr.logCoeff (k + 2) k
          = (((k : K) + 3) * ((k : K) + 2) * ((k : K) + 1) / 6 * (Fr.logConst b 1 - b ^ 2 / 2)
            + ((k : K) + 3) * ((k : K) + 2) * ((k : K) + 2) * ((k : K) + 1) / 8 * b ^ 2)
            / Fr.ρ ^ (k + 1) := by
        rw [eq_div_iff (pow_ne_zero _ hρ), mul_comm]
        exact ih
      rw [show k + 1 + 2 = (k + 2) + 1 from rfl, logCoeff_succ_succ, hk, hsub,
        Fr.dK_div (pow_ne_zero _ hρ), Fr.dK_mul, dK_natCast,
        show k + 2 = (k + 1) + 1 from rfl, Fr.dK_pow_succ, hdρ, hdb, Nat.cast_choose_two]
      push_cast
      field_simp
      ring

/-! ### The rescaled tower as a polynomial family -/

/-- The affine tower, rescaled by weights, as a polynomial family in a parameter `ν`:
`x_j ↦ ∑_i ν^{j−i} ρ^{i+1} a_{j,i}·x_i + ν^{j+1} b_j`.  Its last row is the tower defect. -/
def towerFamily (b : K) (n : ℕ) (j : Fin (n + 1)) : Polynomial (MvPolynomial (Fin (n + 1)) K) :=
  (∑ i : Fin (n + 1), Polynomial.monomial ((j : ℕ) - i)
      (C (Fr.ρ ^ ((i : ℕ) + 1) * Fr.logCoeff j i) * X i))
    + Polynomial.monomial ((j : ℕ) + 1) (C (Fr.logConst b j))

theorem towerFamily_coeff_zero (b : K) (n : ℕ) (j : Fin (n + 1)) :
    (Fr.towerFamily b n j).coeff 0 = X j := by
  classical
  have hρ := Fr.ρ_ne
  simp only [towerFamily, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, if_neg (Nat.succ_ne_zero _), add_zero]
  rw [Finset.sum_eq_single j]
  · rw [Nat.sub_self, if_pos rfl, Fr.logCoeff_diag, mul_inv_cancel₀ (pow_ne_zero _ hρ), C_1,
      one_mul]
  · intro i _ hij
    split_ifs with h
    · have hlt : (j : ℕ) < i := by
        have : (i : ℕ) ≠ j := fun h' => hij (Fin.ext h')
        omega
      rw [Fr.logCoeff_eq_zero_of_lt _ _ hlt, mul_zero, C_0, zero_mul]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem towerFamily_coeff_one {b : K} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (n : ℕ)
    (j : Fin (n + 1)) :
    (Fr.towerFamily b n j).coeff 1 = C b * connectionGenValue K (n + 1) 1 j := by
  classical
  simp only [towerFamily, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
  · rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega)]), h0, if_pos rfl, zero_add,
      connectionGenValue_of_succ_eq (by omega), mul_one]
    rfl
  · have hi : (j : ℕ) - 1 < n + 1 := by omega
    set i₀ : Fin (n + 1) := ⟨(j : ℕ) - 1, hi⟩ with hi₀
    have hi₀v : (i₀ : ℕ) = (j : ℕ) - 1 := rfl
    have hsum : (∑ i : Fin (n + 1), if (j : ℕ) - (i : ℕ) = 1 then
          C (Fr.ρ ^ ((i : ℕ) + 1) * Fr.logCoeff j i) * X i else 0)
        = C (Fr.ρ ^ ((i₀ : ℕ) + 1) * Fr.logCoeff j i₀) * X i₀ := by
      rw [Finset.sum_eq_single i₀]
      · rw [if_pos (by rw [hi₀v]; omega)]
      · intro i _ hij
        rw [if_neg]
        intro h
        exact hij (Fin.ext (by rw [hi₀v]; omega))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum, if_neg (show ¬ ((j : ℕ) + 1 = 1) by omega), add_zero,
      connectionGenValue_of_le (show 1 ≤ (j : ℕ) by omega)]
    have h := Fr.pow_mul_logCoeff_subdiag_seed hb ((j : ℕ) - 1)
    rw [show (j : ℕ) - 1 + 1 = (j : ℕ) by omega] at h
    rw [hi₀v, show (j : ℕ) - 1 + 1 = (j : ℕ) by omega, h, connectionJetVar, dif_pos hi,
      show (j : ℕ) - 1 + 2 = (j : ℕ) + 1 by omega, C_mul, hi₀, show (1 + 1 : ℕ) = 2 from rfl]
    ring

theorem towerFamily_coeff_two_of_le (b : K) (n : ℕ) (j : Fin (n + 1)) (hj : 2 ≤ (j : ℕ)) :
    (Fr.towerFamily b n j).coeff 2
      = C (Fr.ρ ^ ((j : ℕ) - 1) * Fr.logCoeff j ((j : ℕ) - 2))
          * connectionJetVar K (n + 1) ((j : ℕ) - 2) := by
  classical
  simp only [towerFamily, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  have hi : (j : ℕ) - 2 < n + 1 := by omega
  set i₀ : Fin (n + 1) := ⟨(j : ℕ) - 2, hi⟩ with hi₀
  have hi₀v : (i₀ : ℕ) = (j : ℕ) - 2 := rfl
  rw [Finset.sum_eq_single i₀, if_pos (by rw [hi₀v]; omega),
    if_neg (show ¬ ((j : ℕ) + 1 = 2) by omega), add_zero, hi₀v,
    show (j : ℕ) - 2 + 1 = (j : ℕ) - 1 by omega, connectionJetVar, dif_pos hi]
  · intro i _ hij
    rw [if_neg]
    intro h
    exact hij (Fin.ext (by rw [hi₀v]; omega))
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem towerFamily_coeff_two_of_eq_one (b : K) (n : ℕ) (j : Fin (n + 1)) (hj : (j : ℕ) = 1) :
    (Fr.towerFamily b n j).coeff 2 = C (Fr.logConst b 1) := by
  classical
  simp only [towerFamily, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega)]), hj, if_pos rfl, zero_add]

theorem towerFamily_coeff_two_of_eq_zero (b : K) (n : ℕ) (j : Fin (n + 1)) (hj : (j : ℕ) = 0) :
    (Fr.towerFamily b n j).coeff 2 = 0 := by
  classical
  simp only [towerFamily, Polynomial.coeff_add, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  rw [Finset.sum_eq_zero (fun i _ => by rw [if_neg (by omega)]), hj, if_neg (by omega), add_zero]

/-- **The first-order derivation of the rescaled tower is `b₀·ξ₁`.** -/
theorem familyDerivOne_towerFamily {b : K} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (n : ℕ) :
    familyDerivOne (Fr.towerFamily_coeff_zero b n) = b • connectionGen K (n + 1) 1 := by
  refine derivation_ext fun j => ?_
  rw [familyDerivOne_X, Fr.towerFamily_coeff_one hb, Derivation.smul_apply, connectionGen_X,
    smul_eq_C_mul]

theorem cast_choose_three [CharZero K] (m : ℕ) :
    (((m + 3).choose 3 : ℕ) : K) = ((m : K) + 3) * ((m : K) + 2) * ((m : K) + 1) / 6 := by
  have h := Nat.add_one_mul_choose_eq (m + 2) 2
  have h' := congrArg (Nat.cast : ℕ → K) h
  push_cast at h'
  rw [Nat.cast_choose_two] at h'
  push_cast at h'
  rw [eq_div_iff (by norm_num : (6 : K) ≠ 0)]
  linear_combination -2 * h'

/-- **The second-order derivation of the rescaled tower is `(b₁ − b₀²/2)·ξ₂`.** -/
theorem familyDerivTwo_towerFamily [CharZero K] {b : K} (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2)
    (n : ℕ) :
    familyDerivTwo (Fr.towerFamily_coeff_zero b n)
      = (Fr.logConst b 1 - b ^ 2 / 2) • connectionGen K (n + 1) 2 := by
  refine derivation_ext fun j => ?_
  rw [familyDerivTwo_X, Fr.towerFamily_coeff_one hb, derivation_C_mul_eq,
    Fr.familyDerivOne_towerFamily hb, Derivation.smul_apply, Derivation.smul_apply,
    connectionGen_X, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
  rcases Nat.lt_trichotomy (j : ℕ) 1 with h0 | h1 | h2
  · have h0' : (j : ℕ) = 0 := by omega
    rw [Fr.towerFamily_coeff_two_of_eq_zero b n j h0',
      connectionGenValue_of_succ_eq (k := 1) (by omega), Derivation.map_one_eq_zero,
      connectionGenValue_of_lt (k := 2) (by omega)]
    simp
  · rw [Fr.towerFamily_coeff_two_of_eq_one b n j h1,
      connectionGenValue_of_le (k := 1) (by omega), derivation_C_mul_eq,
      connectionGen_jetVar _ (by omega), connectionGenValue_of_succ_eq (k := 1) (by omega),
      connectionGenValue_of_succ_eq (k := 2) (by omega), h1, Nat.choose_self]
    simp only [Nat.cast_one, C_1, mul_one]
    rw [← C_mul, ← C_mul, ← map_sub]
    congr 1
    ring
  · obtain ⟨k, hk⟩ : ∃ k, (j : ℕ) = k + 2 := ⟨(j : ℕ) - 2, by omega⟩
    rw [Fr.towerFamily_coeff_two_of_le b n j (by omega),
      connectionGenValue_of_le (k := 1) (by omega), derivation_C_mul_eq,
      connectionGen_jetVar _ (by omega), connectionGenValue_of_le (k := 1) (by omega),
      connectionGenValue_of_le (k := 2) (by omega), hk,
      show k + 2 - 1 - 1 = k by omega, show k + 2 - 2 = k by omega,
      show k + 2 - 1 = k + 1 by omega]
    simp only [← mul_assoc, ← C_mul]
    rw [← sub_mul, ← map_sub]
    congr 1
    have hA := Fr.pow_mul_logCoeff_subsubdiag_seed hb k
    rw [hA, show k + 2 + 1 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
      show (1 + 1 : ℕ) = 2 from rfl, show (2 + 1 : ℕ) = 3 from rfl, cast_choose_three,
      Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    congr 1
    ring

/-! ### Invariance of the rescaled family -/

/-- With shift-fixed coefficients the tower shift is plain substitution. -/
theorem towerShift_eq_aeval_of_fixed (b : K) {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F) :
    Fr.towerShift b n F = aeval (Fr.towerSub b n) F := by
  rw [towerShift, coe_eval₂Hom, aeval_def, algebraMap_eq, eval₂_eq, eval₂_eq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [RingHom.comp_apply, hψ d]

/-- The weight scaling `x_j ↦ c^{j+1} x_j`. -/
def jetWeightScale (n : ℕ) (c : K) : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun i : Fin n => C (c ^ ((i : ℕ) + 1)) * X i

theorem jetWeightScale_of_weightedHomogeneous {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F) (c : K) :
    jetWeightScale n c F = C (c ^ (n + 1)) * F := by
  have hw : IsWeightedHomogeneous (jetWeight n) F (n + 1) := by
    rw [hF]
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _
  exact aeval_weight_scaling (jetWeight n) hw c

/-- A row of the tower substitution: `∑_i a_{r,i} x_i + b_r`. -/
def towerRow (b : K) (n r : ℕ) : MvPolynomial (Fin n) K :=
  (∑ i : Fin n, C (Fr.logCoeff r (i : ℕ)) * X i) + C (Fr.logConst b r)

theorem towerSub_eq_towerRow (b : K) (n : ℕ) (j : Fin n) :
    Fr.towerSub b n j = Fr.towerRow b n j := rfl

theorem defectPoly_eq_towerRow (b : K) (n : ℕ) : Fr.defectPoly b n = Fr.towerRow b n n := rfl

/-- **The rescaled family is the rescaled tower row.** -/
theorem eval_towerFamily (b : K) (n : ℕ) (J : Fin (n + 1)) {μ : K} (hμ : μ ≠ 0) :
    (Fr.towerFamily b n J).eval (C μ)
      = rename Fin.castSucc
          (C (μ ^ ((J : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n J))
        + C (Fr.ρ ^ (n + 1) * Fr.logCoeff J n) * X (Fin.last n) := by
  have hρ := Fr.ρ_ne
  simp only [towerFamily, towerRow, jetWeightScale, Polynomial.eval_add, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, map_add, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    rename_C, rename_X, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, mul_add,
    Finset.mul_sum]
  have hA : ∀ x : Fin n,
      C (Fr.ρ ^ ((x : ℕ) + 1)) * C (Fr.logCoeff J x) * X (Fin.castSucc x) * C μ ^ ((J : ℕ) - x)
        = C (μ ^ ((J : ℕ) + 1)) * (C (Fr.logCoeff J x) * (C ((Fr.ρ / μ) ^ ((x : ℕ) + 1))
          * X (Fin.castSucc x))) := by
    intro x
    rcases Nat.lt_or_ge (J : ℕ) (x : ℕ) with h | h
    · rw [Fr.logCoeff_eq_zero_of_lt _ _ h]
      simp
    · obtain ⟨t, ht⟩ : ∃ t, (J : ℕ) = (x : ℕ) + t := ⟨(J : ℕ) - x, by omega⟩
      have key : Fr.ρ ^ ((x : ℕ) + 1) * Fr.logCoeff ((x : ℕ) + t) x * μ ^ t
          = μ ^ ((x : ℕ) + t + 1) * (Fr.logCoeff ((x : ℕ) + t) x * (Fr.ρ / μ) ^ ((x : ℕ) + 1)) := by
        rw [div_pow]
        field_simp
        ring
      rw [ht, show (x : ℕ) + t - x = t by omega, ← map_pow,
        mul_right_comm _ (X (Fin.castSucc x)), ← C_mul, ← C_mul, ← mul_assoc, ← mul_assoc,
        ← C_mul, ← C_mul, key, mul_assoc]
  have hB : C (Fr.ρ ^ (n + 1)) * C (Fr.logCoeff J n) * X (Fin.last n) * C μ ^ ((J : ℕ) - n)
      = C (Fr.ρ ^ (n + 1)) * C (Fr.logCoeff J n) * X (Fin.last n) := by
    rcases Nat.lt_or_ge (J : ℕ) n with h | h
    · rw [Fr.logCoeff_eq_zero_of_lt _ _ h]
      simp
    · rw [show (J : ℕ) - n = 0 by omega, pow_zero, mul_one]
  rw [Finset.sum_congr rfl fun x _ => hA x, hB, ← map_pow, mul_comm (C (Fr.logConst b J))]
  ring

theorem jetWeightScale_C {n : ℕ} (c a : K) : jetWeightScale n c (C a) = C a := by
  rw [jetWeightScale, aeval_C, algebraMap_eq]

/-- **The collapse, conjugated by the weight scalings.**  Substituting the rescaled tower rows into
a weighted homogeneous collapsing polynomial returns the polynomial plus the rescaled defect. -/
theorem aeval_rescaledTowerRow (b : K) {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F)
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F)
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n)
    {μ : K} (hμ : μ ≠ 0) :
    aeval (fun j : Fin n =>
        C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j)) F
      = F + C (μ ^ (n + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n n) := by
  have hρ := Fr.ρ_ne
  have hcomp : (aeval fun j : Fin n =>
        C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j))
      = (jetWeightScale n (Fr.ρ / μ)).comp
          ((aeval (Fr.towerSub b n)).comp (jetWeightScale n μ)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hws : jetWeightScale n μ (X j) = C (μ ^ ((j : ℕ) + 1)) * X j := by
      rw [jetWeightScale, aeval_X]
    rw [aeval_X, AlgHom.comp_apply, AlgHom.comp_apply, hws, map_mul, aeval_C, algebraMap_eq,
      aeval_X, map_mul, jetWeightScale_C, towerSub_eq_towerRow]
  have hsub : aeval (Fr.towerSub b n) F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n := by
    rw [← Fr.towerShift_eq_aeval_of_fixed b hψ, hpoly]
  rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, jetWeightScale_of_weightedHomogeneous hF,
    map_mul,
    aeval_C, algebraMap_eq, hsub, map_mul, map_add, map_mul, jetWeightScale_C, jetWeightScale_C,
    jetWeightScale_of_weightedHomogeneous hF, defectPoly_eq_towerRow, mul_add, ← mul_assoc,
    ← mul_assoc, ← C_mul, ← C_mul]
  congr 1
  have hscal : μ ^ (n + 1) * (Fr.ρ ^ (n + 1))⁻¹ * (Fr.ρ / μ) ^ (n + 1) = 1 := by
    rw [div_pow]
    field_simp
  rw [hscal, C_1, one_mul]

/-- **Invariance of the top-jet graph under the rescaled family.** -/
theorem towerFamily_invariant (b : K) {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F)
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F)
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n)
    {μ : K} (hμ : μ ≠ 0) :
    aeval (fun J => (Fr.towerFamily b n J).eval (C μ))
        (X (Fin.last n) - rename Fin.castSucc F)
      = X (Fin.last n) - rename Fin.castSucc F := by
  have hρ := Fr.ρ_ne
  set N : Fin n → MvPolynomial (Fin n) K :=
    fun j => C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j) with hN
  have hcast : (fun J => (Fr.towerFamily b n J).eval (C μ)) ∘ Fin.castSucc
      = fun j : Fin n => rename Fin.castSucc (N j) := by
    funext j
    simp only [Function.comp_apply]
    rw [Fr.eval_towerFamily b n _ hμ, Fin.val_castSucc, Fr.logCoeff_eq_zero_of_lt _ _ j.isLt,
      mul_zero, C_0, zero_mul, add_zero]
  have hren : aeval (fun j : Fin n => rename Fin.castSucc (N j)) F
      = rename Fin.castSucc (aeval N F) := by
    have h := MvPolynomial.comp_aeval N
      (rename Fin.castSucc : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K)
    exact (congrArg (fun f => f F) h).symm
  rw [map_sub, aeval_X, aeval_rename, hcast, hren, Fr.eval_towerFamily b n _ hμ, Fin.val_last,
    Fr.logCoeff_diag, mul_inv_cancel₀ (pow_ne_zero _ hρ), C_1, one_mul, hN,
    Fr.aeval_rescaledTowerRow b hψ hF hpoly hμ, map_add]
  ring

/-! ### The residual is impossible -/

/-- **The scale-invariant residual of the affine tower is impossible.**  If the seed constant
`b₀ = −(dρ)/ρ²` is nonzero (the map is not affine) and `b₁ ≠ b₀²/2` (the Schwarzian of the map is
nonzero), no weighted homogeneous polynomial of weight `n + 1` with shift-fixed coefficients solves
the collapse identity of the affine logarithmic tower. -/
theorem false_of_scaleInvariant_collapse [CharZero K] {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    {n : ℕ} {F : MvPolynomial (Fin n) K}
    (hF : F = weightedHomogeneousComponent (jetWeight n) (n + 1) F)
    (hψ : ∀ d, Fr.ψ (coeff d F) = coeff d F)
    (hpoly : Fr.towerShift b n F = C ((Fr.ρ ^ (n + 1))⁻¹) * F + Fr.defectPoly b n) : False := by
  set Φ : MvPolynomial (Fin (n + 1)) K := X (Fin.last n) - rename Fin.castSucc F with hΦ
  have hinf : {μ : K | aeval (fun J => (Fr.towerFamily b n J).eval (C μ)) Φ = Φ}.Infinite :=
    Set.Infinite.mono (fun μ hμ => Fr.towerFamily_invariant b hψ hF hpoly hμ)
      (Set.finite_singleton (0 : K)).infinite_compl
  have hinv := familySubst_eq_C_of_infinite hinf
  obtain ⟨h1, h2⟩ := familyDeriv_eq_zero_of_eq_C (Fr.towerFamily_coeff_zero b n) hinv
  rw [Fr.familyDerivOne_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h1
  rw [Fr.familyDerivTwo_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h2
  exact not_connectionGen_invariant_graph F
    ⟨h1.resolve_left hb0, h2.resolve_left (sub_ne_zero.mpr hS)⟩

end RittFrame

end

end GaloisForLFunctions.HTGeometry
