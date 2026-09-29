import GaloisForLFunctions.HTGeometry.RittEigenPowerLineIdentity

/-!
# The normal forms of an algebraic eigen-coordinate

Let `v^M = Q(u, du, …)` with `M ≥ 1` minimal and `Q(x + s·B(x)) = Q(x) + κ·s^M` (the line
identity).  Then:

* **Weights.**  The line substitution commutes with the weight scalings, so `Q(λx) − λ^M Q(x)` is
  constant along the lines, hence constant: `Q = q₀ + Q_M` with `Q_M` weighted homogeneous of
  weight `M`.  Its coefficients are shift-fixed (top layer of `towerShift Q = ρ^{−M}Q`).
* **`M ≥ 3` is impossible.**  After the weight rescaling the constant `q₀` enters the substitution
  family only at order `ν^M`, so `z²∂` and `z³∂` kill `Q_M`; they generate every `z^{k+1}∂`, which
  are unitriangular on the jet coordinates, so `Q_M` is constant, hence zero.
* **`M = 1`:** `v = α·u + q₀`, i.e. `u − α⁻¹v` lies in the base.
* **`M = 2`:** the first-order term of the line identity forces `Q_M = α(x₀² − 2x₁)`, i.e.
  `d u − u²/2 = q₀/(2α) − v²/(2α)`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K' : Type*} [Field K']

/-! ### Monomials of small weight -/

theorem weight_eq_sum_univ {n : ℕ} (e : Fin n →₀ ℕ) :
    Finsupp.weight (RittFrame.jetWeight n) e = ∑ j : Fin n, e j * ((j : ℕ) + 1) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
  simp [RittFrame.jetWeight, smul_eq_mul]

theorem jetWeight_le_weight {n : ℕ} (e : Fin n →₀ ℕ) (j : Fin n) :
    e j * ((j : ℕ) + 1) ≤ Finsupp.weight (RittFrame.jetWeight n) e := by
  rw [weight_eq_sum_univ]
  exact Finset.single_le_sum (f := fun i : Fin n => e i * ((i : ℕ) + 1))
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

theorem eq_monomial_of_coeff {K σ : Type*} [CommSemiring K] {P : MvPolynomial σ K}
    {s : σ →₀ ℕ} (h : ∀ e, coeff e P ≠ 0 → e = s) : P = monomial s (coeff s P) := by
  classical
  ext e
  rw [coeff_monomial]
  by_cases he : s = e
  · rw [if_pos he, he]
  · rw [if_neg he]
    by_contra hne
    exact he (h e hne).symm

theorem eq_monomial_add_of_coeff {K σ : Type*} [CommSemiring K] {P : MvPolynomial σ K}
    {s t : σ →₀ ℕ} (hst : s ≠ t) (h : ∀ e, coeff e P ≠ 0 → e = s ∨ e = t) :
    P = monomial s (coeff s P) + monomial t (coeff t P) := by
  classical
  ext e
  rw [coeff_add, coeff_monomial, coeff_monomial]
  by_cases hs : s = e
  · rw [if_pos hs, if_neg (fun ht => hst (hs.trans ht.symm)), add_zero, hs]
  · by_cases ht : t = e
    · rw [if_neg hs, if_pos ht, zero_add, ht]
    · rw [if_neg hs, if_neg ht, add_zero]
      by_contra hne
      rcases h e hne with h' | h'
      · exact hs h'.symm
      · exact ht h'.symm

/-- The only monomial of weight one is `x₀`. -/
theorem eq_single_zero_of_weight_eq_one {n : ℕ} (hn : 0 < n) {e : Fin n →₀ ℕ}
    (he : Finsupp.weight (RittFrame.jetWeight n) e = 1) :
    e = Finsupp.single ⟨0, hn⟩ 1 := by
  classical
  have hj : ∀ j : Fin n, (j : ℕ) ≠ 0 → e j = 0 := by
    intro j hj
    have := jetWeight_le_weight e j
    rw [he] at this
    by_contra h
    have : 1 * 2 ≤ e j * ((j : ℕ) + 1) :=
      Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr h) (by omega)
    omega
  have hsum := he
  rw [weight_eq_sum_univ, Finset.sum_eq_single ⟨0, hn⟩ (fun j _ hj0 => by
    rw [hj j (fun h => hj0 (Fin.ext h)), zero_mul]) (fun h => absurd (Finset.mem_univ _) h)]
    at hsum
  ext j
  by_cases hj0 : (j : ℕ) = 0
  · have hj' : j = ⟨0, hn⟩ := Fin.ext hj0
    subst hj'
    rw [Finsupp.single_eq_same]
    simpa using hsum
  · rw [hj j hj0, Finsupp.single_eq_of_ne (fun h => hj0 (by rw [h]))]

/-- A weighted homogeneous polynomial of weight one is a multiple of `x₀`. -/
theorem eq_C_mul_X_of_isWeightedHomogeneous_one {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    {P : MvPolynomial (Fin n) K} (hP : IsWeightedHomogeneous (RittFrame.jetWeight n) P 1) :
    P = C (coeff (Finsupp.single ⟨0, hn⟩ 1) P) * X ⟨0, hn⟩ := by
  rw [C_mul_X_eq_monomial]
  exact eq_monomial_of_coeff fun e he => eq_single_zero_of_weight_eq_one hn (hP he)

/-- The monomials of weight two are `x₀²` and `x₁`. -/
theorem mem_of_weight_eq_two {n : ℕ} (hn : 1 < n) {e : Fin n →₀ ℕ}
    (hw : Finsupp.weight (RittFrame.jetWeight n) e = 2) :
    e = Finsupp.single ⟨0, by omega⟩ 2 ∨ e = Finsupp.single ⟨1, hn⟩ 1 := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, hn⟩ with hi1
  have hj : ∀ j : Fin n, 2 ≤ (j : ℕ) → e j = 0 := by
    intro j hj
    have := jetWeight_le_weight e j
    rw [hw] at this
    by_contra h
    have : 1 * 3 ≤ e j * ((j : ℕ) + 1) :=
      Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr h) (by omega)
    omega
  have hsum := hw
  rw [weight_eq_sum_univ] at hsum
  have hsplit : ∑ j : Fin n, e j * ((j : ℕ) + 1) = e i0 * 1 + e i1 * 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ {i0, i1}) (fun j _ hj' => by
      rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hj'
      rw [hj j (by
        have h0 : (j : ℕ) ≠ 0 := fun h => hj'.1 (Fin.ext h)
        have h1 : (j : ℕ) ≠ 1 := fun h => hj'.2 (Fin.ext h)
        omega), zero_mul])]
    rw [Finset.sum_pair (fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi1]))]
  rw [hsplit] at hsum
  have hrest : ∀ j : Fin n, j ≠ i0 → j ≠ i1 → e j = 0 := by
    intro j h0 h1
    refine hj j ?_
    have h0' : (j : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
    have h1' : (j : ℕ) ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  have hi01 : i0 ≠ i1 := fun h => absurd (congrArg Fin.val h) (by simp [hi0, hi1])
  rcases Nat.lt_or_ge (e i1) 1 with h | h
  · left
    ext j
    by_cases hj0 : j = i0
    · subst hj0; rw [Finsupp.single_eq_same]; omega
    · rw [Finsupp.single_eq_of_ne hj0]
      by_cases hj1 : j = i1
      · subst hj1; omega
      · exact hrest j hj0 hj1
  · right
    ext j
    by_cases hj1 : j = i1
    · subst hj1; rw [Finsupp.single_eq_same]; omega
    · rw [Finsupp.single_eq_of_ne hj1]
      by_cases hj0 : j = i0
      · subst hj0; omega
      · exact hrest j hj0 hj1

/-- A weighted homogeneous polynomial of weight two is `α x₀² + β x₁`. -/
theorem eq_of_isWeightedHomogeneous_two {K : Type*} [Field K] {n : ℕ} (hn : 1 < n)
    {P : MvPolynomial (Fin n) K} (hP : IsWeightedHomogeneous (RittFrame.jetWeight n) P 2) :
    P = C (coeff (Finsupp.single ⟨0, by omega⟩ 2) P) * X ⟨0, by omega⟩ ^ 2
      + C (coeff (Finsupp.single ⟨1, hn⟩ 1) P) * X ⟨1, hn⟩ := by
  have hst : Finsupp.single (⟨0, by omega⟩ : Fin n) 2 ≠ Finsupp.single ⟨1, hn⟩ 1 := by
    intro h
    have := congrArg (fun e : Fin n →₀ ℕ => e ⟨0, by omega⟩) h
    simp only [Finsupp.single_eq_same] at this
    rw [Finsupp.single_eq_of_ne (fun h' => absurd (congrArg Fin.val h') (by simp))] at this
    omega
  rw [C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial]
  exact eq_monomial_add_of_coeff hst fun e he => mem_of_weight_eq_two hn (hP he)

/-- A weighted homogeneous polynomial of weight two in one jet variable is `α x₀²`. -/
theorem eq_of_isWeightedHomogeneous_two_one {K : Type*} [Field K]
    {P : MvPolynomial (Fin 1) K} (hP : IsWeightedHomogeneous (RittFrame.jetWeight 1) P 2) :
    P = C (coeff (Finsupp.single 0 2) P) * X 0 ^ 2 := by
  rw [C_mul_X_pow_eq_monomial]
  refine eq_monomial_of_coeff fun e he => ?_
  have hw := hP he
  rw [weight_eq_sum_univ, Fin.sum_univ_one] at hw
  refine Finsupp.ext fun j => ?_
  rw [Subsingleton.elim j 0, Finsupp.single_eq_same]
  simpa using hw

/-! ### Unitriangularity of the connection generators -/

/-- **The generators `z^{k+1}∂`, `k ≥ 1`, have no common nonconstant invariant.** -/
theorem pderiv_eq_zero_of_connectionGen [CharZero K'] {N : ℕ} {Φ : MvPolynomial (Fin N) K'}
    (h : ∀ k : ℕ, 1 ≤ k → connectionGen K' N k Φ = 0) : ∀ j : Fin N, pderiv j Φ = 0 := by
  classical
  have hexp : ∀ k, connectionGen K' N k Φ = ∑ i, pderiv i Φ * connectionGenValue K' N k i := by
    intro k
    have := derivation_aeval_eq_sum_pderiv (connectionGen K' N k) X Φ
    simpa [aeval_X_left_apply, connectionGen_X] using this
  have key : ∀ m : ℕ, ∀ j : Fin N, N - (j : ℕ) = m → pderiv j Φ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro j hj
    have hk := h ((j : ℕ) + 1) (by omega)
    rw [hexp, Finset.sum_eq_single j] at hk
    · rwa [connectionGenValue_of_succ_eq rfl, mul_one] at hk
    · intro i _ hij
      rcases Nat.lt_or_ge (i : ℕ) j with hlt | hge
      · rw [connectionGenValue_of_lt (by omega), mul_zero]
      · have hgt : (j : ℕ) < i := lt_of_le_of_ne hge (fun h' => hij (Fin.ext h').symm)
        rw [ih (N - i) (by have := i.isLt; omega) i rfl, zero_mul]
    · intro hj'
      exact absurd (Finset.mem_univ _) hj'
  exact fun j => key _ j rfl

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L) {n : ℕ}

/-! ### Weights of an eigen-power -/

/-- **Weights along the lines.**  Every nonconstant monomial of a polynomial satisfying the line
identity `Q(x + s·B) = Q + κ·s^M` has weight `M`. -/
theorem coeff_eq_zero_of_lineSubst_power [CharZero K] {Q : MvPolynomial (Fin n) K} {κ : K} {M : ℕ}
    (hQ : aeval (triLineSubst (bellField K n)) Q = rename Fin.succ Q + C κ * X 0 ^ M)
    {e : Fin n →₀ ℕ} (he : e ≠ 0) (hw : Finsupp.weight (jetWeight n) e ≠ M) :
    coeff e Q = 0 := by
  set G := jetWeightScale n (2 : K) Q - C ((2 : K) ^ M) * Q with hG
  have hC : lineWeightScale n (2 : K) (C κ) = C κ := by simp [lineWeightScale]
  have hinv : aeval (triLineSubst (bellField K n)) G = rename Fin.succ G := by
    rw [hG, map_sub, aeval_lineSubst_jetWeightScale, map_mul, aeval_C, hQ]
    simp only [map_sub, map_add, map_mul, map_pow, lineWeightScale_X_zero, lineWeightScale_rename,
      rename_C, algebraMap_eq, hC]
    ring
  have hconst := eq_C_of_lineSubst_invariant (isUnitriangularField_connBell K n) hinv
  have hce := congrArg (coeff e) hconst
  rw [coeff_C, if_neg (Ne.symm he), hG, coeff_sub, coeff_jetWeightScale, coeff_C_mul] at hce
  have h2 : (2 : K) ^ (Finsupp.weight (jetWeight n) e) - 2 ^ M ≠ 0 := by
    intro h
    exact hw (two_pow_injective_of_charZero (sub_eq_zero.mp h))
  have : ((2 : K) ^ (Finsupp.weight (jetWeight n) e) - 2 ^ M) * coeff e Q = 0 := by
    rw [sub_mul]
    exact hce
  exact (mul_eq_zero.mp this).resolve_left h2

/-- The evaluation at `s = 0` undoes the line substitution. -/
theorem aeval_zero_lineSubst (P : MvPolynomial (Fin n) K) :
    aeval (Fin.cons (0 : MvPolynomial (Fin n) K) (X : Fin n → MvPolynomial (Fin n) K))
      (aeval (triLineSubst (bellField K n)) P) = P := by
  have h := MvPolynomial.comp_aeval (triLineSubst (bellField K n))
    (aeval (Fin.cons (0 : MvPolynomial (Fin n) K) (X : Fin n → MvPolynomial (Fin n) K)) :
      MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K)
  have := congrArg (fun f => f P) h
  simp only [AlgHom.comp_apply] at this
  rw [this]
  have hid : (fun i => (aeval (Fin.cons (0 : MvPolynomial (Fin n) K)
      (X : Fin n → MvPolynomial (Fin n) K)) : MvPolynomial (Fin (n + 1)) K →ₐ[K] _)
      (triLineSubst (bellField K n) i)) = X := by
    funext i
    simp [triLineSubst]
  rw [hid, aeval_X_left_apply]

theorem aeval_zero_rename_succ (P : MvPolynomial (Fin n) K) :
    aeval (Fin.cons (0 : MvPolynomial (Fin n) K) (X : Fin n → MvPolynomial (Fin n) K))
      (rename Fin.succ P) = P := by
  rw [aeval_rename]
  have : (Fin.cons (0 : MvPolynomial (Fin n) K) (X : Fin n → MvPolynomial (Fin n) K) :
      Fin (n + 1) → MvPolynomial (Fin n) K) ∘ Fin.succ = X := by
    funext i; simp
  rw [this, aeval_X_left_apply]

/-- **The first-order term of the line identity.**  For `M ≥ 2` the line derivative of `Q`
vanishes: `∑_j B_j ∂_j Q = 0`. -/
theorem sum_pderiv_mul_connBell_of_lineSubst_power {Q : MvPolynomial (Fin n) K} {κ : K} {M : ℕ}
    (hM : 2 ≤ M)
    (hQ : aeval (triLineSubst (bellField K n)) Q = rename Fin.succ Q + C κ * X 0 ^ M) :
    ∑ j : Fin n, pderiv j Q * connBell K n j = 0 := by
  classical
  have h := congrArg (pderiv (0 : Fin (n + 1))) hQ
  rw [derivation_aeval_eq_sum_pderiv, map_add, pderiv_zero_rename_succ, zero_add,
    Derivation.leibniz, Derivation.leibniz_pow, pderiv_X_self, pderiv_C] at h
  simp only [pderiv_zero_lineSubst, smul_eq_mul, mul_zero, add_zero] at h
  have h' := congrArg (aeval (Fin.cons (0 : MvPolynomial (Fin n) K)
    (X : Fin n → MvPolynomial (Fin n) K))) h
  rw [map_sum] at h'
  simp only [map_mul, aeval_zero_lineSubst, aeval_zero_rename_succ, map_nsmul, map_pow, aeval_X,
    Fin.cons_zero, aeval_C, mul_one] at h'
  rw [zero_pow (by omega : M - 1 ≠ 0), smul_zero, mul_zero] at h'
  rw [← h']
  rfl

/-! ### An eigen-power of weight at least three -/

/-- **The rescaled eigen-relation.** -/
theorem aeval_rescaledTowerRow_power (b : K) {P : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d P) = coeff d P) {M : ℕ}
    (hP : IsWeightedHomogeneous (jetWeight n) P M) {e : K}
    (hpoly : Fr.towerShift b n P = C ((Fr.ρ ^ M)⁻¹) * P + C e) {μ : K} (hμ : μ ≠ 0) :
    aeval (fun j : Fin n =>
        C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j)) P
      = P + C (μ ^ M * e) := by
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
  have hsub : aeval (Fr.towerSub b n) P = C ((Fr.ρ ^ M)⁻¹) * P + C e := by
    rw [← Fr.towerShift_eq_aeval_of_fixed b hψ, hpoly]
  have hscale : ∀ c : K, jetWeightScale n c P = C (c ^ M) * P :=
    fun c => aeval_weight_scaling _ hP c
  have hscal : μ ^ M * (Fr.ρ ^ M)⁻¹ * (Fr.ρ / μ) ^ M = 1 := by
    rw [div_pow]
    field_simp
  rw [hcomp, AlgHom.comp_apply, AlgHom.comp_apply, hscale, map_mul, aeval_C, algebraMap_eq, hsub,
    map_mul, map_add, map_mul, jetWeightScale_C, jetWeightScale_C, jetWeightScale_C, hscale]
  have hF1 : C (μ ^ M) * (C ((Fr.ρ ^ M)⁻¹) * (C ((Fr.ρ / μ) ^ M) * P)) = P := by
    rw [← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, hscal, C_1, one_mul]
  rw [show C (μ ^ M * e) = C (μ ^ M) * C e from C_mul]
  linear_combination hF1

theorem towerFamily_power (b : K) {P : MvPolynomial (Fin n) K}
    (hψ : ∀ d, Fr.ψ (coeff d P) = coeff d P) {M : ℕ}
    (hP : IsWeightedHomogeneous (jetWeight n) P M) {e : K}
    (hpoly : Fr.towerShift b n P = C ((Fr.ρ ^ M)⁻¹) * P + C e) {μ : K} (hμ : μ ≠ 0) :
    aeval (fun J => (Fr.towerFamily b n J).eval (C μ)) (rename Fin.castSucc P)
      = rename Fin.castSucc P + C (μ ^ M * e) := by
  set N : Fin n → MvPolynomial (Fin n) K :=
    fun j => C (μ ^ ((j : ℕ) + 1)) * jetWeightScale n (Fr.ρ / μ) (Fr.towerRow b n j) with hN
  have hcast : (fun J => (Fr.towerFamily b n J).eval (C μ)) ∘ Fin.castSucc
      = fun j : Fin n => rename Fin.castSucc (N j) := by
    funext j
    simp only [Function.comp_apply]
    rw [Fr.eval_towerFamily b n _ hμ, Fin.val_castSucc, Fr.logCoeff_eq_zero_of_lt _ _ j.isLt,
      mul_zero, C_0, zero_mul, add_zero]
  have hren : aeval (fun j : Fin n => rename Fin.castSucc (N j)) P
      = rename Fin.castSucc (aeval N P) := by
    have h := MvPolynomial.comp_aeval N
      (rename Fin.castSucc : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n + 1)) K)
    exact (congrArg (fun f => f P) h).symm
  rw [aeval_rename, hcast, hren, hN, Fr.aeval_rescaledTowerRow_power b hψ hP hpoly hμ, map_add,
    rename_C]

/-- **An eigen-power of weight at least three is impossible.**  For a map that is neither affine
nor Möbius, a weighted homogeneous polynomial of weight `M ≥ 3` with shift-fixed coefficients and
`towerShift P = ρ^{−M}P + e` vanishes. -/
theorem eq_zero_of_scaleInvariant_power [CharZero K] {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    {M : ℕ} (hM : 3 ≤ M) {P : MvPolynomial (Fin n) K}
    (hP : IsWeightedHomogeneous (jetWeight n) P M)
    (hψ : ∀ d, Fr.ψ (coeff d P) = coeff d P) {e : K}
    (hpoly : Fr.towerShift b n P = C ((Fr.ρ ^ M)⁻¹) * P + C e) : P = 0 := by
  classical
  set Φ : MvPolynomial (Fin (n + 1)) K := rename Fin.castSucc P with hΦ
  have hfam : familySubst (Fr.towerFamily b n) Φ
      = Polynomial.C Φ + Polynomial.monomial M (C e) := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono ?_ (((Set.finite_singleton (0 : K)).infinite_compl).image
      (C_injective (Fin (n + 1)) K).injOn)
    rintro _ ⟨μ, hμ, rfl⟩
    show Polynomial.eval _ _ = Polynomial.eval _ _
    rw [eval_familySubst, Fr.towerFamily_power b hψ hP hpoly hμ, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_monomial, ← map_pow, ← C_mul, mul_comm e]
  have hc1 : (familySubst (Fr.towerFamily b n) Φ).coeff 1 = 0 := by
    rw [hfam, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial,
      if_neg one_ne_zero, if_neg (by omega), add_zero]
  have hc2 : (familySubst (Fr.towerFamily b n) Φ).coeff 2 = 0 := by
    rw [hfam, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_monomial,
      if_neg two_ne_zero, if_neg (by omega), add_zero]
  have h1 : familyDerivOne (Fr.towerFamily_coeff_zero b n) Φ = 0 := by
    rw [familyDerivOne_apply, hc1]
  have h2 : familyDerivTwo (Fr.towerFamily_coeff_zero b n) Φ = 0 := by
    rw [familyDerivTwo_apply, hc2, h1, map_zero, smul_zero, sub_zero]
  rw [Fr.familyDerivOne_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h1
  rw [Fr.familyDerivTwo_towerFamily hb, Derivation.smul_apply, smul_eq_zero] at h2
  have hall := connectionGen_eq_zero_of_one_two (h1.resolve_left hb0)
    (h2.resolve_left (sub_ne_zero.mpr hS))
  have hgrad := pderiv_eq_zero_of_connectionGen hall
  have hΦC := eq_C_of_forall_pderiv_eq_zero' hgrad
  have hPC : P = C (coeff 0 Φ) := by
    apply rename_injective Fin.castSucc (Fin.castSucc_injective n)
    rw [rename_C]
    exact hΦC
  by_contra hne
  have hc : coeff 0 Φ ≠ 0 := by
    intro h0
    rw [h0, C_0] at hPC
    exact hne hPC
  have := hP (show coeff 0 P ≠ 0 by rw [hPC, coeff_C, if_pos rfl]; exact hc)
  simp at this
  omega

theorem connBell_one {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
    connBell K n 1 = X ⟨0, hn⟩ := by
  rw [connBell_succ, connBell_zero, Derivation.map_one_eq_zero, zero_add, mul_one, bellJetZero,
    dif_pos hn]

/-! ### The normal form of an algebraic eigen-coordinate -/

/-- **An algebraic eigen-coordinate.**  If the eigen-coordinate `v` is algebraic over the jet field
of `u`, then a power of `v` lies in the base, or `u + c·v` lies in the base for a shift-fixed `c`,
or the Schwarzian `d u − u²/2` is `γ + κ·v²` with `γ, κ` in the base and `κ` shift-fixed. -/
theorem normalForm_of_isAlgebraic_eigen [CharZero K] [DecidableEq K] {u v : L} {b : K}
    (hb : b = -(Fr.dK Fr.ρ) / Fr.ρ ^ 2) (hb0 : b ≠ 0) (hS : Fr.logConst b 1 ≠ b ^ 2 / 2)
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    (halg : IsAlgebraic ↥(Fr.jetPrefixField u n) v) :
    (∃ M : ℕ, 0 < M ∧ ∃ k : K, v ^ M = algebraMap K L k) ∨
      (∃ c a : K, Fr.ψ c = c ∧ u + algebraMap K L c * v = algebraMap K L a) ∨
      (∃ γ κ : K, Fr.ψ κ = κ ∧
        Fr.d u - u ^ 2 / 2 = algebraMap K L γ + algebraMap K L κ * v ^ 2) := by
  classical
  have hex := Fr.exists_pow_eq_aeval_of_isAlgebraic hu hv hv0 hind halg
  set M := Nat.find hex with hMdef
  obtain ⟨hM, Q, hQ⟩ : 0 < M ∧ ∃ Q : MvPolynomial (Fin n) K,
      v ^ M = aeval (Fr.jetFamily u n) Q := Nat.find_spec hex
  have hmin : ∀ (M' : ℕ) (Q' : MvPolynomial (Fin n) K), 0 < M' → M' < M →
      v ^ M' ≠ aeval (Fr.jetFamily u n) Q' := by
    intro M' Q' hM' hlt heq
    exact Nat.find_min hex hlt ⟨hM', Q', heq⟩
  rcases Fr.triLineSubst_eigenPower hu hv hv0 hdv hind hM hQ hmin with hR | ⟨κ, hline⟩
  · exact Or.inl ⟨M, hM, hR⟩
  -- the weights
  have hzero := fun e (he : e ≠ 0) (hw : Finsupp.weight (jetWeight n) e ≠ M) =>
    coeff_eq_zero_of_lineSubst_power hline he hw
  set q₀ := coeff 0 Q with hq₀
  set Q₁ := Q - C q₀ with hQ₁def
  have hcoeff₁ : ∀ e, coeff e Q₁ = if e = 0 then 0 else coeff e Q := by
    intro e
    by_cases he : e = 0
    · subst he
      rw [if_pos rfl, hQ₁def, coeff_sub, coeff_C, if_pos rfl, hq₀, sub_self]
    · rw [if_neg he, hQ₁def, coeff_sub, coeff_C, if_neg (Ne.symm he), sub_zero]
  have hhom : IsWeightedHomogeneous (jetWeight n) Q₁ M := by
    intro d hd
    rw [hcoeff₁] at hd
    split_ifs at hd with hd0
    · exact absurd rfl hd
    · by_contra hw
      exact hd (hzero d hd0 hw)
  -- the eigen-relation and the shift-fixed coefficients
  have hrel : Fr.σ (aeval (Fr.jetFamily u n) Q)
      = algebraMap K L ((Fr.ρ ^ M)⁻¹) * aeval (Fr.jetFamily u n) Q
        + aeval (Fr.jetFamily u n) (0 : MvPolynomial (Fin n) K) := by
    rw [← hQ, map_zero, add_zero, map_pow, hv, mul_pow, ← map_pow, inv_pow]
  have hpoly : Fr.towerShift b n Q = C ((Fr.ρ ^ M)⁻¹) * Q := by
    have h := Fr.towerShift_eq_of_collapse hu hind hrel
    rwa [add_zero] at h
  have hwle : WLe n Q M := by
    intro e he
    by_cases he0 : e = 0
    · subst he0; simp
    · by_contra hlt
      exact (mem_support_iff.mp he) (hzero e he0 (by omega))
  have hψ₁ : ∀ d, Fr.ψ (coeff d Q₁) = coeff d Q₁ := by
    intro d
    rw [hcoeff₁]
    split_ifs with hd
    · exact map_zero _
    · by_cases hw : Finsupp.weight (jetWeight n) d = M
      · have htop := Fr.coeff_towerShift_of_top b hwle hw
        rw [hpoly, coeff_C_mul] at htop
        have hρM : (Fr.ρ ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ Fr.ρ_ne)
        exact (mul_left_cancel₀ hρM (by rw [htop, mul_comm])).symm
      · rw [hzero d hd hw, map_zero]
  have hpoly₁ : Fr.towerShift b n Q₁ = C ((Fr.ρ ^ M)⁻¹) * Q₁
      + C ((Fr.ρ ^ M)⁻¹ * q₀ - Fr.ψ q₀) := by
    rw [hQ₁def, map_sub, towerShift_C, hpoly,
      show C ((Fr.ρ ^ M)⁻¹ * q₀ - Fr.ψ q₀) = C (Fr.ρ ^ M)⁻¹ * C q₀ - C (Fr.ψ q₀) by
        rw [map_sub, C_mul]]
    ring
  have hQsplit : Q = C q₀ + Q₁ := by rw [hQ₁def]; ring
  have haeval : ∀ P : MvPolynomial (Fin n) K,
      aeval (Fr.jetFamily u n) (C q₀ + P) = algebraMap K L q₀ + aeval (Fr.jetFamily u n) P := by
    intro P; rw [map_add, aeval_C]
  -- `Q₁ = 0` gives a power of `v` in the base
  have hRitt : Q₁ = 0 → ∃ M : ℕ, 0 < M ∧ ∃ k : K, v ^ M = algebraMap K L k := by
    intro h0
    refine ⟨M, hM, q₀, ?_⟩
    rw [hQ, hQsplit, h0, add_zero, aeval_C]
  by_cases hM3 : 3 ≤ M
  · exact Or.inl (hRitt (Fr.eq_zero_of_scaleInvariant_power hb hb0 hS hM3 hhom hψ₁ hpoly₁))
  rcases (show M = 1 ∨ M = 2 by omega) with hM1 | hM2
  · -- `M = 1`: `v = α u + q₀`
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine Or.inl (hRitt ?_)
      ext e
      rw [coeff_zero]
      by_contra hne
      have := hhom hne
      rw [hM1, show e = 0 from Subsingleton.elim _ _] at this
      simp at this
    have hQ₁ := eq_C_mul_X_of_isWeightedHomogeneous_one hn (hM1 ▸ hhom)
    set α := coeff (Finsupp.single ⟨0, hn⟩ 1) Q₁ with hα
    have hv1 : v = algebraMap K L α * u + algebraMap K L q₀ := by
      have h := hQ
      rw [hM1, pow_one, hQsplit, haeval, hQ₁, map_mul, aeval_C, aeval_X] at h
      rw [h]
      simp [jetFamily]
      ring
    by_cases hα0 : α = 0
    · exact Or.inl ⟨1, one_pos, q₀, by rw [pow_one, hv1, hα0, map_zero, zero_mul, zero_add]⟩
    refine Or.inr (Or.inl ⟨-α⁻¹, -(q₀ / α), ?_, ?_⟩)
    · rw [map_neg, map_inv₀, hψ₁]
    · have hαL : algebraMap K L α ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hα0
      rw [hv1, map_neg, map_inv₀, map_neg, map_div₀]
      field_simp
      ring
  · -- `M = 2`: `v² = α(u² − 2 du) + q₀`
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
      · refine Or.inl (hRitt ?_)
        ext e
        rw [coeff_zero]
        by_contra hne
        have := hhom hne
        rw [hM2, show e = 0 from Subsingleton.elim _ _] at this
        simp at this
      · have hQ₁ := eq_of_isWeightedHomogeneous_two_one (hM2 ▸ hhom)
        set α := coeff (Finsupp.single (0 : Fin 1) 2) Q₁ with hα
        have hfirst := sum_pderiv_mul_connBell_of_lineSubst_power (by omega) (hM2 ▸ hline)
        simp only [Fin.sum_univ_one, Fin.val_zero, connBell_zero, mul_one] at hfirst
        have hpd : pderiv 0 Q = C α * (2 * X 0) := by
          rw [hQsplit, map_add, pderiv_C, zero_add, hQ₁, Derivation.leibniz,
            Derivation.leibniz_pow, pderiv_X_self, pderiv_C]
          simp only [smul_eq_mul, mul_zero, add_zero, mul_one, nsmul_eq_mul]
          norm_num
        rw [hpd] at hfirst
        have h2 := congrArg (MvPolynomial.eval (fun _ => (1 : K))) hfirst
        simp only [map_mul, eval_C, map_ofNat, eval_X, mul_one, map_zero] at h2
        have hα0 : α = 0 := (mul_eq_zero.mp h2).resolve_right two_ne_zero
        refine Or.inl (hRitt ?_)
        rw [hQ₁, hα0, C_0, zero_mul]
    have hn' : 1 < n := by omega
    have hQ₁ := eq_of_isWeightedHomogeneous_two hn' (hM2 ▸ hhom)
    set α := coeff (Finsupp.single (⟨0, by omega⟩ : Fin n) 2) Q₁ with hα
    set β := coeff (Finsupp.single (⟨1, hn'⟩ : Fin n) 1) Q₁ with hβ
    have hfirst := sum_pderiv_mul_connBell_of_lineSubst_power (by omega) (hM2 ▸ hline)
    have hβα : β = -2 * α := by
      have h2 := congrArg (MvPolynomial.eval (fun _ => (1 : K))) hfirst
      rw [map_sum, map_zero, hQsplit, hQ₁] at h2
      rw [Finset.sum_eq_add (⟨0, by omega⟩ : Fin n) ⟨1, hn'⟩ (fun h => absurd (congrArg Fin.val h)
        (by simp)) ?_ (fun h => absurd (Finset.mem_univ _) h)
        (fun h => absurd (Finset.mem_univ _) h)] at h2
      · simp only [map_add, map_mul, pderiv_C, zero_add, Derivation.leibniz,
          Derivation.leibniz_pow, pderiv_X, smul_eq_mul, Pi.single_apply] at h2
        rw [connBell_zero, connBell_one (by omega)] at h2
        simp at h2
        linear_combination h2
      · intro j _ hj
        rw [map_mul]
        have hpj : pderiv j (C q₀ + (C α * X (⟨0, by omega⟩ : Fin n) ^ 2
            + C β * X ⟨1, hn'⟩)) = 0 := by
          simp only [map_add, pderiv_C, zero_add, Derivation.leibniz, Derivation.leibniz_pow,
            pderiv_X, smul_eq_mul, Pi.single_apply]
          rw [if_neg (fun h => hj.1 h.symm), if_neg (fun h => hj.2 h.symm)]
          simp
        rw [hpj, map_zero, zero_mul]
    have hv2 : v ^ 2 = algebraMap K L α * u ^ 2 + algebraMap K L β * Fr.d u
        + algebraMap K L q₀ := by
      have h := hQ
      rw [hM2, hQsplit, haeval, hQ₁, map_add, map_mul, map_mul, map_pow, aeval_C, aeval_C,
        aeval_X, aeval_X] at h
      rw [h]
      simp [jetFamily]
      ring
    by_cases hα0 : α = 0
    · refine Or.inl ⟨2, two_pos, q₀, ?_⟩
      rw [hv2, hβα, hα0]
      simp
    refine Or.inr (Or.inr ⟨q₀ / (2 * α), -1 / (2 * α), ?_, ?_⟩)
    · have hψα : Fr.ψ α = α := hψ₁ _
      rw [map_div₀, map_neg, map_one, map_mul, hψα, map_ofNat]
    · have hαL : algebraMap K L α ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hα0
      haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
      rw [hβα] at hv2
      rw [hv2]
      simp only [map_div₀, map_neg, map_one, map_mul, map_ofNat]
      field_simp
      ring

end RittFrame

end

end GaloisForLFunctions.HTGeometry
