import GaloisForLFunctions.HTGeometry.RittEigenPowerRigidity

/-!
# The line identity of an eigen-power

Let `v^M = Q(u, du, …)` with `Q` a polynomial in the algebraically independent jets of the affine
connection `u` and `M ≥ 1` minimal.  For every natural number `c` the connection `u + c·v` solves
the same affine transport equation, so `Q(u + c·v, …)` is again a `ρ^{−M}`-eigenvector and
`Q(u + c·v, …)/v^M` is shift-fixed.

Expanding along the line substitution, `Q(u + c·v, …) = ∑_m (c·v)^m·Q_m(u, …)`, where `Q_m` are the
coefficients of `Q(x + s·B(x))` in `s`.  A polynomial in `c` with coefficients in the extension
whose values at all natural numbers are shift-fixed has shift-fixed coefficients, so every
`v^{m−M}·Q_m(u, …)` lies in the base.  Minimality of `M` kills the coefficients `0 < m < M`, and a
coefficient `m > M` would make `Q` a unit.  Hence either `v^M` lies in the base, or

`Q(x + s·B(x)) = Q(x) + κ·s^M`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Evaluation at `(t, g)` through the splitting of the first variable. -/
theorem aeval_cons_eq_eval_finSuccEquiv {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {n : ℕ} (t : A) (g : Fin n → A) (P : MvPolynomial (Fin (n + 1)) K) :
    aeval (Fin.cons t g) P
      = Polynomial.eval t
          ((finSuccEquiv K n P).map (aeval g : MvPolynomial (Fin n) K →ₐ[K] A)) := by
  have h : (aeval (Fin.cons t g) : MvPolynomial (Fin (n + 1)) K →ₐ[K] A).toRingHom
      = ((Polynomial.evalRingHom t).comp
          (Polynomial.mapRingHom (aeval g : MvPolynomial (Fin n) K →ₐ[K] A).toRingHom)).comp
          (finSuccEquiv K n).toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [finSuccEquiv_apply]
    · refine Fin.cases ?_ (fun j => ?_) i
      · show aeval (Fin.cons t g) (X 0)
          = Polynomial.eval t (Polynomial.map _ (finSuccEquiv K n (X 0)))
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X, aeval_X]
        rfl
      · simp [finSuccEquiv_X_succ]
  exact congrArg (fun f => f P) h

/-- The constant coefficient in the first variable is the evaluation at zero. -/
theorem coeff_zero_finSuccEquiv {K : Type*} [CommRing K] {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) K) :
    (finSuccEquiv K n P).coeff 0 = aeval (Fin.cons 0 X) P := by
  rw [aeval_cons_eq_eval_finSuccEquiv, Polynomial.coeff_zero_eq_eval_zero]
  congr 1
  have : (aeval X : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin n) K) = AlgHom.id K _ :=
    MvPolynomial.algHom_ext fun _ => by simp
  rw [this]
  exact (Polynomial.map_id).symm

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (Fr : RittFrame K L) {n : ℕ}

theorem d_natCast (c : ℕ) : Fr.d (c : L) = 0 := by
  have h : (c : L) = algebraMap K L (c : K) := by simp
  rw [h, Fr.d_base, Fr.dK_natCast, map_zero]

theorem iterate_d_natCast_mul (c : ℕ) (x : L) :
    ∀ k : ℕ, Fr.d^[k] ((c : L) * x) = (c : L) * Fr.d^[k] x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Fr.d_mul,
        Fr.d_natCast, zero_mul, zero_add]

theorem triLineSubst_eval_shift {u v : L} (hdv : Fr.d v = u * v) (c : ℕ) (j : Fin n) :
    aeval (Fin.cons ((c : L) * v) (Fr.jetFamily u n) : Fin (n + 1) → L)
        (triLineSubst (bellField K n) j)
      = Fr.d^[(j : ℕ)] (u + (c : L) * v) := by
  rw [triLineSubst, map_add, map_mul, aeval_X, aeval_X, aeval_rename, Fr.iterate_d_add,
    Fr.iterate_d_natCast_mul]
  have hwsucc : (Fin.cons ((c : L) * v) (Fr.jetFamily u n) : Fin (n + 1) → L) ∘ Fin.succ
      = Fr.jetFamily u n := by
    funext i; simp
  rw [hwsucc, Fr.iterate_d_eq_mul_connBell hdv n j j.isLt.le]
  simp [bellField, jetFamily]
  ring

theorem aeval_lineSubst_shift {u v : L} (hdv : Fr.d v = u * v) (c : ℕ)
    (Q : MvPolynomial (Fin n) K) :
    aeval (Fin.cons ((c : L) * v) (Fr.jetFamily u n) : Fin (n + 1) → L)
        (aeval (triLineSubst (bellField K n)) Q)
      = aeval (Fr.jetFamily (u + (c : L) * v) n) Q := by
  have h := MvPolynomial.comp_aeval (triLineSubst (bellField K n))
    (aeval (Fin.cons ((c : L) * v) (Fr.jetFamily u n)) : MvPolynomial (Fin (n + 1)) K →ₐ[K] L)
  have := congrArg (fun f => f Q) h
  simp only [AlgHom.comp_apply] at this
  rw [this, show (fun i => (aeval (Fin.cons ((c : L) * v) (Fr.jetFamily u n)))
      (triLineSubst (bellField K n) i)) = Fr.jetFamily (u + (c : L) * v) n
    from funext fun j => Fr.triLineSubst_eval_shift hdv c j]

/-- **The line identity of a minimal eigen-power.** -/
theorem triLineSubst_eigenPower [CharZero K] {u v : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hv : Fr.σ v = algebraMap K L Fr.ρ⁻¹ * v) (hv0 : v ≠ 0) (hdv : Fr.d v = u * v)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {M : ℕ} (hM : 0 < M) {Q : MvPolynomial (Fin n) K}
    (hQ : v ^ M = aeval (Fr.jetFamily u n) Q)
    (hmin : ∀ (M' : ℕ) (Q' : MvPolynomial (Fin n) K), 0 < M' → M' < M →
      v ^ M' ≠ aeval (Fr.jetFamily u n) Q') :
    (∃ k : K, v ^ M = algebraMap K L k) ∨
      ∃ κ : K, aeval (triLineSubst (bellField K n)) Q = rename Fin.succ Q + C κ * X 0 ^ M := by
  classical
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  set φ : MvPolynomial (Fin n) K →ₐ[K] L := aeval (Fr.jetFamily u n) with hφ
  have hφinj : Function.Injective φ := hind
  have hvM : v ^ M ≠ 0 := pow_ne_zero _ hv0
  -- the eigen-relation of `Q`
  have hrel : Fr.σ (φ Q) = algebraMap K L (Fr.ρ⁻¹ ^ M) * φ Q + φ 0 := by
    rw [← hQ, map_zero, add_zero, map_pow, hv, mul_pow, map_pow]
  have hpoly : Fr.towerShift b n Q = C (Fr.ρ⁻¹ ^ M) * Q := by
    have h := Fr.towerShift_eq_of_collapse hu hind hrel
    rw [add_zero] at h
    exact h
  -- the shifted connections
  have hσshift : ∀ c : ℕ, Fr.σ (aeval (Fr.jetFamily (u + (c : L) * v) n) Q)
      = algebraMap K L (Fr.ρ⁻¹ ^ M) * aeval (Fr.jetFamily (u + (c : L) * v) n) Q := by
    intro c
    have hcv : Fr.σ ((c : L) * v) = algebraMap K L Fr.ρ⁻¹ * ((c : L) * v) := by
      rw [map_mul, map_natCast, hv]; ring
    have hx := Fr.sigma_add_eigen hu hcv
    have h := Fr.aeval_towerShift hx n Q
    have hj : (fun j : Fin n => Fr.d^[(j : ℕ)] (u + (c : L) * v))
        = Fr.jetFamily (u + (c : L) * v) n := rfl
    rw [hj, hpoly, map_mul, aeval_C] at h
    exact h.symm
  -- the coefficients along the line
  set P := finSuccEquiv K n (aeval (triLineSubst (bellField K n)) Q) with hP
  set g : ℕ → L := fun m => φ (P.coeff m) * v ^ m / v ^ M with hg
  set N := P.natDegree with hN
  set G : Polynomial L := ∑ m ∈ Finset.range (N + 1), Polynomial.monomial m (g m) with hG
  have hGcoeff : ∀ m, G.coeff m = g m := by
    intro m
    rw [hG, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · have : P.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by
        simp only [Finset.mem_range, not_lt] at hm; omega)
      rw [hg]
      simp [this]
  have hGeval : ∀ c : ℕ, G.eval (c : L) = aeval (Fr.jetFamily (u + (c : L) * v) n) Q / v ^ M := by
    intro c
    rw [← Fr.aeval_lineSubst_shift hdv c Q, aeval_cons_eq_eval_finSuccEquiv, ← hP,
      Polynomial.eval_eq_sum_range' (n := N + 1)
        (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _)),
      hG, Polynomial.eval_finsetSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.eval_monomial, Polynomial.coeff_map, hg]
    simp only [AlgHom.coe_toRingHom]
    rw [mul_pow]
    ring
  -- the coefficients are shift-fixed
  have hfixval : ∀ c : ℕ, Fr.σ (G.eval (c : L)) = G.eval (c : L) := by
    intro c
    have hρM : algebraMap K L (Fr.ρ⁻¹ ^ M) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K L).injective).mpr (pow_ne_zero _ (inv_ne_zero Fr.ρ_ne))
    rw [hGeval, map_div₀, hσshift c, map_pow Fr.σ v M, hv, mul_pow, ← map_pow]
    rw [mul_div_mul_left _ _ hρM]
  have hGmap : G.map Fr.σ = G := by
    rw [← sub_eq_zero]
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := L)))
    rintro _ ⟨c, rfl⟩
    show Polynomial.IsRoot _ _
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_map]
    have h := Polynomial.hom_eval₂ G (RingHom.id L) Fr.σ (c : L)
    rw [map_natCast, RingHom.comp_id] at h
    rw [← h]
    show Fr.σ (G.eval (c : L)) - G.eval (c : L) = 0
    rw [hfixval c, sub_self]
  have hσg : ∀ m, Fr.σ (g m) = g m := by
    intro m
    have h := congrArg (fun p : Polynomial L => p.coeff m) hGmap
    simp only [Polynomial.coeff_map, hGcoeff] at h
    exact h
  choose κ hκ using fun m => Fr.fixed (g m) (hσg m)
  have hgm : ∀ m, φ (P.coeff m) * v ^ m = algebraMap K L (κ m) * v ^ M := by
    intro m
    have h := hκ m
    rw [hg] at h
    simp only at h
    rw [h, div_mul_cancel₀ _ hvM]
  -- the constant coefficient
  have hP0 : P.coeff 0 = Q := by
    rw [hP, coeff_zero_finSuccEquiv]
    have h := MvPolynomial.comp_aeval (triLineSubst (bellField K n))
      (aeval (Fin.cons (0 : MvPolynomial (Fin n) K) (X : Fin n → MvPolynomial (Fin n) K)) :
        MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin n) K)
    have := congrArg (fun f => f Q) h
    simp only [AlgHom.comp_apply] at this
    rw [this]
    have hid : (fun i => (aeval (Fin.cons (0 : MvPolynomial (Fin n) K)
        (X : Fin n → MvPolynomial (Fin n) K)) : MvPolynomial (Fin (n + 1)) K →ₐ[K] _)
        (triLineSubst (bellField K n) i)) = X := by
      funext i
      simp [triLineSubst]
    rw [hid, aeval_X_left_apply]
  by_cases hR : ∃ k : K, v ^ M = algebraMap K L k
  · exact Or.inl hR
  right
  refine ⟨κ M, ?_⟩
  -- every other coefficient vanishes
  have hPcoeff : ∀ m, P.coeff m = if m = 0 then Q else if m = M then C (κ M) else 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [if_pos rfl, hP0]
    rw [if_neg (by omega)]
    rcases lt_trichotomy m M with hlt | hmM | hgt
    · rw [if_neg (by omega)]
      have hsplit : v ^ M = v ^ m * v ^ (M - m) := by rw [← pow_add]; congr 1; omega
      by_cases hκ0 : κ m = 0
      · have h := hgm m
        rw [hκ0, map_zero, zero_mul] at h
        have hφ : φ (P.coeff m) = 0 :=
          (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hv0)
        exact hφinj (by rw [hφ, map_zero])
      · exfalso
        have hκL : algebraMap K L (κ m) ≠ 0 :=
          (map_ne_zero_iff _ (algebraMap K L).injective).mpr hκ0
        apply hmin (M - m) (C (κ m)⁻¹ * P.coeff m) (by omega) (by omega)
        have h := hgm m
        rw [hsplit] at h
        have hvm : v ^ m ≠ 0 := pow_ne_zero _ hv0
        have h' : φ (P.coeff m) = algebraMap K L (κ m) * v ^ (M - m) :=
          mul_right_cancel₀ hvm (by rw [h]; ring)
        show v ^ (M - m) = φ (C (κ m)⁻¹ * P.coeff m)
        rw [map_mul, hφ, aeval_C, ← hφ, map_inv₀, h', ← mul_assoc, inv_mul_cancel₀ hκL, one_mul]
    · subst hmM
      rw [if_pos rfl]
      have h := hgm m
      have hφ' : φ (P.coeff m) = algebraMap K L (κ m) := mul_right_cancel₀ hvM h
      exact hφinj (by rw [hφ', hφ, aeval_C])
    · rw [if_neg (by omega)]
      by_cases hκ0 : κ m = 0
      · have h := hgm m
        rw [hκ0, map_zero, zero_mul] at h
        have hφ : φ (P.coeff m) = 0 :=
          (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hv0)
        exact hφinj (by rw [hφ, map_zero])
      · exfalso
        apply hR
        have hsplit : v ^ m = v ^ M * v ^ (m - M) := by rw [← pow_add]; congr 1; omega
        have h := hgm m
        rw [hsplit, ← mul_assoc, mul_comm (φ (P.coeff m)) (v ^ M), mul_assoc] at h
        have h1 : φ (P.coeff m) * v ^ (m - M) = algebraMap K L (κ m) :=
          mul_left_cancel₀ hvM (by rw [h, mul_comm])
        -- raise to the power `M`
        have h2 : φ (P.coeff m ^ M * Q ^ (m - M)) = φ (C (κ m ^ M)) := by
          rw [map_mul, map_pow, map_pow, ← hQ, aeval_C, map_pow, ← h1, ← pow_mul, mul_pow,
            ← pow_mul, mul_comm (m - M) M]
        have h3 := hφinj h2
        have hunit : IsUnit Q := by
          have hC : IsUnit (C (κ m ^ M) : MvPolynomial (Fin n) K) :=
            (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hκ0)).map C
          refine isUnit_of_dvd_unit ?_ hC
          rw [← h3]
          refine Dvd.dvd.mul_left (dvd_pow_self Q (by omega)) _
        obtain ⟨q, -, hq⟩ := isUnit_iff_eq_C_of_isReduced.mp hunit
        exact ⟨q, by rw [hQ, hq, aeval_C]⟩
  apply (finSuccEquiv K n).injective
  rw [← hP]
  ext1 m
  rw [hPcoeff m, map_add, map_mul, map_pow, finSuccEquiv_rename_succ, finSuccEquiv_X_zero]
  have hC : finSuccEquiv K n (C (κ M)) = Polynomial.C (C (κ M)) := by
    simp [finSuccEquiv_apply]
  rw [hC, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl, if_pos rfl, if_neg (by omega), mul_zero, add_zero]
  · rw [if_neg hm, if_neg hm, zero_add]
    by_cases hmM : m = M
    · rw [if_pos hmM, if_pos hmM, mul_one]
    · rw [if_neg hmM, if_neg hmM, mul_zero]

end RittFrame

end

end GaloisForLFunctions.HTGeometry
