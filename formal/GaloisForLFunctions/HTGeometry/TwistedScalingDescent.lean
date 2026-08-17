import GaloisForLFunctions.HTGeometry.EigenLogDerivNormalization

/-!
# Coprime descent for a twisted affine substitution

Let `Φ` be a ring endomorphism of a field `K` and let `T` be an affine polynomial with nonzero
linear coefficient.  The operator

`P ↦ (P^Φ) ∘ T`

preserves degrees and multiplies leading coefficients by `Φ` and by the power of the linear
coefficient of `T`.  If a coprime fraction `P/Q` is an eigenvector of the induced map on rational
functions, then coprimality upgrades the cross identity to two separate scalar relations, one for
`P` and one for `Q`, whose scalars are linked by the eigenvalue.

Comparing leading coefficients then produces an eigen-relation for the single field element
`leadingCoeff P / leadingCoeff Q`, with the exponent on the linear coefficient shifted by the
difference of the two degrees.  This is the step that lowers the number of variables in a descent:
the new relation lives in the coefficient field alone.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- Apply a ring endomorphism to the coefficients, then substitute. -/
noncomputable def twistComp (Φ : K →+* K) (T P : Polynomial K) : Polynomial K :=
  (P.map Φ).comp T

@[simp]
theorem twistComp_zero (Φ : K →+* K) (T : Polynomial K) : twistComp Φ T 0 = 0 := by
  simp [twistComp]

theorem natDegree_map_twist (Φ : K →+* K) (P : Polynomial K) :
    (P.map Φ).natDegree = P.natDegree :=
  natDegree_map_eq_of_injective Φ.injective P

theorem coeff_map_twist (Φ : K →+* K) (P : Polynomial K) (j : ℕ) :
    (P.map Φ).coeff j = Φ (P.coeff j) := coeff_map _ _

theorem leadingCoeff_map_twist (Φ : K →+* K) (P : Polynomial K) :
    (P.map Φ).leadingCoeff = Φ P.leadingCoeff := by
  rw [leadingCoeff, leadingCoeff, natDegree_map_twist, coeff_map_twist]

/-- A twisted substitution by an affine polynomial preserves degrees. -/
theorem natDegree_twistComp (Φ : K →+* K) {T : Polynomial K} (hT : T.natDegree = 1)
    (P : Polynomial K) : (twistComp Φ T P).natDegree = P.natDegree := by
  rw [twistComp, natDegree_comp, hT, natDegree_map_twist, mul_one]

/-- The leading coefficient of a twisted affine substitution. -/
theorem leadingCoeff_twistComp (Φ : K →+* K) {T : Polynomial K} (hT : T.natDegree = 1)
    (P : Polynomial K) :
    (twistComp Φ T P).leadingCoeff = Φ P.leadingCoeff * T.leadingCoeff ^ P.natDegree := by
  rw [twistComp, leadingCoeff_comp (by rw [hT]; norm_num), leadingCoeff_map_twist,
    natDegree_map_twist]

theorem twistComp_ne_zero (Φ : K →+* K) {T : Polynomial K} (hT : T.natDegree = 1)
    {P : Polynomial K} (hP : P ≠ 0) : twistComp Φ T P ≠ 0 := by
  have hTl : T.leadingCoeff ≠ 0 := by
    refine leadingCoeff_ne_zero.mpr ?_
    intro h
    rw [h, natDegree_zero] at hT
    exact one_ne_zero hT.symm
  have hPl : Φ P.leadingCoeff ≠ 0 := by
    have : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
    exact fun h => this ((map_eq_zero_iff Φ Φ.injective).mp h)
  refine leadingCoeff_ne_zero.mp ?_
  rw [leadingCoeff_twistComp Φ hT]
  exact mul_ne_zero hPl (pow_ne_zero _ hTl)

theorem twistComp_add (Φ : K →+* K) (T P Q : Polynomial K) :
    twistComp Φ T (P + Q) = twistComp Φ T P + twistComp Φ T Q := by
  simp [twistComp, Polynomial.add_comp]

theorem twistComp_mul (Φ : K →+* K) (T P Q : Polynomial K) :
    twistComp Φ T (P * Q) = twistComp Φ T P * twistComp Φ T Q := by
  simp [twistComp, Polynomial.mul_comp]

theorem twistComp_C (Φ : K →+* K) (T : Polynomial K) (a : K) :
    twistComp Φ T (Polynomial.C a) = Polynomial.C (Φ a) := by
  simp [twistComp]

/-! ## Divisor comparison -/

/-- A nonzero multiple of the same degree differs by a nonzero scalar. -/
theorem eq_C_mul_of_dvd_of_natDegree_eq {P D : Polynomial K} (hD : D ≠ 0) (hdvd : P ∣ D)
    (hdeg : D.natDegree = P.natDegree) : ∃ c : K, c ≠ 0 ∧ D = Polynomial.C c * P := by
  obtain ⟨E, rfl⟩ := hdvd
  have hP : P ≠ 0 := fun h => hD (by rw [h, zero_mul])
  have hE : E ≠ 0 := fun h => hD (by rw [h, mul_zero])
  have hsum : (P * E).natDegree = P.natDegree + E.natDegree := natDegree_mul hP hE
  have hE0 : E.natDegree = 0 := by omega
  refine ⟨E.coeff 0, ?_, ?_⟩
  · intro h
    exact hE (by rw [eq_C_of_natDegree_eq_zero hE0, h, map_zero])
  · rw [← eq_C_of_natDegree_eq_zero hE0, mul_comm]

/-- **Coprimality splits the cross identity.**  An eigen-relation for a coprime fraction under a
twisted affine substitution forces the numerator and the denominator to be separate scalar
eigenvectors, with scalars linked by the eigenvalue. -/
theorem exists_scalars_of_twisted_cross (Φ : K →+* K) {T : Polynomial K} (hT : T.natDegree = 1)
    {P Q : Polynomial K} (hP : P ≠ 0) (hQ : Q ≠ 0) (hcop : IsCoprime P Q)
    {μ ν : K} (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hcross : twistComp Φ T P * Polynomial.C μ * Q
      = Polynomial.C ν * P * twistComp Φ T Q) :
    ∃ c d : K, c ≠ 0 ∧ d ≠ 0 ∧ twistComp Φ T P = Polynomial.C c * P ∧
      twistComp Φ T Q = Polynomial.C d * Q ∧ c * μ = ν * d := by
  have hμ' : (Polynomial.C μ : Polynomial K) ≠ 0 := fun h => hμ (by simpa using h)
  have hν' : (Polynomial.C ν : Polynomial K) ≠ 0 := fun h => hν (by simpa using h)
  have hPT : twistComp Φ T P ≠ 0 := twistComp_ne_zero Φ hT hP
  have hQT : twistComp Φ T Q ≠ 0 := twistComp_ne_zero Φ hT hQ
  -- the numerator
  have hdvdP : P ∣ twistComp Φ T P := by
    have h1 : P ∣ twistComp Φ T P * Polynomial.C μ * Q := by
      rw [hcross]
      exact ⟨Polynomial.C ν * twistComp Φ T Q, by ring⟩
    have h2 : P ∣ twistComp Φ T P * Polynomial.C μ := hcop.dvd_of_dvd_mul_right h1
    obtain ⟨E, hE⟩ := h2
    have hmu : (Polynomial.C μ : Polynomial K) * Polynomial.C μ⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
    refine ⟨Polynomial.C μ⁻¹ * E, ?_⟩
    calc twistComp Φ T P
        = twistComp Φ T P * (Polynomial.C μ * Polynomial.C μ⁻¹) := by rw [hmu, mul_one]
      _ = twistComp Φ T P * Polynomial.C μ * Polynomial.C μ⁻¹ := by ring
      _ = P * E * Polynomial.C μ⁻¹ := by rw [hE]
      _ = P * (Polynomial.C μ⁻¹ * E) := by ring
  obtain ⟨c, hc0, hc⟩ := eq_C_mul_of_dvd_of_natDegree_eq hPT hdvdP (natDegree_twistComp Φ hT P)
  -- the denominator
  have hdvdQ : Q ∣ twistComp Φ T Q := by
    have h1 : Q ∣ Polynomial.C ν * P * twistComp Φ T Q := by
      rw [← hcross]
      exact ⟨twistComp Φ T P * Polynomial.C μ, by ring⟩
    have hcop' : IsCoprime Q (Polynomial.C ν * P) :=
      (isCoprime_mul_unit_left_right (isUnit_C.mpr (Ne.isUnit hν)) _ _).mpr hcop.symm
    exact hcop'.dvd_of_dvd_mul_left h1
  obtain ⟨d, hd0, hd⟩ := eq_C_mul_of_dvd_of_natDegree_eq hQT hdvdQ (natDegree_twistComp Φ hT Q)
  refine ⟨c, d, hc0, hd0, hc, hd, ?_⟩
  rw [hc, hd] at hcross
  have hPQ : (P * Q : Polynomial K) ≠ 0 := mul_ne_zero hP hQ
  have hkey : Polynomial.C (c * μ) * (P * Q) = Polynomial.C (ν * d) * (P * Q) := by
    rw [map_mul, map_mul]
    linear_combination hcross
  have hCeq := mul_right_cancel₀ hPQ hkey
  simpa using congrArg (fun p : Polynomial K => p.coeff 0) hCeq

/-! ## The coefficient relations of a pure scaling -/

/-- Under a pure scaling the twisted substitution acts diagonally on coefficients. -/
theorem coeff_twistComp_scale (Φ : K →+* K) (ρ : K) (P : Polynomial K) (j : ℕ) :
    (twistComp Φ (Polynomial.C ρ * Polynomial.X) P).coeff j = Φ (P.coeff j) * ρ ^ j := by
  rw [twistComp, coeff_comp_C_mul_X, coeff_map_twist, mul_comm]

theorem natDegree_scaleSubst {ρ : K} (hρ : ρ ≠ 0) :
    (Polynomial.C ρ * Polynomial.X : Polynomial K).natDegree = 1 :=
  Polynomial.natDegree_C_mul_X ρ hρ

theorem leadingCoeff_scaleSubst {ρ : K} (hρ : ρ ≠ 0) :
    (Polynomial.C ρ * Polynomial.X : Polynomial K).leadingCoeff = ρ := by
  rw [leadingCoeff, natDegree_scaleSubst hρ, coeff_C_mul, coeff_X_one, mul_one]

/-- **The coefficient eigen-relations of a scaling.**  Every coefficient of a scalar eigenvector
of a twisted scaling is an eigenvector of the twist, with eigenvalue determined by its position. -/
theorem coeff_eigen_of_twistComp_scale (Φ : K →+* K) {ρ c : K} {P : Polynomial K}
    (h : twistComp Φ (Polynomial.C ρ * Polynomial.X) P = Polynomial.C c * P) (j : ℕ) :
    Φ (P.coeff j) * ρ ^ j = c * P.coeff j := by
  have hj := congrArg (fun p : Polynomial K => p.coeff j) h
  simpa only [coeff_twistComp_scale, coeff_C_mul] using hj

/-! ## The affine cocycle -/

theorem twistComp_C_mul_X_pow (Φ : K →+* K) (T : Polynomial K) (u : K) (m : ℕ) :
    twistComp Φ T (Polynomial.C u * Polynomial.X ^ m) = Polynomial.C (Φ u) * T ^ m := by
  rw [twistComp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]

theorem affineSubst_eq (ρ L : K) (hρ : ρ ≠ 0) :
    (Polynomial.C ρ * Polynomial.X + Polynomial.C L : Polynomial K)
      = Polynomial.C ρ * (Polynomial.X + Polynomial.C (L / ρ)) := by
  rw [mul_add, ← Polynomial.C_mul]
  field_simp

theorem coeff_affine_pow (ρ L : K) (hρ : ρ ≠ 0) (m k : ℕ) :
    ((Polynomial.C ρ * Polynomial.X + Polynomial.C L : Polynomial K) ^ m).coeff k
      = ρ ^ k * L ^ (m - k) * (m.choose k : K) := by
  rw [affineSubst_eq ρ L hρ, mul_pow, ← Polynomial.C_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  rcases le_or_gt k m with hk | hk
  · have hsplit : ρ ^ m = ρ ^ (m - k) * ρ ^ k := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_pow, hsplit]
    field_simp
  · rw [Nat.choose_eq_zero_of_lt hk]
    simp

/-- **The affine cocycle, from the two top coefficients.**  Only the two top coefficients of the
relation are used, so the statement applies to a relation that is a scalar multiple of the
polynomial *up to lower-degree terms*. -/
theorem twistComp_affine_cocycle_of_coeff (Φ : K →+* K) {ρ L c : K} (hρ : ρ ≠ 0)
    {P : Polynomial K} {a : ℕ} (hdeg : P.natDegree = a + 1)
    (hcoeff_a : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) P).coeff a
      = c * P.coeff a)
    (hcoeff_a1 : (twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) P).coeff (a + 1)
      = c * P.coeff (a + 1)) :
    Φ (P.coeff a / P.coeff (a + 1))
      = ρ * (P.coeff a / P.coeff (a + 1)) - ((a : K) + 1) * L := by
  classical
  set T : Polynomial K := Polynomial.C ρ * Polynomial.X + Polynomial.C L with hTdef
  have hTdeg : T.natDegree = 1 := natDegree_linear hρ
  have hTpow : ∀ m k : ℕ, (T ^ m).coeff k = ρ ^ k * L ^ (m - k) * (m.choose k : K) := by
    intro m k
    rw [hTdef]
    exact coeff_affine_pow ρ L hρ m k
  have hP0 : P ≠ 0 := by
    intro hh
    rw [hh, Polynomial.natDegree_zero] at hdeg
    omega
  have hlead : P.coeff (a + 1) ≠ 0 := by
    rw [← hdeg]
    exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  set P₂ : Polynomial K :=
    P - Polynomial.C (P.coeff (a + 1)) * Polynomial.X ^ (a + 1)
      - Polynomial.C (P.coeff a) * Polynomial.X ^ a with hP2def
  have hP2 : ∀ j : ℕ, a ≤ j → P₂.coeff j = 0 := by
    intro j hj
    rw [hP2def]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rcases eq_or_lt_of_le hj with rfl | hlt
    · simp
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with heq | hgt
      · rw [← heq]
        simp
      · rw [if_neg (by omega), if_neg (by omega)]
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < j)]
  have hsplit : P = Polynomial.C (P.coeff (a + 1)) * Polynomial.X ^ (a + 1)
      + Polynomial.C (P.coeff a) * Polynomial.X ^ a + P₂ := by
    rw [hP2def]; ring
  have hzero : (twistComp Φ T P₂).coeff a = 0 := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · have hP20 : P₂ = 0 := by
        ext j
        rw [hP2 j (Nat.zero_le j), Polynomial.coeff_zero]
      rw [hP20, twistComp_zero, Polynomial.coeff_zero]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_twistComp Φ hTdeg]
      have hle : P₂.natDegree ≤ a - 1 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => hP2 j (by omega))
      omega
  have hzero' : (twistComp Φ T P₂).coeff (a + 1) = 0 := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · have hP20 : P₂ = 0 := by
        ext j
        rw [hP2 j (Nat.zero_le j), Polynomial.coeff_zero]
      rw [hP20, twistComp_zero, Polynomial.coeff_zero]
    · refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      rw [natDegree_twistComp Φ hTdeg]
      have hle : P₂.natDegree ≤ a - 1 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun j hj => hP2 j (by omega))
      omega
  have hexp : twistComp Φ T P
      = Polynomial.C (Φ (P.coeff (a + 1))) * T ^ (a + 1)
        + Polynomial.C (Φ (P.coeff a)) * T ^ a + twistComp Φ T P₂ := by
    conv_lhs => rw [hsplit]
    rw [twistComp_add, twistComp_add, twistComp_C_mul_X_pow, twistComp_C_mul_X_pow]
  rw [hexp] at hcoeff_a hcoeff_a1
  have hca := hcoeff_a
  have hca1 := hcoeff_a1
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hTpow, hzero, hzero',
    add_zero] at hca hca1
  simp only [Nat.sub_self, Nat.choose_self, Nat.choose_succ_self_right,
    Nat.add_sub_cancel_left] at hca hca1
  have hchoose : (Nat.choose a (a + 1) : K) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    norm_num
  rw [hchoose, mul_zero, mul_zero, add_zero] at hca1
  have hΦl : Φ (P.coeff (a + 1)) ≠ 0 :=
    fun hh => hlead ((map_eq_zero_iff Φ Φ.injective).mp hh)
  push_cast at hca hca1
  have hclear : Φ (P.coeff a) * P.coeff (a + 1)
      = ρ * P.coeff a * Φ (P.coeff (a + 1))
        - ((a : K) + 1) * L * Φ (P.coeff (a + 1)) * P.coeff (a + 1) := by
    refine mul_left_cancel₀ (pow_ne_zero a hρ) ?_
    linear_combination (P.coeff (a + 1)) * hca - (P.coeff a) * hca1
  rw [map_div₀]
  field_simp
  linear_combination hclear

/-- **The affine cocycle.**  In a split relation for an affine twisted substitution the ratio of
the two top coefficients solves the inhomogeneous linear equation whose solution translates the
substitution into a pure scaling. -/
theorem twistComp_affine_cocycle (Φ : K →+* K) {ρ L c : K} (hρ : ρ ≠ 0)
    {P : Polynomial K} {a : ℕ} (hdeg : P.natDegree = a + 1)
    (hcP : twistComp Φ (Polynomial.C ρ * Polynomial.X + Polynomial.C L) P
      = Polynomial.C c * P) :
    Φ (P.coeff a / P.coeff (a + 1))
      = ρ * (P.coeff a / P.coeff (a + 1)) - ((a : K) + 1) * L :=
  twistComp_affine_cocycle_of_coeff Φ hρ hdeg
    (by rw [hcP, Polynomial.coeff_C_mul]) (by rw [hcP, Polynomial.coeff_C_mul])

end GaloisForLFunctions.HTGeometry
