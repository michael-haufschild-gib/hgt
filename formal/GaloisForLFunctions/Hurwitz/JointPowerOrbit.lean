import GaloisForLFunctions.Hurwitz.LadderIndependence

/-!
# Zariski density of joint monodromy power orbits

For a finite vector `q = (q_j)`, assume its nonnegative monomials are pairwise distinct.  Then the
cyclic orbit `m ↦ (q_j^m)` is Zariski dense.  More generally, choosing one common loop count at each
of finitely many branch points gives a product orbit that is Zariski dense in the full deformation
space.  This is the algebraic engine for joint Hurwitz-ladder independence.
-/

open Complex HurwitzOrbit

namespace HurwitzJointOrbit

/-- Evaluation of the monomial encoded by `d` at the point `q`. -/
noncomputable def monomialValue {ι : Type*} (q : ι → ℂ) (d : ι →₀ ℕ) : ℂ :=
  d.prod fun i n => q i ^ n

/-- A monomial evaluated on the common power orbit is the corresponding monomial value raised to
that common power. -/
theorem monomialValue_pow {ι : Type*} (q : ι → ℂ) (d : ι →₀ ℕ) (m : ℕ) :
    monomialValue (fun i => q i ^ m) d = monomialValue q d ^ m := by
  rw [monomialValue, monomialValue, Finsupp.prod, Finsupp.prod, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, ← pow_mul, mul_comm m]

/-- Distinct exponential sequences `m ↦ b_i^m` are linearly independent. -/
theorem power_sum_coeff_zero {n : ℕ} {b c : Fin n → ℂ} (hb : Function.Injective b)
    (h : ∀ m : ℕ, ∑ i, c i * b i ^ m = 0) : c = 0 := by
  apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Matrix.vandermonde b).transpose)
  · rw [Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
    exact hb
  · funext m
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply, Pi.zero_apply]
    simpa [mul_comm] using h (m : ℕ)

/-- **Power-orbit density.**  If distinct monomials in `q` have distinct values, a polynomial
vanishing at every point `(q_i^m)_i` of the cyclic orbit is zero. -/
theorem mv_power_orbit_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) (hq : Function.Injective (monomialValue q))
    (P : MvPolynomial ι ℂ)
    (h : ∀ m : ℕ, MvPolynomial.eval (fun i => q i ^ m) P = 0) : P = 0 := by
  classical
  let e := Fintype.equivFin P.support
  let b : Fin (Fintype.card P.support) → ℂ := fun k => monomialValue q (e.symm k)
  let c : Fin (Fintype.card P.support) → ℂ := fun k => MvPolynomial.coeff (e.symm k) P
  have hb : Function.Injective b := by
    intro k l hkl
    apply e.symm.injective
    apply Subtype.ext
    exact hq hkl
  have hsum : ∀ m : ℕ, ∑ k, c k * b k ^ m = 0 := by
    intro m
    have hm := h m
    rw [MvPolynomial.eval_eq] at hm
    have hm' : ∑ d : P.support,
        MvPolynomial.coeff d.1 P * monomialValue (fun i => q i ^ m) d.1 = 0 := by
      rw [← Finset.sum_attach] at hm
      simpa [monomialValue, Finsupp.prod] using hm
    simp_rw [monomialValue_pow] at hm'
    have he := e.symm.sum_comp (fun d : P.support =>
      MvPolynomial.coeff d.1 P * monomialValue q d.1 ^ m)
    simpa [b, c] using he.trans hm'
  have hc := power_sum_coeff_zero hb hsum
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ P.support
  · let ds : P.support := ⟨d, hd⟩
    have hcd := congrFun hc (e ds)
    simpa [c, ds] using hcd
  · simpa [MvPolynomial.mem_support_iff] using hd

/-- Substitute constants in every branch column except `n`, whose coordinates remain variables. -/
noncomputable def columnPolynomial {ι : Type*} {L : ℕ}
    (n : Fin L) (v : (ι × Fin L) → ℂ) (P : MvPolynomial (ι × Fin L) ℂ) :
    MvPolynomial ι ℂ :=
  (MvPolynomial.bind₁ (R := ℂ) fun jk : ι × Fin L =>
    if jk.2 = n then MvPolynomial.X jk.1 else MvPolynomial.C (v jk)) P

/-- Evaluation of `columnPolynomial` varies exactly the selected branch column. -/
theorem eval_columnPolynomial {ι : Type*} {L : ℕ}
    (n : Fin L) (v : (ι × Fin L) → ℂ) (x : ι → ℂ)
    (P : MvPolynomial (ι × Fin L) ℂ) :
    MvPolynomial.eval x (columnPolynomial n v P) =
      MvPolynomial.eval (fun jk => if jk.2 = n then x jk.1 else v jk) P := by
  rw [columnPolynomial]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x
      (MvPolynomial.bind₁
        (fun jk => if jk.2 = n then MvPolynomial.X jk.1 else MvPolynomial.C (v jk)) P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval
      (fun jk => MvPolynomial.eval x
        (if jk.2 = n then MvPolynomial.X jk.1 else MvPolynomial.C (v jk))) P = _
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext'
  · ext r
    simp
  · intro jk
    by_cases h : jk.2 = n
    · simp [h]
    · simp [h]

/-- **Product power-grid density.**  At each of `L` branch columns choose one common orbit time
`m_n`.  If a polynomial vanishes on every resulting point `(q_j^{m_n})_{j,n}`, it is zero. -/
theorem mv_power_grid_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) (hq : Function.Injective (monomialValue q)) :
    ∀ (L : ℕ) (P : MvPolynomial (ι × Fin L) ℂ),
      (∀ m : Fin L → ℕ,
        MvPolynomial.eval (fun jk => q jk.1 ^ m jk.2) P = 0) → P = 0 := by
  intro L P h
  apply MvPolynomial.funext
  intro y
  suffices H : ∀ K : ℕ, K ≤ L →
      ∀ v : (ι × Fin L) → ℂ,
        (∀ n : Fin L, K ≤ (n : ℕ) → ∃ m : ℕ, ∀ j : ι, v (j, n) = q j ^ m) →
        MvPolynomial.eval v P = 0 by
    exact H L le_rfl y (fun n hbad => absurd hbad (Nat.not_le_of_lt n.isLt))
  intro K hKL
  induction K with
  | zero =>
      intro v hv
      choose m hm using fun n : Fin L => hv n (Nat.zero_le _)
      have hvm : v = fun jk => q jk.1 ^ m jk.2 := by
        funext jk
        exact hm jk.2 jk.1
      rw [hvm]
      exact h m
  | succ K ih =>
      intro v hv
      have hKlt : K < L := Nat.lt_of_succ_le hKL
      let nK : Fin L := ⟨K, hKlt⟩
      let Q := columnPolynomial nK v P
      have hQ : Q = 0 := by
        apply mv_power_orbit_zero q hq Q
        intro m
        rw [eval_columnPolynomial]
        apply ih (Nat.le_of_lt hKlt)
        intro n hn
        by_cases hnK : n = nK
        · subst hnK
          exact ⟨m, fun j => by simp [nK]⟩
        · obtain ⟨m', hm'⟩ := hv n (by
            have hne : (n : ℕ) ≠ K := by
              intro heq
              apply hnK
              apply Fin.ext
              simpa [nK] using heq
            omega)
          refine ⟨m', fun j => ?_⟩
          simp [hnK, hm' j]
      have hEvalQ : MvPolynomial.eval (fun j => v (j, nK)) Q = 0 := by
        rw [hQ, map_zero]
      rw [eval_columnPolynomial] at hEvalQ
      have hsame : (fun jk : ι × Fin L =>
          if jk.2 = nK then v (jk.1, nK) else v jk) = v := by
        funext jk
        by_cases heq : jk.2 = nK
        · rw [if_pos heq]
          exact congrArg (fun n => v (jk.1, n)) heq.symm
        · simp [heq]
      rwa [hsame] at hEvalQ

/-- The exponent family consisting of `1` and the selected Hurwitz exponents. -/
noncomputable def exponentFamily {ι : Type*} (s : ι → ℂ) : Option ι → ℂ
  | none => 1
  | some j => s j

/-- Restricting an exponent family along an injective index map restricts the augmented family
`(1, s_j)` along the induced option map. -/
theorem exponentFamily_comp {ι κ : Type*} (s : ι → ℂ) (f : κ → ι) :
    exponentFamily (s ∘ f) = exponentFamily s ∘ Option.map f := by
  funext x
  cases x <;> rfl

/-- Rational linear independence of an augmented exponent family passes to every injectively
indexed subfamily. -/
theorem exponentFamily_linearIndependent_comp {ι κ : Type*} (s : ι → ℂ)
    (hs : LinearIndependent ℚ (exponentFamily s)) (f : κ → ι)
    (hf : Function.Injective f) :
    LinearIndependent ℚ (exponentFamily (s ∘ f)) := by
  rw [exponentFamily_comp]
  exact hs.comp (Option.map f) (Option.map_injective hf)

/-- The exponent encoded by a nonnegative monomial in a family of Hurwitz exponents. -/
noncomputable def exponentWeight {ι : Type*} (s : ι → ℂ) (d : ι →₀ ℕ) : ℂ :=
  d.sum fun j n => (n : ℂ) * s j

/-- A monomial in the Hurwitz monodromy scalars is the exponential of its weighted exponent. -/
theorem monomialValue_monoScalar {ι : Type*} (s : ι → ℂ) (d : ι →₀ ℕ) :
    monomialValue (fun j => monoScalar (s j)) d =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * exponentWeight s d)) := by
  classical
  rw [monomialValue, Finsupp.prod, exponentWeight, Finsupp.sum]
  induction d.support using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih]
      rw [monoScalar, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring

/-- Rational linear independence of `1` and the exponent family makes all nonnegative monomials
in the corresponding monodromy scalars pairwise distinct. -/
theorem monomialValue_monoScalar_injective_of_linearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℂ)
    (hs : LinearIndependent ℚ (exponentFamily s)) :
    Function.Injective (monomialValue (fun j => monoScalar (s j))) := by
  intro d e hde
  rw [monomialValue_monoScalar, monomialValue_monoScalar] at hde
  have hone : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
      (exponentWeight s d - exponentWeight s e))) = 1 := by
    rw [show -(2 * (Real.pi : ℂ) * Complex.I * (exponentWeight s d - exponentWeight s e)) =
        -(2 * (Real.pi : ℂ) * Complex.I * exponentWeight s d) -
          (-(2 * (Real.pi : ℂ) * Complex.I * exponentWeight s e)) by ring,
      Complex.exp_sub, hde]
    simp
  rw [Complex.exp_eq_one_iff] at hone
  obtain ⟨k, hk⟩ := hone
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hp, Complex.I_ne_zero]
  have hweight : exponentWeight s d - exponentWeight s e = -(k : ℂ) := by
    have hmul : (2 * (Real.pi : ℂ) * Complex.I) *
        (-(exponentWeight s d - exponentWeight s e)) =
        (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
      linear_combination hk
    have hc := mul_left_cancel₀ hpi hmul
    linear_combination -hc
  have hrel : ∑ x : Option ι,
      (match x with
        | none => (k : ℚ)
        | some j => ((d j : ℤ) - (e j : ℤ) : ℤ)) • exponentFamily s x = 0 := by
    rw [Fintype.sum_option]
    simp only [exponentFamily]
    simp only [Rat.smul_def, mul_one]
    have hsum : ∑ j : ι, ((((d j : ℤ) - (e j : ℤ) : ℤ) : ℚ) : ℂ) * s j =
        exponentWeight s d - exponentWeight s e := by
      rw [exponentWeight, exponentWeight, Finsupp.sum_fintype, Finsupp.sum_fintype]
      · push_cast
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
      · simp
      · simp
    rw [hsum, hweight]
    push_cast
    ring
  have hcoeff := Fintype.linearIndependent_iff.mp hs _ hrel
  apply Finsupp.ext
  intro j
  have hj := hcoeff (some j)
  change (((d j : ℤ) - (e j : ℤ) : ℤ) : ℚ) = 0 at hj
  have hz : (d j : ℤ) - (e j : ℤ) = 0 := by exact_mod_cast hj
  exact_mod_cast sub_eq_zero.mp hz

/-- **Exact arithmetic form of monodromy-character separation.**  Pairwise separation of all
nonnegative monomials in the Hurwitz monodromy scalars is equivalent to rational linear
independence of the augmented exponent family `(1, s_j)`. -/
theorem linearIndependent_iff_monomialValue_monoScalar_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℂ) :
    LinearIndependent ℚ (exponentFamily s) ↔
      Function.Injective (monomialValue (fun j => monoScalar (s j))) := by
  constructor
  · exact monomialValue_monoScalar_injective_of_linearIndependent s
  · intro hmono
    apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
    rw [Fintype.linearIndependent_iff]
    intro g hrel x
    let d : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (g (some j)).toNat)
    let e : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (-g (some j)).toNat)
    have hsum : ∑ j : ι, ((g (some j) : ℤ) : ℂ) * s j = -((g none : ℤ) : ℂ) := by
      rw [Fintype.sum_option] at hrel
      simp only [exponentFamily] at hrel
      simp only [zsmul_eq_mul, mul_one] at hrel
      linear_combination hrel
    have hweight : exponentWeight s d - exponentWeight s e = -((g none : ℤ) : ℂ) := by
      rw [exponentWeight, exponentWeight, Finsupp.sum_fintype, Finsupp.sum_fintype]
      · simp only [d, e, ← Finsupp.equivFunOnFinite_apply, Equiv.apply_symm_apply]
        rw [← Finset.sum_sub_distrib]
        calc
          ∑ j : ι, (
              ((↑(g (some j)).toNat : ℕ) : ℂ) * s j -
                ((↑(-g (some j)).toNat : ℕ) : ℂ) * s j) =
              ∑ j : ι, ((g (some j) : ℤ) : ℂ) * s j := by
                apply Finset.sum_congr rfl
                intro j _
                rw [← sub_mul]
                congr 1
                exact_mod_cast Int.toNat_sub_toNat_neg (g (some j))
          _ = -((g none : ℤ) : ℂ) := hsum
      · simp
      · simp
    have hone : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
        (exponentWeight s d - exponentWeight s e))) = 1 := by
      rw [hweight]
      have hk := Complex.exp_int_mul_two_pi_mul_I (g none)
      convert hk using 1 <;> ring
    have hdeVal : monomialValue (fun j => monoScalar (s j)) d =
        monomialValue (fun j => monoScalar (s j)) e := by
      rw [monomialValue_monoScalar, monomialValue_monoScalar]
      have hsplit :
          -(2 * (Real.pi : ℂ) * Complex.I * exponentWeight s d) =
            -(2 * (Real.pi : ℂ) * Complex.I *
              (exponentWeight s d - exponentWeight s e)) +
            -(2 * (Real.pi : ℂ) * Complex.I * exponentWeight s e) := by ring
      rw [hsplit, Complex.exp_add, hone, one_mul]
    have hde : d = e := hmono hdeVal
    cases x with
    | none =>
        have hsome : ∀ j : ι, g (some j) = 0 := by
          intro j
          have hj := congrFun (congrArg (fun x : ι →₀ ℕ => (x : ι → ℕ)) hde) j
          change (g (some j)).toNat = (-g (some j)).toNat at hj
          have hz := Int.toNat_sub_toNat_neg (g (some j))
          rw [hj, sub_self] at hz
          exact hz.symm
        rw [Fintype.sum_option] at hrel
        simp only [exponentFamily, hsome, zero_smul, Finset.sum_const_zero, add_zero] at hrel
        simpa using hrel
    | some j =>
        have hj := congrFun (congrArg (fun x : ι →₀ ℕ => (x : ι → ℕ)) hde) j
        change (g (some j)).toNat = (-g (some j)).toNat at hj
        have hz := Int.toNat_sub_toNat_neg (g (some j))
        rw [hj, sub_self] at hz
        exact hz.symm

/-- Adding an independently chosen natural-number offset to every exponent preserves augmented
rational linear independence. -/
theorem exponentFamily_linearIndependent_natShift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℂ) (m : ι → ℕ)
    (hs : LinearIndependent ℚ (exponentFamily s)) :
    LinearIndependent ℚ (exponentFamily (fun j => s j + m j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hrel x
  let c0 : ℚ := g none + ∑ j : ι, g (some j) * m j
  let h : Option ι → ℚ
    | none => c0
    | some j => g (some j)
  have hold : ∑ y : Option ι, h y • exponentFamily s y = 0 := by
    rw [Fintype.sum_option]
    rw [Fintype.sum_option] at hrel
    simp only [h, c0, exponentFamily, Rat.smul_def, mul_one] at hrel ⊢
    push_cast at hrel ⊢
    simp_rw [mul_add] at hrel
    rw [Finset.sum_add_distrib] at hrel
    linear_combination hrel
  have hc := Fintype.linearIndependent_iff.mp hs h hold
  cases x with
  | some j => exact hc (some j)
  | none =>
      have hj : ∀ j : ι, g (some j) = 0 := fun j => hc (some j)
      have hnone := hc none
      simp [h, c0, hj] at hnone
      exact hnone

end HurwitzJointOrbit
