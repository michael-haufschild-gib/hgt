import GaloisForLFunctions.RHTower.Schanuel.SchanuelAffineCharacterNormalForm

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Field generated over the algebraic numbers by one logarithmic period. -/
abbrev periodRelativeBase (alpha : ℂ) :
    IntermediateField (algebraicClosure ℚ ℂ) ℂ :=
  oneGeneratorField (algebraicClosure ℚ ℂ) ℂ alpha

/-- A nonzero logarithm of an algebraic number is transcendental over the algebraic numbers. -/
theorem transcendental_algebraicClosure_of_exp_isAlgebraic
    (alpha : ℂ) (halpha0 : alpha ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp alpha)) :
    Transcendental (algebraicClosure ℚ ℂ) alpha := by
  have halphaQ : Transcendental ℚ alpha := by
    intro halpha
    have hexpTrans : Transcendental ℚ (Complex.exp alpha) :=
      exp_algebraic_transcendental
        ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr halpha) halpha0
    exact hexpTrans hexp
  letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
    algebraicClosure.isAlgebraic ℚ ℂ
  exact halphaQ.extendScalars (algebraicClosure ℚ ℂ)

/-- Exact normalized period equivalence. -/
theorem periodRelativeBase_edge_iff_no_period_stageTwo_extraction
    (alpha z : ℂ) (halpha0 : alpha ≠ 0)
    (hexp : IsAlgebraic ℚ (Complex.exp alpha)) :
    (IsAlgebraic (periodRelativeBase alpha) z ∧
        IsAlgebraic (periodRelativeBase alpha) (Complex.exp z)) ↔
      ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ Set.range (![alpha, z] : Fin 2 → ℂ) ∪
          Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))) ∧
        AlgebraicIndependent ℚ t := by
  let S : Set ℂ := Set.range (![alpha, z] : Fin 2 → ℂ) ∪
    Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))
  have halphaTrans : Transcendental (algebraicClosure ℚ ℂ) alpha :=
    transcendental_algebraicClosure_of_exp_isAlgebraic alpha halpha0 hexp
  constructor
  · rintro ⟨hz, hexpz⟩ ⟨t, _, htmem, htind⟩
    apply not_algebraicIndependent_fin_two_of_isAlgebraic_oneGeneratorField
      (K := algebraicClosure ℚ ℂ)
      alpha t
    intro i
    rcases htmem i with ht | ht
    · obtain ⟨j, hj⟩ := ht
      rw [← hj]
      fin_cases j
      · have halphaMem : alpha ∈ periodRelativeBase alpha := by
          exact IntermediateField.subset_adjoin _ _ ⟨(), rfl⟩
        have ha := isAlgebraic_algebraMap
          (R := periodRelativeBase alpha) (A := ℂ)
          (⟨alpha, halphaMem⟩ : periodRelativeBase alpha)
        simpa [periodRelativeBase] using ha
      · simpa [periodRelativeBase] using hz
    · obtain ⟨j, hj⟩ := ht
      rw [← hj]
      fin_cases j
      · have hexpA : Complex.exp alpha ∈ algebraicClosure ℚ ℂ :=
          mem_algebraicClosure_iff.mpr hexp
        let eA : algebraicClosure ℚ ℂ := ⟨Complex.exp alpha, hexpA⟩
        have he := isAlgebraic_algebraMap
          (R := periodRelativeBase alpha) (A := ℂ)
          (⟨Complex.exp alpha, (periodRelativeBase alpha).algebraMap_mem eA⟩ :
            periodRelativeBase alpha)
        simpa [periodRelativeBase, eA] using he
      · simpa [periodRelativeBase] using hexpz
    · letI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) :=
        algebraicClosure.isAlgebraic ℚ ℂ
      exact htind.extendScalars (algebraicClosure ℚ ℂ)
  · intro hfail
    have halphaS : alpha ∈ S := Or.inl ⟨0, rfl⟩
    constructor
    · have hzS : z ∈ S := Or.inl ⟨1, rfl⟩
      have hz := isAlgebraic_oneGeneratorField_of_mem_of_no_fin_two_extraction
        (R := ℚ) (K := algebraicClosure ℚ ℂ) S alpha halphaS halphaTrans
        (by simpa [S] using hfail) hzS
      simpa [periodRelativeBase] using hz
    · have hexpzS : Complex.exp z ∈ S := Or.inr ⟨1, rfl⟩
      have hexpz := isAlgebraic_oneGeneratorField_of_mem_of_no_fin_two_extraction
        (R := ℚ) (K := algebraicClosure ℚ ℂ) S alpha halphaS halphaTrans
        (by simpa [S] using hfail) hexpzS
      simpa [periodRelativeBase] using hexpz

/-- A nonzero integral power is algebraic only if its base is algebraic. -/
theorem isAlgebraic_of_zpow_isAlgebraic
    (w : ℂ) (r : ℤ) (hr : r ≠ 0)
    (hpow : IsAlgebraic ℚ (w ^ r)) : IsAlgebraic ℚ w := by
  cases r with
  | ofNat n =>
      have hn : 0 < n := Nat.pos_of_ne_zero (by simpa using hr)
      exact IsAlgebraic.of_pow hn (by simpa using hpow)
  | negSucc n =>
      have hinv : IsAlgebraic ℚ ((w⁻¹) ^ (n + 1)) := by
        simpa [zpow_negSucc] using hpow
      have hwInv : IsAlgebraic ℚ w⁻¹ :=
        IsAlgebraic.of_pow (Nat.succ_pos n) hinv
      simpa using hwInv.inv

/-- Integral additive characters whose exponentials are algebraic. -/
def multiplicativeAlgebraicCharacterLattice (x : Fin 2 → ℂ) :
    AddSubgroup (Fin 2 → ℤ) where
  carrier := {m | IsAlgebraic ℚ (Complex.exp (∑ i, m i • x i))}
  zero_mem' := by
    simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℂ))
  add_mem' := by
    intro m n hm hn
    change IsAlgebraic ℚ (Complex.exp (∑ i, (m + n) i • x i))
    change IsAlgebraic ℚ (Complex.exp (∑ i, m i • x i)) at hm
    change IsAlgebraic ℚ (Complex.exp (∑ i, n i • x i)) at hn
    rw [show (∑ i, (m + n) i • x i) =
        (∑ i, m i • x i) + ∑ i, n i • x i by
      simp only [Fin.sum_univ_two, Pi.add_apply, add_zsmul]
      abel,
      Complex.exp_add]
    exact hm.mul hn
  neg_mem' := by
    intro m hm
    change IsAlgebraic ℚ (Complex.exp (∑ i, (-m) i • x i))
    change IsAlgebraic ℚ (Complex.exp (∑ i, m i • x i)) at hm
    rw [show (∑ i, (-m) i • x i) = -(∑ i, m i • x i) by
      simp only [Fin.sum_univ_two, Pi.neg_apply, neg_zsmul]
      abel,
      Complex.exp_neg]
    exact hm.inv

/-- The multiplicative algebraic-character lattice is saturated. -/
theorem multiplicativeAlgebraicCharacterLattice_saturated
    (x : Fin 2 → ℂ) (r : ℤ) (hr : r ≠ 0) (m : Fin 2 → ℤ)
    (hm : r • m ∈ multiplicativeAlgebraicCharacterLattice x) :
    m ∈ multiplicativeAlgebraicCharacterLattice x := by
  change IsAlgebraic ℚ (Complex.exp (∑ i, m i • x i))
  change IsAlgebraic ℚ (Complex.exp (∑ i, (r • m) i • x i)) at hm
  have hpow : IsAlgebraic ℚ ((Complex.exp (∑ i, m i • x i)) ^ r) := by
    convert hm using 1
    have hsum : (∑ i, (r • m) i • x i) = (r : ℂ) * ∑ i, m i • x i := by
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      ring
    rw [hsum, Complex.exp_int_mul]
  exact isAlgebraic_of_zpow_isAlgebraic _ r hr hpow

/-- Every nonzero multiplicative algebraic character has a primitive divisor. -/
theorem exists_primitive_multiplicativeAlgebraicCharacter
    (x : Fin 2 → ℂ) (m : Fin 2 → ℤ)
    (hm : m ∈ multiplicativeAlgebraicCharacterLattice x) (hm0 : m ≠ 0) :
    ∃ p : Fin 2 → ℤ, p ∈ multiplicativeAlgebraicCharacterLattice x ∧
      Int.gcd (p 0) (p 1) = 1 := by
  have hmcoord : m 0 ≠ 0 ∨ m 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hm0
    funext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hgpos : 0 < Int.gcd (m 0) (m 1) := by
    rcases hmcoord with hmcoord | hmcoord
    · exact Int.gcd_pos_of_ne_zero_left _ hmcoord
    · exact Int.gcd_pos_of_ne_zero_right _ hmcoord
  obtain ⟨a, b, hab, hm0eq, hm1eq⟩ := Int.exists_gcd_one hgpos
  let g : ℤ := Int.gcd (m 0) (m 1)
  have hm0eq' : m 0 = a * g := by simpa [g] using hm0eq
  have hm1eq' : m 1 = b * g := by simpa [g] using hm1eq
  let p : Fin 2 → ℤ := ![a, b]
  have hmp : m = g • p := by
    funext i
    fin_cases i
    · change m 0 = g * a
      rw [hm0eq']
      ring
    · change m 1 = g * b
      rw [hm1eq']
      ring
  have hg0 : g ≠ 0 := by
    change (Int.gcd (m 0) (m 1) : ℤ) ≠ 0
    exact_mod_cast hgpos.ne'
  have hp : p ∈ multiplicativeAlgebraicCharacterLattice x := by
    apply multiplicativeAlgebraicCharacterLattice_saturated x g hg0 p
    rw [← hmp]
    exact hm
  exact ⟨p, hp, by simpa [p] using hab⟩

/-- Any nonzero multiplicative algebraic character normalizes a stage-two failure to a period
relative exponential-edge obstruction. -/
theorem exists_periodRelativeBase_edge_of_nonzero_multiplicative_character
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hfail : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t)
    (hexists : ∃ m : Fin 2 → ℤ,
      m ≠ 0 ∧ m ∈ multiplicativeAlgebraicCharacterLattice x) :
    ∃ alpha z : ℂ, alpha ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp alpha) ∧
      (∀ q : ℚ, z ≠ q • alpha) ∧
      IsAlgebraic (periodRelativeBase alpha) z ∧
      IsAlgebraic (periodRelativeBase alpha) (Complex.exp z) := by
  obtain ⟨m, hm0, hm⟩ := hexists
  obtain ⟨p, hp, hprimitive⟩ :=
    exists_primitive_multiplicativeAlgebraicCharacter x m hm hm0
  let M := primitiveIntegralIsogenyMatrix2 (p 0) (p 1) hprimitive
  let x' := integralIsogenyAdditiveCoordinates x M
  have hx' : LinearIndependent ℚ x' := by
    change LinearIndependent ℚ (fun i : Fin 2 ↦
      if i = 0 then (M.a : ℂ) * x 0 + (M.b : ℂ) * x 1
      else (M.c : ℂ) * x 0 + (M.d : ℂ) * x 1)
    exact linearIndependent_integral_isogeny_fin_two x hx M.a M.b M.c M.d M.det_ne
  have hfail' : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ exponentialPairGeneratorSet x') ∧ AlgebraicIndependent ℚ t := by
    simpa [x'] using no_fin_two_extraction_integralIsogeny x hx hfail M
  let alpha := x' 0
  let z := x' 1
  have hexpalpha : IsAlgebraic ℚ (Complex.exp alpha) := by
    change IsAlgebraic ℚ (Complex.exp (∑ i, p i • x i)) at hp
    simpa [alpha, x', M, primitiveIntegralIsogenyMatrix2,
      integralIsogenyAdditiveCoordinates, Fin.sum_univ_two, zsmul_eq_mul] using hp
  have halpha0 : alpha ≠ 0 := hx'.ne_zero 0
  have hznot : ∀ q : ℚ, z ≠ q • alpha :=
    not_rat_smul_second_of_linearIndependent_fin_two x' hx'
  have hx'vec : x' = ![alpha, z] := by
    funext i
    fin_cases i <;> rfl
  have hfailNorm : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ Set.range (![alpha, z] : Fin 2 → ℂ) ∪
        Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))) ∧
      AlgebraicIndependent ℚ t := by
    rw [← hx'vec]
    simpa [exponentialPairGeneratorSet] using hfail'
  have hedge :=
    (periodRelativeBase_edge_iff_no_period_stageTwo_extraction
      alpha z halpha0 hexpalpha).mpr hfailNorm
  exact ⟨alpha, z, halpha0, hexpalpha, hznot, hedge.1, hedge.2⟩

/-- Exact classification of the nonzero multiplicative-character branch of stage-two failure. -/
theorem nonzero_multiplicative_character_stageTwo_failure_iff_periodRelativeBase_edge :
    (∃ x : Fin 2 → ℂ, LinearIndependent ℚ x ∧
      (¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t) ∧
      ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ m ∈ multiplicativeAlgebraicCharacterLattice x) ↔
    ∃ alpha z : ℂ, alpha ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp alpha) ∧
      (∀ q : ℚ, z ≠ q • alpha) ∧
      IsAlgebraic (periodRelativeBase alpha) z ∧
      IsAlgebraic (periodRelativeBase alpha) (Complex.exp z) := by
  constructor
  · rintro ⟨x, hx, hfail, hexists⟩
    exact exists_periodRelativeBase_edge_of_nonzero_multiplicative_character
      x hx hfail hexists
  · rintro ⟨alpha, z, halpha0, hexpalpha, hznot, hz, hexpz⟩
    let x : Fin 2 → ℂ := ![alpha, z]
    have hx : LinearIndependent ℚ x := by
      simpa [x] using
        linearIndependent_fin_two_of_ne_zero_of_not_rat_smul alpha z halpha0 hznot
    have hfailNorm : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ Set.range (![alpha, z] : Fin 2 → ℂ) ∪
          Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))) ∧
        AlgebraicIndependent ℚ t :=
      (periodRelativeBase_edge_iff_no_period_stageTwo_extraction
        alpha z halpha0 hexpalpha).mp ⟨hz, hexpz⟩
    have hfail : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t := by
      simpa [x, exponentialPairGeneratorSet] using hfailNorm
    let m : Fin 2 → ℤ := ![1, 0]
    have hm0 : m ≠ 0 := by
      intro hm
      have h0 := congrFun hm 0
      norm_num [m] at h0
    have hm : m ∈ multiplicativeAlgebraicCharacterLattice x := by
      change IsAlgebraic ℚ (Complex.exp (∑ i, m i • x i))
      simpa [m, x, Fin.sum_univ_two] using hexpalpha
    exact ⟨x, hx, hfail, m, hm0, hm⟩

end

end GaloisForLFunctions.RHTower
