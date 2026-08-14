import GaloisForLFunctions.RHTower.SchanuelStageTwoIsogenyInvariance

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Integral additive characters whose value is algebraic. -/
def additiveAlgebraicCharacterLattice (x : Fin 2 → ℂ) : AddSubgroup (Fin 2 → ℤ) where
  carrier := {m | IsAlgebraic ℚ (∑ i, m i • x i)}
  zero_mem' := by
    simpa using (isAlgebraic_zero : IsAlgebraic ℚ (0 : ℂ))
  add_mem' := by
    intro m n hm hn
    change IsAlgebraic ℚ (∑ i, (m + n) i • x i)
    change IsAlgebraic ℚ (∑ i, m i • x i) at hm
    change IsAlgebraic ℚ (∑ i, n i • x i) at hn
    rw [show (∑ i, (m + n) i • x i) =
        (∑ i, m i • x i) + ∑ i, n i • x i by
      simp only [Fin.sum_univ_two, Pi.add_apply, add_zsmul]
      abel]
    exact hm.add hn
  neg_mem' := by
    intro m hm
    change IsAlgebraic ℚ (∑ i, (-m) i • x i)
    change IsAlgebraic ℚ (∑ i, m i • x i) at hm
    rw [show (∑ i, (-m) i • x i) = -(∑ i, m i • x i) by
      simp only [Fin.sum_univ_two, Pi.neg_apply, neg_zsmul]
      abel]
    exact hm.neg

/-- The additive algebraic-character lattice is saturated. -/
theorem additiveAlgebraicCharacterLattice_saturated
    (x : Fin 2 → ℂ) (r : ℤ) (hr : r ≠ 0) (m : Fin 2 → ℤ)
    (hm : r • m ∈ additiveAlgebraicCharacterLattice x) :
    m ∈ additiveAlgebraicCharacterLattice x := by
  change IsAlgebraic ℚ (∑ i, m i • x i)
  change IsAlgebraic ℚ (∑ i, (r • m) i • x i) at hm
  have hscaled : IsAlgebraic ℚ (r • ∑ i, m i • x i) := by
    convert hm using 1
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_add, smul_smul]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hrinv : IsAlgebraic ℚ ((r : ℂ)⁻¹) :=
    (isAlgebraic_int r).inv
  have hres : IsAlgebraic ℚ ((r : ℂ)⁻¹ * (r • ∑ i, m i • x i)) :=
    hrinv.mul hscaled
  have heq : (r : ℂ)⁻¹ * (r • ∑ i, m i • x i) = ∑ i, m i • x i := by
    rw [zsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hrC, one_mul]
  rw [heq] at hres
  exact hres

/-- Every nonzero algebraic character has a primitive algebraic divisor. -/
theorem exists_primitive_additiveAlgebraicCharacter
    (x : Fin 2 → ℂ) (m : Fin 2 → ℤ)
    (hm : m ∈ additiveAlgebraicCharacterLattice x) (hm0 : m ≠ 0) :
    ∃ p : Fin 2 → ℤ, p ∈ additiveAlgebraicCharacterLattice x ∧
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
  have hp : p ∈ additiveAlgebraicCharacterLattice x := by
    apply additiveAlgebraicCharacterLattice_saturated x g hg0 p
    rw [← hmp]
    exact hm
  refine ⟨p, hp, ?_⟩
  simpa [p] using hab

/-- Bézout completion of a primitive row to a determinant-one integral matrix. -/
def primitiveIntegralIsogenyMatrix2 (a b : ℤ) (h : Int.gcd a b = 1) :
    IntegralIsogenyMatrix2 where
  a := a
  b := b
  c := -Int.gcdB a b
  d := Int.gcdA a b
  det_ne := by
    have hbez := Int.gcd_eq_gcd_ab a b
    rw [h] at hbez
    have hdet : a * Int.gcdA a b - b * (-Int.gcdB a b) = 1 := by
      calc
        a * Int.gcdA a b - b * (-Int.gcdB a b) =
            a * Int.gcdA a b + b * Int.gcdB a b := by ring
        _ = 1 := hbez.symm
    exact hdet.trans_ne one_ne_zero

/-- Rational independence of a pair rules out a rational multiple relation. -/
theorem not_rat_smul_second_of_linearIndependent_fin_two
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x) :
    ∀ q : ℚ, x 1 ≠ q • x 0 := by
  intro q hq
  let c : Fin 2 → ℚ := ![-q, 1]
  have hsum : ∑ i, c i • x i = 0 := by
    rw [Fin.sum_univ_two]
    simp [c, hq]
  have hc1 := Fintype.linearIndependent_iff.mp hx c hsum 1
  norm_num [c] at hc1

/-- Any stage-two counterexample with a nonzero additive algebraic character yields a failure of
relative exponential-edge rigidity after a determinant-one integral coordinate change. -/
theorem exists_relativeExponentialBase_edge_of_nonzero_additive_character
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hfail : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
      (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t)
    (hexists : ∃ m : Fin 2 → ℤ,
      m ≠ 0 ∧ m ∈ additiveAlgebraicCharacterLattice x) :
    ∃ alpha z : ℂ, alpha ≠ 0 ∧ IsAlgebraic ℚ alpha ∧
      (∀ q : ℚ, z ≠ q • alpha) ∧
      IsAlgebraic (relativeExponentialBase alpha) z ∧
      IsAlgebraic (relativeExponentialBase alpha) (Complex.exp z) := by
  obtain ⟨m, hm0, hm⟩ := hexists
  obtain ⟨p, hp, hprimitive⟩ :=
    exists_primitive_additiveAlgebraicCharacter x m hm hm0
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
  have halpha : IsAlgebraic ℚ alpha := by
    change IsAlgebraic ℚ (∑ i, p i • x i) at hp
    simpa [alpha, x', M, primitiveIntegralIsogenyMatrix2,
      integralIsogenyAdditiveCoordinates, Fin.sum_univ_two, zsmul_eq_mul] using hp
  have halpha0 : alpha ≠ 0 := hx'.ne_zero 0
  have hznot : ∀ q : ℚ, z ≠ q • alpha := by
    exact not_rat_smul_second_of_linearIndependent_fin_two x' hx'
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
    (relativeExponentialBase_edge_iff_no_affine_stageTwo_extraction
      alpha z halpha0 halpha).mpr hfailNorm
  exact ⟨alpha, z, halpha0, halpha, hznot, hedge.1, hedge.2⟩

/-- Exact classification of the nonzero additive-character branch of stage-two failure. -/
theorem nonzero_additive_character_stageTwo_failure_iff_relativeExponentialBase_edge :
    (∃ x : Fin 2 → ℂ, LinearIndependent ℚ x ∧
      (¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t) ∧
      ∃ m : Fin 2 → ℤ, m ≠ 0 ∧ m ∈ additiveAlgebraicCharacterLattice x) ↔
    ∃ alpha z : ℂ, alpha ≠ 0 ∧ IsAlgebraic ℚ alpha ∧
      (∀ q : ℚ, z ≠ q • alpha) ∧
      IsAlgebraic (relativeExponentialBase alpha) z ∧
      IsAlgebraic (relativeExponentialBase alpha) (Complex.exp z) := by
  constructor
  · rintro ⟨x, hx, hfail, hexists⟩
    exact exists_relativeExponentialBase_edge_of_nonzero_additive_character
      x hx hfail hexists
  · rintro ⟨alpha, z, halpha0, halpha, hznot, hz, hexpz⟩
    let x : Fin 2 → ℂ := ![alpha, z]
    have hx : LinearIndependent ℚ x := by
      simpa [x] using
        linearIndependent_fin_two_of_ne_zero_of_not_rat_smul alpha z halpha0 hznot
    have hfailNorm : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ Set.range (![alpha, z] : Fin 2 → ℂ) ∪
          Set.range (fun j : Fin 2 => Complex.exp ((![alpha, z] : Fin 2 → ℂ) j))) ∧
        AlgebraicIndependent ℚ t :=
      (relativeExponentialBase_edge_iff_no_affine_stageTwo_extraction
        alpha z halpha0 halpha).mp ⟨hz, hexpz⟩
    have hfail : ¬ ∃ t : Fin 2 → ℂ, Function.Injective t ∧
        (∀ i, t i ∈ exponentialPairGeneratorSet x) ∧ AlgebraicIndependent ℚ t := by
      simpa [x, exponentialPairGeneratorSet] using hfailNorm
    let m : Fin 2 → ℤ := ![1, 0]
    have hm0 : m ≠ 0 := by
      intro hm
      have h0 := congrFun hm 0
      norm_num [m] at h0
    have hm : m ∈ additiveAlgebraicCharacterLattice x := by
      change IsAlgebraic ℚ (∑ i, m i • x i)
      simpa [m, x, Fin.sum_univ_two] using halpha
    exact ⟨x, hx, hfail, m, hm0, hm⟩

end

end GaloisForLFunctions.RHTower
