import GaloisForLFunctions.RHTower.XiArakelovHurwitzDependenceCollision

/-!
# Functional-equation Hurwitz circuits collide with Arakelov algebraicity

The existing finite-anchor theorem captures one Xi-indexed Hurwitz function inside a family whose
anchor characters are all algebraic.  Here the moving functional-equation partner `1 - rho` is
adjoined as a deliberately nonalgebraic anchor.  A differential circuit on

`{H_rho, H_(1-rho), H_tau}`

has exactly three possible monodromy-character collisions.  Collision of the two Xi exponents
forces `rho = 1-rho` inside the open critical strip and contradicts the real zero-free interval.
Collision with the algebraic-character anchor makes either `q(rho)` or its inverse algebraic; an
algebraic Arakelov coordinate then invokes the Gelfond--Schneider exclusion.

Thus a moving three-function value relation, rather than a sign or a zero-location condition,
closes to RH.  The relation is not subsumed by the fixed finite-anchor result because the
functional-equation partner is not assumed to have algebraic character.
-/

open Complex Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- The three exponents `tau`, `rho`, and `1-rho`, indexed without duplicate constructors. -/
def continuedHurwitzFEAnchorTripleExponent (rho tau : ℂ) : Option Bool → ℂ
  | none => tau
  | some false => rho
  | some true => 1 - rho

/-- A genuine algebraic differential circuit among the Hurwitz functions at one Xi exponent, its
holomorphic functional-equation reflection, and one auxiliary anchor. -/
def ContinuedHurwitzFEAnchorTripleDependent (rho tau : ℂ) : Prop :=
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  ¬ DifferentialIndependent (RatFunc ℂ)
    (fun i : Option Bool =>
      continuedHzetaUpperEndMero (continuedHurwitzFEAnchorTripleExponent rho tau i))

/-- The intrinsic Hurwitz differential matroid resolves a three-function circuit into exactly one
of the three pairwise monodromy-character collisions. -/
theorem monoScalar_collision_of_continuedHurwitzFEAnchorTripleDependent
    {rho tau : ℂ}
    (hrho : ∀ m : ℤ, rho ≠ (m : ℂ))
    (href : ∀ m : ℤ, 1 - rho ≠ (m : ℂ))
    (htau : ∀ m : ℤ, tau ≠ (m : ℂ))
    (hdep : ContinuedHurwitzFEAnchorTripleDependent rho tau) :
    monoScalar rho = monoScalar (1 - rho) ∨
      monoScalar rho = monoScalar tau ∨
      monoScalar (1 - rho) = monoScalar tau := by
  by_contra hnone
  simp only [not_or] at hnone
  apply hdep
  apply (continued_hurwitz_intrinsic_residue_differentialMatroid_law
    (continuedHurwitzFEAnchorTripleExponent rho tau) ?_).mpr
  · intro i j hq
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some b =>
            cases b
            · exact (hnone.2.1 hq.symm).elim
            · exact (hnone.2.2 hq.symm).elim
    | some a =>
        cases j with
        | none =>
            cases a
            · exact (hnone.2.1 hq).elim
            · exact (hnone.2.2 hq).elim
        | some b =>
            cases a <;> cases b
            · rfl
            · exact (hnone.1 hq).elim
            · exact (hnone.1 hq.symm).elim
            · rfl
  · intro i m
    cases i with
    | none => exact htau m
    | some b =>
        cases b
        · exact hrho m
        · exact href m

/-- Holomorphic functional-equation reflection inverts the Hurwitz monodromy character. -/
theorem monoScalar_one_sub_eq_inv (rho : ℂ) :
    monoScalar (1 - rho) = (monoScalar rho)⁻¹ := by
  have hsame : monoScalar (1 - rho) = monoScalar (-rho) := by
    apply (monoScalar_eq_monoScalar_iff_integerDifference (1 - rho) (-rho)).mpr
    refine ⟨1, ?_⟩
    push_cast
    ring
  rw [hsame, monoScalar, monoScalar, ← Complex.exp_neg]
  congr 1
  ring

/-- The two functional-equation exponents of an Xi zero cannot have the same Hurwitz character.
Inside the open strip, character equality makes the exponents equal modulo `Z`, hence equal; the
point is then real, where Xi is strictly positive. -/
theorem xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_oneSub
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hreflect : monoScalar rho = monoScalar (1 - rho)) :
    xi rho ≠ 0 := by
  intro hzero
  have hrefstrip : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference rho (1 - rho)).mp hreflect
  have hrhoeq : rho = 1 - rho :=
    openCriticalStrip_eq_of_sub_eq_int hstrip hrefstrip m hm
  have him := congrArg Complex.im hrhoeq
  simp only [Complex.sub_im, Complex.one_im] at him
  have him0 : rho.im = 0 := by linarith
  have hrhoReal : rho = (rho.re : ℂ) := by
    apply Complex.ext <;> simp [him0]
  have hpos := xi_pos_on_real_anchor hstrip.1 hstrip.2
  rw [hrhoReal] at hzero
  rw [hzero] at hpos
  simp at hpos

/-- Source-value hypothesis on hypothetical right-half Xi points.  Besides an algebraic Arakelov
coordinate, it asks for one nonintegral algebraic-character anchor which completes the moving
functional-equation pair to a differential circuit. -/
def XiRightArakelovAlgebraicHurwitzFEAnchorCircuit : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      ∃ tau : ℂ,
        (∀ m : ℤ, tau ≠ (m : ℂ)) ∧
        IsAlgebraic ℚ (monoScalar tau) ∧
        ContinuedHurwitzFEAnchorTripleDependent (rho : ℂ) tau

/-- **FE-circuit/Arakelov collision to RH.**  Every possible character collision in the moving
three-Hurwitz circuit excludes the hypothetical right-half Xi zero: the FE-pair branch by strip
rigidity, and the two anchor branches by Arakelov--Hurwitz Gelfond--Schneider. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzFEAnchorCircuit
    (h : XiRightArakelovAlgebraicHurwitzFEAnchorCircuit) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hstrip := xi_divisor_support_re_mem_open_unit support
  have hrefstrip : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  obtain ⟨hw, tau, htau, hqtau, hdep⟩ := h support (mem_rightHalf.mp hrho)
  have hcollision :=
    monoScalar_collision_of_continuedHurwitzFEAnchorTripleDependent
      (fun m => openCriticalStrip_point_ne_int hstrip m)
      (fun m => openCriticalStrip_point_ne_int hrefstrip m)
      htau hdep
  rcases hcollision with hreflect | hanchor | hanchor
  · exact xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_oneSub
      hstrip hreflect hzero
  · have hqrho : IsAlgebraic ℚ (monoScalar rho) := by
      rw [hanchor]
      exact hqtau
    exact xi_ne_zero_of_openCriticalStrip_of_arakelovW_algebraic_of_monoScalar_algebraic
      hstrip hw hqrho hzero
  · have hqref : IsAlgebraic ℚ (monoScalar (1 - rho)) := by
      rw [hanchor]
      exact hqtau
    have hqrho : IsAlgebraic ℚ (monoScalar rho) := by
      rw [monoScalar_one_sub_eq_inv rho] at hqref
      simpa using hqref.inv
    exact xi_ne_zero_of_openCriticalStrip_of_arakelovW_algebraic_of_monoScalar_algebraic
      hstrip hw hqrho hzero

/-- The canonical half-exponent anchor has character `-1`. -/
theorem monoScalar_half_eq_neg_one :
    monoScalar (1 / 2 : ℂ) = -1 := by
  have h := monoScalar_eq_neg_height_of_re_eq_half
    (s := (1 / 2 : ℂ)) (by norm_num)
  simpa using h

/-- In particular, the canonical half-exponent anchor has algebraic monodromy character. -/
theorem monoScalar_half_isAlgebraic :
    IsAlgebraic ℚ (monoScalar (1 / 2 : ℂ)) := by
  rw [monoScalar_half_eq_neg_one]
  simpa using
    (isIntegral_algebraMap : IsIntegral ℚ (algebraMap ℚ ℂ (-1))).isAlgebraic

/-- The fixed-anchor source target: every hypothetical right-half Xi point has algebraic Arakelov
coordinate and completes with its FE partner and the canonical exponent `1/2` to a differential
circuit. -/
def XiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    IsAlgebraic ℚ (arakelovW (rho : ℂ)) ∧
      ContinuedHurwitzFEAnchorTripleDependent (rho : ℂ) (1 / 2 : ℂ)

/-- **Canonical fixed-circuit chain to RH.**  It is enough to use the one anchor exponent `1/2`;
its nonintegrality and algebraic character are unconditional. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit
    (h : XiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzFEAnchorCircuit
  intro rho hrho
  obtain ⟨hw, hdep⟩ := h rho hrho
  refine ⟨hw, (1 / 2 : ℂ), ?_, monoScalar_half_isAlgebraic, hdep⟩
  exact fun m => openCriticalStrip_point_ne_int (s := (1 / 2 : ℂ)) (by norm_num) m

end

end RHTower
