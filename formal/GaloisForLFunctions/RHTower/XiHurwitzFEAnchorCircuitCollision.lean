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

/-- Exact three-node circuit law.  For nonintegral exponents, dependence of the functional-
equation/anchor triple is equivalent to one of the three pairwise monodromy-character collisions. -/
theorem continuedHurwitzFEAnchorTripleDependent_iff_monoScalar_collision
    {rho tau : ℂ}
    (hrho : ∀ m : ℤ, rho ≠ (m : ℂ))
    (href : ∀ m : ℤ, 1 - rho ≠ (m : ℂ))
    (htau : ∀ m : ℤ, tau ≠ (m : ℂ)) :
    ContinuedHurwitzFEAnchorTripleDependent rho tau ↔
      monoScalar rho = monoScalar (1 - rho) ∨
        monoScalar rho = monoScalar tau ∨
        monoScalar (1 - rho) = monoScalar tau := by
  constructor
  · exact monoScalar_collision_of_continuedHurwitzFEAnchorTripleDependent
      hrho href htau
  · intro hcollision
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
    letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    intro hDI
    have hinj := (continued_hurwitz_intrinsic_residue_differentialMatroid_law
      (continuedHurwitzFEAnchorTripleExponent rho tau) (by
        intro i m
        cases i with
        | none => exact htau m
        | some b =>
            cases b
            · exact hrho m
            · exact href m)).mp hDI
    rcases hcollision with hFE | hrhoTau | hrefTau
    · have : (some false : Option Bool) = some true := by
        apply hinj
        simpa [continuedHurwitzFEAnchorTripleExponent] using hFE
      simp at this
    · have : (some false : Option Bool) = none := by
        apply hinj
        simpa [continuedHurwitzFEAnchorTripleExponent] using hrhoTau
      simp at this
    · have : (some true : Option Bool) = none := by
        apply hinj
        simpa [continuedHurwitzFEAnchorTripleExponent] using hrefTau
      simp at this

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

/-- **Exact FE-anchor locus on an Xi zero.**  Fix an actual Xi zero `rho` in the open strip and
let `tau` be any other open-strip exponent.  The Hurwitz triple at `rho`, `1-rho`, and `tau` is
differentially dependent exactly when the anchor is one of the two points in the functional-
equation orbit of `rho`. -/
theorem xiZero_continuedHurwitzFEAnchorTripleDependent_iff_anchor_eq_orbit
    {rho tau : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0)
    (htauStrip : 0 < tau.re ∧ tau.re < 1) :
    ContinuedHurwitzFEAnchorTripleDependent rho tau ↔
      tau = rho ∨ tau = 1 - rho := by
  have hrefstrip : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  have hclass := continuedHurwitzFEAnchorTripleDependent_iff_monoScalar_collision
    (fun m => openCriticalStrip_point_ne_int hstrip m)
    (fun m => openCriticalStrip_point_ne_int hrefstrip m)
    (fun m => openCriticalStrip_point_ne_int htauStrip m)
  constructor
  · intro hdep
    rcases hclass.mp hdep with hFE | hrhoTau | hrefTau
    · exact (xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_oneSub
        hstrip hFE hzero).elim
    · obtain ⟨m, hm⟩ :=
        (monoScalar_eq_monoScalar_iff_integerDifference rho tau).mp hrhoTau
      exact Or.inl (openCriticalStrip_eq_of_sub_eq_int hstrip htauStrip m hm).symm
    · obtain ⟨m, hm⟩ :=
        (monoScalar_eq_monoScalar_iff_integerDifference (1 - rho) tau).mp hrefTau
      exact Or.inr (openCriticalStrip_eq_of_sub_eq_int hrefstrip htauStrip m hm).symm
  · rintro (rfl | rfl)
    · exact hclass.mpr (Or.inr (Or.inl rfl))
    · exact hclass.mpr (Or.inr (Or.inr rfl))

/-- Every open-strip point outside the Xi divisor gives an independent FE-anchor triple at an
actual Xi zero.  This is the positive complement of the exact two-point anchor-locus law. -/
theorem xiZero_continuedHurwitzFEAnchorTriple_independent_of_anchor_ne_zero
    {rho tau : ℂ}
    (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0)
    (htauStrip : 0 < tau.re ∧ tau.re < 1) (htau : xi tau ≠ 0) :
    ¬ ContinuedHurwitzFEAnchorTripleDependent rho tau := by
  intro hdep
  rcases (xiZero_continuedHurwitzFEAnchorTripleDependent_iff_anchor_eq_orbit
    hstrip hzero htauStrip).mp hdep with h | h
  · apply htau
    rw [h, hzero]
  · apply htau
    rw [h, xi_one_sub, hzero]

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

/-- A monodromy collision with the canonical half exponent excludes an Xi zero in the open
critical strip.  No algebraicity input is needed: character equality identifies the exponents
modulo `Z`, while the strip leaves only the real anchor `1/2`, where Xi is positive. -/
theorem xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_half
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hhalf : monoScalar rho = monoScalar (1 / 2 : ℂ)) :
    xi rho ≠ 0 := by
  intro hzero
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference rho (1 / 2 : ℂ)).mp hhalf
  have heq : rho = (1 / 2 : ℂ) :=
    openCriticalStrip_eq_of_sub_eq_int hstrip (by norm_num) m hm
  have hpos := xi_pos_on_real_anchor (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hz : xi ((1 / 2 : ℝ) : ℂ) = 0 := by
    simpa [heq] using hzero
  rw [hz] at hpos
  norm_num at hpos

/-- **Unconditional Xi FE-anchor freeness.**  At every actual Xi zero in the open critical strip,
the three analytically continued Hurwitz functions with exponents `rho`, `1-rho`, and `1/2` are
differentially independent.  Every possible circuit would force one of three monodromy-character
collisions, and each collision is excluded by strip rigidity and positivity on the real anchor. -/
theorem xiZero_continuedHurwitzHalfFEAnchorTriple_independent
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0) :
    ¬ ContinuedHurwitzFEAnchorTripleDependent rho (1 / 2 : ℂ) := by
  apply xiZero_continuedHurwitzFEAnchorTriple_independent_of_anchor_ne_zero
    hstrip hzero (by norm_num)
  intro hhalfZero
  have hpos := xi_pos_on_real_anchor (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hz : xi ((1 / 2 : ℝ) : ℂ) = 0 := by simpa using hhalfZero
  rw [hz] at hpos
  norm_num at hpos

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

/-- The algebraicity-free fixed-anchor target.  A circuit is required only at hypothetical
right-half Xi zeros; the half-anchor collision itself supplies the complete contradiction. -/
def XiRightHurwitzHalfFEAnchorCircuit : Prop :=
  ∀ rho : XiDivisorSupport, 1 / 2 < (rho : ℂ).re →
    ContinuedHurwitzFEAnchorTripleDependent (rho : ℂ) (1 / 2 : ℂ)

/-- **Algebraicity-free fixed-circuit chain to RH.**  The Arakelov-coordinate field in the older
certificate is superfluous: the canonical half-anchor circuit alone forces RH. -/
theorem riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit
    (h : XiRightHurwitzHalfFEAnchorCircuit) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  exact xiZero_continuedHurwitzHalfFEAnchorTriple_independent
    (xi_divisor_support_re_mem_open_unit support) hzero
    (h support (mem_rightHalf.mp hrho))

/-- **Canonical fixed-circuit chain to RH.**  It is enough to use the one anchor exponent `1/2`;
the Arakelov algebraicity component is now discharged by the algebraicity-free circuit theorem. -/
theorem riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit
    (h : XiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit
  intro rho hrho
  exact (h rho hrho).2

end

end RHTower
