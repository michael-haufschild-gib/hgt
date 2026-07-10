/-
All-scale Sonin dilation corners and the archimedean Euler semicommutator.

The symmetric dilation sum `U_r + U_{r⁻¹}` is invariant under `r ↦ r⁻¹`, so the fixed-cutoff
Sonin corner extends to every positive scale. The extended family vanishes at `r = 1` and has
essential norm exactly one at every other scale: the corner family of the strongly continuous
dilation group has an essential-norm discontinuity across the trivial scale.

On the archimedean Hardy--Titchmarsh line the diagonal compression defect of the positive Euler
metric, `Π G_p² Π − (Π G_p Π)²`, factors through the complement of the carrier projection and
equals the ordered quadratic corner at equal scales; its essential norm is therefore exactly
`p⁻¹`.
-/
import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm

noncomputable section

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct

/-! ### The dilation corner at every positive scale -/

theorem evenDilationCLM_congr {r s : ℝ} (hr : 0 < r) (h : r = s) :
    evenDilationCLM r hr = evenDilationCLM s (h ▸ hr) := by
  subst h
  rfl

/-- The symmetric dilation sum `U_r + U_{r⁻¹}` at an arbitrary positive scale. -/
def evenDilationSumAll (r : ℝ) (hr : 0 < r) : evenSubspace →L[ℂ] evenSubspace :=
  evenDilationCLM r hr + evenDilationCLM r⁻¹ (inv_pos.mpr hr)

theorem evenDilationSumAll_inv (r : ℝ) (hr : 0 < r) :
    evenDilationSumAll r⁻¹ (inv_pos.mpr hr) = evenDilationSumAll r hr := by
  dsimp [evenDilationSumAll]
  rw [evenDilationCLM_congr (inv_pos.mpr (inv_pos.mpr hr)) (inv_inv r)]
  exact add_comm _ _

theorem evenDilationSumAll_eq_evenDilationSum (p : ℝ) (hp : 1 < p) :
    evenDilationSumAll p (zero_lt_one.trans hp) = evenDilationSum p hp :=
  (evenDilationSum_eq p hp).symm

/-- The fixed-cutoff Sonin dilation corner at an arbitrary positive scale. -/
def evenCentralSoninDilationCornerAll (a r : ℝ) (hr : 0 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  (1 - evenCentralSoninProjection a) * evenDilationSumAll r hr *
    evenCentralSoninProjection a

/-- The corner family is invariant under scale inversion. -/
theorem evenCentralSoninDilationCornerAll_inv (a r : ℝ) (hr : 0 < r) :
    evenCentralSoninDilationCornerAll a r⁻¹ (inv_pos.mpr hr) =
      evenCentralSoninDilationCornerAll a r hr := by
  dsimp [evenCentralSoninDilationCornerAll]
  rw [evenDilationSumAll_inv]

theorem evenCentralSoninDilationCornerAll_eq
    (a p : ℝ) (hp : 1 < p) :
    evenCentralSoninDilationCornerAll a p (zero_lt_one.trans hp) =
      evenCentralSoninDilationCorner a p hp := by
  rw [evenCentralSoninDilationCornerAll, evenDilationSumAll_eq_evenDilationSum,
    ← evenCentralSoninDilationCorner_eq_mul]

/-- At the trivial scale the corner vanishes: `U_1 + U_1⁻¹ = 2` and the two Sonin projections
annihilate each other. -/
theorem evenCentralSoninDilationCornerAll_one (a : ℝ) :
    evenCentralSoninDilationCornerAll a 1 zero_lt_one = 0 := by
  have hone : evenDilationSumAll 1 zero_lt_one =
      (1 : evenSubspace →L[ℂ] evenSubspace) + 1 := by
    dsimp [evenDilationSumAll]
    rw [evenDilationCLM_congr (inv_pos.mpr zero_lt_one) inv_one,
      evenDilationCLM_eq_one_of_eq_one zero_lt_one rfl]
  have hQ : IsIdempotentElem (evenCentralSoninProjection a) := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).isIdempotentElem_starProjection
  have hzero : ((1 : evenSubspace →L[ℂ] evenSubspace) - evenCentralSoninProjection a) *
      evenCentralSoninProjection a = 0 := by
    rw [sub_mul, one_mul, hQ.eq, sub_self]
  rw [evenCentralSoninDilationCornerAll, hone]
  calc ((1 : evenSubspace →L[ℂ] evenSubspace) - evenCentralSoninProjection a) *
      ((1 : evenSubspace →L[ℂ] evenSubspace) + 1) * evenCentralSoninProjection a =
      ((1 : evenSubspace →L[ℂ] evenSubspace) - evenCentralSoninProjection a) *
        evenCentralSoninProjection a +
      ((1 : evenSubspace →L[ℂ] evenSubspace) - evenCentralSoninProjection a) *
        evenCentralSoninProjection a := by
        simp only [mul_add, mul_one, add_mul]
    _ = 0 := by rw [hzero, zero_add]

/-- **All-scale exact essential norm.** For every positive scale different from one, the Sonin
dilation corner has essential norm exactly one. -/
theorem essentialNorm_evenCentralSoninDilationCornerAll
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (hne : r ≠ 1) :
    essentialNorm (evenCentralSoninDilationCornerAll a r hr) = 1 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hlt
    rw [← evenCentralSoninDilationCornerAll_inv a r hr,
      evenCentralSoninDilationCornerAll_eq a r⁻¹ hinv]
    exact essentialNorm_evenCentralSoninDilationCorner a r⁻¹ ha hinv
  · rw [evenCentralSoninDilationCornerAll_eq a r hgt]
    exact essentialNorm_evenCentralSoninDilationCorner a r ha hgt

/-- The essential-norm discontinuity of the corner family at the trivial scale. -/
theorem essentialNorm_evenCentralSoninDilationCornerAll_one (a : ℝ) :
    essentialNorm (evenCentralSoninDilationCornerAll a 1 zero_lt_one) = 0 := by
  rw [evenCentralSoninDilationCornerAll_one, essentialNorm_zero]

/-! ### The archimedean Euler semicommutator -/

theorem isIdempotentElem_archimedeanBoundaryCarrierProjection (a : ℝ) :
    IsIdempotentElem (archimedeanBoundaryCarrierProjection a) := by
  rw [archimedeanBoundaryCarrierProjection, hardyTitchmarshCarrierProjection]
  exact Submodule.isIdempotentElem_starProjection _

theorem adjoint_archimedeanBoundaryCarrierProjection (a : ℝ) :
    (archimedeanBoundaryCarrierProjection a)† = archimedeanBoundaryCarrierProjection a := by
  rw [archimedeanBoundaryCarrierProjection, hardyTitchmarshCarrierProjection]
  exact (isSelfAdjoint_starProjection _).star_eq

theorem adjoint_archimedeanPrimeEulerGram (p : ℝ) :
    (archimedeanPrimeEulerGram p)† = archimedeanPrimeEulerGram p := by
  change ContinuousLinearMap.adjoint
    ((archimedeanPrimeLocalFactor p)† ∘L archimedeanPrimeLocalFactor p) = _
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  rfl

/-- The diagonal compression defect of the positive Euler metric on the boundary carrier:
`Π G_p² Π − (Π G_p Π)²`. -/
def archimedeanPrimeEulerSemicommutator (a p : ℝ) :
    ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
  archimedeanBoundaryCarrierProjection a *
      (archimedeanPrimeEulerGram p * archimedeanPrimeEulerGram p) *
      archimedeanBoundaryCarrierProjection a -
    (archimedeanBoundaryCarrierProjection a * archimedeanPrimeEulerGram p *
        archimedeanBoundaryCarrierProjection a) *
      (archimedeanBoundaryCarrierProjection a * archimedeanPrimeEulerGram p *
        archimedeanBoundaryCarrierProjection a)

/-- The compression defect factors through the complement of the carrier projection: it is the
ordered quadratic Euler corner at equal scales. -/
theorem archimedeanPrimeEulerSemicommutator_eq_quadraticCorner (a p : ℝ) :
    archimedeanPrimeEulerSemicommutator a p =
      archimedeanPrimeEulerQuadraticCorner a p p := by
  set Pc : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
    archimedeanBoundaryCarrierProjection a with hPcdef
  set G : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2 :=
    archimedeanPrimeEulerGram p with hGdef
  have hPc : Pc * Pc = Pc := (isIdempotentElem_archimedeanBoundaryCarrierProjection a).eq
  have hcorner : archimedeanPrimeEulerCorner a p = (1 - Pc) * G * Pc := rfl
  have hadj : (archimedeanPrimeEulerCorner a p)† = Pc * (G * (1 - Pc)) := by
    rw [hcorner]
    change ContinuousLinearMap.adjoint (((1 - Pc) * G) ∘L Pc) = _
    rw [ContinuousLinearMap.adjoint_comp]
    change Pc† ∘L ContinuousLinearMap.adjoint ((1 - Pc) ∘L G) = _
    rw [ContinuousLinearMap.adjoint_comp,
      adjoint_one_sub (adjoint_archimedeanBoundaryCarrierProjection a),
      adjoint_archimedeanPrimeEulerGram,
      adjoint_archimedeanBoundaryCarrierProjection]
    rfl
  have hquad : archimedeanPrimeEulerQuadraticCorner a p p =
      (Pc * (G * (1 - Pc))) * ((1 - Pc) * G * Pc) := by
    rw [archimedeanPrimeEulerQuadraticCorner, hadj, hcorner]
    rfl
  rw [hquad]
  have h1 : (Pc * G * Pc) * (Pc * G * Pc) = Pc * G * (Pc * Pc) * G * Pc := by
    noncomm_ring
  have h2 : (Pc * (G * (1 - Pc))) * ((1 - Pc) * G * Pc) =
      Pc * (G * G) * Pc - Pc * G * ((Pc + Pc) - Pc * Pc) * G * Pc := by
    noncomm_ring
  change Pc * (G * G) * Pc - (Pc * G * Pc) * (Pc * G * Pc) = _
  rw [h1, h2, hPc]
  noncomm_ring

/-- The exact quadratic essential norm at equal scales, in closed form. -/
theorem essentialNorm_archimedeanPrimeEulerQuadraticCorner_self
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    essentialNorm (archimedeanPrimeEulerQuadraticCorner a p p) = (p : ℝ)⁻¹ := by
  rw [essentialNorm_archimedeanPrimeEulerQuadraticCorner a p p ha hp hp,
    Real.mul_self_sqrt (zero_lt_one.trans hp).le]

/-- **Exact essential norm of the Euler metric semicommutator:** `p⁻¹`. -/
theorem essentialNorm_archimedeanPrimeEulerSemicommutator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    essentialNorm (archimedeanPrimeEulerSemicommutator a p) = (p : ℝ)⁻¹ := by
  rw [archimedeanPrimeEulerSemicommutator_eq_quadraticCorner]
  exact essentialNorm_archimedeanPrimeEulerQuadraticCorner_self a p ha hp

/-- The semicommutator is noncompact; in particular the diagonal metric compression is not
multiplicative modulo compact operators. -/
theorem archimedeanPrimeEulerSemicommutator_not_isCompactOperator
    (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (archimedeanPrimeEulerSemicommutator a p) := by
  rw [archimedeanPrimeEulerSemicommutator_eq_quadraticCorner]
  exact archimedeanPrimeEulerQuadraticCorner_not_isCompactOperator a p p ha hp hp

end RHTower
