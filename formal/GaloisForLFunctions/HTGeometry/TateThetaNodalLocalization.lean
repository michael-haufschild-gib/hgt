import GaloisForLFunctions.HTGeometry.TateThetaTransgression
import GaloisForLFunctions.HTGeometry.SourceFaceObservationExcess
import GaloisForLFunctions.HTGeometry.NodalChargeCharacterRealization
import GaloisForLFunctions.HTGeometry.GrothendieckKTheoryIntersectionApplications

/-!
# Exact nodal factorization of the Tate-theta gauge
-/

open Complex Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product tail in the exceptional theta factor on the nodal chart `x*y=t`. -/
def tateThetaExceptionalTail (r : TateQuarterNome) (x y : ℂ) : ℂ :=
  qPochhammerInf ((r.root : ℂ) ^ 3 * x) r.nome *
    qPochhammerInf ((r.root : ℂ) ^ 4 * y) r.nome

/-- Product tail in the ordinary denominator theta factor on the nodal chart. -/
def tateThetaDenominatorTail (r : TateQuarterNome) (x y : ℂ) : ℂ :=
  qPochhammerInf ((r.root : ℂ) * x) r.nome *
    qPochhammerInf ((r.root : ℂ) ^ 2 * y) r.nome

/-- Exact unit factor left after extracting the nodal coordinate from the Tate-theta gauge. -/
def tateThetaNodalUnitFactor (r : TateQuarterNome) (x y : ℂ) : ℂ :=
  (1 - y) ^ 2 * tateThetaExceptionalTail r x y ^ 2 /
    tateThetaDenominatorTail r x y ^ 2

/-- Analytic neighborhood of the node on which every formal unit factor is genuinely nonzero. -/
structure TateNodalUnitDatum where
  r : TateQuarterNome
  x : ℂ
  y : ℂ
  xy_eq_root : x * y = (r.root : ℂ)
  y_norm_lt_one : ‖y‖ < 1
  root_cube_x_norm_lt_one : ‖(r.root : ℂ) ^ 3 * x‖ < 1
  root_four_y_norm_lt_one : ‖(r.root : ℂ) ^ 4 * y‖ < 1
  root_x_norm_lt_one : ‖(r.root : ℂ) * x‖ < 1
  root_sq_y_norm_lt_one : ‖(r.root : ℂ) ^ 2 * y‖ < 1

namespace TateNodalUnitDatum

theorem exceptionalTail_ne_zero (d : TateNodalUnitDatum) :
    tateThetaExceptionalTail d.r d.x d.y ≠ 0 := by
  apply mul_ne_zero
  · exact qPochhammerInf_ne_zero
      { a := (d.r.root : ℂ) ^ 3 * d.x
        q := d.r.nome
        a_norm_lt_one := d.root_cube_x_norm_lt_one }
  · exact qPochhammerInf_ne_zero
      { a := (d.r.root : ℂ) ^ 4 * d.y
        q := d.r.nome
        a_norm_lt_one := d.root_four_y_norm_lt_one }

theorem denominatorTail_ne_zero (d : TateNodalUnitDatum) :
    tateThetaDenominatorTail d.r d.x d.y ≠ 0 := by
  apply mul_ne_zero
  · exact qPochhammerInf_ne_zero
      { a := (d.r.root : ℂ) * d.x
        q := d.r.nome
        a_norm_lt_one := d.root_x_norm_lt_one }
  · exact qPochhammerInf_ne_zero
      { a := (d.r.root : ℂ) ^ 2 * d.y
        q := d.r.nome
        a_norm_lt_one := d.root_sq_y_norm_lt_one }

/-- The extracted nodal factor is an analytic unit on its encoded neighborhood. -/
theorem nodalUnitFactor_ne_zero (d : TateNodalUnitDatum) :
    tateThetaNodalUnitFactor d.r d.x d.y ≠ 0 := by
  have hy : 1 - d.y ≠ 0 := sub_ne_zero.mpr (by
    intro h
    have hnorm := d.y_norm_lt_one
    rw [← h] at hnorm
    norm_num at hnorm)
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 d.exceptionalTail_ne_zero))
    (pow_ne_zero 2 d.denominatorTail_ne_zero)

end TateNodalUnitDatum

/-- First exact nodal theta factorization. -/
theorem root_mul_multiplicativeTheta_root_inv_mul
    (r : TateQuarterNome) {x y : ℂ} (hxy : x * y = (r.root : ℂ)) :
    (r.root : ℂ) * multiplicativeTheta r.nome ((r.root : ℂ)⁻¹ * x) =
      ((r.root : ℂ) - x) * tateThetaExceptionalTail r x y := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    exact r.root_complex_ne_zero hxy.symm
  rw [multiplicativeTheta, qPochhammerInf_shift]
  unfold tateThetaExceptionalTail
  have harg₁ : ((r.root : ℂ)⁻¹ * x) * (r.nome : ℂ) =
      (r.root : ℂ) ^ 3 * x := by
    rw [TateQuarterNome.coe_nome]
    field_simp [r.root_complex_ne_zero]
  have harg₂ : (r.nome : ℂ) / ((r.root : ℂ)⁻¹ * x) =
      (r.root : ℂ) ^ 4 * y := by
    rw [TateQuarterNome.coe_nome]
    field_simp [r.root_complex_ne_zero, hx]
    rw [hxy]
  rw [harg₁, harg₂]
  field_simp [r.root_complex_ne_zero]

/-- Second exact nodal theta factorization. -/
theorem multiplicativeTheta_root_cube_mul
    (r : TateQuarterNome) {x y : ℂ} (hxy : x * y = (r.root : ℂ)) :
    multiplicativeTheta r.nome ((r.root : ℂ) ^ 3 * x) =
      (1 - y) * tateThetaExceptionalTail r x y := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    exact r.root_complex_ne_zero hxy.symm
  rw [multiplicativeTheta]
  have harg : (r.nome : ℂ) / ((r.root : ℂ) ^ 3 * x) = y := by
    rw [TateQuarterNome.coe_nome]
    field_simp [r.root_complex_ne_zero, hx]
    rw [hxy]
  rw [harg, qPochhammerInf_shift y]
  have htail : y * (r.nome : ℂ) = (r.root : ℂ) ^ 4 * y := by
    rw [TateQuarterNome.coe_nome]
    ring
  rw [htail]
  unfold tateThetaExceptionalTail
  ring

/-- Exact denominator theta factorization. -/
theorem multiplicativeTheta_root_mul
    (r : TateQuarterNome) {x y : ℂ} (hxy : x * y = (r.root : ℂ)) :
    multiplicativeTheta r.nome ((r.root : ℂ) * x) =
      tateThetaDenominatorTail r x y := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxy
    exact r.root_complex_ne_zero hxy.symm
  rw [multiplicativeTheta]
  have harg : (r.nome : ℂ) / ((r.root : ℂ) * x) =
      (r.root : ℂ) ^ 2 * y := by
    rw [TateQuarterNome.coe_nome]
    field_simp [r.root_complex_ne_zero, hx]
    rw [hxy]
  rw [harg]
  rfl

/-- Exact nodal localization factorization `E=x*u`. -/
theorem tateThetaGauge_eq_coordinate_mul_nodalUnit
    (r : TateQuarterNome) {x y : ℂ} (hxy : x * y = (r.root : ℂ)) :
    tateThetaGauge r x = x * tateThetaNodalUnitFactor r x y := by
  have h₁ := root_mul_multiplicativeTheta_root_inv_mul r hxy
  have h₂ := multiplicativeTheta_root_cube_mul r hxy
  have h₃ := multiplicativeTheta_root_mul r hxy
  have htx : (r.root : ℂ) - x = -x * (1 - y) := by
    rw [← hxy]
    ring
  have hnum :
      -(r.root : ℂ) * multiplicativeTheta r.nome ((r.root : ℂ)⁻¹ * x) *
          multiplicativeTheta r.nome ((r.root : ℂ) ^ 3 * x) =
        x * (1 - y) ^ 2 * tateThetaExceptionalTail r x y ^ 2 := by
    calc
      _ = -((r.root : ℂ) * multiplicativeTheta r.nome ((r.root : ℂ)⁻¹ * x)) *
          multiplicativeTheta r.nome ((r.root : ℂ) ^ 3 * x) := by ring
      _ = -((r.root : ℂ) - x) * tateThetaExceptionalTail r x y *
          multiplicativeTheta r.nome ((r.root : ℂ) ^ 3 * x) := by
        rw [h₁]
        ring
      _ = -((r.root : ℂ) - x) * tateThetaExceptionalTail r x y *
          ((1 - y) * tateThetaExceptionalTail r x y) :=
        congrArg (fun z => -((r.root : ℂ) - x) * tateThetaExceptionalTail r x y * z) h₂
      _ = x * (1 - y) ^ 2 * tateThetaExceptionalTail r x y ^ 2 := by
        rw [htx]
        ring
  unfold tateThetaGauge
  have hneg : (r.root : ℂ) ^ (-1 : ℤ) = (r.root : ℂ)⁻¹ := by simp
  have hone : (r.root : ℂ) ^ (1 : ℤ) = (r.root : ℂ) := by simp
  rw [hneg, hone]
  simp only [div_eq_mul_inv]
  calc
    _ = (x * (1 - y) ^ 2 * tateThetaExceptionalTail r x y ^ 2) *
        (multiplicativeTheta r.nome ((r.root : ℂ) * x) ^ 2)⁻¹ :=
      congrArg (fun z : ℂ => z *
        (multiplicativeTheta r.nome ((r.root : ℂ) * x) ^ 2)⁻¹) hnum
    _ = (x * (1 - y) ^ 2 * tateThetaExceptionalTail r x y ^ 2) *
        (tateThetaDenominatorTail r x y ^ 2)⁻¹ := by rw [h₃]
    _ = x * tateThetaNodalUnitFactor r x y := by
      unfold tateThetaNodalUnitFactor
      ring

/-- The extracted nodal unit has constant term one: along every degeneration with
`r→0`, `x→0`, and `y→0`, it converges to `1`. -/
theorem tendsto_tateThetaNodalUnitFactor_one
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome) (x y : ι → ℂ)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    (hx : Tendsto x l (nhds 0)) (hy : Tendsto y l (nhds 0)) :
    Tendsto (fun i => tateThetaNodalUnitFactor (r i) (x i) (y i)) l (nhds 1) := by
  have hq := tendsto_tateQuarterNome_nome_zero r hr
  have hrC := hr.ofReal
  have ha : Tendsto (fun i => ((r i).root : ℂ) ^ 3 * x i) l (nhds 0) := by
    convert (hrC.pow 3).mul hx using 1 <;> norm_num
  have hb : Tendsto (fun i => ((r i).root : ℂ) ^ 4 * y i) l (nhds 0) := by
    convert (hrC.pow 4).mul hy using 1 <;> norm_num
  have hc : Tendsto (fun i => ((r i).root : ℂ) * x i) l (nhds 0) := by
    convert hrC.mul hx using 1 <;> norm_num
  have hd : Tendsto (fun i => ((r i).root : ℂ) ^ 2 * y i) l (nhds 0) := by
    convert (hrC.pow 2).mul hy using 1 <;> norm_num
  have hpa := tendsto_qPochhammerInf_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) ^ 3 * x i) (fun i => (r i).nome) ha hq
  have hpb := tendsto_qPochhammerInf_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) ^ 4 * y i) (fun i => (r i).nome) hb hq
  have hpc := tendsto_qPochhammerInf_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) * x i) (fun i => (r i).nome) hc hq
  have hpd := tendsto_qPochhammerInf_one_of_tendsto_zero
    (fun i => ((r i).root : ℂ) ^ 2 * y i) (fun i => (r i).nome) hd hq
  have hexceptional : Tendsto
      (fun i => tateThetaExceptionalTail (r i) (x i) (y i)) l (nhds 1) := by
    simpa [tateThetaExceptionalTail] using hpa.mul hpb
  have hdenominator : Tendsto
      (fun i => tateThetaDenominatorTail (r i) (x i) (y i)) l (nhds 1) := by
    simpa [tateThetaDenominatorTail] using hpc.mul hpd
  have hy' : Tendsto (fun i => 1 - y i) l (nhds 1) := by
    convert tendsto_const_nhds.sub hy using 1 <;> norm_num
  have hlimit := ((hy'.pow 2).mul (hexceptional.pow 2)).div
    (hdenominator.pow 2) (pow_ne_zero 2 one_ne_zero)
  change Tendsto (fun i =>
    (1 - y i) ^ 2 * tateThetaExceptionalTail (r i) (x i) (y i) ^ 2 /
      tateThetaDenominatorTail (r i) (x i) (y i) ^ 2) l (nhds 1)
  convert hlimit using 1
  · funext i
    rfl
  · norm_num

/-- On the analytic nodal neighborhood, the Tate-theta gauge differs from the selected coordinate
by a nonzero unit and hence carries the same local principal divisor. -/
theorem tateThetaGauge_eq_coordinate_mul_unit (d : TateNodalUnitDatum) :
    tateThetaGauge d.r d.x = d.x * tateThetaNodalUnitFactor d.r d.x d.y ∧
      tateThetaNodalUnitFactor d.r d.x d.y ≠ 0 :=
  ⟨tateThetaGauge_eq_coordinate_mul_nodalUnit d.r d.xy_eq_root,
    d.nodalUnitFactor_ne_zero⟩

/-! ## Integral localization boundary on the nodal character lattice -/

/-- Integral localization boundary on the monomial `K₁` lattice of the punctured nodal chart.
The target is the Grothendieck completion of effective copies of the supported face class. -/
def tateNodalLocalizationBoundary : ℤ →+ NaturalMultiplicityK0 :=
  integerToNaturalMultiplicityK0

/-- Exact localization formula `∂[x^m] = m[A/(x)]`, including negative orientation. -/
theorem tateNodalLocalizationBoundary_class (m : ℤ) :
    naturalMultiplicityK0Class (tateNodalLocalizationBoundary m) = m :=
  naturalMultiplicityK0Class_rightInverse m

/-- The coherent localization multiplicity and the complete oriented analytic charge interval
have the same decategorified value. -/
theorem tateNodalLocalizationBoundary_eq_chargeInterval
    (ω : ℂ) (m : ℕ) (z : ℂ) :
    ((naturalMultiplicityK0Class
        (tateNodalLocalizationBoundary (m : ℤ)) : ℤ) : ℂ) =
      nodalChargeBoundaryIntervalPairing ω m z := by
  rw [tateNodalLocalizationBoundary_class,
    nodalChargeBoundaryIntervalPairing_eq]
  norm_num

end

end GaloisForLFunctions.HTGeometry
