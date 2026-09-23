import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapAngularFluxCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceBaseDerivativeBounds
import GaloisForLFunctions.RHTower.SelbergScatteringSourceBounds
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMUniformCuspIntegration

/-!
The literal B2 cap angular flux has a noncompact horizontal cusp boundary.  The
existing pointwise rapid theorem is insufficient for that boundary: this file
upgrades it using the corpus's uniform all-weight tail and first-jet bounds.

Every term in the exact difference between the full Fourier flux and its Weyl
flux contains a genuine value, vertical-jet, or horizontal-jet tail.  The
finite expansion below preserves all terms, then proves the integrated limit.
No scalar cap action or fixed-horizontal decay surrogate is introduced.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
namespace RHTower.D4BMLiteralCyclicPeierlsCapAngularFluxIntegral
open D4BMAngularSeries D4BMGlobalAngularResponse
open D4BMCapAngularFluxCusp D4BMJointSource
noncomputable section
set_option autoImplicit false

private abbrev Field := (Fin 2 → ℝ) → ℂ

/-- Arbitrary complex-power bounds uniform over the whole exterior horizontal strip. -/
private def UniformCuspRapid (f : Field) : Prop :=
  ∀ w : ℂ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 1 ≤ y →
    ‖(y : ℂ) ^ w * f ![x, y]‖ ≤ C

private theorem UniformCuspRapid.add {f g : Field}
    (hf : UniformCuspRapid f) (hg : UniformCuspRapid g) :
    UniformCuspRapid (fun z => f z + g z) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  obtain ⟨B, hB, hb⟩ := hg w
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro x y hy
  rw [mul_add]
  exact (norm_add_le _ _).trans (add_le_add (ha x y hy) (hb x y hy))

private theorem UniformCuspRapid.scale (c : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun z => c * f z) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  refine ⟨‖c‖ * A, mul_nonneg (norm_nonneg _) hA, ?_⟩
  intro x y hy
  rw [mul_left_comm, norm_mul]
  exact mul_le_mul_of_nonneg_left (ha x y hy) (norm_nonneg _)

private theorem UniformCuspRapid.cpow (v : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun z => (z 1 : ℂ) ^ v * f z) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf (w + v)
  refine ⟨A, hA, ?_⟩
  intro x y hy
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_fin_one]
  rw [← mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hy).ne')]
  exact ha x y hy

private theorem UniformCuspRapid.mul {f g : Field}
    (hf : UniformCuspRapid f) (hg : UniformCuspRapid g) :
    UniformCuspRapid (fun z => f z * g z) := by
  intro w
  obtain ⟨A, hA, ha⟩ := hf w
  obtain ⟨B, hB, hb⟩ := hg 0
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro x y hy
  have hgb : ‖g ![x, y]‖ ≤ B := by
    simpa only [Complex.cpow_zero, one_mul] using hb x y hy
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul (ha x y hy) hgb (norm_nonneg _) hA

private theorem UniformCuspRapid.congr {f g : Field}
    (hf : UniformCuspRapid f)
    (he : ∀ x y : ℝ, 1 ≤ y → f ![x, y] = g ![x, y]) :
    UniformCuspRapid g := by
  intro w
  obtain ⟨C, hC, hb⟩ := hf w
  exact ⟨C, hC, fun x y hy => by rw [← he x y hy]; exact hb x y hy⟩

private def verticalTail (u : ℂ) : Field := fun z =>
  d4BMCompletedEisensteinCuspVerticalFirstJetTail u (z 0) (z 1)

private def horizontalTail (u : ℂ) : Field := fun z =>
  d4BMCompletedEisensteinCuspHorizontalFirstJetTail u (z 0) (z 1)

private def principalVertical (u : ℂ) : Field := fun z =>
  d4BMCanonicalCuspConstantVerticalFirstJet u (z 1)

private theorem verticalTail_eq_coordDeriv (u : ℂ) (x : ℝ) (Y : Ici (1 : ℝ)) :
    verticalTail u ![x, Y.val] = coordDeriv 1 (tail u) ![x, Y.val] := by
  let z : Fin 2 → ℝ := ![x, Y.val]
  have hz : 0 < z 1 := zero_lt_one.trans_le Y.property
  have hf : DifferentiableAt ℝ (tail u) z := by
    change DifferentiableAt ℝ (fun v : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspTailPart .scalar u (v 0) (v 1)) z
    exact ((cuspTailPart_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
        (by norm_num)
  have hd : HasDerivAt (fun t => tail u (Function.update z 1 t))
      (coordDeriv 1 (tail u) z) (z 1) := by
    have hf' : HasFDerivAt (tail u) (fderiv ℝ (tail u) z)
        (Function.update z 1 (z 1)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hh := hf'.comp_hasDerivAt (z 1) (hasDerivAt_update z 1 (z 1))
    convert hh using 1 <;> rfl
  have hp := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_vertical
    u u false x Y
  have hn := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_vertical
    u u true x Y
  have ht : HasDerivAt (fun t => tail u ![x, t]) (verticalTail u z) Y.val := by
    simpa [z, tail, verticalTail, d4BMCompletedEisensteinCuspVerticalFirstJetTail,
      d4BMCompletedEisensteinCuspTailPart,
      d4BMCompletedEisensteinFullSignedZeroWord] using (hp.add hn).const_mul (2 : ℂ)
  have hd' : HasDerivAt (fun t => tail u ![x, t])
      (coordDeriv 1 (tail u) z) Y.val := by
    have hupd : ∀ t : ℝ, Function.update z 1 t = ![x, t] := fun t => by
      funext i
      fin_cases i <;> simp [z, Function.update]
    simpa only [hupd, z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hd
  simpa [z] using ht.unique hd'

private theorem horizontalTail_eq_coordDeriv (u : ℂ) (x : ℝ) (Y : Ici (1 : ℝ)) :
    horizontalTail u ![x, Y.val] = coordDeriv 0 (tail u) ![x, Y.val] := by
  let z : Fin 2 → ℝ := ![x, Y.val]
  have hz : 0 < z 1 := zero_lt_one.trans_le Y.property
  have hf : DifferentiableAt ℝ (tail u) z := by
    change DifferentiableAt ℝ (fun v : Fin 2 → ℝ =>
      d4BMCompletedEisensteinCuspTailPart .scalar u (v 0) (v 1)) z
    exact ((cuspTailPart_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
        (by norm_num)
  have hd : HasDerivAt (fun t => tail u (Function.update z 0 t))
      (coordDeriv 0 (tail u) z) (z 0) := by
    have hf' : HasFDerivAt (tail u) (fderiv ℝ (tail u) z)
        (Function.update z 0 (z 0)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have hh := hf'.comp_hasDerivAt (z 0) (hasDerivAt_update z 0 (z 0))
    convert hh using 1 <;> rfl
  have hp := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_horizontal
    u u false x Y
  have hn := hasDerivAt_d4BMCompletedEisensteinSignedSqrtWhittakerTail_horizontal
    u u true x Y
  have ht : HasDerivAt (fun t => tail u ![t, Y.val]) (horizontalTail u z) x := by
    simpa [z, tail, horizontalTail, d4BMCompletedEisensteinCuspHorizontalFirstJetTail,
      d4BMCompletedEisensteinCuspTailPart,
      d4BMCompletedEisensteinFullSignedZeroWord] using (hp.add hn).const_mul (2 : ℂ)
  have hd' : HasDerivAt (fun t => tail u ![t, Y.val])
      (coordDeriv 0 (tail u) z) x := by
    have hupd : ∀ t : ℝ, Function.update z 0 t = ![t, Y.val] := fun t => by
      funext i
      fin_cases i <;> simp [z, Function.update]
    simpa only [hupd, z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hd
  simpa [z] using ht.unique hd'

private theorem tail_uniform (u : ℂ) : UniformCuspRapid (tail u) := by
  intro w
  obtain ⟨C, hC, hb⟩ := weighted_tail_bounded u w 1 (by norm_num)
  exact ⟨C, hC, fun x y hy => by simpa using hb ![x, y] hy⟩

private theorem verticalTail_uniform (u : ℂ) : UniformCuspRapid (verticalTail u) := by
  intro w
  obtain ⟨C, hC, hb⟩ :=
    SelbergScatteringSourceBounds.weighted_tail_vertical_bounded u w 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro x y hy
  rw [verticalTail_eq_coordDeriv u x ⟨y, hy⟩]
  simpa using hb ![x, y] hy

private theorem horizontalTail_uniform (u : ℂ) : UniformCuspRapid (horizontalTail u) := by
  intro w
  obtain ⟨C, hC, hb⟩ :=
    D4BMFullSourceBaseDerivativeBounds.weighted_tail_horizontal_bounded u w 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro x y hy
  rw [horizontalTail_eq_coordDeriv u x ⟨y, hy⟩]
  simpa using hb ![x, y] hy

private theorem UniformCuspRapid.principal_mul (u : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun z => principal u z * f z) := by
  let e0 := d4BMCompletedEisensteinCuspWeylExponent u false
  let e1 := d4BMCompletedEisensteinCuspWeylExponent u true
  let A := d4BMCompletedEisensteinCuspConstantCoefficient u false
  let B := d4BMCompletedEisensteinCuspConstantCoefficient u true
  apply (((hf.cpow e0).scale A).add ((hf.cpow e1).scale B)).congr
  intro x y hy
  dsimp [D4BMGlobalAngularResponse.principal, e0, e1, A, B,
    d4BMCompletedEisensteinCuspConstantPart, d4BMCompletedEisensteinCuspConstantTerm,
    d4BMCompletedEisensteinCuspConstantMaassFactor]
  ring

private theorem UniformCuspRapid.principalVertical_mul (u : ℂ) {f : Field}
    (hf : UniformCuspRapid f) :
    UniformCuspRapid (fun z => principalVertical u z * f z) := by
  let e0 := d4BMCompletedEisensteinCuspWeylExponent u false
  let e1 := d4BMCompletedEisensteinCuspWeylExponent u true
  let A := d4BMCompletedEisensteinCuspConstantCoefficient u false
  let B := d4BMCompletedEisensteinCuspConstantCoefficient u true
  apply ((((hf.cpow e0).cpow (-1 : ℂ)).scale (A * e0)).add
    (((hf.cpow e1).cpow (-1 : ℂ)).scale (B * e1))).congr
  intro x y hy
  dsimp [principalVertical, e0, e1, A, B,
    d4BMCanonicalCuspConstantVerticalFirstJet]
  ring

private def fullVerticalFluxModel (u v : ℂ) : Field := fun z =>
  let F := principal u z + tail u z
  let S := principal v z + tail v z
  let Fx := horizontalTail u z
  let Fy := principalVertical u z + verticalTail u z
  let Sy := principalVertical v z + verticalTail v z
  (v ^ (2 : ℕ) - 1 / 4) * S * F * Fy -
    ((u ^ (2 : ℕ) - 1 / 4) * F ^ (2 : ℕ) + (z 1 : ℂ) ^ (2 : ℕ) * (Fx ^ (2 : ℕ) + Fy ^ (2 : ℕ))) * Sy

private def constantVerticalFluxModel (u v : ℂ) : Field := fun z =>
  let F := principal u z
  let S := principal v z
  let Fy := principalVertical u z
  let Sy := principalVertical v z
  (v ^ (2 : ℕ) - 1 / 4) * S * F * Fy -
    ((u ^ (2 : ℕ) - 1 / 4) * F ^ (2 : ℕ) + (z 1 : ℂ) ^ (2 : ℕ) * Fy ^ (2 : ℕ)) * Sy

private theorem fullVerticalFlux_eq_model (u v : ℂ) (z : Fin 2 → ℝ) :
    fullVerticalFlux u v (z 0) (z 1) = fullVerticalFluxModel u v z := by
  rfl

private theorem constantVerticalFlux_eq_model (u v : ℂ) (z : Fin 2 → ℝ) :
    constantVerticalFlux u v (z 1) = constantVerticalFluxModel u v z := by
  rfl

private theorem fullVerticalFluxModel_remainder_uniform (u v : ℂ) :
    UniformCuspRapid (fun z => fullVerticalFluxModel u v z - constantVerticalFluxModel u v z) := by
  let F0 : Field := principal u
  let S0 : Field := principal v
  let Fy0 : Field := principalVertical u
  let Sy0 : Field := principalVertical v
  let f : Field := tail u
  let s : Field := tail v
  let fy : Field := verticalTail u
  let sy : Field := verticalTail v
  let fx : Field := horizontalTail u
  have hf : UniformCuspRapid f := tail_uniform u
  have hs : UniformCuspRapid s := tail_uniform v
  have hfy : UniformCuspRapid fy := verticalTail_uniform u
  have hsy : UniformCuspRapid sy := verticalTail_uniform v
  have hfx : UniformCuspRapid fx := horizontalTail_uniform u
  have hA1 : UniformCuspRapid (fun z => s z * F0 z * Fy0 z) := by
    apply ((hs.principal_mul u).principalVertical_mul u).congr
    intro x y hy
    dsimp [F0, Fy0, s]
    ring
  have hA2 : UniformCuspRapid (fun z => S0 z * f z * Fy0 z) := by
    apply ((hf.principal_mul v).principalVertical_mul u).congr
    intro x y hy
    dsimp [S0, Fy0, f]
    ring
  have hA3 : UniformCuspRapid (fun z => S0 z * F0 z * fy z) := by
    apply ((hfy.principal_mul u).principal_mul v).congr
    intro x y hy
    dsimp [S0, F0, fy]
    ring
  have hA4 : UniformCuspRapid (fun z => s z * f z * Fy0 z) := by
    apply ((hs.mul hf).principalVertical_mul u).congr
    intro x y hy
    dsimp [Fy0, s, f]
    ring
  have hA5 : UniformCuspRapid (fun z => s z * F0 z * fy z) := by
    apply ((hs.mul hfy).principal_mul u).congr
    intro x y hy
    dsimp [F0, s, fy]
    ring
  have hA6 : UniformCuspRapid (fun z => S0 z * f z * fy z) := by
    apply ((hf.mul hfy).principal_mul v).congr
    intro x y hy
    dsimp [S0, f, fy]
    ring
  have hA7 : UniformCuspRapid (fun z => s z * f z * fy z) :=
    (hs.mul hf).mul hfy
  have hA : UniformCuspRapid (fun z =>
      (S0 z + s z) * (F0 z + f z) * (Fy0 z + fy z) - S0 z * F0 z * Fy0 z) := by
    apply ((((((hA1.add hA2).add hA3).add hA4).add hA5).add hA6).add hA7).congr
    intro x y hy
    dsimp [F0, S0, Fy0, f, s, fy]
    ring
  have hB1 : UniformCuspRapid (fun z => F0 z * f z * Sy0 z) := by
    apply ((hf.principal_mul u).principalVertical_mul v).congr
    intro x y hy
    dsimp [F0, Sy0, f]
    ring
  have hB2 : UniformCuspRapid (fun z => f z * f z * Sy0 z) := by
    apply ((hf.mul hf).principalVertical_mul v).congr
    intro x y hy
    dsimp [Sy0, f]
    ring
  have hB3 : UniformCuspRapid (fun z => F0 z * F0 z * sy z) := by
    apply ((hsy.principal_mul u).principal_mul u).congr
    intro x y hy
    dsimp [F0, sy]
    ring
  have hB4 : UniformCuspRapid (fun z => F0 z * f z * sy z) := by
    apply ((hf.mul hsy).principal_mul u).congr
    intro x y hy
    dsimp [F0, f, sy]
    ring
  have hB5 : UniformCuspRapid (fun z => f z * f z * sy z) :=
    (hf.mul hf).mul hsy
  have hB : UniformCuspRapid (fun z =>
      (F0 z + f z) ^ (2 : ℕ) * (Sy0 z + sy z) - F0 z ^ (2 : ℕ) * Sy0 z) := by
    apply (((((hB1.scale 2).add hB2).add hB3).add (hB4.scale 2)).add hB5).congr
    intro x y hy
    dsimp [F0, Sy0, f, sy]
    ring
  have hC1 : UniformCuspRapid (fun z => Fy0 z * fy z * Sy0 z) := by
    apply ((hfy.principalVertical_mul u).principalVertical_mul v).congr
    intro x y hy
    dsimp [Fy0, Sy0, fy]
    ring
  have hC2 : UniformCuspRapid (fun z => fy z * fy z * Sy0 z) := by
    apply ((hfy.mul hfy).principalVertical_mul v).congr
    intro x y hy
    dsimp [Sy0, fy]
    ring
  have hC3 : UniformCuspRapid (fun z => Fy0 z * Fy0 z * sy z) := by
    apply ((hsy.principalVertical_mul u).principalVertical_mul u).congr
    intro x y hy
    dsimp [Fy0, sy]
    ring
  have hC4 : UniformCuspRapid (fun z => Fy0 z * fy z * sy z) := by
    apply ((hfy.mul hsy).principalVertical_mul u).congr
    intro x y hy
    dsimp [Fy0, fy, sy]
    ring
  have hC5 : UniformCuspRapid (fun z => fy z * fy z * sy z) :=
    (hfy.mul hfy).mul hsy
  have hC : UniformCuspRapid (fun z =>
      (Fy0 z + fy z) ^ (2 : ℕ) * (Sy0 z + sy z) - Fy0 z ^ (2 : ℕ) * Sy0 z) := by
    apply (((((hC1.scale 2).add hC2).add hC3).add (hC4.scale 2)).add hC5).congr
    intro x y hy
    dsimp [Fy0, Sy0, fy, sy]
    ring
  have hD1 : UniformCuspRapid (fun z => fx z ^ (2 : ℕ) * Sy0 z) := by
    apply ((hfx.mul hfx).principalVertical_mul v).congr
    intro x y hy
    dsimp [Sy0, fx]
    ring
  have hD2 : UniformCuspRapid (fun z => fx z ^ (2 : ℕ) * sy z) := by
    apply ((hfx.mul hfx).mul hsy).congr
    intro x y hy
    dsimp [fx, sy]
    ring
  have hD : UniformCuspRapid (fun z => fx z ^ (2 : ℕ) * (Sy0 z + sy z)) := by
    apply (hD1.add hD2).congr
    intro x y hy
    dsimp [Sy0, fx, sy]
    ring
  have hCD : UniformCuspRapid (fun z =>
      (z 1 : ℂ) ^ (2 : ℕ) *
        ((Fy0 z + fy z) ^ (2 : ℕ) * (Sy0 z + sy z) - Fy0 z ^ (2 : ℕ) * Sy0 z +
          fx z ^ (2 : ℕ) * (Sy0 z + sy z))) := by
    apply ((hC.add hD).cpow (2 : ℂ)).congr
    intro x y hy
    rw [Complex.cpow_two]
  have hmain := ((hA.scale (v ^ (2 : ℕ) - 1 / 4)).add
    (hB.scale (-(u ^ (2 : ℕ) - 1 / 4)))).add (hCD.scale (-1))
  apply hmain.congr
  intro x y hy
  dsimp [fullVerticalFluxModel, constantVerticalFluxModel,
    F0, S0, Fy0, Sy0, f, s, fy, sy, fx]
  ring

private theorem UniformCuspRapid.integral_vanish {f : Field}
    (hf : UniformCuspRapid f) (w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1 / 2 : ℝ)..1 / 2,
      (y : ℂ) ^ w * f ![x, y]) atTop (𝓝 0) := by
  exact D4BMUniformCuspIntegration.UniformCuspRapid.integral_vanish
    (f := fun x y => f ![x, y]) (by
      intro v
      exact hf v) w

/-- Literal full Fourier cap flux, after subtraction of its exact Weyl flux,
has a vanishing horizontal cusp integral after every complex height weight. -/
theorem fullVerticalFlux_remainder_integral_tendsto_zero (u v w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1 / 2 : ℝ)..1 / 2,
      (y : ℂ) ^ w *
        (fullVerticalFlux u v x y - constantVerticalFlux u v y)) atTop (𝓝 0) := by
  apply ((fullVerticalFluxModel_remainder_uniform u v).integral_vanish w).congr'
  filter_upwards with y
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x _
  rw [← fullVerticalFlux_eq_model u v ![x, y], ← constantVerticalFlux_eq_model u v ![x, y]]
  simp

/-- The same all-weight integrated cusp law for the actual literal B2 cap
angular current.  This is the noncompact boundary input missing from B2. -/
theorem angularFlux_remainder_integral_tendsto_zero (q r : XiZeroCopy) (w : ℂ) :
    Tendsto (fun y : ℝ => ∫ x in (-1 / 2 : ℝ)..1 / 2,
      (y : ℂ) ^ w *
        (angularFlux q r 1 ![x, y] -
          constantVerticalFlux (center q) (physicalAngularParameter r) y)) atTop (𝓝 0) := by
  apply (fullVerticalFlux_remainder_integral_tendsto_zero
    (center q) (physicalAngularParameter r) w).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  apply intervalIntegral.integral_congr_ae
  filter_upwards with x _
  rw [angularFlux_full_cusp q r x ⟨y, hy⟩]

end
end RHTower.D4BMLiteralCyclicPeierlsCapAngularFluxIntegral
