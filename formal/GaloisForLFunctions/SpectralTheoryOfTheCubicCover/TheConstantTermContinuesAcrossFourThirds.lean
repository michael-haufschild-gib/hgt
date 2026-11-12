import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicConstantTermPole
import GaloisForLFunctions.FamilyContinuationTheory.TheHeckeFamilyOfTheThirdCyclotomicFieldContainsZeta
import GaloisForLFunctions.RHTower.ZetaDiscUniformCarlsonTail

/-!
# The constant term of the cubic Eisenstein series continues across `4/3`

The constant term of the cubic Eisenstein series at height `v` is `v^s + v^{2−s} (π/(s − 1)) φ(s)`
for `Re s > 2`, and for `Re s > 4/3` the scattering coefficient is (MMD,
`scatteringCoefficient_zero_zeta`)

`φ(s) = (2/|P|) (3^{3s−3} − 1)⁻¹ Z₀(3s − 3)/Z₀(3s − 2)`,   `Z₀(u) = (1 − 3^{−u}) ζ_K(u)`,

with `K = ℚ(ζ₃)`. Since `ζ_K(u) = ζ(u) L(u, χ₋₃)` and `(u − 1) ζ(u)` is entire, the pole-cleared
coefficient

`(s − 4/3) φ(s) = (2/|P|) (3^{3s−3} − 1)⁻¹ (1 − 3^{3−3s}) (3s − 4)ζ(3s − 3) L(3s − 3, χ₋₃) / (3 Z₀(3s − 2))`

(`clearedScattering`, `sub_mul_scatteringCoefficient`) is holomorphic on `Re s > 1`
(`clearedScattering_differentiableOn`), and its value at `4/3` is MMD's nonzero arithmetic residue `r`
(`clearedScattering_four_thirds`), using `Res_{u=1} ζ_K = L(1, χ₋₃)` (`dedekindZeta_residue_eq`).
So `φ` has a two-sided simple pole at `4/3` with residue `r ≠ 0`, and the constant term has residue
`3π r v^{2/3}` there (`clearedConstantTerm_four_thirds`): the constant term of the residue `θ`. Its
constant Laurent coefficient at `4/3` is `v^{4/3} + v^{2/3}(g'(4/3) − 3π r log v)`
(`hasDerivAt_clearedConstantTerm`, `g = scatteringFactor`): the term `v^{2/3} log v` that produces the
double pole in the renormalization of `θ²`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.SpectralTheoryOfTheCubicCover

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicEisenstein
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The area `|P| = 9√3/2` of the period parallelogram. -/
abbrev cuspArea : ℂ := ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)

theorem cuspArea_ne_zero : cuspArea ≠ 0 := cusp_volume_ne_zero

/-- The pole-cleared scattering coefficient `(s − 4/3) φ(s)`. -/
def clearedScattering (s : ℂ) : ℂ :=
  (2 / cuspArea) * ((3 : ℂ) ^ (3 * s - 3) - 1)⁻¹ * (1 - (3 : ℂ) ^ (-(3 * s - 3))) *
    (_root_.RHTower.zetaPoleFilled (3 * s - 3) * DirichletCharacter.LFunction chi3D (3 * s - 3)) /
      (3 * unramifiedIdealZeta (3 * s - 2))

/-- `3^{3s−3} ≠ 1` on `Re s > 1`. -/
theorem three_cpow_ne_one {s : ℂ} (hs : 1 < s.re) : (3 : ℂ) ^ (3 * s - 3) - 1 ≠ 0 := by
  intro h
  have hn : ‖(3 : ℂ) ^ (3 * s - 3)‖ = 1 := by rw [sub_eq_zero.mp h, norm_one]
  have hre : 0 < (3 * s - 3).re := by
    have : (3 * s - 3).re = 3 * s.re - 3 := by simp
    rw [this]
    linarith
  have hn' : ‖(3 : ℂ) ^ (3 * s - 3)‖ = (3 : ℝ) ^ (3 * s - 3).re := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (show (0 : ℝ) < 3 by norm_num) (3 * s - 3)
    simpa using this
  have := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 3) hre
  linarith

/-- **The cleared coefficient.** For `Re s > 4/3`, `(s − 4/3) φ(s)` is `clearedScattering s`. -/
theorem sub_mul_scatteringCoefficient {s : ℂ} (hs : (4 : ℝ) / 3 < s.re) :
    (s - 4 / 3) * scatteringCoefficient s 0 = clearedScattering s := by
  have hu : 1 < (3 * s - 3).re := by
    have : (3 * s - 3).re = 3 * s.re - 3 := by simp
    rw [this]
    linarith
  have hu2 : 1 < (3 * s - 2).re := by
    have : (3 * s - 2).re = 3 * s.re - 2 := by simp
    rw [this]
    linarith
  have h1 : 3 * s - 3 ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hA := three_cpow_ne_one (by linarith : 1 < s.re)
  have hZ := unramifiedIdealZeta_ne_zero _ hu2
  have hV := cuspArea_ne_zero
  rw [scatteringCoefficient_zero_zeta s hs, unramifiedIdealZeta_eq_dedekindZeta _ hu,
    dedekindZeta_thirdCyclotomic (CyclotomicField 3 ℚ) hu]
  unfold clearedScattering
  rw [_root_.RHTower.zetaPoleFilled_of_ne h1]
  field_simp
  ring

/-- `(s − 4/3) φ(s)` is holomorphic on `Re s > 1`. -/
theorem clearedScattering_differentiableOn :
    DifferentiableOn ℂ clearedScattering {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  have hu2 : 1 < (3 * s - 2).re := by
    have : (3 * s - 2).re = 3 * s.re - 2 := by simp
    rw [this]
    linarith
  have hlin : ∀ a : ℂ, DifferentiableAt ℂ (fun s : ℂ => 3 * s - a) s := fun a =>
    (differentiableAt_id.const_mul 3).sub_const a
  have hpow : DifferentiableAt ℂ (fun s : ℂ => (3 : ℂ) ^ (3 * s - 3)) s :=
    (hlin 3).const_cpow (Or.inl (by norm_num))
  have hpow' : DifferentiableAt ℂ (fun s : ℂ => (3 : ℂ) ^ (-(3 * s - 3))) s :=
    (hlin 3).neg.const_cpow (Or.inl (by norm_num))
  have hzeta : DifferentiableAt ℂ (fun s : ℂ => _root_.RHTower.zetaPoleFilled (3 * s - 3)) s :=
    (_root_.RHTower.differentiable_zetaPoleFilled _).comp s (hlin 3)
  have hL : DifferentiableAt ℂ (fun s : ℂ => DirichletCharacter.LFunction chi3D (3 * s - 3)) s :=
    (DirichletCharacter.differentiable_LFunction chi3D_ne_one _).comp s (hlin 3)
  have hZ : DifferentiableAt ℂ (unramifiedIdealZeta ∘ fun s : ℂ => 3 * s - 2) s :=
    DifferentiableAt.comp s (unramifiedIdealZeta_differentiableAt (3 * s - 2) hu2) (hlin 2)
  have hZ0 := unramifiedIdealZeta_ne_zero _ hu2
  unfold clearedScattering
  refine DifferentiableAt.differentiableWithinAt ?_
  refine ((((differentiableAt_const _).mul ((hpow.sub_const 1).inv (three_cpow_ne_one hs'))).mul
    ((differentiableAt_const 1).sub hpow')).mul (hzeta.mul hL)).div
    ((differentiableAt_const 3).mul hZ) (mul_ne_zero (by norm_num) hZ0)

/-- **The residue of `ζ_K` is `L(1, χ₋₃)`.** -/
theorem dedekindZeta_residue_eq :
    ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) = DirichletCharacter.LFunction chi3D 1 := by
  have h := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hcont : ContinuousAt (fun u : ℂ => _root_.RHTower.zetaPoleFilled u *
      DirichletCharacter.LFunction chi3D u) 1 :=
    ((_root_.RHTower.differentiable_zetaPoleFilled 1).continuousAt).mul
      ((DirichletCharacter.differentiable_LFunction chi3D_ne_one 1).continuousAt)
  have h1 : _root_.RHTower.zetaPoleFilled 1 = 1 := Function.update_self _ _ _
  have h2 : Tendsto (fun x : ℝ => _root_.RHTower.zetaPoleFilled (x : ℂ) *
      DirichletCharacter.LFunction chi3D (x : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (DirichletCharacter.LFunction chi3D 1)) := by
    have hc := hcont.tendsto.comp (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)) (a := (1 : ℝ))))
    simp only [h1, one_mul] at hc
    exact hc
  refine tendsto_nhds_unique h (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hx1 : (x : ℂ) ≠ 1 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith [show (1 : ℝ) < x from hx]
  rw [_root_.RHTower.zetaPoleFilled_of_ne hx1, dedekindZeta_thirdCyclotomic (CyclotomicField 3 ℚ) hx']
  ring

/-- **The value at `4/3` is the arithmetic residue.** `clearedScattering (4/3) = r ≠ 0`. -/
theorem clearedScattering_four_thirds : clearedScattering (4 / 3) = constantArithmeticResidue := by
  have h1 : (3 : ℂ) * (4 / 3) - 3 = 1 := by norm_num
  have h2 : (3 : ℂ) * (4 / 3) - 2 = 2 := by norm_num
  have hZ := unramifiedIdealZeta_ne_zero 2 (by norm_num)
  have hV := cuspArea_ne_zero
  unfold clearedScattering constantArithmeticResidue unramifiedZetaResidue
  rw [h1, h2, show _root_.RHTower.zetaPoleFilled 1 = 1 from Function.update_self _ _ _,
    dedekindZeta_residue_eq, Complex.cpow_one, Complex.cpow_neg_one]
  field_simp

theorem clearedScattering_four_thirds_ne_zero : clearedScattering (4 / 3) ≠ 0 := by
  rw [clearedScattering_four_thirds]
  exact constantArithmeticResidue_ne_zero

/-! ### The constant term -/

/-- The pole part of the constant term at height `v`: `v^{2−s} (π/(s − 1)) (s − 4/3) φ(s)`. -/
def clearedConstantTerm (v : ℝ) (s : ℂ) : ℂ :=
  (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1)) * clearedScattering s

/-- **The constant term continues.** For `Re s > 2`,
`(s − 4/3) (a₀(E(·, s); v) − v^s) = clearedConstantTerm v s`, and `clearedConstantTerm v` is
holomorphic on `Re s > 1`. -/
theorem sub_mul_constantTerm (v : ℝ) (hv : 0 < v) {s : ℂ} (hs : 2 < s.re) :
    (s - 4 / 3) * (eisensteinFourierCoefficient v hv s 0 - (v : ℂ) ^ s) = clearedConstantTerm v s := by
  rw [eisensteinConstantCoefficient_formula v hv s hs, clearedConstantTerm,
    ← sub_mul_scatteringCoefficient (by linarith)]
  ring

theorem clearedConstantTerm_differentiableOn (v : ℝ) (hv : 0 < v) :
    DifferentiableOn ℂ (clearedConstantTerm v) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : 1 < s.re := hs
  have hs1 : s - 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp at this
    linarith
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  unfold clearedConstantTerm
  exact ((((differentiableAt_const 2).sub differentiableAt_id).const_cpow (Or.inl hvC)).mul
    ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) hs1)).differentiableWithinAt.mul
    (clearedScattering_differentiableOn s hs)

/-- **The residue of the constant term** at `4/3` is `3π r v^{2/3}`. -/
theorem clearedConstantTerm_four_thirds (v : ℝ) :
    clearedConstantTerm v (4 / 3) = 3 * Real.pi * constantArithmeticResidue * (v : ℂ) ^ ((2 : ℂ) / 3) := by
  rw [clearedConstantTerm, clearedScattering_four_thirds]
  rw [show (2 : ℂ) - 4 / 3 = 2 / 3 by norm_num, show (4 / 3 : ℂ) - 1 = 1 / 3 by norm_num]
  field_simp

/-! ### The logarithm in the Laurent coefficient -/

/-- The holomorphic factor `g(s) = (π/(s − 1)) (s − 4/3) φ(s)` of the constant term. -/
def scatteringFactor (s : ℂ) : ℂ := ((Real.pi : ℂ) / (s - 1)) * clearedScattering s

theorem clearedConstantTerm_eq (v : ℝ) (s : ℂ) :
    clearedConstantTerm v s = (v : ℂ) ^ (2 - s) * scatteringFactor s := by
  unfold clearedConstantTerm scatteringFactor
  ring

theorem scatteringFactor_four_thirds :
    scatteringFactor (4 / 3) = 3 * Real.pi * constantArithmeticResidue := by
  rw [scatteringFactor, clearedScattering_four_thirds, show (4 / 3 : ℂ) - 1 = 1 / 3 by norm_num]
  field_simp

theorem scatteringFactor_differentiableAt : DifferentiableAt ℂ scatteringFactor (4 / 3) := by
  have hmem : (4 / 3 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    change 1 < (4 / 3 : ℂ).re
    norm_num
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc := (clearedScattering_differentiableOn _ hmem).differentiableAt (hopen.mem_nhds hmem)
  exact ((differentiableAt_const _).div (differentiableAt_id.sub_const 1) (by norm_num)).mul hc

/-- **The logarithm in the Laurent coefficient.** At `4/3` the pole part `v^{2−s} g(s)` of the
constant term has derivative `v^{2/3} (g'(4/3) − 3π r log v)`: the constant Laurent coefficient
`v^{4/3} + ∂_s(v^{2−s} g(s))|_{4/3}` of the continued constant term carries `−3π r v^{2/3} log v`. -/
theorem hasDerivAt_clearedConstantTerm (v : ℝ) (hv : 0 < v) :
    HasDerivAt (clearedConstantTerm v)
      ((v : ℂ) ^ ((2 : ℂ) / 3) *
        (deriv scatteringFactor (4 / 3) - Real.log v * (3 * Real.pi * constantArithmeticResidue)))
      (4 / 3) := by
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hlin : HasDerivAt (fun s : ℂ => 2 - s) (-1) (4 / 3) := by
    simpa using (hasDerivAt_id (4 / 3 : ℂ)).const_sub 2
  have hpow := hlin.const_cpow (c := (v : ℂ)) (Or.inl hvC)
  have hprod := hpow.mul scatteringFactor_differentiableAt.hasDerivAt
  have hfun : clearedConstantTerm v = fun s => (v : ℂ) ^ (2 - s) * scatteringFactor s := by
    funext s
    exact clearedConstantTerm_eq v s
  have key : (v : ℂ) ^ (2 - 4 / 3 : ℂ) * Complex.log (v : ℂ) * -1 * scatteringFactor (4 / 3) +
      (v : ℂ) ^ (2 - 4 / 3 : ℂ) * deriv scatteringFactor (4 / 3) =
      (v : ℂ) ^ ((2 : ℂ) / 3) *
        (deriv scatteringFactor (4 / 3) - Real.log v * (3 * Real.pi * constantArithmeticResidue)) := by
    rw [scatteringFactor_four_thirds, show (2 : ℂ) - 4 / 3 = 2 / 3 by norm_num,
      ← Complex.ofReal_log hv.le]
    ring
  rw [hfun]
  exact hprod.congr_deriv key

end GaloisForLFunctions.SpectralTheoryOfTheCubicCover
