import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary
import GaloisForLFunctions.RHTower.L2FourierReflection
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The `L²` Voronoi involution of a degree-`d` functional equation

On `L²((0,∞), dx)` with the Mellin unitary `𝓜 f(ξ) = Mf(1/2 - 2πiξ)`, a Mellin multiplier `G`
that is unimodular on `Re s = 1/2` defines the Voronoi transform by `M[Hf](s) = G(s) Mf(1-s)`, i.e.
`𝓜(Hf)(ξ) = m(ξ) 𝓜f(-ξ)` with `m(ξ) = G(1/2 - 2πiξ)`. It is unitary, and an involution exactly
when `G(s) G(1-s) = 1`.

For `G(s) = Γℝ(s)³ / Γℝ(1-s)³` (the functional equation of `ζ(s)³`) the symbol is continuous,
unimodular, and satisfies `m(ξ) m(-ξ) = 1`, so `gammaRCubeVoronoi` is a unitary involution: the
operator whose `-1` eigenspace carries the self-dual relations of the degree-three abundance
theorem.
-/

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Reflection `f ↦ f(-·)` on `L²(ℝ)`, pointwise a.e. -/
theorem l2Reflection_ae' (f : Lp (α := ℝ) ℂ 2) :
    l2Reflection f =ᵐ[volume] fun x : ℝ => f (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))

section Unimodular

variable (m : ℝ → ℂ) (hmc : Continuous m) (hm : ∀ x, ‖m x‖ = 1)
include hmc hm

/-- Multiplying an `L²` function by a unimodular continuous function stays in `L²`. -/
theorem memLp_unimodular_mul (f : Lp (α := ℝ) ℂ 2) :
    MemLp (fun x => m x * f x) 2 (volume : Measure ℝ) := by
  apply (Lp.memLp f).congr_norm
  · exact hmc.aestronglyMeasurable.mul (Lp.memLp f).1
  · filter_upwards with x
    simp [hm x]

/-- The multiplication map on `L²` representatives. -/
def unimodularMulAux (f : Lp (α := ℝ) ℂ 2) : Lp (α := ℝ) ℂ 2 :=
  (memLp_unimodular_mul m hmc hm f).toLp _

/-- Pointwise form of the multiplication map. -/
theorem unimodularMulAux_ae (f : Lp (α := ℝ) ℂ 2) :
    unimodularMulAux m hmc hm f =ᵐ[volume] fun x => m x * f x :=
  (memLp_unimodular_mul m hmc hm f).coeFn_toLp

/-- The multiplication map is linear. -/
def unimodularMulLinear : Lp (α := ℝ) ℂ 2 →ₗ[ℂ] Lp (α := ℝ) ℂ 2 where
  toFun := unimodularMulAux m hmc hm
  map_add' f g := by
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae m hmc hm (f + g), unimodularMulAux_ae m hmc hm f,
      unimodularMulAux_ae m hmc hm g, Lp.coeFn_add f g,
      Lp.coeFn_add (unimodularMulAux m hmc hm f) (unimodularMulAux m hmc hm g)]
      with x hfg hf hg hadd hout
    rw [hfg, hout]
    change m x * (f + g : Lp (α := ℝ) ℂ 2) x =
      unimodularMulAux m hmc hm f x + unimodularMulAux m hmc hm g x
    rw [hadd, hf, hg]
    change m x * (f x + g x) = m x * f x + m x * g x
    ring
  map_smul' c f := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [unimodularMulAux_ae m hmc hm (c • f), unimodularMulAux_ae m hmc hm f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (unimodularMulAux m hmc hm f)] with x hcf hf hcin hcout
    rw [hcf, hcout]
    change m x * (c • f : Lp (α := ℝ) ℂ 2) x = c • unimodularMulAux m hmc hm f x
    rw [hcin, hf]
    change m x * (c * f x) = c * (m x * f x)
    ring

/-- Unimodular multiplication preserves the `L²` norm. -/
theorem norm_unimodularMulAux (f : Lp (α := ℝ) ℂ 2) : ‖unimodularMulAux m hmc hm f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (unimodularMulAux_ae m hmc hm f)]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  simp [hm x]

/-- Multiplication by a continuous unimodular function, as a linear isometry of `L²(ℝ)`. -/
def unimodularMulIsometry : Lp (α := ℝ) ℂ 2 →ₗᵢ[ℂ] Lp (α := ℝ) ℂ 2 where
  __ := unimodularMulLinear m hmc hm
  norm_map' := norm_unimodularMulAux m hmc hm

/-- The `L²` Voronoi transform with Mellin multiplier `m`: `𝓜(V f)(ξ) = m(ξ) 𝓜f(-ξ)`. -/
def voronoiL2 : HalfLineL2 →L[ℂ] HalfLineL2 :=
  (halfLineMellinUnitary.symm.toLinearIsometry.toContinuousLinearMap).comp
    ((unimodularMulIsometry m hmc hm).toContinuousLinearMap.comp
      (l2Reflection.comp halfLineMellinUnitary.toLinearIsometry.toContinuousLinearMap))

/-- Defining Mellin identity of the Voronoi transform. -/
theorem mellin_voronoiL2 (f : HalfLineL2) :
    halfLineMellinUnitary (voronoiL2 m hmc hm f)
      = unimodularMulAux m hmc hm (l2Reflection (halfLineMellinUnitary f)) := by
  simp [voronoiL2, unimodularMulIsometry, unimodularMulLinear]

/-- The Voronoi transform is an isometry. -/
theorem norm_voronoiL2 (f : HalfLineL2) : ‖voronoiL2 m hmc hm f‖ = ‖f‖ := by
  rw [← halfLineMellinUnitary.norm_map, mellin_voronoiL2, norm_unimodularMulAux,
    show ‖l2Reflection (halfLineMellinUnitary f)‖ = ‖halfLineMellinUnitary f‖ from
      l2ReflectionIsometry.norm_map _, halfLineMellinUnitary.norm_map]

/-- If `m(ξ) m(-ξ) = 1`, the Voronoi transform is an involution. -/
theorem voronoiL2_voronoiL2 (hsym : ∀ ξ, m ξ * m (-ξ) = 1) (f : HalfLineL2) :
    voronoiL2 m hmc hm (voronoiL2 m hmc hm f) = f := by
  apply halfLineMellinUnitary.injective
  rw [mellin_voronoiL2, mellin_voronoiL2]
  set φ := halfLineMellinUnitary f
  apply Lp.ext
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have h1 := unimodularMulAux_ae m hmc hm (l2Reflection (unimodularMulAux m hmc hm (l2Reflection φ)))
  have h2 := l2Reflection_ae' (unimodularMulAux m hmc hm (l2Reflection φ))
  have h3 := (unimodularMulAux_ae m hmc hm (l2Reflection φ)).comp_tendsto hneg.tendsto_ae
  have h4 := (l2Reflection_ae' φ).comp_tendsto hneg.tendsto_ae
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  rw [hx1, hx2]
  simp only [Function.comp] at hx3 hx4
  rw [hx3, hx4, neg_neg, ← mul_assoc, hsym, one_mul]

end Unimodular

section GammaRCube

open Complex

/-- `Γℝ(s̄) = conj Γℝ(s)`. -/
theorem gammaR_conj (s : ℂ) : Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Gammaℝ s) := by
  have harg : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm
  have e : (starRingEnd ℂ) (-s / 2) = -(starRingEnd ℂ) s / 2 := by
    rw [map_div₀, map_neg, map_ofNat]
  have e2 : (starRingEnd ℂ) (s / 2) = (starRingEnd ℂ) s / 2 := by
    rw [map_div₀, map_ofNat]
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Complex.Gamma_conj, e2, ← e,
    Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

/-- `Γℝ` is continuous on `Re s > 0`. -/
theorem continuousAt_gammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) : ContinuousAt Gammaℝ s := by
  have h := (differentiable_Gammaℝ_inv s).continuousAt.inv₀ (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  convert h using 1
  funext x
  simp

/-- The `L²` Mellin symbol of the `Γℝ(s)³` Voronoi transform: `G(1/2 - 2πiξ)` with
`G(s) = Γℝ(s)³ / Γℝ(1-s)³`. -/
def gammaRCubeSymbol (ξ : ℝ) : ℂ :=
  Gammaℝ (1 / 2 - 2 * Real.pi * ξ * I) ^ 3 / Gammaℝ (1 / 2 + 2 * Real.pi * ξ * I) ^ 3

private theorem re_half_sub (ξ : ℝ) : 0 < ((1 : ℂ) / 2 - 2 * Real.pi * ξ * I).re := by simp
private theorem re_half_add (ξ : ℝ) : 0 < ((1 : ℂ) / 2 + 2 * Real.pi * ξ * I).re := by simp

private theorem conj_half_add (ξ : ℝ) :
    (starRingEnd ℂ) ((1 : ℂ) / 2 + 2 * Real.pi * ξ * I) = 1 / 2 - 2 * Real.pi * ξ * I := by
  simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The symbol is continuous. -/
theorem continuous_gammaRCubeSymbol : Continuous gammaRCubeSymbol := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have h1 : ContinuousAt (fun ξ : ℝ => Gammaℝ (1 / 2 - 2 * Real.pi * ξ * I)) ξ :=
    (continuousAt_gammaR_of_re_pos (re_half_sub ξ)).comp
      (f := fun ξ : ℝ => (1 / 2 : ℂ) - 2 * Real.pi * ξ * I) (x := ξ) (by fun_prop)
  have h2 : ContinuousAt (fun ξ : ℝ => Gammaℝ (1 / 2 + 2 * Real.pi * ξ * I)) ξ :=
    (continuousAt_gammaR_of_re_pos (re_half_add ξ)).comp
      (f := fun ξ : ℝ => (1 / 2 : ℂ) + 2 * Real.pi * ξ * I) (x := ξ) (by fun_prop)
  exact (h1.pow 3).div (h2.pow 3) (pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (re_half_add ξ)))

/-- The symbol is unimodular: `Γℝ(1/2 - it)` is the conjugate of `Γℝ(1/2 + it)`. -/
theorem norm_gammaRCubeSymbol (ξ : ℝ) : ‖gammaRCubeSymbol ξ‖ = 1 := by
  unfold gammaRCubeSymbol
  rw [← conj_half_add, gammaR_conj, norm_div, norm_pow, norm_pow, Complex.norm_conj]
  exact div_self (pow_ne_zero 3 (norm_ne_zero_iff.mpr (Gammaℝ_ne_zero_of_re_pos (re_half_add ξ))))

/-- `m(ξ) m(-ξ) = 1`, the Mellin form of `G(s) G(1-s) = 1`. -/
theorem gammaRCubeSymbol_mul_neg (ξ : ℝ) : gammaRCubeSymbol ξ * gammaRCubeSymbol (-ξ) = 1 := by
  unfold gammaRCubeSymbol
  have hA := pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (re_half_add ξ))
  have hB := pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (re_half_sub ξ))
  push_cast
  rw [show (1 : ℂ) / 2 - 2 * Real.pi * (-(ξ : ℂ)) * I = 1 / 2 + 2 * Real.pi * ξ * I by ring,
    show (1 : ℂ) / 2 + 2 * Real.pi * (-(ξ : ℂ)) * I = 1 / 2 - 2 * Real.pi * ξ * I by ring,
    div_mul_div_comm, mul_comm (Gammaℝ (1 / 2 + 2 * Real.pi * ξ * I) ^ 3),
    div_self (mul_ne_zero hB hA)]

/-- The Voronoi transform of `ζ(s)³`'s functional equation on `L²((0,∞), dx)`:
`M[Hf](s) = Γℝ(s)³/Γℝ(1-s)³ · Mf(1-s)` on `Re s = 1/2`, a unitary involution. -/
def gammaRCubeVoronoi : HalfLineL2 →L[ℂ] HalfLineL2 :=
  voronoiL2 gammaRCubeSymbol continuous_gammaRCubeSymbol norm_gammaRCubeSymbol

/-- The `Γℝ³` Voronoi transform is an involution. -/
theorem gammaRCubeVoronoi_involutive (f : HalfLineL2) :
    gammaRCubeVoronoi (gammaRCubeVoronoi f) = f :=
  voronoiL2_voronoiL2 _ _ _ gammaRCubeSymbol_mul_neg f

/-- The `Γℝ³` Voronoi transform is unitary. -/
theorem norm_gammaRCubeVoronoi (f : HalfLineL2) : ‖gammaRCubeVoronoi f‖ = ‖f‖ :=
  norm_voronoiL2 _ _ _ f

end GammaRCube

end RHTower
