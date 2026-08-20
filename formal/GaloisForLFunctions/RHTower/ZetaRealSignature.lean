import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.RHTower.EulerPositiveFisherHilbertLift

/-!
# The signature change of the arithmetic norm form across the critical line

The Bohr lift of the arithmetic state family has squared norm `‖ψ(s)‖² = ζ(2σ)`.  As a quadratic
form in `σ` this changes signature exactly at the critical line:

* `σ > 1/2`  — positive definite, `ζ(2σ) > 0` (a convergent series of positive terms);
* `σ = 1/2`  — degenerate, `ζ(2σ) → +∞` (the simple pole of `ζ` at `1`);
* `0 < σ < 1/2` — negative, `ζ(2σ) < 0` (the Dirichlet eta quotient has a negative denominator).

Nothing here is conditional on the location of the zeros: the wall is a classical fact about `ζ`
on the real axis.
-/

noncomputable section

open Filter Topology

namespace RHTower

/-! ### The positive region -/

/-- **Positive definite region.**  Right of the critical line the arithmetic norm form is a
convergent series of positive terms. -/
theorem eulerPositiveTotal_two_mul_pos {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 < eulerPositiveTotal (2 * σ) :=
  eulerPositiveTotal_pos (by linarith)

theorem riemannZeta_two_mul_eq_ofReal {σ : ℝ} (hσ : 1 / 2 < σ) :
    riemannZeta ((2 * σ : ℝ) : ℂ) = ((eulerPositiveTotal (2 * σ) : ℝ) : ℂ) :=
  (ofReal_eulerPositiveTotal_eq_riemannZeta (by linarith)).symm

/-! ### The ghost region -/

/-- **Negative (ghost) region.**  Left of the critical line the arithmetic norm form is negative:
`ζ(2σ) < 0` for `0 < σ < 1/2`. -/
theorem riemannZeta_two_mul_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1 / 2) :
    ∃ z : ℝ, z < 0 ∧ riemannZeta ((2 * σ : ℝ) : ℂ) = (z : ℂ) :=
  riemannZeta_real_strip_neg (by linarith) (by linarith)

/-! ### The degenerate wall -/

theorem tendsto_ofReal_nhdsGT_one_ne : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 : ℝ))
    (𝓝[≠] (1 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (x : ℝ) ≠ 1 := ne_of_gt (Set.mem_Ioi.mp hx)
    simpa [Complex.ofReal_eq_one] using hx1

theorem tendsto_sub_one_mul_eulerPositiveTotal :
    Tendsto (fun x : ℝ => (x - 1) * eulerPositiveTotal x) (𝓝[>] (1 : ℝ)) (𝓝 1) := by
  have hres : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * riemannZeta (x : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp tendsto_ofReal_nhdsGT_one_ne
  have hre : Tendsto (fun x : ℝ => (((x : ℂ) - 1) * riemannZeta (x : ℂ)).re)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hcomp := (Complex.continuous_re.tendsto (1 : ℂ)).comp hres
    simpa [Function.comp_def] using hcomp
  refine hre.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hzeta : riemannZeta ((x : ℝ) : ℂ) = ((eulerPositiveTotal x : ℝ) : ℂ) :=
    (ofReal_eulerPositiveTotal_eq_riemannZeta hx).symm
  rw [hzeta]
  have hcast : ((x : ℂ) - 1) = (((x - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem tendsto_inv_sub_one_atTop : Tendsto (fun x : ℝ => (x - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop := by
  have hmap : Tendsto (fun x : ℝ => x - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Tendsto (fun x : ℝ => x - 1) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using sub_pos.mpr (Set.mem_Ioi.mp hx)
  exact tendsto_inv_nhdsGT_zero.comp hmap

/-- **The degenerate wall.**  The arithmetic norm form blows up at the critical line: `ζ(x) → +∞`
as `x → 1⁺`. -/
theorem tendsto_eulerPositiveTotal_atTop :
    Tendsto eulerPositiveTotal (𝓝[>] (1 : ℝ)) atTop := by
  have h := Filter.Tendsto.pos_mul_atTop (one_pos) tendsto_sub_one_mul_eulerPositiveTotal
    tendsto_inv_sub_one_atTop
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (x : ℝ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Set.mem_Ioi.mp hx))
  field_simp

theorem tendsto_two_mul_nhdsGT_half : Tendsto (fun σ : ℝ => 2 * σ) (𝓝[>] (1 / 2 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have hc : Tendsto (fun σ : ℝ => 2 * σ) (𝓝 (1 / 2 : ℝ)) (𝓝 (1 : ℝ)) := by
      have h2 : Tendsto (fun σ : ℝ => 2 * σ) (𝓝 (1 / 2 : ℝ)) (𝓝 (2 * (1 / 2 : ℝ))) :=
        (tendsto_const_nhds).mul tendsto_id
      simpa using h2
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ' : (1 / 2 : ℝ) < σ := Set.mem_Ioi.mp hσ
    simpa using (by linarith : (1 : ℝ) < 2 * σ)

/-- **The signature wall in the position coordinate.**  `ζ(2σ) → +∞` as `σ → 1/2⁺`. -/
theorem tendsto_eulerPositiveTotal_two_mul_atTop :
    Tendsto (fun σ : ℝ => eulerPositiveTotal (2 * σ)) (𝓝[>] (1 / 2 : ℝ)) atTop :=
  tendsto_eulerPositiveTotal_atTop.comp tendsto_two_mul_nhdsGT_half

end RHTower
