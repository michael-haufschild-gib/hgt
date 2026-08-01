import GaloisForLFunctions.RHTower.DeningerStationaryKahlerGerm
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The logarithmic cusp of a prime chart and its Hodge star

On the punctured normal collar of a prime divisor, with `L = -log|z|` and `θ = arg z`, the
suspension carries the conformal metric `(u/L)(dL² + dθ²)` and its Kähler form.  The power
correspondence multiplies both `L` and `θ` by `q` and divides the suspension height by `q`, and the
metric is invariant: the two factors of `q²` from the coframe cancel the `q` of the height and the
`q` of `L`.  The transverse flow multiplies the height, hence the metric and the Kähler form, by
`e^t`.

The length of the collar toward the divisor is infinite, so the divisor is a complete cusp end and
not a finite-distance smooth point.

The Hodge star on one-forms in real dimension two depends only on the oriented conformal class:
the defining identity `α ∧ ⋆β = ⟨α, β⟩_g vol_g` has a conformal-factor-free right-hand side, and it
determines `⋆`.  Consequently the star of the cusp metric is the quarter turn for every height,
every uniformizer and every conformal comparison with the generic leaf, and it squares to `-1` with
a positive wedge density.

On the complexified logarithmic summand `⋆ d log z = i d log z`, so any residue functional
normalized on `d log z` satisfies `Res(⋆α) = i Res(α)`, and it is unchanged by a change of
uniformizer, whose logarithmic difference has zero residue.

* `deningerCuspMetric_deck`, `deningerCuspKahler_deck` : deck invariance `(8)`.
* `deningerCuspMetric_flow`, `deningerCuspKahler_flow` : flow weight one `(5)`.
* `deningerCusp_length_not_integrable` : completeness `(9)`.
* `deningerConformalStar_char`, `_unique`, `_transfer` : conformal invariance of `⋆`.
* `deningerComplexStar_dlogZ`, `deningerResidue_star` : `(10)`--`(12)`.
-/

namespace RHTower

open MeasureTheory Set

section CuspMetric

/-- The conformal factor of the logarithmic cusp metric at height `u` and log-radius `L`. -/
noncomputable def deningerCuspFactor (u L : ℝ) : ℝ := u / L

/-- The logarithmic cusp metric on the normal leaf, in the coframe `dL, dθ`. -/
noncomputable def deningerCuspMetric (u L : ℝ) (v w : ℝ × ℝ) : ℝ :=
  deningerCuspFactor u L * (v.1 * w.1 + v.2 * w.2)

/-- The logarithmic cusp Kähler form on the normal leaf. -/
noncomputable def deningerCuspKahler (u L : ℝ) (v w : ℝ × ℝ) : ℝ :=
  deningerCuspFactor u L * deningerLeafWedge v w

/-- **Deck invariance of the metric `(8)`.**  The power correspondence multiplies the coframe by
`q` and the log-radius by `q`, and the deck map divides the height by `q`; the three factors
cancel. -/
theorem deningerCuspMetric_deck {q u L : ℝ} (hq : 0 < q) (hL : 0 < L) (v w : ℝ × ℝ) :
    deningerCuspMetric (u / q) (q * L) (q • v) (q • w) = deningerCuspMetric u L v w := by
  have hq' : q ≠ 0 := ne_of_gt hq
  have hL' : L ≠ 0 := ne_of_gt hL
  show (u / q) / (q * L) * ((q * v.1) * (q * w.1) + (q * v.2) * (q * w.2))
      = u / L * (v.1 * w.1 + v.2 * w.2)
  field_simp

/-- **Deck invariance of the Kähler form `(8)`.** -/
theorem deningerCuspKahler_deck {q u L : ℝ} (hq : 0 < q) (hL : 0 < L) (v w : ℝ × ℝ) :
    deningerCuspKahler (u / q) (q * L) (q • v) (q • w) = deningerCuspKahler u L v w := by
  have hq' : q ≠ 0 := ne_of_gt hq
  have hL' : L ≠ 0 := ne_of_gt hL
  rw [deningerCuspKahler, deningerCuspKahler, deningerLeafWedge_smul]
  show (u / q) / (q * L) * (q ^ 2 * deningerLeafWedge v w)
      = u / L * deningerLeafWedge v w
  field_simp

/-- **The flow has weight one on the metric `(5)`.** -/
theorem deningerCuspMetric_flow (t u L : ℝ) (v w : ℝ × ℝ) :
    deningerCuspMetric (Real.exp t * u) L v w = Real.exp t * deningerCuspMetric u L v w := by
  show Real.exp t * u / L * (v.1 * w.1 + v.2 * w.2)
      = Real.exp t * (u / L * (v.1 * w.1 + v.2 * w.2))
  ring

/-- **The flow has weight one on the Kähler form `(5)`.** -/
theorem deningerCuspKahler_flow (t u L : ℝ) (v w : ℝ × ℝ) :
    deningerCuspKahler (Real.exp t * u) L v w = Real.exp t * deningerCuspKahler u L v w := by
  show Real.exp t * u / L * deningerLeafWedge v w
      = Real.exp t * (u / L * deningerLeafWedge v w)
  ring

/-- **The cusp is complete `(9)`.**  The leafwise length toward the divisor diverges, so the prime
stratum is a complete cusp end and not a finite-distance smooth point. -/
theorem deningerCusp_length_not_integrable {u : ℝ} (hu : 0 < u) :
    ¬ IntegrableOn (fun L : ℝ => Real.sqrt (deningerCuspFactor u L)) (Ioi (1 : ℝ)) := by
  intro hint
  have hsqrt : Real.sqrt u ≠ 0 := Real.sqrt_ne_zero'.mpr hu
  have hcongr : IntegrableOn (fun L : ℝ => Real.sqrt u * L ^ (-(1 / 2) : ℝ)) (Ioi (1 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun hint (fun L hL => ?_) measurableSet_Ioi
    have hL0 : (0 : ℝ) < L := lt_trans one_pos hL
    show Real.sqrt (u / L) = Real.sqrt u * L ^ (-(1 / 2) : ℝ)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.div_rpow (le_of_lt hu) (le_of_lt hL0),
      div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hL0)]
  have hbase : IntegrableOn (fun L : ℝ => L ^ (-(1 / 2) : ℝ)) (Ioi (1 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hcongr.const_mul (Real.sqrt u)⁻¹)
      (fun L _ => ?_) measurableSet_Ioi
    field_simp
  have hlt : (-(1 / 2) : ℝ) < -1 := (integrableOn_Ioi_rpow_iff one_pos).mp hbase
  norm_num at hlt

end CuspMetric

section ConformalStar

/-- The inner product of the conformal metric with factor `lam` on one-forms. -/
noncomputable def deningerConformalInner (lam : ℝ) (α β : ℝ × ℝ) : ℝ :=
  (α.1 * β.1 + α.2 * β.2) / lam

/-- The volume of the conformal metric with factor `lam`. -/
def deningerConformalVolume (lam : ℝ) : ℝ := lam

/-- **The defining identity of the Hodge star is conformal-factor free.**  The right-hand side
`⟨α, β⟩_g vol_g` does not depend on the conformal factor, and the quarter turn realizes it for
every factor. -/
theorem deningerConformalStar_char {lam : ℝ} (hlam : lam ≠ 0) (α β : ℝ × ℝ) :
    deningerLeafWedge α (deningerLeafStar β)
      = deningerConformalInner lam α β * deningerConformalVolume lam := by
  show α.1 * β.1 - α.2 * (-β.2) = (α.1 * β.1 + α.2 * β.2) / lam * lam
  field_simp
  ring

/-- **The star is determined by that identity.** -/
theorem deningerConformalStar_unique {S : ℝ × ℝ → ℝ × ℝ}
    (hS : ∀ α β : ℝ × ℝ, deningerLeafWedge α (S β) = α.1 * β.1 + α.2 * β.2) (β : ℝ × ℝ) :
    S β = deningerLeafStar β := by
  have h1 := hS (1, 0) β
  have h2 := hS (0, 1) β
  simp only [deningerLeafWedge] at h1 h2
  refine Prod.ext ?_ ?_
  · show (S β).1 = -β.2
    have : -(S β).1 = β.2 := by
      have := h2
      simp at this
      linarith
    linarith
  · show (S β).2 = β.1
    have := h1
    simp at this
    linarith

/-- The star realizing the conformal identity for one factor realizes it for every factor. -/
theorem deningerConformalStar_transfer {lam mu : ℝ} (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    {S : ℝ × ℝ → ℝ × ℝ}
    (hS : ∀ α β : ℝ × ℝ, deningerLeafWedge α (S β)
      = deningerConformalInner lam α β * deningerConformalVolume lam) (α β : ℝ × ℝ) :
    deningerLeafWedge α (S β)
      = deningerConformalInner mu α β * deningerConformalVolume mu := by
  rw [hS α β, deningerConformalInner, deningerConformalVolume, deningerConformalInner,
    deningerConformalVolume]
  field_simp

end ConformalStar

section LogResidue

open Complex

/-- The complexified logarithmic generator `d log z = -dL + i dθ` in the coframe `dL, dθ`. -/
def deningerDLogZ : ℂ × ℂ := (-1, Complex.I)

/-- The complexified Hodge star of the cusp: the quarter turn. -/
def deningerComplexStar (α : ℂ × ℂ) : ℂ × ℂ := (-α.2, α.1)

theorem deningerComplexStar_smul (c : ℂ) (α : ℂ × ℂ) :
    deningerComplexStar (c • α) = c • deningerComplexStar α := by
  refine Prod.ext ?_ ?_
  · show -(c * α.2) = c * -α.2
    ring
  · rfl

/-- **The star squares to `-1`.** -/
theorem deningerComplexStar_sq (α : ℂ × ℂ) :
    deningerComplexStar (deningerComplexStar α) = -α := by
  refine Prod.ext ?_ ?_
  · show -α.1 = -α.1
    rfl
  · show -α.2 = -α.2
    rfl

/-- **`(10)`: the star acts on the logarithmic generator by `i`.** -/
theorem deningerComplexStar_dlogZ :
    deningerComplexStar deningerDLogZ = Complex.I • deningerDLogZ := by
  refine Prod.ext ?_ ?_
  · show -Complex.I = Complex.I * (-1)
    ring
  · show (-1 : ℂ) = Complex.I * Complex.I
    rw [Complex.I_mul_I]

/-- **`(12)`: residue compatibility.**  Any residue functional normalized on the logarithmic
generator turns the star into multiplication by `i` on the holomorphic logarithmic summand. -/
theorem deningerResidue_star (res : (ℂ × ℂ) →ₗ[ℂ] ℂ) (hres : res deningerDLogZ = 1) (c : ℂ) :
    res (deningerComplexStar (c • deningerDLogZ)) = Complex.I * res (c • deningerDLogZ) := by
  simp only [deningerComplexStar_smul, deningerComplexStar_dlogZ, map_smul, smul_eq_mul, hres,
    mul_one]
  ring

/-- **Uniformizer independence.**  A change of uniformizer adds a logarithmic unit with zero
residue, so the residue of the generator is unchanged. -/
theorem deningerResidue_uniformizer (res : (ℂ × ℂ) →ₗ[ℂ] ℂ) (hres : res deningerDLogZ = 1)
    (eta : ℂ × ℂ) (heta : res eta = 0) : res (deningerDLogZ + eta) = 1 := by
  rw [map_add, hres, heta, add_zero]

/-- **Tate normalization cancels the power scaling.**  The power correspondence scales the
logarithmic generator and its residue by `q`; the Tate line of weight `-1` contributes `q⁻¹`. -/
theorem deningerTateNormalizedResidue (q c : ℂ) (hq : q ≠ 0) : q⁻¹ * (q * c) = c := by
  field_simp

end LogResidue

end RHTower
