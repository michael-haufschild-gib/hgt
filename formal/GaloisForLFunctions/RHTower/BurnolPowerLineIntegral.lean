import GaloisForLFunctions.RHTower.SoninMellinInversion

/-!
# The line integral against `k^{-s}`

Burnol's Proposition 5.4 pairs the continued Mellin transform with the Möbius Dirichlet series.
The `k`-th term is the vertical line integral

`(1/2π)∫ M(f)(σ+iτ)·k^{-(σ+iτ)} dτ`,

which on an abscissa `σ ∈ (1/2, 1)` is the inverse Mellin transform at the point `1/k` — hence the
band constant divided by `k`, as soon as `1/k` lies in the aperture band.

## Main results

* `ofReal_one_div_cpow_eq_neg` — `(1/k)^z = k^{-z}` for `k > 0`.
* `burnolPowLine`, `burnolPowLine_eq_band_const`.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem ofReal_one_div_cpow_eq_neg {k : ℝ} (hk : 0 < k) (z : ℂ) :
    (((1 / k : ℝ) : ℂ)) ^ z = ((k : ℝ) : ℂ) ^ (-z) := by
  have hkne : ((k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hk)
  have hinvne : (((1 / k : ℝ)) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 ?_
    positivity
  rw [Complex.cpow_def_of_ne_zero hinvne, Complex.cpow_def_of_ne_zero hkne]
  congr 1
  have hlog : Complex.log (((1 / k : ℝ)) : ℂ) = -Complex.log ((k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log (by positivity : (0:ℝ) ≤ 1 / k),
      ← Complex.ofReal_log hk.le, Real.log_div one_ne_zero (ne_of_gt hk), Real.log_one]
    push_cast
    ring
  rw [hlog]
  ring

/-- The vertical line integral of `G` against `k^{-s}`. -/
def burnolPowLine (G : ℂ → ℂ) (k : ℝ) (σ : ℝ) : ℂ :=
  ∫ τ : ℝ, G ((σ : ℂ) + (τ : ℂ) * I) * ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * I))

/-- **The line integral at an abscissa of the convergence strip is the band constant.** -/
theorem burnolPowLine_eq_band_const {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f))
    {σ : ℝ} (hσ0 : 1 / 2 < σ) (hσ1 : σ < 1)
    {k : ℝ} (hk : 0 < k) (hka : 1 / k ≤ a) :
    (1 / (2 * (Real.pi : ℂ))) * burnolPowLine (extendedMellinContinuation a c d f) k σ
      = d / (k : ℂ) := by
  set σ' : ℝ := 1 - σ with hσ'def
  have hσ'0 : 0 < σ' := by rw [hσ'def]; linarith
  have hσ'1 : σ' < 1 / 2 := by rw [hσ'def]; linarith
  have hx0 : (0 : ℝ) < 1 / k := by positivity
  have hinv := mellinInv_eq_band_const_endpoint ha hev hc hd hrapid hσ'0 hσ'1 hx0 hka
  -- unfold the inverse transform
  have hmel : ∀ y : ℝ, mellin ((f : ℝ → ℂ)) ((σ' : ℂ) + (y : ℂ) * I)
      = extendedMellinContinuation a c d f ((σ : ℂ) - (y : ℂ) * I) := by
    intro y
    have h := mellin_eq_extendedMellinContinuation ha hev hc hd
      (w := (σ' : ℂ) + (y : ℂ) * I) (by simp; linarith) (by simp; linarith)
    rw [h]
    congr 1
    rw [hσ'def]
    push_cast
    ring
  have hstep : mellinInv σ' (mellin ((f : ℝ → ℂ))) (1 / k)
      = (1 / (2 * (Real.pi : ℂ))) *
        ∫ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
          * extendedMellinContinuation a c d f ((σ : ℂ) - (y : ℂ) * I) := by
    rw [mellinInv, Complex.real_smul]
    have hint : (∫ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
          • mellin ((f : ℝ → ℂ)) ((σ' : ℂ) + (y : ℂ) * I))
        = ∫ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
          * extendedMellinContinuation a c d f ((σ : ℂ) - (y : ℂ) * I) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
          • mellin ((f : ℝ → ℂ)) ((σ' : ℂ) + (y : ℂ) * I) = _
      rw [smul_eq_mul, hmel y]
    rw [hint]
    push_cast
    ring
  -- the change of variables `y ↦ -y`
  have hswap : (∫ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
        * extendedMellinContinuation a c d f ((σ : ℂ) - (y : ℂ) * I))
      = ∫ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) - (y : ℂ) * I))
          * extendedMellinContinuation a c d f ((σ : ℂ) + (y : ℂ) * I) := by
    have h := integral_neg_eq_self
      (fun y : ℝ => (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + (y : ℂ) * I))
        * extendedMellinContinuation a c d f ((σ : ℂ) - (y : ℂ) * I)) volume
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have h1 : -((σ' : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ' : ℂ) - (y : ℂ) * I) := by
      push_cast; ring
    have h2 : (σ : ℂ) - ((-y : ℝ) : ℂ) * I = (σ : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    show (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) + ((-y : ℝ) : ℂ) * I))
        * extendedMellinContinuation a c d f ((σ : ℂ) - ((-y : ℝ) : ℂ) * I) = _
    rw [h1, h2]
  -- and the identification of the kernel
  have hkernel : ∀ y : ℝ, (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) - (y : ℂ) * I))
      = (k : ℂ) * ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) := by
    intro y
    rw [ofReal_one_div_cpow_eq_neg hk]
    have hexp : -(-((σ' : ℂ) - (y : ℂ) * I)) = 1 + (-((σ : ℂ) + (y : ℂ) * I)) := by
      rw [hσ'def]
      push_cast
      ring
    rw [hexp, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (ne_of_gt hk)), Complex.cpow_one]
  have hfin : (1 / (2 * (Real.pi : ℂ)))
      * ((k : ℂ) * burnolPowLine (extendedMellinContinuation a c d f) k σ)
      = mellinInv σ' (mellin ((f : ℝ → ℂ))) (1 / k) := by
    rw [hstep, hswap, burnolPowLine, ← MeasureTheory.integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (k : ℂ) * (extendedMellinContinuation a c d f ((σ : ℂ) + (y : ℂ) * I)
        * ((k : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)))
      = (((1 / k : ℝ)) : ℂ) ^ (-((σ' : ℂ) - (y : ℂ) * I))
        * extendedMellinContinuation a c d f ((σ : ℂ) + (y : ℂ) * I)
    rw [hkernel y]
    ring
  rw [hinv] at hfin
  have hkne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hk)
  field_simp at hfin ⊢
  linear_combination hfin

end

end RHTower
