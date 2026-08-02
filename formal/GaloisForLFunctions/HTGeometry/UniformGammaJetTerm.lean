import GaloisForLFunctions.HTGeometry.UniformDominantSum

/-!
# A Gamma-jet term against its own shape, uniformly on a vertical tube

A term of a Gamma-field presentation is `Γ^u·ψ^e·g` where `g` is a jet polynomial in the
positive-order jets with rational coefficients.  Its shape is `Γ^u·s^{-p}·(log s)^e`, and dividing by
that shape leaves exactly two factors: `ψ^e/(log s)^e`, which tends to `1` uniformly, and `s^p·g`,
which tends to the datum of `g` uniformly.

So each term of a presentation has its residue uniformly on the tube, and the dominant-class sum then
gives the residue of the whole presentation: the tube form of eq. (3) for a Gamma-field element in
normal form.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A datum `s^p·g → c` is a residue against the shape `s^{-p}`. -/
theorem tubeLimit_div_gammaShapeZ_of_datum {M : ℝ} {g : ℝ → ℝ → ℂ} {p : ℕ} {c : ℂ}
    (h : TubeLimit M (fun σ t => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * g σ t) c) :
    TubeLimit M (fun σ t => g σ t / gammaShapeZ σ 0 (-(p : ℤ)) 0 t) c := by
  refine h.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h0] at him
    simp only [Complex.zero_im] at him
    linarith
  have hshape : gammaShapeZ σ 0 (-(p : ℤ)) 0 t
      = (((σ : ℂ) + (t : ℂ) * Complex.I) ^ p)⁻¹ := by
    rw [gammaShapeZ, zpow_zero, zpow_zero, one_mul, mul_one, zpow_neg, zpow_natCast]
  rw [hshape, div_inv_eq_mul, mul_comm]

/-- **A Gamma-jet term against its own shape, uniformly.**  Multiplying a datum by `Γ^u` and `ψ^e`
multiplies its shape by `Γ^u` and `(log s)^e`. -/
theorem tubeLimit_gammaJet_term {M : ℝ} (hM : 0 < M) {g : ℝ → ℝ → ℂ} {p : ℕ} {c : ℂ}
    (h : TubeLimit M (fun σ t => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * g σ t) c) (u e : ℕ) :
    TubeLimit M (fun σ t => (gammaLine σ t ^ u
        * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e * g σ t)
      / gammaShapeZ σ (u : ℤ) (-(p : ℤ)) (e : ℤ) t) c := by
  have hprod := h.mul (tubeLimit_digamma_pow_div_vertLog_pow hM e)
  rw [mul_one] at hprod
  refine hprod.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h0] at him
    simp only [Complex.zero_im] at him
    linarith
  have hΓ : gammaLine σ t ≠ 0 := gammaLine_ne_zero hσ t
  have hL : vertLog t ≠ 0 := by
    intro h0
    have hre : (vertLog t).re = Real.log t := by
      rw [vertLog]
      simp
    rw [h0] at hre
    simp only [Complex.zero_re] at hre
    have hlog1 : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hshape : gammaShapeZ σ (u : ℤ) (-(p : ℤ)) (e : ℤ) t
      = gammaLine σ t ^ u * ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ p)⁻¹ * vertLog t ^ e) := by
    rw [gammaShapeZ, zpow_natCast, zpow_neg, zpow_natCast, zpow_natCast]
  rw [hshape]
  field_simp

/-- **The residue of a Gamma-field presentation, uniformly on a tube.**  Each term is a datum times
`Γ^{u_α}·ψ^{e_α}`; the sum has the residue of the dominant class against that member's shape. -/
theorem exists_tubeLimit_gammaJet_residue {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (g : Fin N → ℝ → ℝ → ℂ) (p u e : Fin N → ℕ) (c : Fin N → ℂ)
    (hdatum : ∀ α, TubeLimit M
      (fun σ t => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (p α) * g α σ t) (c α)) :
    ∃ β : Fin N, TubeLimit M
      (fun σ t => (∑ α : Fin N, gammaLine σ t ^ u α
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α * g α σ t)
        / gammaShapeZ σ (u β : ℤ) (-(p β : ℤ)) (e β : ℤ) t)
      (∑ α ∈ Finset.univ.filter (fun α : Fin N =>
          (u α : ℤ) = (u β : ℤ) ∧ (-(p α : ℤ)) = (-(p β : ℤ)) ∧ (e α : ℤ) = (e β : ℤ)), c α) := by
  classical
  exact exists_tubeLimit_dominant_class hM hN
    (fun α σ t => gammaLine σ t ^ u α
      * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α * g α σ t)
    (fun α => (u α : ℤ)) (fun α => -(p α : ℤ)) (fun α => (e α : ℤ)) c
    (fun α => tubeLimit_gammaJet_term hM (hdatum α) (u α) (e α))

end

end GaloisForLFunctions.HTGeometry
