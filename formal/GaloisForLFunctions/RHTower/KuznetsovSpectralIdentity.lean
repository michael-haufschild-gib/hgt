import GaloisForLFunctions.RHTower.KuznetsovCuspFormPairing
import GaloisForLFunctions.RHTower.DeckEisensteinSpectralIsometry

/-!
# The rough Kuznetsov identity

The deck Poincaré series `U = U(·| s₁, μ, v)` and the conjugate series `P = P(·| h̄_{s₂,ν}, w)`
(`Re s₁, Re s₂ > 1`, `μ, ν > 0`) are central square-integrable fields, and `P ⊥ 𝟙`: the frequency
`−ν` coefficient of the constant field is `⟨w, 𝟙⟩ ∫_0^1 e(νx) dx`, and `(1 − e(ν))⟨w, 𝟙⟩ = 0` since
`𝟙` is `ρ(T)`-fixed while `ρ(T)w = e(−ν)w`.  Parseval over the full spectrum then expresses the
geometric side `2 Σ_{(c,d) reduced} ⟨v, ρ(M)⁻¹w⟩ e((μd−νa)/c)(c²)^{−s̄₂} V(s̄₁, s̄₂; μ, ν, c²)` as

`Σ_j ⟨U, u_j⟩⟨u_j, P⟩ + π⁻¹ ⟨T̄ U, T̄ P⟩`

(`kuznetsov_rough`), `u_j` the cuspidal eigenbasis and `T̄` the Eisenstein transform.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

theorem inner_toDeckL2_toDeckL2 {F G : ℍ → DeckSpace N} (hF : MemLp F 2 cellMeasure)
    (hG : MemLp G 2 cellMeasure) :
    ⟪toDeckL2 F hF, toDeckL2 G hG⟫_ℂ = ∫ z in fd, ⟪F z, G z⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hF, MemLp.coeFn_toLp hG] with z h1 h2
  change ⟪(hF.toLp F) z, (hG.toLp G) z⟫_ℂ = _
  rw [h1, h2]

/-- The coefficient of the constant field at a cusp vector of frequency `μ ≠ 0` vanishes. -/
theorem deckCuspCoeff_onesField {μ : ℝ} (hμ : μ ≠ 0) {v : DeckSpace N} (hv : IsCuspEigen μ v)
    (y : ℝ) : deckCuspCoeff μ v (onesField N) y = 0 := by
  have h1 : (1 - cexp (-(2 * Real.pi * Complex.I * μ))) * ⟪v, onesVec N⟫_ℂ = 0 := by
    have h := (deckRho N ModularGroup.T).inner_map_map v (onesVec N)
    rw [hv, deckRho_onesVec, inner_smul_left, ← Complex.exp_conj] at h
    have he : conj (2 * Real.pi * Complex.I * (μ : ℂ)) = -(2 * Real.pi * Complex.I * μ) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      ring
    rw [he] at h
    linear_combination -h
  have hc : (-(2 * Real.pi * Complex.I * μ) : ℂ) ≠ 0 := by
    have : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast Real.pi_pos.ne')) Complex.I_ne_zero) this)
  have hint : ∫ x in Ico (0 : ℝ) 1, cuspChar μ x =
      (cexp (-(2 * Real.pi * Complex.I * μ)) - 1) / (-(2 * Real.pi * Complex.I * μ)) := by
    have hpt : ∀ x : ℝ, cuspChar μ x = cexp ((-(2 * Real.pi * Complex.I * μ)) * x) := fun x => by
      rw [cuspChar]; congr 1; ring
    simp_rw [hpt]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_exp_mul_complex hc]
    push_cast
    rw [mul_one, mul_zero, Complex.exp_zero]
  rw [deckCuspCoeff]
  simp only [onesField]
  rw [integral_mul_const, hint, div_mul_eq_mul_div,
    show (cexp (-(2 * Real.pi * Complex.I * μ)) - 1) * ⟪v, onesVec N⟫_ℂ =
      -((1 - cexp (-(2 * Real.pi * Complex.I * μ))) * ⟪v, onesVec N⟫_ℂ) by ring, h1, neg_zero,
    zero_div]

/-- The conjugate series is orthogonal to the constants. -/
theorem integral_inner_poincSeries_conjProfile_onesField {s : ℂ} (hs : 1 < s.re) {ν : ℝ}
    (hν : 0 < ν) {w : DeckSpace N} (hw : IsCuspEigen (-ν) w) :
    ∫ z in fd, ⟪poincSeries (conjProfile s ν) w z, onesField N z⟫_ℂ = 0 := by
  rw [integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff (G := onesField N) hs hν hw
    (continuous_const : Continuous (onesField N)) deckEquivariant_onesField memLp_onesField]
  simp [deckCuspCoeff_onesField (neg_ne_zero.mpr hν.ne') hw]

/-- **The rough Kuznetsov identity**: the geometric side equals the spectral side, with the
continuous spectrum through the Eisenstein transform. -/
theorem kuznetsov_rough (hN : 2 ≤ N) {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re) (hs₂ : 1 < s₂.re)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N} (hv : IsCuspEigen μ v)
    (hw : IsCuspEigen (-ν) w) :
    2 * ∑' r : ReducedRow, rowWeight μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-conj s₂) *
        Kuznetsov.kuzValue (conj s₁) (conj s₂) μ ν ((r.1.1 0 : ℝ) ^ 2) =
      (∑' j, ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v),
          (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
        ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w)⟫_ℂ) +
      (Real.pi : ℂ)⁻¹ * ⟪eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)),
        eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w))⟫_ℂ := by
  rw [← integral_inner_poincSeries_conjProfile hs₁ hs₂ hμ hν hv hw,
    ← inner_toDeckL2_toDeckL2 (memLp_poincSeries_profile hs₁ hμ v)
      (memLp_poincSeries_conjProfile hs₂ hν w)]
  refine inner_eq_cusp_add_eisTransform hN
    (toDeckL2_mem_deckCentralFixedL2
      (deckEquivariant_poincSeries (cuspCompatible_poincProfile s₁ hv)) _)
    (toDeckL2_mem_deckCentralFixedL2
      (deckEquivariant_poincSeries (cuspCompatible_conjProfile s₂ hw)) _) ?_
  rw [onesL2, inner_toDeckL2_toDeckL2]
  have hc : ∀ z, ⟪onesField N z, poincSeries (conjProfile s₂ ν) w z⟫_ℂ =
      conj ⟪poincSeries (conjProfile s₂ ν) w z, onesField N z⟫_ℂ := fun z =>
    (inner_conj_symm _ _).symm
  simp_rw [hc]
  rw [integral_conj, integral_inner_poincSeries_conjProfile_onesField hs₂ hν hw, map_zero]

end

end GaloisForLFunctions.RHTower.DeckPointPair
