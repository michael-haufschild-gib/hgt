import GaloisForLFunctions.RHTower.KuznetsovSameSignPairing
import GaloisForLFunctions.RHTower.KuznetsovExplicitIdentity

/-!
# The same-sign Kuznetsov identity with explicit spectral data

For `Re s₁, Re s₂ > 1`, `μ, ν > 0`, `ρ(T)v = e(μ)v`, `ρ(T)w = e(ν)w`, Parseval over the full spectrum
applied to the two Poincaré series `U(·| s₁, μ, v)` and `U(·| s₂, ν, w)` gives

`2 [μ = ν] (4πμ)^{1−s̄₁−s₂} Γ(s̄₁+s₂−1) ⟨v, w + ρ(−1)⁻¹w⟩
   + 2 Σ_{(c,d)} ⟨v, ρ(M)⁻¹w⟩ e((μd+νa)/c) (c²)^{−s₂} V⁺(s̄₁, s₂; μ, ν, c²)
 = 4 (2πμ)^{½−s̄₁} (2πν)^{½−s₂} (Σ_j ρ_j(v) ρ̄_j(w) W(s̄₁, ν_j) W(s₂, ν_j)
     + (4π)⁻¹ ∫ Σ_i η_i(v, t) η̄_i(w, t) W(s̄₁, it) W(s₂, it) dt)`

(`kuznetsov_same_sign_explicit`), where `ρ_j` are the Whittaker coefficients of the cuspidal
eigenbasis and `η_i` the Eisenstein coefficients.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set EisensteinSeries Complex
open scoped MatrixGroups InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- **The `j`-th eigenfunction against the Poincaré series.** -/
theorem inner_cuspEigenBasis_poincL2 {s₂ : ℂ} (hs₂ : 1 < s₂.re) {ν : ℝ} (hν : 0 < ν)
    {w : DeckSpace N} (hw : IsCuspEigen ν w) (j : CuspEigenIndex N) :
    ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_profile hs₂ hν w)⟫_ℂ =
      2 * (conj (cuspCoeff j ν w) * ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(s₂ - 1 / 2)) *
        whittMellin s₂ (specParam j.1)) := by
  rw [← inner_conj_symm, inner_poincL2_cuspEigenBasis hs₂ hν hw j]
  have hk : (0 : ℝ) ≤ 2 * Real.pi * ν := by positivity
  rw [map_mul, map_mul, map_mul, map_ofNat, conj_ofReal_cpow hk, conj_whittMellin_specParam,
    Complex.conj_conj]
  simp only [map_neg, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]

/-- **The Eisenstein transforms of two Poincaré series**:
`⟨T̄U₁, T̄U₂⟩ = ¼ ∫ Σ_i Φ^{U₁}_{e_i}(½+it) conj Φ^{U₂}_{e_i}(½+it) dt`. -/
theorem inner_eisTransformL2_poinc_poinc (hN : 2 ≤ N) {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re)
    (hs₂ : 1 < s₂.re) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N}
    (hv : IsCuspEigen μ v) (hw : IsCuspEigen ν w) {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    (hm : ν * ((N + 1 : ℕ) : ℝ) = m) :
    ⟪eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v)),
        eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₂ hν w))⟫_ℂ =
      4⁻¹ * ∫ t : ℝ, ∑ i, poincEisPairing s₁ μ v (cuspBasisVec N i) n (1 / 2 + t * Complex.I) *
        conj (poincEisPairing s₂ ν w (cuspBasisVec N i) m (1 / 2 + t * Complex.I)) := by
  set X := eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v))
  set Y := eisTransformL2 hN (toDeckL2 _ (memLp_poincSeries_profile hs₂ hν w))
  have hX := eisTransformL2_mem_symSpace hN (toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v))
  have hY := eisTransformL2_mem_symSpace hN (toDeckL2 _ (memLp_poincSeries_profile hs₂ hν w))
  have hXi := ae_all_iff.2 fun i =>
    eisTransformL2_poinc_inner hN hs₁ hμ hv hn (isCuspVec_cuspBasisVec (N := N) i)
  have hYi := ae_all_iff.2 fun i =>
    eisTransformL2_poinc_inner hN hs₂ hν hw hm (isCuspVec_cuspBasisVec (N := N) i)
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hX, hY, hXi, hYi] with t h1 h2 h3 h4
  rw [inner_eq_sum_cuspBasisVec h1.1 h2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h3 i, ← h4 i, map_mul, inner_conj_symm, map_ofNat]
  ring

/-- **The same-sign Kuznetsov identity with explicit spectral data.** -/
theorem kuznetsov_same_sign_explicit (hN : 2 ≤ N) {s₁ s₂ : ℂ} (hs₁ : 1 < s₁.re)
    (hs₂ : 1 < s₂.re) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) {v w : DeckSpace N}
    (hv : IsCuspEigen μ v) (hw : IsCuspEigen ν w) {n m : ℤ} (hn : μ * ((N + 1 : ℕ) : ℝ) = n)
    (hm : ν * ((N + 1 : ℕ) : ℝ) = m) :
    2 * diagPlus (conj s₁) s₂ μ ν v w +
      2 * ∑' r : ReducedRow, rowWeightPlus μ ν v w r.1 * (((r.1.1 0 : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s₂) *
        kuzValuePlus (conj s₁) s₂ μ ν ((r.1.1 0 : ℝ) ^ 2) =
      4 * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
        ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(s₂ - 1 / 2)) *
        ((∑' j : CuspEigenIndex N, cuspCoeff j μ v * conj (cuspCoeff j ν w) *
            whittMellin (conj s₁) (specParam j.1) * whittMellin s₂ (specParam j.1)) +
          (4 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ, ∑ i, eisCoeff (1 / 2 + t * Complex.I) v (cuspBasisVec N i) n *
            conj (eisCoeff (1 / 2 + t * Complex.I) w (cuspBasisVec N i) m) *
            whittMellin (conj s₁) (t * Complex.I) * whittMellin s₂ (t * Complex.I)) := by
  set K : ℂ := 4 * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
    ((2 * Real.pi * ν : ℝ) : ℂ) ^ (-(s₂ - 1 / 2))
  rw [← integral_inner_poincSeries_poincProfile hs₁ hs₂ hμ hν hv hw,
    ← inner_toDeckL2_toDeckL2 (memLp_poincSeries_profile hs₁ hμ v)
      (memLp_poincSeries_profile hs₂ hν w),
    inner_eq_cusp_add_eisTransform hN
      (toDeckL2_mem_deckCentralFixedL2
        (deckEquivariant_poincSeries (cuspCompatible_poincProfile s₁ hv)) _)
      (toDeckL2_mem_deckCentralFixedL2
        (deckEquivariant_poincSeries (cuspCompatible_poincProfile s₂ hw)) _)
      (by rw [← inner_conj_symm, inner_poincL2_onesL2 hs₂ hν hw, map_zero]),
    inner_eisTransformL2_poinc_poinc hN hs₁ hs₂ hμ hν hv hw hn hm]
  have hd : ∀ j : CuspEigenIndex N,
      ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), (cuspEigenBasis N j : DeckL2 N)⟫_ℂ *
        ⟪(cuspEigenBasis N j : DeckL2 N), toDeckL2 _ (memLp_poincSeries_profile hs₂ hν w)⟫_ℂ =
      K * (cuspCoeff j μ v * conj (cuspCoeff j ν w) *
        whittMellin (conj s₁) (specParam j.1) * whittMellin s₂ (specParam j.1)) := fun j => by
    rw [inner_poincL2_cuspEigenBasis hs₁ hμ hv j, inner_cuspEigenBasis_poincL2 hs₂ hν hw j]
    simp only [K]
    ring
  have hk : (0 : ℝ) ≤ 2 * Real.pi * ν := by positivity
  have hc : ∀ t : ℝ, ∑ i, poincEisPairing s₁ μ v (cuspBasisVec N i) n (1 / 2 + t * Complex.I) *
      conj (poincEisPairing s₂ ν w (cuspBasisVec N i) m (1 / 2 + t * Complex.I)) =
      K * ∑ i, eisCoeff (1 / 2 + t * Complex.I) v (cuspBasisVec N i) n *
        conj (eisCoeff (1 / 2 + t * Complex.I) w (cuspBasisVec N i) m) *
        whittMellin (conj s₁) (t * Complex.I) * whittMellin s₂ (t * Complex.I) := fun t => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hti : (1 / 2 + t * Complex.I) - 1 / 2 = t * Complex.I := by ring
    have hct : conj ((t : ℂ) * Complex.I) = -(t * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [poincEisPairing_eq, poincEisPairing_eq, hti, map_mul, map_mul, map_mul,
      map_ofNat, conj_ofReal_cpow hk, conj_whittMellin, hct, whittMellin_neg, Complex.conj_conj]
    simp only [K, map_neg, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
    ring
  simp_rw [hd, hc]
  rw [tsum_mul_left, integral_const_mul]
  ring

end

end GaloisForLFunctions.RHTower.DeckPointPair
