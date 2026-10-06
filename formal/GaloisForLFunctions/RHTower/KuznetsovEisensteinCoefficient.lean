import GaloisForLFunctions.RHTower.DeckPoincareMajorantUnfolding
import GaloisForLFunctions.RHTower.EisensteinStarLevelCoefficient

/-!
# The frequency-`μ` coefficient of the deck Eisenstein series

For `Re s > 1`, `w ∈ V_∞` and a cusp vector `v` of frequency `μ ≠ 0` (`μ(N+1) = n ∈ ℤ`), the
coefficient of `Ẽ(·, s; w)` at `v` is a Whittaker function,

`∫_0^1 e(−μx)⟨v, Ẽ(x+iy, s; w)⟩ dx = c_μ(s) √y K_{s−½}(2π|μ|y)`,

with `c_μ(s) = (2L)⁻¹ Σ_q conj(v_q) Σ_g w(q g⁻¹) L^{−s} 2π^s Γ(s)⁻¹ |n|^{s−½} L^{−½} D^{g}_n(s)`
(`eisCoeff`, `deckCuspCoeff_eisVec_eq_whittaker`): only the `n`-th Fourier term of the continued
non-constant part at each cusp contributes over the level period, and the constant term
`y^s w + y^{1−s}Φ̃(s)w` does not contribute.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries Complex
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry SelbergMaassFourier SelbergMaassMean MaassWhittaker

noncomputable section

variable {N : ℕ}

/-- **The level-period Fourier modes of the deck Eisenstein series.** -/
theorem deckMode_eisVec (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {w : DeckSpace N} (hw : IsCuspVec w)
    (q : Deck N) {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    deckMode (eisVec s w) q n y = (2 * (N + 1 : ℂ))⁻¹ * ∑ g : Deck N, w (q * g⁻¹) *
      SelbergEisensteinStarCriticalLine.termCoeff (N + 1) (Quotient.out g) n s y := by
  have hL0 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hs2 : 1 / 2 < s.re := by linarith
  set K : ℝ → ℂ := _root_.RHTower.deningerFourierKernel ((N + 1 : ℕ) : ℝ) n
  set a : Deck N → ℂ := fun g => (y : ℂ) ^ s *
      (SelbergEisensteinCuspConstant.count0 (N + 1) (Quotient.out g) : ℂ) +
    (y : ℂ) ^ (1 - s) * ((N + 1 : ℕ) : ℂ)⁻¹ * SelbergEisensteinCriticalLine.phiExt (N + 1) (Quotient.out g) s
  set E : Deck N → ℝ → ℂ := fun g x =>
    SelbergEisensteinStarCriticalLine.EstarExt (N + 1) (Quotient.out g) s (ofComplex (point x y))
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun x =>
    (_root_.RHTower.deningerFourierKernel_hasDerivAt ((N + 1 : ℕ) : ℝ) n x).continuousAt
  have hEc : ∀ g, Continuous (E g) := fun g =>
    SelbergEisensteinStarCriticalLine.continuous_EstarExt_slice (N + 1) (Quotient.out g) hs2 hy
  have hpt : ∀ x : ℝ, K x * eisVec s w (ofComplex (point x y)) q =
      (2 * ((N + 1 : ℕ) : ℂ))⁻¹ * ∑ g : Deck N, w (q * g⁻¹) * (K x * a g + K x * E g x) := fun x => by
    have hp : 0 < (point x y).im := by simpa [point] using hy
    rw [eisVec_eq_eisExt hN hs hw, eisExt_apply_eq_sum hw s, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [EcuspExt_expand, show (ofComplex (point x y)).im = y by
      rw [ofComplex_apply_of_im_pos hp]; simp [point]]
    simp only [a, E]
    push_cast
    ring
  have hK0 : ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), K x = 0 := by
    have h := SelbergEisensteinStarCriticalLine.integral_exp_two_pi_int_mul_nat (N + 1) (-n)
    rw [if_neg (neg_ne_zero.mpr hn)] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [K, _root_.RHTower.deningerFourierKernel]
    congr 1
    push_cast
    ring
  show (1 / (((N + 1 : ℕ) : ℝ) : ℂ)) * ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      K x * eisVec s w (ofComplex (point x y)) q = _
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
    (f := fun g x => w (q * g⁻¹) * (K x * a g + K x * E g x)) fun g _ =>
    (continuous_const.mul ((hKc.mul continuous_const).add (hKc.mul (hEc g)))).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_const_mul]
  have hsplit : ∀ g, ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), (K x * a g + K x * E g x) =
      a g * (∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), K x) +
        ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), K x * E g x := fun g => by
    rw [intervalIntegral.integral_add (f := fun x => K x * a g) (g := fun x => K x * E g x)
      ((hKc.mul continuous_const).intervalIntegrable _ _)
      ((hKc.mul (hEc g)).intervalIntegrable _ _), intervalIntegral.integral_mul_const]
    ring
  simp_rw [hsplit, hK0, mul_zero, zero_add]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hc := SelbergEisensteinStarCriticalLine.levelCoeff_EstarExt (N + 1) (Quotient.out g) hs2 (n := n) hy
  rw [← hc]
  simp only [E, K]
  push_cast
  ring

/-- The Whittaker coefficient `c_μ(s)` of `Ẽ(·, s; w)` at a cusp vector `v`, `n = μ(N+1)`. -/
def eisCoeff (s : ℂ) (v w : DeckSpace N) (n : ℤ) : ℂ :=
  (2 * ((N + 1 : ℕ) : ℂ))⁻¹ * ∑ q : Deck N, conj (v q) * ∑ g : Deck N, w (q * g⁻¹) *
    (cexp (-s * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ *
      (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * ((((N + 1 : ℕ) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))))) *
      SelbergEisensteinCoefficientSeries.Dn (N + 1) (Quotient.out g) n s)

theorem continuousOn_comp_ofComplex {U : ℍ → DeckSpace N} (hU : Continuous U) :
    ContinuousOn (fun ζ => U (ofComplex ζ)) {ζ : ℂ | 0 < ζ.im} := by
  intro ζ hζ
  have hc : ContinuousAt (fun ζ : ℂ => (ofComplex ζ : ℍ)) ζ :=
    ofComplex.continuousAt (by exact ⟨⟨_, hζ⟩, Set.mem_univ _, rfl⟩)
  exact (hU.continuousAt.comp hc).continuousWithinAt

/-- **The coefficient of the deck Eisenstein series at a cusp vector is a Whittaker function.** -/
theorem deckCuspCoeff_eisVec_eq_whittaker (hN : 2 ≤ N) {s : ℂ} (hs : 1 < s.re) {w : DeckSpace N}
    (hw : IsCuspVec w) {μ : ℝ} (hμ0 : μ ≠ 0) {v : DeckSpace N} (hv : IsCuspEigen μ v) {n : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) {y : ℝ} (hy : 0 < y) :
    deckCuspCoeff μ v (eisVec s w) y =
      eisCoeff s v w n * whittakerW (2 * Real.pi * |μ|) (s - 1 / 2) y := by
  have hL0 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, mul_eq_zero] at hn
    exact hn.elim hμ0 (fun h => hL0.ne' h)
  have hfreq : 2 * Real.pi * |(n : ℝ)| / ((N + 1 : ℕ) : ℝ) = 2 * Real.pi * |μ| := by
    rw [← hn, abs_mul, abs_of_pos hL0]
    field_simp
  rw [deckCuspCoeff_eq_sum_deckMode (continuousOn_comp_ofComplex (continuous_eisVec hs hw.1))
    (deckEquivariant_eisVec hw.1) hv hn hy, eisCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [deckMode_eisVec hN hs hw q hn0 hy, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [SelbergEisensteinStarCriticalLine.termCoeff, if_neg hn0,
    SelbergEisensteinStarCriticalLine.kerBessel_div_eq_whittaker hL0 hy s hn0, hfreq]
  push_cast
  ring

/-! ## The Poincaré series against the Eisenstein series -/

/-- The explicit pairing `Φ(s) = 2 c_μ(s) (2πμ)^{−(s̄₁−½)} 2^{s̄₁−3/2} Γ(s̄₁−½)Γ(s̄₁+s−1)Γ(s̄₁−s)/Γ(2s̄₁−1)`. -/
def poincEisPairing (s₁ : ℂ) (μ : ℝ) (v w : DeckSpace N) (n : ℤ) (s : ℂ) : ℂ :=
  2 * (eisCoeff s v w n * ((2 * Real.pi * μ : ℝ) : ℂ) ^ (-(conj s₁ - 1 / 2)) *
    ((2 : ℂ) ^ (conj s₁ - 1 / 2 - 1) * Complex.Gamma (conj s₁ - 1 / 2) *
      Complex.Gamma (conj s₁ - 1 / 2 + (s - 1 / 2)) * Complex.Gamma (conj s₁ - 1 / 2 - (s - 1 / 2)) /
        Complex.Gamma (2 * (conj s₁ - 1 / 2))))

/-- The Selberg–Poincaré majorant against the deck Eisenstein series is integrable on `𝒟` for
`1 < Re s < Re s₁`. -/
theorem integrable_tsum_norm_poincProfile_mul_norm_eisVec {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ}
    (hμ : 0 < μ) {s : ℂ} (hs : 1 < s.re) (hss : s.re < s₁.re) {w : DeckSpace N}
    (hw : IsCuspVec w) :
    Integrable (fun z => (∑' p : gammaSet 1 1 0,
      ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖) * ‖eisVec s w z‖) cellMeasure := by
  have hB := (integrable_tsum_norm_poincProfile_mul_rowSum hs₁ hμ hs hss).const_mul
    (1 / 2 * ‖w‖)
  refine hB.mono' (((continuous_tsum_norm_poincProfile hs₁ hμ.le).mul
    (continuous_eisVec hs hw.1).norm).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
  have hA0 : 0 ≤ ∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖ :=
    tsum_nonneg fun _ => norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 (norm_nonneg _))]
  calc (∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖) * ‖eisVec s w z‖
      ≤ (∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖) *
          (1 / 2 * ((∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ s.re) * ‖w‖)) :=
        mul_le_mul_of_nonneg_left (norm_eisVec_le hs w z) hA0
    _ = 1 / 2 * ‖w‖ * ((∑' p : gammaSet 1 1 0, ‖poincProfile s₁ μ (gammaSetMatrix p • z)‖) *
          ∑' p : gammaSet 1 1 0, RHTower.rowHeight p z ^ s.re) := by ring

/-- **The Poincaré series against the deck Eisenstein series** for `1 < Re s < Re s₁`. -/
theorem integral_inner_poincSeries_eisVec (hN : 2 ≤ N) {s₁ : ℂ} (hs₁ : 1 < s₁.re) {μ : ℝ}
    (hμ : 0 < μ) {v : DeckSpace N} (hv : IsCuspEigen μ v) {n : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) {s : ℂ} (hs : 1 < s.re) (hss : s.re < s₁.re)
    {w : DeckSpace N} (hw : IsCuspVec w) :
    ∫ z in fd, ⟪poincSeries (poincProfile s₁ μ) v z, eisVec s w z⟫_ℂ =
      poincEisPairing s₁ μ v w n s := by
  rw [integral_inner_poincSeries_eq_deckCuspCoeff_of_majorant hs₁ hμ.le hv (continuous_eisVec hs hw.1)
    (deckEquivariant_eisVec hw.1) (integrable_tsum_norm_poincProfile_mul_norm_eisVec hs₁ hμ hs hss hw),
    poincEisPairing]
  congr 1
  have hk : (0 : ℝ) < 2 * Real.pi * μ := by positivity
  have hνb : |(s - 1 / 2).re| < (conj s₁).re - 1 / 2 := by
    rw [Complex.conj_re, Complex.sub_re, abs_of_pos (by norm_num; linarith)]
    norm_num
    linarith
  rw [← integral_whittaker_mellin hνb hk (eisCoeff s v w n)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [deckCuspCoeff_eisVec_eq_whittaker hN hs hw hμ.ne' hv hn hy, abs_of_pos hμ]

/-- **The conjugate series against the deck Eisenstein series** for `1 < Re s < Re s₂`: the pairing
of `P(·|h̄_{s₂,ν}, w₂)` is the explicit pairing at `(s̄₂, ν)` and the frequency `−ν(N+1) = m`. -/
theorem integral_inner_poincSeries_conjProfile_eisVec (hN : 2 ≤ N) {s₂ : ℂ} (hs₂ : 1 < s₂.re)
    {ν : ℝ} (hν : 0 < ν) {w₂ : DeckSpace N} (hw₂ : IsCuspEigen (-ν) w₂) {m : ℤ}
    (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) {s : ℂ} (hs : 1 < s.re) (hss : s.re < s₂.re)
    {w : DeckSpace N} (hw : IsCuspVec w) :
    ∫ z in fd, ⟪poincSeries (conjProfile s₂ ν) w₂ z, eisVec s w z⟫_ℂ =
      poincEisPairing (conj s₂) ν w₂ w m s := by
  rw [integral_inner_poincSeries_conjProfile_eq_deckCuspCoeff_of_majorant hs₂ hν.le hw₂
    (continuous_eisVec hs hw.1) (deckEquivariant_eisVec hw.1)
    (integrable_tsum_norm_poincProfile_mul_norm_eisVec hs₂ hν hs hss hw), poincEisPairing,
    Complex.conj_conj]
  congr 1
  have hk : (0 : ℝ) < 2 * Real.pi * ν := by positivity
  have hνb : |(s - 1 / 2).re| < s₂.re - 1 / 2 := by
    rw [Complex.sub_re, abs_of_pos (by norm_num; linarith)]
    norm_num
    linarith
  rw [← integral_whittaker_mellin hνb hk (eisCoeff s w₂ w m)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  rw [deckCuspCoeff_eisVec_eq_whittaker hN hs hw (neg_ne_zero.mpr hν.ne') hw₂ hm hy, abs_neg,
    abs_of_pos hν]

/-- **`⟨U, E(·|φ,w)⟩` as a line integral of the explicit pairing** on `Re s = σ ∈ (1, Re s₁)`. -/
theorem inner_poincL2_incEisL2_eq_integral_pairing (hN : 2 ≤ N) {s₁ : ℂ} (hs₁ : 1 < s₁.re)
    {μ : ℝ} (hμ : 0 < μ) {v : DeckSpace N} (hv : IsCuspEigen μ v) {n : ℤ}
    (hn : μ * ((N + 1 : ℕ) : ℝ) = n) (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun)
    {w : DeckSpace N} (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 < σ) (hσs : σ < s₁.re) :
    ⟪toDeckL2 _ (memLp_poincSeries_profile hs₁ hμ v), incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
        poincEisPairing s₁ μ v w n ((σ : ℂ) + t * Complex.I) := by
  rw [inner_poincL2_incEisL2_eq_integral_line hN hs₁ hμ v φ hφ hw hσ hσs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_inner_poincSeries_eisVec hN hs₁ hμ hv hn (by simpa using hσ) (by simpa using hσs) hw]

/-- **`⟨P(·|h̄_{s₂,ν},w₂), E(·|φ,w)⟩` as a line integral of the explicit pairing** on
`Re s = σ ∈ (1, Re s₂)`. -/
theorem inner_conjL2_incEisL2_eq_integral_pairing (hN : 2 ≤ N) {s₂ : ℂ} (hs₂ : 1 < s₂.re)
    {ν : ℝ} (hν : 0 < ν) {w₂ : DeckSpace N} (hw₂ : IsCuspEigen (-ν) w₂) {m : ℤ}
    (hm : -ν * ((N + 1 : ℕ) : ℝ) = m) (φ : HeightProfile) (hφ : ContDiff ℝ 2 φ.toFun)
    {w : DeckSpace N} (hw : IsCuspVec w) {σ : ℝ} (hσ : 1 < σ) (hσs : σ < s₂.re) :
    ⟪toDeckL2 _ (memLp_poincSeries_conjProfile hs₂ hν w₂), incEisL2 φ w⟫_ℂ =
      (Real.pi : ℂ)⁻¹ * ∫ t : ℝ, hMellin φ.toFun ((σ : ℂ) + t * Complex.I) *
        poincEisPairing (conj s₂) ν w₂ w m ((σ : ℂ) + t * Complex.I) := by
  rw [inner_conjL2_incEisL2_eq_integral_line hN hs₂ hν w₂ φ hφ hw hσ hσs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [integral_inner_poincSeries_conjProfile_eisVec hN hs₂ hν hw₂ hm (by simpa using hσ)
    (by simpa using hσs) hw]

end

end GaloisForLFunctions.RHTower.DeckPointPair
