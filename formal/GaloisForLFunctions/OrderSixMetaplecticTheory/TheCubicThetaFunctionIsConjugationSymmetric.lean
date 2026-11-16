import GaloisForLFunctions.OrderSixMetaplecticTheory.TheGaussSumSeriesAreConjugationSymmetric

/-!
# The cubic theta function is conjugation symmetric

The Fourier coefficient `ρ(h)` of the cubic theta function combines the residues at `s = 4/3` of two
continued Gauss-sum Dirichlet series: `D(s, h)` at the cusp `∞` and `U(s, 9h)` at the cusp `0`.

Both continuations are cusp Fourier coefficients `K(s)` of the corrected Eisenstein seed. They are
analytic off the real axis in `Re s > 1` and equal `D` (resp. `U`) times the Whittaker factor on
`Re s > 4` in **both** half-planes: the resolvent identification only needs the spectral parameter
`s(2 − s)` to be nonreal (`correction_initial_overlap_of_im_ne`). The series and the Whittaker factor
are conjugation symmetric at rational rows, so `K(s̄) = \overline{K(s)}` on `Re s > 4`; the identity
theorem in the lower half-plane spreads this to all of `Re s > 1` (`reflection_of_initial`).

Conjugation `h ↦ h̄` of the row conjugates both series and the Whittaker factor, so `K_{h̄}(s̄) = \overline{K_h(s)}`
on `Re s > 4`, and the identity theorem in the lower half-plane spreads this to all of `Re s > 1`
(`reflection_of_initial`). Residues at the real point `4/3` of reflected functions are conjugate
(`residue_star_of_reflection`). Hence **the cubic theta function is conjugation symmetric**:
`ρ(h̄) = \overline{ρ(h)}` for every row (`rationalSourceResidualFourierCoefficient_conj`). At `h = 1`: **the
theta scalar `C = \overline{ρ(1)}` is real** (`rationalSourceThetaScalar_star`); at the self-conjugate 3-adic row
`ω²λ²` the coefficient is real.
-/

noncomputable section

open Filter Topology MeasureTheory
open scoped MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### The resolvent identification off the real axis -/

/-- On `Re s > 4` the resolvent correction is the Eisenstein remainder in both half-planes. -/
theorem correction_initial_overlap_of_im_ne (a b : ℝ) (ha : 1 < a) (hab : a < b) (s : ℂ) (hs : 4 < s.re)
    (hi : s.im ≠ 0) :
    kernelEisensteinL2Correction a b (by linarith) hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => kernelQuotientEisenstein s (by linarith) q - kernelQuotientSeed a b s q := by
  rw [kernelEisensteinL2Correction_unique a b (by linarith) hab s
    (kernelSpectralFormOperator_isUnit_nonreal _
      (kernelEisensteinSpectralParameter_nonreal s (by linarith) hi))
    _ (kernelEisensteinRemainderL2_graph a b ha hab s hs)]
  exact kernelEisensteinRemainderL2_ae a b ha hab s hs

theorem kernelCuspFourierFamily_eq_of_im_ne (h : O) (hh : h ≠ 0) (s : ℂ) (hs : 4 < s.re) (hi : s.im ≠ 0) :
    kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s =
      ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) * scatteringCoefficient s h * cuspWhittakerHeightFactor s h :=
  kernelCuspFourierFamily_nonzero_of_initial_overlap h hh 2 3 (by norm_num) (by norm_num) s (by linarith)
    (correction_initial_overlap_of_im_ne 2 3 (by norm_num) (by norm_num) s hs hi)

theorem rationalCuspFamily_eq_of_im_ne (h : O) (g : rationalExtension)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (ha1 : 1 < a) (s : ℂ) (hs : 4 < s.re) (hi : s.im ≠ 0) :
    rationalCuspFamily h g a b ha hab s = ∫ w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (integralComplexMatrix (g : SL(2, O)) • w) *
        cuspFourierPhase h w ∂hyperbolicVolume := by
  have hcorrected : kernelCorrectedSeed a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientEisenstein s (by linarith) := by
    filter_upwards [correction_initial_overlap_of_im_ne a b ha1 hab s hs hi] with q hq
    change kernelQuotientSeed a b s q + kernelEisensteinL2Correction a b ha hab s q = _
    rw [hq]
    ring
  have hsource := (kernelRationalAction_measurePreserving g).quasiMeasurePreserving.ae_eq_comp hcorrected
  have hm := kernelProjection_cuspPeriodStrip_measurePreserving 5 6 (by norm_num)
  have he := hm.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hsource (s := kernelCuspStripSet))
  rw [rationalCuspFamily_actual_integral]
  apply integral_congr_ae
  filter_upwards [he] with w hw
  exact congrArg (fun z : ℂ => z * cuspFourierPhase h w)
    (hw.trans (by dsimp only [Function.comp_def]; rw [kernelRationalAction_mk, kernelQuotientEisenstein_mk]))

theorem rationalCuspFamily_opposite_of_im_ne (h : O) (s : ℂ) (hs : 4 < s.re) (hi : s.im ≠ 0) :
    rationalCuspFamily (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num) s =
      unramifiedCubicGaussSeries s h * cuspWhittakerHeightFactor s (3 * h) := by
  rw [rationalCuspFamily_eq_of_im_ne (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num) (by norm_num) s hs hi,
    opposite_cusp_fourier_average s (by linarith), show (9 : O) * (3 * h) = 27 * h by ring,
    unramifiedCubicGaussSeries_twentySeven]

/-! ### Reflection -/

theorem star_re' (s : ℂ) : (star s).re = s.re := Complex.conj_re s

theorem star_im' (s : ℂ) : (star s).im = -s.im := Complex.conj_im s

theorem star_four_thirds : star (4 / 3 : ℂ) = 4 / 3 := by
  rw [star_div₀, star_ofNat, star_ofNat]

/-- **Reflection.** Let `K, K'` be analytic off the real axis in `Re s > 1` with `K'(s̄) = \overline{K(s)}` on
`Re s > 4`. Then `K'(s̄) = \overline{K(s)}` on all of `Re s > 1`: the identity theorem in the lower half-plane. -/
theorem reflection_of_initial {K K' : ℂ → ℂ} (hK : ∀ s : ℂ, 1 < s.re → s.im ≠ 0 → AnalyticAt ℂ K s)
    (hK' : ∀ s : ℂ, 1 < s.re → s.im ≠ 0 → AnalyticAt ℂ K' s)
    (hinit : ∀ s : ℂ, 4 < s.re → 0 < s.im → K' (star s) = star (K s)) :
    ∀ s : ℂ, 1 < s.re → 0 < s.im → K' (star s) = star (K s) := by
  let L : Set ℂ := {s | 1 < s.re ∧ s.im < 0}
  have hLconv : Convex ℝ L :=
    ((convex_Ioi (1 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Iio (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hLopen : IsOpen L :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_im continuous_const)
  let G : ℂ → ℂ := fun s => (starRingEnd ℂ) (K ((starRingEnd ℂ) s))
  have hG : AnalyticOnNhd ℂ G L := by
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hLopen
    have hKd : DifferentiableAt ℂ K ((starRingEnd ℂ) s) :=
      (hK _ (by rw [Complex.conj_re]; exact hs.1) (by rw [Complex.conj_im]; linarith [hs.2])).differentiableAt
    have hc := hKd.conj_conj
    rw [Complex.conj_conj] at hc
    exact hc.differentiableWithinAt
  have hKL : AnalyticOnNhd ℂ K' L := fun s hs => hK' s hs.1 hs.2.ne
  have hstart : (5 - Complex.I : ℂ) ∈ L := by
    constructor <;> simp
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ s.im < 0} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_im continuous_const)
  have hevent : K' =ᶠ[𝓝 (5 - Complex.I)] G := by
    filter_upwards [hopen.mem_nhds (by constructor <;> simp; norm_num)] with s hs
    have h := hinit (star s) (by rw [star_re']; exact hs.1) (by rw [star_im']; linarith [hs.2])
    rw [star_star] at h
    exact h
  have heq := hKL.eqOn_of_preconnected_of_eventuallyEq hG hLconv.isPreconnected hstart hevent
  intro s hs1 hs2
  have hmem : star s ∈ L := ⟨by rw [star_re']; exact hs1, by rw [star_im']; linarith⟩
  have h := heq hmem
  change K' (star s) = (starRingEnd ℂ) (K ((starRingEnd ℂ) (star s))) at h
  rw [h, show (starRingEnd ℂ) (star s) = s from star_star s]
  rfl

/-- **Reflected residues at `4/3` are conjugate.** -/
theorem residue_star_of_reflection {K K' : ℂ → ℂ} {R R' : ℂ}
    (hres : Tendsto (fun s => (s - 4 / 3) * K s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R))
    (hres' : Tendsto (fun s => (s - 4 / 3) * K' s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 R'))
    (hrefl : ∀ s : ℂ, 1 < s.re → 0 < s.im → K' (star s) = star (K s)) : R' = star R := by
  let P : Set ℂ := {s | 0 < s.im}
  have hcl : (4 / 3 : ℂ) ∈ closure P := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨4 / 3 + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · change 0 < (4 / 3 + ((ε / 2 : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
  haveI : (𝓝[P] (4 / 3 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have hne : ∀ s ∈ P, s ≠ 4 / 3 := by
    intro s hs he
    have h0 : s.im = 0 := by rw [he]; norm_num
    have hs' : 0 < s.im := hs
    rw [h0] at hs'
    exact lt_irrefl 0 hs'
  have hle : 𝓝[P] (4 / 3 : ℂ) ≤ 𝓝[≠] (4 / 3) := nhdsWithin_mono _ hne
  have h1 := hres.mono_left hle
  have hconj : Tendsto star (𝓝[P] (4 / 3 : ℂ)) (𝓝[≠] (4 / 3)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (continuous_star.tendsto (4 / 3 : ℂ)).mono_left (nhdsWithin_le_nhds (s := P))
      rwa [star_four_thirds] at h
    · filter_upwards [self_mem_nhdsWithin] with s hs he
      have h0 := congrArg Complex.im he
      rw [star_im'] at h0
      have h0' : s.im = 0 := by norm_num at h0; linarith
      have hs' : 0 < s.im := hs
      rw [h0'] at hs'
      exact lt_irrefl 0 hs'
  have h2 := hres'.comp hconj
  have hre : ∀ᶠ s in 𝓝[P] (4 / 3 : ℂ), 1 < s.re := by
    apply nhdsWithin_le_nhds
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have h3 : Tendsto (fun s => star ((s - 4 / 3) * K s)) (𝓝[P] (4 / 3 : ℂ)) (𝓝 R') := by
    refine h2.congr' ?_
    filter_upwards [hre, self_mem_nhdsWithin] with s hs1 hs2
    change (star s - 4 / 3) * K' (star s) = _
    rw [hrefl s hs1 hs2, star_mul', star_sub, star_four_thirds]
  have h4 : Tendsto (fun s => star ((s - 4 / 3) * K s)) (𝓝[P] (4 / 3 : ℂ)) (𝓝 (star R)) :=
    (continuous_star.tendsto R).comp h1
  exact tendsto_nhds_unique h3 h4

/-! ### The residues at the two cusps conjugate -/

theorem conjO_three_mul (h : O) : conjO (3 * h) = 3 * conjO h := by
  rw [map_mul, conjO_ofNat]

theorem star_nineSqrtThree : star (((9 * Real.sqrt 3 / 2 : ℝ) : ℂ)) = ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) :=
  Complex.conj_ofReal _

/-- The residue of `D(·, h)` at the cusp `∞`: `R(h̄) = \overline{R(h)}`. -/
theorem nonzeroScatteringResidue_conj (h : O) (hh : h ≠ 0) :
    nonzeroScatteringResidue (conjO h) = star (nonzeroScatteringResidue h) := by
  have hh' : conjO h ≠ 0 := conjO_ne_zero hh
  have hK : ∀ k : O, ∀ s : ℂ, 1 < s.re → s.im ≠ 0 →
      AnalyticAt ℂ (kernelCuspFourierFamily k 2 3 (by norm_num) (by norm_num)) s := fun k s hs hi =>
    kernelCuspFourierFamily_analyticAt_nonreal k 2 3 (by norm_num) (by norm_num) s hs.ne' hi
  have hinit : ∀ s : ℂ, 4 < s.re → 0 < s.im →
      kernelCuspFourierFamily (conjO h) 2 3 (by norm_num) (by norm_num) (star s) =
        star (kernelCuspFourierFamily h 2 3 (by norm_num) (by norm_num) s) := by
    intro s hs hi
    rw [kernelCuspFourierFamily_eq_of_im_ne (conjO h) hh' (star s) (by rw [star_re']; exact hs)
        (by rw [star_im']; linarith),
      kernelCuspFourierFamily_eq_of_im_ne h hh s hs hi.ne', scatteringCoefficient_conj,
      cuspWhittakerHeightFactor_conj, star_mul', star_mul', star_nineSqrtThree]
  have hR := residue_star_of_reflection (kernelCuspFourierFamily_residue_limit h 2 3 (by norm_num) (by norm_num))
    (kernelCuspFourierFamily_residue_limit (conjO h) 2 3 (by norm_num) (by norm_num))
    (reflection_of_initial (hK h) (hK (conjO h)) hinit)
  have hW := cuspWhittakerHeightFactor_conj h (4 / 3)
  rw [star_four_thirds] at hW
  unfold nonzeroScatteringResidue
  rw [star_div₀, star_mul', star_nineSqrtThree, ← hW]
  exact congrArg (· / _) hR

/-- The residue of `U(·, h)` at the cusp `0`: `U(h̄) = \overline{U(h)}`. -/
theorem unramifiedGaussResidue_conj (h : O) :
    unramifiedGaussResidue (conjO h) = star (unramifiedGaussResidue h) := by
  have hK : ∀ k : O, ∀ s : ℂ, 1 < s.re → s.im ≠ 0 →
      AnalyticAt ℂ (rationalCuspFamily (3 * k) oppositeSource 2 3 (by norm_num) (by norm_num)) s :=
    fun k s hs hi =>
      rationalCuspFamily_analyticAt_nonreal (3 * k) oppositeSource 2 3 (by norm_num) (by norm_num) s hs.ne' hi
  have hinit : ∀ s : ℂ, 4 < s.re → 0 < s.im →
      rationalCuspFamily (3 * conjO h) oppositeSource 2 3 (by norm_num) (by norm_num) (star s) =
        star (rationalCuspFamily (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num) s) := by
    intro s hs hi
    have hW := cuspWhittakerHeightFactor_conj (3 * h) s
    rw [conjO_three_mul] at hW
    rw [rationalCuspFamily_opposite_of_im_ne (conjO h) (star s) (by rw [star_re']; exact hs)
        (by rw [star_im']; linarith),
      rationalCuspFamily_opposite_of_im_ne h s hs hi.ne', unramifiedCubicGaussSeries_conj, hW, star_mul']
  have hR := residue_star_of_reflection
    (rationalCuspFamily_residue_limit (3 * h) oppositeSource 2 3 (by norm_num) (by norm_num))
    (rationalCuspFamily_residue_limit (3 * conjO h) oppositeSource 2 3 (by norm_num) (by norm_num))
    (reflection_of_initial (hK h) (hK (conjO h)) hinit)
  have hW := cuspWhittakerHeightFactor_conj (3 * h) (4 / 3)
  rw [star_four_thirds, conjO_three_mul] at hW
  unfold unramifiedGaussResidue
  rw [star_div₀, ← hW]
  exact congrArg (· / _) hR

/-! ### The cubic theta function is conjugation symmetric -/

theorem tracePhase_of_star_eq_neg {z : ℂ} (hz : star z = -z) : tracePhase z = 1 := by
  change Complex.exp _ = 1
  rw [← Complex.star_def, hz, add_neg_cancel, mul_zero, Complex.exp_zero]

theorem rationalCuspPhaseSum_conj (h : O) : rationalCuspPhaseSum (conjO h) = star (rationalCuspPhaseSum h) := by
  have h1 : cuspFrequency (conjO h) = -star (cuspFrequency h) := by rw [star_cuspFrequency, neg_neg]
  unfold rationalCuspPhaseSum
  rw [h1, show -star (cuspFrequency h) * 2 = -star (cuspFrequency h * 2) by rw [star_mul', star_ofNat]; ring,
    tracePhase_neg_star, tracePhase_neg_star, star_add, star_add, star_one]

theorem norm_cuspFrequency_conj (h : O) : ‖cuspFrequency (conjO h)‖ = ‖cuspFrequency h‖ := by
  rw [← norm_star (cuspFrequency h), star_cuspFrequency, norm_neg]

/-- **The cubic theta function is conjugation symmetric:** `ρ(h̄) = \overline{ρ(h)}` for every row `h ≠ 0`. -/
theorem rationalSourceResidualFourierCoefficient_conj (h : O) (hh : h ≠ 0) :
    rationalSourceResidualFourierCoefficient (conjO h) = star (rationalSourceResidualFourierCoefficient h) := by
  have hreal : ∀ r : ℝ, star (r : ℂ) = r := fun r => Complex.conj_ofReal r
  have hΓ : star (Complex.Gamma (4 / 3)) = Complex.Gamma (4 / 3) := by
    rw [Complex.star_def, ← Complex.Gamma_conj, ← Complex.star_def, star_four_thirds]
  have hpow : star ((2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ)) =
      (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) ^ (1 / 3 : ℂ) := by
    rw [show (2 * Real.pi * ‖cuspFrequency h‖ : ℂ) = ((2 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow_star (by positivity), star_div₀, star_one, star_ofNat]
  have hopp : ∀ k : O, oppositeCuspResidue k = unramifiedGaussResidue (9 * k) := oppositeCuspResidue_eq_unramified
  have h9 : 9 * conjO h = conjO (9 * h) := by rw [map_mul, conjO_ofNat]
  rw [rationalSourceResidualFourierCoefficient_eq (conjO h) (conjO_ne_zero hh),
    rationalSourceResidualFourierCoefficient_eq h hh, rationalSourceScatteringResidue,
    rationalSourceScatteringResidue, if_neg (conjO_ne_zero hh), if_neg hh, hopp, hopp, h9,
    nonzeroScatteringResidue_conj h hh, unramifiedGaussResidue_conj, rationalCuspPhaseSum_conj,
    norm_cuspFrequency_conj]
  simp only [star_mul', star_add, star_div₀, star_inv₀, star_ofNat, hreal, hΓ, hpow]

/-- **The cubic theta scalar is real.** -/
theorem rationalSourceThetaScalar_star : star rationalSourceThetaScalar = rationalSourceThetaScalar := by
  have h := rationalSourceResidualFourierCoefficient_conj 1 one_ne_zero
  rw [map_one] at h
  unfold rationalSourceThetaScalar
  rw [star_star]
  exact h

theorem rationalSourceThetaScalar_im : rationalSourceThetaScalar.im = 0 :=
  Complex.conj_eq_iff_im.mp rationalSourceThetaScalar_star

/-- A row fixed by conjugation up to sign has a real theta coefficient. -/
theorem rationalSourceResidualFourierCoefficient_star_of_conj {h : O} (hh : h ≠ 0)
    (hc : conjO h = h ∨ conjO h = -h) :
    star (rationalSourceResidualFourierCoefficient h) = rationalSourceResidualFourierCoefficient h := by
  rw [← rationalSourceResidualFourierCoefficient_conj h hh]
  rcases hc with hc | hc
  · rw [hc]
  · rw [hc, rationalSourceResidualFourierCoefficient_neg]

theorem conjO_omega_sq_mul_lambda_sq : conjO (omega ^ 2 * lambda ^ 2) = omega ^ 2 * lambda ^ 2 := by
  rw [map_mul, map_pow, map_pow, conjO_omega, conjO_lambda]
  linear_combination (lambda ^ 2 * (omega ^ 4 + omega ^ 3 - omega ^ 2)) * omega_sq_add

/-- **A real 3-adic theta coefficient:** `T(ω²λ²)` is real (`ω²λ²` is fixed by conjugation). -/
theorem rationalSourceResidualFourierCoefficient_omega_sq_lambda_sq_star :
    star (rationalSourceResidualFourierCoefficient (omega ^ 2 * lambda ^ 2)) =
      rationalSourceResidualFourierCoefficient (omega ^ 2 * lambda ^ 2) :=
  rationalSourceResidualFourierCoefficient_star_of_conj
    (mul_ne_zero (pow_ne_zero 2 (omega_primitive.ne_zero (by norm_num))) (pow_ne_zero 2 residue_lambda_prime.ne_zero))
    (Or.inl conjO_omega_sq_mul_lambda_sq)

end GaloisForLFunctions.OrderSixMetaplecticTheory
