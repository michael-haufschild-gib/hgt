import GaloisForLFunctions.OrderSixMetaplecticTheory.TheShiftedHeckeTraceIsTwiceNormTranslatedProductsUpToABoundedRemainder
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheDilateCorrelationAtEveryPrimaryPrimeHasADoublePole

/-!
# The phased cubic twist carries a quarter of the double pole

Insert the shift phase `φ(k) = e(2ωξ_k)` into the Hecke-trace argument at a primary prime `p`. The bounded remainder
`R^ω_p = Tr_pF^ω − 2N(p)F_ω` has constant term `N(p)|P|(2ρ^{−2}R[φT(h)T(−p²h)](ρv) + ρR[φT(k)T(kp)](v/ρ) − 2R[φT²](v))`
(`cuspConstantTerm_heckeShiftRemainder`, `ρ = |p|`), so the phased dilate combination carries the double pole of
`2M(s)C(s)`, `C = Σφ(k)T(k)²(4π|ξ_k|)^{−s}` the translated correlation, whose leading coefficient is `27π³r³` (STCC).
The phase is invariant under `p^{3j+1}` (`p ≡ 1 mod 3`), so Patterson's relations give the same Euler identity
`D^φ_{p²} = ρρ^{−s}(1 − ρ²ρ^{−3s})^{−1}D^φ_{dil}` (`besselDirichlet_phShiftSq`) and the same factor `c_p(s)`. With
`T(k)T(kp) = (9/p)₃\overline{G̃(p)}(k/p)₃T(k)²`:

**the phased cubic twist `Σ_kφ(k)(k/p)₃T(k)²(4π|ξ_k|)^{−s}` has the double pole of `L_{χ_p}` with a quarter of its
leading coefficient** (`phasedCubicTwist_double_pole`).
-/

noncomputable section

open MeasureTheory Filter Function Topology
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem summable_phShiftSq {σ : ℝ} (hσ : 4 < σ) (b : O) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.phShiftSq b h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [phShiftSq, norm_mul, norm_shiftPhase, one_mul] using P.summable_shiftSqCoeff hσ

theorem summable_phDilate {σ : ℝ} (hσ : 4 < σ) (b : O) :
    Summable (fun h : O => if h = 0 then 0 else ‖P.phDilate b h‖ * ‖cuspFrequency h‖ ^ (-σ)) := by
  simpa only [phDilate, norm_mul, norm_shiftPhase, one_mul] using P.summable_dilateCoeff hσ

/-! ### The Mellin identity -/

/-- **The constant term of `R^ω_p`.** -/
theorem cuspConstantTerm_heckeShiftRemainder (v : ℝ) (hv : 0 < v) :
    cuspConstantTerm P.heckeShiftRemainder v = (Fintype.card P.Res : ℂ) * periodArea *
      (2 * ((‖ringComplex P.p‖ : ℂ) ^ 2)⁻¹ * besselRemainder (P.phShiftSq omega) (‖ringComplex P.p‖ * v) +
        (‖ringComplex P.p‖ : ℂ) * besselRemainder (P.phDilate omega) (v / ‖ringComplex P.p‖) -
          2 * besselRemainder translatedCoeff v) := by
  have hlift : ∀ z, cuspCoordinateLift (v, z) = upperPoint z v hv := fun z => cuspCoordinateLift_positive v z hv
  have hc1 : Continuous (fun z : ℂ => P.heckeShiftTrace sourceTheta omega (upperPoint z v hv)) :=
    P.heckeShiftTrace_source_continuous.comp (continuous_upperPoint_z v hv)
  have hc2 : Continuous (fun z : ℂ => translatedThetaProduct (upperPoint z v hv)) :=
    translatedThetaProduct_continuous.comp (continuous_upperPoint_z v hv)
  have hT := cuspConstantTerm_translatedThetaProduct v hv
  rw [cuspConstantTerm] at hT
  simp_rw [hlift] at hT
  have hcp : ((v ^ ((4 : ℝ) / 3) : ℝ) : ℂ) = (v : ℂ) ^ (4 / 3 : ℂ) := by
    rw [Complex.ofReal_cpow hv.le]
    norm_num
  rw [cuspConstantTerm]
  simp_rw [hlift, heckeShiftRemainder]
  rw [integral_sub (integrableOn_periodDomain_of_continuous _ hc1)
    ((integrableOn_periodDomain_of_continuous _ hc2).const_mul _), integral_const_mul,
    P.integral_sourceHeckeShiftTrace_bessel omega v hv, hT, hcp]
  simp only [thetaCoeff, thetaConstant]
  ring

/-- **The Mellin identity of `R^ω_p`.** For `4 < Re s < 13/3`:
`∫ R^ω_pE(s) = N(p)|P|M(s)(2ρ^{−s}D^φ_{p²}(s) + ρ^{s−1}D^φ_{dil}(s) − 2C(s))`. -/
theorem integral_heckeShiftRemainder_mul_eisenstein (s : ℂ) (hs4 : 4 < s.re) (hs : s.re < 13 / 3) :
    ∫ w in levelSet, P.heckeShiftRemainder w * hyperbolicEisenstein s w ∂hyperbolicVolume =
      (Fintype.card P.Res : ℂ) * periodArea * (besselSqMellin s *
        (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet (P.phShiftSq omega) s +
          ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet (P.phDilate omega) s -
            2 * besselDirichlet translatedCoeff s)) := by
  have hG := P.heckeShiftRemainder_remainderData
  have hn := P.norm_pos
  set ρ := ‖ringComplex P.p‖ with hρ
  have hs23 : 2 / 3 < s.re := by linarith
  rw [hG.integral_mul_eisenstein s (by linarith) hs]
  set RA := besselRemainder (P.phShiftSq omega)
  set RD := besselRemainder (P.phDilate omega)
  set R := besselRemainder translatedCoeff
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
      (v : ℂ) ^ s * (∫ z in periodDomain, P.heckeShiftRemainder (cuspCoordinateLift (v, z))) / (v : ℂ) ^ 3 =
        (Fintype.card P.Res : ℂ) * periodArea * (2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3) +
          (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3) - 2 * ((v : ℂ) ^ s * R v / (v : ℂ) ^ 3)) := by
    intro v (hv : 0 < v)
    have hc := P.cuspConstantTerm_heckeShiftRemainder v hv
    rw [cuspConstantTerm] at hc
    rw [hc, show v / ρ = 1 / ρ * v by ring]
    ring
  have hIA := integrableOn_mellin_comp_mul RA s hn
    (integrableOn_besselRemainder (P.phShiftSq omega) s hs23 (P.summable_phShiftSq hs4 omega))
  have hID := integrableOn_mellin_comp_mul RD s (one_div_pos.mpr hn)
    (integrableOn_besselRemainder (P.phDilate omega) s hs23 (P.summable_phDilate hs4 omega))
  have hI := integrableOn_besselRemainder translatedCoeff s hs23 (summable_translatedCoeff hs4)
  have J1 : IntegrableOn (fun v : ℝ => 2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3))
      (Set.Ioi 0) := hIA.const_mul _
  have J2 : IntegrableOn (fun v : ℝ => (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) :=
    hID.const_mul _
  have J3 : IntegrableOn (fun v : ℝ => 2 * ((v : ℂ) ^ s * R v / (v : ℂ) ^ 3)) (Set.Ioi 0) := hI.const_mul _
  have J12 : IntegrableOn (fun v : ℝ => 2 * ((ρ : ℂ) ^ 2)⁻¹ * ((v : ℂ) ^ s * RA (ρ * v) / (v : ℂ) ^ 3) +
      (ρ : ℂ) * ((v : ℂ) ^ s * RD (1 / ρ * v) / (v : ℂ) ^ 3)) (Set.Ioi 0) := J1.add J2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, integral_sub J12 J3,
    integral_add J1 J2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_mellin_comp_mul RA s hn, integral_mellin_comp_mul RD s (one_div_pos.mpr hn),
    integral_besselRemainder (P.phShiftSq omega) s hs23 (P.summable_phShiftSq hs4 omega),
    integral_besselRemainder (P.phDilate omega) s hs23 (P.summable_phDilate hs4 omega),
    integral_besselRemainder translatedCoeff s hs23 (summable_translatedCoeff hs4)]
  obtain ⟨h1, h2⟩ := real_cpow_identities ρ hn s
  linear_combination (Fintype.card P.Res : ℂ) * periodArea * besselSqMellin s *
    (2 * besselDirichlet (P.phShiftSq omega) s * h1 + besselDirichlet (P.phDilate omega) s * h2)

/-- **The phased dilate combination carries the double pole of `2M(s)C(s)`.** -/
theorem phasedDilateCombination_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * (2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet (P.phShiftSq omega) s +
          ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet (P.phDilate omega) s)) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (2 * (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3))) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl, -⟩ := translatedCorrelation_double_pole
  have hG := P.heckeShiftRemainder_remainderData
  have hq : ((Fintype.card P.Res : ℂ) * periodArea : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (Complex.ofReal_ne_zero.mpr periodAreaReal_pos.ne')
  refine ⟨fun s => 2 * Λ s + ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ * hG.pairing s, fun s hs4 hs hi => ?_,
    fun s hs1 hs hi => ?_, ?_, ?_⟩
  · show 2 * Λ s + ((Fintype.card P.Res : ℂ) * periodArea)⁻¹ * hG.pairing s = _
    rw [hΛ s hs4 hs hi, ← hG.pairing_eq s hs4 hs hi, P.integral_heckeShiftRemainder_mul_eisenstein s hs4 hs,
      inv_mul_cancel_left₀ hq]
    ring
  · exact ((hΛd s hs1 hs hi).const_mul _).add ((hG.pairing_differentiableAt s hs1 hs hi).const_mul _)
  · filter_upwards [hΛn, hG.pairing_near_four_thirds.1] with s h1 h2
    exact (h1.const_mul _).add (h2.const_mul _)
  · have h2 := hG.pairing_near_four_thirds.2
    have hsum := (hΛl.const_mul 2).add (h2.const_mul ((Fintype.card P.Res : ℂ) * periodArea)⁻¹)
    rw [mul_zero, add_zero] at hsum
    refine hsum.congr' (Eventually.of_forall fun s => ?_)
    ring

/-! ### Patterson's relations with the phase -/

theorem three_dvd_p_pow_sub_one (n : ℕ) : (3 : O) ∣ P.p ^ n - 1 :=
  P.three_dvd_sub_one.trans (by simpa only [one_pow] using sub_dvd_pow_sub_pow P.p 1 n)

/-- **The phased Euler identity at `p`.** `D^φ_{p²}(s) = ρρ^{−s}(1 − ρ²ρ^{−3s})^{−1}D^φ_{dil}(s)`. -/
theorem besselDirichlet_phShiftSq (s : ℂ) (hs : 4 < s.re) :
    besselDirichlet (P.phShiftSq omega) s =
      (‖ringComplex P.p‖ : ℂ) * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) *
        (1 - (‖ringComplex P.p‖ : ℂ) ^ 2 * (((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s)) ^ 3)⁻¹ *
          besselDirichlet (P.phDilate omega) s := by
  set t : ℂ := ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) with htdef
  set ρc : ℂ := (‖ringComplex P.p‖ : ℂ) with hρc
  let w : O → ℂ := fun h => ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)
  let F : O → ℂ := fun h => if h = 0 then 0 else P.phShiftSq omega h * w h
  let g : P.Coprime → ℂ := fun x => P.phDilate omega x.val * w x.val
  have hq := P.norm_rho_cube_lt s (by linarith)
  have hsupp : Function.support F ⊆ Set.range P.tripleIndex := by
    intro h hF
    have hh : h ≠ 0 := fun h0 => hF (by simp [F, h0])
    obtain ⟨k, x, hx, rfl⟩ := WfDvdMonoid.max_power_factor hh P.prime.irreducible
    by_cases hk : k % 3 = 1
    · refine ⟨(k / 3, ⟨x, hx⟩), ?_⟩
      simp only [tripleIndex]
      congr 2
      omega
    · exfalso
      apply hF
      simp [F, hh, phShiftSq, P.shiftSqCoeff_eq_zero k x hx hk]
  have hterm : ∀ q : ℕ × P.Coprime, F (P.tripleIndex q) = (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := by
    rintro ⟨j, x, hx⟩
    have hne : P.p ^ (3 * j + 1) * x ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ P.ne_zero) (fun h0 => hx (by rw [h0]; exact dvd_zero _))
    have hph : shiftPhase omega (P.p ^ (3 * j + 1) * x) = shiftPhase omega x := by
      rw [mul_comm]
      exact shiftPhase_mul_of_three_dvd omega x _ (P.three_dvd_p_pow_sub_one _)
    simp only [F, g, w, tripleIndex]
    rw [if_neg hne, phShiftSq, phDilate, hph, P.shiftSqCoeff_index j x hx, P.weight_tripleIndex, mul_pow, pow_mul]
    ring
  have hgsum : Summable (fun x : P.Coprime => ‖g x‖) := by
    refine (((P.summable_phDilate hs omega).subtype {x : O | ¬ P.p ∣ x}).mul_left
      ((4 * Real.pi) ^ (-s.re))).congr fun x => ?_
    have hx0 := Coprime.ne_zero x
    have hξ : 0 < ‖cuspFrequency x.val‖ := norm_pos_iff.mpr (cuspFrequency_ne_zero _ hx0)
    simp only [Function.comp, if_neg hx0, g, w, norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re,
      Real.mul_rpow (by positivity) hξ.le]
    ring
  have hqsum : Summable (fun j : ℕ => ‖(ρc ^ 2 * t ^ 3) ^ j‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) hq
  have hD : ∑' x : P.Coprime, g x = besselDirichlet (P.phDilate omega) s := by
    have hsub : Function.support (fun h : O => if h = 0 then 0 else
        P.phDilate omega h * ((4 * Real.pi * ‖cuspFrequency h‖ : ℝ) : ℂ) ^ (-s)) ⊆ {x : O | ¬ P.p ∣ x} := by
      intro h hG hd
      apply hG
      simp [phDilate, dilateCoeff, hd]
    rw [besselDirichlet, ← tsum_subtype_eq_of_support_subset hsub]
    refine tsum_congr fun x => ?_
    simp only [g, w, if_neg (Coprime.ne_zero x)]
  calc besselDirichlet (P.phShiftSq omega) s = ∑' h, F h := rfl
    _ = ∑' q : ℕ × P.Coprime, F (P.tripleIndex q) := (P.tripleIndex_injective.tsum_eq hsupp).symm
    _ = ∑' q : ℕ × P.Coprime, (ρc * t) * ((ρc ^ 2 * t ^ 3) ^ q.1 * g q.2) := tsum_congr hterm
    _ = (ρc * t) * ((∑' j : ℕ, (ρc ^ 2 * t ^ 3) ^ j) * ∑' x : P.Coprime, g x) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hqsum hgsum]
    _ = _ := by
        rw [tsum_geometric_of_norm_lt_one hq, hD]
        simp only [htdef, hρc]
        ring

theorem phasedCombination_eq (s : ℂ) (hs : 4 < s.re) :
    2 * ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (-s) * besselDirichlet (P.phShiftSq omega) s +
        ((‖ringComplex P.p‖ : ℝ) : ℂ) ^ (s - 1) * besselDirichlet (P.phDilate omega) s =
      P.dilateFactor s * besselDirichlet (P.phDilate omega) s := by
  rw [P.besselDirichlet_phShiftSq s hs, dilateFactor]
  ring

/-- **The phased dilate correlation has a quarter of the double pole of the dilate correlation.** -/
theorem phasedDilateCorrelation_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
        Λ s = besselSqMellin s * besselDirichlet (P.phDilate omega) s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ))
        (𝓝 (2 * (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) / P.dilateFactor (4 / 3))) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl⟩ := P.phasedDilateCombination_double_pole
  have hre43 : (2 / 3 : ℝ) < (4 / 3 : ℂ).re := by norm_num
  have hc0 : P.dilateFactor (4 / 3) ≠ 0 := P.dilateFactor_ne_zero _ hre43
  refine ⟨fun s => Λ s / P.dilateFactor s, fun s hs4 hs hi => ?_, fun s hs1 hs hi => ?_, ?_, ?_⟩
  · have hc := P.dilateFactor_ne_zero s (by linarith)
    show Λ s / P.dilateFactor s = _
    rw [hΛ s hs4 hs hi, P.phasedCombination_eq s hs4, div_eq_iff hc]
    ring
  · exact (hΛd s hs1 hs hi).div (P.dilateFactor_differentiableAt s (by linarith))
      (P.dilateFactor_ne_zero s (by linarith))
  · have hre : ∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), 2 / 3 < s.re :=
      eventually_nhdsWithin_of_eventually_nhds
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre43)
    filter_upwards [hΛn, hre] with s h1 h2
    exact h1.div (P.dilateFactor_differentiableAt s h2) (P.dilateFactor_ne_zero s h2)
  · have hcont : Tendsto P.dilateFactor (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.dilateFactor (4 / 3))) :=
      (P.dilateFactor_differentiableAt _ hre43).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine (hΛl.div hcont hc0).congr' (Eventually.of_forall fun s => ?_)
    simp only [Pi.div_apply]
    ring

/-! ### The phased cubic twist -/

/-- `φ(k)(k/p)₃T(k)²`. -/
def phTwistCoeff (k : O) : ℂ := shiftPhase omega k * P.twistCoeff k

/-- The leading coefficient `216π³r³/(c_p(4/3)(9/p)₃\overline{G̃(p)})` of the cubic twist `L_{χ_p}`. -/
def twistLimit : ℂ :=
  2 * (108 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
    (P.dilateFactor (4 / 3) * (ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p)))

theorem twistLimit_ne_zero : P.twistLimit ≠ 0 := by
  obtain ⟨-, -, -, -, -, hne⟩ := P.cubicTwistAtPrime_double_pole
  exact hne

/-- **The phased cubic twist carries a quarter of the double pole of `L_{χ_p}`.** For every primary prime `p`,
`M(s)L^φ_{χ_p}(s)`, `L^φ_{χ_p}(s) = Σ_kφ(k)(k/p)₃T(k)²(4π|ξ_k|)^{−s}`, continues to `{1 < Re s < 13/3, Im s > 0}`
and a punctured neighbourhood of `4/3`, and `(s − 4/3)²M(s)L^φ_{χ_p}(s) → L/4`, `L` the leading coefficient of
`L_{χ_p}`. -/
theorem phasedCubicTwist_double_pole :
    ∃ Λ : ℂ → ℂ,
      (∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * besselDirichlet P.phTwistCoeff s) ∧
      (∀ s : ℂ, 1 < s.re → s.re < 13 / 3 → 0 < s.im → DifferentiableAt ℂ Λ s) ∧
      (∀ᶠ s in 𝓝[≠] (4 / 3 : ℂ), DifferentiableAt ℂ Λ s) ∧
      Tendsto (fun s => (s - 4 / 3) ^ 2 * Λ s) (𝓝[≠] (4 / 3 : ℂ)) (𝓝 (P.twistLimit / 4)) := by
  obtain ⟨Λ, hΛ, hΛd, hΛn, hΛl⟩ := P.phasedDilateCorrelation_double_pole
  set κ₀ := ringComplex (symbol 9 P.p) * star (normalizedCubicUnitGauss P.p) with hκ₀
  have hκ := P.twistFactor_ne_zero
  have hD : ∀ s, besselDirichlet (P.phDilate omega) s = κ₀ * besselDirichlet P.phTwistCoeff s := by
    intro s
    rw [besselDirichlet, besselDirichlet, ← tsum_mul_left]
    refine tsum_congr fun h => ?_
    split_ifs
    · ring
    · rw [phDilate, phTwistCoeff, P.dilateCoeff_eq_twist]
      ring
  refine ⟨fun s => Λ s / κ₀, fun s hs4 hs hi => ?_, fun s hs1 hs hi => (hΛd s hs1 hs hi).div_const _, ?_, ?_⟩
  · show Λ s / κ₀ = _
    rw [hΛ s hs4 hs hi, hD, div_eq_iff hκ]
    ring
  · filter_upwards [hΛn] with s h1
    exact h1.div_const _
  · have h := hΛl.div_const κ₀
    have hval : P.twistLimit / 4 = 2 * (27 * (Real.pi : ℂ) ^ 3 * constantArithmeticResidue ^ 3) /
        P.dilateFactor (4 / 3) / κ₀ := by
      rw [twistLimit, ← hκ₀]
      ring
    rw [hval]
    refine h.congr' (Eventually.of_forall fun s => ?_)
    simp only
    ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
