import GaloisForLFunctions.RHTower.PrimeArchBernsteinConfinedPhase
import GaloisForLFunctions.RHTower.PrimeArchBernsteinNegativeMassAbscissa
import GaloisForLFunctions.RHTower.BernsteinEllipseRigidity
import GaloisForLFunctions.RHTower.FiniteExponentialPencilDominantConstant

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Failure of RH produces an attained maximal endpoint amplitude and a Bernstein pencil on which
that exact maximal exponential mode survives with an eventual positive margin. -/
theorem exists_maximalAmplitude_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ w : ℂ, ∃ r δ : ℝ,
      ‖w‖ = 1 ∧ 1 < r ∧ 0 < δ ∧
        (∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ r) ∧
        (∃ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q = r) ∧
        ∀ᶠ n : ℕ in atTop,
          δ ≤ ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w /
            (r : ℂ) ^ n‖ := by
  classical
  let R : ℝ := primeArchEndpointHausdorffRadius
  let u : XiZeroCopy → ℂ := xiEndpointNormalizedReciprocalSquare
  let A : XiZeroCopy → ℝ := xiEndpointBernsteinAtomAmplitudeBase
  let a : XiZeroCopy → ℂ := fun q => (A q : ℂ)
  have hR : 0 < R := primeArchEndpointHausdorffRadius_pos
  have hu : Tendsto u cofinite (nhds 0) := by
    have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
      summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
    simpa [u, xiEndpointNormalizedReciprocalSquare, R] using
      hzero.div_const (primeArchEndpointHausdorffRadius : ℂ)
  have hA : Tendsto A cofinite (nhds 1) := by
    have hone : Tendsto (fun _ : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
      tendsto_const_nhds
    have h := hu.norm.add (hone.sub hu).norm
    simpa only [A, xiEndpointBernsteinAtomAmplitudeBase, u, norm_zero,
      sub_zero, norm_one, zero_add] using h
  have ha : Tendsto a cofinite (nhds 1) := by
    have h := Complex.continuous_ofReal.tendsto 1
    have := h.comp hA
    simpa only [a, Complex.ofReal_one] using this
  obtain ⟨q₀, hq₀im0⟩ :=
    exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis hRH
  have hq₀uim : (u q₀).im ≠ 0 := by
    dsimp only [u, xiEndpointNormalizedReciprocalSquare]
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
      Complex.normSq_ofReal]
    exact div_ne_zero (mul_ne_zero hq₀im0 hR.ne') (mul_ne_zero hR.ne' hR.ne')
  have hq₀A : 1 < A q₀ := by
    simpa only [A, xiEndpointBernsteinAtomAmplitudeBase, u, add_comm] using
      one_lt_norm_add_norm_one_sub hq₀uim
  have hAnorm (q : XiZeroCopy) : ‖a q‖ = A q := by
    have hnonneg : 0 ≤ A q := by
      exact add_nonneg (norm_nonneg _) (norm_nonneg _)
    dsimp only [a]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hq₀a : 1 < ‖a q₀‖ := by
    rw [hAnorm]
    exact hq₀A
  obtain ⟨D, r, hr, hDne, hD, hDsub⟩ :=
    exists_finite_maximal_norm_packet_of_tendsto_cofinite_one a ha hq₀a
  obtain ⟨qmax, hqmaxD⟩ := hDne
  have hAofD (q : XiZeroCopy) (hq : q ∈ D) : A q = r := by
    simpa only [hAnorm] using hD q hq
  have hqmaxA : A qmax = r := by
    exact hAofD qmax hqmaxD
  have hoff_of_mem_D (q : XiZeroCopy) (hq : q ∈ D) :
      (q.1 : ℂ).re ≠ 1 / 2 := by
    intro hline
    have hone := xiEndpointBernsteinAtomAmplitudeBase_eq_one_of_onLine q hline
    change A q = 1 at hone
    have hAr := hAofD q hq
    linarith
  have huim_of_mem_D (q : XiZeroCopy) (hq : q ∈ D) : (u q).im ≠ 0 := by
    have hoff := hoff_of_mem_D q hq
    have him0 : (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact fun him => hoff ((xiCentralReciprocalSquare_im_eq_zero_iff q.1).mp him)
    dsimp only [u, xiEndpointNormalizedReciprocalSquare]
    rw [Complex.div_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_div, sub_zero,
      Complex.normSq_ofReal]
    exact div_ne_zero (mul_ne_zero him0 hR.ne') (mul_ne_zero hR.ne' hR.ne')
  have hqmaxuim : (u qmax).im ≠ 0 := huim_of_mem_D qmax hqmaxD
  let w : ℂ := bernsteinEllipsePhase (u qmax)
  have hw : ‖w‖ = 1 := by
    simpa only [w] using bernsteinEllipsePhase_norm_eq_one hqmaxuim
  have hqmaxattain : ‖1 - u qmax + u qmax * w‖ = A qmax := by
    obtain ⟨w', hw', heq, _⟩ :=
      exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero hqmaxuim
    have hw'eq := bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude
      hqmaxuim hw' heq
    rw [hw'eq] at heq
    simpa only [w, A, xiEndpointBernsteinAtomAmplitudeBase, u, add_comm] using heq
  let b : XiZeroCopy → ℂ := xiBernsteinAffineBase R w
  have hb_eq (q : XiZeroCopy) : b q = 1 - u q + u q * w := by
    rfl
  have hb_le_A (q : XiZeroCopy) : ‖b q‖ ≤ A q := by
    rw [hb_eq]
    calc
      ‖1 - u q + u q * w‖ ≤ ‖1 - u q‖ + ‖u q * w‖ := norm_add_le _ _
      _ = ‖1 - u q‖ + ‖u q‖ := by rw [norm_mul, hw, mul_one]
      _ = A q := by
        simp only [A, xiEndpointBernsteinAtomAmplitudeBase, u, add_comm]
  let F : Finset XiZeroCopy := D.filter (fun q => ‖b q‖ = r)
  have hqmaxb : ‖b qmax‖ = r := by
    rw [hb_eq, hqmaxattain, hqmaxA]
  have hqmaxF : qmax ∈ F := by
    exact Finset.mem_filter.mpr ⟨hqmaxD, hqmaxb⟩
  have hbsub : ∀ q ∉ F, ‖b q‖ < r := by
    intro q hqF
    by_cases hqD : q ∈ D
    · have hle : ‖b q‖ ≤ r := (hb_le_A q).trans_eq (hAofD q hqD)
      exact lt_of_le_of_ne hle (fun heq => hqF (Finset.mem_filter.mpr ⟨hqD, heq⟩))
    · have hAlt : A q < r := by
        have := hDsub q hqD
        simpa only [hAnorm] using this
      exact (hb_le_A q).trans_lt hAlt
  have hu_eq_of_mem_F (q : XiZeroCopy) (hqF : q ∈ F) : u q = u qmax := by
    have hqD : q ∈ D := (Finset.mem_filter.mp hqF).1
    have hqb : ‖b q‖ = r := (Finset.mem_filter.mp hqF).2
    have hquim : (u q).im ≠ 0 := huim_of_mem_D q hqD
    have hqattain : ‖1 - u q + u q * w‖ = ‖1 - u q‖ + ‖u q‖ := by
      rw [← hb_eq, hqb, ← hAofD q hqD]
      simp only [A, xiEndpointBernsteinAtomAmplitudeBase, u, add_comm]
    have hphaseq : bernsteinEllipsePhase (u q) = bernsteinEllipsePhase (u qmax) := by
      have := bernsteinEllipsePhase_eq_of_norm_affine_eq_amplitude hquim hw hqattain
      simpa only [w] using this.symm
    have hampq : ‖u q‖ + ‖1 - u q‖ = ‖u qmax‖ + ‖1 - u qmax‖ := by
      have hqA := hAofD q hqD
      have heqA : A q = A qmax := hqA.trans hqmaxA.symm
      simpa only [A, xiEndpointBernsteinAtomAmplitudeBase, u] using heqA
    rcases eq_or_eq_one_sub_conj_of_bernsteinEllipsePhase_eq_of_amplitude_eq
      hqmaxuim hquim hphaseq hampq with heq | hreflect
    · exact heq
    · have hqoff := hoff_of_mem_D q hqD
      have hmaxoff := hoff_of_mem_D qmax hqmaxD
      have hqbound := norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius q hqoff
      have hmaxbound :=
        norm_xiEndpointNormalizedReciprocalSquare_le_offLineRadius qmax hmaxoff
      change ‖u q‖ ≤ xiOffLineNormalizedBernsteinRadius at hqbound
      change ‖u qmax‖ ≤ xiOffLineNormalizedBernsteinRadius at hmaxbound
      have hone : (1 : ℝ) ≤ ‖1 - star (u qmax)‖ + ‖star (u qmax)‖ := by
        have htri := norm_add_le (1 - star (u qmax)) (star (u qmax))
        norm_num at htri ⊢
        exact htri
      rw [← hreflect, norm_star] at hone
      nlinarith [xiOffLineNormalizedBernsteinRadius_lt_one_fourth]
  have hbconst : ∀ q ∈ F, b q = b qmax := by
    intro q hq
    rw [hb_eq, hb_eq, hu_eq_of_mem_F q hq]
  let c : XiZeroCopy → ℂ := xiZeroCopyReciprocalSquare
  have hcconst : ∀ q ∈ F, c q = c qmax := by
    intro q hq
    have huEq := hu_eq_of_mem_F q hq
    dsimp only [u, xiEndpointNormalizedReciprocalSquare] at huEq
    exact (div_left_inj' (Complex.ofReal_ne_zero.mpr hR.ne')).mp huEq
  have hcmax : c qmax ≠ 0 := by
    dsimp only [c]
    rw [xiZeroCopyReciprocalSquare_eq]
    exact xiCentralReciprocalSquare_ne_zero qmax.1
  have hC : ∑ q ∈ F, c q ≠ 0 := by
    have hcard : ((F.card : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.card_pos.mpr ⟨qmax, hqmaxF⟩))
    rw [Finset.sum_eq_card_nsmul hcconst, nsmul_eq_mul]
    exact mul_ne_zero hcard hcmax
  have hevent :=
    eventually_norm_tsum_normalizedExponentialPencil_ge_of_dominant_constant
      c b summable_xiZeroCopyReciprocalSquare F (lt_trans (by norm_num) hr)
      hbconst hbsub hqmaxb hC
  let δ : ℝ := ‖∑ q ∈ F, c q‖ / 2
  have hδ : 0 < δ := half_pos (norm_pos_iff.mpr hC)
  have heq (n : ℕ) :
      (∑' q : XiZeroCopy, c q * (b q / (r : ℂ)) ^ n) =
        xiCentralBernsteinPencil R n w / (r : ℂ) ^ n := by
    rw [show (∑' q : XiZeroCopy, c q * (b q / (r : ℂ)) ^ n) =
        (∑' q : XiZeroCopy, c q * b q ^ n) / (r : ℂ) ^ n by
      simp_rw [div_pow, div_eq_mul_inv]
      rw [show (fun q : XiZeroCopy =>
          c q * (b q ^ n * ((r : ℂ) ^ n)⁻¹)) =
          fun q : XiZeroCopy => (c q * b q ^ n) * ((r : ℂ) ^ n)⁻¹ by
            funext q
            ring]
      rw [tsum_mul_right]]
    rfl
  have hAmax (q : XiZeroCopy) : A q ≤ r := by
    by_cases hqD : q ∈ D
    · exact (hAofD q hqD).le
    · simpa only [hAnorm] using (hDsub q hqD).le
  refine ⟨w, r, δ, hw, hr, hδ,
    (fun q => by simpa only [A] using hAmax q),
    ⟨qmax, by simpa only [A] using hqmaxA⟩, ?_⟩
  filter_upwards [hevent] with n hn
  rw [← heq]
  exact hn

/-- Failure of RH produces a Bernstein pencil whose maximal exponential mode survives with an
eventual positive margin. -/
theorem exists_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ w : ℂ, ∃ r δ : ℝ,
      ‖w‖ = 1 ∧ 1 < r ∧ 0 < δ ∧
        ∀ᶠ n : ℕ in atTop,
          δ ≤ ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w /
            (r : ℂ) ^ n‖ := by
  obtain ⟨w, r, δ, hw, hr, hδ, _, _, hevent⟩ :=
    exists_maximalAmplitude_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_rh hRH
  exact ⟨w, r, δ, hw, hr, hδ, hevent⟩

/-- Failure of RH forces an eventual exponential lower envelope for the positive endpoint
Bernstein purity, up to its unavoidable linear dimension factor. -/
theorem exists_eventually_exponential_lower_envelope_primeArchEndpointBernsteinPurity_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ ρ η : ℝ, 1 < ρ ∧ 0 < η ∧
      ∀ᶠ n : ℕ in atTop,
        η * ρ ^ n ≤ (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := by
  obtain ⟨w, r, δ, hw, hr, hδ, hevent⟩ :=
    exists_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_riemannHypothesis hRH
  have hrpos : 0 < r := lt_trans (by norm_num) hr
  refine ⟨r ^ 2, δ ^ 2, ?_, sq_pos_of_pos hδ, ?_⟩
  · nlinarith [sq_pos_of_pos (sub_pos.mpr hr)]
  filter_upwards [hevent] with n hn
  have hrpow : 0 < r ^ n := pow_pos hrpos n
  have hn' : δ ≤
      ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ / r ^ n := by
    simpa only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrpos] using hn
  have hlower : δ * r ^ n ≤
      ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ := by
    exact (le_div_iff₀ hrpow).mp hn'
  have htransform :
      ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ ≤
        primeArchEndpointBernsteinTotalVariation n := by
    rw [← bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil]
    exact norm_bernsteinCoefficientTransform_le_l1 _ _ hw.le
  have hTVnonneg : 0 ≤ primeArchEndpointBernsteinTotalVariation n := by
    rw [primeArchEndpointBernsteinTotalVariation, bernsteinCoefficientL1]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq :
      (δ * r ^ n) ^ 2 ≤ primeArchEndpointBernsteinTotalVariation n ^ 2 := by
    exact (sq_le_sq₀
      (mul_nonneg hδ.le (pow_nonneg hrpos.le n))
      hTVnonneg).2
      (hlower.trans htransform)
  have hcard := bernsteinCoefficientL1_sq_le_card_mul_purity
    (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n
  change primeArchEndpointBernsteinTotalVariation n ^ 2 ≤
      (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n at hcard
  calc
    δ ^ 2 * (r ^ 2) ^ n = (δ * r ^ n) ^ 2 := by ring
    _ ≤ primeArchEndpointBernsteinTotalVariation n ^ 2 := hsq
    _ ≤ (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := hcard

/-- A positive exponential divided by the linear degree tends to positive infinity. -/
lemma tendsto_const_mul_pow_div_nat_add_one_atTop
    {ρ η : ℝ} (hρ : 1 < ρ) (hη : 0 < η) :
    Tendsto (fun n : ℕ => η * ρ ^ n / (n + 1 : ℝ)) atTop atTop := by
  have hpoly : Tendsto (fun n : ℕ => (n + 1 : ℝ) / ρ ^ n)
      atTop (nhds 0) := by
    have hn := tendsto_pow_const_div_const_pow_of_one_lt 1 hρ
    have hone : Tendsto (fun n : ℕ => 1 / ρ ^ n) atTop (nhds 0) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (inv_nonneg.mpr (lt_trans (by norm_num) hρ).le)
        (inv_lt_one_of_one_lt₀ hρ)
      simpa [div_eq_mul_inv, inv_pow] using hp
    simpa only [pow_one, Nat.cast_add, Nat.cast_one, add_div, zero_add] using hn.add hone
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < (n + 1 : ℝ) / ρ ^ n :=
    Eventually.of_forall fun n => div_pos (by positivity)
      (pow_pos (lt_trans (by norm_num) hρ) n)
  have hright : Tendsto (fun n : ℕ => (n + 1 : ℝ) / ρ ^ n)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpoly, hpos⟩
  have hinv := hright.inv_tendsto_nhdsGT_zero
  have hmul := hinv.atTop_mul_pos hη tendsto_const_nhds
  convert hmul using 1
  funext n
  change η * ρ ^ n / (n + 1 : ℝ) =
    (((n + 1 : ℝ) / ρ ^ n)⁻¹) * η
  rw [inv_div]
  ring

/-- **Purity divergence law.** Failure of RH forces the positive source-defined endpoint
Bernstein purity to tend to positive infinity, not merely to have exponential spikes. -/
theorem tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    Tendsto primeArchEndpointBernsteinPurity atTop atTop := by
  obtain ⟨ρ, η, hρ, hη, hlower⟩ :=
    exists_eventually_exponential_lower_envelope_primeArchEndpointBernsteinPurity_of_not_rh hRH
  have hbase := tendsto_const_mul_pow_div_nat_add_one_atTop hρ hη
  have hbound : ∀ᶠ n : ℕ in atTop,
      η * ρ ^ n / (n + 1 : ℝ) ≤ primeArchEndpointBernsteinPurity n := by
    filter_upwards [hlower] with n hn
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
      (by simpa only [mul_comm] using hn)
  exact tendsto_atTop_mono' atTop hbound hbase

/-- A sequence is cofinally bounded when one fixed bound is met arbitrarily far out. -/
def PrimeArchEndpointBernsteinPurityCofinallyBounded : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧ primeArchEndpointBernsteinPurity n ≤ C

/-- **Cofinal bounded-sampling criterion.** RH requires only one bounded cofinal sampling of the
positive endpoint purity; uniform control at every degree is unnecessary. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded :
    RiemannHypothesis ↔ PrimeArchEndpointBernsteinPurityCofinallyBounded := by
  constructor
  · intro hRH
    refine ⟨normalizedPrimeArchMoment 0 ^ 2, fun N => ⟨N, le_rfl, ?_⟩⟩
    exact primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH N
  · rintro ⟨C, hC⟩
    by_contra hRH
    have htend :=
      tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH
    obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually_gt_atTop C)
    obtain ⟨n, hnN, hnC⟩ := hC N
    exact (not_lt_of_ge hnC) (hN n hnN)

/-- The cofinal positive-purity condition is exactly the prime--polar critical absolute-abscissa
bound.  Thus a recurring finite purity ceiling discharges the remaining source inequality. -/
theorem primeArchEndpointBernsteinPurityCofinallyBounded_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    PrimeArchEndpointBernsteinPurityCofinallyBounded ↔
      LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) :=
  riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded.symm.trans
    (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one hL hN)


lemma bernsteinCoefficientPurity_le_mass_sq_of_hausdorffBernsteinNonnegative
    {a : ℕ → ℝ} (ha : HausdorffBernsteinNonnegative a) (n : ℕ) :
    bernsteinCoefficientPurity a n ≤ a 0 ^ 2 := by
  have hL1 : bernsteinCoefficientL1 a n = a 0 := by
    rw [bernsteinCoefficientL1]
    calc
      (∑ i ∈ Finset.range (n + 1), |bernsteinCoefficient a n i|) =
          ∑ i ∈ Finset.range (n + 1), bernsteinCoefficient a n i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_of_nonneg]
        exact ha n i
      _ = a 0 := sum_bernsteinCoefficient a n
  exact (bernsteinCoefficientPurity_le_l1_sq a n).trans_eq (by rw [hL1])

lemma bernsteinCoefficientPurity_le_two_mass_sq_add_two_squareDiscrepancy
    (m a : ℕ → ℝ) (N : ℕ) (ha : HausdorffBernsteinNonnegative a) :
    bernsteinCoefficientPurity m (N + 1) ≤
      2 * a 0 ^ 2 + 2 * bernsteinCoefficientSquareDiscrepancyAtDefectDegree m a N := by
  have hpoint (i : ℕ) :
      bernsteinCoefficient m (N + 1) i ^ 2 ≤
        2 * bernsteinCoefficient a (N + 1) i ^ 2 +
          2 * (bernsteinCoefficient m (N + 1) i -
            bernsteinCoefficient a (N + 1) i) ^ 2 := by
    nlinarith [sq_nonneg (bernsteinCoefficient m (N + 1) i -
      2 * bernsteinCoefficient a (N + 1) i)]
  rw [bernsteinCoefficientPurity,
    bernsteinCoefficientSquareDiscrepancyAtDefectDegree]
  calc
    (∑ i ∈ Finset.range (N + 1 + 1),
        bernsteinCoefficient m (N + 1) i ^ 2) ≤
      ∑ i ∈ Finset.range (N + 2),
        (2 * bernsteinCoefficient a (N + 1) i ^ 2 +
          2 * (bernsteinCoefficient m (N + 1) i -
            bernsteinCoefficient a (N + 1) i) ^ 2) := by
        rw [show N + 1 + 1 = N + 2 by omega]
        exact Finset.sum_le_sum fun i _ => hpoint i
    _ = 2 * bernsteinCoefficientPurity a (N + 1) +
        2 * ∑ i ∈ Finset.range (N + 2),
          (bernsteinCoefficient m (N + 1) i -
            bernsteinCoefficient a (N + 1) i) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [bernsteinCoefficientPurity]
    _ ≤ 2 * a 0 ^ 2 +
        2 * ∑ i ∈ Finset.range (N + 2),
          (bernsteinCoefficient m (N + 1) i -
            bernsteinCoefficient a (N + 1) i) ^ 2 := by
      gcongr
      exact bernsteinCoefficientPurity_le_mass_sq_of_hausdorffBernsteinNonnegative ha (N + 1)

theorem riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy_bounded
    (d : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (A E : ℝ)
    (hd : Tendsto d atTop atTop)
    (ha : ∀ j, HausdorffBernsteinNonnegative (a j))
    (hmass : ∀ j, (a j 0) ^ 2 ≤ A)
    (herr : ∀ j,
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (a j) (d j) ≤ E) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_primeArchEndpointBernsteinPurity_cofinallyBounded.mpr
  refine ⟨2 * A + 2 * E, fun N => ?_⟩
  obtain ⟨j, hj⟩ := eventually_atTop.1 ((tendsto_atTop.1 hd) N)
  refine ⟨d j + 1, (hj j le_rfl).trans (Nat.le_succ _), ?_⟩
  have hsource :=
    bernsteinCoefficientPurity_le_two_mass_sq_add_two_squareDiscrepancy
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment) (a j) (d j) (ha j)
  change primeArchEndpointBernsteinPurity (d j + 1) ≤ _ at hsource
  exact hsource.trans (by linarith [hmass j, herr j])

lemma xiThermalTruncation_zero_nonneg (M : ℕ) :
    0 ≤ xiThermalTruncation M 0 := by
  rw [xiThermalTruncation]
  exact Finset.sum_nonneg fun j hj =>
    mul_nonneg (xiThermalNode_pos _).le (pow_nonneg (xiThermalNode_pos _).le 0)

lemma xiThermalTruncation_zero_le_positiveMoment (M : ℕ) :
    xiThermalTruncation M 0 ≤ xiThermalPositiveMoment 0 := by
  have hsumm := (hasSum_xiThermalEnumeration_positiveMoment 0).summable
  have hle := hsumm.sum_le_tsum (Finset.range M)
    (fun j hj => pow_nonneg (xiThermalNode_pos _).le 1)
  rw [← (hasSum_xiThermalEnumeration_positiveMoment 0).tsum_eq]
  simpa only [xiThermalTruncation, pow_zero, mul_one, pow_one, zero_add] using hle

/-- Uniformly bounded Hilbert packet error against the explicit finite Xi thermal systems, at
cofinally large degrees, proves RH. No inverse-dimension error rate is required. -/
theorem riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_bounded
    (d M : ℕ → ℕ) (E : ℝ)
    (hd : Tendsto d atTop atTop)
    (herr : ∀ j,
      bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation (M j))) (d j) ≤ E) :
    RiemannHypothesis := by
  apply
    riemannHypothesis_of_cofinal_hausdorffBernsteinApproximation_squareDiscrepancy_bounded
      d
      (fun j => radiusNormalizedMoment primeArchEndpointHausdorffRadius
        (xiThermalTruncation (M j)))
      (xiThermalPositiveMoment 0 ^ 2) E hd
  · intro j
    exact hausdorffBernsteinNonnegative_radiusNormalized_xiThermalTruncation (M j)
  · intro j
    simp only [radiusNormalizedMoment, pow_zero, div_one]
    exact (sq_le_sq₀ (xiThermalTruncation_zero_nonneg (M j))
      (tsum_nonneg fun q => pow_nonneg (xiThermalNode_pos q).le 1)).2
      (xiThermalTruncation_zero_le_positiveMoment (M j))
  · exact herr

/-- Under RH, every fixed Bernstein coefficient of the explicit finite Xi thermal system
converges to the corresponding source coefficient. -/
theorem tendsto_bernsteinCoefficient_xiThermalTruncation_of_riemannHypothesis
    (hRH : RiemannHypothesis) (n i : ℕ) :
    Tendsto
      (fun M => bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation M)) n i)
      atTop
      (nhds (bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) n i)) := by
  let p := bernsteinPolynomial ℝ n i
  have hmoment (k : ℕ) : Tendsto
      (fun M => radiusNormalizedMoment primeArchEndpointHausdorffRadius
        (xiThermalTruncation M) k)
      atTop
      (nhds (radiusNormalizedMoment primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k)) := by
    have hk := (tendsto_pi_nhds.mp (tendsto_xiThermalTruncation_of_rh hRH)) k
    simpa only [radiusNormalizedMoment] using
      hk.div_const (primeArchEndpointHausdorffRadius ^ k)
  simp only [bernsteinCoefficient, HTGeometry.momentFunctional_eq_support_sum]
  exact tendsto_finsetSum p.support (fun k hk =>
    tendsto_const_nhds.mul (hmoment k))

/-- Under RH, the squared Bernstein packet discrepancy of every fixed degree tends to zero as
the explicit thermal cutoff grows. -/
theorem tendsto_bernsteinSquareDiscrepancy_xiThermalTruncation_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (N : ℕ) :
    Tendsto
      (fun M => bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment)
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          (xiThermalTruncation M)) N)
      atTop (nhds 0) := by
  rw [show (0 : ℝ) = ∑ _i ∈ Finset.range (N + 2), 0 by simp]
  apply tendsto_finsetSum
  intro i hi
  have hcoeff :=
    tendsto_bernsteinCoefficient_xiThermalTruncation_of_riemannHypothesis
      hRH (N + 1) i
  have hconst : Tendsto
      (fun _ : ℕ => bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (N + 1) i)
      atTop
      (nhds (bernsteinCoefficient
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (N + 1) i)) := tendsto_const_nhds
  have hdiff := hconst.sub hcoeff
  simpa only [bernsteinCoefficientSquareDiscrepancyAtDefectDegree,
    sub_self, pow_two, zero_mul] using hdiff.pow 2

/-- **Concrete finite-thermal RH law.** RH is equivalent to choosing one explicit finite Xi
thermal truncation at each Bernstein degree whose squared packet error is at most one. No common
cutoff, convergence rate, or inverse-dimension decay is required. -/
theorem riemannHypothesis_iff_exists_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one :
    RiemannHypothesis ↔
      ∃ M : ℕ → ℕ, ∀ N : ℕ,
        bernsteinCoefficientSquareDiscrepancyAtDefectDegree
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment)
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            (xiThermalTruncation (M N))) N ≤ 1 := by
  constructor
  · intro hRH
    have hex (N : ℕ) : ∃ M : ℕ,
        bernsteinCoefficientSquareDiscrepancyAtDefectDegree
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment)
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            (xiThermalTruncation M)) N ≤ 1 := by
      have htend :=
        tendsto_bernsteinSquareDiscrepancy_xiThermalTruncation_zero_of_riemannHypothesis
          hRH N
      have hev : ∀ᶠ M : ℕ in atTop,
          bernsteinCoefficientSquareDiscrepancyAtDefectDegree
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment)
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              (xiThermalTruncation M)) N < 1 :=
        (tendsto_order.1 htend).2 1 (by norm_num)
      obtain ⟨M, hM⟩ := hev.exists
      exact ⟨M, hM.le⟩
    choose M hM using hex
    exact ⟨M, hM⟩
  · rintro ⟨M, hM⟩
    exact
      riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_bounded
        id M 1 tendsto_id hM

/-- RH needs the finite-thermal Hilbert bound only on one cofinal degree schedule. Degrees outside
the schedule and the behavior of the cutoffs themselves are irrelevant. -/
theorem riemannHypothesis_iff_exists_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one :
    RiemannHypothesis ↔
      ∃ d M : ℕ → ℕ, Tendsto d atTop atTop ∧
        ∀ j : ℕ,
          bernsteinCoefficientSquareDiscrepancyAtDefectDegree
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment)
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              (xiThermalTruncation (M j))) (d j) ≤ 1 := by
  constructor
  · intro hRH
    obtain ⟨M, hM⟩ :=
      riemannHypothesis_iff_exists_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one.mp hRH
    exact ⟨id, M, tendsto_id, hM⟩
  · rintro ⟨d, M, hd, hM⟩
    exact
      riemannHypothesis_of_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_bounded
        d M 1 hd hM

/-- The remaining prime--polar absolute-abscissa inequality is exactly one cofinal constant-one
Hilbert approximation by the explicit finite Xi thermal systems. -/
theorem rectangularPrimePolarSource_negativeAbscissa_le_one_iff_exists_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal)) ↔
      ∃ d M : ℕ → ℕ, Tendsto d atTop atTop ∧
        ∀ j : ℕ,
          bernsteinCoefficientSquareDiscrepancyAtDefectDegree
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              normalizedPrimeArchMoment)
            (radiusNormalizedMoment primeArchEndpointHausdorffRadius
              (xiThermalTruncation (M j))) (d j) ≤ 1 :=
  (riemannHypothesis_iff_rectangularPrimePolarSource_negativeAbscissa_le_one
    hL hN).symm.trans
      riemannHypothesis_iff_exists_cofinal_xiThermalTruncation_bernsteinSquareDiscrepancy_le_one

/-- Under failure of RH, every bounded-mass Hausdorff-positive comparator family separates from
the source in Bernstein Hilbert distance. -/
theorem tendsto_bernsteinSquareDiscrepancy_from_boundedMass_positiveComparators_atTop_of_not_rh
    (hRH : ¬ RiemannHypothesis) (a : ℕ → ℕ → ℝ) (A : ℝ)
    (ha : ∀ N, HausdorffBernsteinNonnegative (a N))
    (hmass : ∀ N, (a N 0) ^ 2 ≤ A) :
    Tendsto
      (fun N => bernsteinCoefficientSquareDiscrepancyAtDefectDegree
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (a N) N)
      atTop atTop := by
  have hp := tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH
  have hpshift : Tendsto (fun N => primeArchEndpointBernsteinPurity (N + 1))
      atTop atTop := (tendsto_add_atTop_iff_nat 1).mpr hp
  have hbase : Tendsto (fun N => primeArchEndpointBernsteinPurity (N + 1) / 4)
      atTop atTop := hpshift.atTop_div_const (by norm_num)
  have hlarge := hpshift.eventually_ge_atTop (4 * A)
  have hbound : ∀ᶠ N : ℕ in atTop,
      primeArchEndpointBernsteinPurity (N + 1) / 4 ≤
        bernsteinCoefficientSquareDiscrepancyAtDefectDegree
          (radiusNormalizedMoment primeArchEndpointHausdorffRadius
            normalizedPrimeArchMoment) (a N) N := by
    filter_upwards [hlarge] with N hN
    have hsource :=
      bernsteinCoefficientPurity_le_two_mass_sq_add_two_squareDiscrepancy
        (radiusNormalizedMoment primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment) (a N) N (ha N)
    change primeArchEndpointBernsteinPurity (N + 1) ≤ _ at hsource
    linarith [hmass N]
  exact tendsto_atTop_mono' atTop hbound hbase

/-- RH is exactly the nondivergent phase of the positive endpoint purity. -/
theorem riemannHypothesis_iff_not_tendsto_primeArchEndpointBernsteinPurity_atTop :
    RiemannHypothesis ↔
      ¬ Tendsto primeArchEndpointBernsteinPurity atTop atTop := by
  constructor
  · intro hRH htend
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (htend.eventually_gt_atTop (normalizedPrimeArchMoment 0 ^ 2))
    have hupper :=
      primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH N
    exact (not_lt_of_ge hupper) (hN N le_rfl)
  · intro hnot
    by_contra hRH
    exact hnot
      (tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH)

/-- **Endpoint purity dichotomy law.** The source scalar has only two asymptotic phases: under RH
it stays below the exact mass-squared wall; under failure of RH it tends to positive infinity. -/
theorem primeArchEndpointBernsteinPurity_dichotomy :
    (RiemannHypothesis ∧
      ∀ n : ℕ,
        primeArchEndpointBernsteinPurity n ≤ normalizedPrimeArchMoment 0 ^ 2) ∨
    (¬ RiemannHypothesis ∧
      Tendsto primeArchEndpointBernsteinPurity atTop atTop) := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl ⟨hRH,
      primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH⟩
  · exact Or.inr ⟨hRH,
      tendsto_primeArchEndpointBernsteinPurity_atTop_of_not_riemannHypothesis hRH⟩

end

end RHTower
