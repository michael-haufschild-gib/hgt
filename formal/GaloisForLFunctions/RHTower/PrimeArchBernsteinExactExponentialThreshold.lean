import GaloisForLFunctions.RHTower.PrimeArchBernsteinPurityDivergence
import GaloisForLFunctions.RHTower.PrimeArchBernsteinSectorConfinedPhase

/-!
# Exact exponential threshold of the endpoint Bernstein purity

Failure of RH gives an attained maximal affine Bernstein amplitude.  The dominant-mode theorem
supplies a matching lower envelope, while the complete divisor envelope supplies the upper bound.
Together they identify the square of that maximal amplitude as the exact exponential threshold of
the positive endpoint purity.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- An exact exponential exponent for a real sequence: normalization above `E` vanishes, whereas
every positive normalization below `E` diverges. -/
def ExactExponentialExponentAtNatInfinity (f : ℕ → ℝ) (E : ℝ) : Prop :=
  0 < E ∧
    (∀ r : ℝ, E < r →
      Tendsto (fun n : ℕ => f n / r ^ n) atTop (nhds 0)) ∧
    (∀ r : ℝ, 0 < r → r < E →
      Tendsto (fun n : ℕ => f n / r ^ n) atTop atTop)

/-- The exact exponential exponent specialized to the endpoint purity. -/
def PrimeArchEndpointBernsteinExactExponentialExponent (E : ℝ) : Prop :=
  ExactExponentialExponentAtNatInfinity primeArchEndpointBernsteinPurity E

/-- A linear polynomial factor times a strict geometric contraction tends to zero. -/
lemma tendsto_natCast_add_one_mul_pow_nhds_zero
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) * q ^ n) atTop (nhds 0) := by
  rcases hq0.eq_or_lt with hq | hq
  · rw [← hq]
    refine (tendsto_congr' (show ∀ᶠ n : ℕ in atTop,
      (n + 1 : ℝ) * 0 ^ n = 0 by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp [Nat.ne_of_gt hn])).mpr tendsto_const_nhds
  · let ρ : ℝ := 1 / q
    have hρ : 1 < ρ := by
      dsimp only [ρ]
      exact (one_lt_div hq).2 hq1
    have hn := tendsto_pow_const_div_const_pow_of_one_lt 1 hρ
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1
    have hadd := hn.add hpow
    simpa only [ρ, one_div, inv_pow, div_inv_eq_mul, pow_one, zero_add,
      Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hadd

/-- Multiplication by the linear degree factor does not alter the exact exponential exponent of
a nonnegative sequence. -/
theorem exactExponentialExponentAtNatInfinity_natCast_add_one_mul_iff
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (E : ℝ) :
    ExactExponentialExponentAtNatInfinity (fun n => (n + 1 : ℝ) * f n) E ↔
      ExactExponentialExponentAtNatInfinity f E := by
  constructor
  · rintro ⟨hE, habove, hbelow⟩
    refine ⟨hE, ?_, ?_⟩
    · intro r hEr
      have hr : 0 < r := hE.trans hEr
      have hscaled := habove r hEr
      apply squeeze_zero
        (fun n => div_nonneg (hf n) (pow_nonneg hr.le n))
        (fun n => ?_) hscaled
      exact div_le_div_of_nonneg_right
        (calc
          f n = 1 * f n := by ring
          _ ≤ (n + 1 : ℝ) * f n :=
            mul_le_mul_of_nonneg_right
              (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (hf n))
        (pow_nonneg hr.le n)
    · intro r hr hrE
      set s : ℝ := (r + E) / 2 with hsdef
      have hrs : r < s := by rw [hsdef]; linarith
      have hsE : s < E := by rw [hsdef]; linarith
      have hs : 0 < s := hr.trans hrs
      have hscaled := hbelow s hs hsE
      have hlarge : ∀ᶠ n : ℕ in atTop,
          1 ≤ ((n + 1 : ℝ) * f n) / s ^ n :=
        hscaled.eventually_ge_atTop 1
      have hratio : 1 < s / r := (one_lt_div hr).2 hrs
      have hgeom := tendsto_const_mul_pow_div_nat_add_one_atTop hratio (by norm_num : (0 : ℝ) < 1)
      have hbound : ∀ᶠ n : ℕ in atTop,
          (s / r) ^ n / (n + 1 : ℝ) ≤ f n / r ^ n := by
        filter_upwards [hlarge] with n hn
        have hsPow : 0 < s ^ n := pow_pos hs n
        have hrPow : 0 < r ^ n := pow_pos hr n
        have hsource : s ^ n ≤ (n + 1 : ℝ) * f n :=
          by simpa only [one_mul] using (le_div_iff₀ hsPow).mp hn
        have hden : 0 ≤ (n + 1 : ℝ) * r ^ n := by positivity
        calc
          (s / r) ^ n / (n + 1 : ℝ) =
              s ^ n / ((n + 1 : ℝ) * r ^ n) := by
            rw [div_pow]
            field_simp [hr.ne']
          _ ≤ ((n + 1 : ℝ) * f n) / ((n + 1 : ℝ) * r ^ n) :=
            div_le_div_of_nonneg_right hsource hden
          _ = f n / r ^ n := by
            field_simp [hr.ne']
      exact tendsto_atTop_mono' atTop hbound (by simpa using hgeom)
  · rintro ⟨hE, habove, hbelow⟩
    refine ⟨hE, ?_, ?_⟩
    · intro r hEr
      set s : ℝ := (E + r) / 2 with hsdef
      have hEs : E < s := by rw [hsdef]; linarith
      have hsr : s < r := by rw [hsdef]; linarith
      have hs : 0 < s := hE.trans hEs
      have hr : 0 < r := hs.trans hsr
      have hzero := habove s hEs
      have hratio0 : 0 ≤ s / r := div_nonneg hs.le hr.le
      have hratio1 : s / r < 1 := (div_lt_one hr).2 hsr
      have hgeom := tendsto_natCast_add_one_mul_pow_nhds_zero hratio0 hratio1
      have hprod := hzero.mul hgeom
      have heq (n : ℕ) :
          f n / s ^ n * ((n + 1 : ℝ) * (s / r) ^ n) =
            ((n + 1 : ℝ) * f n) / r ^ n := by
        rw [div_pow]
        field_simp [hs.ne', hr.ne']
        have hratioCancel : (s / r) ^ n * r ^ n = s ^ n := by
          rw [div_pow]
          field_simp [hr.ne']
        have hsDouble : 2 ^ n * s ^ n = (E + r) ^ n := by
          rw [← mul_pow, hsdef]
          congr 1
          ring
        calc
          f n * 2 ^ n * (s / r) ^ n * r ^ n =
              f n * 2 ^ n * ((s / r) ^ n * r ^ n) := by ring
          _ = f n * (2 ^ n * s ^ n) := by rw [hratioCancel]; ring
          _ = f n * (E + r) ^ n := by rw [hsDouble]
      exact Filter.Tendsto.congr'
        (Eventually.of_forall heq) (by simpa using hprod)
    · intro r hr hrE
      have hdiv := hbelow r hr hrE
      have hbound : ∀ n : ℕ,
          f n / r ^ n ≤ ((n + 1 : ℝ) * f n) / r ^ n := by
        intro n
        exact div_le_div_of_nonneg_right
          (calc
            f n = 1 * f n := by ring
            _ ≤ (n + 1 : ℝ) * f n :=
              mul_le_mul_of_nonneg_right
                (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (hf n))
          (pow_nonneg hr.le n)
      exact tendsto_atTop_mono' atTop (Eventually.of_forall hbound) hdiv

/-- A uniform atom-amplitude ceiling gives the corresponding exact-base purity envelope. -/
theorem primeArchEndpointBernsteinPurity_le_of_atomAmplitudeBase
    (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B)
    (n : ℕ) :
    primeArchEndpointBernsteinPurity n ≤
      (xiReciprocalSquareAbsoluteMass * B ^ n) ^ 2 := by
  have htv := primeArchEndpointBernsteinTotalVariation_le_of_atomAmplitudeBase B hmax n
  exact (bernsteinCoefficientPurity_le_l1_sq _ _).trans
    ((sq_le_sq₀
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg xiReciprocalSquareAbsoluteMass_nonneg (pow_nonneg hB n))).2 htv)

/-- Above the square of any uniform atom-amplitude ceiling, the normalized purity vanishes. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_of_atomAmplitudeBase_sq_lt
    {B r : ℝ} (hB : 0 ≤ B)
    (hmax : ∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B)
    (hr : B ^ 2 < r) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop (nhds 0) := by
  have hrpos : 0 < r := lt_of_le_of_lt (sq_nonneg B) hr
  let q : ℝ := B ^ 2 / r
  have hq0 : 0 ≤ q := div_nonneg (sq_nonneg B) hrpos.le
  have hq1 : q < 1 := (div_lt_one hrpos).2 hr
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hupper : Tendsto
      (fun n : ℕ => xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hpow
  apply squeeze_zero
    (fun n => div_nonneg (bernsteinCoefficientPurity_nonneg _ n)
      (pow_nonneg hrpos.le n))
    (fun n => ?_) hupper
  calc
    primeArchEndpointBernsteinPurity n / r ^ n ≤
        (xiReciprocalSquareAbsoluteMass * B ^ n) ^ 2 / r ^ n :=
      div_le_div_of_nonneg_right
        (primeArchEndpointBernsteinPurity_le_of_atomAmplitudeBase B hB hmax n)
        (pow_nonneg hrpos.le n)
    _ = xiReciprocalSquareAbsoluteMass ^ 2 * q ^ n := by
      dsimp only [q]
      rw [div_pow]
      ring

/-- An eventual lower envelope at amplitude `B` forces divergence after normalization by every
strictly smaller positive squared base. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_atTop_of_lowerEnvelope
    {B η r : ℝ} (hη : 0 < η) (hr : 0 < r) (hthreshold : r < B ^ 2)
    (hlower : ∀ᶠ n : ℕ in atTop,
      η * (B ^ 2) ^ n ≤
        (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop atTop := by
  have hρ : 1 < B ^ 2 / r := (one_lt_div hr).2 hthreshold
  have hbase := tendsto_const_mul_pow_div_nat_add_one_atTop hρ hη
  have hbound : ∀ᶠ n : ℕ in atTop,
      η * (B ^ 2 / r) ^ n / (n + 1 : ℝ) ≤
        primeArchEndpointBernsteinPurity n / r ^ n := by
    filter_upwards [hlower] with n hn
    have hden : 0 ≤ (n + 1 : ℝ) * r ^ n := by positivity
    calc
      η * (B ^ 2 / r) ^ n / (n + 1 : ℝ) =
          (η * (B ^ 2) ^ n) / ((n + 1 : ℝ) * r ^ n) := by
        rw [div_pow]
        field_simp [hr.ne']
      _ ≤ ((n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) /
          ((n + 1 : ℝ) * r ^ n) := div_le_div_of_nonneg_right hn hden
      _ = primeArchEndpointBernsteinPurity n / r ^ n := by
        field_simp [hr.ne']
  exact tendsto_atTop_mono' atTop hbound hbase

/-- The conserved positive source mass forces divergence below the critical base one. -/
theorem tendsto_primeArchEndpointBernsteinPurity_div_pow_atTop_of_lt_one
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
      atTop atTop := by
  let C : ℝ := normalizedPrimeArchMoment 0 ^ 2
  have hC : 0 < C := by
    dsimp only [C]
    exact sq_pos_of_pos normalizedPrimeArchMoment_zero_pos
  have hρ : 1 < 1 / r := (one_lt_div hr).2 hr1
  have hbase := tendsto_const_mul_pow_div_nat_add_one_atTop hρ hC
  have hbound : ∀ n : ℕ,
      C * (1 / r) ^ n / (n + 1 : ℝ) ≤
        primeArchEndpointBernsteinPurity n / r ^ n := by
    intro n
    have hfloor := mass_sq_le_card_mul_primeArchEndpointBernsteinPurity n
    have hden : 0 ≤ (n + 1 : ℝ) * r ^ n := by positivity
    calc
      C * (1 / r) ^ n / (n + 1 : ℝ) =
          C / ((n + 1 : ℝ) * r ^ n) := by
        dsimp only [C]
        rw [one_div, inv_pow]
        field_simp [hr.ne']
      _ ≤ ((n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) /
          ((n + 1 : ℝ) * r ^ n) := div_le_div_of_nonneg_right hfloor hden
      _ = primeArchEndpointBernsteinPurity n / r ^ n := by
        field_simp [hr.ne']
  exact tendsto_atTop_mono' atTop (Eventually.of_forall hbound) hbase

/-- Under RH, one is the exact exponential exponent of the endpoint purity. -/
theorem primeArchEndpointBernsteinExactExponentialExponent_one_of_rh
    (hRH : RiemannHypothesis) :
    PrimeArchEndpointBernsteinExactExponentialExponent 1 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · exact riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.mp hRH
  · intro r hr hr1
    exact tendsto_primeArchEndpointBernsteinPurity_div_pow_atTop_of_lt_one hr hr1

/-- The critical value one of the exact exponent is equivalent to RH. -/
theorem riemannHypothesis_iff_primeArchEndpointBernsteinExactExponentialExponent_one :
    RiemannHypothesis ↔ PrimeArchEndpointBernsteinExactExponentialExponent 1 := by
  constructor
  · exact primeArchEndpointBernsteinExactExponentialExponent_one_of_rh
  · intro hE
    exact riemannHypothesis_iff_primeArchEndpointBernsteinPurity_subexponential.mpr hE.2.1

/-- An exact exponential exponent is unique. -/
theorem primeArchEndpointBernsteinExactExponentialExponent_unique
    {E F : ℝ}
    (hE : PrimeArchEndpointBernsteinExactExponentialExponent E)
    (hF : PrimeArchEndpointBernsteinExactExponentialExponent F) :
    E = F := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hEF | hFE
  · let r : ℝ := (E + F) / 2
    have hEr : E < r := by dsimp only [r]; linarith
    have hrF : r < F := by dsimp only [r]; linarith
    have hr0 : 0 < r := hE.1.trans hEr
    have hzero := hE.2.1 r hEr
    have hinf := hF.2.2 r hr0 hrF
    have hsmall : ∀ᶠ n : ℕ in atTop,
        primeArchEndpointBernsteinPurity n / r ^ n < 1 :=
      (tendsto_order.1 hzero).2 1 (by norm_num)
    have hlarge : ∀ᶠ n : ℕ in atTop,
        1 < primeArchEndpointBernsteinPurity n / r ^ n :=
      hinf.eventually_gt_atTop 1
    obtain ⟨n, hnsmall, hnlarge⟩ := (hsmall.and hlarge).exists
    linarith
  · let r : ℝ := (F + E) / 2
    have hFr : F < r := by dsimp only [r]; linarith
    have hrE : r < E := by dsimp only [r]; linarith
    have hr0 : 0 < r := hF.1.trans hFr
    have hzero := hF.2.1 r hFr
    have hinf := hE.2.2 r hr0 hrE
    have hsmall : ∀ᶠ n : ℕ in atTop,
        primeArchEndpointBernsteinPurity n / r ^ n < 1 :=
      (tendsto_order.1 hzero).2 1 (by norm_num)
    have hlarge : ∀ᶠ n : ℕ in atTop,
        1 < primeArchEndpointBernsteinPurity n / r ^ n :=
      hinf.eventually_gt_atTop 1
    obtain ⟨n, hnsmall, hnlarge⟩ := (hsmall.and hlarge).exists
    linarith

/-- **Exact false-RH exponential-threshold law.**  Failure of RH produces an attained maximal
atom amplitude `B` strictly inside the source sector.  The purity has exact exponential threshold
`B^2`: every larger normalization vanishes, while every smaller positive normalization diverges. -/
theorem exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ B η : ℝ,
      1 < B ∧ B < xiSectorConfinedBernsteinAmplitudeBase ∧ 0 < η ∧
      (∃ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B) ∧
      (∀ n : ℕ,
        primeArchEndpointBernsteinPurity n ≤
          (xiReciprocalSquareAbsoluteMass * B ^ n) ^ 2) ∧
      (∀ᶠ n : ℕ in atTop,
        η * (B ^ 2) ^ n ≤
          (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n) ∧
      (∀ r : ℝ, B ^ 2 < r →
        Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop (nhds 0)) ∧
      (∀ r : ℝ, 0 < r → r < B ^ 2 →
        Tendsto (fun n : ℕ => primeArchEndpointBernsteinPurity n / r ^ n)
          atTop atTop) := by
  obtain ⟨w, B, δ, hw, hB, hδ, hmax, hattained, hevent⟩ :=
    exists_maximalAmplitude_unit_xiCentralBernsteinPencil_eventually_exponential_of_not_rh hRH
  obtain ⟨qmax, hqmax⟩ := hattained
  have hBsector : B < xiSectorConfinedBernsteinAmplitudeBase := by
    rw [← hqmax]
    exact xiEndpointBernsteinAtomAmplitudeBase_lt_sectorConfined qmax
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  let η : ℝ := δ ^ 2
  have hη : 0 < η := by
    dsimp only [η]
    exact sq_pos_of_pos hδ
  have hlower : ∀ᶠ n : ℕ in atTop,
      η * (B ^ 2) ^ n ≤
        (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := by
    filter_upwards [hevent] with n hn
    have hBpow : 0 < B ^ n := pow_pos hBpos n
    have hn' : δ ≤
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ / B ^ n := by
      simpa only [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hBpos] using hn
    have hpencil : δ * B ^ n ≤
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ :=
      (le_div_iff₀ hBpow).mp hn'
    have htransform :
        ‖xiCentralBernsteinPencil primeArchEndpointHausdorffRadius n w‖ ≤
          primeArchEndpointBernsteinTotalVariation n := by
      rw [← bernsteinCoefficientTransform_source_eq_xiCentralBernsteinPencil]
      exact norm_bernsteinCoefficientTransform_le_l1 _ _ hw.le
    have htvnonneg : 0 ≤ primeArchEndpointBernsteinTotalVariation n := by
      rw [primeArchEndpointBernsteinTotalVariation, bernsteinCoefficientL1]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsq :
        (δ * B ^ n) ^ 2 ≤ primeArchEndpointBernsteinTotalVariation n ^ 2 := by
      exact (sq_le_sq₀
        (mul_nonneg hδ.le (pow_nonneg hBpos.le n)) htvnonneg).2
        (hpencil.trans htransform)
    have hcard := bernsteinCoefficientL1_sq_le_card_mul_purity
      (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment) n
    change primeArchEndpointBernsteinTotalVariation n ^ 2 ≤
      (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n at hcard
    calc
      η * (B ^ 2) ^ n = (δ * B ^ n) ^ 2 := by
        dsimp only [η]
        ring
      _ ≤ primeArchEndpointBernsteinTotalVariation n ^ 2 := hsq
      _ ≤ (n + 1 : ℝ) * primeArchEndpointBernsteinPurity n := hcard
  refine ⟨B, η, hB, hBsector, hη, ⟨qmax, hqmax⟩, hmax,
    fun n => primeArchEndpointBernsteinPurity_le_of_atomAmplitudeBase B hBpos.le hmax n,
    hlower, ?_, ?_⟩
  · intro r hr
    exact tendsto_primeArchEndpointBernsteinPurity_div_pow_of_atomAmplitudeBase_sq_lt
      hBpos.le hmax hr
  · intro r hr hrB
    exact tendsto_primeArchEndpointBernsteinPurity_div_pow_atTop_of_lowerEnvelope
      hη hr hrB hlower

/-- A false-phase threshold is source-attained when it is the square of a genuine maximal atom
amplitude, rather than an external normalization parameter. -/
def PrimeArchEndpointBernsteinAttainedExactThreshold (B : ℝ) : Prop :=
  1 < B ∧ B < xiSectorConfinedBernsteinAmplitudeBase ∧
    (∃ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
    (∀ q : XiZeroCopy, xiEndpointBernsteinAtomAmplitudeBase q ≤ B) ∧
    PrimeArchEndpointBernsteinExactExponentialExponent (B ^ 2)

/-- False RH has a source-attained exact threshold inside the narrow sector. -/
theorem exists_primeArchEndpointBernsteinAttainedExactThreshold_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ B : ℝ, PrimeArchEndpointBernsteinAttainedExactThreshold B := by
  obtain ⟨B, η, hB, hBsector, hη, hattained, hmax, hupper,
      hlower, habove, hbelow⟩ :=
    exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh hRH
  exact ⟨B, hB, hBsector, hattained, hmax,
    ⟨sq_pos_of_pos (lt_trans zero_lt_one hB), habove, hbelow⟩⟩

/-- **Unique critical-exponent theorem.**  The endpoint purity has a unique exact exponential
exponent in the narrow universal chamber.  Its critical value is one exactly under RH; under
failure of RH the preceding theorem identifies it as the square of an attained maximal atom
amplitude. -/
theorem existsUnique_primeArchEndpointBernsteinExactExponentialExponent :
    ∃! E : ℝ,
      1 ≤ E ∧
      E < xiSectorConfinedBernsteinAmplitudeBase ^ 2 ∧
      PrimeArchEndpointBernsteinExactExponentialExponent E ∧
      (RiemannHypothesis ↔ E = 1) := by
  by_cases hRH : RiemannHypothesis
  · have hE := primeArchEndpointBernsteinExactExponentialExponent_one_of_rh hRH
    refine ⟨1, ⟨le_rfl, ?_, hE, ⟨fun _ => rfl, fun _ => hRH⟩⟩, ?_⟩
    · nlinarith [one_lt_xiSectorConfinedBernsteinAmplitudeBase]
    · intro F hF
      exact primeArchEndpointBernsteinExactExponentialExponent_unique hF.2.2.1 hE
  · obtain ⟨B, η, hB, hBsector, hη, hattained, hmax, hupper,
        hlower, habove, hbelow⟩ :=
      exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh hRH
    have hBpos : 0 < B := lt_trans zero_lt_one hB
    have hSpos : 0 < xiSectorConfinedBernsteinAmplitudeBase :=
      lt_trans zero_lt_one one_lt_xiSectorConfinedBernsteinAmplitudeBase
    have hBsq : 1 < B ^ 2 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hB)]
    have hBsquareSector :
        B ^ 2 < xiSectorConfinedBernsteinAmplitudeBase ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hBsector) (add_pos hSpos hBpos)]
    have hE : PrimeArchEndpointBernsteinExactExponentialExponent (B ^ 2) :=
      ⟨sq_pos_of_pos hBpos, habove, hbelow⟩
    refine ⟨B ^ 2, ⟨hBsq.le, hBsquareSector, hE, ?_⟩, ?_⟩
    · exact ⟨fun h => (hRH h).elim, fun heq => ((ne_of_gt hBsq) heq).elim⟩
    · intro F hF
      exact primeArchEndpointBernsteinExactExponentialExponent_unique hF.2.2.1 hE

end

end RHTower
