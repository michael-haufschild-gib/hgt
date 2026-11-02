import GaloisForLFunctions.RenormalizedIntersectionTheory.TheZeroDensitySpectralTailIsRelative
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheFixedScaleDefectIsBounded

/-!
# Conductor comparison at the zero-density endpoint

The signed harmonic primitive supplies its own normalization. Relative rough
tails and bounded fixed-scale defects approximate the infinite prime flip by
finite flips in the excited energy norm, without a rate of prime-density decay.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

open GaloisForLFunctions.ArithmeticCountingPositivity
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
open GaloisForLFunctions.ArithmeticElectrostatics (atomicWeilForm)

local notation "γ" => Real.eulerMascheroniConstant

private theorem unnormalized_fixedScaleDefect_le (P : Set ℕ) (T N : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hH : 0 < gaugeHarmonicSum (fun _ => 1) N)
    (hbound : ∑ a ∈ smoothSet T N,
      (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        (harmonicCorrelation (primeSetFlip P) N / δ) * roughHarmonic T (N / a)) ^ (2 : ℕ) /
          (a * roughHarmonic T (N / a)) ≤
      ε * gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) / gaugeHarmonicSum (fun _ => 1) N) :
    ∑ a ∈ smoothSet T N,
      (δ * gaugeHarmonicSum (fun _ => 1) N *
          gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        gaugeHarmonicSum (primeSetFlip P) N * roughHarmonic T (N / a)) ^ (2 : ℕ) /
          (a * roughHarmonic T (N / a)) ≤
      ε * δ ^ (2 : ℕ) * gaugeHarmonicSum (fun _ => 1) N *
        gaugeHarmonicSum (primeSetFlip P) N ^ (2 : ℕ) := by
  let H := gaugeHarmonicSum (fun _ => 1) N
  let S := gaugeHarmonicSum (primeSetFlip P) N
  have hH0 : H ≠ 0 := hH.ne'
  have hscale (a : ℕ) : δ * H * gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
      S * roughHarmonic T (N / a) = (δ * H) *
      (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
        (harmonicCorrelation (primeSetFlip P) N / δ) * roughHarmonic T (N / a)) := by
    change δ * H * _ - S * _ = δ * H * (_ - (S / H / δ) * _)
    field_simp [hδ.ne', hH0]
  calc
    _ = (δ * H) ^ (2 : ℕ) * ∑ a ∈ smoothSet T N,
        (gaugeHarmonicSum (roughGauge T (primeSetFlip P)) (N / a) -
          (harmonicCorrelation (primeSetFlip P) N / δ) * roughHarmonic T (N / a)) ^ (2 : ℕ) /
            (a * roughHarmonic T (N / a)) := by
      rw [mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [hscale a, mul_pow]
      ring
    _ ≤ (δ * H) ^ (2 : ℕ) * (ε * S ^ (2 : ℕ) / H) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = _ := by change _ = ε * δ ^ (2 : ℕ) * H * S ^ (2 : ℕ); field_simp [hH0]

/-- Every zero-density prime flip is, in excited energy norm, its harmonic
normalization times a sufficiently large finite flip, with arbitrarily small relative error. -/
theorem exists_scale_zeroDensity_inner_sub_le (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {s t : ℝ} (hs : 0 < s) (hst : s < t) {θ : ℝ} (hθ : 0 < θ) (T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ 3 ≤ T ∧ ∀ᶠ N : ℕ in atTop,
      0 < harmonicCorrelation (primeSetFlip P) N ∧
      ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
        ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
          |⟪w, primeSetHorizonVector P N⟫ - harmonicCorrelation (primeSetFlip P) N /
              finiteFlipHarmonicDensity (primeSetCutoff P (T - 1)) *
                ⟪w, finiteFlipHorizonVector (primeSetCutoff P (T - 1)) N⟫| ≤
            harmonicCorrelation (primeSetFlip P) N * θ *
              Real.sqrt (primeEnergy N w - s * ‖w‖ ^ (2 : ℕ)) := by
  have hts : 0 < t - s := sub_pos.mpr hst
  let CD := 2 + (2 * s + 1) / (t - s)
  have hCD : 0 ≤ CD := by dsimp only [CD]; positivity
  obtain ⟨K₁, K₂, hK₁, hK₂, htail⟩ := exists_eventually_relative_spectralTail_bound P hP
  have hTlim : Tendsto (fun T : ℕ => Real.log T ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hsmall : 0 < (θ / 8) / (K₁ * Real.sqrt CD + 1) := by positivity
  obtain ⟨T, hTlarge, hTsmall⟩ := ((eventually_ge_atTop (max 3 T₀)).and
    (hTlim.eventually (ge_mem_nhds hsmall))).exists
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hTlarge
  have hT1 : 1 ≤ T := by omega
  let LT := Real.log T ^ (-(1 / 4 : ℝ))
  have hLT : 0 ≤ LT := Real.rpow_nonneg (Real.log_natCast_nonneg T) _
  have hTcost : 2 * K₁ * LT * Real.sqrt CD ≤ θ / 4 := by
    have hpay := (le_div_iff₀ (show 0 < K₁ * Real.sqrt CD + 1 by positivity)).mp hTsmall
    have hbase := mul_le_mul_of_nonneg_right
      (show K₁ * Real.sqrt CD ≤ K₁ * Real.sqrt CD + 1 by linarith) hLT
    nlinarith only [hpay, hbase]
  refine ⟨T, (le_max_right _ _).trans hTlarge, hT3, ?_⟩
  let δ := finiteFlipHarmonicDensity (primeSetCutoff P (T - 1))
  have hδ : 0 < δ := finiteFlipHarmonicDensity_pos (primeSetCutoff_prime' P _)
  have hδeq : flipDensityBelow (primeSetFlip P) T = δ := flipDensityBelow_eq P hT1
  have hdef := eventually_zeroDensity_fixedScaleDefect_le P hP T
    (ε := (θ / 4) ^ (2 : ℕ) * (t - s)) (by positivity)
  have hgrowth := (tendsto_sparse_signedMean_div_log_rpow_atTop P hP
    (show (1 / 2 : ℝ) < 1 by norm_num)).eventually
      (eventually_ge_atTop (8 * K₂ * Real.sqrt CD / θ + 1))
  obtain ⟨N₄, h4⟩ := eventually_poleDefect_le_primeEnergy
  filter_upwards [htail, hdef, hgrowth, eventually_ge_atTop (max T N₄)]
    with N htailN hdefN hbig hlarge
  have hTN : T ≤ N := (le_max_left _ _).trans hlarge
  have hN4 : N₄ ≤ N := (le_max_right _ _).trans hlarge
  have hN3 : 3 ≤ N := hT3.trans hTN
  let L := Real.log N
  let H := gaugeHarmonicSum (fun _ => 1) N
  let S := gaugeHarmonicSum (primeSetFlip P) N
  let cN := harmonicCorrelation (primeSetFlip P) N
  let A := K₁ * S / L
  have hL1 : 1 ≤ L := one_le_log_of_three_le hN3
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hH : 0 < H := gaugeHarmonicSum_one_pos (by omega)
  have hHupper : H ≤ 2 * L := by
    have h := (abs_le.mp (abs_harmonic_sub_log_le N)).2
    linarith only [h, hL1]
  have hhalf : 0 < L ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hratio1 : 1 ≤ S / L ^ (1 / 2 : ℝ) := by
    have h0 : 0 ≤ 8 * K₂ * Real.sqrt CD / θ := by positivity
    linarith only [hbig, h0]
  have hS : 0 < S := by
    have h := (le_div_iff₀ hhalf).mp hratio1
    linarith only [h, hhalf]
  have hc : 0 < cN := div_pos hS hH
  refine ⟨hc, fun i₀ hg w hw => ?_⟩
  have hhalf_sq : (L ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have hSratio : (S / L) * L ^ (1 / 2 : ℝ) = S / L ^ (1 / 2 : ℝ) := by
    field_simp [hL.ne', hhalf.ne']
    nlinarith only [hhalf_sq]
  have hRpow : (S ^ (2 : ℕ) / L) ^ (1 / 2 : ℝ) = S / L ^ (1 / 2 : ℝ) := by
    rw [Real.div_rpow (sq_nonneg S) hL.le, ← Real.rpow_natCast, ← Real.rpow_mul hS.le]
    norm_num
  have hSc : S / L ≤ 2 * cN := by
    change S / L ≤ 2 * (S / H)
    rw [show 2 * (S / H) = (2 * S) / H by ring, div_le_div_iff₀ hL hH]
    nlinarith only [mul_le_mul_of_nonneg_left hHupper hS.le]
  have hTch : A * LT * Real.sqrt CD ≤ θ / 4 * cN := by
    have h1 := mul_le_mul_of_nonneg_left hSc
      (show 0 ≤ K₁ * LT * Real.sqrt CD by positivity)
    have h2 := mul_le_mul_of_nonneg_right hTcost hc.le
    calc
      A * LT * Real.sqrt CD = (K₁ * LT * Real.sqrt CD) * (S / L) := by
        dsimp only [A]
        ring
      _ ≤ (K₁ * LT * Real.sqrt CD) * (2 * cN) := h1
      _ = 2 * K₁ * LT * Real.sqrt CD * cN := by ring
      _ ≤ _ := h2
  have hKpay : K₂ * Real.sqrt CD ≤ θ / 4 * cN * L ^ (1 / 2 : ℝ) := by
    have hsmall : 8 * K₂ * Real.sqrt CD / θ ≤ S / L ^ (1 / 2 : ℝ) := by
      linarith only [hbig]
    have h1 := (div_le_iff₀ hθ).mp hsmall
    have h2 := mul_le_mul_of_nonneg_right hSc hhalf.le
    rw [hSratio] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hθ.le
    nlinarith only [h1, h3]
  have hrawtail := htailN T hT3 hTN w
  have hms : |⟪w, gaugeVector N (primeSetFlip P) -
      (smoothFibreSpace T N).starProjection (gaugeVector N (primeSetFlip P))⟫| ≤
      (A * L ^ (1 / 2 : ℝ) * LT + K₂) * Real.sqrt (poleDefect N (horizonExtend w)) := by
    refine hrawtail.trans_eq ?_
    change (K₁ * (S ^ (2 : ℕ) / L) ^ (1 / 2 : ℝ) * LT + K₂) * _ = _
    rw [hRpow, ← hSratio]
    dsimp only [A]
    ring
  have hD : poleDefect N (horizonExtend w) ≤ CD * (primeEnergy N w - s * ‖w‖ ^ (2 : ℕ)) := by
    have h := h4 N hN4 w
    have hcoer := primeEnergy_sub_ge_of_perp (s := s) hg hw
    have hnorm : (2 * s + 1) * ‖w‖ ^ (2 : ℕ) ≤
        (2 * s + 1) / (t - s) * (primeEnergy N w - s * ‖w‖ ^ (2 : ℕ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hts]
      have hm := mul_le_mul_of_nonneg_left hcoer (show 0 ≤ 2 * s + 1 by positivity)
      nlinarith only [hm]
    dsimp only [CD]
    nlinarith only [h, hnorm]
  rw [hδeq] at hdefN
  have hdefOld := unnormalized_fixedScaleDefect_le P T N hδ hH hdefN
  exact abs_inner_primeSetHorizonVector_sub_le P hT1 (κ := 0) (K₁ := A) (K₂ := K₂)
    (LT := LT) (c'' := cN) hst hg hw hθ.le hc.le hCD hL1 hdefOld
    (by simpa only [mul_zero, sub_zero] using hms) hD
    (by dsimp only [A]; positivity) hTch
    (by simpa only [mul_zero, sub_zero] using hKpay)
    (by simp only [mul_zero, neg_zero, Real.rpow_zero, mul_one]; exact le_rfl)

/-- Conductor partial-sum bounds control the excited spectral weight of every
zero-density prime flip at the precision of its actual harmonic correlation. -/
theorem eventually_zeroDensity_inner_sq_le_conductorSeries (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    {s t W : ℝ} (hs : 0 < s) (hst : s < t) (ht2 : t < 2 * Real.log 2)
    (hW : ∀ K, ∑ k ∈ range K, primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ W) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i₀ : PrimeHorizonIndex N, IsGroundBelow N t i₀ →
      ∀ w : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪w, primeEigen N i₀⟫ = 0 →
        ⟪w, primeSetHorizonVector P N⟫ ^ (2 : ℕ) ≤
          harmonicCorrelation (primeSetFlip P) N ^ (2 : ℕ) * (W + ε) *
            (primeEnergy N w - s * ‖w‖ ^ (2 : ℕ)) := by
  have hs2 := hst.trans ht2
  have hts : 0 < t - s := sub_pos.mpr hst
  have hW0 : 0 ≤ W := by simpa using hW 0
  let θ := min 1 (ε / (4 * (Real.sqrt W + 1)))
  have hθ : 0 < θ := lt_min one_pos (by positivity)
  have hWθ : (Real.sqrt W + 2 * θ) ^ (2 : ℕ) ≤ W + ε := by
    have h1 : θ ≤ ε / (4 * (Real.sqrt W + 1)) := min_le_right _ _
    have h2 : θ * (4 * (Real.sqrt W + 1)) ≤ ε :=
      (le_div_iff₀ (by positivity)).mp h1
    have h3 : θ ≤ 1 := min_le_left _ _
    have hprod := mul_nonneg hθ.le (sub_nonneg.mpr h3)
    have hsqrt := Real.sq_sqrt hW0
    nlinarith only [h2, hprod, hsqrt]
  obtain ⟨T, _, _, hA⟩ := exists_scale_zeroDensity_inner_sub_le P hP hs hst hθ 0
  let F := primeSetCutoff P (T - 1)
  have hF := primeSetCutoff_prime' P (T - 1)
  let δ := finiteFlipHarmonicDensity F
  have hδ : 0 < δ := finiteFlipHarmonicDensity_pos hF
  have hWF : finiteFlipSecular F s + 1 / s ≤ W := finiteFlipSecular_add_le P hs hs2 hW (T - 1)
  have hfinite := eventually_excitedResolvent_finiteFlip_le F hF hs hst ht2
    (ε := (δ * θ) ^ (2 : ℕ)) (by positivity)
  filter_upwards [hA, hfinite] with N ⟨hcpos, hAN⟩ hfiniteN i₀ hg w hw
  let cN := harmonicCorrelation (primeSetFlip P) N
  let G := primeEnergy N w - s * ‖w‖ ^ (2 : ℕ)
  have hG : 0 ≤ G :=
    (mul_nonneg hts.le (sq_nonneg _)).trans (primeEnergy_sub_ge_of_perp (s := s) hg hw)
  have hρ : excitedResolvent N s i₀ (finiteFlipHorizonVector F N) ≤
      (δ * (Real.sqrt W + θ)) ^ (2 : ℕ) := by
    refine (hfiniteN i₀ hg).trans ?_
    have hm := mul_le_mul_of_nonneg_left hWF (sq_nonneg δ)
    have heq : (δ * (Real.sqrt W + θ)) ^ (2 : ℕ) =
        δ ^ (2 : ℕ) * W + (δ * θ) ^ (2 : ℕ) + 2 * δ ^ (2 : ℕ) * θ * Real.sqrt W := by
      rw [mul_pow, add_sq, Real.sq_sqrt hW0]
      ring
    have hnonneg : 0 ≤ 2 * δ ^ (2 : ℕ) * θ * Real.sqrt W := by positivity
    rw [heq]
    linarith only [hm, hnonneg]
  have hFinner : |⟪w, finiteFlipHorizonVector F N⟫| ≤ δ * (Real.sqrt W + θ) * Real.sqrt G := by
    have h := Real.abs_le_sqrt ((inner_sq_le_excited hg hst hw _).trans
      (mul_le_mul_of_nonneg_right hρ hG))
    rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h
  have hmainF : |cN / δ * ⟪w, finiteFlipHorizonVector F N⟫| ≤
      cN * (Real.sqrt W + θ) * Real.sqrt G := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hcpos.le hδ.le)]
    calc
      _ ≤ cN / δ * (δ * (Real.sqrt W + θ) * Real.sqrt G) :=
        mul_le_mul_of_nonneg_left hFinner (div_nonneg hcpos.le hδ.le)
      _ = _ := by field_simp [hδ.ne']
  have habs : |⟪w, primeSetHorizonVector P N⟫| ≤
      cN * (Real.sqrt W + 2 * θ) * Real.sqrt G := by
    have heq : ⟪w, primeSetHorizonVector P N⟫ = (⟪w, primeSetHorizonVector P N⟫ -
        cN / δ * ⟪w, finiteFlipHorizonVector F N⟫) +
          cN / δ * ⟪w, finiteFlipHorizonVector F N⟫ := by ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    exact (add_le_add (hAN i₀ hg w hw) hmainF).trans_eq (by ring)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hG] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hWθ (sq_nonneg _)) hG)

/-- A zero-density prime flip retains the maximal hyperplane gap whenever all
conductor partial sums stay below the reciprocal spectral parameter. -/
theorem zeroDensity_primeSetFlip_hasHyperplaneGap_of_conductorSeries (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0))
    (hsec : ∀ s, 0 < s → s < 2 * Real.log 2 → ∀ K, ∑ k ∈ range K,
      primeSetSpectralWeight P (k + 2) / (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ 1 / s) :
    HasHyperplaneGap (primeSetFlip P) (2 * Real.log 2) := by
  intro ε hε
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let s := 2 * Real.log 2 - min ε (Real.log 2)
  have hmin0 : 0 < min ε (Real.log 2) := lt_min hε hl2
  have hminl := min_le_right ε (Real.log 2)
  have hs0 : 0 < s := by dsimp only [s]; linarith only [hl2, hminl]
  have hs2 : s < 2 * Real.log 2 := by dsimp only [s]; linarith only [hmin0]
  have hsε : 2 * Real.log 2 - ε ≤ s := by
    dsimp only [s]
    linarith only [min_le_left ε (Real.log 2)]
  let t := (s + 2 * Real.log 2) / 2
  have hst : s < t := by dsimp only [t]; linarith only [hs2]
  have ht2 : t < 2 * Real.log 2 := by dsimp only [t]; linarith only [hs2]
  have ht0 : 0 < t := hs0.trans hst
  let W := 1 / t
  have hW : ∀ K, ∑ k ∈ range K, primeSetSpectralWeight P (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ W := by
    intro K
    refine (sum_le_sum fun k _ => ?_).trans (hsec t ht0 ht2 K)
    have hgap := conductorEnergy_gap (m := k + 2) (by omega)
    have hden : 0 < ramanujanAdjunctionEnergy (k + 2) - γ - t := by linarith only [hgap, ht2]
    exact div_le_div_of_nonneg_left (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      hden (by linarith only [hst])
  have hsW : s * W < 1 := by
    dsimp only [W]
    rw [mul_one_div, div_lt_one ht0]
    exact hst
  let m := 1 - s * W
  have hm0 : 0 < m := by dsimp only [m]; linarith only [hsW]
  have hm1 : m ≤ 1 := by
    have h : 0 ≤ s * W := by dsimp only [W]; positivity
    dsimp only [m]
    linarith only [h]
  let ε' := m / (4 * s)
  have hε' : 0 < ε' := by dsimp only [ε']; positivity
  let X := W + ε'
  have hX : 0 < X := by dsimp only [X, W]; positivity
  let ε₀ := min (m / (8 * X)) ((m / 8) ^ (2 : ℕ) / (2 * X))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  have hε₀1 : ε₀ * X ≤ m / 8 := by
    have h := min_le_left (m / (8 * X)) ((m / 8) ^ (2 : ℕ) / (2 * X))
    rw [le_div_iff₀ (by positivity)] at h
    linarith only [h]
  have hε₀2 : 2 * ε₀ * X ≤ (m / 8) ^ (2 : ℕ) := by
    have h := min_le_right (m / (8 * X)) ((m / 8) ^ (2 : ℕ) / (2 * X))
    rw [le_div_iff₀ (by positivity)] at h
    linarith only [h]
  have hθ' : Real.sqrt (2 * ε₀ * X) ≤ m / 8 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hε₀2
  have hθ1 : Real.sqrt (2 * ε₀ * X) < 1 := by linarith only [hθ', hm1]
  have hcond : (s + ε₀) * X ≤ (1 - Real.sqrt (2 * ε₀ * X)) ^ (2 : ℕ) := by
    have hsX : s * X = s * W + m / 4 := by
      dsimp only [X, ε']
      field_simp [hs0.ne']
    have hsq : 1 - 2 * Real.sqrt (2 * ε₀ * X) ≤
        (1 - Real.sqrt (2 * ε₀ * X)) ^ (2 : ℕ) := by
      nlinarith only [sq_nonneg (Real.sqrt (2 * ε₀ * X))]
    dsimp only [m] at hm0 hθ' hε₀1 hsX
    nlinarith only [hsX, hε₀1, hθ', hsq, hm0]
  have hground := eventually_exists_ground ht0 ht2 hε₀
  have hmain := eventually_zeroDensity_inner_sq_le_conductorSeries P hP hs0 hst ht2 hW hε'
  have hpole := eventually_primeEnergy_poleUnit_le hε₀
  have hpositive := (tendsto_sparse_signedMean_atTop P hP).eventually (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (hground.and (hmain.and (hpole.and (hpositive.and (eventually_ge_atTop (1 : ℕ))))))
  refine ⟨N₀, fun N hN x hx => ?_⟩
  obtain ⟨⟨i₀, hg, hlam⟩, hmainN, hpoleN, hSN, hN1⟩ := hN₀ N hN
  have hcpos : 0 < harmonicCorrelation (primeSetFlip P) N :=
    div_pos (zero_lt_one.trans_le hSN) (gaugeHarmonicSum_one_pos hN1)
  let u : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 fun i => primeSetFlip P i * x i
  have hext : ∀ n ∈ Icc 1 N, horizonExtend u n = primeSetFlip P n * x n := by
    intro n hn
    simp only [horizonExtend, dif_pos hn, u]
  have hu : ⟪u, primeSetHorizonVector P N⟫ = 0 := by
    rw [primeSetHorizonVector_eq, real_inner_smul_right, real_inner_comm, inner_gaugeVector_eq]
    have heq : ∑ n ∈ Icc 1 N, primeSetFlip P n * (Real.sqrt n * horizonExtend u n) / n =
        ∑ n ∈ Icc 1 N, x n / Real.sqrt n := by
      refine sum_congr rfl fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      have hsqrt := Real.mul_self_sqrt hn0.le
      have hsqrt0 := (Real.sqrt_pos.mpr hn0).ne'
      rw [hext n hn, ← mul_assoc, mul_comm (primeSetFlip P n), mul_assoc, ← mul_assoc
        (primeSetFlip P n), primeSetFlip_mul_self, one_mul, div_eq_div_iff hn0.ne' hsqrt0,
        mul_comm (Real.sqrt n) (x n), mul_assoc, hsqrt]
    rw [heq, hx, mul_zero]
  have hmarg := le_primeEnergy_of_perp hs0.le hst hg hcpos hX.le hε₀.le hlam
    (fun w hw => hmainN i₀ hg w hw) (norm_poleUnit hN1)
    (inner_poleUnit_primeSetHorizonVector P hN1) hpoleN hθ1 hcond u hu
  have hform : atomicWeilForm N (fun n => primeSetFlip P n * x n) =
      ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, u⟫ := by
    rw [← atomicWeilForm_horizonExtend_eq_inner]
    exact atomicWeilForm_congr fun n hn => (hext n hn).symm
  have hmass : ‖u‖ ^ (2 : ℕ) = ∑ n ∈ Icc 1 N, x n ^ (2 : ℕ) := by
    rw [← sum_sq_horizonExtend]
    refine sum_congr rfl fun n hn => ?_
    rw [hext n hn, mul_pow, sq (primeSetFlip P n), primeSetFlip_mul_self, one_mul]
  rw [hform, ← hmass]
  unfold primeEnergy at hmarg
  have hmargin := mul_le_mul_of_nonneg_right hsε (sq_nonneg ‖u‖)
  nlinarith only [hmarg, hmargin]

/-- The conductor-series criterion holds at the bare zero-density endpoint,
including prime flips whose limiting Euler harmonic density is zero. -/
theorem zeroDensity_hodgeSeparates_primeSetFlip_iff_conductorSeries (P : Set ℕ)
    (hP : Tendsto (fun N => primeSetLogMass P N / (1 + Real.log N)) atTop (𝓝 0)) :
    HodgeSeparates (primeSetFlip P) ↔ ∃ s : ℝ, 0 < s ∧ s < 2 * Real.log 2 ∧
      1 / s < ∑' k : ℕ, primeSetSpectralWeight P (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
  have hf0 : ∀ s : ℝ, s < 2 * Real.log 2 → ∀ k : ℕ,
      0 ≤ primeSetSpectralWeight P (k + 2) / (ramanujanAdjunctionEnergy (k + 2) - γ - s) := by
    intro s hs2 k
    refine div_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) ?_
    have hgap := conductorEnergy_gap (m := k + 2) (by omega)
    linarith only [hgap, hs2]
  constructor
  · intro hsep
    by_contra hno
    push Not at hno
    have hsec : ∀ s, 0 < s → s < 2 * Real.log 2 → ∀ K, ∑ k ∈ range K,
        primeSetSpectralWeight P (k + 2) / (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤ 1 / s := by
      intro s hs hs2 K
      have hsum := summable_zeroDensity_conductorSeries P hP hs.le hs2
      exact (hsum.sum_le_tsum _ fun k _ => hf0 s hs2 k).trans (hno s hs hs2)
    exact (hodgeSeparates_iff_not_hasHyperplaneGap (primeSetFlip_mul_self P)).mp hsep
      (zeroDensity_primeSetFlip_hasHyperplaneGap_of_conductorSeries P hP hsec)
  · rintro ⟨s, hs, hs2, hlarge⟩
    have hsum := summable_zeroDensity_conductorSeries P hP hs.le hs2
    obtain ⟨K, hK⟩ := (hsum.hasSum.tendsto_sum_nat.eventually (Ioi_mem_nhds hlarge)).exists
    apply hodgeSeparates_primeSetFlip_of_packet P hs hs2 ((range K).image (· + 2))
      (fun m hm => by obtain ⟨k, _, rfl⟩ := mem_image.mp hm; omega)
    rw [sum_image fun a _ b _ h => by omega]
    exact hK

end GaloisForLFunctions.RenormalizedIntersectionTheory

