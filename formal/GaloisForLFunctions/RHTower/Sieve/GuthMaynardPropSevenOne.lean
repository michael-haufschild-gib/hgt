import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSevenOneDecay
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardSmoothedLagSum
import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-!
# Guth–Maynard Proposition 7.1: cancellation within the `I_m` integrals

By (7.4), `I_m = N³ ∫_{ℝ²} J(v, N L_m(v)) R(v₁) R(v₂/v₁) R(1/v₂) dv` with
`L_m(v) = m₁v₁ + m₂v₂ + m₃` and `J(v, ξ) = ∫ e(−ξu) u² w(u)² w(uv₁)² w(uv₂)² du`. The inner integral
vanishes unless `v ∈ [1/2, 2]²`, is `O(1)`, and by uniform non-stationary phase is `O_j(|ξ|^{−j})`.
Splitting `[1/2, 2]²` at `|L_m(v)| = δ/N` gives, for every `j` (`norm_cubicTerm_le_of_threshold`),

`|I_m| ≤ C N³ ∫_{v ∈ [1/2,2]², |L_m(v)| ≤ δ/N} |R(v₁) R(v₂/v₁) R(v₂)| dv + C N³ |W|³ δ^{−j}`,

using `|R(1/v)| = |R(v)|`. With `δ = T^η` this is Proposition 7.1 (`prop71`, and `prop71_paper`
with the error `O(T^{−200})` for a `1`-separated `W ⊂ [0, T]` and `N ≤ T`). The region is empty when
`|m₃| > 2|m₁| + 2|m₂| + δ/N`, which gives the second claim: for `|m₁| ≤ |m₂| ≤ |m₃|`, `I_m` is
negligible unless `|m₃| ≤ 4|m₂| + T^η/N` (`≤ 5|m₂|` once `T^η ≤ N`), i.e. `|m₂| ≍ |m₃|`.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace RHTower.GuthMaynard

noncomputable section

/-- The cancellation region `{v ∈ [1/2, 2]² : |m₁v₁ + m₂v₂ + m₃| ≤ δ}` of Proposition 7.1. -/
def cancellationRegion (m₁ m₂ m₃ : ℤ) (δ : ℝ) : Set (ℝ × ℝ) :=
  {v | v ∈ Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2 ∧ |cubicLinearForm m₁ m₂ m₃ v| ≤ δ}

/-- `|R(v₁) R(v₂/v₁) R(v₂)|`, the integrand of Proposition 7.1. -/
def lagTripleNorm (W : Finset ℝ) (v : ℝ × ℝ) : ℝ :=
  ‖lagSum W v.1‖ * ‖lagSum W (v.2 / v.1)‖ * ‖lagSum W v.2‖

theorem lagTripleNorm_nonneg (W : Finset ℝ) (v : ℝ × ℝ) : 0 ≤ lagTripleNorm W v := by
  unfold lagTripleNorm; positivity

theorem lagTripleNorm_le (W : Finset ℝ) (v : ℝ × ℝ) : lagTripleNorm W v ≤ (W.card : ℝ) ^ 3 := by
  unfold lagTripleNorm
  have h1 := norm_lagSum_le W v.1
  have h2 := norm_lagSum_le W (v.2 / v.1)
  have h3 := norm_lagSum_le W v.2
  calc ‖lagSum W v.1‖ * ‖lagSum W (v.2 / v.1)‖ * ‖lagSum W v.2‖
      ≤ (W.card : ℝ) * W.card * W.card := by gcongr
    _ = (W.card : ℝ) ^ 3 := by ring

/-- `|R(v₁) R(v₂/v₁) R(1/v₂)| = |R(v₁) R(v₂/v₁) R(v₂)|`, from `R(1/v) = conj R(v)`. -/
theorem norm_lagTriple (W : Finset ℝ) (v : ℝ × ℝ) : ‖lagTriple W v‖ = lagTripleNorm W v := by
  rw [lagTriple, norm_mul, norm_mul, lagSum_inv, Complex.norm_conj, lagTripleNorm]

theorem measurable_lagTripleNorm (W : Finset ℝ) : Measurable (lagTripleNorm W) := by
  have h := measurable_lagSum W
  unfold lagTripleNorm
  fun_prop

theorem measurableSet_cancellationRegion (m₁ m₂ m₃ : ℤ) (δ : ℝ) :
    MeasurableSet (cancellationRegion m₁ m₂ m₃ δ) := by
  change MeasurableSet ((Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2) ∩
    {v | |cubicLinearForm m₁ m₂ m₃ v| ≤ δ})
  refine (measurableSet_Icc.prod measurableSet_Icc).inter
    (measurableSet_le (f := fun v => |cubicLinearForm m₁ m₂ m₃ v|) ?_ measurable_const)
  unfold cubicLinearForm
  fun_prop

theorem cancellationRegion_subset (m₁ m₂ m₃ : ℤ) (δ : ℝ) :
    cancellationRegion m₁ m₂ m₃ δ ⊆ Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2 := fun _ hv => hv.1

theorem volume_real_box :
    (volume : Measure (ℝ × ℝ)).real (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2) = 9 / 4 := by
  rw [Measure.real, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
  norm_num

theorem volume_box_ne_top :
    (volume : Measure (ℝ × ℝ)) (Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne

/-- `|R(v₁) R(v₂/v₁) R(v₂)|` is integrable on every cancellation region. -/
theorem integrableOn_lagTripleNorm (W : Finset ℝ) (m₁ m₂ m₃ : ℤ) (δ : ℝ) :
    IntegrableOn (lagTripleNorm W) (cancellationRegion m₁ m₂ m₃ δ) :=
  Measure.integrableOn_of_bounded
    ((measure_mono (cancellationRegion_subset m₁ m₂ m₃ δ)).trans_lt
      volume_box_ne_top.lt_top).ne
    (measurable_lagTripleNorm W).aestronglyMeasurable (M := (W.card : ℝ) ^ 3)
    (ae_of_all _ fun v => by
      rw [Real.norm_of_nonneg (lagTripleNorm_nonneg W v)]
      exact lagTripleNorm_le W v)

/-- The region is empty when `|m₃| > 2|m₁| + 2|m₂| + δ`: on `[1/2, 2]²` the form
`m₁v₁ + m₂v₂ + m₃` stays away from zero. -/
theorem cancellationRegion_eq_empty {m₁ m₂ m₃ : ℤ} {δ : ℝ}
    (h : 2 * |(m₁ : ℝ)| + 2 * |(m₂ : ℝ)| + δ < |(m₃ : ℝ)|) :
    cancellationRegion m₁ m₂ m₃ δ = ∅ := by
  refine eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hL⟩ := hv
  unfold cubicLinearForm at hL
  have e1 : |(m₁ : ℝ) * v.1| ≤ 2 * |(m₁ : ℝ)| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < v.1)]; nlinarith [abs_nonneg (m₁ : ℝ)]
  have e2 : |(m₂ : ℝ) * v.2| ≤ 2 * |(m₂ : ℝ)| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < v.2)]; nlinarith [abs_nonneg (m₂ : ℝ)]
  have : |(m₃ : ℝ)| ≤ |(m₁ : ℝ) * v.1 + m₂ * v.2 + m₃| + |(m₁ : ℝ) * v.1| + |(m₂ : ℝ) * v.2| := by
    calc |(m₃ : ℝ)| = |((m₁ : ℝ) * v.1 + m₂ * v.2 + m₃) - (m₁ : ℝ) * v.1 - m₂ * v.2| := by
          congr 1; ring
      _ ≤ |(m₁ : ℝ) * v.1 + m₂ * v.2 + m₃| + |(m₁ : ℝ) * v.1| + |(m₂ : ℝ) * v.2| := by
          have := abs_sub (((m₁ : ℝ) * v.1 + m₂ * v.2 + m₃) - (m₁ : ℝ) * v.1) ((m₂ : ℝ) * v.2)
          have := abs_sub ((m₁ : ℝ) * v.1 + m₂ * v.2 + m₃) ((m₁ : ℝ) * v.1)
          linarith
  linarith

/-- Real-number assembly of the two pieces of `|I_m|`. -/
theorem prop71_assembly {K₀ K a b : ℝ} (hK₀ : 0 ≤ K₀) (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    K₀ * a + K * b * (9 / 4) ≤ (K₀ + 3 * K) * a + (K₀ + 3 * K) * b := by
  nlinarith [mul_nonneg hK ha, mul_nonneg hK₀ hb, mul_nonneg hK hb]

/-- **Proposition 7.1, explicit threshold.** For every `j` there is `C` such that for all finite
`W`, `N > 0`, `δ > 0` and `m ∈ ℤ³`,
`|I_m| ≤ C N³ ∫_{v ∈ [1/2,2]², |m₁v₁+m₂v₂+m₃| ≤ δ/N} |R(v₁)R(v₂/v₁)R(v₂)| dv + C N³ |W|³ / δ^j`. -/
theorem norm_cubicTerm_le_of_threshold (w : CGLSmoothBump) (j : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ (W : Finset ℝ) (N δ : ℝ) (m₁ m₂ m₃ : ℤ), 0 < N → 0 < δ →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤
        C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (δ / N), lagTripleNorm W v) +
          C * N ^ 3 * (W.card : ℝ) ^ 3 / δ ^ j := by
  obtain ⟨K₀, hK₀, hJ₀⟩ := exists_pow_mul_norm_cubicPhaseIntegral_le w 0
  obtain ⟨K, hK, hJ⟩ := exists_pow_mul_norm_cubicPhaseIntegral_le w j
  refine ⟨K₀ + 3 * K, by positivity, fun W N δ m₁ m₂ m₃ hN hδ => ?_⟩
  set G := cancellationRegion m₁ m₂ m₃ (δ / N) with hG
  set B : Set (ℝ × ℝ) := Icc (1 / 2 : ℝ) 2 ×ˢ Icc (1 / 2 : ℝ) 2 with hB
  set c : ℝ := K / δ ^ j * (W.card : ℝ) ^ 3 with hc
  have hc0 : 0 ≤ c := by positivity
  set g : ℝ × ℝ → ℝ := fun v => K₀ * G.indicator (lagTripleNorm W) v + B.indicator (fun _ => c) v
    with hg
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hGm : MeasurableSet G := measurableSet_cancellationRegion m₁ m₂ m₃ (δ / N)
  -- pointwise majorant of `|J| |R R R|`
  have hpt : ∀ v : ℝ × ℝ,
      ‖cubicPhaseIntegral w v (N * cubicLinearForm m₁ m₂ m₃ v) * lagTriple W v‖ ≤ g v := by
    intro v
    rw [norm_mul, norm_lagTriple]
    have hT0 := lagTripleNorm_nonneg W v
    by_cases hvB : v ∈ B
    · by_cases hvG : v ∈ G
      · have h0 := hJ₀ v (N * cubicLinearForm m₁ m₂ m₃ v)
        rw [pow_zero, one_mul] at h0
        simp only [hg, indicator_of_mem hvG, indicator_of_mem hvB]
        nlinarith [mul_le_mul_of_nonneg_right h0 hT0]
      · have hlarge : δ < |N * cubicLinearForm m₁ m₂ m₃ v| := by
          have : δ / N < |cubicLinearForm m₁ m₂ m₃ v| := lt_of_not_ge fun h => hvG ⟨hvB, h⟩
          rw [abs_mul, abs_of_pos hN]
          rwa [div_lt_iff₀ hN, mul_comm] at this
        have hJv : ‖cubicPhaseIntegral w v (N * cubicLinearForm m₁ m₂ m₃ v)‖ ≤ K / δ ^ j := by
          have h1 := hJ v (N * cubicLinearForm m₁ m₂ m₃ v)
          have hδj : 0 < δ ^ j := pow_pos hδ j
          have hle : δ ^ j ≤ |N * cubicLinearForm m₁ m₂ m₃ v| ^ j :=
            pow_le_pow_left₀ hδ.le hlarge.le j
          rw [le_div_iff₀ hδj, mul_comm]
          exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans h1
        simp only [hg, indicator_of_notMem hvG, indicator_of_mem hvB, mul_zero, zero_add, hc]
        calc ‖cubicPhaseIntegral w v (N * cubicLinearForm m₁ m₂ m₃ v)‖ * lagTripleNorm W v
            ≤ K / δ ^ j * (W.card : ℝ) ^ 3 :=
              mul_le_mul hJv (lagTripleNorm_le W v) hT0 (by positivity)
          _ = K / δ ^ j * (W.card : ℝ) ^ 3 := rfl
    · have hvG : v ∉ G := fun h => hvB (cancellationRegion_subset _ _ _ _ h)
      rw [cubicPhaseIntegral_eq_zero w hvB]
      simp [hg, indicator_of_notMem hvG, indicator_of_notMem hvB]
  have hgint : Integrable g :=
    ((integrableOn_lagTripleNorm W m₁ m₂ m₃ (δ / N)).integrable_indicator hGm).const_mul K₀ |>.add
      ((integrableOn_const volume_box_ne_top).integrable_indicator hBm)
  have hgval : ∫ v, g v = K₀ * (∫ v in G, lagTripleNorm W v) + c * (9 / 4) := by
    rw [hg, integral_add
      (((integrableOn_lagTripleNorm W m₁ m₂ m₃ (δ / N)).integrable_indicator hGm).const_mul K₀)
      ((integrableOn_const volume_box_ne_top).integrable_indicator hBm),
      integral_const_mul, integral_indicator hGm, integral_indicator_const _ hBm,
      volume_real_box, smul_eq_mul, mul_comm (9 / 4 : ℝ)]
  have hX : 0 ≤ ∫ v in G, lagTripleNorm W v :=
    setIntegral_nonneg hGm fun v _ => lagTripleNorm_nonneg W v
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  calc ‖cubicTerm w W N m₁ m₂ m₃‖
      = N ^ 3 * ‖∫ v : ℝ × ℝ, cubicPhaseIntegral w v (N * cubicLinearForm m₁ m₂ m₃ v) *
          lagTriple W v‖ := by
        rw [cubicTerm_eq_integral_ray, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg hN.le]
    _ ≤ N ^ 3 * ∫ v, g v := by
        gcongr
        exact (norm_integral_le_integral_norm _).trans
          (integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hgint (ae_of_all _ hpt))
    _ = K₀ * (N ^ 3 * ∫ v in G, lagTripleNorm W v) +
          K * (N ^ 3 * (W.card : ℝ) ^ 3 / δ ^ j) * (9 / 4) := by
        rw [hgval, hc]; ring
    _ ≤ (K₀ + 3 * K) * (N ^ 3 * ∫ v in G, lagTripleNorm W v) +
          (K₀ + 3 * K) * (N ^ 3 * (W.card : ℝ) ^ 3 / δ ^ j) :=
        prop71_assembly hK₀ hK (mul_nonneg hN3 hX) (by positivity)
    _ = _ := by ring

/-- **Guth–Maynard Proposition 7.1.** For every `η > 0` and `A` there is `C` such that for all
`T ≥ 1`, `N > 0`, finite `W` and `m ∈ ℤ³`,
`|I_m| ≤ C N³ ∫_{v ∈ [1/2,2]², |m₁v₁+m₂v₂+m₃| ≤ T^η/N} |R(v₁)R(v₂/v₁)R(v₂)| dv + C N³ |W|³ T^{−A}`. -/
theorem prop71 (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ), 1 ≤ T → 0 < N →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤
        C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) +
          C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := norm_cubicTerm_le_of_threshold w ⌈A / η⌉₊
  refine ⟨C, hC, fun T N W m₁ m₂ m₃ hT hN => ?_⟩
  have hTη : 0 < T ^ η := Real.rpow_pos_of_pos (by linarith) η
  refine (hbound W N (T ^ η) m₁ m₂ m₃ hN hTη).trans ?_
  gcongr
  -- `T^{−ηj} ≤ T^{−A}` for `j = ⌈A/η⌉`
  have hpow : (T ^ η) ^ ⌈A / η⌉₊ = T ^ (η * ⌈A / η⌉₊) := by
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast]
  have hexp : -(η * ⌈A / η⌉₊) ≤ -A := by
    have := Nat.le_ceil (A / η)
    rw [div_le_iff₀ hη] at this
    linarith
  rw [div_eq_mul_inv, hpow, ← Real.rpow_neg (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hexp) (by positivity)

/-- `|W| ≤ T + 1` for a `1`-separated `W ⊂ [0, T]`. -/
theorem card_le_of_isSeparated {T : ℝ} (hT : 0 ≤ T) {W : Finset ℝ} (hW : ∀ t ∈ W, t ∈ Icc 0 T)
    (hsep : IsSeparated 1 W) : (W.card : ℝ) ≤ T + 1 := by
  have := card_le_of_separated_of_subset_Icc one_pos hT W hsep hW
  simpa using this

/-- **Proposition 7.1 in the paper's normalisation.** For `1`-separated `W ⊂ [0, T]`, `T ≥ 1`,
`0 < N ≤ T`: `|I_m| ≤ C N³ ∫_{|m₁v₁+m₂v₂+m₃| ≤ T^η/N, v ∈ [1/2,2]²} |R(v₁)R(v₂/v₁)R(v₂)| + C T^{−200}`. -/
theorem prop71_paper (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ), 1 ≤ T → 0 < N → N ≤ T →
      (∀ t ∈ W, t ∈ Icc 0 T) → IsSeparated 1 W →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤
        C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) +
          C * T ^ (-200 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := prop71 w hη 206
  refine ⟨64 * C, by positivity, fun T N W m₁ m₂ m₃ hT hN hNT hW hsep => ?_⟩
  refine (hbound T N W m₁ m₂ m₃ hT hN).trans ?_
  have hcard : (W.card : ℝ) ≤ 2 * T := by
    have := card_le_of_isSeparated (by linarith) hW hsep; linarith
  have hX : 0 ≤ ∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v :=
    setIntegral_nonneg (measurableSet_cancellationRegion _ _ _ _) fun v _ =>
      lagTripleNorm_nonneg W v
  have hT0 : 0 < T := by linarith
  -- `N³ |W|³ T^{−206} ≤ 8 T^6 T^{−206} = 8 T^{−200}`
  have herr : N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-206 : ℝ) ≤ 8 * T ^ (-200 : ℝ) := by
    have h6 : T ^ (-200 : ℝ) = T ^ (6 : ℝ) * T ^ (-206 : ℝ) := by
      rw [← Real.rpow_add hT0]; norm_num
    rw [h6]
    have hN3 : N ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ hN.le hNT 3
    have hW3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
    have hT6 : T ^ (6 : ℝ) = T ^ 3 * T ^ 3 := by
      rw [show (6 : ℝ) = ((3 + 3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_add]
    rw [hT6]
    have hpos : 0 < T ^ (-206 : ℝ) := Real.rpow_pos_of_pos hT0 _
    calc N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-206 : ℝ) ≤ T ^ 3 * (2 * T) ^ 3 * T ^ (-206 : ℝ) := by
          gcongr
      _ = 8 * (T ^ 3 * T ^ 3 * T ^ (-206 : ℝ)) := by ring
  have : C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-206 : ℝ) ≤ 64 * C * T ^ (-200 : ℝ) := by
    have h8 := mul_le_mul_of_nonneg_left herr hC
    have hpos : 0 ≤ C * T ^ (-200 : ℝ) := mul_nonneg hC (Real.rpow_pos_of_pos hT0 _).le
    nlinarith
  have hmain : C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) ≤
      64 * C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) := by
    have : 0 ≤ C * N ^ 3 * (∫ v in cancellationRegion m₁ m₂ m₃ (T ^ η / N), lagTripleNorm W v) :=
      by positivity
    nlinarith
  linarith

/-- **Proposition 7.1, second claim.** If `|m₁| ≤ |m₂|` and `|m₃| > 4|m₂| + T^η/N` then the
cancellation region is empty, so `|I_m| ≤ C N³ |W|³ T^{−A}`. -/
theorem prop71_negligible (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ), 1 ≤ T → 0 < N →
      |(m₁ : ℝ)| ≤ |(m₂ : ℝ)| → 4 * |(m₂ : ℝ)| + T ^ η / N < |(m₃ : ℝ)| →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤ C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := prop71 w hη A
  refine ⟨C, hC, fun T N W m₁ m₂ m₃ hT hN h12 h23 => ?_⟩
  have hempty : cancellationRegion m₁ m₂ m₃ (T ^ η / N) = ∅ :=
    cancellationRegion_eq_empty (by linarith)
  have := hbound T N W m₁ m₂ m₃ hT hN
  rwa [hempty, Measure.restrict_empty, integral_zero_measure, mul_zero, zero_add] at this

/-- With `T^η ≤ N` and `1 ≤ |m₂|`, the second claim reads: `I_m` is negligible once
`|m₃| > 5|m₂|`. -/
theorem prop71_negligible_of_le (w : CGLSmoothBump) {η : ℝ} (hη : 0 < η) (A : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ (T N : ℝ) (W : Finset ℝ) (m₁ m₂ m₃ : ℤ), 1 ≤ T → T ^ η ≤ N →
      |(m₁ : ℝ)| ≤ |(m₂ : ℝ)| → 1 ≤ |(m₂ : ℝ)| → 5 * |(m₂ : ℝ)| < |(m₃ : ℝ)| →
      ‖cubicTerm w W N m₁ m₂ m₃‖ ≤ C * N ^ 3 * (W.card : ℝ) ^ 3 * T ^ (-A) := by
  obtain ⟨C, hC, hbound⟩ := prop71_negligible w hη A
  refine ⟨C, hC, fun T N W m₁ m₂ m₃ hT hTN h12 h2 h23 => ?_⟩
  have hTη : 0 < T ^ η := Real.rpow_pos_of_pos (by linarith) η
  have hN : 0 < N := hTη.trans_le hTN
  refine hbound T N W m₁ m₂ m₃ hT hN h12 ?_
  have : T ^ η / N ≤ 1 := (div_le_one hN).mpr hTN
  linarith

end

end RHTower.GuthMaynard
