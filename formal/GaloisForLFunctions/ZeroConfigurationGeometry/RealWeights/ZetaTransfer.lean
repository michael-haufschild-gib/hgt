import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.KernelChoice
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.ImageEnvelope
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.CountTransfer
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.ZetaMass
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.SpectralMass

/-!
# Sharp local weighted counts for positive ζ mimics

A positive on-line weighting with the ζ image on any fixed positive
aperture inherits every local density coefficient above `1/(2π)`.
A normalized strip envelope transfers the actual ζ multiplicity count;
the absolute Lorentzian tail is absorbed by reserved density slack.
The resulting constants are uniform over all such weightings.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 Zeta23.RvM SquareRootThreshold

/-- Every positive on-line mimic of the ζ image on the smooth windows of a positive aperture
satisfies the sharp local weighted count at sufficiently large height. Constants are uniform
in the mimic; weights need neither be integral nor bounded below. -/
theorem zeta_positive_mimic_weighted_count_on_band_of_smooth {a θ : ℝ} (ha : 0 < a) (hθ : 1 < θ) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 40 ≤ T₀ ∧ ∀ w : ℂ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≠ 0 → z.re = 1 / 2) →
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) →
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ Icc (-a) a →
        weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f) →
      ∀ T : ℝ, T₀ ≤ T → ∀ x y : ℝ, T / 2 ≤ x → x ≤ y → y ≤ 3 * T / 2 →
      ∀ s : Finset ℂ, (∀ z ∈ s, z.im ∈ Icc x y) →
        (∑ z ∈ s, w z) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
          A * Real.log (T / (2 * π)) := by
  classical
  -- Reserve part of the density slack for the far tail.
  let θm := (1 + θ) / 2
  let θs := (1 + θm) / 2
  let q := θm / θs
  have hθm : 1 < θm := by dsimp [θm]; linarith only [hθ]
  have hθs : 1 < θs := by dsimp [θs]; linarith only [hθm]
  have hθsm : θs < θm := by dsimp [θs]; linarith only [hθm]
  have hθmθ : θm < θ := by dsimp [θm]; linarith only [hθ]
  have hq : 1 < q := (one_lt_div (by linarith only [hθs])).mpr hθsm
  have hq0 : 0 ≤ q := (lt_trans zero_lt_one hq).le
  have hqθs : q * θs = θm := by
    dsimp [q]
    exact div_mul_cancel₀ θm (by linarith only [hθs])
  -- The strip envelope costs at most `q` after central-mass normalization.
  obtain ⟨ε, R, b, hε, hεa, hR, hb, hbs, hQ, hE_Q⟩ :=
    exists_camera_kernel_with_strip_mass ha hq
  have hbw : ApertureWindow ε b := ⟨hb.of_le (by norm_cast), hbs⟩
  let Q := ∫ v in (-R)..R, ‖paperFT b v‖ ^ 2
  let E := cameraStripEnvelope b ε
  change 0 < Q at hQ
  change (∫ x, E x) ≤ q * Q at hE_Q
  obtain ⟨hEi, _⟩ := cameraStripEnvelope_integrable_and_mass_le hbw.1 hbs hε
  let c : ℂ → ℂ := multDiff zetaZeroConfig emptyZeroConfig
  have hcmem (z : ℂ) (hz : c z ≠ 0) : z ∈ zetaZeroConfig.carrier := by
    by_contra hn
    apply hz
    dsimp [c]
    rw [multDiff_emptyZeroConfig, Set.indicator_of_notMem hn]
  have hcnorm (z : ℂ) : ‖c z‖ = zetaZeroConfig.carrier.indicator
      (fun z => (zetaZeroConfig.mult z : ℝ)) z := by
    change ‖multDiff zetaZeroConfig emptyZeroConfig z‖ =
      zetaZeroConfig.carrier.indicator (fun z => (zetaZeroConfig.mult z : ℝ)) z
    rw [multDiff_emptyZeroConfig]
    by_cases hz : z ∈ zetaZeroConfig.carrier
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Complex.norm_natCast]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
  have hc : Summable fun z => ‖c z‖ / (1 + Complex.normSq (gammaOf z)) := by
    simpa only [hcnorm] using summable_indicator_tempered zetaZeroConfig temperedConfig_zeta
  have hstrip (z : ℂ) (hz : c z ≠ 0) := zetaZeroConfig.strip z (hcmem z hz)
  obtain ⟨C, hC, hsource⟩ := weightedImage_le_central_envelope hstrip hc hb hbs hε
  let B := 320 * C * C * Real.exp ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ := θ - θm
  have hδ : 0 < δ := sub_pos.mpr hθmθ
  let H := max 1 (2 * π * B / (Q * δ))
  let T₀ := max (max 40 (zetaCameraCountHeight θs)) (max (8 * R) (2 * π * Real.exp H))
  let A := 2 * R * θ / (2 * π) + q * zetaCameraCountConstant θs
  have hc0 : 0 ≤ zetaCameraCountConstant θs := zetaCameraCountConstant_nonneg hθs
  have hA : 0 ≤ A := by
    have hRs : 0 ≤ R := by linarith only [hR]
    have hθ0 : 0 ≤ θ := by linarith only [hθ]
    dsimp [A]
    positivity
  refine ⟨A, T₀, hA, (le_max_left _ _).trans (le_max_left _ _),
    fun w hw0 hline hw himage T hT x y hx hxy hy s hs => ?_⟩
  have hTcount : max 40 (zetaCameraCountHeight θs) ≤ T := (le_max_left _ _).trans hT
  have hT40 : 40 ≤ T := (le_max_left _ _).trans hTcount
  have hT0 : 0 < T := by linarith only [hT40]
  have hTR : 8 * R ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTheight : 2 * π * Real.exp H ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hπ : 0 < 2 * π := by positivity
  let u := Real.log (T / (2 * π))
  have hHu : H ≤ u := by
    have hh : Real.exp H ≤ T / (2 * π) := (le_div_iff₀ hπ).mpr (by linarith only [hTheight])
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos H) hh
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hHu
  have hu0 : 0 ≤ u := by linarith only [hu1]
  have hbudget : B / Q ≤ δ / (2 * π) * u := by
    have hh : 2 * π * B ≤ u * (Q * δ) :=
      (div_le_iff₀ (mul_pos hQ hδ)).mp ((le_max_right _ _).trans hHu)
    apply (div_le_iff₀ hQ).mpr
    apply (mul_le_mul_iff_right₀ hπ).mp
    calc (2 * π) * B ≤ u * (Q * δ) := hh
      _ = (2 * π) * (δ / (2 * π) * u * Q) := by field_simp
  -- A wider source band leaves distance `T/8` beyond every modulation point.
  let Z : Set ℂ := {z | IsNontrivialZero z ∧ |z.im - T| ≤ 3 * T / 4}
  have hZfin : Z.Finite := (zerosIn_finite (T / 4 - 1) (7 * T / 4)).subset (by
    intro z hz
    obtain ⟨hlo, hhi⟩ := abs_le.mp hz.2
    exact ⟨hz.1, by linarith only [hlo], by linarith only [hhi]⟩)
  let p := hZfin.toFinset
  have hp (z : ℂ) : z ∈ p ↔ z ∈ Z := Set.Finite.mem_toFinset hZfin
  have hsourcecount (l r : ℝ) (hlr : l ≤ r) (t : Finset ℂ) (ht : t ⊆ p)
      (htt : ∀ z ∈ t, z.im ∈ Icc l r) :
      (∑ z ∈ t, (zetaZeroConfig.mult z : ℝ)) ≤
        θs / (2 * π) * u * (r - l) + zetaCameraCountConstant θs * u := by
    apply zeta_mass_wide_camera_band_le hθs hTcount t l r hlr
    intro z hz
    exact ⟨((hp z).mp (ht hz)).1, ((hp z).mp (ht hz)).2, htt z hz⟩
  have hupper (X : ℝ) (hX : X ∈ Icc (x - R) (y + R)) :
      (weightedImage (fun z => (w z : ℂ)) (localWindow X b) (localWindow X b)).re ≤
        (∑ z ∈ p, (zetaZeroConfig.mult z : ℝ) * E (z.im - X)) + B := by
    have hXR : |X - T| ≤ 5 * T / 8 := by
      rw [abs_le]
      constructor <;> linarith only [hX.1, hX.2, hx, hy, hTR]
    have hX0 : 0 ≤ X := by linarith only [hX.1, hx, hTR, hT40]
    have hX2 : |X| ≤ 2 * T := by rw [abs_of_nonneg hX0]; linarith only [hX.2, hy, hTR, hT40]
    have hfar (z : ℂ) (hcz : c z ≠ 0) (hz : z ∉ p) : T / 8 < |z.im - X| := by
      have hnot : ¬ |z.im - T| ≤ 3 * T / 4 := fun h => hz ((hp z).mpr ⟨hcmem z hcz, h⟩)
      have htri : |z.im - T| ≤ |z.im - X| + |X - T| := by
        calc |z.im - T| = |(z.im - X) + (X - T)| := by congr 1; ring
          _ ≤ |z.im - X| + |X - T| := abs_add_le _ _
      linarith only [lt_of_not_ge hnot, htri, hXR]
    have hh := hsource X (T / 8) p (by positivity) hfar
    -- The sixth-order tail is uniformly bounded; the height budget pays it.
    have hcoeff : 5 / 4 * (1 + |X|) ^ 2 / (1 + T / 8) ^ 4 ≤ 320 := by
      have hv1 : 1 ≤ 1 + T / 8 := by linarith only [hT40]
      have hv0 : 0 < 1 + T / 8 := lt_of_lt_of_le zero_lt_one hv1
      have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |X|)
        (show 1 + |X| ≤ 16 * (1 + T / 8) by linarith only [hX2]) 2
      have hpow := pow_le_pow_right₀ hv1 (by norm_num : 2 ≤ (4 : ℕ))
      rw [div_le_iff₀ (pow_pos hv0 4)]
      nlinarith only [hsq, hpow]
    have htail : C * C * Real.exp ε * (5 / 4 * (1 + |X|) ^ 2 / (1 + T / 8) ^ 4) *
        (∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z))) ≤ B := by
      have hm : (∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z))) ≤ 1 :=
        zeta_empty_lorentzian_mass_lt.le.trans (by norm_num)
      have hm0 : 0 ≤ ∑' z, ‖c z‖ / (1 + Complex.normSq (gammaOf z)) :=
        tsum_nonneg fun z => div_nonneg (norm_nonneg _)
          (by linarith only [Complex.normSq_nonneg (gammaOf z)])
      calc _ ≤ (C * C * Real.exp ε * 320) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hcoeff (by positivity)) hm hm0 (by positivity)
        _ = B := by dsimp [B]; ring
    have hcentral : (∑ z ∈ p, ‖c z‖ * cameraStripEnvelope b ε (z.im - X)) =
        ∑ z ∈ p, (zetaZeroConfig.mult z : ℝ) * E (z.im - X) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzc : z ∈ zetaZeroConfig.carrier := ((hp z).mp hz).1
      rw [hcnorm, Set.indicator_of_mem hzc]
    have hba : ApertureWindow a b := ⟨hbw.1, hbs.trans (Icc_subset_Icc (neg_le_neg hεa) hεa)⟩
    rw [himage (localWindow X b) (hb.mul (contDiff_const.mul Complex.ofRealCLM.contDiff).neg.cexp)
      (apertureWindow_localWindow hba X).2]
    have hsourceeq : weightedImage c (localWindow X b) (localWindow X b) =
        zetaZeroConfig.W (localWindow X b) (localWindow X b) := by
      unfold weightedImage
      simp_rw [c, multDiff_emptyZeroConfig]
      exact (W_eq_tsum_indicator _ _ _).symm
    rw [hcentral, hsourceeq] at hh
    exact (Complex.re_le_norm _).trans (hh.trans (add_le_add le_rfl htail))
  -- Integrate the source envelope, then cancel its central kernel mass.
  have hmain := weighted_count_le_of_envelope hw0 hline hw hbw.1 hbw.hasCompactSupport
    hxy (by linarith only [hR]) hQ hEi (cameraStripEnvelope_nonneg hε) p
    (fun z => (zetaZeroConfig.mult z : ℝ)) hsourcecount hupper s hs
  let L := y - x + 2 * R
  have hL : 0 ≤ L := by dsimp [L]; linarith only [hxy, hR]
  have hD : 0 ≤ θs / (2 * π) * u * L + zetaCameraCountConstant θs * u := by
    have hθs0 : 0 ≤ θs := by linarith only [hθs]
    positivity
  have hn : ((θs / (2 * π) * u * L + zetaCameraCountConstant θs * u) * (∫ v, E v) + B * L) / Q ≤
      q * (θs / (2 * π) * u * L + zetaCameraCountConstant θs * u) + (B / Q) * L := by
    apply (div_le_iff₀ hQ).mpr
    have hh := mul_le_mul_of_nonneg_left hE_Q hD
    calc _ ≤ (θs / (2 * π) * u * L + zetaCameraCountConstant θs * u) * (q * Q) + B * L :=
        add_le_add hh le_rfl
      _ = _ := by field_simp [ne_of_gt hQ]
  have hbnd := mul_le_mul_of_nonneg_right hbudget hL
  refine hmain.trans (hn.trans ?_)
  calc _ ≤ q * (θs / (2 * π) * u * L + zetaCameraCountConstant θs * u) +
        (δ / (2 * π) * u) * L := add_le_add le_rfl hbnd
    _ = (q * θs / (2 * π) + δ / (2 * π)) * u * L +
        q * zetaCameraCountConstant θs * u := by ring
    _ = θ / (2 * π) * u * L + q * zetaCameraCountConstant θs * u := by
      rw [hqθs]
      dsimp [δ]
      ring
    _ = θ / (2 * π) * u * (y - x) + A * u := by dsimp [A, L]; ring

/-- The sharp weighted count in the camera's height band for a mimic of the smooth windows, for
arbitrary interval endpoints. -/
theorem zeta_positive_mimic_weighted_count_of_smooth {a θ : ℝ} (ha : 0 < a) (hθ : 1 < θ) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 40 ≤ T₀ ∧ ∀ w : ℂ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≠ 0 → z.re = 1 / 2) →
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) →
      (∀ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f → tsupport f ⊆ Icc (-a) a →
        weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f) →
      ∀ T : ℝ, T₀ ≤ T → ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℂ,
      (∀ z ∈ s, |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
        (∑ z ∈ s, w z) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
          A * Real.log (T / (2 * π)) := by
  classical
  obtain ⟨A, T₀, hA, hT₀, hcount⟩ := zeta_positive_mimic_weighted_count_on_band_of_smooth ha hθ
  refine ⟨A, T₀, hA, hT₀, fun w hw0 hline hw himage T hT x y hxy s hs => ?_⟩
  have hT40 : 40 ≤ T := hT₀.trans hT
  have hlog : 0 ≤ Real.log (T / (2 * π)) :=
    Real.log_nonneg ((one_le_div (by positivity : 0 < 2 * π)).mpr
      (by linarith only [hT40, Real.pi_lt_four]))
  have hθ0 : 0 ≤ θ := by linarith only [hθ]
  let l := max x (T / 2)
  let r := min y (3 * T / 2)
  have hsr : ∀ z ∈ s, z.im ∈ Icc l r := by
    intro z hz
    obtain ⟨hb, hxz, hzy⟩ := hs z hz
    obtain ⟨hlo, hhi⟩ := abs_le.mp hb
    exact ⟨max_le hxz (by linarith only [hlo]), le_min hzy (by linarith only [hhi])⟩
  by_cases hlr : l ≤ r
  · have hh := hcount w hw0 hline hw himage T hT l r
      (le_max_right _ _) hlr (min_le_right _ _) s hsr
    have hlen : r - l ≤ y - x := by
      linarith only [min_le_left y (3 * T / 2), le_max_left x (T / 2)]
    exact hh.trans (add_le_add
      (mul_le_mul_of_nonneg_left hlen (by positivity)) le_rfl)
  · have he : s = ∅ := Finset.eq_empty_of_forall_notMem fun z hz =>
      hlr ((hsr z hz).1.trans (hsr z hz).2)
    rw [he, Finset.sum_empty]
    have hlen : 0 ≤ y - x := sub_nonneg.mpr hxy
    positivity

/-- Every positive on-line mimic of the ζ image on a positive aperture satisfies the sharp local
weighted count at sufficiently large height. -/
theorem zeta_positive_mimic_weighted_count_on_band {a θ : ℝ} (ha : 0 < a) (hθ : 1 < θ) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 40 ≤ T₀ ∧ ∀ w : ℂ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≠ 0 → z.re = 1 / 2) →
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) →
      (∀ f : ℝ → ℂ, ApertureWindow a f →
        weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f) →
      ∀ T : ℝ, T₀ ≤ T → ∀ x y : ℝ, T / 2 ≤ x → x ≤ y → y ≤ 3 * T / 2 →
      ∀ s : Finset ℂ, (∀ z ∈ s, z.im ∈ Icc x y) →
        (∑ z ∈ s, w z) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
          A * Real.log (T / (2 * π)) := by
  obtain ⟨A, T₀, hA, hT₀, hcount⟩ := zeta_positive_mimic_weighted_count_on_band_of_smooth ha hθ
  exact ⟨A, T₀, hA, hT₀, fun w hw0 hline hw himage =>
    hcount w hw0 hline hw fun f hf hs => himage f ⟨hf.of_le (by norm_cast), hs⟩⟩

/-- The sharp weighted count in the camera's height band, for arbitrary interval endpoints. -/
theorem zeta_positive_mimic_weighted_count {a θ : ℝ} (ha : 0 < a) (hθ : 1 < θ) :
    ∃ A T₀ : ℝ, 0 ≤ A ∧ 40 ≤ T₀ ∧ ∀ w : ℂ → ℝ,
      (∀ z, 0 ≤ w z) → (∀ z, w z ≠ 0 → z.re = 1 / 2) →
      (Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z))) →
      (∀ f : ℝ → ℂ, ApertureWindow a f →
        weightedImage (fun z => (w z : ℂ)) f f = zetaZeroConfig.W f f) →
      ∀ T : ℝ, T₀ ≤ T → ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℂ,
      (∀ z ∈ s, |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
        (∑ z ∈ s, w z) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
          A * Real.log (T / (2 * π)) := by
  obtain ⟨A, T₀, hA, hT₀, hcount⟩ := zeta_positive_mimic_weighted_count_of_smooth ha hθ
  exact ⟨A, T₀, hA, hT₀, fun w hw0 hline hw himage =>
    hcount w hw0 hline hw fun f hf hs => himage f ⟨hf.of_le (by norm_cast), hs⟩⟩

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_positive_mimic_weighted_count_on_band

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_positive_mimic_weighted_count
