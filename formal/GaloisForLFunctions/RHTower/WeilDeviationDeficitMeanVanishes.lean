import GaloisForLFunctions.RHTower.WeilDeviationPacketDecomposition

/-!
# Mean balance: the deficit of a Weil-positive system is controlled by its excess

Let `lam` be full-cone Weil-positive, with translation-bounded (`CauchyBounded`) excess `e` and
deficit `v`. For a weight `w`, the *mean* `M_δ(w) = W_w(𝓕G_{0,δ})` is the average of `w` against
the window `δ𝓕G(δu)` of length `1/δ`. Write `A_δ = M_δ(v)` and `E_δ = M_δ(e)`.

**Theorem** (`meanBalance`). `(F(0) − 3/8) A_δ ≤ (F(0) + 3/8) E_δ + o(1)` as `δ → 0⁺`. Here
`F(0) = 0.4356`, so the deficit density is at most about `13.4` times the excess density.

**Corollary** (`tendsto_deficitMean`). If `E_δ → 0`, then `A_δ → 0`. This holds in particular when
the excess is summable (`excessMeanVanishes_of_summable`).

**Proof.**
- **Fejér identity.** The Fejér test `F` has `𝓕F = 0` at `±log n` for every `n ≥ 2`, so the
  deviation pairs to zero with `𝓕F`.
- **Cut off.** Cut `F` off at `Γ`, so `h = F χ(·/Γ)`. The tail pairing tends to `0`.
- **Decompose** `h` into the packet `G_{0,δ}` at the origin, flattened packets at the finitely many
  zeros `γ` of `Ξ` in `[−2Γ, 2Γ]`, and a nonnegative remainder vanishing near the zeros.
- **Estimate the pieces.**
  - The remainder pairs nonpositively (near-null positivity).
  - The origin packet contributes `F(0)(E_δ − A_δ)` up to `O(δ)`.
  - Each zero packet contributes at most `F(γ)(A_δ + E_δ + K'ε)` up to `O_ε(δ)`.
- **Conclude.** `F(0)(A_δ − E_δ) ≤ Σ_γ F(γ)(A_δ + E_δ) +` errors. The zero budget
  `Σ_γ F(γ) ≤ 3/8` finishes the proof.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-! ## The Fejér identity -/

theorem hasCompactSupport_fourier_fejerTestC : HasCompactSupport (𝓕 fejerTestC) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(17 / 25)) (b := 17 / 25)) fun u hu => ?_
  apply fourier_fejerTestC_eq_zero
  rw [mem_Icc, not_and_or, not_le, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_abs_le u]
  · linarith [le_abs_self u]

theorem integrable_fourier_fejerTestC : Integrable (𝓕 fejerTestC) :=
  (continuous_fourier_integrable integrable_fejerTestC).integrable_of_hasCompactSupport
    hasCompactSupport_fourier_fejerTestC

/-- A test whose transform vanishes at every `±log n`, `n ≥ 2`, pairs to zero. -/
theorem deviationPairing_eq_zero_of_log {lam : ℕ → ℝ} {φ : ℝ → ℂ}
    (hφ : ∀ n : ℕ, 2 ≤ n → φ (Real.log n) = 0 ∧ φ (-Real.log n) = 0) :
    deviationPairing lam φ = 0 := by
  unfold deviationPairing
  refine (tsum_congr fun n => ?_).trans tsum_zero
  by_cases hn : 2 ≤ n
  · rw [(hφ n hn).1, (hφ n hn).2]; simp
  · simp [weilDeviation, hn]

/-! ## Cut-off tests -/

theorem norm_packet_cutoffC_le (Γ ξ : ℝ) : ‖packet cutoffC 0 Γ ξ‖ ≤ 1 := norm_cutoffC_le _

theorem packet_cutoffC_eq_zero {Γ ξ : ℝ} (hΓ : 0 < Γ) (hξ : 2 * Γ ≤ |ξ|) :
    packet cutoffC 0 Γ ξ = 0 := by
  simp only [packet, cutoffC, sub_zero]
  rw [excessFlatBump_eq_zero (by rw [abs_div, abs_of_pos hΓ, le_div_iff₀ hΓ]; linarith)]
  simp

theorem packet_cutoffC_eq_one {Γ ξ : ℝ} (hΓ : 0 < Γ) (hξ : |ξ| ≤ Γ) :
    packet cutoffC 0 Γ ξ = 1 := by
  simp only [packet, cutoffC, sub_zero]
  rw [excessFlatBump_eq_one (by rw [abs_div, abs_of_pos hΓ, div_le_one hΓ]; exact hξ)]
  simp

theorem tsupport_mul_cutoff_subset {Φ : ℝ → ℂ} {Γ : ℝ} (hΓ : 0 < Γ) :
    tsupport (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) ⊆ Icc (-(2 * Γ)) (2 * Γ) := by
  refine closure_minimal (fun ξ hξ => ?_) isClosed_Icc
  rw [Function.mem_support] at hξ
  by_contra hout
  apply hξ
  rw [mem_Icc, not_and_or, not_le, not_le] at hout
  rw [packet_cutoffC_eq_zero hΓ, mul_zero]
  rcases hout with h | h
  · linarith [neg_abs_le ξ]
  · linarith [le_abs_self ξ]

theorem hasCompactSupport_mul_cutoff {Φ : ℝ → ℂ} {Γ : ℝ} (hΓ : 0 < Γ) :
    HasCompactSupport (fun ξ => Φ ξ * packet cutoffC 0 Γ ξ) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_mul_cutoff_subset hΓ)

/-! ## The zero window and its budget -/

/-- The zeros of `Ξ` in `[−R, R]`, as a finite set. -/
def zeroWindow (R : ℝ) : Finset ℝ := (finite_riemannXi_zeros R).toFinset

theorem mem_zeroWindow {R ξ : ℝ} : ξ ∈ zeroWindow R ↔ |ξ| ≤ R ∧ riemannXi ξ = 0 := by
  simp [zeroWindow]

theorem zero_notMem_zeroWindow (R : ℝ) : (0 : ℝ) ∉ zeroWindow R := by
  rw [mem_zeroWindow]
  rintro ⟨-, h⟩
  exact riemannXiReal_zero_ne (by rw [riemannXiReal, h, Complex.zero_re])

/-- **The zero budget of the Fejér test over a zero window.** -/
theorem sum_fejerTest_zeroWindow_le (R : ℝ) : ∑ γ ∈ zeroWindow R, fejerTest γ ≤ 3 / 8 := by
  classical
  set s := (zeroWindow R).image fun γ => 2 * π * γ with hs
  have hinj : Set.InjOn (fun γ : ℝ => 2 * π * γ) (zeroWindow R) := fun a _ b _ h => by
    simpa [Real.pi_ne_zero] using h
  have hs0 : ∀ t ∈ s, XiC t = 0 := by
    intro t ht
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp ht
    have := (mem_zeroWindow.mp hγ).2
    rw [riemannXi_eq_zero_iff] at this
    simpa using this
  have h := sum_fejerTest_zeros_le s hs0
  rw [hs, Finset.sum_image hinj] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1; field_simp

theorem hasCompactSupport_flatPacketC {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) :
    HasCompactSupport (flatPacketC ε) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) fun x hx => ?_
  apply flatPacketC_eq_zero hε0 hε
  rw [mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

theorem integrable_flatPacketC {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) : Integrable (flatPacketC ε) :=
  (contDiff_flatPacketC ε).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_flatPacketC hε0 hε)

theorem norm_fejerTestC_le (ξ : ℝ) : ‖fejerTestC ξ‖ ≤ 2 := by
  rw [fejerTestC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerTest_nonneg ξ)]
  refine (fejerTest_le_profile ξ).trans ?_
  rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ξ]

/-! ## The cut-off Fejér test -/

/-- The Fejér test cut off at `Γ`: `F(ξ) χ(ξ/Γ)`. -/
def fejerCutoff (Γ ξ : ℝ) : ℂ := fejerTestC ξ * packet cutoffC 0 Γ ξ

/-- The real form of the cut-off Fejér test. -/
def fejerCutoffReal (Γ ξ : ℝ) : ℝ := fejerTest ξ * excessFlatBump (ξ / Γ)

theorem fejerCutoffReal_nonneg (Γ ξ : ℝ) : 0 ≤ fejerCutoffReal Γ ξ :=
  mul_nonneg (fejerTest_nonneg ξ) excessFlatBump.nonneg

theorem fejerCutoff_eq_ofReal (Γ : ℝ) : fejerCutoff Γ = fun ξ => (fejerCutoffReal Γ ξ : ℂ) := by
  funext ξ
  simp [fejerCutoff, fejerCutoffReal, fejerTestC, packet, cutoffC]

theorem contDiff_fejerCutoff (Γ : ℝ) : ContDiff ℝ ∞ (fejerCutoff Γ) :=
  contDiff_fejerTestC.mul (contDiff_packet contDiff_cutoffC 0 Γ)

theorem hasCompactSupport_fejerCutoff {Γ : ℝ} (hΓ : 0 < Γ) : HasCompactSupport (fejerCutoff Γ) :=
  hasCompactSupport_mul_cutoff hΓ

theorem norm_fejerCutoff_le (Γ ξ : ℝ) : ‖fejerCutoff Γ ξ‖ ≤ fejerTest ξ := by
  rw [fejerCutoff, norm_mul]
  refine (mul_le_of_le_one_right (norm_nonneg _) (norm_packet_cutoffC_le Γ ξ)).trans ?_
  rw [fejerTestC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (fejerTest_nonneg ξ)]

theorem norm_fejerCutoff_le_two (Γ ξ : ℝ) : ‖fejerCutoff Γ ξ‖ ≤ 2 := by
  refine (norm_fejerCutoff_le Γ ξ).trans ?_
  refine (fejerTest_le_profile ξ).trans ?_
  rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg ξ]

theorem fejerCutoff_zero {Γ : ℝ} (hΓ : 0 < Γ) : fejerCutoff Γ 0 = (fejerTest 0 : ℂ) := by
  rw [fejerCutoff, packet_cutoffC_eq_one hΓ (by rw [abs_zero]; exact hΓ.le), mul_one, fejerTestC]

theorem mem_zeroWindow_of_mem_tsupport {Γ : ℝ} (hΓ : 0 < Γ) :
    ∀ ξ ∈ tsupport (fejerCutoff Γ), riemannXi ξ = 0 → ξ ∈ zeroWindow (2 * Γ) := by
  intro ξ hξ hz
  have := tsupport_mul_cutoff_subset (Φ := fejerTestC) hΓ hξ
  exact mem_zeroWindow.mpr ⟨abs_le.mpr this, hz⟩

theorem sum_norm_fejerCutoff_le (Γ : ℝ) : ∑ γ ∈ zeroWindow (2 * Γ), ‖fejerCutoff Γ γ‖ ≤ 3 / 8 :=
  (Finset.sum_le_sum fun γ _ => norm_fejerCutoff_le Γ γ).trans (sum_fejerTest_zeroWindow_le _)

theorem sum_norm_fejerCutoff_le_card (Γ : ℝ) :
    ∑ γ ∈ zeroWindow (2 * Γ), ‖fejerCutoff Γ γ‖ ≤ 2 * ((zeroWindow (2 * Γ)).card : ℝ) := by
  refine (Finset.sum_le_sum fun γ _ => norm_fejerCutoff_le_two Γ γ).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The Fejér identity.** The cut-off Fejér test pairs to minus the tail. -/
theorem deviationPairing_fourier_fejerCutoff (lam : ℕ → ℝ) {Γ : ℝ} (hΓ : 0 < Γ) :
    deviationPairing lam (𝓕 (fejerCutoff Γ)) =
      -deviationPairing lam (tailTransform fejerTestC Γ) := by
  have hi : Integrable (fejerCutoff Γ) :=
    (contDiff_fejerCutoff Γ).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_fejerCutoff hΓ)
  have hi2 : Integrable fun ξ => fejerTestC ξ * (1 - packet cutoffC 0 Γ ξ) :=
    integrable_fejerTestC.mul_bdd (c := 1)
      ((continuous_const.sub (contDiff_packet contDiff_cutoffC 0 Γ).continuous).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => norm_one_sub_cutoffC_le _)
  have hfun : (fun ξ => fejerCutoff Γ ξ + fejerTestC ξ * (1 - packet cutoffC 0 Γ ξ)) =
      fejerTestC := by
    funext ξ; rw [fejerCutoff]; ring
  have hsplit : ∀ u, 𝓕 fejerTestC u = 𝓕 (fejerCutoff Γ) u + tailTransform fejerTestC Γ u := by
    intro u
    rw [tailTransform, ← fourier_add_eq hi hi2, hfun]
  unfold deviationPairing
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n
  · have hz := fourier_fejerTestC_log_eq_zero hn
    have e1 := hsplit (Real.log n)
    have e2 := hsplit (-Real.log n)
    rw [hz.1] at e1
    rw [hz.2] at e2
    rw [show 𝓕 (fejerCutoff Γ) (Real.log n) = -tailTransform fejerTestC Γ (Real.log n) by
        linear_combination -e1,
      show 𝓕 (fejerCutoff Γ) (-Real.log n) = -tailTransform fejerTestC Γ (-Real.log n) by
        linear_combination -e2]
    ring
  · simp [weilDeviation, hn]

/-! ## Two complex inequalities -/

theorem neg_re_le_of_eq {P T R : ℂ} {Z : Finset ℝ} {Q : ℝ → ℂ}
    (h : -T = P + ∑ γ ∈ Z, Q γ + R) (hR : R.re ≤ 0) :
    -P.re ≤ ‖T‖ + ∑ γ ∈ Z, ‖Q γ‖ := by
  have hP := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.add_re, Complex.re_sum] at hP
  have h1 := Complex.re_le_norm T
  have h2 : ∑ γ ∈ Z, (Q γ).re ≤ ∑ γ ∈ Z, ‖Q γ‖ :=
    Finset.sum_le_sum fun γ _ => Complex.re_le_norm _
  linarith

theorem mul_le_of_eq_sub {P We Wv : ℂ} {c A e k : ℝ} (hP : P = We - Wv) (he : ‖We‖ ≤ e)
    (hv : ‖Wv - (c : ℂ) * (A : ℂ)‖ ≤ k) : c * A ≤ e + k - P.re := by
  have h1 := Complex.re_le_norm We
  have h2 := Complex.abs_re_le_norm (Wv - (c : ℂ) * (A : ℂ))
  have h3 : (Wv - (c : ℂ) * (A : ℂ)).re = Wv.re - c * A := by simp
  rw [h3] at h2
  have h4 := (abs_le.mp h2).1
  rw [hP, Complex.sub_re]
  linarith

/-! ## The mean-balance inequality -/

/-- The origin packet of the cut-off Fejér test is controlled by the tail and the zero packets. -/
theorem neg_re_originPairing_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) {D : ℝ}
    (hD : CauchyBounded (deviationDeficit lam) D)
    {Γ ε δ : ℝ} (hΓ : 0 < Γ) (hS : Separated (zeroWindow (2 * Γ)) δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    -(deviationPairing lam (𝓕 fun ξ => fejerCutoff Γ ξ * packet pdPacketC 0 δ ξ)).re ≤
      ‖deviationPairing lam (tailTransform fejerTestC Γ)‖ +
      ∑ γ ∈ zeroWindow (2 * Γ),
        ‖deviationPairing lam (𝓕 fun ξ => fejerCutoff Γ ξ * packet (flatPacketC ε) γ δ ξ)‖ := by
  obtain ⟨σ, hσf, hσ⟩ := exists_spectralMeasure hW
  have hdecomp := deviationPairing_packet_decomposition hexc hD (contDiff_fejerCutoff Γ)
    (hasCompactSupport_fejerCutoff hΓ) (zeroWindow (2 * Γ)) ε δ
  rw [deviationPairing_fourier_fejerCutoff lam hΓ] at hdecomp
  refine neg_re_le_of_eq hdecomp ?_
  have hs := contDiff_fejerCutoff Γ
  have hc := hasCompactSupport_fejerCutoff hΓ
  have hZ := mem_zeroWindow_of_mem_tsupport hΓ
  rw [fejerCutoff_eq_ofReal] at hs hc hZ ⊢
  exact re_deviationPairing_packetRemainder_nonpos hW hexc σ hσ (fejerCutoffReal_nonneg Γ) hs hc
    hS hε0 hε1 hZ

/-- If `P = W_e − W_v` with `W_e ≈ cE` and `W_v ≈ cA`, then `cA − cE ≤ k_e + k_v − Re P`. -/
theorem mul_sub_le_of_eq_sub {P We Wv : ℂ} {c A E ke kv : ℝ} (hP : P = We - Wv)
    (he : ‖We - (c : ℂ) * (E : ℂ)‖ ≤ ke) (hv : ‖Wv - (c : ℂ) * (A : ℂ)‖ ≤ kv) :
    c * A - c * E ≤ ke + kv - P.re := by
  have h1 := Complex.abs_re_le_norm (We - (c : ℂ) * (E : ℂ))
  have h2 := Complex.abs_re_le_norm (Wv - (c : ℂ) * (A : ℂ))
  have e1 : (We - (c : ℂ) * (E : ℂ)).re = We.re - c * E := by simp
  have e2 : (Wv - (c : ℂ) * (A : ℂ)).re = Wv.re - c * A := by simp
  rw [e1] at h1
  rw [e2] at h2
  rw [hP, Complex.sub_re]
  linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]

/-- **The mean-balance inequality at fixed parameters.** For the cut-off Fejér test at `Γ`, flat
packets of flatness `ε` and packets of width `δ`:
`(F(0) − 3/8) A_δ ≤ (F(0) + 3/8) E_δ +` tail `+ O(Nε) + O_ε(δ)`, where `N` is the number of zeros of
`Ξ` in `[−2Γ, 2Γ]`. -/
theorem exists_meanBalance_inequality {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) :
    ∃ K₀ K' : ℝ, 0 ≤ K₀ ∧ 0 ≤ K' ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Kε : ℝ, 0 ≤ Kε ∧
      ∀ Γ δ : ℝ, 0 < Γ → 0 < δ → δ ≤ 1 → Separated (zeroWindow (2 * Γ)) δ →
      (fejerTest 0 - 3 / 8) * deficitMean (deviationDeficit lam) δ ≤
        (fejerTest 0 + 3 / 8) * deficitMean (deviationExcess lam) δ +
        ‖deviationPairing lam (tailTransform fejerTestC Γ)‖ +
        2 * ((zeroWindow (2 * Γ)).card : ℝ) * K' * ε +
        (K₀ + ((zeroWindow (2 * Γ)).card : ℝ) * Kε) * δ *
          (∫ s, ‖𝓕 (fejerCutoff Γ) s‖ * (|s| * (1 + s ^ 2))) := by
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  have hv0 := deviationDeficit_nonneg lam
  have he0 := deviationExcess_nonneg lam
  obtain ⟨K₀v, hK₀v, hOPv⟩ := exists_originPacket_bound hv0 hD
  obtain ⟨K₀e, hK₀e, hOPe⟩ := exists_originPacket_bound he0 hexc
  obtain ⟨K'v, hK'v, hZPv⟩ := exists_zeroPacket_bound hv0 hD
  obtain ⟨K'e, hK'e, hZPe⟩ := exists_zeroPacket_bound he0 hexc
  refine ⟨K₀v + K₀e, K'v + K'e, add_nonneg hK₀v hK₀e, add_nonneg hK'v hK'e,
    fun ε hε0 hε1 => ?_⟩
  obtain ⟨Kεv, hKεv, hZPεv⟩ := hZPv hε0 hε1
  obtain ⟨Kεe, hKεe, hZPεe⟩ := hZPe hε0 hε1
  refine ⟨Kεv + Kεe, add_nonneg hKεv hKεe, fun Γ δ hΓ hδ0 hδ1 hS => ?_⟩
  have hs := contDiff_fejerCutoff Γ
  have hc := hasCompactSupport_fejerCutoff hΓ
  have hA0 := deficitMean_nonneg hv0 hD hδ0 hδ1
  have hE0 := deficitMean_nonneg he0 hexc hδ0 hδ1
  -- the origin packet
  obtain ⟨hvs₀, hv₀⟩ := hOPv hs hc hδ0 hδ1
  obtain ⟨hes₀, he₀⟩ := hOPe hs hc hδ0 hδ1
  rw [fejerCutoff_zero hΓ] at hv₀ he₀
  have h1 := mul_sub_le_of_eq_sub (deviationPairing_eq_sub hes₀ hvs₀) he₀ hv₀
  -- the decomposition
  have h2 := neg_re_originPairing_le hW hexc hD hΓ hS hε0 hε1
  -- the zero packets
  have hPγ : ∀ γ ∈ zeroWindow (2 * Γ),
      ‖deviationPairing lam (𝓕 fun ξ => fejerCutoff Γ ξ * packet (flatPacketC ε) γ δ ξ)‖ ≤
        ‖fejerCutoff Γ γ‖ * ((deficitMean (deviationDeficit lam) δ +
          deficitMean (deviationExcess lam) δ) + (K'v + K'e) * ε) +
        (Kεv + Kεe) * δ * ∫ s, ‖𝓕 (fejerCutoff Γ) s‖ * (|s| * (1 + s ^ 2)) := by
    intro γ _
    obtain ⟨hvsγ, hvγ⟩ := hZPεv hs hc γ hδ0 hδ1
    obtain ⟨hesγ, heγ⟩ := hZPεe hs hc γ hδ0 hδ1
    rw [deviationPairing_eq_sub hesγ hvsγ]
    have := norm_sub_le (weightPairing (deviationExcess lam)
      (𝓕 fun ξ => fejerCutoff Γ ξ * packet (flatPacketC ε) γ δ ξ))
      (weightPairing (deviationDeficit lam)
      (𝓕 fun ξ => fejerCutoff Γ ξ * packet (flatPacketC ε) γ δ ξ))
    linarith
  have h3 := Finset.sum_le_sum hPγ
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul] at h3
  -- the zero budget
  have hAE : 0 ≤ deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ :=
    add_nonneg hA0 hE0
  have h4 := mul_le_mul_of_nonneg_right (sum_norm_fejerCutoff_le Γ) hAE
  have h5 := mul_le_mul_of_nonneg_right (sum_norm_fejerCutoff_le_card Γ)
    (mul_nonneg (add_nonneg hK'v hK'e) hε0.le)
  have h6 := mul_add (∑ γ ∈ zeroWindow (2 * Γ), ‖fejerCutoff Γ γ‖)
    (deficitMean (deviationDeficit lam) δ + deficitMean (deviationExcess lam) δ)
    ((K'v + K'e) * ε)
  linarith

/-! ## Choice of parameters -/

theorem separated_of_separation {Z : Finset ℝ} (hZ : (0 : ℝ) ∉ Z) {d δ : ℝ}
    (hsep : ∀ p ∈ insert 0 Z, ∀ q ∈ insert 0 Z, p ≠ q → d ≤ |p - q|) (hδ0 : 0 < δ)
    (hδ : δ ≤ d / 4) : Separated Z δ := by
  refine ⟨hZ, hδ0, fun γ hγ => ?_, fun γ hγ γ' hγ' hne => ?_⟩
  · have hne : γ ≠ 0 := fun h => hZ (h ▸ hγ)
    have := hsep γ (Finset.mem_insert_of_mem hγ) 0 (Finset.mem_insert_self _ _) hne
    rw [sub_zero] at this
    linarith
  · have := hsep γ (Finset.mem_insert_of_mem hγ) γ' (Finset.mem_insert_of_mem hγ') hne
    linarith

theorem exists_small_width {C₁ C₂ η₁ d : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < η₁)
    (hd : 0 < d) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ δ₀ ≤ d / 4 ∧ C₁ * δ₀ ≤ η₁ ∧ C₂ * δ₀ ≤ η₁ := by
  have p1 : 0 < η₁ / (C₁ + 1) := div_pos hη (by linarith)
  have p2 : 0 < η₁ / (C₂ + 1) := div_pos hη (by linarith)
  refine ⟨min (min 1 (d / 4)) (min (η₁ / (C₁ + 1)) (η₁ / (C₂ + 1))),
    lt_min (lt_min one_pos (by linarith)) (lt_min p1 p2),
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_, ?_⟩
  · have h1 : min (min 1 (d / 4)) (min (η₁ / (C₁ + 1)) (η₁ / (C₂ + 1))) ≤ η₁ / (C₁ + 1) :=
      (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    have h2 : 0 ≤ min (min 1 (d / 4)) (min (η₁ / (C₁ + 1)) (η₁ / (C₂ + 1))) :=
      (lt_min (lt_min one_pos (by linarith)) (lt_min p1 p2)).le
    linarith
  · have h1 : min (min 1 (d / 4)) (min (η₁ / (C₁ + 1)) (η₁ / (C₂ + 1))) ≤ η₁ / (C₂ + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by linarith)] at h1
    have h2 : 0 ≤ min (min 1 (d / 4)) (min (η₁ / (C₁ + 1)) (η₁ / (C₂ + 1))) :=
      (lt_min (lt_min one_pos (by linarith)) (lt_min p1 p2)).le
    linarith

/-! ## Mean balance -/

/-- **Mean balance.** For a full-cone Weil-positive system with translation-bounded excess,
`(F(0) − 3/8) A_δ ≤ (F(0) + 3/8) E_δ + η` for all sufficiently small `δ`. -/
theorem meanBalance {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) :
    ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (fejerTest 0 - 3 / 8) * deficitMean (deviationDeficit lam) δ ≤
        (fejerTest 0 + 3 / 8) * deficitMean (deviationExcess lam) δ + η := by
  intro η hη
  obtain ⟨K₀, K', hK₀, hK', hineq⟩ := exists_meanBalance_inequality hW hexc
  obtain ⟨D, -, hD'⟩ := exists_tsum_deficit_cauchyProfile_le hW hexc
  have hD : CauchyBounded (deviationDeficit lam) D := hD'
  obtain ⟨η₁, hη₁0, hη₁⟩ : ∃ η₁ : ℝ, 0 < η₁ ∧ 3 * η₁ = η := ⟨η / 3, by positivity, by ring⟩
  -- the cut-off
  have htail := tendsto_deviationPairing_tail hexc hD (Φ := fejerTestC)
    contDiff_fejerTestC.continuous integrable_fejerTestC integrable_fourier_fejerTestC
    (b := 17 / 25) (by norm_num) (fun u hu => fourier_fejerTestC_eq_zero hu)
  obtain ⟨Γ₀, hΓ₀⟩ := (Metric.tendsto_atTop.mp htail) η₁ hη₁0
  obtain ⟨Γ, hΓ, hT⟩ : ∃ Γ : ℝ, 0 < Γ ∧
      ‖deviationPairing lam (tailTransform fejerTestC Γ)‖ < η₁ := by
    refine ⟨max Γ₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    have := hΓ₀ (max Γ₀ 1) (le_max_left _ _)
    rwa [dist_zero_right] at this
  -- the flatness
  have hN0 : (0 : ℝ) ≤ (zeroWindow (2 * Γ)).card := Nat.cast_nonneg _
  obtain ⟨ε, hε0, hε1, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      2 * ((zeroWindow (2 * Γ)).card : ℝ) * K' * ε ≤ η₁ := by
    have hC : 0 ≤ 2 * ((zeroWindow (2 * Γ)).card : ℝ) * K' := by positivity
    obtain ⟨δ₀, h0, h1, -, h3, -⟩ := exists_small_width hC hC hη₁0 one_pos
    exact ⟨δ₀, h0, h1, h3⟩
  obtain ⟨Kε, hKε, hineqε⟩ := hineq ε hε0 hε1
  -- the width
  obtain ⟨d, hd, hsep⟩ := exists_separation (insert 0 (zeroWindow (2 * Γ)))
  have hM := moment_nonneg (fejerCutoff Γ)
  have hC₁ : 0 ≤ (K₀ + ((zeroWindow (2 * Γ)).card : ℝ) * Kε) *
      ∫ s, ‖𝓕 (fejerCutoff Γ) s‖ * (|s| * (1 + s ^ 2)) :=
    mul_nonneg (add_nonneg hK₀ (mul_nonneg hN0 hKε)) hM
  obtain ⟨δ₀, hδ₀, hδ₀1, hδ₀d, hδ₀C₁, -⟩ := exists_small_width hC₁ hC₁ hη₁0 hd
  refine ⟨δ₀, hδ₀, fun δ hδ0 hδ => ?_⟩
  have hS := separated_of_separation (zero_notMem_zeroWindow (2 * Γ)) hsep hδ0 (hδ.trans hδ₀d)
  have key := hineqε Γ δ hΓ hδ0 (hδ.trans hδ₀1) hS
  have e1 := (mul_le_mul_of_nonneg_left hδ hC₁).trans hδ₀C₁
  linarith

/-- The excess mean tends to zero. -/
def ExcessMeanVanishes (lam : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    deficitMean (deviationExcess lam) δ ≤ η

/-- A summable excess has vanishing mean. -/
theorem excessMeanVanishes_of_summable {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam)) :
    ExcessMeanVanishes lam := by
  intro η hη
  set E := ∑' n, deviationExcess lam n with hE
  have hE0 : 0 ≤ E := tsum_nonneg (deviationExcess_nonneg lam)
  set BG := ∫ x, ‖pdPacketC x‖ with hBG
  have hBG0 : 0 ≤ BG := integral_nonneg fun _ => norm_nonneg _
  refine ⟨η / (2 * BG * E + 1), div_pos hη (by positivity), fun δ hδ0 hδ => ?_⟩
  obtain ⟨-, hle⟩ := norm_weightPairing_excess_packet_le (deviationExcess_nonneg lam) hexc
    (h := fun _ => (1 : ℂ)) (B := pdPacketC) (γ := 0) (H := 1) (fun _ => by simp)
    (continuous_const.mul (contDiff_packet contDiff_pdPacketC 0 δ).continuous)
    integrable_pdPacketC hδ0
  have hfun : (fun ξ => (fun _ => (1 : ℂ)) ξ * packet pdPacketC 0 δ ξ) = packet pdPacketC 0 δ := by
    funext ξ; simp
  rw [hfun] at hle
  have h1 : deficitMean (deviationExcess lam) δ ≤ 2 * (1 * (δ * BG)) * E :=
    (Complex.re_le_norm _).trans hle
  rw [le_div_iff₀ (by positivity)] at hδ
  nlinarith [mul_nonneg hBG0 hE0]

/-- **The deficit mean vanishes** when the excess mean does. -/
theorem tendsto_deficitMean {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ) (hmean : ExcessMeanVanishes lam) :
    ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      deficitMean (deviationDeficit lam) δ ≤ η := by
  intro η hη
  have hF0 : 3 / 8 < fejerTest 0 := three_eighths_lt_fejerTest_zero
  have hc : 0 < fejerTest 0 - 3 / 8 := sub_pos.mpr hF0
  have hc' : 0 < fejerTest 0 + 3 / 8 := by linarith
  obtain ⟨δ₁, hδ₁, hB⟩ := meanBalance hW hexc ((fejerTest 0 - 3 / 8) * η / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hE⟩ := hmean ((fejerTest 0 - 3 / 8) * η / (2 * (fejerTest 0 + 3 / 8)))
    (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun δ hδ0 hδ => ?_⟩
  have h1 := hB δ hδ0 (hδ.trans (min_le_left _ _))
  have h2 := hE δ hδ0 (hδ.trans (min_le_right _ _))
  rw [le_div_iff₀ (by positivity)] at h2
  have h4 : (fejerTest 0 - 3 / 8) * deficitMean (deviationDeficit lam) δ ≤
      (fejerTest 0 - 3 / 8) * η := by linarith
  exact le_of_mul_le_mul_left h4 hc

end

end RHTower.WeilExcess
