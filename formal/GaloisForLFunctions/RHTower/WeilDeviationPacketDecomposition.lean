import GaloisForLFunctions.RHTower.WeilDeviationPacketEstimates

/-!
# The packet decomposition of a test function

Let `h` be smooth and compactly supported, `Z'` a finite set containing every real zero of `Ξ` in
the support of `h`, with `0 ∉ Z'`, and let `δ` be smaller than a quarter of the separation of
`Z' ∪ {0}`. Put
- `P₀ = G((·)/δ)`, the positive-definite packet at the origin;
- `P_γ = β_ε((· − γ)/δ)`, the flattened packets at the zeros `γ ∈ Z'`;
- `R = h (1 − P₀ − Σ_γ P_γ)`.

Then:
- `h = h P₀ + Σ_γ h P_γ + R`;
- `R` vanishes on a neighbourhood of every zero of `Ξ` (`remainder_eventuallyEq_zero`), because
  `β_ε = 1` near `0` and the packets have disjoint supports;
- `0 ≤ R` when `h ≥ 0`, because the packets take values in `[0, 1]` and are disjoint.

Near-null positivity then applies to the remainder.
-/

open Complex MeasureTheory Filter Topology Set FourierTransform
open scoped Real ComplexConjugate ContDiff

namespace RHTower.WeilExcess

noncomputable section

/-! ## Finite sums -/

theorem fourier_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ s, Integrable (f i)) (u : ℝ) :
    𝓕 (fun ξ => ∑ i ∈ s, f i ξ) u = ∑ i ∈ s, 𝓕 (f i) u := by
  simp only [fourier_eq_integral, Finset.mul_sum]
  exact integral_finsetSum _ fun i hi => integrable_exp_mul (hf i hi) u

theorem deviationPairing_finset_sum {lam : ℕ → ℝ} {ι : Type*} (s : Finset ι) {φ : ι → ℝ → ℂ}
    (hφ : ∀ i ∈ s, Summable fun n : ℕ => (weilDeviation lam n : ℂ) *
      (φ i (Real.log n) + φ i (-Real.log n))) :
    deviationPairing lam (fun u => ∑ i ∈ s, φ i u) = ∑ i ∈ s, deviationPairing lam (φ i) := by
  unfold deviationPairing
  rw [← Summable.tsum_finsetSum hφ]
  refine tsum_congr fun n => ?_
  simp only
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

theorem deviationPairing_add {lam : ℕ → ℝ} {φ ψ : ℝ → ℂ}
    (hφ : Summable fun n : ℕ => (weilDeviation lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n)))
    (hψ : Summable fun n : ℕ => (weilDeviation lam n : ℂ) * (ψ (Real.log n) + ψ (-Real.log n))) :
    deviationPairing lam (fun u => φ u + ψ u) = deviationPairing lam φ + deviationPairing lam ψ := by
  unfold deviationPairing
  rw [← Summable.tsum_add hφ hψ]
  exact tsum_congr fun n => by ring

/-- Summability of the deviation pairing from the two weight pairings. -/
theorem summable_deviation_of {lam : ℕ → ℝ} {φ : ℝ → ℂ}
    (he : Summable fun n : ℕ => (deviationExcess lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n)))
    (hv : Summable fun n : ℕ => (deviationDeficit lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n))) :
    Summable fun n : ℕ => (weilDeviation lam n : ℂ) * (φ (Real.log n) + φ (-Real.log n)) :=
  (he.sub hv).congr fun n => by rw [weilDeviation_eq_sub]; push_cast; ring

/-! ## Separation of finite sets -/

theorem exists_separation (T : Finset ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → d ≤ |p - q| := by
  classical
  set P := (T ×ˢ T).filter fun pq => pq.1 ≠ pq.2 with hP
  rcases P.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun p hp q hq hpq => ?_⟩
    have : (p, q) ∈ P := by simp [hP, hp, hq, hpq]
    rw [hE] at this; simp at this
  · obtain ⟨pq₀, hpq₀, hmin⟩ := P.exists_min_image (fun pq => |pq.1 - pq.2|) hne
    have hpos : 0 < |pq₀.1 - pq₀.2| := by
      have h := (Finset.mem_filter.mp hpq₀).2
      exact abs_pos.mpr (sub_ne_zero.mpr h)
    refine ⟨_, hpos, fun p hp q hq hpq => ?_⟩
    exact hmin (p, q) (by simp [hP, hp, hq, hpq])

/-! ## Packet supports -/

theorem pdPacketC_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : pdPacketC x = 0 := by
  simp [pdPacketC, pdPacket_eq_zero_of_two_le hx]

theorem flatPacketC_eq_zero {ε x : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hx : 2 ≤ |x|) :
    flatPacketC ε x = 0 := by
  simp [flatPacketC, excessFlatPacket_eq_zero hε0 hε hx]

theorem packet_eq_zero_of_far {B : ℝ → ℂ} (hB : ∀ x, 2 ≤ |x| → B x = 0) {γ δ ξ : ℝ}
    (hδ : 0 < δ) (hξ : 2 * δ ≤ |ξ - γ|) : packet B γ δ ξ = 0 := by
  apply hB
  rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
  linarith

/-! ## Summability for smooth tests -/

/-- The deviation pairing with the transform of any smooth compactly supported function is
absolutely convergent. -/
theorem summable_deviation_fourier_smooth {lam : ℕ → ℝ} {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ)
    {D : ℝ} (hD : CauchyBounded (deviationDeficit lam) D) {f : ℝ → ℂ} (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    Summable fun n : ℕ => (weilDeviation lam n : ℂ) * (𝓕 f (Real.log n) + 𝓕 f (-Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_fourier_profile_smooth hs hc
  have hprof : ∀ u, ‖𝓕 f u‖ ≤ C * cauchyProfile 1 0 u := fun u => by
    rw [cauchyProfile_one_zero]; exact (hC u).trans (le_of_eq (by ring))
  exact summable_deviation_of
    (summable_weightPairing_of_profile (deviationExcess_nonneg lam) hexc one_pos le_rfl hprof).1
    (summable_weightPairing_of_profile (deviationDeficit_nonneg lam) hD one_pos le_rfl hprof).1

/-! ## The packet remainder -/

/-- The real packet sum `P₀ + Σ_{γ ∈ Z} P_γ`. -/
def packetSumReal (Z : Finset ℝ) (ε δ ξ : ℝ) : ℝ :=
  pdPacket ((ξ - 0) / δ) + ∑ γ ∈ Z, excessFlatPacket ε ((ξ - γ) / δ)

/-- The remainder `R = h (1 − P₀ − Σ_γ P_γ)`. -/
def packetRemainder (h : ℝ → ℂ) (Z : Finset ℝ) (ε δ ξ : ℝ) : ℂ :=
  h ξ * ((1 - packetSumReal Z ε δ ξ : ℝ) : ℂ)

/-- A separated configuration: the origin and the zeros in `Z` are `4δ`-separated. -/
structure Separated (Z : Finset ℝ) (δ : ℝ) : Prop where
  zero_notMem : (0 : ℝ) ∉ Z
  pos : 0 < δ
  sep_zero : ∀ γ ∈ Z, 4 * δ ≤ |γ|
  sep : ∀ γ ∈ Z, ∀ γ' ∈ Z, γ ≠ γ' → 4 * δ ≤ |γ - γ'|

theorem pdPacket_packet_eq_zero {δ ξ : ℝ} (hδ : 0 < δ) (hξ : 2 * δ ≤ |ξ - 0|) :
    pdPacket ((ξ - 0) / δ) = 0 := by
  apply pdPacket_eq_zero_of_two_le
  rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]; linarith

theorem flatPacket_packet_eq_zero {ε δ ξ γ : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1) (hδ : 0 < δ)
    (hξ : 2 * δ ≤ |ξ - γ|) : excessFlatPacket ε ((ξ - γ) / δ) = 0 := by
  apply excessFlatPacket_eq_zero hε0 hε
  rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]; linarith

/-- **At most one packet is active.** -/
theorem packetSumReal_le_one {Z : Finset ℝ} {δ ε : ℝ} (hS : Separated Z δ) (hε0 : 0 < ε)
    (hε : ε ≤ 1) (ξ : ℝ) : packetSumReal Z ε δ ξ ≤ 1 := by
  classical
  have hδ := hS.pos
  unfold packetSumReal
  by_cases h0 : |ξ - 0| < 2 * δ
  · -- only the origin packet
    have hz : ∀ γ ∈ Z, excessFlatPacket ε ((ξ - γ) / δ) = 0 := by
      intro γ hγ
      apply flatPacket_packet_eq_zero hε0 hε hδ
      have := hS.sep_zero γ hγ
      have h1 : |γ| ≤ |ξ - γ| + |ξ - 0| := by
        calc |γ| = |(ξ - 0) - (ξ - γ)| := by ring_nf
          _ ≤ |ξ - 0| + |ξ - γ| := abs_sub _ _
          _ = _ := by ring
      linarith
    rw [Finset.sum_eq_zero hz, add_zero]
    exact pdPacket_le_one _
  · push Not at h0
    rw [pdPacket_packet_eq_zero hδ h0, zero_add]
    by_cases hex : ∃ γ ∈ Z, |ξ - γ| < 2 * δ
    · obtain ⟨γ₀, hγ₀, hξγ₀⟩ := hex
      rw [← Finset.add_sum_erase Z _ hγ₀]
      have hz : ∀ γ ∈ Z.erase γ₀, excessFlatPacket ε ((ξ - γ) / δ) = 0 := by
        intro γ hγ
        obtain ⟨hne, hγ⟩ := Finset.mem_erase.mp hγ
        apply flatPacket_packet_eq_zero hε0 hε hδ
        have := hS.sep γ hγ γ₀ hγ₀ hne
        have h1 : |γ - γ₀| ≤ |ξ - γ| + |ξ - γ₀| := by
          calc |γ - γ₀| = |(ξ - γ₀) - (ξ - γ)| := by ring_nf
            _ ≤ |ξ - γ₀| + |ξ - γ| := abs_sub _ _
            _ = _ := by ring
        linarith
      rw [Finset.sum_eq_zero hz, add_zero]
      exact excessFlatPacket_le_one _ _
    · push Not at hex
      rw [Finset.sum_eq_zero fun γ hγ => flatPacket_packet_eq_zero hε0 hε hδ (hex γ hγ)]
      norm_num

theorem packetSumReal_nonneg (Z : Finset ℝ) (ε δ ξ : ℝ) : 0 ≤ packetSumReal Z ε δ ξ :=
  add_nonneg (pdPacket_nonneg _) (Finset.sum_nonneg fun _ _ => excessFlatPacket_nonneg _ _)

/-- **The remainder vanishes near every zero of `Ξ`.** -/
theorem remainder_eventuallyEq_zero {h : ℝ → ℂ} {Z : Finset ℝ} {δ ε : ℝ} (hS : Separated Z δ)
    (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ Z) {ξ₀ : ℝ} (hξ₀ : riemannXi ξ₀ = 0) :
    packetRemainder h Z ε δ =ᶠ[𝓝 ξ₀] 0 := by
  classical
  have hδ := hS.pos
  by_cases ht : ξ₀ ∈ tsupport h
  · have hmem := hZ ξ₀ ht hξ₀
    have hball : Metric.ball ξ₀ (ε * δ) ∈ 𝓝 ξ₀ := Metric.ball_mem_nhds _ (mul_pos hε0 hδ)
    filter_upwards [hball] with ξ hξ
    rw [Metric.mem_ball, Real.dist_eq] at hξ
    have hεδ : ε * δ ≤ δ := by nlinarith
    have hone : excessFlatPacket ε ((ξ - ξ₀) / δ) = 1 := by
      apply excessFlatPacket_eq_one hε0
      rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]; linarith
    have hothers : ∀ γ ∈ Z.erase ξ₀, excessFlatPacket ε ((ξ - γ) / δ) = 0 := by
      intro γ hγ
      obtain ⟨hne, hγ⟩ := Finset.mem_erase.mp hγ
      apply flatPacket_packet_eq_zero hε0 hε hδ
      have := hS.sep γ hγ ξ₀ hmem hne
      have h1 : |γ - ξ₀| ≤ |ξ - γ| + |ξ - ξ₀| := by
        calc |γ - ξ₀| = |(ξ - ξ₀) - (ξ - γ)| := by ring_nf
          _ ≤ |ξ - ξ₀| + |ξ - γ| := abs_sub _ _
          _ = _ := by ring
      linarith
    have horigin : pdPacket ((ξ - 0) / δ) = 0 := by
      apply pdPacket_packet_eq_zero hδ
      have := hS.sep_zero ξ₀ hmem
      have h1 : |ξ₀| ≤ |ξ - 0| + |ξ - ξ₀| := by
        calc |ξ₀| = |(ξ - 0) - (ξ - ξ₀)| := by ring_nf
          _ ≤ |ξ - 0| + |ξ - ξ₀| := abs_sub _ _
      linarith
    simp only [Pi.zero_apply, packetRemainder, packetSumReal, horigin, zero_add]
    rw [← Finset.add_sum_erase Z _ hmem, Finset.sum_eq_zero hothers, hone]
    simp
  · have hev : h =ᶠ[𝓝 ξ₀] 0 := notMem_tsupport_iff_eventuallyEq.mp ht
    filter_upwards [hev] with ξ hξ
    simp [packetRemainder, hξ]

theorem contDiff_packetSumReal (Z : Finset ℝ) (ε δ : ℝ) : ContDiff ℝ ∞ (packetSumReal Z ε δ) := by
  unfold packetSumReal
  exact (contDiff_pdPacket.comp ((contDiff_id.sub contDiff_const).div_const δ)).add
    (ContDiff.sum fun γ _ => (contDiff_excessFlatPacket ε).comp
      ((contDiff_id.sub contDiff_const).div_const δ))

theorem contDiff_packetRemainder {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h) (Z : Finset ℝ) (ε δ : ℝ) :
    ContDiff ℝ ∞ (packetRemainder h Z ε δ) :=
  hs.mul (ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_packetSumReal Z ε δ)))

theorem hasCompactSupport_packetRemainder {h : ℝ → ℂ} (hc : HasCompactSupport h)
    (Z : Finset ℝ) (ε δ : ℝ) : HasCompactSupport (packetRemainder h Z ε δ) :=
  hc.mul_right

/-- **The packet decomposition of `h`.** -/
theorem eq_packet_decomposition (h : ℝ → ℂ) (Z : Finset ℝ) (ε δ ξ : ℝ) :
    h ξ = h ξ * packet pdPacketC 0 δ ξ + ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ +
      packetRemainder h Z ε δ ξ := by
  simp only [packetRemainder, packetSumReal, packet, pdPacketC, flatPacketC]
  rw [← Finset.mul_sum]
  push_cast
  ring

/-! ## The pairing decomposition -/

theorem contDiff_flatPacketC (ε : ℝ) : ContDiff ℝ ∞ (flatPacketC ε) :=
  ofRealCLM.contDiff.comp (contDiff_excessFlatPacket ε)

theorem contDiff_mul_packet {h B : ℝ → ℂ} (hs : ContDiff ℝ ∞ h) (hB : ContDiff ℝ ∞ B) (γ δ : ℝ) :
    ContDiff ℝ ∞ fun ξ => h ξ * packet B γ δ ξ :=
  hs.mul (contDiff_packet hB γ δ)

theorem integrable_of_smooth {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hfc

/-- The transform splits along the packet decomposition. -/
theorem fourier_packet_decomposition {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (Z : Finset ℝ) (ε δ u : ℝ) :
    𝓕 h u = 𝓕 (fun ξ => h ξ * packet pdPacketC 0 δ ξ) u +
      ∑ γ ∈ Z, 𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) u +
      𝓕 (packetRemainder h Z ε δ) u := by
  have i₀ : Integrable fun ξ => h ξ * packet pdPacketC 0 δ ξ :=
    integrable_of_smooth (contDiff_mul_packet hs contDiff_pdPacketC 0 δ) hc.mul_right
  have iγ : ∀ γ ∈ Z, Integrable fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ := fun γ _ =>
    integrable_of_smooth (contDiff_mul_packet hs (contDiff_flatPacketC ε) γ δ) hc.mul_right
  have iR : Integrable (packetRemainder h Z ε δ) :=
    integrable_of_smooth (contDiff_packetRemainder hs Z ε δ)
      (hasCompactSupport_packetRemainder hc Z ε δ)
  have iS : Integrable fun ξ => ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ :=
    integrable_finsetSum _ iγ
  have i1 : Integrable fun ξ => h ξ * packet pdPacketC 0 δ ξ +
      ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ := i₀.add iS
  have e : h = fun ξ => (h ξ * packet pdPacketC 0 δ ξ +
      ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ) + packetRemainder h Z ε δ ξ :=
    funext fun ξ => eq_packet_decomposition h Z ε δ ξ
  calc 𝓕 h u = 𝓕 (fun ξ => (h ξ * packet pdPacketC 0 δ ξ +
        ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ) + packetRemainder h Z ε δ ξ) u := by
        rw [← e]
    _ = 𝓕 (fun ξ => h ξ * packet pdPacketC 0 δ ξ +
        ∑ γ ∈ Z, h ξ * packet (flatPacketC ε) γ δ ξ) u + 𝓕 (packetRemainder h Z ε δ) u :=
        fourier_add_eq i1 iR u
    _ = _ := by rw [fourier_add_eq i₀ iS u, fourier_finset_sum Z iγ u]

/-- **The deviation pairing splits along the packet decomposition.** -/
theorem deviationPairing_packet_decomposition {lam : ℕ → ℝ} {Dₑ : ℝ}
    (hexc : CauchyBounded (deviationExcess lam) Dₑ)
    {D : ℝ} (hD : CauchyBounded (deviationDeficit lam) D) {h : ℝ → ℂ} (hs : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport h) (Z : Finset ℝ) (ε δ : ℝ) :
    deviationPairing lam (𝓕 h) =
      deviationPairing lam (𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ) +
      ∑ γ ∈ Z, deviationPairing lam (𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) +
      deviationPairing lam (𝓕 (packetRemainder h Z ε δ)) := by
  have sm₀ := summable_deviation_fourier_smooth hexc hD
    (contDiff_mul_packet hs contDiff_pdPacketC 0 δ) hc.mul_right
  have smγ : ∀ γ ∈ Z, Summable fun n : ℕ => (weilDeviation lam n : ℂ) *
      (𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) (Real.log n) +
        𝓕 (fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ) (-Real.log n)) := fun γ _ =>
    summable_deviation_fourier_smooth hexc hD
      (contDiff_mul_packet hs (contDiff_flatPacketC ε) γ δ) hc.mul_right
  have smR := summable_deviation_fourier_smooth hexc hD (contDiff_packetRemainder hs Z ε δ)
    (hasCompactSupport_packetRemainder hc Z ε δ)
  set φ₀ := 𝓕 fun ξ => h ξ * packet pdPacketC 0 δ ξ with hφ₀
  set φ : ℝ → ℝ → ℂ := fun γ => 𝓕 fun ξ => h ξ * packet (flatPacketC ε) γ δ ξ with hφ
  set φR := 𝓕 (packetRemainder h Z ε δ) with hφR
  have hF : 𝓕 h = fun u => (φ₀ u + ∑ γ ∈ Z, φ γ u) + φR u :=
    funext fun u => fourier_packet_decomposition hs hc Z ε δ u
  have smS : Summable fun n : ℕ => (weilDeviation lam n : ℂ) *
      ((∑ γ ∈ Z, φ γ (Real.log n)) + ∑ γ ∈ Z, φ γ (-Real.log n)) :=
    (summable_sum smγ).congr fun n => by rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have sm₀S : Summable fun n : ℕ => (weilDeviation lam n : ℂ) *
      ((φ₀ (Real.log n) + ∑ γ ∈ Z, φ γ (Real.log n)) +
        (φ₀ (-Real.log n) + ∑ γ ∈ Z, φ γ (-Real.log n))) :=
    (sm₀.add smS).congr fun n => by ring
  have e1 := deviationPairing_add (lam := lam) (φ := fun u => φ₀ u + ∑ γ ∈ Z, φ γ u) (ψ := φR)
    sm₀S smR
  have e2 := deviationPairing_add (lam := lam) (φ := φ₀) (ψ := fun u => ∑ γ ∈ Z, φ γ u) sm₀ smS
  have e3 := deviationPairing_finset_sum (lam := lam) Z (φ := φ) smγ
  rw [hF, e1, e2, e3]

/-- **Near-null positivity for the remainder.** -/
theorem deviationPairing_packetRemainder {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : ∀ t, charFun σ t = ((-deviationPotential lam t : ℝ) : ℂ)) {h : ℝ → ℂ}
    (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {Z : Finset ℝ} {δ ε : ℝ}
    (hS : Separated Z δ) (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hZ : ∀ ξ ∈ tsupport h, riemannXi ξ = 0 → ξ ∈ Z) :
    deviationPairing lam (𝓕 (packetRemainder h Z ε δ)) =
      -∫ t, divRiemannXiSq (packetRemainder h Z ε δ) (t / (2 * π)) ∂σ := by
  set R := packetRemainder h Z ε δ with hR
  have hvan : ∀ ξ, riemannXi ξ = 0 → R =ᶠ[𝓝 ξ] 0 := fun ξ hξ =>
    remainder_eventuallyEq_zero hS hε0 hε hZ hξ
  have hsR := contDiff_packetRemainder hs Z ε δ
  have hcR := hasCompactSupport_packetRemainder hc Z ε δ
  have hgs := contDiff_divRiemannXiSq hsR hvan
  have hgc := hasCompactSupport_divRiemannXiSq hcR
  have hRg : (fun ξ => riemannXi ξ ^ 2 * divRiemannXiSq R ξ) = R :=
    funext (riemannXi_sq_mul_divRiemannXiSq fun ξ hξ => (hvan ξ hξ).eq_of_nhds)
  have key := deviationPairing_fourier_riemannXi_sq_mul hW hexc σ hσ hgs.continuous
    (hgs.continuous.integrable_of_hasCompactSupport hgc) (integrable_fourier_smooth hgs hgc)
  rw [hRg] at key
  exact key

/-- For a nonnegative real amplitude, the remainder pairs nonpositively. -/
theorem re_deviationPairing_packetRemainder_nonpos {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {Dₑ : ℝ} (hexc : CauchyBounded (deviationExcess lam) Dₑ) (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hσ : ∀ t, charFun σ t = ((-deviationPotential lam t : ℝ) : ℂ)) {r : ℝ → ℝ}
    (hr0 : ∀ ξ, 0 ≤ r ξ) (hs : ContDiff ℝ ∞ fun ξ => (r ξ : ℂ))
    (hc : HasCompactSupport fun ξ => (r ξ : ℂ)) {Z : Finset ℝ} {δ ε : ℝ}
    (hS : Separated Z δ) (hε0 : 0 < ε) (hε : ε ≤ 1)
    (hZ : ∀ ξ ∈ tsupport (fun ξ => (r ξ : ℂ)), riemannXi ξ = 0 → ξ ∈ Z) :
    (deviationPairing lam (𝓕 (packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ))).re ≤ 0 := by
  rw [deviationPairing_packetRemainder hW hexc σ hσ hs hc hS hε0 hε hZ]
  set R := packetRemainder (fun ξ => (r ξ : ℂ)) Z ε δ with hR
  have hvan : ∀ ξ, riemannXi ξ = 0 → R =ᶠ[𝓝 ξ] 0 := fun ξ hξ =>
    remainder_eventuallyEq_zero hS hε0 hε hZ hξ
  have hgs := contDiff_divRiemannXiSq (contDiff_packetRemainder hs Z ε δ) hvan
  have hgc := hasCompactSupport_divRiemannXiSq (hasCompactSupport_packetRemainder hc Z ε δ)
  -- the quotient is real and nonnegative
  have hreal : ∀ ξ, divRiemannXiSq R ξ =
      ((r ξ * (1 - packetSumReal Z ε δ ξ) / riemannXiReal ξ ^ 2 : ℝ) : ℂ) := by
    intro ξ
    simp only [divRiemannXiSq, hR, packetRemainder, riemannXi_eq_ofReal]
    push_cast; ring
  have hnn : ∀ ξ, 0 ≤ r ξ * (1 - packetSumReal Z ε δ ξ) / riemannXiReal ξ ^ 2 := fun ξ =>
    div_nonneg (mul_nonneg (hr0 ξ) (by linarith [packetSumReal_le_one hS hε0 hε ξ]))
      (sq_nonneg _)
  have hint : Integrable (fun t => divRiemannXiSq R (t / (2 * π))) σ := by
    obtain ⟨C, hC⟩ := (hgs.continuous.norm.bddAbove_range_of_hasCompactSupport hgc.norm)
    refine (integrable_const C).mono' ((hgs.continuous.comp (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun t => hC ⟨_, rfl⟩)
  rw [Complex.neg_re, neg_nonpos,
    show (∫ t, divRiemannXiSq R (t / (2 * π)) ∂σ).re =
      ∫ t, (divRiemannXiSq R (t / (2 * π))).re ∂σ from (integral_re hint).symm]
  refine integral_nonneg fun t => ?_
  rw [hreal]
  simp only [Complex.ofReal_re]
  exact hnn _

end

end RHTower.WeilExcess
