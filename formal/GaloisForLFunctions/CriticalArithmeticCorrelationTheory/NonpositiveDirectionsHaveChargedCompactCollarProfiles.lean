import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WholeSpaceGardingRetainsThePolarChannel

/-!
# Charged compact collar profiles

A nonpositive whole-space direction has a nonzero joint collar-and-pole mass.
Gårding controls the collar's weighted mass, Lévy energy, and discrete seventh
mass. The sharp comparison retains the actual pole diagonal and its collar pairing.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Every nonzero nonpositive direction supplies a charged collar with uniform compactness
bounds and an arbitrarily accurate energy inequality retaining its literal pole coordinate. -/
theorem exists_critical_charged_collar_weilQuad_bridge
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ K_W K_L K_S K_Q : ℝ, 0 < K_W ∧ 0 < K_L ∧ 0 < K_S ∧ 0 < K_Q ∧
    ∀ {ε : ℝ}, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
      completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0 →
      ∃ (τ : ℝ) (w : EuclideanSpace ℝ (PrimeHorizonIndex N)),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let M := N / linearDefectCutoff (c N)
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
        let J := (∫ u, U u ^ 2) + τ ^ 2 / Real.log N
        0 < J ∧
        (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W * J ∧
        levyEnergy U ≤ K_L * J ∧
        topCollarSeventhMass M N (primeHorizonExtension w) ≤ K_S * J ∧
        weilQuad U ≤ K_Q * J ∧
        weilQuad U + ((∫ u, tiltedUnitSpline u ^ 2) / c N) *
          (completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * τ ^ 2 +
            2 * τ * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫) ≤ ε * J := by
  obtain ⟨c_W, B, C₀, hcW, hB, hC₀, hG⟩ :=
    exists_critical_wholeSpace_garding_and_polar_bridge hc hR hcrit
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  let B' := B + C₀
  have hB' : 0 < B' := add_pos hB hC₀
  let K_W := (R + 1) * B' / c_W
  let K_L := 4 * I₂ * B'
  let K_S := 128 * B' * (R + 1) / dyadicTopMassConstant
  let H := 2 * I₂ * B' + K_W + K_L + 1
  let K_Q := 3 * I₂ * B' + H
  have hKW : 0 < K_W := by dsimp only [K_W]; positivity
  have hKL : 0 < K_L := by dsimp only [K_L]; positivity
  have hKS : 0 < K_S := by dsimp only [K_S]; exact div_pos (by positivity) dyadicTopMassConstant_pos
  have hH : 0 < H := by dsimp only [H]; positivity
  have hKQ : 0 < K_Q := by dsimp only [K_Q]; positivity
  refine ⟨K_W, K_L, K_S, K_Q, hKW, hKL, hKS, hKQ, fun {ε} hε => ?_⟩
  let e := ε / (16 * I₂ * B')
  let η := ε / (4 * I₂ * B')
  let δ := ε / (2 * (H + ε))
  have he0 : 0 < e := by dsimp only [e]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (by dsimp only [H]; positivity : 0 < 2 * (H + ε))).mpr
    linarith only [hH, hε]
  have hδH : δ * H ≤ ε / 2 := by
    have hh : H / (H + ε) ≤ 1 := (div_le_one (by positivity)).mpr
      (le_add_of_nonneg_right hε.le)
    calc
      δ * H = (ε / 2) * (H / (H + ε)) := by dsimp only [δ]; ring
      _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = ε / 2 := mul_one _
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hG he0 hη, eventually_poleOrthogonal_collar_weilQuad_bridge
      (show 0 < R + 1 by linarith) hδ,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hQlim.eventually_ge_atTop 1]
    with N hGN hbridgeN hratio hL1 hQge x hne hnonpos
  let Q := lowPacketCutoff N
  let y := (conductorSubspace Q N).starProjection x
  let z := x - y
  have hy : y ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQge)
  have hz : z ∈ (conductorSubspace Q N)ᗮ := sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨b, _, hb⟩ := mem_conductorSubspace_iff.mp hy
  have hx : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z = x := by
    rw [← hb]; dsimp only [z]; abel
  obtain ⟨w, hw, hg, he, hsharp⟩ := hGN b z hz
  refine ⟨b 1, w, hw, ?_⟩
  let L := Real.log (N : ℝ)
  let M := N / linearDefectCutoff (c N)
  let U := normalizedCentredAtomicTest tiltedUnitSpline
    (atomicTailCoefficients M (primeHorizonExtension w)) (c N) N
  let P := (L / (64 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5)) *
    (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2)
  let S := (dyadicTopMassConstant * L / (128 * c N ^ 7)) *
    topCollarSeventhMass M N (primeHorizonExtension w)
  let A := (∑ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline (c N) m * b m ^ 2)
  let U₂ := ∫ u, U u ^ 2
  let W₈ := ∫ u, U u ^ 2 * Real.exp (-(8 * u))
  let J := U₂ + b 1 ^ 2 / L
  have hβ : 0 ≤ b 1 ^ 2 / L := div_nonneg (sq_nonneg _) (zero_lt_one.trans_le hL1).le
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hℓ : 0 < 1 + Real.log L := by have := Real.log_nonneg hL1; positivity
  have hD := explicitConductorCutoffConstant_pos
  have hdyad := dyadicTopMassConstant_pos
  have hκ := tiltedSplineSpectralFloorConstant_pos
  have hA : 0 ≤ A := sum_nonneg fun m hm => mul_nonneg
    (completedConductorEnergy_tilted_pos hc0 (mem_Icc.mp hm).1).le (sq_nonneg _)
  have hP : 0 ≤ P := by
    have hh : 0 ≤ ∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    dsimp only [P]; positivity
  have hS : 0 ≤ S := by
    have hh := topCollarSeventhMass_nonneg M N (primeHorizonExtension w)
    dsimp only [S]; positivity
  have hU₂ : 0 ≤ U₂ := integral_nonneg fun _ => sq_nonneg _
  have hW₈ : 0 ≤ W₈ := integral_nonneg fun _ => by positivity
  have hlev := levyEnergy_nonneg' U
  have hnorm : 0 ≤ (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 := by positivity
  change (1 / 4 : ℝ) * A + (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 + P + S +
      (c N * c_W / (R + 1)) * W₈ + (c N / (4 * I₂)) * levyEnergy U ≤
    completeWeilEnergy tiltedUnitSpline (c N) N
      ((∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z) + (c N * B) * U₂ + (C₀ * c N / L) * b 1 ^ 2 at hg
  rw [hx] at hg
  change completeWeilEnergy tiltedUnitSpline (c N) N w ≤
    completeWeilEnergy tiltedUnitSpline (c N) N
      ((∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z) + 2 * (P + S) + (C₀ * c N / L) * b 1 ^ 2 at he
  rw [hx] at he
  change completeWeilEnergy tiltedUnitSpline (c N) N w +
      completeWeilEnergy tiltedUnitSpline (c N) N (normalizedRamanujanHorizonVector 1 N) * b 1 ^ 2 +
      2 * b 1 * ⟪conductorResidualVector (c N) 1 N, horizonCollarVector M w⟫ ≤
    completeWeilEnergy tiltedUnitSpline (c N) N
      ((∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z) + e * A + η * (P + S) at hsharp
  rw [hx] at hsharp
  have hmass : (c N * B) * U₂ + (C₀ * c N / L) * b 1 ^ 2 ≤ (c N * B') * J := by
    have h1 := mul_nonneg hB.le hβ
    have h2 := mul_nonneg hC₀.le hU₂
    dsimp only [B', J]
    simp only [div_eq_mul_inv, mul_inv_rev] at h1 ⊢
    nlinarith only [mul_nonneg hc0.le h1, mul_nonneg hc0.le h2]
  have hg' : (1 / 4 : ℝ) * A + (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 + P + S +
      (c N * c_W / (R + 1)) * W₈ + (c N / (4 * I₂)) * levyEnergy U ≤
      completeWeilEnergy tiltedUnitSpline (c N) N x + (c N * B') * J := by
    linarith only [hg, hmass]
  have hwterm : 0 ≤ (c N * c_W / (R + 1)) * W₈ := by positivity
  have hlterm : 0 ≤ (c N / (4 * I₂)) * levyEnergy U := by positivity
  have hAP : A / 4 + (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤ (c N * B') * J := by
    linarith only [hg', hnonpos, hP, hS, hwterm, hlterm]
  have hPS : P + S ≤ (c N * B') * J := by
    linarith only [hg', hnonpos, hA, hnorm, hwterm, hlterm]
  have hW : W₈ ≤ K_W * J := by
    have hh : (c N * c_W / (R + 1)) * W₈ ≤ (c N * B') * J := by
      linarith only [hg', hnonpos, hA, hnorm, hP, hS, hlterm]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ (R + 1) / (c N * c_W) by positivity)
    calc
      W₈ = ((R + 1) / (c N * c_W)) * ((c N * c_W / (R + 1)) * W₈) := by
        field_simp [hc0.ne', hcW.ne', (show R + 1 ≠ 0 by positivity)]
      _ ≤ ((R + 1) / (c N * c_W)) * ((c N * B') * J) := hm
      _ = K_W * J := by dsimp only [K_W]; field_simp [hc0.ne', hcW.ne']
  have hLev : levyEnergy U ≤ K_L * J := by
    have hh : (c N / (4 * I₂)) * levyEnergy U ≤ (c N * B') * J := by
      linarith only [hg', hnonpos, hA, hnorm, hP, hS, hwterm]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * I₂ / c N by positivity)
    calc
      levyEnergy U = (4 * I₂ / c N) * ((c N / (4 * I₂)) * levyEnergy U) := by
        field_simp [hc0.ne', hI₂.ne']
      _ ≤ (4 * I₂ / c N) * ((c N * B') * J) := hm
      _ = K_L * J := by dsimp only [K_L]; field_simp [hc0.ne']
  have hpositive : 0 < J := by
    by_contra hnot
    have hzero : J = 0 := le_antisymm (not_lt.mp hnot) (add_nonneg hU₂ hβ)
    rw [hzero, mul_zero] at hAP
    have hAz : A = 0 := by linarith only [hAP, hA, hnorm]
    have hzsq : ‖z‖ ^ 2 = 0 := by nlinarith only [hAP, hA, hκ, sq_nonneg ‖z‖]
    have hz0 : z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hzsq)
    have hb0 : ∀ m ∈ Icc 1 Q, b m = 0 := by
      intro m hm
      have ht := (sum_eq_zero_iff_of_nonneg (fun k hk => mul_nonneg
        (completedConductorEnergy_tilted_pos hc0 (mem_Icc.mp hk).1).le (sq_nonneg (b k)))).mp hAz m hm
      have hepos := completedConductorEnergy_tilted_pos hc0 (mem_Icc.mp hm).1
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left hepos.ne')
    have hy0 : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, zero_smul]
    apply hne
    rw [← hx, hy0, hz0, add_zero]
  have hAupper : A ≤ 4 * (c N * B') * J := by
    linarith only [hAP, hnorm]
  have hSupper : topCollarSeventhMass M N (primeHorizonExtension w) ≤ K_S * J := by
    have hs : S ≤ (c N * B') * J := by linarith only [hPS, hP]
    have hratio' : c N ^ 8 / L ≤ R + 1 := hratio.le
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 128 * c N ^ 7 / (dyadicTopMassConstant * L) by positivity)
    have hr := mul_le_mul_of_nonneg_right hratio'
      (show 0 ≤ (128 * B' / dyadicTopMassConstant) * J by positivity)
    have heq : (128 * c N ^ 7 / (dyadicTopMassConstant * L)) * S =
        topCollarSeventhMass M N (primeHorizonExtension w) := by
      dsimp only [S]
      field_simp [hc0.ne', hdyad.ne', hL0.ne']
    rw [heq] at hm
    dsimp only [K_S]
    simp only [div_eq_mul_inv, mul_inv_rev] at hm hr ⊢
    ring_nf at hm hr ⊢
    exact hm.trans hr
  have hrough : completeWeilEnergy tiltedUnitSpline (c N) N w ≤ 3 * (c N * B') * J := by
    have hpenalty : (C₀ * c N / L) * b 1 ^ 2 ≤ (c N * B') * J := by
      have hh := mul_nonneg (mul_nonneg hc0.le hB.le) hU₂
      linarith only [hmass, hh]
    linarith only [he, hnonpos, hPS, hpenalty]
  have hR₁ : 1 ≤ subexpCutoff N := by
    unfold subexpCutoff
    exact Nat.le_floor (by exact_mod_cast Real.one_le_exp (by positivity))
  have hw1 : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono hR₁ N hv)
  have hc8 : c N ^ 8 ≤ (R + 1) * Real.log N := (div_le_iff₀ hL0).mp hratio.le
  have hpole := hbridgeN (hc N) hc8 hw1
  change weilQuad U - δ * ((I₂ / c N) *
      (L / (2 * explicitConductorCutoffConstant * (1 + Real.log L) ^ 5) / 16) *
        (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) + W₈ + levyEnergy U + U₂) ≤
    (I₂ / c N) * completeWeilEnergy tiltedUnitSpline (c N) N w at hpole
  have hPbound : (I₂ / c N) * (2 * P) ≤ 2 * I₂ * B' * J := by
    have hp : P ≤ (c N * B') * J := by linarith only [hPS, hS]
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * I₂ / c N by positivity)
    calc
      _ = (2 * I₂ / c N) * P := by ring
      _ ≤ (2 * I₂ / c N) * ((c N * B') * J) := hh
      _ = _ := by field_simp [hc0.ne']
  have hUle : U₂ ≤ J := le_add_of_nonneg_right hβ
  have hsum : (I₂ / c N) * (2 * P) + W₈ + levyEnergy U + U₂ ≤ H * J := by
    dsimp only [H]
    linarith only [hPbound, hW, hLev, hUle]
  have herror := mul_le_mul_of_nonneg_left hsum hδ.le
  have herrsmall : δ * (H * J) ≤ (ε / 2) * J := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hδH hpositive.le
  have herrrough : δ * (H * J) ≤ H * J :=
    (mul_le_mul_of_nonneg_right hδ1 (mul_nonneg hH.le hpositive.le)).trans_eq (one_mul _)
  have hchargedUpper := mul_le_mul_of_nonneg_left hsharp (show 0 ≤ I₂ / c N by positivity)
  have hApaid := mul_le_mul_of_nonneg_left hAupper he0.le
  have hPSpaid := mul_le_mul_of_nonneg_left hPS hη.le
  have hpay : (I₂ / c N) * (e * A + η * (P + S)) ≤ (ε / 2) * J := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hApaid hPSpaid)
      (show 0 ≤ I₂ / c N by positivity)
    exact hh.trans_eq (by dsimp only [e, η]; field_simp [hc0.ne', hI₂.ne', hB'.ne']; ring)
  have hroughScaled := mul_le_mul_of_nonneg_left hrough (show 0 ≤ I₂ / c N by positivity)
  have hnonposScaled := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ I₂ / c N by positivity) hnonpos
  dsimp only [P] at herror
  refine ⟨hpositive, hW, hLev, hSupper, ?_, ?_⟩
  · dsimp only [K_Q]
    simp only [div_eq_mul_inv, mul_inv_rev] at hpole herror hroughScaled ⊢
    ring_nf at hpole herror hroughScaled ⊢
    nlinarith only [hpole, herror, hroughScaled, herrrough]
  · simp only [div_eq_mul_inv, mul_inv_rev] at hpole herror hchargedUpper hpay hnonposScaled ⊢
    ring_nf at hpole herror hchargedUpper hpay hnonposScaled ⊢
    linarith only [hpole, herror, hchargedUpper, hpay, hnonposScaled, herrsmall]

#print axioms exists_critical_charged_collar_weilQuad_bridge
end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
