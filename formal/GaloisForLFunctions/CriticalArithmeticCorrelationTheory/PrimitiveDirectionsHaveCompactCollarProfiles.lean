import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WholeSpaceCollarGarding

/-!
# Compact collar profiles of primitive nonpositive directions

Orthogonal projection separates the positive low packet. Its polar coefficient
is paid by the primitive Gram estimate; the remaining collar has bounded
weighted mass and Lévy energy, and asymptotically nonpositive Weil form.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology RHTower
open scoped Classical BigOperators RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Every nonzero primitive nonpositive direction yields a nonzero collar profile with uniform
compactness bounds and an arbitrarily small normalized Weil form. -/
theorem exists_critical_primitive_collar_weilQuad_bridge
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ K_W K_L : ℝ, 0 < K_W ∧ 0 < K_L ∧ ∀ {ε : ℝ}, 0 < ε →
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      x ∈ (conductorSubspace 1 N)ᗮ → x ≠ 0 →
      completeWeilEnergy tiltedUnitSpline (c N) N x ≤ 0 →
      ∃ w : EuclideanSpace ℝ (PrimeHorizonIndex N),
        w ∈ (conductorSubspace (subexpCutoff N) N)ᗮ ∧
        let U := normalizedCentredAtomicTest tiltedUnitSpline
          (atomicTailCoefficients (N / linearDefectCutoff (c N)) (primeHorizonExtension w)) (c N) N
        0 < ∫ u, U u ^ 2 ∧
        (∫ u, U u ^ 2 * Real.exp (-(8 * u))) ≤ K_W * (∫ u, U u ^ 2) ∧
        levyEnergy U ≤ K_L * (∫ u, U u ^ 2) ∧
        weilQuad U ≤ ε * (∫ u, U u ^ 2) := by
  obtain ⟨c_W, B, hcW, hB, hG⟩ :=
    exists_critical_primitive_collar_garding_and_far_bridge hc hR hcrit
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₂ : 0 < I₂ := integral_tiltedUnitSpline_sq_pos
  let K_W := (R + 1) * B / c_W
  let K_L := 4 * I₂ * B
  have hKW : 0 < K_W := by dsimp only [K_W]; positivity
  have hKL : 0 < K_L := by dsimp only [K_L]; positivity
  refine ⟨K_W, K_L, hKW, hKL, fun {ε} hε => ?_⟩
  let H := 2 * I₂ * B + K_W + K_L + 1
  have hH : 0 < H := by dsimp only [H]; positivity
  let δ := ε / (2 * H)
  let η := ε / (2 * I₂ * B)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hη : 0 < η := by dsimp only [η]; positivity
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hG hη, eventually_poleOrthogonal_collar_weilQuad_bridge
      (show 0 < R + 1 by linarith) hδ,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    hQlim.eventually_ge_atTop 1]
    with N hGN hbridgeN hratio hL1 hQge x hprim hne hnonpos
  let Q := lowPacketCutoff N
  let y := (conductorSubspace Q N).starProjection x
  let z := x - y
  have hy : y ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hQ1 : 1 ≤ Q := Nat.le_floor (by exact_mod_cast hQge)
  have hyp : y ∈ (conductorSubspace 1 N)ᗮ :=
    starProjection_mem_orthogonal_of_le (conductorSubspace_mono hQ1 N) hprim
  have hz : z ∈ (conductorSubspace Q N)ᗮ := sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨b, _, hb⟩ := mem_conductorSubspace_iff.mp hy
  have hx : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z = x := by
    rw [← hb]; dsimp only [z]; abel
  obtain ⟨w, hw, hg, he⟩ := hGN b (by rwa [← hb]) z hz
  refine ⟨w, hw, ?_⟩
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
  change (1 / 8 : ℝ) * A + (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 + P + S +
      (c N * c_W / (R + 1)) * W₈ + (c N / (4 * I₂)) * levyEnergy U ≤
    completeWeilEnergy tiltedUnitSpline (c N) N
      ((∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z) + (c N * B) * U₂ at hg
  rw [hx] at hg
  change completeWeilEnergy tiltedUnitSpline (c N) N w ≤
    completeWeilEnergy tiltedUnitSpline (c N) N
      ((∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) + z) + η * (P + S) at he
  rw [hx] at he
  have hwterm : 0 ≤ (c N * c_W / (R + 1)) * W₈ := by positivity
  have hlterm : 0 ≤ (c N / (4 * I₂)) * levyEnergy U := by positivity
  have hAP : A / 8 + (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤ (c N * B) * U₂ := by
    linarith only [hg, hnonpos, hP, hS, hwterm, hlterm]
  have hPS : P + S ≤ (c N * B) * U₂ := by
    linarith only [hg, hnonpos, hA, hnorm, hwterm, hlterm]
  have hW : W₈ ≤ K_W * U₂ := by
    have hh : (c N * c_W / (R + 1)) * W₈ ≤ (c N * B) * U₂ := by
      linarith only [hg, hnonpos, hA, hnorm, hP, hS, hlterm]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ (R + 1) / (c N * c_W) by positivity)
    calc
      W₈ = ((R + 1) / (c N * c_W)) * ((c N * c_W / (R + 1)) * W₈) := by
        field_simp [hc0.ne', hcW.ne', (show R + 1 ≠ 0 by positivity)]
      _ ≤ ((R + 1) / (c N * c_W)) * ((c N * B) * U₂) := hm
      _ = K_W * U₂ := by dsimp only [K_W]; field_simp [hc0.ne', hcW.ne']
  have hLev : levyEnergy U ≤ K_L * U₂ := by
    have hh : (c N / (4 * I₂)) * levyEnergy U ≤ (c N * B) * U₂ := by
      linarith only [hg, hnonpos, hA, hnorm, hP, hS, hwterm]
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4 * I₂ / c N by positivity)
    calc
      levyEnergy U = (4 * I₂ / c N) * ((c N / (4 * I₂)) * levyEnergy U) := by
        field_simp [hc0.ne', hI₂.ne']
      _ ≤ (4 * I₂ / c N) * ((c N * B) * U₂) := hm
      _ = K_L * U₂ := by dsimp only [K_L]; field_simp [hc0.ne']
  have hpositive : 0 < U₂ := by
    by_contra hnot
    have hzero : U₂ = 0 := le_antisymm (not_lt.mp hnot) hU₂
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
  have hfar : (I₂ / c N) * completeWeilEnergy tiltedUnitSpline (c N) N w ≤ (ε / 2) * U₂ := by
    have hh := mul_le_mul_of_nonneg_left hPS hη.le
    have he' : completeWeilEnergy tiltedUnitSpline (c N) N w ≤ η * ((c N * B) * U₂) := by
      linarith only [he, hnonpos, hh]
    have hm := mul_le_mul_of_nonneg_left he' (show 0 ≤ I₂ / c N by positivity)
    exact hm.trans_eq (by dsimp only [η]; field_simp [hc0.ne', hI₂.ne', hB.ne'])
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
  have hPbound : (I₂ / c N) * (2 * P) ≤ 2 * I₂ * B * U₂ := by
    have hp : P ≤ (c N * B) * U₂ := by linarith only [hPS, hS]
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * I₂ / c N by positivity)
    calc
      _ = (2 * I₂ / c N) * P := by ring
      _ ≤ (2 * I₂ / c N) * ((c N * B) * U₂) := hh
      _ = _ := by field_simp [hc0.ne']
  have hsum : (I₂ / c N) * (2 * P) + W₈ + levyEnergy U + U₂ ≤ H * U₂ := by
    dsimp only [H]
    linarith only [hPbound, hW, hLev]
  have herror := mul_le_mul_of_nonneg_left hsum hδ.le
  have hid : δ * (H * U₂) = (ε / 2) * U₂ := by dsimp only [δ]; field_simp [hH.ne']
  rw [hid] at herror
  dsimp only [P] at herror
  refine ⟨hpositive, hW, hLev, ?_⟩
  simp only [div_eq_mul_inv, mul_inv_rev] at hpole herror hfar ⊢
  ring_nf at hpole herror hfar ⊢
  linarith only [hpole, herror, hfar]

#print axioms exists_critical_primitive_collar_weilQuad_bridge

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
