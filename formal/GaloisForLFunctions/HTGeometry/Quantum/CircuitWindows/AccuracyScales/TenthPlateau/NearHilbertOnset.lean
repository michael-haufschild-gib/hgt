import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.PlateauLaw

/-! # Exact 1/10-plateau onset, canonical-budget post-onset majority, and near-Hilbert core -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords
noncomputable section

/-- Sixteen double-angle steps at error 1/10 exceed the π/2 geodesic diameter
of the projective unitary group, certifying that q = 15 is the maximal
geodesic hard-lag step count. -/
theorem thirty_two_arcsin_twentieth_gt_pi_div_two :
    π / 2 < 32 * arcsin (1 / 20) := by
  have hsin : sin (1 / 20 : ℝ) < 1 / 20 := sin_lt (by norm_num)
  have hpi := pi_lt_d2
  have hpi3 := pi_gt_three
  have harc : (1 / 20 : ℝ) < arcsin (1 / 20) := by
    have hlt := arcsin_lt_arcsin (neg_one_le_sin _) hsin (by norm_num)
    rwa [arcsin_sin (by linarith only [hpi3]) (by linarith only [hpi3])] at hlt
  linarith only [harc, hpi]

private theorem one_fifth_entropy :
    zeroGateArcTolerance (1 / 5) ∈ Ioo (0 : ℝ) 2 ∧
      log (physicalArc (zeroGateArcTolerance (1 / 5))) + 32 * log 2 / (14 : ℕ) <
        log (44 / 45) := by
  let η := zeroGateArcTolerance (1 / 5)
  have h0 : zeroGateArcTolerance 0 = 0 := by simp [zeroGateArcTolerance]
  have h1 : zeroGateArcTolerance 1 = 2 := by
    unfold zeroGateArcTolerance
    rw [mul_one, sin_pi_div_two, mul_one]
  have hη : η ∈ Ioo (0 : ℝ) 2 := ⟨h0 ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩ (by norm_num),
    h1 ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ (by norm_num)⟩
  obtain ⟨harc, htol⟩ := physicalArc_full hη
  have harc_eq : physicalArc η = 1 / 5 :=
    strictMonoOn_zeroGateArcTolerance_full.injOn ⟨harc.1.le, harc.2.le⟩ ⟨by norm_num, by norm_num⟩ htol
  refine ⟨hη, ?_⟩
  rw [harc_eq]
  have hpow : (1 / 5 : ℝ) ^ 14 * (2 : ℝ) ^ 32 < (44 / 45 : ℝ) ^ 14 := by norm_num
  have hlog := log_lt_log (by positivity) hpow
  rw [log_mul (by positivity) (by positivity), log_pow, log_pow, log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  linarith only [hlog]

private theorem four_arcsin_twentieth_lt_fifth_arc :
    0 ≤ arcsin (1 / 20) ∧ 2 * sin (arcsin (1 / 20)) = 1 / 10 ∧
      4 * arcsin (1 / 20) ≤ π / 2 ∧
      2 * sin (4 * arcsin (1 / 20)) < zeroGateArcTolerance (1 / 5) := by
  let α := arcsin (1 / 20)
  have hα0 : 0 < α := arcsin_pos.mpr (by norm_num)
  have hsin : 2 * sin α = 1 / 10 := by
    dsimp only [α]
    rw [sin_arcsin (by norm_num) (by norm_num)]
    norm_num
  have hcube := sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1001 / 20000)
  have htwentieth : (1 / 20 : ℝ) < sin (1001 / 20000) := by linarith only [hcube]
  have hpi := pi_gt_d6
  have hα_lt : α < 1001 / 20000 := by
    have hlt := arcsin_lt_arcsin (by norm_num) htwentieth (sin_le_one _)
    rwa [arcsin_sin (by linarith only [hpi]) (by linarith only [hpi])] at hlt
  have h4 : 4 * α < π * (1 / 5) / 2 := by linarith only [hα_lt, hpi]
  have hpi2 : π * (1 / 5) / 2 ≤ π / 2 := by linarith only [hpi]
  refine ⟨hα0.le, hsin, (h4.trans_le hpi2).le, ?_⟩
  unfold zeroGateArcTolerance
  exact mul_lt_mul_of_pos_left
    (strictMonoOn_sin ⟨by linarith only [hα0, hpi], (h4.trans_le hpi2).le⟩
      ⟨by linarith only [hpi], hpi2⟩ h4) two_pos

/-- Exact first nonnegative time at which s two-qubit gates fail to approximate
the evolution at projective operator error 1/10. -/
def tenthPlateauOnset {N : ℕ} (H : selfAdjoint (Register N)) (s : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧
    ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)}

/-- When the s-gate distance stays strictly below 1/10 on [0,r] and exceeds
1/10 at B, tenthPlateauOnset H s is strictly between r and B, attains distance
1/10, keeps [0,τ] affordable, and meets the 1/10 plateau in positive measure on
every right neighborhood. -/
theorem tenthPlateauOnset_spec {N s : ℕ} (H : selfAdjoint (Register N)) {r B : ℝ}
    (hr0 : 0 < r) (hB0 : 0 ≤ B)
    (hr : ∀ t ∈ Icc 0 r, orbitCircuitDistance H s t < 1 / 10)
    (hB : 1 / 10 < orbitCircuitDistance H s B) :
    let τ := tenthPlateauOnset H s
    r < τ ∧ τ < B ∧
      (∀ t ∈ Icc 0 τ, HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)) ∧
      orbitCircuitDistance H s τ = 1 / 10 ∧
      ∀ δ : ℝ, 0 < δ → 0 < volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc τ (τ + δ)) := by
  intro τ
  let E := {t : ℝ | 0 ≤ t ∧
    ¬ HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)}
  have hE_iff (t : ℝ) : t ∈ E ↔ 0 ≤ t ∧ 1 / 10 < orbitCircuitDistance H s t := by
    simp only [E, mem_setOf_eq, hasProjectiveCircuitApproximation_iff_infDist, not_le]
    rfl
  have hB_mem : B ∈ E := (hE_iff B).mpr ⟨hB0, hB⟩
  have hE_ne : E.Nonempty := ⟨B, hB_mem⟩
  have hbdd : BddBelow E := ⟨0, fun _ ht => ht.1⟩
  have hr_le : r ≤ τ := le_csInf hE_ne fun t ht => by
    by_contra! hlt
    exact ((hE_iff t).mp ht).2.not_ge (hr t ⟨ht.1, hlt.le⟩).le
  have hτ_pos : 0 < τ := hr0.trans_le hr_le
  have hcont : Continuous (orbitCircuitDistance H s) :=
    (orbitCircuitDistance_lipschitz H s).continuous
  have hrB : r < B := by
    by_contra! hle
    exact hB.not_ge (hr B ⟨hB0, hle⟩).le
  have hτ_lt_B : τ < B := by
    have hB_pos : 0 < B := hr0.trans hrB
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hcont.neg.continuousAt.eventually_lt_const (neg_lt_neg hB))
    let t' := B - min (B / 2) (δ / 2)
    have hm : 0 < min (B / 2) (δ / 2) := lt_min (half_pos hB_pos) (half_pos hδ)
    have ht'0 : 0 ≤ t' := by dsimp only [t']; linarith only [min_le_left (B / 2) (δ / 2), hB_pos]
    have ht'B : t' < B := by dsimp only [t']; linarith only [hm]
    have hd : dist t' B < δ := by
      rw [Real.dist_eq, show t' - B = -(min (B / 2) (δ / 2)) by dsimp only [t']; ring,
        abs_neg, abs_of_pos hm]
      linarith only [min_le_right (B / 2) (δ / 2), hδ]
    have hgt : 1 / 10 < orbitCircuitDistance H s t' := neg_lt_neg_iff.mp (hnear hd)
    exact (csInf_le hbdd ((hE_iff t').mpr ⟨ht'0, hgt⟩)).trans_lt ht'B
  have hτ_le_tenth : orbitCircuitDistance H s τ ≤ 1 / 10 := by
    by_contra! hgt
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hcont.neg.continuousAt.eventually_lt_const (neg_lt_neg hgt))
    let t' := τ - min (τ / 2) (δ / 2)
    have hm : 0 < min (τ / 2) (δ / 2) := lt_min (half_pos hτ_pos) (half_pos hδ)
    have ht'0 : 0 ≤ t' := by dsimp only [t']; linarith only [min_le_left (τ / 2) (δ / 2), hτ_pos]
    have ht'τ : t' < τ := by dsimp only [t']; linarith only [hm]
    have hd : dist t' τ < δ := by
      rw [Real.dist_eq, show t' - τ = -(min (τ / 2) (δ / 2)) by dsimp only [t']; ring,
        abs_neg, abs_of_pos hm]
      linarith only [min_le_right (τ / 2) (δ / 2), hδ]
    have hgt' : 1 / 10 < orbitCircuitDistance H s t' := neg_lt_neg_iff.mp (hnear hd)
    exact (csInf_le hbdd ((hE_iff t').mpr ⟨ht'0, hgt'⟩)).not_gt ht'τ
  have hτ_eq : orbitCircuitDistance H s τ = 1 / 10 := by
    refine le_antisymm hτ_le_tenth ?_
    by_contra! hlt
    obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp
      (hcont.continuousAt.eventually_lt_const hlt)
    obtain ⟨u, huE, hu_lt⟩ := exists_lt_of_csInf_lt hE_ne (lt_add_of_pos_right τ hδ)
    have hτu : τ ≤ u := csInf_le hbdd huE
    have hd : dist u τ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hτu)]
      linarith only [hu_lt]
    exact ((hE_iff u).mp huE).2.not_ge (hnear hd).le
  have hr_lt : r < τ := lt_of_le_of_ne hr_le fun heq => by
    have := hr r ⟨hr0.le, le_rfl⟩
    rw [heq, hτ_eq] at this
    exact lt_irrefl _ this
  have hprior (t : ℝ) (ht : t ∈ Icc 0 τ) :
      HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t) := by
    rcases eq_or_lt_of_le ht.2 with rfl | hlt
    · exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr hτ_le_tenth
    · by_contra hnot
      exact (csInf_le hbdd ⟨ht.1, hnot⟩).not_gt hlt
  refine ⟨hr_lt, hτ_lt_B, hprior, hτ_eq, fun δ hδ => ?_⟩
  obtain ⟨u, huE, hu_lt⟩ := exists_lt_of_csInf_lt hE_ne (lt_add_of_pos_right τ hδ)
  have hτu : τ ≤ u := csInf_le hbdd huE
  have hu_gt : 1 / 10 < orbitCircuitDistance H s u := ((hE_iff u).mp huE).2
  obtain ⟨η, hη, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hcont.neg.continuousAt.eventually_lt_const (neg_lt_neg hu_gt))
  let v := u + min (τ + δ - u) (η / 2)
  have hm : 0 < min (τ + δ - u) (η / 2) := lt_min (sub_pos.mpr hu_lt) (half_pos hη)
  have huv : u < v := by dsimp only [v]; linarith only [hm]
  have hv_le : v ≤ τ + δ := by dsimp only [v]; linarith only [min_le_left (τ + δ - u) (η / 2)]
  have hsub : Icc u v ⊆ (visitSet H s (1 / 10))ᶜ ∩ Icc τ (τ + δ) := by
    rintro x ⟨hux, hxv⟩
    refine ⟨fun hx => ?_, hτu.trans hux, hxv.trans hv_le⟩
    have hdx : dist x u < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hux)]
      have h1 : x - u ≤ min (τ + δ - u) (η / 2) := by dsimp only [v] at hxv; linarith only [hxv]
      linarith only [h1, min_le_right (τ + δ - u) (η / 2), hη]
    have hgt : 1 / 10 < orbitCircuitDistance H s x := neg_lt_neg_iff.mp (hnear hdx)
    have hdist_x := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / 10 : ℝ)).mp hx
    change orbitCircuitDistance H s x ≤ _ at hdist_x
    linarith only [hgt, hdist_x]
  have hpos : 0 < volume.real (Icc u v) := by
    rw [Real.volume_real_Icc_of_le huv.le]
    linarith only [huv]
  exact hpos.trans_le (measureReal_mono hsub
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne))

private theorem two_five_six_mul_le_two_pow {s : ℕ} (hs : 16 ≤ s) :
    256 * (s + 1) ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ n _ ih => rw [pow_succ]; omega

private theorem near_hilbert_arith {N : ℕ} (hr : 64 ≤ N.sqrt) :
    let r := N.sqrt
    65536 * (N + 1) ≤ 2 ^ (2 * r) ∧
      5 * (2 * N).sqrt + 17 ≤ 8 * r ∧
      14 * r ≤ N ∧
      2 ^ r * (2 ^ N / 2 ^ (3 * r)) ≤ 2 ^ N / (7 * (N + 1)) ∧
      2 ^ N / 2 ^ (3 * r) ≤ (2 ^ N / (2048 * (N + 1))) / 30 := by
  intro r
  have h256 := two_five_six_mul_le_two_pow (by omega : 16 ≤ r)
  have hN_succ : N + 1 ≤ (r + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt N
    nlinarith only [this]
  have h65 : 65536 * (N + 1) ≤ 2 ^ (2 * r) := calc
    65536 * (N + 1) ≤ (256 * (r + 1)) ^ 2 := by nlinarith only [hN_succ]
    _ ≤ (2 ^ r) ^ 2 := Nat.pow_le_pow_left h256 2
    _ = 2 ^ (2 * r) := by rw [← pow_mul, Nat.mul_comm r 2]
  have hsqrt2 : 5 * (2 * N).sqrt + 17 ≤ 8 * r := by
    let q := (2 * N).sqrt
    have hq2 : q * q ≤ 2 * N := Nat.sqrt_le (2 * N)
    have hq_le : q ≤ 2 * r := by nlinarith only [hq2, hN_succ, hr]
    by_contra! hlt
    have hge : 8 * r ≤ 5 * q + 16 := by omega
    nlinarith only [hge, hq2, hN_succ, hq_le, hr]
  have h14 : 14 * r ≤ N := by
    have hsq : r * r ≤ N := Nat.sqrt_le N
    nlinarith only [hsq, hr]
  have hslack : 2 ^ r * (2 ^ N / 2 ^ (3 * r)) ≤ 2 ^ N / (7 * (N + 1)) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have h7 : 7 * (N + 1) ≤ 2 ^ (2 * r) := by omega
    calc 2 ^ r * (2 ^ N / 2 ^ (3 * r)) * (7 * (N + 1))
        ≤ 2 ^ r * (2 ^ N / 2 ^ (3 * r)) * 2 ^ (2 * r) := Nat.mul_le_mul_left _ h7
      _ = (2 ^ N / 2 ^ (3 * r)) * 2 ^ (3 * r) := by
          rw [mul_comm (2 ^ r), mul_assoc, ← pow_add, show r + 2 * r = 3 * r by omega]
      _ ≤ 2 ^ N := Nat.div_mul_le_self _ _
  have hS : 2 ^ N / 2 ^ (3 * r) ≤ (2 ^ N / (2048 * (N + 1))) / 30 := by
    rw [Nat.div_div_eq_div_mul]
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have hle : 2048 * (N + 1) * 30 ≤ 2 ^ (3 * r) := calc
      2048 * (N + 1) * 30 = 61440 * (N + 1) := by ring
      _ ≤ 65536 * (N + 1) := by omega
      _ ≤ 2 ^ (2 * r) := h65
      _ ≤ 2 ^ (3 * r) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.mul_le_mul_left _ hle).trans (Nat.div_mul_le_self _ _)
  exact ⟨h65, hsqrt2, h14, hslack, hS⟩

private theorem near_hilbert_sim_step {N : ℕ} (hr64 : 64 ≤ N.sqrt)
    (H : selfAdjoint (Register N))
    (hcomp : ∀ (t : ℝ) (b d : ℕ), N ≤ d → (2 : ℝ) ^ b * ((N : ℝ) * (1 + |t|)) ≤ (2 : ℝ) ^ d →
      ∃ s : ℕ, HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ b) s (unitaryEvolution H.val t) ∧
        (s : ℝ) ≤ (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ (5 * d.sqrt + 17))
    {t : ℝ} (ht : |t| ≤ (2 : ℝ) ^ N / (2 : ℝ) ^ (14 * N.sqrt)) :
    HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N)
      (2 ^ N / 2 ^ (3 * N.sqrt)) (unitaryEvolution H.val t) := by
  let r := N.sqrt
  obtain ⟨h65, hsqrt2, h14, _, _⟩ := near_hilbert_arith hr64
  have hR1 : 1 ≤ (2 : ℝ) ^ N / (2 : ℝ) ^ (14 * r) := by
    rw [one_le_div (by positivity)]
    exact_mod_cast Nat.pow_le_pow_right (by decide) h14
  have hN_pow : (N : ℝ) ≤ (2 : ℝ) ^ (2 * r) := by
    exact_mod_cast (show N ≤ 2 ^ (2 * r) by dsimp only [r]; omega)
  have h1t : 1 + |t| ≤ 2 * ((2 : ℝ) ^ N / (2 : ℝ) ^ (14 * r)) := by linarith only [ht, hR1]
  have hNt : (N : ℝ) * (1 + |t|) ≤ 2 * (2 : ℝ) ^ N / (2 : ℝ) ^ (12 * r) := by
    calc (N : ℝ) * (1 + |t|)
        ≤ (2 : ℝ) ^ (2 * r) * (2 * ((2 : ℝ) ^ N / (2 : ℝ) ^ (14 * r))) :=
          mul_le_mul hN_pow h1t (by positivity) (by positivity)
      _ = 2 * (2 : ℝ) ^ N / (2 : ℝ) ^ (12 * r) := by
          rw [show 14 * r = 2 * r + 12 * r by omega, pow_add (2 : ℝ) (2 * r) (12 * r)]
          field_simp
  have hNt_D : (N : ℝ) * (1 + |t|) ≤ (2 : ℝ) ^ N := by
    refine hNt.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h2_le : (2 : ℝ) ≤ (2 : ℝ) ^ (12 * r) := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ 12 * r)
    nlinarith only [h2_le, show (0 : ℝ) ≤ (2 : ℝ) ^ N by positivity]
  have hscaled : (2 : ℝ) ^ N * ((N : ℝ) * (1 + |t|)) ≤ (2 : ℝ) ^ (2 * N) :=
    (mul_le_mul_of_nonneg_left hNt_D (by positivity)).trans_eq
      (by rw [two_mul, pow_add (2 : ℝ) N N])
  obtain ⟨g, hfit, hg⟩ := hcomp t N (2 * N) (by omega) hscaled
  have hg_bound : g ≤ 2 ^ N / 2 ^ (3 * r) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    have h5 : ((2 : ℝ) ^ (5 * (2 * N).sqrt + 17)) ≤ (2 : ℝ) ^ (8 * r) :=
      pow_le_pow_right₀ (by norm_num) hsqrt2
    have hreal : (g : ℝ) * (2 : ℝ) ^ (3 * r) ≤ (2 : ℝ) ^ N := by
      calc (g : ℝ) * (2 : ℝ) ^ (3 * r)
          ≤ ((N : ℝ) * (1 + |t|) * (2 : ℝ) ^ (5 * (2 * N).sqrt + 17)) * (2 : ℝ) ^ (3 * r) :=
            mul_le_mul_of_nonneg_right hg (by positivity)
        _ ≤ (2 * (2 : ℝ) ^ N / (2 : ℝ) ^ (12 * r) * (2 : ℝ) ^ (8 * r)) * (2 : ℝ) ^ (3 * r) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hNt h5 (by positivity) (by positivity)) (by positivity)
        _ = 2 * (2 : ℝ) ^ N / (2 : ℝ) ^ r := by
            rw [show 12 * r = 8 * r + (3 * r + r) by omega,
              pow_add (2 : ℝ) (8 * r) (3 * r + r), pow_add (2 : ℝ) (3 * r) r]
            field_simp
        _ ≤ (2 : ℝ) ^ N := by
            rw [div_le_iff₀ (by positivity)]
            have h2r : (2 : ℝ) ≤ (2 : ℝ) ^ r := by
              simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ r)
            nlinarith only [h2r, show (0 : ℝ) ≤ (2 : ℝ) ^ N by positivity]
    exact_mod_cast hreal
  exact LocalPatches.approx_enlarge hfit le_rfl hg_bound

private theorem post_onset_two_at_tenth {N : ℕ} (H : selfAdjoint (Register N))
    {σ : ℝ} (hσ : 0 ≤ σ)
    (heq : orbitCircuitDistance H (2 ^ N / (14 * (N + 1))) σ = zeroGateArcTolerance (1 / 5))
    (s : ℕ) (hs : s ≤ nearHilbertContinuousCircuitBudget N) :
    (∀ T : ℝ, σ ≤ T →
      4 * (T - σ) - 3 * σ ≤ 6 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ T)) ∧
    (∀ T : ℝ, 4 * σ < T →
      T - σ < 2 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ T)) := by
  obtain ⟨hα0, hsin_tenth, h4_pi, h4_lt⟩ := four_arcsin_twentieth_lt_fifth_arc
  have hj_le : 2 * s * 2 ≤ 2 ^ N / (14 * (N + 1)) := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc 2 * s * 2 * (14 * (N + 1))
        = s * (56 * (N + 1)) := by ring
      _ ≤ nearHilbertContinuousCircuitBudget N * (64 * (N + 1)) :=
          Nat.mul_le_mul hs (Nat.mul_le_mul_right (N + 1) (by decide))
      _ ≤ 2 ^ N := Nat.div_mul_le_self (2 ^ N) (64 * (N + 1))
  have hfar : 2 * sin (2 * (2 : ℝ) * arcsin (1 / 20)) < orbitCircuitDistance H (2 ^ N / (14 * (N + 1))) σ := by
    rw [heq, show 2 * (2 : ℝ) * arcsin (1 / 20) = 4 * arcsin (1 / 20) by ring]
    exact h4_lt
  obtain ⟨_, hp1, hp2⟩ := post_onset_occupation_of_geodesic_endpoint H hσ
    (q := 2) (by decide) hα0 (by norm_num only [Nat.cast_ofNat]; linarith only [h4_pi])
    hj_le hfar
  rw [hsin_tenth] at hp1 hp2
  norm_num only [Nat.cast_ofNat] at hp1 hp2
  exact ⟨fun T hT => by linarith only [hp1 T hT],
    fun T hT => hp2 (by decide) T (by simpa only [show ((2 : ℝ) + 2) / ((2 : ℝ) - 1) = 4 by norm_num] using hT)⟩

/-- Exact 1/10-plateau onset dating at near-Hilbert lower scale D / 2^(14√N),
zero-wait post-onset majority at the canonical exponential budget
P = nearHilbertContinuousCircuitBudget N, and uninterrupted plateau intervals of
radius D / 2^(14√N) with subexponential relative gate slack L_near ≤ B₇ / 2^√N. -/
theorem gaussian_tenth_error_exact_onset_and_near_hilbert_core :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k + 3
      let D : ℕ := 2 ^ N
      let u := pathPauliDisorderShell ω (k + 1)
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
      let G := (2 : ℝ) ^ (D ^ c)
      let P := nearHilbertContinuousCircuitBudget N
      let B₁₄ := D / (14 * (N + 1))
      let B₇ := D / (7 * (N + 1))
      let J := D / (2048 * (N + 1))
      let S := J / 30
      let L_near := D / 2 ^ (3 * N.sqrt)
      let R_near := (D : ℝ) / (2 : ℝ) ^ (14 * N.sqrt)
      let η_P := zeroGateArcTolerance (1 / 5)
      let nearCore := tenthPlateauCore H B₇ L_near R_near
      2 ^ N.sqrt * L_near ≤ B₇ ∧ L_near ≤ S ∧
      (∀ s : ℕ, L_near ≤ s → s ≤ B₇ →
        let τ := tenthPlateauOnset H s
        R_near < τ ∧
        (1 - (4 / 5 : ℝ) ^ D) * τ ≤ (4 / 5 : ℝ) ^ D * G ∧
        (∀ t ∈ Icc 0 τ, HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)) ∧
        orbitCircuitDistance H s τ = 1 / 10 ∧
        (∀ δ : ℝ, 0 < δ → 0 < volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc τ (τ + δ)))) ∧
      (∃ σ_P : ℝ,
        R_near < σ_P ∧ orbitCircuitDistance H B₁₄ σ_P = η_P ∧
        (∀ t ∈ Ico 0 σ_P, orbitCircuitDistance H B₁₄ t < η_P) ∧
        (1 - (44 / 45 : ℝ) ^ D) * σ_P ≤ (44 / 45 : ℝ) ^ D * G ∧
        (∀ s ≤ P, ∀ T : ℝ, σ_P ≤ T →
          4 * (T - σ_P) - 3 * σ_P ≤ 6 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ_P T)) ∧
        (∀ s ≤ P, ∀ T : ℝ, 4 * σ_P < T →
          T - σ_P < 2 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ_P T))) ∧
      MeasurableSet nearCore ∧
      (∀ a T : ℝ, 0 ≤ T → volume.real (Icc a (a + T) \ nearCore) ≤ (4 / 5 : ℝ) ^ D * (T + G)) ∧
      (∀ a T : ℝ, G ≤ T → (1 - 2 * (4 / 5 : ℝ) ^ D) * T ≤ volume.real (nearCore ∩ Icc a (a + T))) := by
  obtain ⟨c, hfin⟩ := gaussian_finite_hilbert_occupation_full
  refine ⟨c, ?_⟩
  obtain ⟨h13_mem, h13_log⟩ := thirteen_125_entropy
  obtain ⟨h5_mem, h5_log⟩ := one_fifth_entropy
  obtain ⟨_, hsin_tenth, h4_pi, h4_lt⟩ := four_arcsin_twentieth_lt_fifth_arc
  filter_upwards [hfin, LocalPatches.gaussian_binary_precision_compiler] with ω hocc hbin
  filter_upwards [hocc 7 (by decide) (13 / 125) h13_mem (4 / 5) (by norm_num) h13_log,
    hocc 14 (by decide) (zeroGateArcTolerance (1 / 5)) h5_mem (44 / 45) (by norm_num) h5_log,
    (tendsto_add_atTop_nat 1).eventually hbin,
    eventually_ge_atTop (64 * 64)] with k hocc7 hocc14 hcomp hk64
  intro N D u H G P B₁₄ B₇ J S L_near R_near η_P nearCore
  let r := N.sqrt
  have hr64 : 64 ≤ r := Nat.le_sqrt.mpr (by dsimp only [N]; omega)
  obtain ⟨_, _, h14, hslack, hLS⟩ := near_hilbert_arith hr64
  have hN8 : 8 ≤ N := by dsimp only [N]; omega
  have hD0 : D ≠ 0 := (Nat.two_pow_pos N).ne'
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  have hR1 : 1 ≤ R_near := by
    dsimp only [R_near, D]
    rw [one_le_div (by positivity)]
    exact_mod_cast Nat.pow_le_pow_right (by decide) h14
  have hR_pos : 0 < R_near := zero_lt_one.trans_le hR1
  have hsim_near (t : ℝ) (ht : |t| ≤ R_near) :
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N) L_near (unitaryEvolution H.val t) :=
    near_hilbert_sim_step hr64 H hcomp (by simpa only [R_near, D, Nat.cast_pow, Nat.cast_ofNat] using ht)
  obtain ⟨σ_plat, hσp_pos, hσp_eq, _, _⟩ := dated_crossing_of_occupation (j := B₇) H
    h13_mem.1 le_rfl (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) D)
    (pow_lt_one₀ (by norm_num) (by norm_num) hD0) hG0
    (fun T hT => by simpa only [zero_add] using hocc7 B₇ le_rfl 0 T hT)
  obtain ⟨σ_P, hσP_pos, hσP_eq, hσP_prior, hσP_up⟩ := dated_crossing_of_occupation (j := B₁₄) H
    h5_mem.1 le_rfl (pow_nonneg (by norm_num : (0 : ℝ) ≤ 44 / 45) D)
    (pow_lt_one₀ (by norm_num) (by norm_num) hD0) hG0
    (fun T hT => by simpa only [zero_add] using hocc14 B₁₄ le_rfl 0 T hT)
  have hearly_near (s : ℕ) (hLs : L_near ≤ s) (t : ℝ) (ht : t ∈ Icc 0 R_near) :
      orbitCircuitDistance H s t < 1 / 10 := by
    have habs : |t| ≤ R_near := by rw [abs_of_nonneg ht.1]; exact ht.2
    obtain ⟨z, hz, C, hC, herr⟩ := hsim_near t habs
    have hd := (hasProjectiveCircuitApproximation_iff_infDist _ s (1 / (2 : ℝ) ^ N)).mp
      ⟨z, hz, C, hC.trans hLs, herr⟩
    change orbitCircuitDistance H s t ≤ _ at hd
    have hpow : (256 : ℝ) ≤ (2 : ℝ) ^ N := by
      calc (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
           _ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN8
    exact hd.trans_lt ((one_div_le_one_div_of_le (by norm_num) hpow).trans_lt (by norm_num))
  have honset (s : ℕ) (hLs : L_near ≤ s) (hsB : s ≤ B₇) :
      let τ := tenthPlateauOnset H s
      R_near < τ ∧
      (1 - (4 / 5 : ℝ) ^ D) * τ ≤ (4 / 5 : ℝ) ^ D * G ∧
      (∀ t ∈ Icc 0 τ, HasProjectiveCircuitApproximation N (1 / 10 : ℝ) s (unitaryEvolution H.val t)) ∧
      orbitCircuitDistance H s τ = 1 / 10 ∧
      (∀ δ : ℝ, 0 < δ → 0 < volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc τ (τ + δ))) := by
    intro τ
    have hB_gt : 1 / 10 < orbitCircuitDistance H s σ_plat := by
      have hle : orbitCircuitDistance H B₇ σ_plat ≤ orbitCircuitDistance H s σ_plat := by
        apply (hasProjectiveCircuitApproximation_iff_infDist _ B₇ _).mp
        obtain ⟨z, hz, C, hC, he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr
          (le_rfl : orbitCircuitDistance H s σ_plat ≤ _)
        exact ⟨z, hz, C, hC.trans hsB, he⟩
      rw [hσp_eq] at hle
      linarith only [hle]
    obtain ⟨hR_lt, _, hprior, heq, hpos_meas⟩ := tenthPlateauOnset_spec H hR_pos hσp_pos.le
      (hearly_near s hLs) hB_gt
    have hτ0 : 0 ≤ τ := hR_pos.le.trans hR_lt.le
    have hsub_vis : Icc 0 τ ⊆ visitSet H B₇ (13 / 125 : ℝ) ∩ Icc 0 (0 + τ) := by
      intro t ht
      obtain ⟨z, hz, C, hC, herr⟩ := hprior t ht
      exact ⟨⟨z, hz, C, hC.trans hsB, herr.trans (by norm_num)⟩, ht.1, by linarith only [ht.2]⟩
    have hτ_le : τ ≤ (4 / 5 : ℝ) ^ D * (τ + G) := by
      have hm := (measureReal_mono hsub_vis
        (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)).trans
        (hocc7 B₇ le_rfl 0 τ hτ0)
      rw [Real.volume_real_Icc_of_le hτ0, sub_zero] at hm
      exact hm
    exact ⟨hR_lt, by linarith only [hτ_le], hprior, heq, hpos_meas⟩
  have hLB14 : L_near ≤ B₁₄ := hLS.trans <| (Nat.le_div_iff_mul_le (by positivity)).mpr <|
    (Nat.mul_le_mul_left S (show 14 * (N + 1) ≤ 2048 * (N + 1) * 30 by omega)).trans <| by
      dsimp only [S, J]
      rw [Nat.div_div_eq_div_mul]
      exact Nat.div_mul_le_self _ _
  have hR_lt_P : R_near < σ_P := by
    by_contra! hle
    have hlt := hearly_near B₁₄ hLB14 σ_P ⟨hσP_pos.le, hle⟩
    rw [hσP_eq] at hlt
    have hα_pos : 0 < arcsin (1 / 20) := arcsin_pos.mpr (by norm_num)
    have h10_lt_5 : (1 / 10 : ℝ) < η_P := by
      calc (1 / 10 : ℝ) = 2 * sin (arcsin (1 / 20)) := hsin_tenth.symm
           _ < 2 * sin (4 * arcsin (1 / 20)) := mul_lt_mul_of_pos_left
               (strictMonoOn_sin ⟨by linarith only [hα_pos, pi_pos], by linarith only [hα_pos, h4_pi]⟩
                 ⟨by linarith only [hα_pos, pi_pos], h4_pi⟩ (by linarith only [hα_pos])) two_pos
           _ < η_P := h4_lt
    linarith only [hlt, h10_lt_5]
  have hcore_sub : (visitSet H B₇ (13 / 125 : ℝ))ᶜ ⊆ nearCore :=
    compl_visitSet_subset_tenthPlateauCore hN8 H hsim_near
  have hcore_meas : MeasurableSet nearCore := measurableSet_tenthPlateauCore H B₇ L_near R_near
  have hcore_diff (a T : ℝ) (hT : 0 ≤ T) :
      volume.real (Icc a (a + T) \ nearCore) ≤ (4 / 5 : ℝ) ^ D * (T + G) := by
    have hsub : Icc a (a + T) \ nearCore ⊆ visitSet H B₇ (13 / 125 : ℝ) ∩ Icc a (a + T) := by
      rintro t ⟨htI, hnc⟩
      exact ⟨by_contra fun hn => hnc (hcore_sub hn), htI⟩
    exact (measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)).trans
      (hocc7 B₇ le_rfl a T hT)
  have hcore_maj : ∀ a T : ℝ, G ≤ T → (1 - 2 * (4 / 5 : ℝ) ^ D) * T ≤ volume.real (nearCore ∩ Icc a (a + T)) :=
    measureReal_inter_ge_of_sdiff_le hcore_meas (pow_nonneg (by norm_num) D) hG0 hcore_diff
  exact ⟨hslack, hLS, honset,
    ⟨σ_P, hR_lt_P, hσP_eq, hσP_prior, hσP_up,
      fun s hs => (post_onset_two_at_tenth H hσP_pos.le hσP_eq s hs).1,
      fun s hs => (post_onset_two_at_tenth H hσP_pos.le hσP_eq s hs).2⟩,
    hcore_meas, hcore_diff, hcore_maj⟩

#print axioms thirty_two_arcsin_twentieth_gt_pi_div_two
#print axioms tenthPlateauOnset_spec
#print axioms gaussian_tenth_error_exact_onset_and_near_hilbert_core
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
