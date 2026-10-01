import GaloisForLFunctions.RHTower.ReflectedCompactTargetAssembly
import GaloisForLFunctions.RHTower.CompactGaussianRotatedRetainedEvent
import GaloisForLFunctions.RHTower.CompactGaussianWindowHolomorphicTarget
import GaloisForLFunctions.RHTower.ReflectedCompactPrimalCubicTail
import GaloisForLFunctions.RHTower.SteinhausSquareScaleWindowSeam
import GaloisForLFunctions.RHTower.SteinhausPrefixTargetEvent

open Complex MeasureTheory Filter Topology Finset Metric
noncomputable section
namespace RHTower
open SteinhausModel

/-- One accuracy works for every fixed holomorphic catalogue member. Each
member supplies an original-law compact target bound whenever it approximates
the literal moving reference target. No physical-height count is asserted. -/
theorem exists_reflectedCompactTarget_branch_mass
    (c : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hc0 : 1 / 2 < c.re - R) (hc1 : c.re + R < 1)
    (P : ℕ) (ω : Omega) {δ ε κ : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ e : ℝ, 0 < e ∧ ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (closedBall c R) →
      ∃ m : ℝ, 0 < m ∧ ∀ᶠ n : ℕ in atTop,
        ∀ tau ∈ Set.Icc ((n ^ 2 : ℕ) : ℝ) (2 * (n ^ 2 : ℕ)), ∀ f : ℂ → ℂ,
          (∀ s ∈ closedBall c r,
            ‖reflectedCompactReferenceTarget f (n ^ 2 : ℕ) tau (steinhausLogPhaseShift ω (-tau)) s - g s‖ ≤ e) →
          m * Real.exp (-(2 * κ * Real.log (n ^ 2 : ℕ))) ≤ steinhausMeasure.real
            (steinhausCharacterCell P (steinhausLogPhaseShift ω (-tau)) δ ∩
              reflectedCompactTargetEvent c r f ε (n ^ 2) tau) := by
  classical
  have hc0r : 1 / 2 < c.re - r := by linarith
  have hc1r : c.re + r < 1 := by linarith
  obtain ⟨C, hC, hrow⟩ := exists_reflectedCompactGaussianRow_disc_bounds c hr hc0r.le hc1r
  let e := ε / (8 * (C + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have heid : e * (8 * (C + 1)) = ε := by
    dsimp [e]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨Bc, _, δc, hδc, hcorr⟩ :=
    exists_steinhausCompactReflectedCorrection_character_tolerance c hr hc0r hc1r (by positivity : 0 < ε / 4)
  let B0 := max P Bc
  refine ⟨e, he, ?_⟩
  intro g hg
  obtain ⟨ω', hprefix, B, D, δw, hB, hδw, hwindow⟩ :=
    exists_compactGaussianWindow_holomorphic_target_mass (Nat.primesLE B0) ω B0 he hκ
      hr hrR (by linarith) hc1 hg
  let δ' := min δw (min δ δc)
  have hδ' : 0 < δ' := lt_min hδw (lt_min hδ hδc)
  obtain ⟨m, hm, hret⟩ := exists_compactGaussian_rotatedRetained_event c hr hrR hc0 hc1 B ω' hδ' he
  obtain ⟨Ct, _, htail⟩ := exists_fullReflectedPrimal_compact_cubic_tail_le c hr hc0r hc1r (q := 1) (by norm_num)
  have htlim : Tendsto (fun n : ℕ => Ct * (n : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => Ct / (n : ℝ)) atTop (𝓝 0))
  have hsquare : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
    Filter.tendsto_pow_atTop (by decide)
  refine ⟨m / 4, by positivity, ?_⟩
  filter_upwards [hsquare.eventually hrow, hsquare.eventually hcorr,
    hsquare.eventually hwindow, hsquare.eventually hret, htail,
    htlim.eventually (Iio_mem_nhds (by positivity : 0 < ε / 4)),
    eventually_squareScale_cubicCutoff_freeWindow_seam (Nat.succ_pos B) B D]
    with n hrowN hcorrN hwindowN hretN htailN htailSmall hseam
  rcases hseam with ⟨hn, hNL, hLD, hBY, hLY⟩
  let N := n ^ 2
  let L := n ^ 3
  let Y := N / (2 * (B + 1))
  let S := steinhausWindowRetainedPrimes L N Y
  have hN : 0 < N := pow_pos hn _
  have hYN : Y ≤ N := Nat.div_le_self _ _
  have hBS : Nat.primesLE B ⊆ S := by
    intro p hp
    change p ∈ Nat.primesLE L \ largePrimes N Y
    apply Finset.mem_sdiff.mpr
    have hpB := Nat.mem_primesLE.mp hp
    refine ⟨Nat.mem_primesLE.mpr ⟨hpB.1.trans (hBY.trans (hYN.trans hNL)), hpB.2⟩, ?_⟩
    intro hpP
    exact not_lt_of_ge (hpB.1.trans hBY) (mem_largePrimes.mp hpP).2
  have hB0S : Nat.primesLE B0 ⊆ S := by
    intro p hp
    exact hBS (Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hB, (Nat.mem_primesLE.mp hp).2⟩)
  intro tau htau f hcatalogue
  obtain ⟨E, hE, hmass, hretain, hgood⟩ := hretN L S hBS tau
  let ω0 := steinhausLogPhaseShift ω (-tau)
  have hbase (η : Omega) (hη : η ∈ E) : η ∈ steinhausCharacterCell B0 ω0 δ' := by
    have hcell := (steinhausCharacterCell_logPhaseShift_iff B ω' η δ' tau).mp (hgood η hη).1
    intro k hk
    have hcent : X k (steinhausLogPhaseShift ω' (-tau)) = X k ω0 := by
      apply X_congr_of_eqOn_primeFactors
      intro p hp
      have hpB0 : p ∈ Nat.primesLE B0 := Nat.mem_primesLE.mpr ⟨
        (Nat.le_of_dvd (by have := (mem_Icc.mp hk).1; omega)
          (Nat.dvd_of_mem_primeFactors hp)).trans (mem_Icc.mp hk).2,
        Nat.prime_of_mem_primeFactors hp⟩
      simp only [ω0, steinhausLogPhaseShift, hprefix p hpB0]
    rw [← hcent]
    exact hcell k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hB⟩)
  let A := reflectedCompactTargetEvent c r f ε N tau
  have hA : MeasurableSet A := measurableSet_reflectedCompactTargetEvent c r (by linarith) hc1r.le f ε hN tau
  let q := (1 / 4 : ℝ) * Real.exp (-(2 * κ * Real.log N))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hconditional (η : Omega) (hη : η ∈ E) :
      q ≤ steinhausMeasure.real {ξ | freezeSteinhausPrefix S η ξ ∈ A} := by
    have hw := hwindowN tau (steinhausLogPhaseShift η tau)
      (fun k hk => ((hgood η hη).1 k hk).trans_le (min_le_left _ _)) L hLD
    refine hw.trans (measureReal_mono ?_)
    intro ξ hξ
    let φ := freezeSteinhausPrefix S η ξ
    have hφcell : φ ∈ steinhausCharacterCell B0 ω0 δ' :=
      (steinhausCharacterCell_congr_smallPrimes B0 ω0 δ'
        (fun p hp => by simp only [φ, freezeSteinhausPrefix, if_pos (hB0S hp)])).mpr (hbase η hη)
    have hφcorr : φ ∈ steinhausCharacterCell Bc ω0 δc := by
      intro k hk
      exact (hφcell k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
        (mem_Icc.mp hk).2.trans (le_max_right _ _)⟩)).trans_le
        ((min_le_right δw _).trans (min_le_right δ δc))
    intro s hs
    have hre0 : |s.re - c.re| ≤ dist s c := by
      simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c)
    have hre := abs_le.mp (hre0.trans hs)
    have htailφ := (htailN tau htau s hs φ).trans htailSmall.le
    have hbound := norm_reflectedCompactTarget_error_le
      (by linarith : 1 / 2 < s.re) (by linarith : s.re < 1)
      tau N L Y hN hYN hNL hLY η ξ ω0 f g C e e e (ε / 4) (ε / 4)
      (hrowN tau htau s hs).1 ((hgood η hη).2 s hs).le (hξ s hs)
      (hcatalogue s hs) (hcorrN tau htau s hs ω0 φ hφcorr).le
      (by simpa only [add_comm] using htailφ)
    exact hbound.trans (by nlinarith [mul_pos hC he])
  have hint := measureReal_prefixEvent_inter_target_ge S hE hA hretain hq hconditional
  calc
    _ = q * m := by dsimp [q, N]; ring
    _ ≤ q * steinhausMeasure.real E := mul_le_mul_of_nonneg_left hmass hq
    _ ≤ steinhausMeasure.real (E ∩ A) := hint
    _ ≤ _ := measureReal_mono (by
      intro η hη
      refine ⟨?_, hη.2⟩
      intro k hk
      exact ((hbase η hη.1) k (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,
        (mem_Icc.mp hk).2.trans (le_max_left _ _)⟩)).trans_le
          ((min_le_right δw _).trans (min_le_left δ δc)))

end RHTower
