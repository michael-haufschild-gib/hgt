import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.HilbertBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GeodesicPacking
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactSynthesis.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.CriticalHeights
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.HighPrecision.OrbitProfiles
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.ExponentialCompiler
import Mathlib.Topology.Maps.Proper.Basic

/-! # The plateau at error one tenth, its onset, and its occupation of later times -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
open SharpOccupation SharpOccupation.FiniteRecords
noncomputable section

/-- Centers of symmetric radius-R intervals on which every 1/10-approximation
requires strictly more than B - L gates. -/
def tenthPlateauCore {N : ℕ} (H : selfAdjoint (Register N)) (B L : ℕ) (R : ℝ) : Set ℝ :=
  {z : ℝ | ∀ s : ℝ, |s| ≤ R → ∀ j : ℕ,
    HasProjectiveCircuitApproximation N (1 / 10 : ℝ) j (unitaryEvolution H.val (z + s)) →
      B < j + L}

/-- The exponential-interval plateau core is open, hence Lebesgue measurable. -/
theorem isOpen_tenthPlateauCore {N : ℕ} (H : selfAdjoint (Register N)) (B L : ℕ) (R : ℝ) :
    IsOpen (tenthPlateauCore H B L R) := by
  by_cases hR : R < 0
  · convert isOpen_univ
    ext z
    simp only [tenthPlateauCore, mem_setOf_eq, mem_univ, iff_true]
    intro s hs
    linarith only [abs_nonneg s, hs, hR]
  by_cases hBL : B < L
  · convert isOpen_univ
    ext z
    simp only [tenthPlateauCore, mem_setOf_eq, mem_univ, iff_true]
    intro _ _ j _
    omega
  push Not at hR hBL
  let I := Icc (-R) R
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Set (ℝ × I) := {p | orbitCircuitDistance H (B - L) (p.1 + p.2.val) ≤ 1 / 10}
  have hcont : Continuous (fun p : ℝ × I => orbitCircuitDistance H (B - L) (p.1 + p.2.val)) :=
    (orbitCircuitDistance_lipschitz H (B - L)).continuous.comp
      (continuous_fst.add (continuous_subtype_val.comp continuous_snd))
  have hF : IsClosed F := isClosed_le hcont continuous_const
  have heq : (tenthPlateauCore H B L R)ᶜ = Prod.fst '' F := by
    ext z
    constructor
    · intro hz
      rw [mem_compl_iff, tenthPlateauCore, mem_setOf_eq] at hz
      push Not at hz
      obtain ⟨s, hs, j, hfit, hj⟩ := hz
      have hfit' : HasProjectiveCircuitApproximation N (1 / 10 : ℝ) (B - L)
          (unitaryEvolution H.val (z + s)) := by
        obtain ⟨c, hc, C, hC, herr⟩ := hfit
        exact ⟨c, hc, C, hC.trans (by omega), herr⟩
      exact ⟨(z, ⟨s, abs_le.mp hs⟩),
        (hasProjectiveCircuitApproximation_iff_infDist ..).mp hfit', rfl⟩
    · rintro ⟨⟨z', s⟩, hdist, rfl⟩ hcore
      have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ (B - L) (1 / 10 : ℝ)).mpr hdist
      have hlt := hcore s.val (abs_le.mpr s.property) (B - L) hfit
      omega
  rw [← isClosed_compl_iff, heq]
  exact isClosedMap_fst_of_compactSpace _ hF

theorem measurableSet_tenthPlateauCore {N : ℕ} (H : selfAdjoint (Register N)) (B L : ℕ) (R : ℝ) :
    MeasurableSet (tenthPlateauCore H B L R) :=
  (isOpen_tenthPlateauCore H B L R).measurableSet

/-- Any date with distance at least 104/1000 = 13/125 from the B-gate set
centers a radius-R interval in the 1/10 plateau core once local simulation of
|s| ≤ R costs L gates at error 2⁻ᴺ and N ≥ 8. -/
theorem tenthPlateauCore_of_distance_ge {N B L : ℕ} (hN : 8 ≤ N)
    (H : selfAdjoint (Register N)) {R z : ℝ}
    (hsim : ∀ s : ℝ, |s| ≤ R →
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N) L (unitaryEvolution H.val s))
    (hz : (13 / 125 : ℝ) ≤ orbitCircuitDistance H B z) :
    z ∈ tenthPlateauCore H B L R := by
  intro s hs j hfit
  by_contra! hle
  have hrev := hsim (-s) (by rwa [abs_neg])
  have hcomb := affordable_add_time H hfit hrev
  rw [show z + s + -s = z by ring] at hcomb
  obtain ⟨c, hc, C, hC, herr⟩ := hcomb
  have hpow : (256 : ℝ) ≤ (2 : ℝ) ^ N := by
    calc (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
         _ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hinv : 1 / (2 : ℝ) ^ N ≤ 1 / 256 := one_div_le_one_div_of_le (by norm_num) hpow
  have hd := (hasProjectiveCircuitApproximation_iff_infDist _ B (1 / 10 + 1 / 256 : ℝ)).mp
    ⟨c, hc, C, hC.trans hle, herr.trans (by linarith only [hinv])⟩
  change orbitCircuitDistance H B z ≤ _ at hd
  linarith only [hz, hd]

theorem compl_visitSet_subset_tenthPlateauCore {N B L : ℕ} (hN : 8 ≤ N)
    (H : selfAdjoint (Register N)) {R : ℝ}
    (hsim : ∀ s : ℝ, |s| ≤ R →
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N) L (unitaryEvolution H.val s)) :
    (visitSet H B (13 / 125 : ℝ))ᶜ ⊆ tenthPlateauCore H B L R := by
  intro z hz
  apply tenthPlateauCore_of_distance_ge hN H hsim
  by_contra! hlt
  exact hz ((hasProjectiveCircuitApproximation_iff_infDist _ B (13 / 125 : ℝ)).mpr hlt.le)

theorem measureReal_inter_ge_of_sdiff_le {S : Set ℝ} (hS : MeasurableSet S)
    {p G : ℝ} (hp : 0 ≤ p) (hG : 0 ≤ G)
    (hdiff : ∀ a T : ℝ, 0 ≤ T → volume.real (Icc a (a + T) \ S) ≤ p * (T + G))
    (a T : ℝ) (hTG : G ≤ T) :
    (1 - 2 * p) * T ≤ volume.real (S ∩ Icc a (a + T)) := by
  have hT0 : 0 ≤ T := hG.trans hTG
  have hd : Disjoint (S ∩ Icc a (a + T)) (Icc a (a + T) \ S) :=
    disjoint_left.mpr fun _ hx hy => hy.2 hx.1
  have hun : (S ∩ Icc a (a + T)) ∪ (Icc a (a + T) \ S) = Icc a (a + T) := by
    ext x
    constructor
    · rintro (hx | hx); exacts [hx.2, hx.1]
    · intro hx
      by_cases h : x ∈ S
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨hx, h⟩
  have hB : MeasurableSet (Icc a (a + T) \ S) := measurableSet_Icc.diff hS
  have hAfin : volume (S ∩ Icc a (a + T)) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hBfin : volume (Icc a (a + T) \ S) ≠ ⊤ :=
    measure_ne_top_of_subset Set.sdiff_subset measure_Icc_lt_top.ne
  have hsum : volume.real (S ∩ Icc a (a + T)) + volume.real (Icc a (a + T) \ S) = T := by
    rw [← measureReal_union hd hB hAfin hBfin, hun,
      Real.volume_real_Icc_of_le (le_add_of_nonneg_right hT0), add_sub_cancel_left]
  have hB_le : volume.real (Icc a (a + T) \ S) ≤ 2 * p * T := calc
    volume.real (Icc a (a + T) \ S) ≤ p * (T + G) := hdiff a T hT0
    _ ≤ p * (2 * T) := mul_le_mul_of_nonneg_left (by linarith only [hTG]) hp
    _ = 2 * p * T := by ring
  linarith only [hsum, hB_le]

private theorem post_onset_thirty_at_tenth {N J : ℕ} (H : selfAdjoint (Register N))
    {σ : ℝ} (hσ : 0 ≤ σ) (heq : orbitCircuitDistance H J σ = zeroGateArcTolerance (31 / 32))
    (s : ℕ) (hs : s ≤ J / 30) :
    (∀ T : ℝ, σ ≤ T →
      30 * (T - σ) - 3 * σ ≤ 32 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ T)) ∧
    (∀ T : ℝ, (17 / 14 : ℝ) * σ < T →
      T - σ < 2 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ T)) := by
  obtain ⟨hα0, hsin_tenth, h30_pi, h30_lt⟩ := thirty_arcsin_twentieth_lt_arc
  have hj_le : 2 * s * 15 ≤ J := by
    have h1 : 30 * (J / 30) ≤ J := Nat.mul_div_le J 30
    omega
  have hfar : 2 * sin (2 * (15 : ℝ) * arcsin (1 / 20)) < orbitCircuitDistance H J σ := by
    rw [heq, show 2 * (15 : ℝ) * arcsin (1 / 20) = 30 * arcsin (1 / 20) by ring]
    exact h30_lt
  obtain ⟨_, hpost1, hpost2⟩ := post_onset_occupation_of_geodesic_endpoint H hσ
    (q := 15) (by decide) hα0.le (by norm_num only [Nat.cast_ofNat]; linarith only [h30_pi])
    hj_le hfar
  rw [hsin_tenth] at hpost1 hpost2
  norm_num only [Nat.cast_ofNat] at hpost1 hpost2
  exact ⟨fun T hT => by linarith only [hpost1 T hT],
    fun T hT => hpost2 (by decide) T (by simpa only [show ((15 : ℝ) + 2) / ((15 : ℝ) - 1) = 17 / 14 by norm_num] using hT)⟩

theorem thirteen_125_entropy :
    (13 / 125 : ℝ) ∈ Ioo (0 : ℝ) 2 ∧
      log (physicalArc (13 / 125)) + 32 * log 2 / (7 : ℕ) < log (4 / 5) := by
  have hmem : (13 / 125 : ℝ) ∈ Ioo (0 : ℝ) 2 := by constructor <;> norm_num
  refine ⟨hmem, ?_⟩
  obtain ⟨harc, htol⟩ := physicalArc_full hmem
  let u : ℝ := 6283 / 120000
  have hcube := sin_gt_sub_cube (by norm_num : (0 : ℝ) < u)
  have hsin_u : (13 / 125 : ℝ) < 2 * sin u := by
    dsimp only [u] at hcube ⊢
    linarith only [hcube]
  have hpi := pi_gt_d6
  have hu_lt : u < π * (1 / 30) / 2 := by
    dsimp only [u]; linarith only [hpi]
  have htol_lt : zeroGateArcTolerance (physicalArc (13 / 125)) < zeroGateArcTolerance (1 / 30) := by
    rw [htol]
    unfold zeroGateArcTolerance
    exact hsin_u.trans (mul_lt_mul_of_pos_left
      (strictMonoOn_sin ⟨by dsimp only [u]; linarith only [hpi], (hu_lt.trans (by linarith only [hpi])).le⟩
        ⟨by linarith only [hpi], by linarith only [hpi]⟩ hu_lt) two_pos)
  have harc_lt : physicalArc (13 / 125) < 1 / 30 := by
    by_contra! hge
    exact htol_lt.not_ge (strictMonoOn_zeroGateArcTolerance_full.monotoneOn
      ⟨by norm_num, by norm_num⟩ ⟨harc.1.le, harc.2.le⟩ hge)
  have hpow : (physicalArc (13 / 125)) ^ 7 * (2 : ℝ) ^ 32 < (4 / 5 : ℝ) ^ 7 := by
    calc (physicalArc (13 / 125)) ^ 7 * (2 : ℝ) ^ 32
        < (1 / 30 : ℝ) ^ 7 * (2 : ℝ) ^ 32 :=
          mul_lt_mul_of_pos_right (pow_lt_pow_left₀ harc_lt harc.1.le (by decide)) (by positivity)
      _ < (4 / 5 : ℝ) ^ 7 := by norm_num
  have hlog := log_lt_log (mul_pos (pow_pos harc.1 7) (by positivity)) hpow
  rw [log_mul (pow_pos harc.1 7).ne' (by positivity), log_pow, log_pow, log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  linarith only [hlog]

private theorem thirty_one_32_entropy :
    zeroGateArcTolerance (31 / 32) ∈ Ioo (0 : ℝ) 2 ∧
      log (physicalArc (zeroGateArcTolerance (31 / 32))) + 32 * log 2 / (2048 : ℕ) <
        log (127 / 128) := by
  let η := zeroGateArcTolerance (31 / 32)
  have h0 : zeroGateArcTolerance 0 = 0 := by simp [zeroGateArcTolerance]
  have h1 : zeroGateArcTolerance 1 = 2 := by
    unfold zeroGateArcTolerance
    rw [mul_one, sin_pi_div_two, mul_one]
  have hη : η ∈ Ioo (0 : ℝ) 2 := ⟨h0 ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩ (by norm_num),
    h1 ▸ strictMonoOn_zeroGateArcTolerance_full
    ⟨by norm_num, by norm_num⟩ ⟨zero_le_one, le_rfl⟩ (by norm_num)⟩
  obtain ⟨harc, htol⟩ := physicalArc_full hη
  have harc_eq : physicalArc η = 31 / 32 :=
    strictMonoOn_zeroGateArcTolerance_full.injOn ⟨harc.1.le, harc.2.le⟩ ⟨by norm_num, by norm_num⟩ htol
  refine ⟨hη, ?_⟩
  rw [harc_eq]
  have hbern := one_add_mul_le_pow (by norm_num : (-2 : ℝ) ≤ 3 / 124) 64
  have hratio : (2 : ℝ) < (127 / 124 : ℝ) ^ 64 := by
    calc (2 : ℝ) < 1 + 64 * (3 / 124 : ℝ) := by norm_num
         _ ≤ (1 + 3 / 124 : ℝ) ^ 64 := hbern
         _ = (127 / 124 : ℝ) ^ 64 := by norm_num
  have hpow : (31 / 32 : ℝ) ^ 64 * 2 < (127 / 128 : ℝ) ^ 64 := by
    have hm := mul_lt_mul_of_pos_left hratio (by positivity : 0 < (31 / 32 : ℝ) ^ 64)
    rwa [← mul_pow, show (31 / 32 : ℝ) * (127 / 124) = 127 / 128 by norm_num] at hm
  have hlog := log_lt_log (by positivity) hpow
  rw [log_mul (by positivity) (by norm_num), log_pow, log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog ⊢
  linarith only [hlog]

private theorem sublinear_lt_hilbert {β : ℝ} (hβ : β < 1) (q : ℕ) (hq : 0 < q) :
    ∀ᶠ N : ℕ in atTop, ⌊(2 : ℝ) ^ (β * (N : ℝ))⌋₊ ≤ 2 ^ N / (q * (N + 1)) := by
  by_cases hβ0 : β < 0
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hlt1 : (2 : ℝ) ^ (β * (N : ℝ)) < 1 :=
      rpow_lt_one_of_one_lt_of_neg (by norm_num) (mul_neg_of_neg_of_pos hβ0 (by exact_mod_cast hN))
    rw [Nat.floor_eq_zero.mpr hlt1]
    exact Nat.zero_le _
  push Not at hβ0
  let δ := (1 - β) / 2
  have hlim : Tendsto (fun N : ℕ => (q : ℝ) * ((N : ℝ) + 1) / (2 : ℝ) ^ (δ * (N : ℝ))) atTop (𝓝 0) := by
    have hb : 1 < (2 : ℝ) ^ δ := one_lt_rpow (by norm_num) (by dsimp only [δ]; linarith only [hβ])
    have h1 := (tendsto_pow_const_div_const_pow_of_one_lt 1 hb).const_mul (q : ℝ)
    have h0 := (tendsto_pow_const_div_const_pow_of_one_lt 0 hb).const_mul (q : ℝ)
    have hsum : Tendsto (fun N : ℕ => (q : ℝ) * ((N : ℝ) ^ 1 / ((2 : ℝ) ^ δ) ^ N) +
        (q : ℝ) * ((N : ℝ) ^ 0 / ((2 : ℝ) ^ δ) ^ N)) atTop (𝓝 0) := by
      simpa only [mul_zero, add_zero] using h1.add h0
    refine hsum.congr fun N => ?_
    rw [pow_one, pow_zero, ← rpow_natCast ((2 : ℝ) ^ δ) N, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  filter_upwards [hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
    LocalPatches.binary_compiler_envelope hβ0 (show β < β + δ by dsimp only [δ]; linarith only [hβ]),
    eventually_ge_atTop 1] with N hq_small _ hN1
  apply (Nat.le_div_iff_mul_le (Nat.mul_pos hq (Nat.succ_pos N))).mpr
  have hfloor : (⌊(2 : ℝ) ^ (β * (N : ℝ))⌋₊ : ℝ) ≤ (2 : ℝ) ^ (β * (N : ℝ)) :=
    Nat.floor_le (rpow_nonneg (by norm_num) _)
  have hqN : (q : ℝ) * ((N : ℝ) + 1) ≤ (2 : ℝ) ^ (δ * (N : ℝ)) :=
    ((div_lt_iff₀ (rpow_pos_of_pos (by norm_num) _)).mp hq_small).le.trans_eq (one_mul _)
  have hprod : (⌊(2 : ℝ) ^ (β * (N : ℝ))⌋₊ : ℝ) * ((q : ℝ) * ((N : ℝ) + 1)) ≤ (2 : ℝ) ^ N := by
    calc (⌊(2 : ℝ) ^ (β * (N : ℝ))⌋₊ : ℝ) * ((q : ℝ) * ((N : ℝ) + 1))
        ≤ (2 : ℝ) ^ (β * (N : ℝ)) * (2 : ℝ) ^ (δ * (N : ℝ)) :=
          mul_le_mul hfloor hqN (by positivity) (rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ ((β + δ) * (N : ℝ)) := by
          rw [← rpow_add (by norm_num : (0 : ℝ) < 2), add_mul]
      _ ≤ (2 : ℝ) ^ ((1 : ℝ) * (N : ℝ)) := rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right (by dsimp only [δ]; linarith only [hβ]) (Nat.cast_nonneg N))
      _ = (2 : ℝ) ^ N := by rw [one_mul, rpow_natCast]
  exact_mod_cast hprod

/-- Establish the physical complexity plateau at error 1/10, date its first
onset from the identity, and prove it occupies most later times both
immediately after saturation (without phase-clock wait) and in exponential-width
uninterrupted plateau intervals across later horizons. -/
theorem gaussian_tenth_error_plateau_onset_and_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        let G := (2 : ℝ) ^ (D ^ c)
        let B₇ := D / (7 * (N + 1))
        let J := D / (2048 * (N + 1))
        let S := J / 30
        let L := ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊
        let R := (2 : ℝ) ^ (γ * (N : ℝ))
        let η_sat := zeroGateArcTolerance (31 / 32)
        let core := tenthPlateauCore H B₇ L R
        (∃ m : ℕ, B₇ < m ∧ m ≤ (4 * N + 1) * (2 * N + 2) * D ^ 2 ∧
          IsRecurrentOrbitCircuitMaximumAt H (1 / 10) m) ∧
        (∃ m_sat : ℕ, J < m_sat ∧ IsRecurrentOrbitCircuitMaximumAt H η_sat m_sat ∧
          ∃ u_sat : ℝ, 0 ≤ u_sat ∧ ∀ s : ℕ, 30 * s < m_sat → ∀ a T : ℝ, 0 ≤ T →
            16 * volume.real (visitSet H s (1 / 10) ∩ Icc a (a + T)) ≤ T + u_sat) ∧
        (∃ σ_plat σ_sat : ℝ,
          R < σ_plat ∧ orbitCircuitDistance H B₇ σ_plat = 13 / 125 ∧
          (∀ t ∈ Ico 0 σ_plat, orbitCircuitDistance H B₇ t < 13 / 125) ∧
          σ_plat ∈ core ∧
          (1 - (4 / 5 : ℝ) ^ D) * σ_plat ≤ (4 / 5 : ℝ) ^ D * G ∧
          R < σ_sat ∧ orbitCircuitDistance H J σ_sat = η_sat ∧
          (∀ t ∈ Ico 0 σ_sat, orbitCircuitDistance H J t < η_sat) ∧
          (1 - (127 / 128 : ℝ) ^ D) * σ_sat ≤ (127 / 128 : ℝ) ^ D * G ∧
          (∀ s ≤ S, ∀ T : ℝ, σ_sat ≤ T →
            30 * (T - σ_sat) - 3 * σ_sat ≤
              32 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ_sat T)) ∧
          (∀ s ≤ S, ∀ T : ℝ, (17 / 14 : ℝ) * σ_sat < T →
            T - σ_sat < 2 * volume.real ((visitSet H s (1 / 10))ᶜ ∩ Icc σ_sat T))) ∧
        MeasurableSet core ∧
        (∀ a T : ℝ, 0 ≤ T → volume.real (Icc a (a + T) \ core) ≤ (4 / 5 : ℝ) ^ D * (T + G)) ∧
        (∀ a T : ℝ, G ≤ T → (1 - 2 * (4 / 5 : ℝ) ^ D) * T ≤ volume.real (core ∩ Icc a (a + T))) := by
  obtain ⟨c, hfin⟩ := gaussian_finite_hilbert_occupation_full
  refine ⟨c, ?_⟩
  obtain ⟨h13_mem, h13_log⟩ := thirteen_125_entropy
  obtain ⟨h31_mem, h31_log⟩ := thirty_one_32_entropy
  obtain ⟨hα0, hsin_tenth, h30_pi, h30_lt⟩ := thirty_arcsin_twentieth_lt_arc
  filter_upwards [hfin, gaussian_orbit_maximum_full_range,
    LocalPatches.gaussian_exponential_precision_compiler] with ω hocc hmax hcomp
  intro γ α hγ hγα hα
  let β := (α + 1) / 2
  have hαβ : α < β := by dsimp only [β]; linarith only [hα]
  have hβ1 : β < 1 := by dsimp only [β]; linarith only [hα]
  have h10_mem : (1 / 10 : ℝ) ∈ Ioo (0 : ℝ) 2 := by constructor <;> norm_num
  have h10_log : log (physicalArc (1 / 10)) + 32 * log 2 / (7 : ℕ) < 0 := by
    have hm : physicalArc (1 / 10) ≤ physicalArc (13 / 125) := by
      unfold physicalArc
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (arcsin_le_arcsin (by norm_num)) two_pos.le) pi_pos.le
    have hp10 := (physicalArc_full h10_mem).1.1
    have hl := log_le_log hp10 hm
    have hneg : log (4 / 5 : ℝ) < 0 := log_neg (by norm_num) (by norm_num)
    linarith only [hl, h13_log, hneg]
  have h31_neg : log (physicalArc (zeroGateArcTolerance (31 / 32))) + 32 * log 2 / (2048 : ℕ) < 0 := by
    have hneg : log (127 / 128 : ℝ) < 0 := log_neg (by norm_num) (by norm_num)
    linarith only [h31_log, hneg]
  filter_upwards [hocc 7 (by decide) (13 / 125) h13_mem (4 / 5) (by norm_num) h13_log,
    hocc 2048 (by decide) (zeroGateArcTolerance (31 / 32)) h31_mem (127 / 128) (by norm_num) h31_log,
    hmax (1 / 10) h10_mem 7 (by decide) h10_log,
    hmax (zeroGateArcTolerance (31 / 32)) h31_mem 2048 (by decide) h31_neg,
    hcomp 1 γ α hγ hγα hα.le,
    hcomp 1 γ β hγ (hγα.trans hαβ) hβ1.le,
    (tendsto_add_atTop_nat 3).eventually (sublinear_lt_hilbert hβ1 2048 (by decide)),
    eventually_ge_atTop 8] with k hocc7 hocc2048 hm10 hm31 hsimα hsimβ hsubβ hk8
  intro N D u H G B₇ J S L R η_sat core
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  have hN8 : 8 ≤ N := by dsimp only [N]; omega
  have hD0 : D ≠ 0 := (Nat.two_pow_pos N).ne'
  have hG0 : 0 ≤ G := by dsimp only [G]; positivity
  -- Part 1: Orbit maximum at 1/10
  obtain ⟨m, hmB, hm_rec⟩ := hm10
  have hm_cap : m ≤ (4 * N + 1) * (2 * N + 2) * D ^ 2 := by
    obtain ⟨_, w, _, hw, hvisit⟩ := hm_rec.2
    obtain ⟨v, _, hv⟩ := hvisit 0
    obtain ⟨z, hz, C, hC, he⟩ := (DiagonalSynthesis.exact_evolution_gate_cap hN2 H v).approx
      (by norm_num : (0 : ℝ) ≤ 1 / 10)
    exact (hv v ⟨le_rfl, le_add_of_nonneg_right hw.le⟩ z hz C he).trans hC
  -- Part 2: Deep saturation maximum and 15/16 long-window quantile at 1/10
  obtain ⟨m_sat, hmJ, hmsat_rec⟩ := hm31
  obtain ⟨_, w_s, _, hws, hvisit_s⟩ := hmsat_rec.2
  obtain ⟨u_sat, hus0, hfloor_s⟩ := hvisit_s 0
  have hmsat_occ (s : ℕ) (hs : 30 * s < m_sat) (a T : ℝ) (hT : 0 ≤ T) :
      16 * volume.real (visitSet H s (1 / 10) ∩ Icc a (a + T)) ≤ T + u_sat := by
    have hfar : 2 * sin (2 * (15 : ℝ) * arcsin (1 / 20)) < orbitCircuitDistance H (2 * s * 15) u_sat := by
      rw [show 2 * (15 : ℝ) * arcsin (1 / 20) = 30 * arcsin (1 / 20) by ring]
      refine h30_lt.trans_le ?_
      by_contra! hlt
      obtain ⟨z, hz, C, hC, he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ (2 * s * 15) η_sat).mpr hlt.le
      have hc := hfloor_s u_sat ⟨le_rfl, le_add_of_nonneg_right hws.le⟩ z hz C he
      omega
    have hpack := affordable_occupation_of_geodesic_hard_lag H (q := 15) (by decide)
      hα0.le (by norm_num only [Nat.cast_ofNat]; linarith only [h30_pi]) hus0.1 hfar a T hT
    rw [hsin_tenth] at hpack
    norm_num only [Nat.cast_ofNat] at hpack
    exact hpack
  -- Part 3: Core inclusion and measurability
  have hsimα' (s : ℝ) (hs : |s| ≤ R) :
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N) L (unitaryEvolution H.val s) := by
    have h := hsimα s hs
    rw [Nat.one_mul] at h
    exact h
  have hcore_sub : (visitSet H B₇ (13 / 125 : ℝ))ᶜ ⊆ core :=
    compl_visitSet_subset_tenthPlateauCore hN8 H hsimα'
  have hcore_meas : MeasurableSet core := measurableSet_tenthPlateauCore H B₇ L R
  have hcore_diff (a T : ℝ) (hT : 0 ≤ T) :
      volume.real (Icc a (a + T) \ core) ≤ (4 / 5 : ℝ) ^ D * (T + G) := by
    have hsub : Icc a (a + T) \ core ⊆ visitSet H B₇ (13 / 125 : ℝ) ∩ Icc a (a + T) := by
      rintro t ⟨htI, hnc⟩
      exact ⟨by_contra fun hn => hnc (hcore_sub hn), htI⟩
    exact (measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)).trans
      (hocc7 B₇ le_rfl a T hT)
  have hcore_maj : ∀ a T : ℝ, G ≤ T → (1 - 2 * (4 / 5 : ℝ) ^ D) * T ≤ volume.real (core ∩ Icc a (a + T)) :=
    measureReal_inter_ge_of_sdiff_le hcore_meas (pow_nonneg (by norm_num) D) hG0 hcore_diff
  -- Part 4: Two-sided onset dating and immediate post-onset majority
  obtain ⟨σ_plat, hσp_pos, hσp_eq, hσp_prior, hσp_up⟩ := dated_crossing_of_occupation (j := B₇) H
    h13_mem.1 le_rfl (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5) D)
    (pow_lt_one₀ (by norm_num) (by norm_num) hD0) hG0
    (fun T hT => by simpa only [zero_add] using hocc7 B₇ le_rfl 0 T hT)
  obtain ⟨σ_sat, hσs_pos, hσs_eq, hσs_prior, hσs_up⟩ := dated_crossing_of_occupation (j := J) H
    h31_mem.1 le_rfl (pow_nonneg (by norm_num : (0 : ℝ) ≤ 127 / 128) D)
    (pow_lt_one₀ (by norm_num) (by norm_num) hD0) hG0
    (fun T hT => by simpa only [zero_add] using hocc2048 J le_rfl 0 T hT)
  have hJB : J ≤ B₇ := (Nat.le_div_iff_mul_le (by positivity)).mpr <|
    (Nat.mul_le_mul_left J (Nat.mul_le_mul_right (N + 1) (by decide : 7 ≤ 2048))).trans
      (Nat.div_mul_le_self D (2048 * (N + 1)))
  have hearly (t : ℝ) (ht : t ∈ Icc 0 R) : orbitCircuitDistance H J t < 1 / 10 := by
    have habs : |t| ≤ R := by rw [abs_of_nonneg ht.1]; exact ht.2
    obtain ⟨c, hc, C, hC, herr⟩ := hsimβ t habs
    rw [Nat.one_mul] at herr
    have hfitJ : HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ N) J (unitaryEvolution H.val t) :=
      ⟨c, hc, C, hC.trans hsubβ, herr⟩
    have hdJ := (hasProjectiveCircuitApproximation_iff_infDist _ J (1 / (2 : ℝ) ^ N)).mp hfitJ
    have hpow : (256 : ℝ) ≤ (2 : ℝ) ^ N := by
      calc (256 : ℝ) = (2 : ℝ) ^ 8 := by norm_num
           _ ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN8
    have hinv : 1 / (2 : ℝ) ^ N < 1 / 10 :=
      (one_div_le_one_div_of_le (by norm_num) hpow).trans_lt (by norm_num)
    exact hdJ.trans_lt hinv
  have hR_lt_plat : R < σ_plat := by
    by_contra! hle
    have hJb : orbitCircuitDistance H B₇ σ_plat ≤ orbitCircuitDistance H J σ_plat := by
      apply (hasProjectiveCircuitApproximation_iff_infDist _ B₇ _).mp
      obtain ⟨z, hz, C, hC, he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ J _).mpr
        (le_rfl : orbitCircuitDistance H J σ_plat ≤ _)
      exact ⟨z, hz, C, hC.trans hJB, he⟩
    have hlt := hJb.trans_lt (hearly σ_plat ⟨hσp_pos.le, hle⟩)
    rw [hσp_eq] at hlt
    norm_num at hlt
  have hR_lt_sat : R < σ_sat := by
    by_contra! hle
    have hlt := hearly σ_sat ⟨hσs_pos.le, hle⟩
    rw [hσs_eq] at hlt
    have h10_lt_η : (1 / 10 : ℝ) < η_sat := by
      calc (1 / 10 : ℝ) = 2 * sin (arcsin (1 / 20)) := hsin_tenth.symm
           _ < 2 * sin (30 * arcsin (1 / 20)) := mul_lt_mul_of_pos_left
               (strictMonoOn_sin ⟨by linarith only [hα0, pi_pos], by linarith only [hα0, h30_pi]⟩
                 ⟨by linarith only [hα0, pi_pos], h30_pi⟩ (by linarith only [hα0])) two_pos
           _ < η_sat := h30_lt
    linarith only [hlt, h10_lt_η]
  have hσp_core : σ_plat ∈ core :=
    tenthPlateauCore_of_distance_ge hN8 H hsimα' hσp_eq.ge
  refine ⟨⟨m, hmB, hm_cap, hm_rec⟩,
    ⟨m_sat, hmJ, hmsat_rec, u_sat, hus0.1, hmsat_occ⟩,
    ⟨σ_plat, σ_sat, hR_lt_plat, hσp_eq, hσp_prior, hσp_core, hσp_up,
      hR_lt_sat, hσs_eq, hσs_prior, hσs_up,
      fun s hs => (post_onset_thirty_at_tenth H hσs_pos.le hσs_eq s hs).1,
      fun s hs => (post_onset_thirty_at_tenth H hσs_pos.le hσs_eq s hs).2⟩,
    hcore_meas, hcore_diff, hcore_maj⟩

#print axioms isOpen_tenthPlateauCore
#print axioms compl_visitSet_subset_tenthPlateauCore
#print axioms gaussian_tenth_error_plateau_onset_and_occupation

/-- Quadratic-precision local compilation produces recurrent radius-2^(γN)
intervals at error 1/10 within ⌊2^(αN)⌋₊ gates of the orbit maximum at
1/10 + 2^(1 - ⌊δ²N²⌋), with no exceptional-tolerance exclusion. -/
theorem gaussian_tenth_error_quadratic_precision_intervals :
    ∃ C : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw,
      ∀ γ α : ℝ, 0 ≤ γ → γ < α → α < 1 → ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        let b := ⌊(((α - γ) / 12) ^ 2) * (N : ℝ) ^ 2⌋₊
        let ε_quad := (1 / 10 : ℝ) + 2 / (2 : ℝ) ^ b
        ∃ m > D / (7 * (N + 1)), IsRecurrentOrbitCircuitMaximumAt H ε_quad m ∧
          ∀ a : ℝ, ∃ z ∈ Icc a (a + (2 : ℝ) ^ (D ^ C)),
            ∀ t : ℝ, |t| ≤ (2 : ℝ) ^ (γ * (N : ℝ)) → ∀ j : ℕ,
              HasProjectiveCircuitApproximation N (1 / 10 : ℝ) j (unitaryEvolution H.val (z + t)) →
                m ≤ j + ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊ := by
  obtain ⟨C, hprof⟩ := SpectralJets.HighPrecision.gaussian_uniform_profile_recurrence
  refine ⟨C, ?_⟩
  obtain ⟨h13_mem, h13_log⟩ := thirteen_125_entropy
  have h13_neg : log (physicalArc (13 / 125)) + 32 * log 2 / (7 : ℕ) < 0 := by
    have hneg : log (4 / 5 : ℝ) < 0 := log_neg (by norm_num) (by norm_num)
    linarith only [h13_log, hneg]
  filter_upwards [hprof, gaussian_orbit_maximum_full_range,
    LocalPatches.gaussian_binary_precision_compiler] with ω hrep hmax hbin
  intro γ α hγ hγα hα
  let δ := (α - γ) / 12
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hγα]
  have hquad_large : ∀ᶠ N : ℕ in atTop, 9 ≤ ⌊δ ^ 2 * (N : ℝ) ^ 2⌋₊ ∧
      (N : ℝ) ≤ 3 * δ ^ 2 * (N : ℝ) ^ 2 ∧ ⌊δ ^ 2 * (N : ℝ) ^ 2⌋₊ ≤ 2 ^ N := by
    obtain ⟨M₁, hM₁⟩ := exists_nat_gt (max (4 / δ) (1 / (3 * δ ^ 2)))
    have hlim : Tendsto (fun N : ℕ => δ ^ 2 * (N : ℝ) ^ 2 / (2 : ℝ) ^ N) atTop (𝓝 0) := by
      simpa only [mul_div_assoc', mul_zero] using
        (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).const_mul (δ ^ 2)
    filter_upwards [eventually_ge_atTop (M₁ + 1),
      hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with N hNM hN2
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hM_lt : max (4 / δ) (1 / (3 * δ ^ 2)) < (N : ℝ) :=
      hM₁.trans_le (by exact_mod_cast (by omega : M₁ ≤ N))
    have h4 : 4 < (N : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp ((le_max_left (4 / δ) (1 / (3 * δ ^ 2))).trans_lt hM_lt)
    have h16 : (9 : ℝ) ≤ δ ^ 2 * (N : ℝ) ^ 2 := by nlinarith only [h4]
    have h3 : 1 < (N : ℝ) * (3 * δ ^ 2) :=
      (div_lt_iff₀ (by positivity)).mp ((le_max_right (4 / δ) (1 / (3 * δ ^ 2))).trans_lt hM_lt)
    have hfloor_le : (⌊δ ^ 2 * (N : ℝ) ^ 2⌋₊ : ℝ) ≤ (2 : ℝ) ^ N :=
      (Nat.floor_le (by positivity)).trans (((div_lt_iff₀ (by positivity)).mp hN2).le.trans_eq (one_mul _))
    exact ⟨Nat.le_floor h16, by nlinarith only [h3, hN_pos], by exact_mod_cast hfloor_le⟩
  filter_upwards [hrep, hmax (13 / 125) h13_mem 7 (by decide) h13_neg,
    (tendsto_add_atTop_nat 1).eventually hbin,
    (tendsto_add_atTop_nat 3).eventually hquad_large,
    (tendsto_add_atTop_nat 3).eventually
      (LocalPatches.binary_compiler_envelope hγ (show γ < γ + (α - γ) / 6 by linarith only [hγα])),
    (tendsto_add_atTop_nat 3).eventually
      (LocalPatches.binary_compiler_envelope hγ hγα)] with k hr hm13 hcomp hql henv1 henv2
  intro N D u H b ε_quad
  obtain ⟨hb9, hN_le_3, hb_le_D⟩ := hql
  have hN2 : 2 ≤ N := by dsimp only [N]; omega
  have hε_pos : 0 < ε_quad := by dsimp only [ε_quad]; positivity
  have hε_le_13 : ε_quad ≤ 13 / 125 := by
    have hpow : (512 : ℝ) ≤ (2 : ℝ) ^ b := by
      calc (512 : ℝ) = (2 : ℝ) ^ 9 := by norm_num
           _ ≤ (2 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hb9
    have h2 : 2 / (2 : ℝ) ^ b ≤ 2 / 512 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpow
    dsimp only [ε_quad]; linarith only [h2]
  obtain ⟨m₁₃, hm13_gt, hm13_rec⟩ := hm13
  obtain ⟨m, hm_rec⟩ := twoLocal_exists_recurrent_maximum_at hN2 H
    (hasPauliWeightAtMost_pathHamiltonian u (isSelfAdjoint_pathHamiltonian u)) ε_quad hε_pos
  have hm_ge : m₁₃ ≤ m := by
    obtain ⟨t, ht⟩ := MaximumIntervals.required_at_some_date hm13_rec
    obtain ⟨z, hz, C, hC, herr⟩ := hm_rec.1 t
    exact ht m ⟨z, hz, C, hC, herr.trans hε_le_13⟩
  let d := b + N
  have hsim_quad (t : ℝ) (ht : |t| ≤ (2 : ℝ) ^ (γ * (N : ℝ))) :
      HasProjectiveCircuitApproximation N (1 / (2 : ℝ) ^ b) ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊
        (unitaryEvolution H.val t) := by
    have hF1 : 1 ≤ (2 : ℝ) ^ (5 * N.sqrt + 17) := one_le_pow₀ (by norm_num)
    have hvolN : (N : ℝ) * (1 + |t|) ≤ (2 : ℝ) ^ N := by
      have h1 : (N : ℝ) * (1 + |t|) ≤ (2 : ℝ) ^ (α * (N : ℝ)) :=
        (le_mul_of_one_le_right (by positivity) hF1).trans
          ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right ht 1) (Nat.cast_nonneg N))
            (zero_le_one.trans hF1)).trans henv2)
      refine h1.trans ?_
      simpa only [one_mul, rpow_natCast] using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (mul_le_mul_of_nonneg_right hα.le (Nat.cast_nonneg N))
    have hscaled : (2 : ℝ) ^ b * ((N : ℝ) * (1 + |t|)) ≤ (2 : ℝ) ^ d :=
      (mul_le_mul_of_nonneg_left hvolN (by positivity)).trans_eq (by dsimp only [d]; rw [pow_add (2 : ℝ) b N])
    obtain ⟨s, hfit, hs_le⟩ := hcomp t b d (Nat.le_add_left N b) hscaled
    have hdsqrt : (d.sqrt : ℝ) ≤ 2 * δ * (N : ℝ) := by
      have hd_le : (d : ℝ) ≤ (2 * δ * (N : ℝ)) ^ 2 := by
        have hfl : (b : ℝ) ≤ δ ^ 2 * (N : ℝ) ^ 2 := Nat.floor_le (by positivity)
        dsimp only [d]; push_cast
        nlinarith only [hfl, hN_le_3]
      have hsq : ((d.sqrt : ℝ)) ^ 2 ≤ (d : ℝ) := by exact_mod_cast Nat.sqrt_le' d
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp (hsq.trans hd_le)
    have hs_exp : (s : ℝ) ≤ (2 : ℝ) ^ (α * (N : ℝ)) := by
      have hbase : (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ ((γ + (α - γ) / 6) * (N : ℝ)) := by
        have h17 : (2 : ℝ) ^ 17 ≤ (2 : ℝ) ^ (5 * N.sqrt + 17) :=
          pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 17 _)
        exact (mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right ht 1) (Nat.cast_nonneg N))
          h17 (by positivity) (by positivity)).trans henv1
      have h5 : ((2 : ℝ) ^ (5 * d.sqrt) : ℝ) ≤ (2 : ℝ) ^ ((5 / 6 * (α - γ)) * (N : ℝ)) := by
        rw [← rpow_natCast]
        apply rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        dsimp only [δ] at hdsqrt
        linarith only [hdsqrt]
      calc (s : ℝ) ≤ (N : ℝ) * (1 + |t|) * (2 : ℝ) ^ (5 * d.sqrt + 17) := hs_le
           _ = ((N : ℝ) * (1 + |t|) * (2 : ℝ) ^ 17) * (2 : ℝ) ^ (5 * d.sqrt) := by rw [pow_add]; ring
           _ ≤ (2 : ℝ) ^ ((γ + (α - γ) / 6) * (N : ℝ)) * (2 : ℝ) ^ ((5 / 6 * (α - γ)) * (N : ℝ)) :=
               mul_le_mul hbase h5 (by positivity) (by positivity)
           _ = (2 : ℝ) ^ (α * (N : ℝ)) := by
               rw [← rpow_add (by norm_num : (0 : ℝ) < 2)]
               congr 1; ring
    exact LocalPatches.approx_enlarge hfit le_rfl (Nat.le_floor hs_exp)
  obtain ⟨v, hv⟩ := MaximumIntervals.required_at_some_date hm_rec
  refine ⟨m, hm13_gt.trans_le hm_ge, hm_rec, fun a => ?_⟩
  obtain ⟨z, hz, hz_prof⟩ := hr a v
  have hr_le : 1 / (2 : ℝ) ^ D ≤ 1 / (2 : ℝ) ^ b :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hb_le_D)
  refine ⟨z, hz, fun t ht j hfit => ?_⟩
  have hh := affordable_add_time H hfit (hsim_quad (-t) (by rwa [abs_neg]))
  rw [show z + t + -t = z by ring] at hh
  have hd_z : orbitCircuitDistance H (j + ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊) z ≤ 1 / 10 + 1 / (2 : ℝ) ^ b :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mp hh
  have hgap := (abs_le.mp (hz_prof 0 (j + ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊))).1
  simp only [add_zero] at hgap
  apply hv (j + ⌊(2 : ℝ) ^ (α * (N : ℝ))⌋₊)
  apply (hasProjectiveCircuitApproximation_iff_infDist ..).mpr
  change orbitCircuitDistance H _ v ≤ (1 / 10 : ℝ) + 2 / (2 : ℝ) ^ b
  change -(1 / (2 : ℝ) ^ D) ≤ orbitCircuitDistance H _ z - orbitCircuitDistance H _ v at hgap
  have htwo : 1 / (2 : ℝ) ^ b + 1 / (2 : ℝ) ^ b = 2 / (2 : ℝ) ^ b := by ring
  linarith only [hd_z, hgap, hr_le, htwo]

#print axioms gaussian_tenth_error_quadratic_precision_intervals
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.TenthPlateau
