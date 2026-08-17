import GaloisForLFunctions.RHTower.ProlateSmallApertureIndexedSeparation
import GaloisForLFunctions.RHTower.ProlateEvenCrossSpectralContinuity
import GaloisForLFunctions.HTGeometry.DerivSignMonotone

open MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

theorem bandOperatorL2_unitBandEvenProjection (c : ℝ)
    (f : RealIntervalL2 (-1 : ℝ) 1) :
    bandOperatorL2 c (unitBandEvenProjection f) =
      unitBandEvenProjection (bandOperatorL2 c f) := by
  simp only [unitBandEvenProjection_apply, map_smul, map_add,
    bandOperatorL2_unitBandReflection]

theorem exists_evenProlateSignedValue_sq_eq_of_bandEigen_evenProjection_ne
    {a lam : ℝ} (ha : 0 < a) (hlam : lam ≠ 0)
    {psi : RealIntervalL2 (-1 : ℝ) 1}
    (hproj : unitBandEvenProjection psi ≠ 0)
    (heig : bandOperatorL2 (signedModeRadialBandwidth a) psi = lam • psi) :
    ∃ n : ℕ, evenProlateSignedValue a n ^ 2 = lam := by
  let u : unitBandEvenSubspace :=
    ⟨unitBandEvenProjection psi,
      (mem_unitBandEvenSubspace_iff _).2 (unitBandReflection_evenProjection psi)⟩
  have huNe : u ≠ 0 := by
    intro h
    exact hproj (congrArg Subtype.val h)
  let z : complexUnitBandEvenSubspace := complexifyUnitBandEven u
  have hzNe : z ≠ 0 := complexifyUnitBandEven_ne_zero huNe
  have huEig : unitBandEvenBlock (signedModeRadialBandwidth a) u = lam • u := by
    apply Subtype.ext
    change bandOperatorL2 (signedModeRadialBandwidth a)
        (unitBandEvenProjection psi) = lam • unitBandEvenProjection psi
    rw [bandOperatorL2_unitBandEvenProjection, heig, map_smul]
  have hzEig : complexUnitBandEvenBlock (signedModeRadialBandwidth a) z =
      (lam : ℂ) • z := by
    rw [show z = complexifyUnitBandEven u from rfl,
      complexUnitBandEvenBlock_complexifyUnitBandEven, huEig]
    apply Subtype.ext
    exact ofRealLp_real_smul lam (u : RealIntervalL2 (-1 : ℝ) 1)
  exact exists_evenProlateSignedValue_sq_eq_of_complexUnitBandEvenBlock_eigen
    ha hlam hzNe (by simpa [signedModeRadialBandwidth] using hzEig)

/-- A continuous live band eigenbranch born from canonical even index `m` cannot change its
index locally.  The proof uses only even projection, exact spectral exhaustion, strict simplicity,
and the two adjacent continuous indexed eigenvalues. -/
theorem eventually_bandEigenbranch_eq_evenProlateSignedValue_sq
    {a₀ : ℝ} (ha₀ : 0 < a₀) (m : ℕ)
    {psi : ℝ → RealIntervalL2 (-1 : ℝ) 1} {nu : ℝ → ℝ}
    (hpsi : ContinuousAt psi (signedModeRadialBandwidth a₀))
    (hnu : ContinuousAt nu (signedModeRadialBandwidth a₀))
    (hpsiEven : psi (signedModeRadialBandwidth a₀) ∈ unitBandEvenSubspace)
    (hpsiUnit : (inner ℝ (psi (signedModeRadialBandwidth a₀))
      (psi (signedModeRadialBandwidth a₀)) : ℝ) = 1)
    (hnu₀ : nu (signedModeRadialBandwidth a₀) =
      evenProlateSignedValue a₀ m ^ 2)
    (heig : ∀ᶠ c in 𝓝 (signedModeRadialBandwidth a₀),
      bandOperatorL2 c (psi c) = nu c • psi c ∧
        (inner ℝ (psi c) (psi c) : ℝ) = 1) :
    ∀ᶠ a in 𝓝 a₀,
      nu (signedModeRadialBandwidth a) = evenProlateSignedValue a m ^ 2 := by
  let bw : ℝ → ℝ := fun a => signedModeRadialBandwidth a
  have hbw : Continuous bw := by
    dsimp only [bw, signedModeRadialBandwidth]
    fun_prop
  have hbwt : Tendsto bw (𝓝 a₀) (𝓝 (bw a₀)) := hbw.continuousAt
  have hpsiA : ContinuousAt (fun a => psi (bw a)) a₀ := by
    simpa only [Function.comp_def, bw] using hpsi.comp hbwt
  have hnuA : ContinuousAt (fun a => nu (bw a)) a₀ := by
    simpa only [Function.comp_def, bw] using hnu.comp hbwt
  have hpsiNe : psi (signedModeRadialBandwidth a₀) ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hpsiUnit
    exact zero_ne_one hpsiUnit
  have hprojBase : unitBandEvenProjection
      (psi (signedModeRadialBandwidth a₀)) =
        psi (signedModeRadialBandwidth a₀) := by
    rw [unitBandEvenProjection_apply,
      (mem_unitBandEvenSubspace_iff _).mp hpsiEven]
    module
  have hprojA : ContinuousAt
      (fun a => unitBandEvenProjection (psi (bw a))) a₀ := by
    have h := unitBandEvenProjection.continuous.continuousAt.comp hpsiA
    simpa only [Function.comp_def] using h
  have hprojNe : ∀ᶠ a in 𝓝 a₀,
      unitBandEvenProjection (psi (bw a)) ≠ 0 := by
    apply hprojA.eventually_ne
    rw [show bw a₀ = signedModeRadialBandwidth a₀ from rfl, hprojBase]
    exact hpsiNe
  have hnuNeBase : nu (bw a₀) ≠ 0 := by
    rw [show bw a₀ = signedModeRadialBandwidth a₀ from rfl, hnu₀]
    exact pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha₀ m)
  have hnuNe : ∀ᶠ a in 𝓝 a₀, nu (bw a) ≠ 0 :=
    hnuA.eventually_ne hnuNeBase
  have heigA : ∀ᶠ a in 𝓝 a₀,
      bandOperatorL2 (bw a) (psi (bw a)) = nu (bw a) • psi (bw a) ∧
        (inner ℝ (psi (bw a)) (psi (bw a)) : ℝ) = 1 :=
    hbwt.eventually (by simpa only [bw] using heig)
  have haPos : ∀ᶠ a in 𝓝 a₀, 0 < a := Ioi_mem_nhds ha₀
  have hspec : ∀ᶠ a in 𝓝 a₀,
      ∃ k : ℕ, evenProlateSignedValue a k ^ 2 = nu (bw a) := by
    filter_upwards [haPos, hnuNe, hprojNe, heigA]
      with a ha hlam hproj heigNow
    exact exists_evenProlateSignedValue_sq_eq_of_bandEigen_evenProjection_ne
      ha hlam hproj (by simpa only [bw] using heigNow.1)
  have hcontValue (k : ℕ) :
      ContinuousAt (fun a => evenProlateSignedValue a k ^ 2) a₀ :=
    (continuousOn_evenProlateSignedValue_sq k).continuousAt (Ioi_mem_nhds ha₀)
  cases m with
  | zero =>
      let mid := (evenProlateSignedValue a₀ 0 ^ 2 +
        evenProlateSignedValue a₀ 1 ^ 2) / 2
      have hgap := evenProlateSignedValue_sq_strictAnti ha₀ (show 0 < 1 by omega)
      have hmid : evenProlateSignedValue a₀ 1 ^ 2 < mid ∧
          mid < evenProlateSignedValue a₀ 0 ^ 2 := by
        dsimp only [mid]
        constructor <;> linarith
      have hnuLower : ∀ᶠ a in 𝓝 a₀, mid < nu (bw a) := by
        apply hnuA.eventually_const_lt
        simpa only [bw, hnu₀] using hmid.2
      have honeUpper : ∀ᶠ a in 𝓝 a₀,
          evenProlateSignedValue a 1 ^ 2 < mid :=
        (hcontValue 1).eventually_lt_const hmid.1
      filter_upwards [haPos, hspec, hnuLower, honeUpper]
        with a ha hka hnuLo honeHi
      obtain ⟨k, hk⟩ := hka
      cases k with
      | zero => exact hk.symm
      | succ k =>
          have hle : evenProlateSignedValue a (k + 1) ^ 2 ≤
              evenProlateSignedValue a 1 ^ 2 :=
            (evenProlateSignedValue_sq_strictAnti ha).antitone (by omega)
          rw [hk] at hle
          linarith
  | succ p =>
      let upper := (evenProlateSignedValue a₀ p ^ 2 +
        evenProlateSignedValue a₀ (p + 1) ^ 2) / 2
      let lower := (evenProlateSignedValue a₀ (p + 1) ^ 2 +
        evenProlateSignedValue a₀ (p + 2) ^ 2) / 2
      have hgapUp := evenProlateSignedValue_sq_strictAnti ha₀
        (show p < p + 1 by omega)
      have hgapDown := evenProlateSignedValue_sq_strictAnti ha₀
        (show p + 1 < p + 2 by omega)
      have hupper : evenProlateSignedValue a₀ (p + 1) ^ 2 < upper ∧
          upper < evenProlateSignedValue a₀ p ^ 2 := by
        dsimp only [upper]
        constructor <;> linarith
      have hlower : evenProlateSignedValue a₀ (p + 2) ^ 2 < lower ∧
          lower < evenProlateSignedValue a₀ (p + 1) ^ 2 := by
        dsimp only [lower]
        constructor <;> linarith
      have hnuUpper : ∀ᶠ a in 𝓝 a₀, nu (bw a) < upper := by
        apply hnuA.eventually_lt_const
        simpa only [bw, hnu₀] using hupper.1
      have hpredLower : ∀ᶠ a in 𝓝 a₀,
          upper < evenProlateSignedValue a p ^ 2 :=
        (hcontValue p).eventually_const_lt hupper.2
      have hnuLower : ∀ᶠ a in 𝓝 a₀, lower < nu (bw a) := by
        apply hnuA.eventually_const_lt
        simpa only [bw, hnu₀] using hlower.2
      have hsuccUpper : ∀ᶠ a in 𝓝 a₀,
          evenProlateSignedValue a (p + 2) ^ 2 < lower :=
        (hcontValue (p + 2)).eventually_lt_const hlower.1
      filter_upwards [haPos, hspec, hnuUpper, hpredLower, hnuLower, hsuccUpper]
        with a ha hka hnuHi hpredLo hnuLo hsuccHi
      obtain ⟨k, hk⟩ := hka
      rcases lt_trichotomy k (p + 1) with hlt | heq | hgt
      · have hle : evenProlateSignedValue a p ^ 2 ≤
            evenProlateSignedValue a k ^ 2 :=
          (evenProlateSignedValue_sq_strictAnti ha).antitone (by omega)
        rw [hk] at hle
        linarith
      · subst k
        simpa only [bw] using hk.symm
      · have hle : evenProlateSignedValue a k ^ 2 ≤
            evenProlateSignedValue a (p + 2) ^ 2 :=
          (evenProlateSignedValue_sq_strictAnti ha).antitone (by omega)
        rw [hk] at hle
        linarith

theorem normalizedSecondPairingL2_smul_smul
    (c nuF nuG r s : ℝ)
    (f g : RealIntervalL2 (-1 : ℝ) 1) (hr : r ≠ 0) (hs : s ≠ 0) :
    normalizedSecondPairingL2 c nuF nuG (r • f) (s • g) =
      normalizedSecondPairingL2 c nuF nuG f g := by
  simp only [normalizedSecondPairingL2, bandEigenExtensionEndpointL2,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  field_simp [hr, hs]

theorem normalizedSecondPairingL2_eq_signedMode_of_bandEigen
    {a nuM nuN : ℝ} (ha : 0 < a) (m n : ℕ)
    {psiM psiN : RealIntervalL2 (-1 : ℝ) 1}
    (hnuM : nuM = evenProlateSignedValue a m ^ 2)
    (hnuN : nuN = evenProlateSignedValue a n ^ 2)
    (hpsiMEig : bandOperatorL2 (signedModeRadialBandwidth a) psiM = nuM • psiM)
    (hpsiNEig : bandOperatorL2 (signedModeRadialBandwidth a) psiN = nuN • psiN)
    (hpsiMUnit : (inner ℝ psiM psiM : ℝ) = 1)
    (hpsiNUnit : (inner ℝ psiN psiN : ℝ) = 1) :
    normalizedSecondPairingL2 (signedModeRadialBandwidth a) nuM nuN psiM psiN =
      ∫ x in (-1 : ℝ)..1,
        deriv (deriv (signedModeRadialData a m).R) x *
          (signedModeRadialData a n).R x := by
  let Dm := signedModeRadialData a m
  let Dn := signedModeRadialData a n
  have hm := signedModeRadialData_isExact_of_pos ha m
  have hn := signedModeRadialData_isExact_of_pos ha n
  rcases hm with ⟨_, _, _, _, hmRdef, hmRSmooth, _, hmROne, hmBand,
    _, _, _, _, _⟩
  rcases hn with ⟨_, _, _, _, hnRdef, hnRSmooth, _, hnROne, hnBand,
    _, _, _, _, _⟩
  let fm := bandClass Dm.R hmRSmooth.continuous
  let fn := bandClass Dn.R hnRSmooth.continuous
  let lamM := evenProlateSignedValue a m ^ 2
  let lamN := evenProlateSignedValue a n ^ 2
  have hmBandR : ∀ x : ℝ, bandTransform (signedModeRadialBandwidth a) Dm.R x =
      lamM * Dm.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a m).R x =
        evenProlateSignedValue a m ^ 2 * (signedModeRadialData a m).R x
    rw [hmRdef]
    exact bandTransform_endpointNormalize_eigen hmBand
  have hnBandR : ∀ x : ℝ, bandTransform (signedModeRadialBandwidth a) Dn.R x =
      lamN * Dn.R x := by
    change ∀ x : ℝ,
      bandTransform (signedModeRadialBandwidth a) (signedModeRadialData a n).R x =
        evenProlateSignedValue a n ^ 2 * (signedModeRadialData a n).R x
    rw [hnRdef]
    exact bandTransform_endpointNormalize_eigen hnBand
  have hlamM : lamM ≠ 0 := pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha m)
  have hlamN : lamN ≠ 0 := pow_ne_zero 2 (evenProlateSignedValue_ne_zero ha n)
  have hfm : fm ≠ 0 :=
    bandClass_ne_zero_of_global_band_eigen hmRSmooth.continuous hlamM (by
      intro hzero
      have h := congrFun hzero 1
      rw [hmROne] at h
      exact one_ne_zero h) hmBandR
  have hfn : fn ≠ 0 :=
    bandClass_ne_zero_of_global_band_eigen hnRSmooth.continuous hlamN (by
      intro hzero
      have h := congrFun hzero 1
      rw [hnROne] at h
      exact one_ne_zero h) hnBandR
  let canonM : RealIntervalL2 (-1 : ℝ) 1 := (‖fm‖ : ℝ)⁻¹ • fm
  let canonN : RealIntervalL2 (-1 : ℝ) 1 := (‖fn‖ : ℝ)⁻¹ • fn
  have hcanonMNe : canonM ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hfm)) hfm
  have hcanonNNe : canonN ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hfn)) hfn
  have hfmEig : bandOperatorL2 (signedModeRadialBandwidth a) fm = lamM • fm :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hmRSmooth.continuous hmBandR
  have hfnEig : bandOperatorL2 (signedModeRadialBandwidth a) fn = lamN • fn :=
    bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hnRSmooth.continuous hnBandR
  have hcanonMEig : bandOperatorL2 (signedModeRadialBandwidth a) canonM =
      lamM • canonM := by
    dsimp only [canonM]
    rw [map_smul, hfmEig, smul_comm]
  have hcanonNEig : bandOperatorL2 (signedModeRadialBandwidth a) canonN =
      lamN • canonN := by
    dsimp only [canonN]
    rw [map_smul, hfnEig, smul_comm]
  have hpsiMNe : psiM ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hpsiMUnit
    exact zero_ne_one hpsiMUnit
  have hpsiNNe : psiN ≠ 0 := by
    intro hzero
    rw [hzero, inner_zero_left] at hpsiNUnit
    exact zero_ne_one hpsiNUnit
  obtain ⟨r, hr⟩ := bandOperatorL2_eigenvectors_proportional
    (by dsimp [signedModeRadialBandwidth]; positivity) hlamM
    hcanonMEig hcanonMNe (by simpa only [hnuM] using hpsiMEig)
  obtain ⟨s, hs⟩ := bandOperatorL2_eigenvectors_proportional
    (by dsimp [signedModeRadialBandwidth]; positivity) hlamN
    hcanonNEig hcanonNNe (by simpa only [hnuN] using hpsiNEig)
  have hrNe : r ≠ 0 := by
    intro hzero
    apply hpsiMNe
    rw [hr, hzero, zero_smul]
  have hsNe : s ≠ 0 := by
    intro hzero
    apply hpsiNNe
    rw [hs, hzero, zero_smul]
  rw [hnuM, hnuN, hr, hs,
    normalizedSecondPairingL2_smul_smul _ _ _ _ _ _ _ hrNe hsNe]
  simpa only [Dm, Dn, fm, fn, canonM, canonN, lamM, lamN] using
    normalizedSecondPairingL2_signedMode_eq ha m n

theorem continuousAt_signedModeRadialData_secondDerivPairing
    {a₀ : ℝ} (ha₀ : 0 < a₀) (m n : ℕ) :
    ContinuousAt (fun a : ℝ =>
      ∫ x in (-1 : ℝ)..1,
        deriv (deriv (signedModeRadialData a m).R) x *
          (signedModeRadialData a n).R x) a₀ := by
  obtain ⟨psiM, psiN, nuM, nuN, hpsiM, hnuM, hdpsiM, hdnuM, heigM,
    hpsiN, hnuN, hdpsiN, hdnuN, heigN, hcont, hbase⟩ :=
    exists_local_continuous_signedMode_crossPairing ha₀ m n
  let bw : ℝ → ℝ := fun a => signedModeRadialBandwidth a
  have hbw : Continuous bw := by
    dsimp only [bw, signedModeRadialBandwidth]
    fun_prop
  have hbwt : Tendsto bw (𝓝 a₀) (𝓝 (bw a₀)) := hbw.continuousAt
  have hpsiMEven : psiM (signedModeRadialBandwidth a₀) ∈
      unitBandEvenSubspace := by
    rw [hpsiM]
    apply Submodule.smul_mem
    exact bandClass_mem_unitBandEvenSubspace_of_even
      (signedModeRadialData_isExact_of_pos ha₀ m).2.2.2.2.2.1.continuous
      (signedModeRadialData_isExact_of_pos ha₀ m).2.2.2.2.2.2.1
  have hpsiNEven : psiN (signedModeRadialBandwidth a₀) ∈
      unitBandEvenSubspace := by
    rw [hpsiN]
    apply Submodule.smul_mem
    exact bandClass_mem_unitBandEvenSubspace_of_even
      (signedModeRadialData_isExact_of_pos ha₀ n).2.2.2.2.2.1.continuous
      (signedModeRadialData_isExact_of_pos ha₀ n).2.2.2.2.2.2.1
  have hlabelM := eventually_bandEigenbranch_eq_evenProlateSignedValue_sq
    ha₀ m hdpsiM.continuousAt hdnuM.continuousAt hpsiMEven
      (heigM.self_of_nhds).2 hnuM heigM
  have hlabelN := eventually_bandEigenbranch_eq_evenProlateSignedValue_sq
    ha₀ n hdpsiN.continuousAt hdnuN.continuousAt hpsiNEven
      (heigN.self_of_nhds).2 hnuN heigN
  have heigMA : ∀ᶠ a in 𝓝 a₀,
      bandOperatorL2 (bw a) (psiM (bw a)) = nuM (bw a) • psiM (bw a) ∧
        (inner ℝ (psiM (bw a)) (psiM (bw a)) : ℝ) = 1 :=
    hbwt.eventually (by simpa only [bw] using heigM)
  have heigNA : ∀ᶠ a in 𝓝 a₀,
      bandOperatorL2 (bw a) (psiN (bw a)) = nuN (bw a) • psiN (bw a) ∧
        (inner ℝ (psiN (bw a)) (psiN (bw a)) : ℝ) = 1 :=
    hbwt.eventually (by simpa only [bw] using heigN)
  have haPos : ∀ᶠ a in 𝓝 a₀, 0 < a := Ioi_mem_nhds ha₀
  have heq : (fun a : ℝ =>
      ∫ x in (-1 : ℝ)..1,
        deriv (deriv (signedModeRadialData a m).R) x *
          (signedModeRadialData a n).R x) =ᶠ[𝓝 a₀]
      (fun a => normalizedSecondPairingL2 (bw a)
        (nuM (bw a)) (nuN (bw a)) (psiM (bw a)) (psiN (bw a))) := by
    filter_upwards [haPos, hlabelM, hlabelN, heigMA, heigNA]
      with a ha hmLabel hnLabel hmEig hnEig
    exact (normalizedSecondPairingL2_eq_signedMode_of_bandEigen
      ha m n hmLabel hnLabel hmEig.1 hnEig.1 hmEig.2 hnEig.2).symm
  have hcontA : ContinuousAt (fun a => normalizedSecondPairingL2 (bw a)
      (nuM (bw a)) (nuN (bw a)) (psiM (bw a)) (psiN (bw a))) a₀ := by
    simpa only [Function.comp_def, bw] using hcont.comp hbwt
  exact hcontA.congr_of_eventuallyEq heq

theorem eventually_signedModeRadialData_chi_strictAnti
    {m n : ℕ} (hmn : m < n) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      (signedModeRadialData a n).chi <
        (signedModeRadialData a m).chi := by
  let Km : ℝ := (((2 * m) * (2 * m + 1) : ℕ) : ℝ)
  let Kn : ℝ := (((2 * n) * (2 * n + 1) : ℕ) : ℝ)
  have hK : Km < Kn := by
    dsimp only [Km, Kn]
    push_cast
    have hmnR : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hm := tendsto_signedModeRadialData_chi_smallAperture m
  have hn := tendsto_signedModeRadialData_chi_smallAperture n
  change Tendsto (fun a : ℝ => (signedModeRadialData a m).chi)
      (𝓝[>] (0 : ℝ)) (nhds (-Km)) at hm
  change Tendsto (fun a : ℝ => (signedModeRadialData a n).chi)
      (𝓝[>] (0 : ℝ)) (nhds (-Kn)) at hn
  have hmid : -Kn < (-Kn + -Km) / 2 ∧
      (-Kn + -Km) / 2 < -Km := by
    constructor <;> linarith
  filter_upwards [hn.eventually_lt_const hmid.1,
    hm.eventually_const_lt hmid.2] with a hna ham
  exact lt_trans hna ham

theorem eventually_signedModeRadialData_s_strictMono
    {m n : ℕ} (hmn : m < n) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      (signedModeRadialData a m).s <
        (signedModeRadialData a n).s := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_signedModeRadialData_chi_strictAnti hmn]
      with a ha hchi
  have haPos : 0 < a := ha
  have hmExact := signedModeRadialData_isExact_of_pos haPos m
  have hnExact := signedModeRadialData_isExact_of_pos haPos n
  have hmS := hmExact.2.2.2.2.2.2.2.2.2.2.1
  have hnS := hnExact.2.2.2.2.2.2.2.2.2.2.1
  rw [hmS, hnS, radialSeparationRatio]
  have hcSq : 0 < signedModeRadialBandwidth a ^ 2 := by
    dsimp only [signedModeRadialBandwidth]
    positivity
  exact (div_lt_div_iff_of_pos_right hcSq).2 (by linarith)

theorem eventually_signedModeRadialData_secondDerivPairing_pos
    {m n : ℕ} (hmn : m < n) :
    ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
      0 < ∫ x in (-1 : ℝ)..1,
        deriv (deriv (signedModeRadialData a m).R) x *
          (signedModeRadialData a n).R x := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_signedModeRadialData_s_strictMono hmn]
      with a ha hs
  exact (signedModeRadialData_secondDerivPairing_pos_iff_s_lt ha hmn).2 hs

/-- Global positivity of the canonical cross-derivative pairing.  Small aperture fixes its
orientation; local indexed-branch stability makes it continuous; spectral simplicity forbids a
zero, so the sign cannot change on the positive aperture axis. -/
theorem signedModeRadialData_secondDerivPairing_pos
    {a : ℝ} (ha : 0 < a) {m n : ℕ} (hmn : m < n) :
    0 < ∫ x in (-1 : ℝ)..1,
      deriv (deriv (signedModeRadialData a m).R) x *
        (signedModeRadialData a n).R x := by
  let pair : ℝ → ℝ := fun b =>
    ∫ x in (-1 : ℝ)..1,
      deriv (deriv (signedModeRadialData b m).R) x *
        (signedModeRadialData b n).R x
  have hlt : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), b < a :=
    (eventually_lt_nhds ha).filter_mono
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have hanchor : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < pair b := by
    simpa only [pair] using eventually_signedModeRadialData_secondDerivPairing_pos hmn
  have hex : ∃ b : ℝ, 0 < b ∧ b < a ∧ 0 < pair b := by
    have hev : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < b ∧ b < a ∧ 0 < pair b := by
      filter_upwards [self_mem_nhdsWithin, hlt, hanchor]
        with b hb hba hpair
      exact ⟨hb, hba, hpair⟩
    exact hev.exists
  obtain ⟨b, hb, hba, hpair⟩ := hex
  have hcont : ContinuousOn pair (Icc b a) := by
    intro x hx
    have hxPos : 0 < x := lt_of_lt_of_le hb hx.1
    exact (continuousAt_signedModeRadialData_secondDerivPairing hxPos m n).continuousWithinAt
  have hne : ∀ x ∈ Icc b a, pair x ≠ 0 := by
    intro x hx
    have hxPos : 0 < x := lt_of_lt_of_le hb hx.1
    exact signedModeRadialData_secondDerivPairing_ne_zero hxPos hmn.ne
  rcases HTGeometry.sign_const_of_continuousOn_ne_zero hba.le hcont hne with hpos | hneg
  · exact hpos a ⟨hba.le, le_rfl⟩
  · exact False.elim ((not_lt_of_ge hpair.le) (hneg b ⟨le_rfl, hba.le⟩))

/-- Canonical even prolate separation values are globally strictly ordered by the indexed mode. -/
theorem signedModeRadialData_s_strictMono
    {a : ℝ} (ha : 0 < a) : StrictMono fun n : ℕ => (signedModeRadialData a n).s := by
  intro m n hmn
  exact (signedModeRadialData_secondDerivPairing_pos_iff_s_lt ha hmn).1
    (signedModeRadialData_secondDerivPairing_pos ha hmn)

/-- Equivalent global strict ordering of the canonical angular separation constants. -/
theorem signedModeRadialData_chi_strictAnti
    {a : ℝ} (ha : 0 < a) : StrictAnti fun n : ℕ => (signedModeRadialData a n).chi := by
  intro m n hmn
  have hs := signedModeRadialData_s_strictMono ha hmn
  change (signedModeRadialData a m).s < (signedModeRadialData a n).s at hs
  change (signedModeRadialData a n).chi < (signedModeRadialData a m).chi
  have hmS := (signedModeRadialData_isExact_of_pos ha m).2.2.2.2.2.2.2.2.2.2.1
  have hnS := (signedModeRadialData_isExact_of_pos ha n).2.2.2.2.2.2.2.2.2.2.1
  rw [hmS, hnS] at hs
  simp only [radialSeparationRatio] at hs
  have hcSq : 0 < signedModeRadialBandwidth a ^ 2 := by
    dsimp only [signedModeRadialBandwidth]
    positivity
  have hdiv : (signedModeRadialData a n).chi / signedModeRadialBandwidth a ^ 2 <
      (signedModeRadialData a m).chi / signedModeRadialBandwidth a ^ 2 := by
    calc
      _ = -(-(signedModeRadialData a n).chi / signedModeRadialBandwidth a ^ 2) := by ring
      _ < -(-(signedModeRadialData a m).chi / signedModeRadialBandwidth a ^ 2) := neg_lt_neg hs
      _ = _ := by ring
  exact (div_lt_div_iff_of_pos_right hcSq).1 hdiv

end GaloisForLFunctions.RHTower
