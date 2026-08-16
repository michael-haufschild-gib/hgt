import GaloisForLFunctions.RHTower.XiShiftedHardEdgeRepeatedRootSuzukiAdmission
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeOddPrimeWallEndpointInvisibility
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge

/-!
# Repeated Route-U root jets cannot be born at a prime wall

Repeated symmetric roots produce a parity-doubled family of divided jets.  The compact recursive
division theorem admits every odd jet to Suzuki's logarithmic form domain at the original aperture.
This file identifies each admitted complex Fourier vector with its literal real squared-variable
hard-edge profile and applies bilinear endpoint orthogonality.

The result is stronger than diagonal wall invisibility: every mixed prime-wall response between
two depths of the repeated-root flag is zero.  Hence the entire odd Gram matrix of the admitted
flag is unchanged when the prime atom enters.  A repeated-root odd kernel cannot be newly created
by that wall; any such kernel was already present in the incoming chamber.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

/-- An `L¹ ∩ L²` complex source whose classical Fourier transform is real has an exact real `L²`
Fourier profile. -/
theorem exists_memLp_realProfile_fourierUnitary_eq_ofRealLp
    {q : ℝ → ℂ} (hq1 : Integrable q)
    (hq2 : MemLp q 2 (volume : Measure ℝ))
    {g : ℝ → ℝ} (hfourier : ∀ ξ : ℝ, 𝓕 q ξ = (g ξ : ℂ)) :
    ∃ hg : MemLp g 2 (volume : Measure ℝ),
      fourierUnitary (hq2.toLp q) =
        GaloisForLFunctions.HTGeometry.ofRealLp (hg.toLp g) := by
  let u : SoninL2 := hq2.toLp q
  have hucoe : (u : ℝ → ℂ) =ᵐ[volume] q := by
    simpa [u] using hq2.coeFn_toLp
  have hu1 : Integrable (u : ℝ → ℂ) := hq1.congr hucoe.symm
  have hunitary := l2_fourier_coeFn_eq_l1_fourier_of_integrable u hu1
  have hu1lp : MemLp (u : ℝ → ℂ) 1 (volume : Measure ℝ) :=
    memLp_one_iff_integrable.mpr hu1
  rw [Real.fourierTransform_toLp hu1lp] at hunitary
  have hunitary' : ((fourierUnitary u : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      𝓕 (u : ℝ → ℂ) := by
    have hFU : fourierUnitary u = 𝓕 u := rfl
    rw [hFU]
    exact hunitary
  have hfourier_congr : ∀ ξ : ℝ, 𝓕 (u : ℝ → ℂ) ξ = 𝓕 q ξ :=
    Real.fourier_congr_ae hucoe
  have hprofile : ((fourierUnitary u : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (g ξ : ℂ) := by
    filter_upwards [hunitary'] with ξ hξ
    rw [hξ, hfourier_congr ξ, hfourier ξ]
  have hcomplex : MemLp (fun ξ : ℝ => (g ξ : ℂ)) 2 (volume : Measure ℝ) :=
    (MeasureTheory.memLp_congr_ae hprofile).mp (Lp.memLp (fourierUnitary u))
  have hg : MemLp g 2 (volume : Measure ℝ) := by
    simpa using hcomplex.re
  refine ⟨hg, ?_⟩
  rw [GaloisForLFunctions.HTGeometry.ofRealLp_toLp hg]
  apply Lp.ext
  exact hprofile.trans
    (GaloisForLFunctions.HTGeometry.memLp_ofReal hg).coeFn_toLp.symm

/-- Normalized real squared-variable profile of the odd jet remaining after `k+1` divisions of a
root pair of multiplicity `m`. -/
def routeURepeatedRootOddSquaredProfile
    (c : ℝ) (m k : ℕ) (K : ℝ → ℝ) (u : ℝ) : ℝ :=
  (-2 * Real.pi) *
    ((((-2 * Real.pi) ^ 2 * u - c ^ 2) ^ (m - (k + 1))) *
      K ((-2 * Real.pi) ^ 2 * u))

theorem routeURepeatedRootOddSquaredProfile_identity
    (c : ℝ) (m k : ℕ) (K : ℝ → ℝ) (x : ℝ) :
    ((-2 * Real.pi * x : ℝ) : ℂ) *
        ((((-2 * Real.pi * x) ^ 2 - c ^ 2 : ℝ) : ℂ) ^ (m - (k + 1))) *
          (K ((-2 * Real.pi * x) ^ 2) : ℂ) =
      ((x * routeURepeatedRootOddSquaredProfile c m k K (x ^ 2) : ℝ) : ℂ) := by
  rw [routeURepeatedRootOddSquaredProfile]
  push_cast
  rw [show (-2 * Real.pi * x) ^ 2 = (-2 * Real.pi) ^ 2 * x ^ 2 by ring]
  ring

/-- Every repeated-root odd jet has a literal real `L²` squared-variable profile and an exact
Suzuki admission at unchanged aperture. -/
theorem exists_routeURepeatedRootOddSquaredProfile_suzukiAdmission
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {K : ℝ → ℝ} (hK : Continuous K)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * (K (w ^ 2) : ℂ))
    {k : ℕ} (hk : k < m) :
    ∃ (hg : MemLp (fun x : ℝ =>
          x * routeURepeatedRootOddSquaredProfile c m k K (x ^ 2)) 2
        (volume : Measure ℝ))
      (v : SuzukiHlogFormDomain a),
      suzukiHlogWeightedToL2 v.1 =
        GaloisForLFunctions.HTGeometry.ofRealLp
          (hg.toLp (fun x : ℝ =>
            x * routeURepeatedRootOddSquaredProfile c m k K (x ^ 2))) := by
  let G : ℝ → ℂ := fun w => (K (w ^ 2) : ℂ)
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have hfactorG : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * G w := by
    simpa [G] using hfactor
  have hadmission := exists_routeURealRepeatedRootOddSuzukiAdmission
    a hh hsupp hc0 m hG hfactorG hk
  dsimp only at hadmission
  obtain ⟨hodd2, v, hweighted, hoddFourier⟩ := hadmission
  obtain ⟨hq1, hqsupp, _⟩ := routeURealRepeatedRootDividedTime_invariants
    a hh hsupp hc0 m hG hfactorG k (Nat.le_of_lt hk)
  obtain ⟨hqc, hqnegc⟩ := routeURealRepeatedRootDividedTime_zero_at_roots
    a hh hsupp hc0 m hG hfactorG hk
  have hbd : -a.1 ≤ a.1 := by linarith [a.2]
  let odd := routeURealOddRootDividedTime (-a.1) c
    (routeURealRepeatedRootDividedTime (-a.1) c h k)
  have hodd1 : Integrable odd :=
    integrable_routeURealOddRootDividedTime
      hbd hq1 hqsupp hqc hqnegc hc0
  have hclassical : ∀ ξ : ℝ, 𝓕 odd ξ =
      ((ξ * routeURepeatedRootOddSquaredProfile c m k K (ξ ^ 2) : ℝ) : ℂ) := by
    intro ξ
    rw [← routeURealFourier_neg_two_pi_eq_fourier]
    rw [hoddFourier]
    dsimp [G]
    exact routeURepeatedRootOddSquaredProfile_identity c m k K ξ
  obtain ⟨hg, hfourier⟩ :=
    exists_memLp_realProfile_fourierUnitary_eq_ofRealLp hodd1 hodd2 hclassical
  exact ⟨hg, v, hweighted.trans hfourier⟩

/-- Every diagonal prime response of the repeated-root odd flag vanishes at the critical wall. -/
theorem routeURepeatedRootPrimeJumpOddResponse_eq_zero
    {n : ℕ} (hn : 2 ≤ n) (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {K : ℝ → ℝ} (hK : Continuous K)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * (K (w ^ 2) : ℂ))
    {k : ℕ} (hk : k < m) :
    routeUHardEdgePrimeJumpOddResponse n
      (routeURepeatedRootOddSquaredProfile c m k K)
      (routeURepeatedRootOddSquaredProfile c m k K) = 0 := by
  obtain ⟨hg, v, hv⟩ :=
    exists_routeURepeatedRootOddSquaredProfile_suzukiAdmission
      a hh hsupp hc0 m hK hfactor hk
  exact routeUHardEdgePrimeJumpOddResponse_eq_zero_of_suzukiHlogAdmission
    hn hg a ha v hv

/-- **Repeated-root prime-wall Gram obstruction.**  Every mixed response between any two depths
of the admitted odd jet flag is zero. -/
theorem routeURepeatedRootMixedPrimeJumpOddResponse_eq_zero
    {n : ℕ} (hn : 2 ≤ n) (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {K : ℝ → ℝ} (hK : Continuous K)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * (K (w ^ 2) : ℂ))
    {k l : ℕ} (hk : k < m) (hl : l < m) :
    routeUHardEdgePrimeJumpOddResponse n
      (routeURepeatedRootOddSquaredProfile c m k K)
      (routeURepeatedRootOddSquaredProfile c m l K) = 0 := by
  obtain ⟨hg, vg, hvg⟩ :=
    exists_routeURepeatedRootOddSquaredProfile_suzukiAdmission
      a hh hsupp hc0 m hK hfactor hk
  obtain ⟨hf, vf, hvf⟩ :=
    exists_routeURepeatedRootOddSquaredProfile_suzukiAdmission
      a hh hsupp hc0 m hK hfactor hl
  exact routeUHardEdgePrimeJumpOddResponse_eq_zero_of_two_suzukiHlogAdmissions
    hn hg hf a ha vg vf hvg hvf

/-- The complete odd Gram matrix of the repeated-root flag is unchanged across the prime wall. -/
theorem routeURepeatedRootOddForm_wall_eq_incoming
    {n : ℕ} (hn : 2 ≤ n) (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {K : ℝ → ℝ} (hK : Continuous K)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * (K (w ^ 2) : ℂ))
    {k l : ℕ} (hk : k < m) (hl : l < m)
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (routeURepeatedRootOddSquaredProfile c m k K u *
        routeURepeatedRootOddSquaredProfile c m l K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (routeURepeatedRootOddSquaredProfile c m k K u *
        routeURepeatedRootOddSquaredProfile c m l K u) *
        routeUHardEdgePrimeJumpDensity n (Real.sqrt u) / Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeOddForm (Real.log n / 2)
        (routeURepeatedRootOddSquaredProfile c m k K)
        (routeURepeatedRootOddSquaredProfile c m l K) =
      routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n)
        (routeURepeatedRootOddSquaredProfile c m k K)
        (routeURepeatedRootOddSquaredProfile c m l K) := by
  rw [routeUHardEdgeOddForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    hn _ _ hbase hjump,
    routeURepeatedRootMixedPrimeJumpOddResponse_eq_zero
      hn a ha hh hsupp hc0 m hK hfactor hk hl,
    sub_zero]

/-- A strictly positive incoming odd jet cannot become a wall-null jet.  Thus no admitted
repeated-root odd direction is newly born at a prime wall. -/
theorem routeURepeatedRootOddJet_not_new_wall_kernel
    {n : ℕ} (hn : 2 ≤ n) (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc0 : c ≠ 0) (m : ℕ) {K : ℝ → ℝ} (hK : Continuous K)
    (hfactor : ∀ w : ℝ, routeURealFourier h w =
      (((w ^ 2 - c ^ 2 : ℝ) : ℂ) ^ m) * (K (w ^ 2) : ℂ))
    {k : ℕ} (hk : k < m)
    (hbase : IntegrableOn (fun u : ℝ =>
      u * (routeURepeatedRootOddSquaredProfile c m k K u *
        routeURepeatedRootOddSquaredProfile c m k K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      u * (routeURepeatedRootOddSquaredProfile c m k K u *
        routeURepeatedRootOddSquaredProfile c m k K u) *
        routeUHardEdgePrimeJumpDensity n (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hincoming : 0 < routeUHardEdgeOddForm (routeUHardEdgeIncomingAperture n)
      (routeURepeatedRootOddSquaredProfile c m k K)
      (routeURepeatedRootOddSquaredProfile c m k K)) :
    routeUHardEdgeOddForm (Real.log n / 2)
        (routeURepeatedRootOddSquaredProfile c m k K)
        (routeURepeatedRootOddSquaredProfile c m k K) ≠ 0 := by
  rw [routeURepeatedRootOddForm_wall_eq_incoming
    hn a ha hh hsupp hc0 m hK hfactor hk hk hbase hjump]
  exact ne_of_gt hincoming

end RHTower
