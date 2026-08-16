import GaloisForLFunctions.RHTower.XiShiftedHardEdgeOddPrimeWallEndpointInvisibility

/-!
# Route U: parity-complete endpoint invisibility at prime walls

The existing endpoint theorem closed the odd branch of a hard-edge prime wall.  The same Fourier
support mechanism is parity-blind.  For an even state `x ↦ H(x²)` of endpoint Paley--Wiener type,
the entering atom has frequency exactly twice the band edge, so the translated support intervals
meet only on a null endpoint.  Its full bilinear prime response therefore vanishes.

Consequently both even and odd restricted-Weil Gram forms are unchanged across every prime-power
wall on their admitted endpoint bands.  Prime atoms cannot create a first negative direction in
either parity sector; any Route-U first contact must be caused by continuous enlargement of the
admitted source space inside a fixed-density chamber.  This does not prove the required incoming
strictness or RH.
-/

noncomputable section

open MeasureTheory Set FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Even response of one newly entering von Mangoldt source atom. -/
def routeUHardEdgePrimeJumpEvenResponse (n : ℕ) (H K : ℝ → ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ),
    (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) / Real.sqrt u

theorem routeUHardEdgeEvenForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    {n : ℕ} (hn : 2 ≤ n) (H K : ℝ → ℝ)
    (hbase : IntegrableOn (fun u : ℝ =>
      (H u * K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0)) :
    routeUHardEdgeEvenForm (Real.log n / 2) H K =
      routeUHardEdgeEvenForm (routeUHardEdgeIncomingAperture n) H K -
        routeUHardEdgePrimeJumpEvenResponse n H K := by
  unfold routeUHardEdgeEvenForm routeUHardEdgePairing
  have hint :
      (∫ u in Ioi (0 : ℝ),
        (H u * K u) *
          routeUHardEdgeDensity (Real.log n / 2) (Real.sqrt u) / Real.sqrt u) =
      (∫ u in Ioi (0 : ℝ),
        (H u * K u) *
          routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
            Real.sqrt u) -
      ∫ u in Ioi (0 : ℝ),
        (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
          Real.sqrt u := by
    rw [← integral_sub hbase hjump]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [routeUHardEdgeDensity_log_nat_half_eq_incoming_sub_primeJump hn]
    ring
  rw [hint]
  unfold routeUHardEdgePrimeJumpEvenResponse
  ring

theorem routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_bandSupports
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => H (x ^ 2)) 2 volume)
    (hk : MemLp (fun x : ℝ => K (x ^ 2)) 2 volume)
    (hbandg : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => H (x ^ 2)))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0)
    (hbandk : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hk.toLp (fun x : ℝ => K (x ^ 2)))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    routeUHardEdgePrimeJumpEvenResponse n H K = 0 := by
  have hnreal : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnreal
  have hb : 0 ≤ Real.log (n : ℝ) / (4 * Real.pi) := by positivity
  have hendpoint :=
    MellinL2.integral_mul_mul_cos_four_pi_eq_zero_of_two_bandSupports
      hb hg hk hbandg hbandk
  have hscale : 4 * Real.pi * (Real.log (n : ℝ) / (4 * Real.pi)) =
      Real.log (n : ℝ) := by
    field_simp [Real.pi_ne_zero]
  have hendpoint' :
      (∫ x : ℝ, (H (x ^ 2) * K (x ^ 2)) * Real.cos (Real.log n * x)) = 0 := by
    simpa only [hscale] using hendpoint
  have hcos :
      (∫ x : ℝ, (H (x ^ 2) * K (x ^ 2)) * Real.cos (x * Real.log n)) = 0 := by
    rw [show (fun x : ℝ => (H (x ^ 2) * K (x ^ 2)) * Real.cos (x * Real.log n)) =
        fun x : ℝ => (H (x ^ 2) * K (x ^ 2)) * Real.cos (Real.log n * x) by
      funext x
      rw [mul_comm x (Real.log n)]]
    exact hendpoint'
  unfold routeUHardEdgePrimeJumpEvenResponse
  have hsub := integral_comp_sq_eq_integral_Ioi
    (fun u : ℝ => (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u))
  rw [← hsub]
  calc
    (∫ x : ℝ, (H (x ^ 2) * K (x ^ 2)) *
        routeUHardEdgePrimeJumpDensity n (Real.sqrt (x ^ 2))) =
      ∫ x : ℝ, ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ((H (x ^ 2) * K (x ^ 2)) * Real.cos (x * Real.log n)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [routeUHardEdgePrimeJumpDensity, Real.sqrt_sq_eq_abs]
          have hcosabs : Real.cos (|x| * Real.log n) =
              Real.cos (x * Real.log n) := by
            rcases abs_choice x with h | h
            · rw [h]
            · rw [h, neg_mul, Real.cos_neg]
          rw [hcosabs]
          ring
    _ = ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n) *
        ∫ x : ℝ, (H (x ^ 2) * K (x ^ 2)) * Real.cos (x * Real.log n) := by
          rw [integral_const_mul]
    _ = 0 := by rw [hcos, mul_zero]

/-- The diagonal even response vanishes at the endpoint frequency. -/
theorem routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_bandSupport
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => H (x ^ 2)) 2 volume)
    (hband : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => H (x ^ 2)))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0) :
    routeUHardEdgePrimeJumpEvenResponse n H H = 0 :=
  routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_bandSupports
    hn hg hg hband hband

/-- An endpoint-bandlimited even state cannot lose nonnegativity at a prime wall. -/
theorem routeUHardEdgeEvenForm_log_nat_half_nonneg_of_incoming_and_bandSupport
    {n : ℕ} (hn : 2 ≤ n) {H : ℝ → ℝ}
    (hbase : IntegrableOn (fun u : ℝ =>
      (H u * H u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      (H u * H u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hg : MemLp (fun x : ℝ => H (x ^ 2)) 2 volume)
    (hband : ∀ᵐ ξ : ℝ, Real.log n / (4 * Real.pi) < |ξ| →
      (𝓕 (ofRealLp (hg.toLp (fun x : ℝ => H (x ^ 2)))) :
        Lp ℂ 2 (volume : Measure ℝ)) ξ = 0)
    (hincoming : 0 ≤ routeUHardEdgeEvenForm
      (routeUHardEdgeIncomingAperture n) H H) :
    0 ≤ routeUHardEdgeEvenForm (Real.log n / 2) H H := by
  rw [routeUHardEdgeEvenForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    hn H H hbase hjump,
    routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_bandSupport hn hg hband,
    sub_zero]
  exact hincoming

theorem routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_suzukiHlogAdmissions
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hg : MemLp (fun x : ℝ => H (x ^ 2)) 2 volume)
    (hk : MemLp (fun x : ℝ => K (x ^ 2)) 2 volume)
    (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    (qH qK : SuzukiHlogFormDomain a)
    (hqH : suzukiHlogWeightedToL2 qH.1 =
      ofRealLp (hg.toLp (fun x : ℝ => H (x ^ 2))))
    (hqK : suzukiHlogWeightedToL2 qK.1 =
      ofRealLp (hk.toLp (fun x : ℝ => K (x ^ 2)))) :
    routeUHardEdgePrimeJumpEvenResponse n H K = 0 := by
  apply routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_bandSupports hn hg hk
  · have hs := suzukiHlogFormDomain_fourier_bandSupport a qH
    rw [hqH] at hs
    simpa only [ha] using hs
  · have hs := suzukiHlogFormDomain_fourier_bandSupport a qK
    rw [hqK] at hs
    simpa only [ha] using hs

theorem routeUHardEdgeEvenForm_log_nat_half_eq_incoming_of_two_suzukiHlogAdmissions
    {n : ℕ} (hn : 2 ≤ n) {H K : ℝ → ℝ}
    (hbase : IntegrableOn (fun u : ℝ =>
      (H u * K u) *
        routeUHardEdgeDensity (routeUHardEdgeIncomingAperture n) (Real.sqrt u) /
          Real.sqrt u) (Ioi 0))
    (hjump : IntegrableOn (fun u : ℝ =>
      (H u * K u) * routeUHardEdgePrimeJumpDensity n (Real.sqrt u) /
        Real.sqrt u) (Ioi 0))
    (hg : MemLp (fun x : ℝ => H (x ^ 2)) 2 volume)
    (hk : MemLp (fun x : ℝ => K (x ^ 2)) 2 volume)
    (a : SuzukiPositiveAperture)
    (ha : a.1 = Real.log n / (4 * Real.pi))
    (qH qK : SuzukiHlogFormDomain a)
    (hqH : suzukiHlogWeightedToL2 qH.1 =
      ofRealLp (hg.toLp (fun x : ℝ => H (x ^ 2))))
    (hqK : suzukiHlogWeightedToL2 qK.1 =
      ofRealLp (hk.toLp (fun x : ℝ => K (x ^ 2)))) :
    routeUHardEdgeEvenForm (Real.log n / 2) H K =
      routeUHardEdgeEvenForm (routeUHardEdgeIncomingAperture n) H K := by
  rw [routeUHardEdgeEvenForm_log_nat_half_eq_incoming_sub_primeJumpResponse
    hn H K hbase hjump,
    routeUHardEdgePrimeJumpEvenResponse_eq_zero_of_two_suzukiHlogAdmissions
      hn hg hk a ha qH qK hqH hqK,
    sub_zero]

end RHTower
