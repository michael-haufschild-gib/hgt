import GaloisForLFunctions.HTGeometry.ComplexLaplacianGreenIdentity
import GaloisForLFunctions.HTGeometry.AnalyticBallFinsetFactorization
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount
import GaloisForLFunctions.HTGeometry.PoissonKernelBound
import GaloisForLFunctions.Bottcher.Q62BrolinDominated

/-!
# Poincaré–Lelong for entire functions on the complex plane

Local finite zero factorization, the planar logarithmic fundamental solution, and compactly
supported Green self-adjointness give the literal distributional identity

` ∫ log ‖f‖ · Δφ = 2π ∑ₐ ordₐ(f) φ(a) `

for every nonzero entire function and every real `C²` compactly supported test.  The right side is
the canonical zero-multiplicity `finsum`; it is not a finite-multiset surrogate.
-/

open MeasureTheory Complex Metric Filter Set Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A locally harmonic function times the Laplacian of a compactly supported test is integrable
when the test support lies inside the harmonicity ball. -/
theorem integrable_harmonic_mul_laplacian
    (u phi : ℂ → ℝ) {rin R : ℝ} (hrinR : rin < R)
    (hu : HarmonicOnNhd u (ball 0 R))
    (hphi : ContDiff ℝ 2 phi) (hphic : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ ball 0 rin) :
    Integrable (fun x => u x * Δ phi x) := by
  have hlapcont : Continuous (Δ phi) :=
    Bottcher.continuous_laplacian_of_contDiff hphi
  have hcont : Continuous (fun x => u x * Δ phi x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ ball (0 : ℂ) R
    · exact (hu x hx).1.continuousAt.mul hlapcont.continuousAt
    · have hxt : x ∉ tsupport phi := by
        intro hmem
        exact hx (ball_subset_ball hrinR.le (hsupp hmem))
      have hnh : (tsupport phi)ᶜ ∈ nhds x :=
        (isClosed_tsupport phi).isOpen_compl.mem_nhds hxt
      have heq : (fun y => u y * Δ phi y) =ᶠ[nhds x] (0 : ℂ → ℝ) := by
        filter_upwards [hnh] with y hy
        have hyphi : phi =ᶠ[nhds y] (0 : ℂ → ℝ) := by
          have hynh : (tsupport phi)ᶜ ∈ nhds y :=
            (isClosed_tsupport phi).isOpen_compl.mem_nhds hy
          filter_upwards [hynh] with w hw
          by_contra hne
          exact hw (subset_tsupport phi hne)
        have hlapy : Δ phi y = 0 := by
          rw [(laplacian_congr_nhds hyphi).eq_of_nhds,
            laplacian_eq_iteratedFDeriv_complexPlane]
          simp
        simp [hlapy]
      exact continuousAt_const.congr_of_eventuallyEq heq
  exact hcont.integrable_of_hasCompactSupport
    (Bottcher.hasCompactSupport_laplacian hphic).mul_left

/-- Poincaré–Lelong for an explicit finite zero factorization on a ball containing the test
support. -/
theorem poincareLelong_of_factorization
    (f g : ℂ → ℂ) (phi : ℂ → ℝ) (Z : Finset ℂ) (m : ℂ → ℕ)
    {rin rout R : ℝ}
    (hrin : 0 < rin) (hrout : rin < rout) (hR : rout < R)
    (hgan : AnalyticOnNhd ℂ g (ball 0 R))
    (hgne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (heq : Set.EqOn f (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball 0 R))
    (hphi : ContDiff ℝ 2 phi) (hphic : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ ball 0 rin) :
    (∫ z, Real.log ‖f z‖ * Δ phi z) =
      2 * Real.pi * ∑ ρ ∈ Z, (m ρ : ℝ) * phi ρ := by
  let M : Multiset ℂ := _root_.HTGeometry.multisetOfFinsetMultiplicities Z m
  let rootPot : ℂ → ℝ := fun z =>
    (M.map (fun ρ => Real.log ‖z - ρ‖)).sum
  let unitPot : ℂ → ℝ := fun z => Real.log ‖g z‖
  have hZae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ (Z : Set ℂ) := by
    have hmem : {z : ℂ | z ∉ (Z : Set ℂ)} ∈ MeasureTheory.ae volume := by
      rw [mem_ae_iff]
      have hset : {z : ℂ | z ∉ (Z : Set ℂ)}ᶜ = (Z : Set ℂ) := by
        ext z
        simp
      rw [hset]
      exact Z.countable_toSet.measure_zero (volume : Measure ℂ)
    exact hmem
  have hpoint : ∀ᵐ z ∂(volume : Measure ℂ),
      Real.log ‖f z‖ * Δ phi z =
        rootPot z * Δ phi z + unitPot z * Δ phi z := by
    filter_upwards [hZae] with z hzZ
    by_cases hzt : z ∈ tsupport phi
    · have hzR : z ∈ ball (0 : ℂ) R :=
        ball_subset_ball (by linarith : rin < R).le (hsupp hzt)
      have hzM : z ∉ M := by
        intro hzmem
        exact hzZ (_root_.HTGeometry.mem_multisetOfFinsetMultiplicities hzmem)
      have hprod : _root_.HTGeometry.multisetLinearProd M z ≠ 0 := by
        exact (not_congr
          (_root_.HTGeometry.multisetLinearProd_eq_zero_iff M z)).mpr hzM
      have hgz : g z ≠ 0 := hgne z hzR
      have hMprod : _root_.HTGeometry.multisetLinearProd M z =
          ∏ ρ ∈ Z, (z - ρ) ^ m ρ := by
        simpa [M] using
          (_root_.HTGeometry.multisetLinearProd_multisetOfFinsetMultiplicities Z m z)
      have hlog : Real.log ‖f z‖ = rootPot z + unitPot z := by
        calc
          Real.log ‖f z‖ = Real.log ‖(∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z‖ := by
            rw [heq hzR]
          _ = Real.log ‖∏ ρ ∈ Z, (z - ρ) ^ m ρ‖ + Real.log ‖g z‖ := by
            rw [norm_mul, Real.log_mul
              (norm_ne_zero_iff.mpr (hMprod ▸ hprod))
              (norm_ne_zero_iff.mpr hgz)]
          _ = rootPot z + unitPot z := by
            rw [← hMprod, ← rootLogSum_eq_log_norm_multisetLinearProd M hzM]
      rw [hlog, add_mul]
    · have hnh : (tsupport phi)ᶜ ∈ nhds z :=
        (isClosed_tsupport phi).isOpen_compl.mem_nhds hzt
      have heqzero : phi =ᶠ[nhds z] (0 : ℂ → ℝ) := by
        filter_upwards [hnh] with w hw
        by_contra hne
        exact hw (subset_tsupport phi (by simpa using hne))
      have hlap : Δ phi z = 0 := by
        rw [(laplacian_congr_nhds heqzero).eq_of_nhds,
          laplacian_eq_iteratedFDeriv_complexPlane]
        simp
      simp [hlap]
  have hroot : Integrable (fun z => rootPot z * Δ phi z) :=
    Bottcher.integrable_rootLogSum_mul_laplacian M phi hphi hphic
  have hunitH : HarmonicOnNhd unitPot (ball (0 : ℂ) R) :=
    harmonicOnNhd_log_norm hgan hgne
  have hunit : Integrable (fun z => unitPot z * Δ phi z) :=
    integrable_harmonic_mul_laplacian unitPot phi
      (by linarith : rin < R) hunitH hphi hphic hsupp
  calc
    (∫ z, Real.log ‖f z‖ * Δ phi z) =
        ∫ z, rootPot z * Δ phi z + unitPot z * Δ phi z := integral_congr_ae hpoint
    _ = (∫ z, rootPot z * Δ phi z) +
        ∫ z, unitPot z * Δ phi z := integral_add hroot hunit
    _ = 2 * Real.pi * (M.map phi).sum := by
      rw [Bottcher.integral_rootLogSum_mul_laplacian M phi hphi hphic,
        integral_harmonic_mul_laplacian_eq_zero
          unitPot phi hrin hrout hR hunitH hphi hphic hsupp,
        add_zero]
    _ = 2 * Real.pi * ∑ ρ ∈ Z, (m ρ : ℝ) * phi ρ := by
      rw [sum_map_multisetOfFinsetMultiplicities]

/-- Real-valued pairing with the canonical zero divisor. -/
noncomputable def realDivisorPairing (f : ℂ → ℂ) (phi : ℂ → ℝ) : ℝ :=
  ∑ᶠ a : ℂ, (zeroMult f a : ℝ) * phi a

/-- The real divisor pairing is a finite sum over any finite set containing every multiplicity
visible to the test. -/
theorem realDivisorPairing_eq_sum {f : ℂ → ℂ} {phi : ℂ → ℝ} {s : Finset ℂ}
    (hs : ∀ a : ℂ, zeroMult f a ≠ 0 → phi a ≠ 0 → a ∈ s) :
    realDivisorPairing f phi = ∑ a ∈ s, (zeroMult f a : ℝ) * phi a := by
  refine finsum_eq_finsetSum_of_support_subset _ ?_
  intro a ha
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at ha
  have hmult : zeroMult f a ≠ 0 := by
    intro hzero
    exact ha.1 (by simp [hzero])
  exact hs a hmult ha.2

/-- Factorized Poincaré–Lelong, expressed using the canonical multiplicity function rather than
the chosen factorization. -/
theorem poincareLelong_of_factorization_canonical
    (f g : ℂ → ℂ) (phi : ℂ → ℝ) (Z : Finset ℂ) (m : ℂ → ℕ)
    {rin rout R : ℝ}
    (hrin : 0 < rin) (hrout : rin < rout) (hR : rout < R)
    (hZball : ∀ ρ ∈ Z, ρ ∈ ball (0 : ℂ) R)
    (hgan : AnalyticOnNhd ℂ g (ball 0 R))
    (hgne : ∀ z ∈ ball (0 : ℂ) R, g z ≠ 0)
    (heq : Set.EqOn f (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball 0 R))
    (hphi : ContDiff ℝ 2 phi) (hphic : HasCompactSupport phi)
    (hsupp : tsupport phi ⊆ ball 0 rin) :
    (∫ z, Real.log ‖f z‖ * Δ phi z) =
      2 * Real.pi * realDivisorPairing f phi := by
  have hpair : realDivisorPairing f phi = ∑ ρ ∈ Z, (m ρ : ℝ) * phi ρ := by
    rw [realDivisorPairing_eq_sum (s := Z) (fun a hmult hphinz => by
      have hat : a ∈ tsupport phi := subset_tsupport phi hphinz
      have haR : a ∈ ball (0 : ℂ) R :=
        ball_subset_ball (by linarith : rin < R).le (hsupp hat)
      by_contra haZ
      rw [zeroMult_of_factorization isOpen_ball Z m
        hgan.differentiableOn hgne heq haR, if_neg haZ] at hmult
      exact hmult rfl)]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [zeroMult_of_factorization isOpen_ball Z m
      hgan.differentiableOn hgne heq (hZball a ha), if_pos ha]
  rw [poincareLelong_of_factorization f g phi Z m hrin hrout hR
    hgan hgne heq hphi hphic hsupp, hpair]

/-- Distributional Poincaré–Lelong identity against real `C²` compactly supported tests. -/
def IsPoincareLelongOfSmooth (f : ℂ → ℂ) : Prop :=
  ∀ phi : ℂ → ℝ, ContDiff ℝ 2 phi → HasCompactSupport phi →
    (∫ z, Real.log ‖f z‖ * Δ phi z) =
      2 * Real.pi * realDivisorPairing f phi

/-- Every nonzero entire function satisfies the distributional Poincaré–Lelong identity. -/
theorem entire_isPoincareLelongOfSmooth {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, AnalyticAt ℂ f z) {z₀ : ℂ} (hfz₀ : f z₀ ≠ 0) :
    IsPoincareLelongOfSmooth f := by
  intro phi hphi hphic
  obtain ⟨rin, hrin, hsuppNorm⟩ := hphic.isCompact.isBounded.exists_pos_norm_lt
  have hsupp : tsupport phi ⊆ ball (0 : ℂ) rin := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    exact hsuppNorm z hz
  let rout : ℝ := rin + 1
  let R : ℝ := max (rin + 2) (‖z₀‖ + 1)
  have hrout : rin < rout := by simp [rout]
  have hR : rout < R := by
    dsimp [rout, R]
    have hle : rin + 2 ≤ max (rin + 2) (‖z₀‖ + 1) := le_max_left _ _
    linarith
  have hz₀R : z₀ ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    have hle : ‖z₀‖ + 1 ≤ max (rin + 2) (‖z₀‖ + 1) := le_max_right _ _
    linarith
  have hfball : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) := fun z _ => hf z
  obtain ⟨Z, m, g, hZball, _hZpos, _hZzero, hgan, hgne, heq⟩ :=
    _root_.HTGeometry.exists_finset_zeroFree_factorization hfball hz₀R hfz₀
  exact poincareLelong_of_factorization_canonical f g phi Z m hrin hrout hR
    hZball hgan hgne heq hphi hphic hsupp

end

end GaloisForLFunctions.HTGeometry
