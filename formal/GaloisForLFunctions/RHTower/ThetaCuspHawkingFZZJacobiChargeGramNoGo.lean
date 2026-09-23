import GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZJostDelayIncidenceNoGo
import GaloisForLFunctions.RHTower.ThetaCuspHawkingStimulatedCubicUnmaskingEndpoint
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity

/-!
# FZZ Jacobi charge Gram: full diagonal scattering cannot realize selective Xi stimulation

`[LITERATURE]` The supersymmetric cigar elliptic genus is a torus trace with Gaussian
momentum--winding weights; see Ashok--Troost, arXiv:1101.1059, equations (3.4), (4.2), and
(4.8)--(4.10).  The last equations derive the continuum density mismatch from exact bosonic and
fermionic reflection amplitudes.  `FZZCigarScatteringSpectralAsymmetry` and
`ThetaCuspHawkingFZZJostDelayIncidenceNoGo` already prove the corresponding charge Jost factors,
their all-pass real-axis optical law, and the positive delay

`exp (-(n + 1) t)`.

This file tests the next source-faithful completion: apply a positive Jacobi heat weight to every
protected charge channel.  It uses the one-dimensional positive-charge heat slice

`w_tau(n) = exp (-pi tau (n + 1)^(2 : ℕ))`

and does not claim that this slice alone is the full noncompact elliptic genus.  Every finite
charge truncation obeys two exact laws.

* Its collective real-axis optical energy equals its Jacobi partition weight because each exact
  FZZ Jost channel is all-pass.
* Its two-shell delay is a Euclidean feature Gram.  Consequently every three-shell determinant
  is nonnegative, with no KMS, CCR, passivity, or RH assumption.

`[PROVED NO-GO]` An off-critical Xi orbit makes the selectively stimulated Hawking kernel
eventually have negative three-shell determinant.  Therefore that kernel cannot equal any
positive diagonal Jacobi-weighted FZZ charge truncation at sufficiently large rapidity.  A full
FZZ/RH producer must derive coefficient-faithful off-diagonal momentum--winding interference (or
another genuinely non-diagonal backreaction channel).  Diagonal charge passivity cannot supply
the negative-cubic exclusion, and an unweighted product of charge Jost ratios is not promoted to
a physical theta S-matrix here.
-/

open Complex Real Filter Topology Set
open scoped BigOperators Matrix

noncomputable section

namespace RHTower

/-- Positive Jacobi heat weight on the `n+1` protected FZZ charge. -/
def fzzCigarThetaHeatChargeWeight (tau : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(Real.pi * tau * ((n : ℝ) + 1) ^ (2 : ℕ)))

/-- Finite positive-charge Jacobi partition weight. -/
def fzzCigarThetaHeatChargePartition (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ n : Fin N, fzzCigarThetaHeatChargeWeight tau n

/-- Collective optical energy of the exact diagonal FZZ charge Jost channels. -/
def fzzCigarThetaHeatCollectiveOpticalEnergy
    (N : ℕ) (tau radialMomentum : ℝ) : ℝ :=
  ∑ n : Fin N, fzzCigarThetaHeatChargeWeight tau n *
    fzzCigarChargeJostOpticalEnergyShare
      (((n : ℕ) : ℝ) + 1) radialMomentum

/-- Exact finite Jacobi optical identity.  Gaussian charge weighting changes the ensemble but
not the unit optical share of any protected FZZ scattering channel. -/
theorem fzzCigarThetaHeatCollectiveOpticalEnergy_eq_partition
    (N : ℕ) (tau radialMomentum : ℝ) :
    fzzCigarThetaHeatCollectiveOpticalEnergy N tau radialMomentum =
      fzzCigarThetaHeatChargePartition N tau := by
  unfold fzzCigarThetaHeatCollectiveOpticalEnergy
    fzzCigarThetaHeatChargePartition
  apply Finset.sum_congr rfl
  intro n _
  rw [fzzCigarChargeJostOpticalEnergyShare_eq_one (by positivity)]
  ring

/-- Square-root heat-weighted delay feature of charge `n+1` on one exterior shell. -/
def fzzCigarThetaHeatChargeFeature (tau x : ℝ) (n : Fin N) : ℝ :=
  Real.exp
    (-(Real.pi * tau * (((n : ℕ) : ℝ) + 1) ^ (2 : ℕ)) / 2 -
      (((n : ℕ) : ℝ) + 1) * x)

/-- Diagonal charge sum of the physical FZZ continuum-delay reporters. -/
def fzzCigarThetaHeatChargeGram (N : ℕ) (tau x y : ℝ) : ℝ :=
  ∑ n : Fin N,
    fzzCigarThetaHeatChargeFeature tau x n *
      fzzCigarThetaHeatChargeFeature tau y n

/-- Each Gram summand is exactly Jacobi weight times the FZZ charge delay reconstructed from the
reflection spectral asymmetry. -/
theorem fzzCigarThetaHeatChargeFeature_mul_eq_weight_mul_delay
    (tau x y : ℝ) (n : Fin N) :
    fzzCigarThetaHeatChargeFeature tau x n *
        fzzCigarThetaHeatChargeFeature tau y n =
      fzzCigarThetaHeatChargeWeight tau n *
        HTGeometry.fzzCigarChargeDelay n (x + y) := by
  unfold fzzCigarThetaHeatChargeFeature fzzCigarThetaHeatChargeWeight
    HTGeometry.fzzCigarChargeDelay
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Exact discrete-charge plus radial-continuum delay identity for the finite Jacobi slice.  The
right side uses the delay whose radial-momentum Fourier representation is the positive FZZ
reflection deficit. -/
theorem fzzCigarThetaHeatChargeGram_eq_weightedDelay
    (N : ℕ) (tau x y : ℝ) :
    fzzCigarThetaHeatChargeGram N tau x y =
      ∑ n : Fin N, fzzCigarThetaHeatChargeWeight tau n *
        HTGeometry.fzzCigarChargeDelay n (x + y) := by
  unfold fzzCigarThetaHeatChargeGram
  apply Finset.sum_congr rfl
  intro n _
  exact fzzCigarThetaHeatChargeFeature_mul_eq_weight_mul_delay tau x y n

theorem fzzCigarThetaHeatChargeGram_comm (N : ℕ) (tau x y : ℝ) :
    fzzCigarThetaHeatChargeGram N tau x y =
      fzzCigarThetaHeatChargeGram N tau y x := by
  unfold fzzCigarThetaHeatChargeGram
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The three-shell response matrix is literally the finite Euclidean charge-feature Gram. -/
theorem fzzCigarThetaHeatChargeGram_eq_standardFeatureGram
    (N : ℕ) (tau : ℝ) (node : Fin 3 → ℝ) :
    GaloisForLFunctions.HilbertMetric.standardFeatureGram
        (fun (i : Fin 3) (n : Fin N) =>
          fzzCigarThetaHeatChargeFeature tau (node i) n) =
      fun i j => fzzCigarThetaHeatChargeGram N tau (node i) (node j) := by
  ext i j
  rfl

/-- Full-diagonal FZZ charge completion excludes the negative cubic chamber unconditionally.
This is a charge-feature Gram theorem, not a consequence of generic KMS or passivity. -/
theorem fzzCigarThetaHeatChargeGram_threePointDet_nonneg
    (N : ℕ) (tau x y z : ℝ) :
    0 ≤ symmetricThreePointDet
      (fzzCigarThetaHeatChargeGram N tau) x y z := by
  let node : Fin 3 → ℝ := ![x, y, z]
  let evaluation : Fin 3 → Fin N → ℝ :=
    fun i n => fzzCigarThetaHeatChargeFeature tau (node i) n
  have hdet :
      0 ≤ (GaloisForLFunctions.HilbertMetric.standardFeatureGram evaluation).det := by
    rw [GaloisForLFunctions.HilbertMetric.det_standardFeatureGram_eq_pluckerVolumeSq]
    unfold GaloisForLFunctions.HilbertMetric.standardFeaturePluckerVolumeSq
    positivity
  have heq :
      (GaloisForLFunctions.HilbertMetric.standardFeatureGram evaluation).det =
        symmetricThreePointDet
          (fzzCigarThetaHeatChargeGram N tau) x y z := by
    rw [fzzCigarThetaHeatChargeGram_eq_standardFeatureGram N tau node]
    simp [node, symmetricThreePointDet, Matrix.det_fin_three]
    rw [fzzCigarThetaHeatChargeGram_comm N tau y x,
      fzzCigarThetaHeatChargeGram_comm N tau z x,
      fzzCigarThetaHeatChargeGram_comm N tau z y]
    ring
  rwa [heq] at hdet

/-- Pointwise thermodynamic limits of diagonal FZZ charge truncations retain the nonnegative
three-shell determinant.  Thus an infinite charge limit cannot evade the finite Gram wall by
convergence alone. -/
theorem fzzCigarThetaHeatChargeGram_limit_threePointDet_nonneg
    (tau x y z : ℝ) (K : ℝ → ℝ → ℝ)
    (hlimit : ∀ u v : ℝ,
      Tendsto (fun N : ℕ => fzzCigarThetaHeatChargeGram N tau u v)
        atTop (𝓝 (K u v))) :
    0 ≤ symmetricThreePointDet K x y z := by
  have hxx := hlimit x x
  have hyy := hlimit y y
  have hzz := hlimit z z
  have hxy := hlimit x y
  have hxz := hlimit x z
  have hyz := hlimit y z
  have htwo : Tendsto (fun _N : ℕ => (2 : ℝ)) atTop (𝓝 2) :=
    tendsto_const_nhds
  have hdiag := (hxx.mul hyy).mul hzz
  have hcross := ((htwo.mul hxy).mul hxz).mul hyz
  have hnegYZ := (hxx.mul hyz).mul hyz
  have hnegXZ := (hyy.mul hxz).mul hxz
  have hnegXY := (hzz.mul hxy).mul hxy
  have hdet : Tendsto
      (fun N : ℕ => symmetricThreePointDet
        (fzzCigarThetaHeatChargeGram N tau) x y z)
      atTop (𝓝 (symmetricThreePointDet K x y z)) := by
    unfold symmetricThreePointDet
    have htotal := (((hdiag.add hcross).sub hnegYZ).sub hnegXZ).sub hnegXY
    convert htotal using 1
    · funext N
      ring
    · congr 1
      ring
  apply isClosed_Ici.mem_of_tendsto hdet
  exact Filter.Eventually.of_forall fun N =>
    fzzCigarThetaHeatChargeGram_threePointDet_nonneg N tau x y z

/-- **Diagonal FZZ completion no-go.**  For every off-critical Xi orbit and every ordered
positive shell triple, sufficiently strong genuine Hawking modular gain separates the selective
Xi kernel from every finite diagonal Jacobi-weighted FZZ charge Gram. -/
theorem exists_eventually_thetaCuspHawking_offCritical_ne_fzzCigarThetaHeatChargeGram
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (N : ℕ) (tau : ℝ) :
    ∃ R : ℝ, ∀ rapidity : ℝ, R ≤ rapidity →
      thetaCuspHawkingSelectiveModularGainKernel q rapidity ≠
        fzzCigarThetaHeatChargeGram N tau := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, ?_⟩
  intro rapidity hrapidity heq
  have hneg := hR rapidity hrapidity
  rw [heq] at hneg
  have hnonneg :=
    fzzCigarThetaHeatChargeGram_threePointDet_nonneg N tau x y z
  linarith

/-- **Full diagonal thermodynamic no-go.**  Any pointwise limit of the Jacobi-weighted diagonal
FZZ charge truncations remains separated from the off-critical selective Hawking kernel once
modular gain is large enough. -/
theorem exists_eventually_thetaCuspHawking_offCritical_ne_fzzCigarThetaHeatChargeGram_limit
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (tau : ℝ) (K : ℝ → ℝ → ℝ)
    (hlimit : ∀ u v : ℝ,
      Tendsto (fun N : ℕ => fzzCigarThetaHeatChargeGram N tau u v)
        atTop (𝓝 (K u v))) :
    ∃ R : ℝ, ∀ rapidity : ℝ, R ≤ rapidity →
      thetaCuspHawkingSelectiveModularGainKernel q rapidity ≠ K := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, ?_⟩
  intro rapidity hrapidity heq
  have hneg := hR rapidity hrapidity
  rw [heq] at hneg
  have hnonneg :=
    fzzCigarThetaHeatChargeGram_limit_threePointDet_nonneg
      tau x y z K hlimit
  linarith

end RHTower
