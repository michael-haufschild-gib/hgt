import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyFloor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# P-G105R: balanced physical determinant square-jet retention

The balanced two-channel physical determinant factors through the square
coordinate `v = u^(2 : ℕ)`. For every finite prime block, its punctured quadratic
quotient tends exactly to minus sixty-four times child Hilbert--Schmidt energy.

Square blocks exhaust the full child kernel, so these finite determinant jets
converge to `-64 E(d)`. P-G105Q then forces the cofinal square jet eventually
below `-256/11025` at the aperture wall and forces all sufficiently large
literal finite blocks below `-128/11025`.

This is determinant-level wall noncollapse. It does not identify the cofinal
physical determinant with Xi.
-/

open Complex Filter Topology Set
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

theorem hasDerivAt_complexDet_one_add_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) :
    HasDerivAt (fun z : ℂ => (1 + z • B : Matrix ι ι ℂ).det)
      (Matrix.trace B) 0 := by
  let P : Polynomial ℂ := Matrix.det
    ((1 : Matrix ι ι (Polynomial ℂ)) + (Polynomial.X : Polynomial ℂ) •
      B.map (Polynomial.C : ℂ →+* Polynomial ℂ))
  have hpoly : HasDerivAt (fun z : ℂ => P.eval z) (Matrix.trace B) 0 := by
    convert! P.hasDerivAt 0 using 1
    simpa [P] using! (Matrix.derivative_det_one_add_X_smul B).symm
  convert hpoly using 1
  funext z
  simp [P, eval_det, ← Matrix.smul_eq_mul_diagonal]

def routePPrimitiveGammaJuliaPhysicalStokesHellingerSquareCoordinatePencil
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (v : ℂ) : Matrix ι ι ℂ :=
  1 - (64 * v) • (H * H)

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil_eq_squareCoordinate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (u : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u =
      routePPrimitiveGammaJuliaPhysicalStokesHellingerSquareCoordinatePencil H (u ^ (2 : ℕ)) := by
  rfl

theorem trace_sq_eq_matHSNormSq_of_isHermitian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    (H * H).trace =
      ((GaloisForLFunctions.HTGeometry.matHSNormSq H : ℝ) : ℂ) := by
  calc
    (H * H).trace = (Matrix.conjTranspose H * H).trace := by rw [hH.eq]
    _ = ((GaloisForLFunctions.HTGeometry.matHSNormSq H : ℝ) : ℂ) :=
      (GaloisForLFunctions.HTGeometry.matHSNormSq_eq_trace H).symm

theorem hasDerivAt_squareCoordinatePencil_det_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    HasDerivAt
      (fun v : ℂ =>
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerSquareCoordinatePencil H v).det)
      (-64 * ((GaloisForLFunctions.HTGeometry.matHSNormSq H : ℝ) : ℂ)) 0 := by
  have h := hasDerivAt_complexDet_one_add_smul ((-64 : ℂ) • (H * H))
  have htrace : Matrix.trace ((-64 : ℂ) • (H * H)) =
      -64 * ((GaloisForLFunctions.HTGeometry.matHSNormSq H : ℝ) : ℂ) := by
    simpa using congrArg (fun z : ℂ => (-64 : ℂ) * z)
      (trace_sq_eq_matHSNormSq_of_isHermitian H hH)
  rw [htrace] at h
  convert h using 1
  funext v
  congr 1
  unfold routePPrimitiveGammaJuliaPhysicalStokesHellingerSquareCoordinatePencil
  module

private theorem tendsto_sq_nhdsNE_zero :
    Tendsto (fun u : ℂ => u ^ (2 : ℕ)) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hsq : Tendsto (fun u : ℂ => u ^ (2 : ℕ)) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      have hsq' := ((continuousAt_id' (y := (0 : ℂ))).mul
        (continuousAt_id' (y := (0 : ℂ)))).tendsto
      convert hsq' using 1
      funext u
      change u ^ (2 : ℕ) = u * u
      exact pow_two u
      simp
    exact hsq.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact pow_ne_zero 2 hu

theorem tendsto_squaredChildPencil_det_sub_one_div_sq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    Tendsto
      (fun u : ℂ =>
        ((routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil H u).det - 1) /
          u ^ (2 : ℕ))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-64 * ((GaloisForLFunctions.HTGeometry.matHSNormSq H : ℝ) : ℂ))) := by
  have hslope := (hasDerivAt_squareCoordinatePencil_det_zero H hH).tendsto_slope_zero
  have hcomp := hslope.comp tendsto_sq_nhdsNE_zero
  simpa [Function.comp_def,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil_eq_squareCoordinate,
    routePPrimitiveGammaJuliaPhysicalStokesHellingerSquareCoordinatePencil,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using hcomp

theorem tendsto_channelCompleteFiniteDet_sub_one_div_sq_zero
    (d : ℝ) (t : Finset Nat.Primes) :
    Tendsto
      (fun u : ℂ =>
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
            (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u - 1) /
          u ^ (2 : ℕ))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-64 *
        ((GaloisForLFunctions.HTGeometry.matHSNormSq
          (HilbertSchmidt.blockMatrix
            (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t) : ℝ) : ℂ))) := by
  simpa only [
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild]
    using tendsto_squaredChildPencil_det_sub_one_div_sq_zero
      (HilbertSchmidt.blockMatrix
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t)
      (routePPrimitiveGammaJuliaStokesCofinalChildBlockMatrix_posSemidef d t).isHermitian

def routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteSquareJet
    (d : ℝ) (t : Finset Nat.Primes) : ℝ :=
  -64 * GaloisForLFunctions.HTGeometry.matHSNormSq
    (HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t)

def routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet
    (d : ℝ) : ℝ :=
  -64 * routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d

theorem tendsto_childBlockEnergy_atTop
    {d : ℝ} (hd : 0 < d) :
    Tendsto
      (fun t : Finset Nat.Primes =>
        GaloisForLFunctions.HTGeometry.matHSNormSq
          (HilbertSchmidt.blockMatrix
            (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t))
      atTop
      (𝓝 (routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d)) := by
  let K := routePPrimitiveGammaJuliaStokesCofinalChildKernel d
  have hK : HilbertSchmidt.IsHS K :=
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_isHS hd
  have hsum : Tendsto
      (fun t : Finset Nat.Primes => ∑ pq ∈ t ×ˢ t, ‖K pq‖ ^ (2 : ℕ))
      atTop (𝓝 (∑' pq : Nat.Primes × Nat.Primes, ‖K pq‖ ^ (2 : ℕ))) :=
    hK.hasSum.comp (HilbertSchmidt.tendsto_finset_product_atTop (ι := Nat.Primes))
  convert hsum using 1
  · funext t
    exact HilbertSchmidt.matHSNormSq_blockMatrix K t
  · congr 1
    rw [routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy]
    apply tsum_congr
    intro pq
    rw [Complex.sq_norm]

theorem tendsto_finiteSquareJet_atTop
    {d : ℝ} (hd : 0 < d) :
    Tendsto
      (routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteSquareJet d)
      atTop
      (𝓝 (routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet d)) := by
  have hneg := ((tendsto_childBlockEnergy_atTop hd).const_mul (64 : ℝ)).neg
  change Tendsto
    (fun t : Finset Nat.Primes => -64 *
      GaloisForLFunctions.HTGeometry.matHSNormSq
        (HilbertSchmidt.blockMatrix
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t))
    atTop
    (𝓝 (-64 * routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d))
  convert hneg using 1
  · funext t
    ring
  · congr 1
    ring

theorem eventually_cofinalSquareJet_le :
    ∀ᶠ d in 𝓝[>] (0 : ℝ),
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet d ≤
        (-256 / 11025 : ℝ) := by
  filter_upwards [eventually_wallHilbertSchmidtEnergy_ge] with d hd
  rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet]
  nlinarith

theorem eventually_eventually_finiteSquareJet_le :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), ∀ᶠ t : Finset Nat.Primes in atTop,
      routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteSquareJet d t ≤
        (-128 / 11025 : ℝ) := by
  filter_upwards [self_mem_nhdsWithin, eventually_wallHilbertSchmidtEnergy_ge]
    with d hd henergy
  have hlim :
      routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet d <
        (-128 / 11025 : ℝ) := by
    rw [routePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalSquareJet]
    nlinarith
  exact ((tendsto_order.1 (tendsto_finiteSquareJet_atTop hd)).2 _ hlim).mono
    (fun _ ht => ht.le)

end

end RHTower

