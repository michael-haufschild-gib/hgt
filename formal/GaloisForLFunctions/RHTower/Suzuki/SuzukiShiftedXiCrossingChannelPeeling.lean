import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiBoundaryFactorization
import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingPacket
import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingRadialPhase

open Complex Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Fixed finite packet of isolated shifted-Xi layers. Each positive multiplicity is retained
literally; `q` selects the layer location, not a truncation of the global divisor. -/
inductive XiShiftCrossingPacket {ι : Type*} (omega : ι → ℝ) where
  | terminal (q : ∀ i, XiShiftRightZeroCopy (omega i))
      (m : ℕ) (hm : 0 < m)
  | cons (q : ∀ i, XiShiftRightZeroCopy (omega i))
      (m : ℕ) (hm : 0 < m) (tail : XiShiftCrossingPacket omega)

namespace XiShiftCrossingPacket

def multiplicity {ι : Type*} {omega : ι → ℝ} :
    XiShiftCrossingPacket omega → ℕ
  | terminal _ m _ => m
  | cons _ m _ tail => m + multiplicity tail

def blockDivisor {ι : Type*} {omega : ι → ℝ}
    (q : ∀ i, XiShiftRightZeroCopy (omega i))
    (m : ℕ) (_hm : 0 < m) (i : ι) : FiniteBlaschke :=
  FiniteBlaschke.repeatSingle
    (norm_xiShiftPoleDiskCoordinate_lt_one (omega i) (q i)) (m - 1)

@[simp] theorem deg_blockDivisor {ι : Type*} {omega : ι → ℝ}
    (q : ∀ i, XiShiftRightZeroCopy (omega i))
    (m : ℕ) (hm : 0 < m) (i : ι) :
    (blockDivisor q m hm i).deg = m := by
  rw [blockDivisor, FiniteBlaschke.deg_repeatSingle]
  omega

def localPhase {ι : Type*} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (q : ∀ i, XiShiftRightZeroCopy (omega i)) (i : ι) : ℂ :=
  phaseNormalize 1
    ((xiShiftInfiniteSchurNumerator (homega i).le).fn
      (xiShiftPoleDiskCoordinate (omega i) (q i)))

def toBoundaryPacket {ι : Type*} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i) :
    XiShiftCrossingPacket omega → FiniteBoundaryScalingPacket ι
  | terminal q m hm =>
      .terminal (blockDivisor q m hm) (localPhase homega q)
  | cons q m hm tail =>
      .cons (blockDivisor q m hm) (localPhase homega q)
        (toBoundaryPacket homega tail)

@[simp] theorem deg_toBoundaryPacket_divisor {ι : Type*} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (i : ι) :
    ((toBoundaryPacket homega P).divisor i).deg = multiplicity P := by
  induction P with
  | terminal q m hm => exact deg_blockDivisor q m hm i
  | cons q m hm tail ih =>
      rw [toBoundaryPacket, FiniteBoundaryScalingPacket.divisor,
        FiniteBlaschke.deg_append, deg_blockDivisor, ih, multiplicity]

/-- Exact tame isolated-layer conditions from theorem B/C, block by block. -/
def Tame {ι : Type*} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i) (l : Filter ι) :
    XiShiftCrossingPacket omega → Prop
  | terminal q m _ =>
      Tendsto (fun i =>
        omega i / (I * xiSpectralPoint (q i).1).re) l (𝓝 1) ∧
      Tendsto (fun i =>
        ‖xiShiftCrossingResidualValue (homega i).le (q i) m‖) l (𝓝 1)
  | cons q m _ tail =>
      Tendsto (fun i =>
        omega i / (I * xiSpectralPoint (q i).1).re) l (𝓝 1) ∧
      Tendsto (fun i =>
        ‖xiShiftCrossingResidualValue (homega i).le (q i) m‖) l (𝓝 1) ∧
      Tame homega l tail

/-- Every actual tame shifted-Xi packet supplies the exact separated local residual convergence
needed by boundary scaling `(16)`. -/
theorem residualTendsToZero_toBoundaryPacket
    {ι : Type*} {l : Filter ι} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (hP : Tame homega l P) :
    (toBoundaryPacket homega P).ResidualTendsToZero
      (fun i => xiShiftInfiniteSchurNumerator (homega i).le) l := by
  induction P with
  | terminal q m hm =>
      apply tendsto_norm_finiteModelResidualCore_repeatSingle_zero_of_norm_value_one
        (fun i => xiShiftInfiniteSchurNumerator (homega i).le)
        (fun i => xiShiftInfiniteSchurNumerator_isometry (homega i).le)
        (fun i => xiShiftPoleDiskCoordinate (omega i) (q i))
        (fun i => norm_xiShiftPoleDiskCoordinate_lt_one (omega i) (q i))
        (m - 1)
      exact tendsto_norm_xiShiftInfiniteSchurNumerator_pole_one_of_tameCrossing
        omega homega q m hP.1 hP.2
  | cons q m hm tail ih =>
      refine ⟨?_, ih hP.2.2⟩
      apply tendsto_norm_finiteModelResidualCore_repeatSingle_zero_of_norm_value_one
        (fun i => xiShiftInfiniteSchurNumerator (homega i).le)
        (fun i => xiShiftInfiniteSchurNumerator_isometry (homega i).le)
        (fun i => xiShiftPoleDiskCoordinate (omega i) (q i))
        (fun i => norm_xiShiftPoleDiskCoordinate_lt_one (omega i) (q i))
        (m - 1)
      exact tendsto_norm_xiShiftInfiniteSchurNumerator_pole_one_of_tameCrossing
        omega homega q m hP.1 hP.2.1

/-- Crossing channel has exactly total isolated-layer multiplicity. -/
theorem finrank_crossingChannel_eq_multiplicity
    {ι : Type*} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : ι → DiskMultiplier)
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i)) (i : ι) :
    Module.finrank ℂ
      (hardyMultiplierFiniteCrossingChannel (B₀ i)
        ((toBoundaryPacket homega P).divisor i)) = multiplicity P := by
  rw [finrank_hardyMultiplierFiniteCrossingChannel _ _ (hB₀ i),
    deg_toBoundaryPacket_divisor]

/-- Actual shifted-Xi theorem-C Gram convergence `(11)` after the literal factorization
`B_omega = B_0 D` of the complete pole multiplier. -/
theorem tendsto_norm_actualXiCrossingGramDefect_zero
    {ι : Type*} {l : Filter ι} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : ι → DiskMultiplier)
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hfactor : ∀ i,
      (B₀ i).mul ((toBoundaryPacket homega P).divisor i).toMultiplier =
        xiShiftPoleBlaschkeMultiplier (homega i).le)
    (hP : Tame homega l P) :
    Tendsto (fun i =>
      ‖channelGramDefect
        (hardyMultiplierFiniteCrossingChannel (B₀ i)
          ((toBoundaryPacket homega P).divisor i))
        (hardyMultiplierLeakageCore
          (xiShiftInfiniteSchurNumerator (homega i).le)
          (xiShiftPoleBlaschkeMultiplier (homega i).le))‖) l (𝓝 0) := by
  have h := tendsto_norm_hardyMultiplierPacketCrossingGramDefect_zero
    (fun i => xiShiftInfiniteSchurNumerator (homega i).le) B₀
    (toBoundaryPacket homega P)
    (fun i => xiShiftInfiniteSchurNumerator_isometry (homega i).le)
    hB₀ (residualTendsToZero_toBoundaryPacket homega P hP)
  convert h using 1
  funext i
  rw [hfactor i]

/-- Actual shifted-Xi theorem-C off-diagonal convergence `(12)`. -/
theorem tendsto_norm_actualXiCrossingOffDiagonalGram_zero
    {ι : Type*} {l : Filter ι} {omega : ι → ℝ}
    (homega : ∀ i, 0 < omega i)
    (P : XiShiftCrossingPacket omega) (B₀ : ι → DiskMultiplier)
    (hB₀ : ∀ i, HardyMultiplierIsometry (B₀ i))
    (hfactor : ∀ i,
      (B₀ i).mul ((toBoundaryPacket homega P).divisor i).toMultiplier =
        xiShiftPoleBlaschkeMultiplier (homega i).le)
    (hP : Tame homega l P) :
    Tendsto (fun i =>
      ‖channelOffDiagonalGram
        (hardyMultiplierFiniteCrossingChannel (B₀ i)
          ((toBoundaryPacket homega P).divisor i))
        (hardyMultiplierLeakageCore
          (xiShiftInfiniteSchurNumerator (homega i).le)
          (xiShiftPoleBlaschkeMultiplier (homega i).le))‖) l (𝓝 0) := by
  have h := tendsto_norm_hardyMultiplierPacketCrossingOffDiagonalGram_zero
    (fun i => xiShiftInfiniteSchurNumerator (homega i).le) B₀
    (toBoundaryPacket homega P)
    (fun i => xiShiftInfiniteSchurNumerator_isometry (homega i).le)
    hB₀ (residualTendsToZero_toBoundaryPacket homega P hP)
  convert h using 1
  funext i
  rw [hfactor i]

end XiShiftCrossingPacket

end

end RHTower
