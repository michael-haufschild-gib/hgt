import GaloisForLFunctions.HTGeometry.RydbergSymmetricFrozenNoise
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaSymbol
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLogisticCoupling
import GaloisForLFunctions.HTGeometry.SteinhausLaplaceProduct
import GaloisForLFunctions.RHTower.HardyZ

/-!
# Symmetric frozen-noise applications across the corpus

The parity mechanism isolated from arXiv:2608.29858 applies mechanically to
pre-existing even response profiles.  Each profile is packaged with its
existing reflection theorem, yielding exact symmetric-average invariance and
zero first-order response at the origin.
-/

noncomputable section

namespace RHTower

def gaussianRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := GaloisForLFunctions.gaussReal
  reflection := gaussReal_neg

theorem gaussian_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage GaloisForLFunctions.gaussReal ε =
      GaloisForLFunctions.gaussReal ε :=
  gaussianRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem gaussian_frozenNoise_deriv_zero :
    deriv GaloisForLFunctions.gaussReal 0 = 0 :=
  gaussianRydbergEvenResponse.deriv_zero

def logisticKernelRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := logisticKernel
  reflection := logisticKernel_neg

theorem logisticKernel_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage logisticKernel ε = logisticKernel ε :=
  logisticKernelRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem logisticKernel_frozenNoise_deriv_zero : deriv logisticKernel 0 = 0 :=
  logisticKernelRydbergEvenResponse.deriv_zero

def logisticMomentRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := logisticMoment
  reflection := logisticMoment_neg

theorem logisticMoment_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage logisticMoment ε = logisticMoment ε :=
  logisticMomentRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem logisticMoment_frozenNoise_deriv_zero : deriv logisticMoment 0 = 0 :=
  logisticMomentRydbergEvenResponse.deriv_zero

def steinhausLaplaceRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := HTGeometry.steinhausLaplace
  reflection := HTGeometry.steinhausLaplace_neg

theorem steinhausLaplace_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage HTGeometry.steinhausLaplace ε =
      HTGeometry.steinhausLaplace ε :=
  steinhausLaplaceRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem steinhausLaplace_frozenNoise_deriv_zero :
    deriv HTGeometry.steinhausLaplace 0 = 0 :=
  steinhausLaplaceRydbergEvenResponse.deriv_zero

def steinhausLogLaplaceRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := HTGeometry.steinhausLogLaplace
  reflection := HTGeometry.steinhausLogLaplace_neg

theorem steinhausLogLaplace_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage HTGeometry.steinhausLogLaplace ε =
      HTGeometry.steinhausLogLaplace ε :=
  steinhausLogLaplaceRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem steinhausLogLaplace_frozenNoise_deriv_zero :
    deriv HTGeometry.steinhausLogLaplace 0 = 0 :=
  steinhausLogLaplaceRydbergEvenResponse.deriv_zero

def hardyZRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := hardyZ
  reflection := hardyZ_neg

theorem hardyZ_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage hardyZ ε = hardyZ ε :=
  hardyZRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem hardyZ_frozenNoise_deriv_zero : deriv hardyZ 0 = 0 :=
  hardyZRydbergEvenResponse.deriv_zero

def hardySEMRydbergEvenResponse (N : ℕ) : HTGeometry.RydbergEvenResponse where
  response := hardySEM N
  reflection := hardySEM_neg N

theorem hardySEM_symmetricFrozenAverage (N : ℕ) (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage (hardySEM N) ε = hardySEM N ε :=
  (hardySEMRydbergEvenResponse N).symmetricFrozenAverage_eq ε

theorem hardySEM_frozenNoise_deriv_zero (N : ℕ) : deriv (hardySEM N) 0 = 0 :=
  (hardySEMRydbergEvenResponse N).deriv_zero

def suzukiGammaSymbolRydbergEvenResponse : HTGeometry.RydbergEvenResponse where
  response := GaloisForLFunctions.RHTower.suzukiGammaSymbol
  reflection := GaloisForLFunctions.RHTower.suzukiGammaSymbol_neg

theorem suzukiGammaSymbol_symmetricFrozenAverage (ε : ℝ) :
    HTGeometry.symmetricFrozenAverage
        GaloisForLFunctions.RHTower.suzukiGammaSymbol ε =
      GaloisForLFunctions.RHTower.suzukiGammaSymbol ε :=
  suzukiGammaSymbolRydbergEvenResponse.symmetricFrozenAverage_eq ε

theorem suzukiGammaSymbol_frozenNoise_deriv_zero :
    deriv GaloisForLFunctions.RHTower.suzukiGammaSymbol 0 = 0 :=
  suzukiGammaSymbolRydbergEvenResponse.deriv_zero

end RHTower
