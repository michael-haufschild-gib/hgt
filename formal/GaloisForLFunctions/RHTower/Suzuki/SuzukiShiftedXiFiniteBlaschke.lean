import GaloisForLFunctions.HTGeometry.FiniteBlaschkeFamily
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiDivisorFactorization

open Complex

namespace RHTower

noncomputable section

/-- Cayley image of one shifted upper-half-plane Xi pole. -/
def xiShiftPoleDiskCoordinate (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) : ℂ :=
  (xiShiftPoleCoordinate omega q - I) /
    (xiShiftPoleCoordinate omega q + I)

theorem norm_xiShiftPoleDiskCoordinate_lt_one (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) :
    ‖xiShiftPoleDiskCoordinate omega q‖ < 1 := by
  exact GaloisForLFunctions.cayley_upperHalfPlane_to_disk
    (xiShiftPoleCoordinate omega q)
    (xiShiftPoleCoordinate_im_pos omega q)

/-- Finite Blaschke denominator obtained from every shifted Xi pole copy. -/
def xiShiftFinitePoleBlaschke (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] :
    GaloisForLFunctions.HTGeometry.FiniteBlaschke :=
  GaloisForLFunctions.HTGeometry.finiteBlaschkeOfFiniteFamily
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)

@[simp]
theorem xiShiftFinitePoleBlaschke_deg (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] :
    (xiShiftFinitePoleBlaschke omega).deg =
      Fintype.card (XiShiftRightZeroCopy omega) := by
  exact GaloisForLFunctions.HTGeometry.finiteBlaschkeOfFiniteFamily_deg
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega)

theorem xiShiftFinitePoleBlaschke_fn (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    (xiShiftFinitePoleBlaschke omega).fn z =
      ∏ q : XiShiftRightZeroCopy omega,
        GaloisForLFunctions.HTGeometry.blaschkeFactor
          (xiShiftPoleDiskCoordinate omega q) z := by
  exact GaloisForLFunctions.HTGeometry.finiteBlaschkeOfFiniteFamily_fn
    (xiShiftPoleDiskCoordinate omega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega) z

end

end RHTower
