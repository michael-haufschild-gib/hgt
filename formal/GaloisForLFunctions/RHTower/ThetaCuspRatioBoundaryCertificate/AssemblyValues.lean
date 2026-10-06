import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment2
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment4
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment6
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment8
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Moment10
import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.SlopeCofactors
namespace HTGeometry.ThetaRatioInfinity
noncomputable section
open MvPolynomial ThetaRatioSource ThetaRatioSquare

def boundaryQM2 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryMoment2ReNorm v k).val,(boundaryMoment2ImNorm v k).val⟩

theorem boundaryQM2_eq (v k : ℂ) : boundaryQM2 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^4*24^1)⁻¹)*boundaryHom v k moment2 := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQM2] using (boundaryMoment2ReNorm v k).property.symm
  · simpa [boundaryQM2] using (boundaryMoment2ImNorm v k).property.symm

def boundaryQF2 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryFlow2ReNorm v k).val,(boundaryFlow2ImNorm v k).val⟩

theorem boundaryQF2_eq (v k : ℂ) : boundaryQF2 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^4*24^1)⁻¹)*boundaryHom v k (squareLie moment2) := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQF2] using (boundaryFlow2ReNorm v k).property.symm
  · simpa [boundaryQF2] using (boundaryFlow2ImNorm v k).property.symm

def boundaryT2 (v k : ℂ) : BoundaryAlg v k :=
  algebraMap ℂ (BoundaryAlg v k) (6*k-1)*boundaryQF2 v k-
    2*boundaryQM2 v k*⟨0,6*(12*k+4)*v⟩

def boundaryQM4 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryMoment4ReNorm v k).val,(boundaryMoment4ImNorm v k).val⟩

theorem boundaryQM4_eq (v k : ℂ) : boundaryQM4 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^6*24^2)⁻¹)*boundaryHom v k moment4 := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQM4] using (boundaryMoment4ReNorm v k).property.symm
  · simpa [boundaryQM4] using (boundaryMoment4ImNorm v k).property.symm

def boundaryQF4 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryFlow4ReNorm v k).val,(boundaryFlow4ImNorm v k).val⟩

theorem boundaryQF4_eq (v k : ℂ) : boundaryQF4 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^6*24^2)⁻¹)*boundaryHom v k (squareLie moment4) := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQF4] using (boundaryFlow4ReNorm v k).property.symm
  · simpa [boundaryQF4] using (boundaryFlow4ImNorm v k).property.symm

def boundaryT4 (v k : ℂ) : BoundaryAlg v k :=
  algebraMap ℂ (BoundaryAlg v k) (6*k-1)*boundaryQF4 v k-
    2*boundaryQM4 v k*⟨0,6*(12*k+4)*v⟩

def boundaryQM6 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryMoment6ReNorm v k).val,(boundaryMoment6ImNorm v k).val⟩

theorem boundaryQM6_eq (v k : ℂ) : boundaryQM6 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^8*24^3)⁻¹)*boundaryHom v k moment6 := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQM6] using (boundaryMoment6ReNorm v k).property.symm
  · simpa [boundaryQM6] using (boundaryMoment6ImNorm v k).property.symm

def boundaryQF6 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryFlow6ReNorm v k).val,(boundaryFlow6ImNorm v k).val⟩

theorem boundaryQF6_eq (v k : ℂ) : boundaryQF6 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^8*24^3)⁻¹)*boundaryHom v k (squareLie moment6) := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQF6] using (boundaryFlow6ReNorm v k).property.symm
  · simpa [boundaryQF6] using (boundaryFlow6ImNorm v k).property.symm

def boundaryT6 (v k : ℂ) : BoundaryAlg v k :=
  algebraMap ℂ (BoundaryAlg v k) (6*k-1)*boundaryQF6 v k-
    2*boundaryQM6 v k*⟨0,6*(12*k+4)*v⟩

def boundaryQM8 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryMoment8ReNorm v k).val,(boundaryMoment8ImNorm v k).val⟩

theorem boundaryQM8_eq (v k : ℂ) : boundaryQM8 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^10*24^4)⁻¹)*boundaryHom v k moment8 := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQM8] using (boundaryMoment8ReNorm v k).property.symm
  · simpa [boundaryQM8] using (boundaryMoment8ImNorm v k).property.symm

def boundaryQF8 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryFlow8ReNorm v k).val,(boundaryFlow8ImNorm v k).val⟩

theorem boundaryQF8_eq (v k : ℂ) : boundaryQF8 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^10*24^4)⁻¹)*boundaryHom v k (squareLie moment8) := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQF8] using (boundaryFlow8ReNorm v k).property.symm
  · simpa [boundaryQF8] using (boundaryFlow8ImNorm v k).property.symm

def boundaryT8 (v k : ℂ) : BoundaryAlg v k :=
  algebraMap ℂ (BoundaryAlg v k) (6*k-1)*boundaryQF8 v k-
    2*boundaryQM8 v k*⟨0,6*(12*k+4)*v⟩

def boundaryQM10 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryMoment10ReNorm v k).val,(boundaryMoment10ImNorm v k).val⟩

theorem boundaryQM10_eq (v k : ℂ) : boundaryQM10 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^12*24^5)⁻¹)*boundaryHom v k moment10 := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQM10] using (boundaryMoment10ReNorm v k).property.symm
  · simpa [boundaryQM10] using (boundaryMoment10ImNorm v k).property.symm

def boundaryQF10 (v k : ℂ) : BoundaryAlg v k :=
  ⟨(boundaryFlow10ReNorm v k).val,(boundaryFlow10ImNorm v k).val⟩

theorem boundaryQF10_eq (v k : ℂ) : boundaryQF10 v k =
    algebraMap ℂ (BoundaryAlg v k) (((6:ℂ)^12*24^5)⁻¹)*boundaryHom v k (squareLie moment10) := by
  apply QuadraticAlgebra.ext
  · simpa [boundaryQF10] using (boundaryFlow10ReNorm v k).property.symm
  · simpa [boundaryQF10] using (boundaryFlow10ImNorm v k).property.symm

def boundaryT10 (v k : ℂ) : BoundaryAlg v k :=
  algebraMap ℂ (BoundaryAlg v k) (6*k-1)*boundaryQF10 v k-
    2*boundaryQM10 v k*⟨0,6*(12*k+4)*v⟩

end
end HTGeometry.ThetaRatioInfinity
