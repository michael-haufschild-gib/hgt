import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalSquareIncidence
import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalQuadraticPrincipal

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open Polynomial

abbrev TerminalFamily := Polynomial (Polynomial ℂ)

def specializeTerminal (T : ℂ) : TerminalFamily →+* Polynomial ℂ :=
  Polynomial.mapRingHom (Polynomial.evalRingHom T)

theorem specializeTerminal_coeff (T : ℂ) (P : TerminalFamily) (j : ℕ) :
    (specializeTerminal T P).coeff j=(P.coeff j).eval T := by
  simp [specializeTerminal]

theorem specializeTerminal_C (T : ℂ) (P : Polynomial ℂ) :
    specializeTerminal T (C P)=C (P.eval T) := by simp [specializeTerminal]

theorem specializeTerminal_X (T : ℂ) : specializeTerminal T X=X := by
  simp [specializeTerminal]

theorem specializeTerminal_divX (T : ℂ) (P : TerminalFamily) :
    specializeTerminal T P.divX=(specializeTerminal T P).divX := by
  ext j
  simp only [specializeTerminal_coeff,coeff_divX]

def homogenizeFamily (d : ℕ) (P : Polynomial ℂ) : TerminalFamily :=
  ((P.map C).comp (C X*X)).reflect d

theorem specialize_homogenizeFamily (T : ℂ) (d : ℕ) (P : Polynomial ℂ) :
    specializeTerminal T (homogenizeFamily d P)=homogenizeAt d P T := by
  ext j
  simp [specializeTerminal_coeff,homogenizeFamily,homogenizeAt,coeff_reflect,
    comp_C_mul_X_coeff]

def reflectionFamily (n : ℕ) : TerminalFamily :=
  homogenizeFamily (n-1) (amplitudeSelf n)-6*homogenizeFamily n (amplitudeCross n)

def reflectionYFamily (n : ℕ) : TerminalFamily :=
  2*homogenizeFamily (n-1) (amplitudeSelf n)-6*homogenizeFamily n (amplitudeCross n)

def reflectionTFamily (n : ℕ) : TerminalFamily :=
  homogenizeFamily (n-2) (amplitudeSelf n).derivative-
    6*homogenizeFamily (n-1) (amplitudeCross n).derivative

theorem specialize_reflectionFamily (T : ℂ) (n : ℕ) :
    specializeTerminal T (reflectionFamily n)=reflectionHomogeneous n 1 T := by
  simp [map_ofNat,reflectionFamily,reflectionHomogeneous,specialize_homogenizeFamily]

theorem specialize_reflectionYFamily (T : ℂ) (n : ℕ) :
    specializeTerminal T (reflectionYFamily n)=reflectionYHomogeneous n 1 T := by
  simp [map_ofNat,reflectionYFamily,reflectionYHomogeneous,specialize_homogenizeFamily]

theorem specialize_reflectionTFamily (T : ℂ) (n : ℕ) :
    specializeTerminal T (reflectionTFamily n)=reflectionTHomogeneous n 1 T := by
  simp [map_ofNat,reflectionTFamily,reflectionTHomogeneous,specialize_homogenizeFamily]

def reflectionFamilyRows : Fin 5 → TerminalFamily :=
  ![reflectionFamily 2,reflectionFamily 4,reflectionFamily 6,reflectionFamily 8,reflectionFamily 10]

def reflectionYFamilyRows : Fin 5 → TerminalFamily :=
  ![reflectionYFamily 2,reflectionYFamily 4,reflectionYFamily 6,reflectionYFamily 8,reflectionYFamily 10]

def reflectionTFamilyRows : Fin 5 → TerminalFamily :=
  ![reflectionTFamily 2,reflectionTFamily 4,reflectionTFamily 6,reflectionTFamily 8,reflectionTFamily 10]

def minorFamily : TerminalFamily :=
  -(12^18)*hankel (reflectionFamilyRows 0) (reflectionFamilyRows 1)
    (reflectionFamilyRows 2) (reflectionFamilyRows 3) (reflectionFamilyRows 4)

def minorYFamily : TerminalFamily := -(12^18)*direction reflectionFamilyRows reflectionYFamilyRows

def minorTFamily : TerminalFamily := -(12^18)*direction reflectionFamilyRows reflectionTFamilyRows

theorem specialize_minorFamily (T : ℂ) :
    specializeTerminal T minorFamily=minorHomogeneous 1 T := by
  simp [map_ofNat,minorFamily,minorHomogeneous,hankel,reflectionFamilyRows,reflectionHomogeneousRows,
    specialize_reflectionFamily]

theorem specialize_minorYFamily (T : ℂ) :
    specializeTerminal T minorYFamily=minorYHomogeneous 1 T := by
  simp [map_ofNat,minorYFamily,minorYHomogeneous,direction,reflectionFamilyRows,reflectionHomogeneousRows,
    reflectionYFamilyRows,reflectionYHomogeneousRows,specialize_reflectionFamily,
    specialize_reflectionYFamily]

theorem specialize_minorTFamily (T : ℂ) :
    specializeTerminal T minorTFamily=minorTHomogeneous 1 T := by
  simp [map_ofNat,minorTFamily,minorTHomogeneous,direction,reflectionFamilyRows,reflectionHomogeneousRows,
    reflectionTFamilyRows,reflectionTHomogeneousRows,specialize_reflectionFamily,
    specialize_reflectionTFamily]

def slopeFamilyHomogeneous : TerminalFamily :=
  12*((2-3*X)*((C (1+X)+X)*minorYFamily+X*C X*minorTFamily)-
    12*(C (1+X)+X)*minorFamily)

def slopeFamily : TerminalFamily := slopeFamilyHomogeneous.divX

theorem specialize_slopeFamilyHomogeneous (T : ℂ) :
    specializeTerminal T slopeFamilyHomogeneous=slopeHomogeneous 1 T := by
  simp [map_ofNat,slopeFamilyHomogeneous,slopeHomogeneous,specializeTerminal_C,specializeTerminal_X,
    specialize_minorFamily,specialize_minorYFamily,specialize_minorTFamily]

theorem specialize_slopeFamily (T : ℂ) :
    specializeTerminal T slopeFamily=slopeRegularized 1 T := by
  rw [slopeFamily,specializeTerminal_divX,specialize_slopeFamilyHomogeneous,slopeRegularized]

theorem slopeFamily_zero :
    slopeFamily.coeff 0=221184*(12:Polynomial ℂ)^18*(X+1)^2*X^15 := by
  apply Polynomial.funext
  intro T
  rw [←specializeTerminal_coeff,specialize_slopeFamily,slopeRegularized_zero]
  simp


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
