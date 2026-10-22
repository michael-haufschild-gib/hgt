import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.RHTower.Deninger.DeningerKummerHasse
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittHasse
import GaloisForLFunctions.RHTower.WindingHomotopyHasse

/-!
# Kummer, Calderón--Witt, and winding Hasse families

Number-field Kummer currents are separated at every place; Calderón--Witt Koszul data are
separated locally and over the direct sum of all primes; realized winding number classifies
nonvanishing-loop deformation classes.
-/

namespace RHTower

noncomputable section

/-- Number-field places jointly determine a Kummer class modulo roots of unity. -/
def deningerKummerPlacewiseHasseFamily
    (K : Type*) [Field K] [NumberField K] :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (deningerKummerGroup K) (DeningerPlace K) where
  Local := fun _ => ℝ
  profile := fun x v => deningerKummerQuotientLocalValue K x v
  profile_injective := by
    intro x y hxy
    exact (deningerKummerQuotient_congr_placewise_hasse_iff K x y).2
      (fun v => congrFun hxy v)

/-- At one prime, the Calderón--Witt degree-two boundary is the complete quotient invariant. -/
def deningerCalderonWittLocalKoszulHasseFamily (p : Nat.Primes) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (DeningerCalderonWittAlgebraicDegreeOne p ⧸
        LinearMap.range (deningerCalderonWittDefectAxisInclusion p))
      Unit :=
  GaloisForLFunctions.HTGeometry.HasseFamily.ofEquivSingle
    (deningerCalderonWittKoszulQuotientEquiv p).toEquiv

/-- All primewise Calderón--Witt degree-two boundaries jointly determine global degree-one data
modulo every local defect axis. -/
def deningerCalderonWittGlobalKoszulHasseFamily :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (DeningerCalderonWittAlgebraicGlobalDegreeOne ⧸
        deningerCalderonWittGlobalDefectAxisInclusionAdd.range)
      Nat.Primes where
  Local := fun p => DeningerCalderonWittAlgebraicDegreeTwo p
  profile := fun x p => deningerCalderonWittGlobalKoszulQuotientEquiv x p
  profile_injective := by
    intro x y hxy
    apply deningerCalderonWittGlobalKoszulQuotientEquiv.injective
    apply DFinsupp.ext
    intro p
    exact congrFun hxy p

/-- Realized winding number is a complete invariant of nonvanishing-loop deformation classes. -/
def windingLoopClassHasseFamily (a b : ℝ) :
    GaloisForLFunctions.HTGeometry.HasseFamily
      (WindingLoopHasseClass a b) Unit :=
  GaloisForLFunctions.HTGeometry.HasseFamily.ofEquivSingle
    (windingLoopClassHasseEquiv a b)

end
end RHTower
