import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalQuadraticPrincipal

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open scoped QuadraticAlgebra

def quadraticChange {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b : R} {a' b' : S} (ha : f a=a') (hb : f b=b') :
    QuadraticAlgebra R a b →+* QuadraticAlgebra S a' b' where
  toFun q := ⟨f q.re,f q.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp
  map_mul' p q := by ext <;> simp [ha,hb]

theorem quadraticChange_re {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b : R} {a' b' : S} (ha : f a=a') (hb : f b=b')
    (q : QuadraticAlgebra R a b) : (quadraticChange f ha hb q).re=f q.re := rfl

theorem quadraticChange_im {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b : R} {a' b' : S} (ha : f a=a') (hb : f b=b')
    (q : QuadraticAlgebra R a b) : (quadraticChange f ha hb q).im=f q.im := rfl

theorem quadraticChange_omega {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b : R} {a' b' : S} (ha : f a=a') (hb : f b=b') :
    quadraticChange f ha hb QuadraticAlgebra.omega=QuadraticAlgebra.omega := by
  ext <;> simp [quadraticChange]

theorem quadraticChange_scalar {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b : R} {a' b' : S} (ha : f a=a') (hb : f b=b') (r : R) :
    quadraticChange f ha hb (algebraMap R _ r)=algebraMap S _ (f r) := by
  ext <;> simp [quadraticChange]


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
