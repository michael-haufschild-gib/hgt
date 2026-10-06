import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalQuadraticChange

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section
open scoped QuadraticAlgebra

def quadraticScale {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : S) {a b : R} {a' b' : S}
    (ha : c^2*a'=f a) (hb : c*b'=f b) :
    QuadraticAlgebra R a b →+* QuadraticAlgebra S a' b' where
  toFun q := ⟨f q.re,c*f q.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' p q := by ext <;> simp [mul_add]
  map_mul' p q := by
    apply QuadraticAlgebra.ext
    · change f (p.re*q.re+a*p.im*q.im)=
        f p.re*f q.re+a'*(c*f p.im)*(c*f q.im)
      simp only [map_add,map_mul,←ha]
      ring
    · change c*f (p.re*q.im+p.im*q.re+b*p.im*q.im)=
        f p.re*(c*f q.im)+(c*f p.im)*f q.re+b'*(c*f p.im)*(c*f q.im)
      simp only [map_add,map_mul,←hb]
      ring

theorem quadraticScale_re {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : S) {a b : R} {a' b' : S}
    (ha : c^2*a'=f a) (hb : c*b'=f b) (q : QuadraticAlgebra R a b) :
    (quadraticScale f c ha hb q).re=f q.re := rfl

theorem quadraticScale_im {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : S) {a b : R} {a' b' : S}
    (ha : c^2*a'=f a) (hb : c*b'=f b) (q : QuadraticAlgebra R a b) :
    (quadraticScale f c ha hb q).im=c*f q.im := rfl

theorem quadraticScale_omega {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : S) {a b : R} {a' b' : S}
    (ha : c^2*a'=f a) (hb : c*b'=f b) :
    quadraticScale f c ha hb QuadraticAlgebra.omega=
      algebraMap S _ c*QuadraticAlgebra.omega := by
  ext <;> simp [quadraticScale]

theorem quadraticScale_scalar {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (c : S) {a b : R} {a' b' : S}
    (ha : c^2*a'=f a) (hb : c*b'=f b) (r : R) :
    quadraticScale f c ha hb (algebraMap R _ r)=algebraMap S _ (f r) := by
  ext <;> simp [quadraticScale]


end
end HTGeometry.ThetaRatioSource.TerminalKinetic
