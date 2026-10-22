import GaloisForLFunctions.RHTower.Deninger.DeningerShiftedFiberTotalization
import GaloisForLFunctions.RHTower.Deninger.DeningerArakelovTraceKernel

/-!
# The arithmetic three-term complex and its endpoints

Assembling the shifted residue fibre with the finite-plus-real Arakelov boundary gives the
arithmetic three-term complex: a two-term generic source in degrees zero and one, and the
finite-plus-real boundary object in degree two.  Its cohomology is the kernel of the generic
differential, the residue kernel modulo generic boundaries, and the boundary object modulo the
residue image — and nothing outside those three degrees, because the complex has no other terms.

Because the Arakelov trace is onto with kernel exactly the residue image, the degree-two group is
the real orientation line.

* `deningerArithmeticFiberComplex` : the three-term complex `(9)`.
* `deningerArithmeticFiber_H0_eq`, `_H1_cycles_eq`, `_H2_boundaries_eq` : its cohomology `(11)`.
* `deningerArithmeticFiber_H2Equiv` : the degree-two endpoint is the orientation line.
-/

namespace RHTower

section Assembly

variable {R A0 U C Bval Bpkt : Type*} [CommRing R]
variable [AddCommGroup A0] [Module R A0]
variable [AddCommGroup U] [Module R U] [AddCommGroup C] [Module R C]
variable [AddCommGroup Bval] [Module R Bval] [AddCommGroup Bpkt] [Module R Bpkt]

/-- **The arithmetic three-term complex `(9)`.**  The generic two-term source in degrees zero and
one, and the finite-plus-real boundary object in degree two, with the collar Arakelov boundary as
the residue differential. -/
def deningerArithmeticFiberComplex (dA : A0 →ₗ[R] (U × C)) (ord : U →ₗ[R] Bval)
    (rho : C →ₗ[R] Bpkt) (W : Bval →ₗ[R] R)
    (h : (deningerCollarArakelovBoundary ord rho W).comp dA = 0) :
    DeningerArithmeticThreeTermComplex R A0 (U × C) ((Bval × Bpkt) × R) :=
  deningerShiftedFiberComplex dA (deningerCollarArakelovBoundary ord rho W) h

/-- Degree zero is the kernel of the generic differential. -/
theorem deningerArithmeticFiber_H0_eq (dA : A0 →ₗ[R] (U × C)) (ord : U →ₗ[R] Bval)
    (rho : C →ₗ[R] Bpkt) (W : Bval →ₗ[R] R)
    (h : (deningerCollarArakelovBoundary ord rho W).comp dA = 0) :
    (deningerArithmeticFiberComplex dA ord rho W h).cycles0 = LinearMap.ker dA := rfl

/-- Degree-one cocycles are the residue kernel. -/
theorem deningerArithmeticFiber_H1_cycles_eq (dA : A0 →ₗ[R] (U × C)) (ord : U →ₗ[R] Bval)
    (rho : C →ₗ[R] Bpkt) (W : Bval →ₗ[R] R)
    (h : (deningerCollarArakelovBoundary ord rho W).comp dA = 0) :
    (deningerArithmeticFiberComplex dA ord rho W h).cycles1
      = LinearMap.ker (deningerCollarArakelovBoundary ord rho W) := rfl

/-- Degree-two boundaries are the residue image, so the top group is its cokernel. -/
theorem deningerArithmeticFiber_H2_boundaries_eq (dA : A0 →ₗ[R] (U × C)) (ord : U →ₗ[R] Bval)
    (rho : C →ₗ[R] Bpkt) (W : Bval →ₗ[R] R)
    (h : (deningerCollarArakelovBoundary ord rho W).comp dA = 0) :
    (deningerArithmeticFiberComplex dA ord rho W h).boundaries2
      = LinearMap.range (deningerCollarArakelovBoundary ord rho W) := rfl

/-- **The degree-two endpoint is the orientation line.**  The Arakelov trace is onto with kernel
exactly the residue image, so the top cohomology of the arithmetic three-term complex is `R(-1)`. -/
noncomputable def deningerArithmeticFiber_H2Equiv {dA : A0 →ₗ[R] (U × C)} {ord : U →ₗ[R] Bval}
    {rho : C →ₗ[R] Bpkt} (W : Bval →ₗ[R] R)
    (h : (deningerCollarArakelovBoundary ord rho W).comp dA = 0)
    (hord : Function.Surjective ord) (hrho : Function.Surjective rho) :
    (deningerArithmeticFiberComplex dA ord rho W h).H2 ≃ₗ[R] R :=
  deningerShiftedFiber_H2Equiv_of_trace dA (deningerCollarArakelovBoundary ord rho W) h
    (deningerCollarArakelovTrace (Bpkt := Bpkt) W)
    (deningerCollarArakelovBoundary_exact W hord hrho)
    (deningerCollarArakelovTrace_surjective W)

end Assembly

end RHTower
