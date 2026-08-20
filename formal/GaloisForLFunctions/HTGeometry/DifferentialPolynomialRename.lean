import GaloisForLFunctions.HTGeometry.DifferentialSystemSolution

/-!
# Renaming differential variables, and kernels of differential maps

Renaming the differential indeterminates commutes with the total derivation — it moves the jet index
untouched and leaves the coefficients alone — so a system can be transported into a larger variable
set without changing its differential meaning.

The kernel of a differential ring map into a field is a radical differential ideal, which is what
turns a solution of a system into an obstruction to the radical differential ideal it generates
being the whole ring.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {ι κ K : Type*} [CommRing K] [Differential K]

/-- Renaming the differential variables. -/
def differentialRename (f : ι → κ) :
    DifferentialPolynomial ι K →ₐ[K] DifferentialPolynomial κ K :=
  MvPolynomial.rename (fun p : ι × ℕ => (f p.1, p.2))

omit [Differential K] in
@[simp] theorem differentialRename_X (f : ι → κ) (i : ι) (n : ℕ) :
    differentialRename (K := K) f (MvPolynomial.X (i, n)) = MvPolynomial.X (f i, n) := by
  simp [differentialRename]

omit [Differential K] in
@[simp] theorem differentialRename_C (f : ι → κ) (a : K) :
    differentialRename (K := K) f (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [differentialRename]

/-- **Renaming commutes with the total derivation.** -/
theorem differentialRename_deriv (f : ι → κ) (p : DifferentialPolynomial ι K) :
    differentialRename (K := K) f (differentialPolynomialOverDerivation ι K p)
      = differentialPolynomialOverDerivation κ K (differentialRename f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [differentialPolynomialOverDerivation_C, differentialRename_C,
      differentialRename_C, differentialPolynomialOverDerivation_C]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  | mul_X p s hp =>
      obtain ⟨i, n⟩ := s
      have hLp : differentialPolynomialOverDerivation ι K (p * MvPolynomial.X (i, n))
          = p * MvPolynomial.X (i, n + 1)
            + MvPolynomial.X (i, n) * differentialPolynomialOverDerivation ι K p := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, differentialPolynomialOverDerivation_X]
      have hRp : differentialPolynomialOverDerivation κ K
            (differentialRename (K := K) f p * MvPolynomial.X (f i, n))
          = differentialRename (K := K) f p * MvPolynomial.X (f i, n + 1)
            + MvPolynomial.X (f i, n) *
              differentialPolynomialOverDerivation κ K (differentialRename (K := K) f p) := by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, differentialPolynomialOverDerivation_X]
      rw [hLp, map_add, map_mul, map_mul, differentialRename_X, differentialRename_X, hp,
        map_mul, differentialRename_X, hRp]

/-- The kernel of a differential ring map into a field is a radical differential ideal. -/
theorem isRadical_ker_of_field {R L : Type*} [CommRing R] [Differential R] [Field L]
    [Differential L] (f : R →+* L) (hf : ∀ x, f (Differential.deriv x) = Differential.deriv (f x)) :
    (RingHom.ker f).IsRadical ∧ ∀ x ∈ RingHom.ker f, Differential.deriv x ∈ RingHom.ker f := by
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker] at hn ⊢
    have hpow : f x ^ n = 0 := by rw [← map_pow]; exact hn
    exact pow_eq_zero_iff'.mp hpow |>.1
  · intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    rw [hf, hx, map_zero]

end

end GaloisForLFunctions.HTGeometry
