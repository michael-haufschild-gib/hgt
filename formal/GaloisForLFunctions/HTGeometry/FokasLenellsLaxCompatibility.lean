import GaloisForLFunctions.HTGeometry.FokasLenellsUniformization

/-!
# The Fokas–Lenells compatibility factorization

The algebra in equations (5.38)–(5.39) and Corollary 5.6 of
Yan–Zhang–Zhu, arXiv:2607.19649v1. Both the polynomial identity with
cleared denominators and the original rational identity are proved.
Exponential spectral coordinates discharge the nonzero denominator condition.

Derivative slots are independent complex coordinates in this module. These
identities isolate the scalar PDE from a flat Lax connection; they do not
assert existence of a reconstructed potential or its differentiability.
-/

open Complex Matrix
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def grading : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
def offDiagonal (p q : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0,p;q,0]

def clearedTemporalLax (p q k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-I) • grading + (2*k) • (offDiagonal p q * grading) +
    (2*I*k^(2 : ℕ)) • (offDiagonal p q ^ (2 : ℕ) * grading)

def clearedTemporalDerivative (p q u v k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (2*k) • (offDiagonal v u * grading) +
    (2*I*k^(2 : ℕ)) • ((offDiagonal v u * offDiagonal p q +
      offDiagonal p q * offDiagonal v u) * grading)

def clearedCurvature (p q u v pt qt k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (4*I*k^(3 : ℕ)) • offDiagonal pt qt - clearedTemporalDerivative p q u v k +
    spatialLax u v k * clearedTemporalLax p q k -
    clearedTemporalLax p q k * spatialLax u v k

/-- Equation (5.38), after multiplying through by 4 k², including the singular point. -/
theorem clearedCurvature_factor (p q u v pt qt k : ℂ) :
    clearedCurvature p q u v pt qt k =
      (4*I*k^(3 : ℕ)) • offDiagonal (pt-p-I*p*q*v) (qt-q+I*p*q*u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [clearedCurvature, clearedTemporalDerivative, clearedTemporalLax,
      spatialLax, grading, offDiagonal, pow_two] <;>
    ring_nf <;> simp <;> ring

/-- Compatibility for every spectral parameter is exactly the pair of scalar equations. -/
theorem clearedCurvature_zero_iff (p q u v pt qt : ℂ) :
    (∀ k : ℂ, clearedCurvature p q u v pt qt k = 0) ↔
      pt-p-I*p*q*v = 0 ∧ qt-q+I*p*q*u = 0 := by
  simp only [clearedCurvature_factor]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (h 1)
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) (h 1)
    simpa [offDiagonal] using And.intro h01 h10
  · rintro ⟨hp,hq⟩ k
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp,hq,offDiagonal]

def temporalLax (p q k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (-I/(4*k^(2 : ℕ))) • grading + (1/(2*k)) • (offDiagonal p q * grading) +
    (I/2) • (offDiagonal p q ^ (2 : ℕ) * grading)

def temporalDerivative (p q u v k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1/(2*k)) • (offDiagonal v u * grading) +
    (I/2) • ((offDiagonal v u * offDiagonal p q +
      offDiagonal p q * offDiagonal v u) * grading)

def curvature (p q u v pt qt k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (I*k) • offDiagonal pt qt - temporalDerivative p q u v k +
    spatialLax u v k * temporalLax p q k -
    temporalLax p q k * spatialLax u v k

/-- The original, uncleared Lax curvature at every exponential spectral parameter.
The parametrization discharges the paper's nonzero-spectral-parameter condition. -/
theorem curvature_exp_factor (p q u v pt qt a : ℂ) :
    curvature p q u v pt qt (Complex.exp a) =
      (I*Complex.exp a) • offDiagonal (pt-p-I*p*q*v) (qt-q+I*p*q*u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvature, temporalDerivative, temporalLax,
      spatialLax, grading, offDiagonal, pow_two] <;>
    field_simp <;> ring_nf <;> simp

theorem curvature_exp_zero_iff (p q u v pt qt a : ℂ) :
    curvature p q u v pt qt (Complex.exp a) = 0 ↔
      pt-p-I*p*q*v = 0 ∧ qt-q+I*p*q*u = 0 := by
  rw [curvature_exp_factor]
  constructor
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
    simpa [offDiagonal, Complex.exp_ne_zero] using And.intro h01 h10
  · rintro ⟨hp,hq⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp,hq,offDiagonal]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
