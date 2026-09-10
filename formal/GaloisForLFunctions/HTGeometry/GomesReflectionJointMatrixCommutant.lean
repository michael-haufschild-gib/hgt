import GaloisForLFunctions.HTGeometry.GomesPolynomialReflectionMatrix
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Joint reflection and differentiation symmetries

The full second-derivative symmetry algebra is a formal matrix algebra. Requiring
commutation with both first differentiation and any affine reflection reduces it
to scalar matrices. This boundary holds for every reflection center.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable (K : Type*) [Field K] [CharZero K]

/-- Exact coefficients of the compressed even exponential. -/
theorem gomesFormalEvenExponential_coeff (c : K) (n : ℕ) :
    PowerSeries.coeff n (gomesFormalEvenExponential K c) =
      c ^ (n * 2) * ((n * 2).factorial : K)⁻¹ := by
  simp [gomesFormalEvenExponential, gomesFormalCoefficientResidue,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

/-- Exact coefficients of the compressed odd exponential. -/
theorem gomesFormalOddExponential_coeff (c : K) (n : ℕ) :
    PowerSeries.coeff n (gomesFormalOddExponential K c) =
      c ^ (n * 2 + 1) * ((n * 2 + 1).factorial : K)⁻¹ := by
  simp [gomesFormalOddExponential, gomesFormalCoefficientResidue,
    PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

/-- The compressed even exponential is nonzero at every center, including zero. -/
theorem gomesFormalEvenExponential_ne_zero (c : K) :
    gomesFormalEvenExponential K c ≠ 0 := by
  intro h
  have h0 := congrArg (PowerSeries.coeff 0) h
  rw [gomesFormalEvenExponential_coeff] at h0
  simp at h0

/-- The full joint matrix commutant of differentiation and every affine reflection is scalar. -/
theorem gomesDerivativeReflectionMatrix_joint_commutant
    (c : K) (M : Matrix (Fin 2) (Fin 2) (PowerSeries K)) :
    (Commute M (gomesEvenOddDerivativeMatrix K) ∧ Commute M (gomesPolynomialReflectionMatrix K c)) ↔
      ∃ F : PowerSeries K, M = Matrix.scalar (Fin 2) F := by
  constructor
  · rintro ⟨hD, hR⟩
    obtain ⟨h10, h11⟩ := (gomesEvenOddDerivativeMatrix_commutes_iff K M).mp hD
    have h01 := congrArg (fun N : Matrix (Fin 2) (Fin 2) (PowerSeries K) => N 0 1) hR.eq
    rw [gomesPolynomialReflectionMatrix_eq] at h01
    simp [Matrix.mul_apply, Fin.sum_univ_two, h11] at h01
    have hprod : (2 : PowerSeries K) * M 0 1 * gomesFormalEvenExponential K c = 0 := by
      linear_combination -h01
    have htwo : (2 : PowerSeries K) ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff : PowerSeries K →+* K) h
      have hk : (2 : K) = 0 := by simpa only [map_ofNat, map_zero] using hc
      exact two_ne_zero hk
    have hb : M 0 1 = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right
        (gomesFormalEvenExponential_ne_zero K c))).resolve_left htwo
    refine ⟨M 0 0, ?_⟩
    apply Matrix.ext
    intro i j
    revert i j
    simp [Fin.forall_fin_two, Matrix.scalar_apply, h10, h11, hb]
  · rintro ⟨F, rfl⟩
    exact ⟨Matrix.scalar_commute F (Commute.all F) _, Matrix.scalar_commute F (Commute.all F) _⟩

end GaloisForLFunctions.HTGeometry
