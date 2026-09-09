import GaloisForLFunctions.HTGeometry.GomesFockObservationFrameGeometry

/-!
Scalar observation kernels in the existing free-Fock moment corpus. This applies
the invariant-menu and diagonal-kernel reconstruction mechanism of Gomes,
arXiv:2607.24901v1, Section 4.3, to a complete infinite sequence of observations.
The source's existing scalar homogeneity is reused. Zeroth mass makes the
ambiguity exact, including zero observing vectors and empty internal carriers.
-/
open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Zero observing vectors produce the zero moment sequence, for arbitrary matrix data. -/
theorem gomesFock_zeroVector_moment {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (n : ℕ) :
    freeFockVectorMoment A 0 n = 0 := by
  have h := freeFockVectorMoment_smul A (0 : ℂ) (0 : Fin d → ℂ) n
  simpa using h

/-- Initial observation mass vanishes exactly at the zero observing vector. -/
theorem gomesFockVector_mass_zero_iff {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) :
    freeFockVectorMoment A x 0 = 0 ↔ x = 0 := by
  rw [freeFockVectorMoment_zero,
    Finset.sum_eq_zero_iff_of_nonneg (fun i hi => Complex.normSq_nonneg (x i))]
  simp [funext_iff]

/-- The complete scalar-orbit moment record distinguishes exactly squared amplitude, unless the source vector is zero. -/
theorem gomesFockScalar_moments_eq_iff {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c e : ℂ) :
    (∀ n, freeFockVectorMoment A (c • x) n = freeFockVectorMoment A (e • x) n) ↔
      Complex.normSq c = Complex.normSq e ∨ x = 0 := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inr hx
    · left
      have h0 := h 0
      rw [freeFockVectorMoment_smul,freeFockVectorMoment_smul] at h0
      exact mul_right_cancel₀ (fun hz => hx ((gomesFockVector_mass_zero_iff A x).mp hz)) h0
  · rintro (hc|rfl) n
    · simp only [freeFockVectorMoment_smul,hc]
    · simp [gomesFock_zeroVector_moment]

/-- Every higher scalar-orbit moment contains no additional scalar information beyond the initial mass. -/
theorem gomesFockScalar_record_eq_iff_mass_eq {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c e : ℂ) :
    (∀ n, freeFockVectorMoment A (c • x) n = freeFockVectorMoment A (e • x) n) ↔
      freeFockVectorMoment A (c • x) 0 = freeFockVectorMoment A (e • x) 0 := by
  constructor
  · exact fun h => h 0
  · intro h
    apply (gomesFockScalar_moments_eq_iff A x c e).mpr
    rw [freeFockVectorMoment_smul,freeFockVectorMoment_smul] at h
    by_cases hx : x = 0
    · exact Or.inr hx
    · exact Or.inl (mul_right_cancel₀ (fun hz => hx ((gomesFockVector_mass_zero_iff A x).mp hz)) h)

/-- The complete moment record has precisely the unit-circle scalar stabilizer at every nonzero state. -/
theorem gomesFockScalar_moment_stabilizer {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) (c : ℂ) :
    (∀ n, freeFockVectorMoment A (c • x) n = freeFockVectorMoment A x n) ↔
      Complex.normSq c = 1 ∨ x = 0 := by
  simpa using gomesFockScalar_moments_eq_iff A x c 1

/-- All vector-state moment observations reconstruct exactly the unit-circle scalar subgroup. -/
theorem gomesFockScalar_global_stabilizer {d k : ℕ}
    (A : Option (Fin k) → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (c : ℂ) :
    (∀ x : Fin (d+1) → ℂ, ∀ n, freeFockVectorMoment A (c • x) n = freeFockVectorMoment A x n) ↔
      Complex.normSq c = 1 := by
  constructor
  · intro h
    have hx : (Pi.single 0 1 : Fin (d+1) → ℂ) ≠ 0 := by
      intro he
      have h0 := congrFun he 0
      simp at h0
    exact ((gomesFockScalar_moment_stabilizer A _ c).mp (h _)).resolve_right hx
  · intro hc x
    exact (gomesFockScalar_moment_stabilizer A x c).mpr (Or.inl hc)

end GaloisForLFunctions.HTGeometry
