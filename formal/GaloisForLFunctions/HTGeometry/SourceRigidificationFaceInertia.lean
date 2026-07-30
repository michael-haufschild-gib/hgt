import GaloisForLFunctions.HTGeometry.DifferenceDifferential
import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# Source rigidification and face-created gauge inertia

A source boundary forgets exactly its joint-fixed gauge.  This file first proves the corresponding
data-processing theorem: adjoining any family of reporters that factors through that same boundary
does not refine a single fibre and is injective exactly when the bare boundary was already
injective.

The positive source-face theorem is analytic rather than merely formal.  Period-one Fourier modes
are linearly independent.  If a second translation has nonzero imaginary part, every positive mode
fails to be fixed by it.  Deleting that second translation therefore creates boundary-only gauge
packets of every finite rank.  Thus degeneration can create arbitrarily large normalization inertia
even though source-only postprocessing can never see the inertia already forgotten by a fixed
source.

These theorems are the exact algebraic and analytic seed for the conjectural failure of source
rigidification to commute with source-face specialization.  They do not themselves construct a
nearby-cycle object or prove a classification theorem for hypertranscendental constraints.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-! ## Source-only reporters have no reconstruction gain -/

/-- The additive source boundary as a bundled homomorphism. -/
def CommutingDifferenceDifferentialField.boundaryFingerprintHom
    {ι C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    (S : CommutingDifferenceDifferentialField ι C K) : K →+ (ι → K) where
  toFun := S.boundaryFingerprint
  map_zero' := by
    funext i
    simp [CommutingDifferenceDifferentialField.boundaryFingerprint,
      CommutingDifferenceDifferentialField.defect]
  map_add' x y := by
    funext i
    exact S.defect_add i x y

/-- A reporter family obtained solely by postprocessing the complete source boundary. -/
def CommutingDifferenceDifferentialField.sourceFactorizedRealization
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (post : ρ → (ι → K) →+ A) : ρ → K →+ A :=
  fun r => (post r).comp S.boundaryFingerprintHom

/-- The bare source boundary augmented by an arbitrary source-factorized reporter family. -/
def CommutingDifferenceDifferentialField.sourceFactorizedBoundaryFingerprint
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (post : ρ → (ι → K) →+ A) (x : K) : (ι → K) × (ρ → A) :=
  (S.boundaryFingerprint x, fun r => S.sourceFactorizedRealization post r x)

/-- Every source-factorized reporter annihilates the joint-fixed gauge. -/
theorem CommutingDifferenceDifferentialField.sourceFactorizedRealization_eq_zero_of_jointFixed
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (post : ρ → (ι → K) →+ A) (z : K) (hz : JointFixed S z) (r : ρ) :
    S.sourceFactorizedRealization post r z = 0 := by
  change post r (S.boundaryFingerprintHom z) = 0
  rw [show S.boundaryFingerprintHom z = 0 by
    funext i
    exact S.defect_eq_zero_of_jointFixed hz i]
  exact map_zero (post r)

/-- **Exact source-data-processing law.**  Adding an arbitrary family of reporters which factors
through the source boundary leaves the source-boundary fibre relation unchanged. -/
theorem CommutingDifferenceDifferentialField.familySourceFactorizedBoundaryFingerprint_eq_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (post : ρ → (ι → K) →+ A) (x y : K) :
    S.sourceFactorizedBoundaryFingerprint post x =
        S.sourceFactorizedBoundaryFingerprint post y ↔
      JointFixed S (x - y) := by
  constructor
  · intro h
    apply S.boundaryFingerprint_eq_iff_sub_jointFixed x y |>.mp
    exact congrArg Prod.fst h
  · intro hfixed
    have hboundary : S.boundaryFingerprint x = S.boundaryFingerprint y :=
      (S.boundaryFingerprint_eq_iff_sub_jointFixed x y).mpr hfixed
    apply Prod.ext hboundary
    funext r
    change post r (S.boundaryFingerprint x) = post r (S.boundaryFingerprint y)
    rw [hboundary]

/-- Source-only postprocessing is conservative exactly when the bare source boundary already was:
no number of source-factorized reporters can improve reconstruction. -/
theorem CommutingDifferenceDifferentialField.familySourceFactorizedBoundaryFingerprint_injective_iff
    {ι ρ C K A : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
    [AddCommGroup A]
    (S : CommutingDifferenceDifferentialField ι C K)
    (post : ρ → (ι → K) →+ A) :
    Function.Injective
        (S.sourceFactorizedBoundaryFingerprint post) ↔
      Function.Injective S.boundaryFingerprint := by
  constructor
  · intro hsource x y hxy
    apply hsource
    apply S.familySourceFactorizedBoundaryFingerprint_eq_iff post x y |>.mpr
    exact (S.boundaryFingerprint_eq_iff_sub_jointFixed x y).mp hxy
  · intro hboundary x y hxy
    apply hboundary
    apply S.boundaryFingerprint_eq_iff_sub_jointFixed x y |>.mpr
    exact (S.familySourceFactorizedBoundaryFingerprint_eq_iff post x y).mp hxy

namespace HTGeometry

/-! ## A source face creates arbitrarily large gauge packets -/

/-- A period-one Fourier mode is an eigenfunction of translation by an arbitrary complex shift. -/
theorem gammaPeriodicMode_add_eigen
    (m : ℕ) (τ z : ℂ) :
    gammaPeriodicMode m (z + τ) =
      (Complex.exp (2 * Real.pi * Complex.I * τ)) ^ m * gammaPeriodicMode m z := by
  rw [gammaPeriodicMode, mul_add, Complex.exp_add, gammaPeriodicMode]
  have harg : gammaPeriodicFrequency m * τ =
      (m : ℂ) * (2 * Real.pi * Complex.I * τ) := by
    simp [gammaPeriodicFrequency]
    ring
  rw [harg, Complex.exp_nat_mul]
  ring

/-- For a nonreal shift, its translation eigenvalue has no positive power equal to one. -/
theorem two_pi_I_exponential_pow_ne_one_of_im_ne_zero
    (τ : ℂ) (hτ : τ.im ≠ 0) (m : ℕ) (hm : 0 < m) :
    (Complex.exp (2 * Real.pi * Complex.I * τ)) ^ m ≠ 1 := by
  rw [← Complex.exp_nat_mul]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2pii : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hmτ : (m : ℂ) * τ = (n : ℂ) := by
    have h' : ((m : ℂ) * τ) * (2 * Real.pi * Complex.I) =
        (n : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination hn
    exact mul_right_cancel₀ h2pii h'
  have him := congrArg Complex.im hmτ
  norm_num [Complex.mul_im] at him
  exact hτ (him.resolve_left hm.ne')

/-- Every positive period-one Fourier mode is removed by a second nonreal source translation. -/
theorem gammaPeriodicMode_not_periodic_of_im_ne_zero
    (τ : ℂ) (hτ : τ.im ≠ 0) (m : ℕ) (hm : 0 < m) :
    ¬ Function.Periodic (gammaPeriodicMode m) τ := by
  intro hperiodic
  have hzero := hperiodic 0
  rw [gammaPeriodicMode_add_eigen] at hzero
  simp [gammaPeriodicMode] at hzero
  exact two_pi_I_exponential_pow_ne_one_of_im_ne_zero τ hτ m hm hzero

/-- Positive period-one Fourier modes of any prescribed finite rank are linearly independent. -/
theorem gammaPositivePeriodicModes_linearIndependent (k : ℕ) :
    LinearIndependent ℂ (fun m : Fin k => gammaPeriodicMode ((m : ℕ) + 1)) := by
  change LinearIndependent ℂ (fun m : Fin k =>
    fun z : ℂ => Complex.exp (gammaPeriodicFrequency m.succ * z))
  exact HurwitzExp.expLin_linearIndependent
    (gammaPeriodicFrequency_fin_injective.comp (Fin.succ_injective k))

/-- A finite packet in the positive period-one Fourier modes. -/
def gammaPositivePeriodicFourierPacket {k : ℕ} (a : Fin k → ℂ) (z : ℂ) : ℂ :=
  ∑ m : Fin k, a m * gammaPeriodicMode ((m : ℕ) + 1) z

/-- Every positive Fourier packet is a gauge for the surviving unit translation. -/
theorem gammaPositivePeriodicFourierPacket_periodic {k : ℕ} (a : Fin k → ℂ) :
    Function.Periodic (gammaPositivePeriodicFourierPacket a) 1 := by
  intro z
  simp [gammaPositivePeriodicFourierPacket]

/-- A nonzero positive Fourier packet cannot also be fixed by a deleted nonreal translation.
Thus the entire finite packet space, not only its displayed basis, is newly created face inertia. -/
theorem gammaPositivePeriodicFourierPacket_not_periodic_of_im_ne_zero
    {k : ℕ} (a : Fin k → ℂ) (ha : a ≠ 0) (τ : ℂ) (hτ : τ.im ≠ 0) :
    ¬ Function.Periodic (gammaPositivePeriodicFourierPacket a) τ := by
  intro hperiodic
  let eigenvalue : ℂ := Complex.exp (2 * Real.pi * Complex.I * τ)
  let c : Fin k → ℂ := fun m => (eigenvalue ^ ((m : ℕ) + 1) - 1) * a m
  have hsum : ∑ m : Fin k,
      c m • gammaPeriodicMode ((m : ℕ) + 1) = 0 := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hz := hperiodic z
    simp only [gammaPositivePeriodicFourierPacket] at hz
    simp_rw [gammaPeriodicMode_add_eigen] at hz
    simp only [c, eigenvalue]
    calc
      ∑ m : Fin k,
          (Complex.exp (2 * Real.pi * Complex.I * τ) ^ ((m : ℕ) + 1) - 1) *
            a m * gammaPeriodicMode ((m : ℕ) + 1) z =
          (∑ m : Fin k, a m *
              (Complex.exp (2 * Real.pi * Complex.I * τ) ^ ((m : ℕ) + 1) *
                gammaPeriodicMode ((m : ℕ) + 1) z)) -
            ∑ m : Fin k, a m * gammaPeriodicMode ((m : ℕ) + 1) z := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro m _
              ring
      _ = 0 := sub_eq_zero.mpr (by simpa [mul_assoc] using hz)
  have hc : ∀ m, c m = 0 :=
    (Fintype.linearIndependent_iff.mp (gammaPositivePeriodicModes_linearIndependent k)) c hsum
  apply ha
  funext m
  have hm := hc m
  exact (mul_eq_zero.mp hm).resolve_left
    (sub_ne_zero.mpr
      (two_pi_I_exponential_pow_ne_one_of_im_ne_zero τ hτ ((m : ℕ) + 1) (by omega)))

/-- **Arbitrary-rank source-face gauge birth.**  For every finite rank `k`, deleting a nonreal
second translation creates `k` linearly independent gauges: all are fixed by the surviving unit
translation, and none was fixed by the deleted translation. -/
theorem nonreal_sourceFace_arbitraryPositiveGaugeBirth
    (τ : ℂ) (hτ : τ.im ≠ 0) (k : ℕ) :
    LinearIndependent ℂ (fun m : Fin k => gammaPeriodicMode ((m : ℕ) + 1)) ∧
      ∀ m : Fin k,
        Function.Periodic (gammaPeriodicMode ((m : ℕ) + 1)) 1 ∧
          ¬ Function.Periodic (gammaPeriodicMode ((m : ℕ) + 1)) τ := by
  refine ⟨gammaPositivePeriodicModes_linearIndependent k, ?_⟩
  intro m
  exact ⟨gammaPeriodicMode_periodic ((m : ℕ) + 1),
    gammaPeriodicMode_not_periodic_of_im_ne_zero τ hτ ((m : ℕ) + 1) (by omega)⟩

end HTGeometry

end

end GaloisForLFunctions
