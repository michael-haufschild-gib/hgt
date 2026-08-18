import GaloisForLFunctions.RHTower.DeningerBigWittFrobeniusRingEndomorphism
import GaloisForLFunctions.RHTower.PrimePowerCenteredMarkRH
import GaloisForLFunctions.RHTower.DeningerEntireQuotientCohomology

/-!
# Big-Witt centered-prime-mark / completed-Xi spectral-fiber comparison

Big-Witt Frobenius acts vertically on the Teichmüller lift of a centered prime mark: it changes
the arithmetic base while retaining the completed-Xi spectral fiber.  The same scalar admits a
horizontal relabeling, but this file does not turn that equality into transport between distinct
completed-Xi fibers.  In particular, every right-half completed-Xi fiber has an injective
Frobenius reporter orbit, ruling out finite preperiodicity as a source mechanism.
-/

open Complex

namespace RHTower

noncomputable section

/-- Nonzero completed-Xi quotient eigenvectors with centered spectral label `alpha`. -/
abbrev CompletedXiThetaSpectralFiber (alpha : ℂ) :=
  {x : DeningerEntireH1 //
    x ≠ 0 ∧
      deningerEntireTheta x =
        (1 / 2 + Complex.I * alpha) • x}

/-- Completed-Xi theta eigenvectors whose associated `s` lies strictly right of `1/2`. -/
abbrev CompletedXiThetaRightSpectralFiber :=
  Σ alpha : {alpha : ℂ //
      1 / 2 < (1 / 2 + Complex.I * alpha).re},
    CompletedXiThetaSpectralFiber alpha.1

/-- Centered prime mark written in the completed-Xi centered spectral coordinate. -/
def completedXiCenteredPrimeMark (p : ℕ) (alpha : ℂ) : ℂ :=
  centeredPrimeMark p (1 / 2 + Complex.I * alpha)

/-- Teichmüller lift of the centered prime mark at a completed-Xi spectral label. -/
def completedXiBigWittPrimeMark (p : ℕ) (alpha : ℂ) :
    DeningerBigWittRing ℂ :=
  deningerBigWittRingTeichmuller (completedXiCenteredPrimeMark p alpha)

/-- Big-Witt reporter on one completed-Xi theta fiber.  It records the fiber label, not vector. -/
def completedXiThetaFiberBigWittReporter
    (p : ℕ) (alpha : ℂ) (_ : CompletedXiThetaSpectralFiber alpha) :
    DeningerBigWittRing ℂ :=
  completedXiBigWittPrimeMark p alpha

/-- Multiplication of the centered completed-Xi spectral label by a natural number. -/
def completedXiSpectralDilation (m : ℕ) (alpha : ℂ) : ℂ :=
  (m : ℂ) * alpha

/-- Explicit Frobenius-two orbit of a centered-prime-mark Teichmüller representative. -/
def completedXiBigWittPrimeMarkOrbit
    (p : ℕ) (alpha : ℂ) (k : ℕ) : DeningerBigWittRing ℂ :=
  deningerBigWittRingTeichmuller
    (completedXiCenteredPrimeMark p alpha ^ (2 ^ k))

/-- Completed-Xi theta fibers are inhabited exactly at zeros of the completed source. -/
theorem nonempty_completedXiThetaSpectralFiber_iff
    (alpha : ℂ) :
    Nonempty (CompletedXiThetaSpectralFiber alpha) ↔ XiC alpha = 0 := by
  constructor
  · rintro ⟨x⟩
    exact (XiC_eq_zero_iff_exists_deningerEntireTheta_eigenvector alpha).mpr
      ⟨x.1, x.2.1, x.2.2⟩
  · intro hXi
    obtain ⟨x, hx0, hx⟩ :=
      (XiC_eq_zero_iff_exists_deningerEntireTheta_eigenvector alpha).mp hXi
    exact ⟨⟨x, hx0, hx⟩⟩

/-- The scalar reporter cannot distinguish base Adams from centered spectral dilation. -/
theorem completedXiCenteredPrimeMark_spectralDilation
    (p m : ℕ) (alpha : ℂ) :
    completedXiCenteredPrimeMark p (completedXiSpectralDilation m alpha) =
      completedXiCenteredPrimeMark p alpha ^ m := by
  rw [completedXiCenteredPrimeMark, completedXiCenteredPrimeMark,
    completedXiSpectralDilation, centeredPrimeMark, centeredPrimeMark]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The orbit starts at the original centered-prime-mark reporter. -/
@[simp] theorem completedXiBigWittPrimeMarkOrbit_zero
    (p : ℕ) (alpha : ℂ) :
    completedXiBigWittPrimeMarkOrbit p alpha 0 =
      completedXiBigWittPrimeMark p alpha := by
  simp [completedXiBigWittPrimeMarkOrbit, completedXiBigWittPrimeMark]

/-- Frobenius two advances the explicit orbit by one step. -/
theorem deningerBigWittFrobeniusTwo_completedXiPrimeMarkOrbit
    (p : ℕ) (alpha : ℂ) (k : ℕ) :
    deningerBigWittFrobeniusTwoRingHom
        (completedXiBigWittPrimeMarkOrbit p alpha k) =
      completedXiBigWittPrimeMarkOrbit p alpha (k + 1) := by
  simp [completedXiBigWittPrimeMarkOrbit, pow_succ, pow_mul]

/-- The actual Frobenius orbit is arithmetic base change at fixed completed-Xi fiber label. -/
theorem completedXiBigWittPrimeMarkOrbit_eq_basePower
    (p : ℕ) (alpha : ℂ) (k : ℕ) :
    completedXiBigWittPrimeMarkOrbit p alpha k =
      completedXiBigWittPrimeMark (p ^ (2 ^ k)) alpha := by
  change
    deningerBigWittRingTeichmuller
        (centeredPrimeMark p (1 / 2 + Complex.I * alpha) ^ (2 ^ k)) =
      deningerBigWittRingTeichmuller
        (centeredPrimeMark (p ^ (2 ^ k))
          (1 / 2 + Complex.I * alpha))
  rw [centeredPrimeMark_primePower]

/-- The same scalar can be relabeled horizontally, without constructing the relabeled Xi fiber. -/
theorem completedXiBigWittPrimeMarkOrbit_eq_spectralDilation
    (p : ℕ) (alpha : ℂ) (k : ℕ) :
    completedXiBigWittPrimeMarkOrbit p alpha k =
      completedXiBigWittPrimeMark p
        (completedXiSpectralDilation (2 ^ k) alpha) := by
  rw [completedXiBigWittPrimeMarkOrbit, completedXiBigWittPrimeMark,
    completedXiCenteredPrimeMark_spectralDilation]

/-- On an existing completed-Xi fiber, Frobenius is same-fiber base change, not fiber transport. -/
theorem deningerBigWittFrobeniusTwo_completedXiThetaFiberReporter
    (p : ℕ) (alpha : ℂ) (x : CompletedXiThetaSpectralFiber alpha) :
    deningerBigWittFrobeniusTwoRingHom
        (completedXiThetaFiberBigWittReporter p alpha x) =
      completedXiThetaFiberBigWittReporter (p ^ 2) alpha x := by
  simp [completedXiThetaFiberBigWittReporter, completedXiBigWittPrimeMark,
    completedXiCenteredPrimeMark, centeredPrimeMark_primePower]

/-- Every hypothetical right-half completed-Xi spectral fiber has an injective Frobenius orbit. -/
theorem completedXiRightSpectralFiber_bigWittPrimeMarkOrbit_injective :
    ∀ e : CompletedXiThetaRightSpectralFiber,
      Function.Injective
        (fun k => completedXiBigWittPrimeMarkOrbit 2 e.1.1 k) := by
  intro e a b hab
  have hteich :
      deningerBigWittRingTeichmuller
          (completedXiCenteredPrimeMark 2 e.1.1 ^ (2 ^ a)) =
        deningerBigWittRingTeichmuller
          (completedXiCenteredPrimeMark 2 e.1.1 ^ (2 ^ b)) := by
    simpa only [completedXiBigWittPrimeMarkOrbit] using hab
  have hpowers :
      completedXiCenteredPrimeMark 2 e.1.1 ^ (2 ^ a) =
        completedXiCenteredPrimeMark 2 e.1.1 ^ (2 ^ b) :=
    (deningerBigWittRingTeichmuller_injective (A := ℂ)) hteich
  have hnorm :
      ‖completedXiCenteredPrimeMark 2 e.1.1‖ ^ (2 ^ a) =
        ‖completedXiCenteredPrimeMark 2 e.1.1‖ ^ (2 ^ b) := by
    simpa only [norm_pow] using congrArg norm hpowers
  have hcontract : ‖completedXiCenteredPrimeMark 2 e.1.1‖ < 1 := by
    rw [completedXiCenteredPrimeMark]
    exact (centeredPrimeMark_norm_lt_one_iff (p := 2) (by omega)
      (1 / 2 + Complex.I * e.1.1)).mpr e.1.2
  have hmark0 : completedXiCenteredPrimeMark 2 e.1.1 ≠ 0 := by
    rw [completedXiCenteredPrimeMark, centeredPrimeMark]
    exact Complex.exp_ne_zero _
  have hexponents : 2 ^ a = 2 ^ b :=
    pow_right_injective₀ (norm_pos_iff.mpr hmark0) (ne_of_lt hcontract) hnorm
  exact Nat.pow_right_injective le_rfl hexponents

/-- No finite Frobenius preperiodicity can occur on a right-half completed-Xi spectral fiber. -/
theorem no_completedXiRightSpectralFiber_bigWittPrimeMarkOrbit_preperiodic :
    ∀ e : CompletedXiThetaRightSpectralFiber,
      ¬ ∃ a b : ℕ, a < b ∧
        completedXiBigWittPrimeMarkOrbit 2 e.1.1 a =
          completedXiBigWittPrimeMarkOrbit 2 e.1.1 b := by
  intro e
  rintro ⟨a, b, hab, horbit⟩
  exact (ne_of_lt hab)
    (completedXiRightSpectralFiber_bigWittPrimeMarkOrbit_injective e horbit)

/-- Closed comparison capstone: receiver classification, verticality, and right-half no-go. -/
theorem deningerBigWitt_centeredPrimeMark_completedXiSpectralFiberComparison :
    (∀ alpha : ℂ,
      Nonempty (CompletedXiThetaSpectralFiber alpha) ↔ XiC alpha = 0) ∧
    (∀ p : ℕ, ∀ alpha : ℂ, ∀ x : CompletedXiThetaSpectralFiber alpha,
      deningerBigWittFrobeniusTwoRingHom
          (completedXiThetaFiberBigWittReporter p alpha x) =
        completedXiThetaFiberBigWittReporter (p ^ 2) alpha x) ∧
    (∀ p : ℕ, ∀ alpha : ℂ, ∀ k : ℕ,
      deningerBigWittFrobeniusTwoRingHom
          (completedXiBigWittPrimeMarkOrbit p alpha k) =
          completedXiBigWittPrimeMarkOrbit p alpha (k + 1) ∧
      completedXiBigWittPrimeMarkOrbit p alpha k =
          completedXiBigWittPrimeMark (p ^ (2 ^ k)) alpha ∧
      completedXiBigWittPrimeMarkOrbit p alpha k =
          completedXiBigWittPrimeMark p
            (completedXiSpectralDilation (2 ^ k) alpha)) ∧
    (∀ e : CompletedXiThetaRightSpectralFiber,
      Function.Injective
        (fun k => completedXiBigWittPrimeMarkOrbit 2 e.1.1 k)) := by
  refine ⟨nonempty_completedXiThetaSpectralFiber_iff,
    deningerBigWittFrobeniusTwo_completedXiThetaFiberReporter, ?_,
    completedXiRightSpectralFiber_bigWittPrimeMarkOrbit_injective⟩
  intro p alpha k
  exact ⟨deningerBigWittFrobeniusTwo_completedXiPrimeMarkOrbit p alpha k,
    completedXiBigWittPrimeMarkOrbit_eq_basePower p alpha k,
    completedXiBigWittPrimeMarkOrbit_eq_spectralDilation p alpha k⟩

end

end RHTower
