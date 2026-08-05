import GaloisForLFunctions.RHTower.AdelicPhaseDefectCharacterBlindnessLaw
import GaloisForLFunctions.RHTower.RouteRKummerCyclicOneCocycleDetector

/-!
# The rational adelic scaling group is defect-blind

The logarithmic Kummer weight `ℓ(q) = log |q|` is additive on the rational adelic scaling group, so
it is a character of that group with values in the additive complex numbers written
multiplicatively.  Scaling it by a complex parameter gives a one-parameter family of characters,
and the family is faithful because the ordinary prime scalings have weight `log p ≠ 0`.

Consequently the character group of the rational adelic scaling group is large, and the general
blindness law applies verbatim: coboundary-defect data on this group cannot detect a character
twist.  Specialising the parameter to `1/2 - Re ρ` gives the source-inverse endpoint residue, whose
triviality is exactly the critical-line condition.  So no criterion formulated at the level of
reciprocity data on the rational adelic source can force `Re ρ = 1/2`; a producer must read the
phase itself, not its defect.
-/

namespace GaloisForLFunctions.RHTower

open scoped Multiplicative

/-- The scaling group of the exact rational adelic crossed product. -/
abbrev AdelicScaling : Type := CCMRationalAdelicScaling

/-- The logarithmic Kummer weight kills the unit scaling. -/
theorem ccmRationalAdelicKummerLogWeight_one :
    RHTower.ccmRationalAdelicKummerLogWeight (1 : AdelicScaling) = 0 := by
  have h := RHTower.ccmRationalAdelicKummerLogWeight_mul (1 : AdelicScaling) 1
  rw [one_mul] at h
  exact left_eq_add.mp h

/-- The `s`-th power character `q ↦ s · log |q|` of the rational adelic scaling group. -/
noncomputable def adelicLogPowerCharacter (s : ℂ) : AdelicScaling →* Multiplicative ℂ where
  toFun k := Multiplicative.ofAdd (s * RHTower.ccmRationalAdelicKummerLogWeight k)
  map_one' := by
    show Multiplicative.ofAdd (s * RHTower.ccmRationalAdelicKummerLogWeight 1) = 1
    rw [ccmRationalAdelicKummerLogWeight_one, mul_zero]
    rfl
  map_mul' k l := by
    show Multiplicative.ofAdd (s * RHTower.ccmRationalAdelicKummerLogWeight (k * l)) = _
    rw [RHTower.ccmRationalAdelicKummerLogWeight_mul, mul_add, ofAdd_add]

@[simp]
theorem adelicLogPowerCharacter_apply (s : ℂ) (k : AdelicScaling) :
    adelicLogPowerCharacter s k =
      Multiplicative.ofAdd (s * RHTower.ccmRationalAdelicKummerLogWeight k) := rfl

/-- The weight of an ordinary prime scaling is nonzero. -/
theorem ccmRationalAdelicKummerLogWeight_primeScaling_ne_zero (p : Nat.Primes) :
    RHTower.ccmRationalAdelicKummerLogWeight (RHTower.ccmRationalAdelicPrimeScaling p) ≠ 0 := by
  rw [RHTower.ccmRationalAdelicKummerLogWeight_primeScaling, Ne, Complex.ofReal_eq_zero]
  exact Real.log_ne_zero_of_pos_of_ne_one
    (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one)

/-- The power characters are faithful in the parameter: the ordinary prime scalings separate
them. -/
theorem adelicLogPowerCharacter_eq_one_iff (s : ℂ) : adelicLogPowerCharacter s = 1 ↔ s = 0 := by
  constructor
  · intro h
    have hp : (2 : ℕ).Prime := Nat.prime_two
    set p : Nat.Primes := ⟨2, hp⟩ with hpdef
    have h1 := congrArg
      (fun f : AdelicScaling →* Multiplicative ℂ =>
        Multiplicative.toAdd (f (RHTower.ccmRationalAdelicPrimeScaling p))) h
    have h2 : s * RHTower.ccmRationalAdelicKummerLogWeight
        (RHTower.ccmRationalAdelicPrimeScaling p) = 0 := h1
    rcases mul_eq_zero.mp h2 with hs | hw
    · exact hs
    · exact absurd hw (ccmRationalAdelicKummerLogWeight_primeScaling_ne_zero p)
  · rintro rfl
    ext k
    simp

/-- Source-inverse endpoint residue of the rational adelic source, `α_ρ(q) = (1/2 - Re ρ)·log|q|`. -/
noncomputable def adelicXiSourceInverseCharacter (ρ : ℂ) : AdelicScaling →* Multiplicative ℂ :=
  adelicLogPowerCharacter ((1 / 2 - ρ.re : ℝ) : ℂ)

/-- Analytic-adjoint endpoint residue, `β_ρ(q) = (Re ρ - 1/2)·log|q|`. -/
noncomputable def adelicXiAnalyticAdjointCharacter (ρ : ℂ) : AdelicScaling →* Multiplicative ℂ :=
  adelicLogPowerCharacter ((ρ.re - 1 / 2 : ℝ) : ℂ)

/-- Triviality of the source-inverse endpoint residue on the rational adelic scaling group is
exactly the critical-line condition. -/
theorem adelicXiSourceInverseCharacter_eq_one_iff (ρ : ℂ) :
    adelicXiSourceInverseCharacter ρ = 1 ↔ ρ.re = 1 / 2 := by
  rw [adelicXiSourceInverseCharacter, adelicLogPowerCharacter_eq_one_iff,
    Complex.ofReal_eq_zero, sub_eq_zero]
  exact eq_comm

/-- **Adelic product formula shadow on the actual source.**  The two endpoint residues are inverse
characters for every spectral parameter, so their product is trivial throughout the critical strip
and carries no information about `Re ρ`. -/
theorem adelicXiSourceInverse_mul_adelicXiAnalyticAdjoint (ρ : ℂ) :
    adelicXiSourceInverseCharacter ρ * adelicXiAnalyticAdjointCharacter ρ = 1 := by
  ext k
  simp only [adelicXiSourceInverseCharacter, adelicXiAnalyticAdjointCharacter,
    MonoidHom.mul_apply, adelicLogPowerCharacter_apply, MonoidHom.one_apply]
  rw [← ofAdd_add, ← add_mul]
  norm_num

/-- Twisting a phase on the rational adelic scaling group by any endpoint residue leaves its
coboundary defect unchanged. -/
theorem phaseDefect_adelicXiSourceInverseCharacter_smul (ρ : ℂ)
    (γ : AdelicScaling → Multiplicative ℂ) :
    phaseDefect (fun k => adelicXiSourceInverseCharacter ρ k * γ k) = phaseDefect γ :=
  phaseDefect_character_smul _ γ

/-- **Route R defect blindness.**  No predicate on coboundary-defect data over the rational adelic
scaling group is equivalent to triviality of the twisting character. -/
theorem not_exists_phaseDefect_criterion_adelicScaling
    (γ : AdelicScaling → Multiplicative ℂ) :
    ¬ ∃ P : (AdelicScaling → AdelicScaling → Multiplicative ℂ) → Prop,
      ∀ χ : AdelicScaling →* Multiplicative ℂ,
        P (phaseDefect fun k => χ k * γ k) ↔ χ = 1 := by
  refine not_exists_phaseDefect_criterion (adelicLogPowerCharacter 1) ?_
  rw [Ne, adelicLogPowerCharacter_eq_one_iff]
  exact one_ne_zero

/-- **Critical-line blindness of the Route R reciprocity layer.**  A criterion that reads only the
coboundary defect of the endpoint-twisted phase on the rational adelic scaling group cannot be
equivalent to `Re ρ = 1/2`.  Reciprocity data — the product of the two endpoint residues, or any
invariant factoring through the defect — is therefore never an RH producer; the comparison must
transport the phase itself. -/
theorem no_phaseDefect_criterion_detects_criticalLine_adelicScaling
    (γ : AdelicScaling → Multiplicative ℂ)
    (P : (AdelicScaling → AdelicScaling → Multiplicative ℂ) → Prop)
    (hP : ∀ ρ : ℂ,
      P (phaseDefect fun k => adelicXiSourceInverseCharacter ρ k * γ k) ↔ ρ.re = 1 / 2) :
    False := by
  have hhalf : P (phaseDefect γ) := by
    have h := (hP (((1 : ℝ) / 2 : ℝ) : ℂ)).mpr (by simp)
    rwa [phaseDefect_adelicXiSourceInverseCharacter_smul] at h
  have hone : ((1 : ℂ)).re = 1 / 2 := by
    refine (hP 1).mp ?_
    rw [phaseDefect_adelicXiSourceInverseCharacter_smul]
    exact hhalf
  rw [Complex.one_re] at hone
  linarith

end GaloisForLFunctions.RHTower
