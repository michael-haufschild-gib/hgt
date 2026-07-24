import GaloisForLFunctions.HTGeometry.ClockEigenvaluePow
import GaloisForLFunctions.HTGeometry.JetScalingClockField
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# A field clock eigenvalue is a ratio of monomials

Extending the ring eigenvalue law (`clock_eigenvalue_pow`) to the fraction field `C⟨y⟩`.  A field clock
eigenvector `x` — a nonzero element with `ρ_λ(x) = χ(λ)·x` for all nonzero `λ` — written in lowest
terms `x = a/b` has numerator and denominator that are *themselves* ring clock eigenvectors: relative
primality forces `a ∣ ρ_λ(a)`, and the clock's invertibility (`ρ_λ ∘ ρ_{λ⁻¹} = id`) forces the reverse
divisibility, so `a` and `ρ_λ(a)` are associates and differ by a constant.  Hence `ρ_λ(a) = λ^{k_a}·a`
and `ρ_λ(b) = λ^{k_b}·b`, and the eigenvalue is their ratio: `χ(λ)·λ^{k_b} = λ^{k_a}`.

This is the field-level algebraicity of the concrete jet-scaling cocharacter: every field clock
eigenvalue is the integer power `λ^{k_a−k_b}`.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {C : Type*} [Field C]

/-- In `C⟨y⟩` over a field, associated polynomials differ by a constant factor. -/
theorem differentialPolynomial_associated_C_mul
    {p q : DifferentialPolynomial Unit C} (h : Associated p q) :
    ∃ r : C, q = MvPolynomial.C r * p := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨r, _, hr⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp u.isUnit
  exact ⟨r, by rw [← hu, hr]; ring⟩

/-- If `ρ_λ(p) = c(λ)·p` for a constant `c(λ)` (for all nonzero `λ`, `p ≠ 0`), the constant is a
monomial: `c(λ) = λ^k`, where `k` is the jet-weight of any monomial of `p`. -/
theorem clock_projective_eigenvalue_pow
    {p : DifferentialPolynomial Unit C} (hp0 : p ≠ 0)
    (h : ∀ lam : C, lam ≠ 0 → ∃ r : C, clockDilationAlgHom lam p = MvPolynomial.C r * p) :
    ∃ k : ℕ, ∀ lam : C, lam ≠ 0 → clockDilationAlgHom lam p = MvPolynomial.C (lam ^ k) * p := by
  obtain ⟨s₀, hs₀⟩ := MvPolynomial.support_nonempty.mpr hp0
  have hc0 : p.coeff s₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hs₀
  refine ⟨Finsupp.weight (fun r : Unit × ℕ => r.2) s₀, fun lam hlam => ?_⟩
  obtain ⟨r, hr⟩ := h lam hlam
  have hco := congrArg (MvPolynomial.coeff s₀) hr
  rw [clockDilationAlgHom_coeff, MvPolynomial.coeff_C_mul] at hco
  have hr_eq : r = lam ^ (Finsupp.weight (fun r : Unit × ℕ => r.2) s₀) :=
    (mul_right_cancel₀ hc0 hco).symm
  rw [hr, hr_eq]

/-- **A field clock eigenvalue is a ratio of monomials.**  If a nonzero `x ∈ C⟨y⟩` satisfies
`ρ_λ(x) = χ(λ)·x` for all nonzero `λ`, then `χ(λ)·λ^{k_b} = λ^{k_a}` for fixed naturals `k_a, k_b`. -/
theorem clock_field_eigenvalue_pow
    {x : ScalarDifferentialField C} (hx0 : x ≠ 0) {χ : C → C}
    (heig : ∀ lam : C, (hlam : lam ≠ 0) →
      clockDilationFieldEquiv lam hlam x
        = algebraMap C (ScalarDifferentialField C) (χ lam) * x) :
    ∃ ka kb : ℕ, ∀ lam : C, lam ≠ 0 → χ lam * lam ^ kb = lam ^ ka := by
  obtain ⟨a, b', hrel, hmk⟩ :=
    IsFractionRing.exists_reduced_fraction (DifferentialPolynomial Unit C) x
  set b : DifferentialPolynomial Unit C := (b' : DifferentialPolynomial Unit C) with hb_def
  have hb0 : b ≠ 0 := nonZeroDivisors.coe_ne_zero b'
  have hxeq : x = algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) a
      / algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) b := by
    rw [hb_def, ← IsFractionRing.mk'_eq_div]; exact hmk.symm
  have ha0 : a ≠ 0 := by
    intro h0
    exact hx0 (by rw [hxeq, h0, map_zero, zero_div])
  -- the clock is injective on the polynomial ring (it has a left inverse `ρ_{λ⁻¹}`)
  have hclock_inj : ∀ lam : C, lam ≠ 0 → ∀ w : DifferentialPolynomial Unit C,
      clockDilationAlgHom lam w = 0 → w = 0 := by
    intro lam hlam w hw
    have hcc := congrArg (clockDilationAlgHom lam⁻¹) hw
    rwa [clockDilationAlgHom_apply_apply, inv_mul_cancel₀ hlam, clockDilationAlgHom_one,
      map_zero] at hcc
  -- the ring cross-relation `ρ_λ(a)·b = χ(λ)·a·ρ_λ(b)`, and nonvanishing of `χ`
  have hmain : ∀ lam : C, lam ≠ 0 →
      clockDilationAlgHom lam a * b
        = MvPolynomial.C (χ lam) * a * clockDilationAlgHom lam b ∧ χ lam ≠ 0 := by
    intro lam hlam
    have Heig := heig lam hlam
    have hχ : χ lam ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at Heig
      exact hx0 ((clockDilationFieldEquiv lam hlam).injective (by rw [Heig, map_zero]))
    refine ⟨?_, hχ⟩
    rw [hxeq, map_div₀, clockDilationFieldEquiv_algebraMap,
      clockDilationFieldEquiv_algebraMap] at Heig
    have hCK : algebraMap C (ScalarDifferentialField C) (χ lam)
        = algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
            (MvPolynomial.C (χ lam)) := by
      rw [IsScalarTower.algebraMap_apply C (DifferentialPolynomial Unit C)
        (ScalarDifferentialField C), MvPolynomial.algebraMap_eq]
    rw [hCK, ← mul_div_assoc] at Heig
    have hbK : algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C) b ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hb0
    have hρbK : algebraMap (DifferentialPolynomial Unit C) (ScalarDifferentialField C)
        (clockDilationAlgHom lam b) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact fun h => hb0 (hclock_inj lam hlam b h)
    rw [div_eq_div_iff hρbK hbK] at Heig
    simp only [← map_mul] at Heig
    exact IsFractionRing.injective (DifferentialPolynomial Unit C) (ScalarDifferentialField C) Heig
  -- the numerator is a ring clock eigenvector
  have hproj_a : ∀ lam : C, lam ≠ 0 →
      ∃ r : C, clockDilationAlgHom lam a = MvPolynomial.C r * a := by
    intro lam hlam
    have hdvd : ∀ mu : C, mu ≠ 0 → a ∣ clockDilationAlgHom mu a := by
      intro mu hmu
      obtain ⟨hst, _⟩ := hmain mu hmu
      have hdm : a ∣ clockDilationAlgHom mu a * b := by
        rw [hst]; exact ⟨MvPolynomial.C (χ mu) * clockDilationAlgHom mu b, by ring⟩
      exact hrel.dvd_of_dvd_mul_right hdm
    have hrev : clockDilationAlgHom lam a ∣ a := by
      have h1 := hdvd lam⁻¹ (inv_ne_zero hlam)
      have h2 := map_dvd (clockDilationAlgHom lam) h1
      rwa [clockDilationAlgHom_apply_apply, mul_inv_cancel₀ hlam, clockDilationAlgHom_one] at h2
    exact differentialPolynomial_associated_C_mul
      (associated_of_dvd_dvd (hdvd lam hlam) hrev)
  obtain ⟨ka, hka⟩ := clock_projective_eigenvalue_pow ha0 hproj_a
  -- the denominator is a ring clock eigenvector, via the numerator's law
  have hproj_b : ∀ lam : C, lam ≠ 0 →
      ∃ r : C, clockDilationAlgHom lam b = MvPolynomial.C r * b := by
    intro lam hlam
    obtain ⟨hst, hχ⟩ := hmain lam hlam
    rw [hka lam hlam] at hst
    have hcancel : MvPolynomial.C (lam ^ ka) * b
        = MvPolynomial.C (χ lam) * clockDilationAlgHom lam b := by
      have h2 : a * (MvPolynomial.C (lam ^ ka) * b)
          = a * (MvPolynomial.C (χ lam) * clockDilationAlgHom lam b) := by linear_combination hst
      exact mul_left_cancel₀ ha0 h2
    have hCχ : MvPolynomial.C (χ lam) ≠ (0 : DifferentialPolynomial Unit C) := by
      rw [Ne, MvPolynomial.C_eq_zero]; exact hχ
    refine ⟨(χ lam)⁻¹ * lam ^ ka, ?_⟩
    apply mul_left_cancel₀ hCχ
    rw [← mul_assoc, ← MvPolynomial.C_mul, ← mul_assoc (χ lam) (χ lam)⁻¹,
      mul_inv_cancel₀ hχ, one_mul]
    exact hcancel.symm
  obtain ⟨kb, hkb⟩ := clock_projective_eigenvalue_pow hb0 hproj_b
  -- assemble: substitute both laws into the cross-relation and cancel `a·b`
  refine ⟨ka, kb, fun lam hlam => ?_⟩
  obtain ⟨hst, _⟩ := hmain lam hlam
  rw [hka lam hlam, hkb lam hlam] at hst
  have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have hfin : MvPolynomial.C (lam ^ ka) * (a * b)
      = MvPolynomial.C (χ lam * lam ^ kb) * (a * b) := by
    rw [MvPolynomial.C_mul]; linear_combination hst
  exact (MvPolynomial.C_injective (Unit × ℕ) C (mul_right_cancel₀ hab0 hfin)).symm

end

end GaloisForLFunctions
