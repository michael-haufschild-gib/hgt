import GaloisForLFunctions.RHTower.RayCompleteTranslationFaithful
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Finite Euler cutoff constraint algebras

This file closes the finite-stage assertions in the ray-complete card.  Every cutoff ideal has an
explicit nonzero product annihilator, is the intersection of maximal translation-character
kernels and hence radical, and its quotient is reduced.  The quotient transition maps are
surjective, while the simultaneous map into all cutoff quotients is injective and compatible with
those transitions.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The elementary period annihilator for one positive frequency ray. -/
def rayPeriodFactor (lam : ℝ) : AddMonoidAlgebra ℂ ℂ :=
  AddMonoidAlgebra.single (2 * (Real.pi : ℂ) * I / (lam : ℂ)) 1 - 1

theorem rayPeriodFactor_ne_zero (lam : ℝ) (hlam : 0 < lam) :
    rayPeriodFactor lam ≠ 0 := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  let h : ℂ := 2 * (Real.pi : ℂ) * I / (lam : ℂ)
  have hh0 : h ≠ 0 := div_ne_zero h2pi hlamC
  rw [rayPeriodFactor, sub_ne_zero]
  intro heq
  have hcoe : (AddMonoidAlgebra.single h (1 : ℂ)).coeff h =
      (1 : AddMonoidAlgebra ℂ ℂ).coeff h :=
    congrArg (fun f : AddMonoidAlgebra ℂ ℂ => f.coeff h) heq
  rw [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.one_def,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply,
    if_pos rfl, if_neg hh0.symm] at hcoe
  exact one_ne_zero hcoe

theorem translationChar_rayPeriodFactor_eq_zero
    (lam : ℝ) (hlam : 0 < lam) (m : ℕ) (_hm : 1 ≤ m) :
    translationChar ((m : ℝ) * lam) (rayPeriodFactor lam) = 0 := by
  have hlamC : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
  rw [rayPeriodFactor, map_sub, translationChar_single, map_one]
  have hkey :
      (-(((m : ℝ) * lam : ℝ) : ℂ) *
          (2 * (Real.pi : ℂ) * I / (lam : ℂ))) =
        ((-(m : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    field_simp
    push_cast
    ring
  rw [hkey, Complex.exp_int_mul_two_pi_mul_I, sub_self]

/-- The primes through the cutoff `N`. -/
def primesThrough (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- The product annihilator `P_N` from the paper. -/
def eulerCutoffAnnihilator (N : ℕ) : AddMonoidAlgebra ℂ ℂ :=
  ∏ p ∈ primesThrough N, rayPeriodFactor (Real.log p)

theorem eulerCutoffAnnihilator_ne_zero (N : ℕ) :
    eulerCutoffAnnihilator N ≠ 0 := by
  rw [eulerCutoffAnnihilator]
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  rw [primesThrough, Finset.mem_filter] at hp
  exact rayPeriodFactor_ne_zero _ (Real.log_pos (by exact_mod_cast hp.2.one_lt))

theorem eulerCutoffAnnihilator_mem_eulerJ (N : ℕ) :
    eulerCutoffAnnihilator N ∈ eulerJ N := by
  rw [eulerJ, mem_annIdeal]
  rintro x ⟨p, hp, hpN, m, hm, rfl⟩
  rw [eulerCutoffAnnihilator, map_prod]
  exact Finset.prod_eq_zero (show p ∈ primesThrough N by
      rw [primesThrough, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hp⟩)
    (translationChar_rayPeriodFactor_eq_zero _
      (Real.log_pos (by exact_mod_cast hp.one_lt)) m hm)

/-- Every finite-stage cutoff has a nonzero analytic translation constraint. -/
theorem eulerJ_ne_bot (N : ℕ) : eulerJ N ≠ ⊥ := by
  intro hbot
  have hmem := eulerCutoffAnnihilator_mem_eulerJ N
  rw [hbot, Ideal.mem_bot] at hmem
  exact eulerCutoffAnnihilator_ne_zero N hmem

/-- Every translation-character kernel is maximal, since the character is onto the coefficient
field through constants. -/
theorem translationCharKer_isMaximal (lam : ℝ) :
    (translationCharKer lam).IsMaximal := by
  rw [translationCharKer]
  apply RingHom.ker_isMaximal_of_surjective (translationChar lam).toRingHom
  intro z
  refine ⟨algebraMap ℂ (AddMonoidAlgebra ℂ ℂ) z, ?_⟩
  exact (translationChar lam).commutes z

/-- Exact finite-stage character-kernel intersection. -/
theorem eulerJ_eq_characterKernel_iInf (N : ℕ) :
    eulerJ N =
      ⨅ l : eulerFreqBelow N, translationCharKer l.1 := rfl

/-- Each cutoff ideal is radical as an intersection of maximal ideals. -/
theorem eulerJ_isRadical (N : ℕ) : (eulerJ N).IsRadical := by
  rw [eulerJ_eq_characterKernel_iInf]
  apply Ideal.isRadical_iInf
  intro l
  exact (translationCharKer_isMaximal l.1).isPrime.isRadical

/-- The cutoff coordinate algebra `B_N = A/J_N` is reduced. -/
theorem eulerCutoffQuotient_isReduced (N : ℕ) :
    IsReduced (AddMonoidAlgebra ℂ ℂ ⧸ eulerJ N) :=
  (Ideal.isRadical_iff_quotient_reduced (eulerJ N)).mp (eulerJ_isRadical N)

/-- The quotient transition `B_M → B_N` for `N ≤ M`. -/
def eulerCutoffTransition {N M : ℕ} (hNM : N ≤ M) :
    (AddMonoidAlgebra ℂ ℂ ⧸ eulerJ M) →ₐ[ℂ]
      (AddMonoidAlgebra ℂ ℂ ⧸ eulerJ N) :=
  Ideal.Quotient.liftₐ (eulerJ M) (Ideal.Quotient.mkₐ ℂ (eulerJ N)) (by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (eulerJ_antitone hNM ha))

theorem eulerCutoffTransition_mk {N M : ℕ} (hNM : N ≤ M)
    (a : AddMonoidAlgebra ℂ ℂ) :
    eulerCutoffTransition hNM (Ideal.Quotient.mk (eulerJ M) a) =
      Ideal.Quotient.mk (eulerJ N) a := rfl

theorem eulerCutoffTransition_surjective {N M : ℕ} (hNM : N ≤ M) :
    Function.Surjective (eulerCutoffTransition hNM) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (eulerJ M) a, rfl⟩

/-- The canonical simultaneous readout in every finite cutoff quotient. -/
def eulerCofinalQuotientMap :
    AddMonoidAlgebra ℂ ℂ →ₐ[ℂ]
      ((N : ℕ) → AddMonoidAlgebra ℂ ℂ ⧸ eulerJ N) where
  toFun a N := Ideal.Quotient.mk (eulerJ N) a
  map_one' := by funext N; simp
  map_mul' a b := by funext N; simp
  map_zero' := by funext N; simp
  map_add' a b := by funext N; simp
  commutes' z := by
    funext N
    exact (Ideal.Quotient.mkₐ ℂ (eulerJ N)).commutes z

/-- The simultaneous cutoff readout is compatible with every transition map. -/
theorem eulerCofinalQuotientMap_compatible
    (a : AddMonoidAlgebra ℂ ℂ) {N M : ℕ} (hNM : N ≤ M) :
    eulerCutoffTransition hNM (eulerCofinalQuotientMap a M) =
      eulerCofinalQuotientMap a N := rfl

/-- Cofinal separation, in coordinate-algebra form: the canonical map into the compatible family
of reduced cutoff quotients is injective. -/
theorem eulerCofinalQuotientMap_injective :
    Function.Injective eulerCofinalQuotientMap := by
  intro a b hab
  apply sub_eq_zero.mp
  have hmem : a - b ∈ ⨅ N, eulerJ N := by
    rw [Ideal.mem_iInf]
    intro N
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (eulerJ N) (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hab N)
  rw [eulerJ_iInf_eq_bot, Ideal.mem_bot] at hmem
  exact hmem

end GaloisForLFunctions.RHTower
