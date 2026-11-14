import GaloisForLFunctions.BiarithmeticGaugeGeometry.RamanujanTorsionStabilizersAndMonomialCollapse
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.HodgeWitt.SemilinearFitting

/-!
# Nilpotent and stable torsion coordinates of monomial dilation

For the existing action `(x,y) ↦ (q₁x,q₂y)` modulo `pᵉ`, the nilpotent
part consists exactly of coordinates whose multiplier is divisible by `p`.
The complementary stable part consists of the other coordinates. The
nilpotent part dies after `e` iterates, and the stable part is invertible.
This applies the finite-torsion Fitting decomposition to rational-torsion
monomial dynamics, with the two summands explicitly identified.
-/

noncomputable section

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

/-- The existing monomial action with its scalar-linear structure. -/
def monomialTorsionEnd (N q₁ q₂ : ℕ) :
    Module.End (ZMod N) (ZMod N × ZMod N) where
  toFun := monomialTorsionAction N q₁ q₂
  map_add' x y := by ext <;> simp [monomialTorsionAction, mul_add]
  map_smul' a x := by ext <;> simp [monomialTorsionAction, mul_left_comm]

theorem monomialTorsionAction_iterate (N q₁ q₂ n : ℕ) (x : ZMod N × ZMod N) :
    (monomialTorsionAction N q₁ q₂)^[n] x =
      ((q₁ : ZMod N) ^ n * x.1, (q₂ : ZMod N) ^ n * x.2) := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [monomialTorsionAction, pow_succ', mul_assoc]

theorem monomialIntegralEnd_pow_apply (N q₁ q₂ n : ℕ) (x : ZMod N × ZMod N) :
    (integralEnd (RingEquiv.refl (ZMod N)) (monomialTorsionEnd N q₁ q₂) ^ n) x =
      ((q₁ : ZMod N) ^ n * x.1, (q₂ : ZMod N) ^ n * x.2) := by
  rw [Module.End.pow_apply]
  exact monomialTorsionAction_iterate N q₁ q₂ n x

variable (p : ℕ) [Fact p.Prime]

/-- A scalar on prime-power torsion is either nilpotent or a unit, with an explicit test. -/
theorem primePower_scalar_dichotomy (e q : ℕ) :
    (p ∣ q ∧ (q : ZMod (p ^ e)) ^ e = 0) ∨
      (¬ p ∣ q ∧ IsUnit (q : ZMod (p ^ e))) := by
  by_cases h : p ∣ q
  · refine Or.inl ⟨h, ?_⟩
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow_of_dvd h e
  · exact Or.inr ⟨h, (ZMod.isUnit_iff_coprime q (p ^ e)).mpr
      ((((Fact.out : p.Prime).coprime_iff_not_dvd).mpr h).symm.pow_right e)⟩

/-- Eventual annihilation of one coordinate is decided solely by divisibility of its multiplier. -/
theorem primePower_scalar_eventually_zero_iff (e q : ℕ) (x : ZMod (p ^ e)) :
    (∃ n : ℕ, (q : ZMod (p ^ e)) ^ n * x = 0) ↔ (¬ p ∣ q → x = 0) := by
  rcases primePower_scalar_dichotomy p e q with ⟨hd, hz⟩ | ⟨hd, hu⟩
  · exact ⟨fun _ hn => False.elim (hn hd), fun _ => ⟨e, by rw [hz, zero_mul]⟩⟩
  · constructor
    · rintro ⟨n, hn⟩ _
      exact (hu.pow n).mul_left_cancel (hn.trans (mul_zero _).symm)
    · intro h
      exact ⟨0, by rw [h hd, mul_zero]⟩

/-- Exponent `e` kills every eventually vanishing coordinate modulo `pᵉ`. -/
theorem primePower_scalar_kernel_iff (e q : ℕ) (x : ZMod (p ^ e)) :
    (q : ZMod (p ^ e)) ^ e * x = 0 ↔ (¬ p ∣ q → x = 0) := by
  constructor
  · intro h
    exact (primePower_scalar_eventually_zero_iff p e q x).mp ⟨e, h⟩
  · intro h
    rcases primePower_scalar_dichotomy p e q with ⟨_, hz⟩ | ⟨hd, _⟩
    · rw [hz, zero_mul]
    · rw [h hd, mul_zero]

/-- Infinite divisibility by a scalar is the complementary coordinate condition. -/
theorem primePower_scalar_stable_iff (e q : ℕ) (x : ZMod (p ^ e)) :
    (∀ n : ℕ, ∃ y : ZMod (p ^ e), (q : ZMod (p ^ e)) ^ n * y = x) ↔
      (p ∣ q → x = 0) := by
  rcases primePower_scalar_dichotomy p e q with ⟨hd, hz⟩ | ⟨hd, hu⟩
  · constructor
    · intro h _
      obtain ⟨y, hy⟩ := h e
      exact hy.symm.trans (by rw [hz, zero_mul])
    · intro h n
      exact ⟨0, (mul_zero _).trans (h hd).symm⟩
  · constructor
    · intro _ h
      exact False.elim (hd h)
    · intro _ n
      obtain ⟨u, hu⟩ := hu.pow n
      refine ⟨(↑u⁻¹ : ZMod (p ^ e)) * x, ?_⟩
      rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

/-- Exact nilpotent summand of the original two-coordinate monomial torsion action. -/
theorem monomial_nilpotentPart_mem_iff (e q₁ q₂ : ℕ) (x : ZMod (p ^ e) × ZMod (p ^ e)) :
    x ∈ semilinearNilpotentPart (RingEquiv.refl (ZMod (p ^ e)))
      (monomialTorsionEnd (p ^ e) q₁ q₂) ↔
      (¬ p ∣ q₁ → x.1 = 0) ∧ (¬ p ∣ q₂ → x.2 = 0) := by
  rw [semilinearNilpotentPart, Submodule.mem_iSup_of_directed _
    (semilinearKerPow_monotone _ _).directed_le]
  constructor
  · rintro ⟨n, hn⟩
    change (integralEnd _ _ ^ n) x = 0 at hn
    rw [monomialIntegralEnd_pow_apply] at hn
    exact ⟨(primePower_scalar_eventually_zero_iff p e q₁ x.1).mp ⟨n, congrArg Prod.fst hn⟩,
      (primePower_scalar_eventually_zero_iff p e q₂ x.2).mp ⟨n, congrArg Prod.snd hn⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨e, ?_⟩
    change (integralEnd _ _ ^ e) x = 0
    rw [monomialIntegralEnd_pow_apply]
    exact Prod.ext ((primePower_scalar_kernel_iff p e q₁ x.1).mpr h₁)
      ((primePower_scalar_kernel_iff p e q₂ x.2).mpr h₂)

/-- Exact stable summand: coordinates with prime-divisible multipliers are absent. -/
theorem monomial_stablePart_mem_iff (e q₁ q₂ : ℕ) (x : ZMod (p ^ e) × ZMod (p ^ e)) :
    x ∈ semilinearStablePart (RingEquiv.refl (ZMod (p ^ e)))
      (monomialTorsionEnd (p ^ e) q₁ q₂) ↔
      (p ∣ q₁ → x.1 = 0) ∧ (p ∣ q₂ → x.2 = 0) := by
  rw [semilinearStablePart, Submodule.mem_iInf]
  constructor
  · intro h
    constructor
    · apply (primePower_scalar_stable_iff p e q₁ x.1).mp
      intro n
      obtain ⟨y, hy⟩ := h n
      rw [monomialIntegralEnd_pow_apply] at hy
      exact ⟨y.1, congrArg Prod.fst hy⟩
    · apply (primePower_scalar_stable_iff p e q₂ x.2).mp
      intro n
      obtain ⟨y, hy⟩ := h n
      rw [monomialIntegralEnd_pow_apply] at hy
      exact ⟨y.2, congrArg Prod.snd hy⟩
  · rintro ⟨h₁, h₂⟩ n
    obtain ⟨y₁, hy₁⟩ := (primePower_scalar_stable_iff p e q₁ x.1).mpr h₁ n
    obtain ⟨y₂, hy₂⟩ := (primePower_scalar_stable_iff p e q₂ x.2).mpr h₂ n
    refine ⟨(y₁, y₂), ?_⟩
    rw [monomialIntegralEnd_pow_apply]
    exact Prod.ext hy₁ hy₂

/-- The two explicitly classified torsion summands reconstruct every original point. -/
def monomialTorsionFittingEquiv (e q₁ q₂ : ℕ) :
    (semilinearNilpotentPart (RingEquiv.refl (ZMod (p ^ e)))
        (monomialTorsionEnd (p ^ e) q₁ q₂) ×
      semilinearStablePart (RingEquiv.refl (ZMod (p ^ e)))
        (monomialTorsionEnd (p ^ e) q₁ q₂)) ≃ₗ[ZMod (p ^ e)]
      (ZMod (p ^ e) × ZMod (p ^ e)) :=
  semilinearFittingEquiv _ _

#print axioms monomial_nilpotentPart_mem_iff
#print axioms monomial_stablePart_mem_iff
#print axioms monomialTorsionFittingEquiv

end GaloisForLFunctions.BiarithmeticGaugeGeometry
