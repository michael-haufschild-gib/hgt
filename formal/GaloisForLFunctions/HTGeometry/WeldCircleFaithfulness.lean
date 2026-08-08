import GaloisForLFunctions.HTGeometry.ExpNatIrrational
import GaloisForLFunctions.HTGeometry.WeldRateLattice

/-!
# The circle recovers prime faithfulness — the non-torsion, transcendence-gated leg

`WeldChargeFaithfulness` shows a dichotomy for reading the prime weld lattice through a charge:

* into a **finite (bounded-exponent)** target the rank-`∞` prime lattice **collapses** to `0`
  (`prime_flux_charge_collapse`, `weldClass_finite_charge_invisible`) — a divisible source has no
  nonzero bounded-exponent character;
* into the **torsion-free** target `H²(WeldGroup; ℝ)` faithfulness is total
  (`primeFluxHom_injective`), needing only unique factorization.

This module fills in the decisive middle case: a **compact, divisible, torsion** target — the circle
`ℝ/ℤ` — where the collapse argument does *not* apply (`ℝ/ℤ` carries nonzero characters) and the naive
independence argument does *not* suffice either.  Faithfulness on the circle is exactly the
`ℤ`-independence of `{log p} ∪ {1}`, and that needs a genuinely new input beyond unique factorization:
the **transcendence of `e`** (`exp_int_irrational`).  A relation `Σ nₚ log p = k ∈ ℤ` exponentiates to
`e^k = ∏ pⁿᵖ ∈ ℚ`, impossible for `k ≠ 0`; so `k = 0` and unique factorization finishes.

So the dividing line in the dichotomy is *bounded exponent*, not torsion: the circle is divisible and
torsion yet reads the prime lattice faithfully — and it is precisely here that the arithmetic of the
weld meets the transcendence of `e`.
-/

open Polynomial

namespace GaloisForLFunctions
namespace RHTower

/-- **Exponentiating a prime-log combination gives a positive rational.**  For any integer
combination `Σ_p z_p log p`, its exponential is the rational product `∏_p p^{z_p}` (a `ℚ`-value cast
to `ℝ`): `exp` turns the sum into a product and `exp(z log p) = p^z`. -/
theorem exp_primeLog_comb_eq_rat (c : Nat.Primes →₀ ℤ) :
    Real.exp (c.sum fun p z => z • Real.log (p : ℕ))
      = ((c.prod fun p z => (p : ℚ) ^ z : ℚ) : ℝ) := by
  simp_rw [zsmul_eq_mul]
  rw [Finsupp.sum, Real.exp_sum, Finsupp.prod, Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  rw [Rat.cast_zpow, Rat.cast_natCast, mul_comm, ← Real.rpow_def_of_pos hp0, Real.rpow_intCast]

/-- **`{log p} ∪ {1}` is `ℤ`-linearly independent.**  If an integer combination of prime logarithms
equals an integer `k`, then `k = 0` and all coefficients vanish.  The transcendence step: `e^k` would
be the rational `∏ p^{z_p}`, impossible for `k ≠ 0` by `exp_int_irrational`; then `k = 0` reduces to
the ordinary prime-log independence `primeLog_linearIndependent` (unique factorization). -/
theorem primeLog_indep_mod_one (c : Nat.Primes →₀ ℤ) (k : ℤ)
    (h : (c.sum fun p z => z • Real.log (p : ℕ)) = (k : ℝ)) : k = 0 ∧ c = 0 := by
  have hrat : Real.exp (k : ℝ) = ((c.prod fun p z => (p : ℚ) ^ z : ℚ) : ℝ) := by
    rw [← h]; exact exp_primeLog_comb_eq_rat c
  have hk : k = 0 := by
    by_contra hk0
    exact (exp_int_irrational hk0) ⟨_, hrat.symm⟩
  refine ⟨hk, ?_⟩
  rw [hk, Int.cast_zero] at h
  exact (linearIndependent_iff.mp primeLog_linearIndependent) c
    (by rw [Finsupp.linearCombination_apply]; exact h)

/-! ### The circle-valued prime charge is injective -/

/-- The prime-log assembly as an additive homomorphism `(Nat.Primes →₀ ℤ) →+ ℝ`,
`c ↦ Σ_p c(p)·log p`. -/
noncomputable def primeLogHom : (Nat.Primes →₀ ℤ) →+ ℝ :=
  Finsupp.liftAddHom (fun p : Nat.Primes =>
    AddMonoidHom.mk' (fun z : ℤ => z • Real.log (p : ℕ)) (fun a b => add_zsmul _ a b))

theorem primeLogHom_apply (c : Nat.Primes →₀ ℤ) :
    primeLogHom c = c.sum fun p z => z • Real.log (p : ℕ) := rfl

/-- **General period-lattice faithfulness criterion.**  For any additive subgroup `Λ ⊆ ℝ`, the prime
charge into the quotient `ℝ/Λ` is injective iff `{log p}` is `ℤ`-independent modulo `Λ`: no nontrivial
integer combination of prime logarithms lands in `Λ`.  This reduces "which period lattices read the
prime lattice faithfully" to a transcendence-mod-`Λ` question — the circle `Λ = ⟨1⟩` is exactly the
instance whose hypothesis is discharged by the transcendence of `e` (`primeLog_indep_mod_one`). -/
theorem primeQuotientCharge_injective_iff (Λ : AddSubgroup ℝ) :
    Function.Injective ((QuotientAddGroup.mk' Λ).comp primeLogHom)
      ↔ ∀ c : Nat.Primes →₀ ℤ, primeLogHom c ∈ Λ → c = 0 := by
  rw [injective_iff_map_eq_zero]
  refine ⟨fun h c hc => h c ?_, fun h c hc => h c ?_⟩
  · rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; exact hc
  · rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hc
    exact hc

/-- The prime charge into the compact circle `ℝ/ℤ`: `c ↦ [Σ_p c(p)·log p] mod 1`. -/
noncomputable def primeCircleHom : (Nat.Primes →₀ ℤ) →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp primeLogHom

/-- **Faithfulness on the circle.**  The circle-valued prime charge is injective: distinct integer
combinations of the primes stay distinct in `ℝ/ℤ`.  Equivalently, `{log p} ∪ {1}` is `ℤ`-independent
— the compact, torsion, divisible target reads the whole rank-`∞` prime lattice, in sharp contrast to
the total collapse under any bounded-exponent charge (`prime_flux_charge_collapse`).  The proof runs
through the transcendence of `e` (`primeLog_indep_mod_one`). -/
theorem primeCircleHom_injective : Function.Injective primeCircleHom := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [primeCircleHom, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    AddCircle.coe_eq_zero_iff] at hc
  obtain ⟨k, hk⟩ := hc
  have hval : (c.sum fun p z => z • Real.log (p : ℕ)) = (k : ℝ) := by
    rw [← primeLogHom_apply, ← hk, zsmul_eq_mul, mul_one]
  exact (primeLog_indep_mod_one c k hval).2

end RHTower
end GaloisForLFunctions
