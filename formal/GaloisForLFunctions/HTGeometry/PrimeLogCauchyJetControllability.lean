import GaloisForLFunctions.HTGeometry.CauchyJetControllability
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# Prime-log Cauchy-jet controllability

The generic real Cauchy-jet theorem specializes unconditionally to the prime-log support.  Thus
finitely supported real changes of prime masses realize every finite complex jet packet at distinct
upper-half-plane nodes.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Finitely supported real prime-log masses realize every prescribed finite complex Cauchy-jet
packet at distinct upper-half-plane nodes. -/
theorem primeLogCauchyJetRealLinearCombination_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) :
    Function.Surjective
      (cauchyJetRealLinearCombination x n primeLogSupport) :=
  cauchyJetRealLinearCombination_surjective x hx hupper n primeLogSupport
    primeLogSupport_injective

/-- At every positive prime mass configuration, every finite complex Cauchy-jet direction has a
finitely supported prime-mass lift that remains strictly positive for all sufficiently small
positive times. -/
theorem primeLogCauchyJet_full_tangent_at_positive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (w : Nat.Primes → ℝ) (hw : ∀ p, 0 < w p)
    (y : (Σ i, Fin (n i)) → ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      cauchyJetRealLinearCombination x n primeLogSupport a = y ∧
      0 < ε ∧ ε < η ∧ ∀ p, 0 < w p + ε * a p := by
  exact surjective_finsupp_full_tangent_at_positive
    (cauchyJetRealLinearCombination x n primeLogSupport)
    (primeLogCauchyJetRealLinearCombination_surjective x hx hupper n)
    w hw y hη

/-- The preceding tangent theorem applies to the actual positive dyadic prime masses of every
gauge, with no boundedness assumption needed for this finite-coordinate statement. -/
theorem primeDyadicCauchyJet_full_tangent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (u : Nat.Primes → ℝ)
    (y : (Σ i, Fin (n i)) → ℂ) {η : ℝ} (hη : 0 < η) :
    ∃ a : Nat.Primes →₀ ℝ, ∃ ε : ℝ,
      cauchyJetRealLinearCombination x n primeLogSupport a = y ∧
      0 < ε ∧ ε < η ∧ ∀ p, 0 < primeDyadicWeight u p + ε * a p := by
  exact primeLogCauchyJet_full_tangent_at_positive x hx hupper n
    (primeDyadicWeight u) (primeDyadicWeight_pos u) y hη

end GaloisForLFunctions.HTGeometry
