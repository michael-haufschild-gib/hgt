import GaloisForLFunctions.RHTower.Sieve.SqrtBarrier
import GaloisForLFunctions.RHTower.Sieve.CoprimeProductSign

/-!
# Local Hall capacity of the distinct products

A family of balanced coprime pairs whose products all lie in one window supplies, inside that
window, at least `(#S)²/(X·balancedMomentConst y)` *distinct* integers, each carrying the product
sign.  When that capacity exceeds the number of sources, the sources inject into the products
without leaving the window.

This is the local form of the distinct-product bound: the Cauchy–Schwarz passage from a
representation count to a physical count, combined with the matching lemma.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Local Hall capacity of the distinct products of balanced coprime pairs.** -/
theorem exists_hall_injection_balanced {X H y : ℕ} (hy : 1 ≤ y) (S : Finset (ℕ × ℕ)) {ε : ℤ}
    (hV : 0 < ((X + H : ℕ) : ℝ) * balancedMomentConst y)
    (hd : ∀ q ∈ S, q.1 ∈ Finset.Icc y (2 * y))
    (hwin : ∀ q ∈ S, X < q.1 * q.2 ∧ q.1 * q.2 ≤ X + H)
    (hcop : ∀ q ∈ S, Nat.Coprime q.1 q.2)
    (hsign : ∀ q ∈ S, moebius q.1 * moebius q.2 = ε)
    (sources : Finset ℕ)
    (hswin : ∀ n ∈ sources, X < n ∧ n ≤ X + H)
    (hcap : ((sources.card : ℕ) : ℝ)
      ≤ ((S.card : ℕ) : ℝ) ^ (2 : ℕ) / (((X + H : ℕ) : ℝ) * balancedMomentConst y)) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑sources
      ∧ (∀ n ∈ sources, f n ∈ S.image (fun q => q.1 * q.2))
      ∧ (∀ n ∈ sources, moebius (f n) = ε)
      ∧ ∀ n ∈ sources, |(f n : ℤ) - (n : ℤ)| ≤ (H : ℤ) := by
  classical
  have himg : ∀ q ∈ S, q.1 * q.2 ∈ Finset.Icc 1 (X + H) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hwin q hq
    rw [Finset.mem_Icc]
    exact ⟨by omega, h2⟩
  have hprod := card_image_mul_ge_explicit (y := y) (X := X + H) hy S hV hd himg
  have hcard : sources.card ≤ (S.image (fun q => q.1 * q.2)).card := by
    have hR : ((sources.card : ℕ) : ℝ)
        ≤ (((S.image (fun q => q.1 * q.2)).card : ℕ) : ℝ) := le_trans hcap hprod
    exact_mod_cast hR
  have htwin : ∀ n ∈ S.image (fun q => q.1 * q.2), X < n ∧ n ≤ X + H := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨q, hq, rfl⟩ := hn
    exact hwin q hq
  obtain ⟨f, hinj, hmem, hdisp⟩ :=
    exists_injOn_displacement_le (X := X) (H := H) hcard hswin htwin
  exact ⟨f, hinj, hmem, fun n hn => moebius_image_sign hcop hsign (f n) (hmem n hn), hdisp⟩

end RHTower.Sieve
