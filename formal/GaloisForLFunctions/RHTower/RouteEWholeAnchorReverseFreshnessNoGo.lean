import Mathlib.Data.Nat.GCD.Basic

/-!
# Route E whole-anchor same-reservoir reverse-freshness no-go

In a whole-anchor edge, the forward reservoir divides the terminal.  A reverse certificate cannot
reuse that reservoir while also requiring it to be coprime to its new source, except for the
trivial reservoir one.  This rules out only same-reservoir transpose pairing; different reverse
reservoirs, aggregate mismatch-divergence control, and toggle-based symmetric relations remain.
-/

namespace RHTower

/-- A nontrivial whole-anchor reservoir cannot be fresh relative to the terminal containing it. -/
theorem routeE_wholeAnchor_sameReservoir_not_reverseFresh
    {t m : ℕ} (ht : 1 < t) :
    ¬Nat.Coprime t (t * m) := by
  intro hcop
  have htOne : t = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (dvd_refl t) ⟨m, rfl⟩
  omega

/-- Exact classification: a reservoir is coprime to a terminal containing it iff it is trivial. -/
theorem routeE_wholeAnchor_reverseFresh_sameReservoir_iff_one
    (t m : ℕ) :
    Nat.Coprime t (t * m) ↔ t = 1 := by
  constructor
  · intro hcop
    exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl t) ⟨m, rfl⟩
  · rintro rfl
    simp

end RHTower
