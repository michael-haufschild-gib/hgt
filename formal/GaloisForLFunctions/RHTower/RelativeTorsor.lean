/-
The relative `2^k`-root torsor of ξ against the free `{σ_p}` reference frame collapses to ξ's own.

The free multiplicative tower — the finite Euler truncation `eulerPartial P`, which carries a global
single-valued `2^k`-th root `eulerRoot k P` on the right half-plane, unconditionally
(`exists_global_pow_root_eulerPartial`) — was proposed as a reference frame against which ξ's
obstructed `2^k`-root torsor could be measured relatively. This module shows the relative torsor is
deck-isomorphic to ξ's own: dressing ξ by the reference frame moves the deck class nowhere.

The reason is structural. The reference root `eulerRoot k P` is a product of exponentials, hence
nonvanishing at every point of ℂ (`eulerRoot_ne_zero`). The deck class is the ratio of the two chart
roots (`deckClass`); multiplying both chart roots by ONE global nonvanishing factor cancels in that
ratio (`deckClass_mul_global`). So the relative deck class equals ξ's deck class `exp(2πi·m/2^k)`
exactly (`relative_deckClass_eq_xi`), and the relative torsor is trivial iff ξ's is — iff the
divisibility clause `2^k ∣ m(ρ₀)` of `RHLadder k` holds (`relative_torsor_trivial_iff_ladder`).

A reference frame can contribute to the relative monodromy only if it carries monodromy itself; the
`{σ_p}` tower's defining property — freeness, a single-valued global root
(`reference_own_deckClass_one`) — is exactly the absence of monodromy, so it is invisible to the deck
cocycle. Freeness and contribution are mutually exclusive: the free reference frame cannot break the
tautology it was meant to break. The collapse holds at every basepoint unconditionally
(`relative_deckClass_eq`); the only way to give the reference nontrivial monodromy is to continue its
Euler product across the wall `Re s = 1`, which is a flow.
-/
import GaloisForLFunctions.RHTower.PrimeDivisorAtomsNoGo
import GaloisForLFunctions.RHTower.XiDeck

noncomputable section

namespace RHTower

open Complex Finset

/-! ### §1 The reference frame is nonvanishing everywhere -/

/-- Each reference root factor is `exp` of something, hence never zero. -/
theorem eulerRootFactor_ne_zero (k p : ℕ) (s : ℂ) : eulerRootFactor k p s ≠ 0 := by
  rw [eulerRootFactor]; exact Complex.exp_ne_zero _

/-- **The reference root is nonvanishing at every point of ℂ** — it is a finite product of
exponentials, so no domain restriction and no hypothesis on the primes is needed. -/
theorem eulerRoot_ne_zero (k : ℕ) (P : Finset ℕ) (s : ℂ) : eulerRoot k P s ≠ 0 := by
  rw [eulerRoot]
  exact Finset.prod_ne_zero_iff.mpr fun p _ => eulerRootFactor_ne_zero k p s

/-! ### §2 The relative carrier and its roots -/

/-- The relative carrier: ξ dressed by the finite `{σ_p}` reference frame. -/
def relCarrier (P : Finset ℕ) : ℂ → ℂ := fun s => xi s * eulerPartial P s

/-- **The dressed root is a `2^k`-th root of the relative carrier.**  Multiplying a local `2^k`-root
`G` of ξ by the reference root gives a `2^k`-root of `relCarrier P` on the right half-plane, since
the reference root is a `2^k`-root of `eulerPartial P` there. -/
theorem relRoot_pow {k : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {G : ℂ → ℂ} {s : ℂ}
    (hs : 0 < s.re) (hG : G s ^ (2 ^ k) = xi s) :
    (G s * eulerRoot k P s) ^ (2 ^ k) = relCarrier P s := by
  rw [relCarrier, mul_pow, hG, eulerRoot_pow hP hs]

/-! ### §3 The collapse: the free reference frame is deck-invisible -/

/-- **The free reference frame contributes nothing to the deck class.**  It appears identically in
both chart roots as one global factor, and cancels in the chart ratio that defines the deck class
(`deckClass_mul_global`).  Since the reference root never vanishes, this holds at every basepoint,
unconditionally — there is no pinned annulus at which the free reference carries monodromy. -/
theorem relative_deckClass_eq (k : ℕ) (P : Finset ℕ) (G₁ G₂ : ℂ → ℂ) (pP pM : ℂ) :
    deckClass (fun z => G₁ z * eulerRoot k P z) (fun z => G₂ z * eulerRoot k P z) pP pM
      = deckClass G₁ G₂ pP pM :=
  deckClass_mul_global (eulerRoot_ne_zero k P pP) (eulerRoot_ne_zero k P pM)

/-- **The reference frame's own torsor is trivial.**  Its single-valued global root has deck class
`1`: the `{σ_p}` tower is free, carrying no monodromy of its own. -/
theorem reference_own_deckClass_one (k : ℕ) (P : Finset ℕ) (pP pM : ℂ) :
    deckClass (eulerRoot k P) (eulerRoot k P) pP pM = 1 := by
  rw [deckClass, div_self (eulerRoot_ne_zero k P pP), div_self (eulerRoot_ne_zero k P pM), div_one]

/-! ### §4 The relative deck class equals ξ's, exactly -/

/-- **The relative torsor is deck-isomorphic to ξ's own.**  For any local `2^k`-roots `G₁ G₂` of ξ
on the two slit charts around a zero `ρ₀`, the deck class of the reference-dressed roots equals ξ's
deck class `exp(2πi·m/2^k)`, `m = ord_{ρ₀} ξ` — the reference frame has moved nothing. -/
theorem relative_deckClass_eq_xi (ρ₀ : ℂ) (k : ℕ) (P : Finset ℕ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) → AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) →
      (∀ z ∈ chartR ρ₀ R, G₁ z ^ (2 ^ k) = xi z) →
      (∀ z ∈ chartL ρ₀ R, G₂ z ^ (2 ^ k) = xi z) →
      deckClass (fun z => G₁ z * eulerRoot k P z) (fun z => G₂ z * eulerRoot k P z)
          (ρ₀ + ((R / 2 : ℝ) : ℂ) * I) (ρ₀ - ((R / 2 : ℝ) : ℂ) * I)
        = exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ₀).toNat : ℕ) / ((2 ^ k : ℕ) : ℂ)) := by
  obtain ⟨R₀, hR₀, hclass⟩ := xi_deckClass ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  exact (relative_deckClass_eq k P G₁ G₂ _ _).trans
    (hclass hR hRle (pow_pos (by norm_num) k) hG₁ hG₂ hpG₁ hpG₂)

/-! ### §5 The collapse is circular: the relative torsor is `RHLadder k` itself -/

/-- **The relative torsor cannot break the tautology.**  It is trivial exactly when ξ's torsor is —
i.e. exactly the divisibility clause `2^k ∣ ord_{ρ₀} ξ` that `RHLadder k` quantifies over.  Measuring
ξ relative to the free `{σ_p}` reference frame returns ξ: the reference moves the equivalence
nowhere. -/
theorem relative_torsor_trivial_iff_ladder (ρ₀ : ℂ) (k : ℕ) (P : Finset ℕ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ₀ R) → AnalyticOnNhd ℂ G₂ (chartL ρ₀ R) →
      (∀ z ∈ chartR ρ₀ R, G₁ z ^ (2 ^ k) = xi z) →
      (∀ z ∈ chartL ρ₀ R, G₂ z ^ (2 ^ k) = xi z) →
      (deckClass (fun z => G₁ z * eulerRoot k P z) (fun z => G₂ z * eulerRoot k P z)
            (ρ₀ + ((R / 2 : ℝ) : ℂ) * I) (ρ₀ - ((R / 2 : ℝ) : ℂ) * I) = 1 ↔
        ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ₀) := by
  obtain ⟨R₀, hR₀, hiff⟩ := xi_deckClass_eq_one_iff_ladder_dvd ρ₀ k
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  rw [relative_deckClass_eq k P G₁ G₂]
  exact hiff hR hRle hG₁ hG₂ hpG₁ hpG₂

end RHTower
