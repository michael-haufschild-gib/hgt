import GaloisForLFunctions.RHTower.WeldRateLattice
import GaloisForLFunctions.RHTower.DeckChargeCalculus

/-!
# Faithfulness dichotomy: which weld charges see the prime lattice

The weld obstruction carries two independent gradings.  The **flux** grading is the real conversion
constant `θ = log(base)`; it is the domain of `weldClassHom : ℝ ↪ H²(WeldGroup; ℝ)`, and the primes are
`ℤ`-linearly independent there (`primes_weld_class_indep` / `weldClass_indep_of_linIndep`).  The **order**
grading is the integer vanishing index, read by the deck charge `wCharge n : ℤ → ℤ/n`.

The question this module settles: *does a deck charge preserve the prime-flux independence, or collapse
it?*  The answer is a dichotomy governed entirely by the **torsion of the charge's target**, not by any
coarseness of a modulus:

* **Total collapse for every finite (torsion) charge.**  Any additive homomorphism
  `H²(WeldGroup; ℝ) →+ ZMod n` kills every real weld class `weldClassHom θ`, because `ℝ` is divisible
  and `ZMod n` is `n`-torsion (`real_addHom_zmod_eq_zero`).  Consequently the whole rank-`∞`
  independent prime lattice maps to `0` under any such charge (`prime_flux_charge_collapse`): the
  independence is entirely invisible to torsion charges.  This is not the modular quotient barrier of
  `DeciderBarrier`; it is a coefficient-ring phenomenon (divisible source, torsion target).

* **Faithfulness on the integer (order) channel.**  On integer welds the `2`-adic charge profile
  `idx ↦ (wCharge (2^k) idx)_k` is injective — it is the embedding `ℤ ↪ ℤ₂`
  (`wCharge_two_pow_profile_injective`).  So the order channel loses nothing: the collapse is confined
  to the transcendental flux channel.

The moral, made exact: the prime independence is a *real-cohomology* (divisible, flow-like) datum; a
deck charge is a *torsion* (discrete, constraint-like) datum; a discrete constraint cannot read a
divisible flow.  Faithfulness returns the instant the target is allowed to be non-torsion — witnessed
already by the injective `weldClassHom` into the torsion-free `H²(·; ℝ)`.
-/

noncomputable section

open scoped BigOperators

namespace GaloisForLFunctions
namespace RHTower

/-! ### The divisibility kill: every bounded-exponent (finite) charge annihilates the flux channel -/

/-- **A divisible source has no nonzero bounded-exponent character.**  If a target group `M` is
annihilated by a fixed `n ≠ 0` (`n • y = 0` for all `y`), then every additive homomorphism `ℝ →+ M`
is identically zero: `ℝ` is divisible, so `x = n • (x/n)`, and `φ x = n • φ(x/n) = 0`.  This is the
coefficient-level reason a torsion charge of bounded exponent cannot see a real weld class.  The
dividing line is *bounded exponent*, not torsion: a divisible torsion target (e.g. the circle `ℝ/ℤ`)
can carry nonzero characters. -/
theorem real_addHom_eq_zero_of_nsmul {M : Type*} [AddCommGroup M] {n : ℕ} (hn : n ≠ 0)
    (hM : ∀ y : M, n • y = 0) (φ : ℝ →+ M) (x : ℝ) : φ x = 0 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hx : x = n • (x / n) := by
    rw [nsmul_eq_mul]; field_simp
  calc φ x = φ (n • (x / n)) := by rw [← hx]
    _ = n • φ (x / n) := by rw [AddMonoidHom.map_nsmul]
    _ = 0 := hM (φ (x / n))

/-- **Every deck charge kills the flux.**  Specialization to `ZMod n`: every additive homomorphism
`ℝ →+ ZMod n` is zero (`ZMod n` is `n`-torsion). -/
theorem real_addHom_zmod_eq_zero {n : ℕ} [NeZero n] (φ : ℝ →+ ZMod n) (x : ℝ) : φ x = 0 :=
  real_addHom_eq_zero_of_nsmul (NeZero.ne n) (ZModModule.char_nsmul_eq_zero n) φ x

/-- **Flux invisibility.**  Every torsion-valued charge on the real weld cohomology annihilates every
weld class: a nonzero conversion constant `θ` still contributes `0` to any `ZMod n`-valued charge.
The composite `ℝ →(weldClassHom) H² →(φ) ZMod n` is a charge on `ℝ`, hence zero. -/
theorem weldClass_charge_invisible {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n) (θ : ℝ) :
    φ (weldClassHom θ) = 0 :=
  real_addHom_zmod_eq_zero (φ.comp weldClassHom) θ

/-- **Total collapse of the prime lattice.**  Under any `ZMod n`-valued charge on the weld
cohomology, every finitely-supported integer combination of the prime weld classes maps to `0`.  The
rank-`∞`, `ℤ`-independent prime family (`primes_weld_class_indep`) is collapsed to the single point `0`:
no torsion charge distinguishes any two prime combinations.  The independence lives entirely in the
divisible flux channel, off every deck charge's radar. -/
theorem prime_flux_charge_collapse {n : ℕ} [NeZero n]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ ZMod n)
    (c : Nat.Primes →₀ ℤ) :
    φ (c.sum fun p z => z • weldClassHom (Real.log (p : ℕ))) = 0 := by
  have hcollapse : (c.sum fun p z => z • weldClassHom (Real.log (p : ℕ)))
      = weldClassHom (c.sum fun p z => z • Real.log (p : ℕ)) := by
    rw [map_finsuppSum]
    simp_rw [map_zsmul]
  rw [hcollapse]
  exact weldClass_charge_invisible φ _

/-- **Collapse under every finite charge.**  A finite abelian target has bounded exponent
(`Nat.card M • y = 0`), so every additive homomorphism `ℝ →+ M` from the flux channel is zero on all
weld classes — not merely the deck charges `ZMod n`, but *every* finite-valued charge whatsoever. -/
theorem weldClass_finite_charge_invisible {M : Type*} [AddCommGroup M] [Fintype M] [Nonempty M]
    (φ : secondConstraintCohomology (G := WeldGroup) (A := ℝ) →+ M) (θ : ℝ) :
    φ (weldClassHom θ) = 0 :=
  real_addHom_eq_zero_of_nsmul Fintype.card_ne_zero (fun _ => card_nsmul_eq_zero)
    (φ.comp weldClassHom) θ

/-! ### The flux channel is faithful for a torsion-free target -/

/-- The prime-flux assembly as an additive homomorphism `(Nat.Primes →₀ ℤ) →+ H²(WeldGroup; ℝ)`:
`c ↦ Σ_p c(p) • [weld_{log p}]`. -/
def primeFluxHom : (Nat.Primes →₀ ℤ) →+ secondConstraintCohomology (G := WeldGroup) (A := ℝ) :=
  Finsupp.liftAddHom (fun p : Nat.Primes =>
    AddMonoidHom.mk' (fun z : ℤ => z • weldClassHom (Real.log (p : ℕ)))
      (fun a b => add_zsmul _ a b))

theorem primeFluxHom_apply (c : Nat.Primes →₀ ℤ) :
    primeFluxHom c = c.sum fun p z => z • weldClassHom (Real.log (p : ℕ)) := rfl

/-- **The flux channel is faithful.**  Into the torsion-free target `H²(WeldGroup; ℝ)`, distinct
integer combinations of prime weld classes are distinct: `primeFluxHom` is injective.  This is the
faithful counterpart of `prime_flux_charge_collapse` on the *same* lattice — the prime independence is
fully present, only invisible to bounded-exponent charges.  It repackages `primes_weld_class_indep`. -/
theorem primeFluxHom_injective : Function.Injective primeFluxHom := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  rw [primeFluxHom_apply] at hc
  exact weldClass_indep_of_linIndep primeLog_linearIndependent c hc

/-! ### The order channel is faithful: the 2-adic charge profile embeds `ℤ` -/

/-- A power of two is nonzero as a modulus. -/
instance neZero_two_pow (k : ℕ) : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩

/-- **An integer divisible by every power of two is zero.**  The Archimedean bound: a nonzero integer
`m` has `|m| < 2^K` for some `K`, contradicting `2^K ∣ m`. -/
theorem eq_zero_of_forall_two_pow_dvd {m : ℤ} (h : ∀ k : ℕ, (2 : ℤ) ^ k ∣ m) : m = 0 := by
  by_contra hne
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |m| < 2 ^ K := by
    obtain ⟨K, hK⟩ := exists_nat_gt (|m| : ℤ)
    refine ⟨K, lt_of_lt_of_le hK ?_⟩
    calc (K : ℤ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
      _ = 2 ^ K := rfl
  have hdvd : (2 : ℤ) ^ K ∣ |m| := (dvd_abs _ _).mpr (h K)
  have hle : (2 : ℤ) ^ K ≤ |m| := Int.le_of_dvd (abs_pos.mpr hne) hdvd
  exact absurd hle (not_le.mpr hK)

/-- **The order channel is faithful.**  The `2`-adic deck-charge profile `idx ↦ (wCharge (2^k) idx)_k`
is injective: two integer indices with the same charge at every depth are equal.  This is the profinite
embedding `ℤ ↪ ℤ₂` — the order grading loses nothing, so the flux collapse is confined to the
transcendental channel. -/
theorem wCharge_two_pow_profile_injective :
    Function.Injective (fun idx : ℤ => (fun k : ℕ => _root_.RHTower.wCharge (2 ^ k) idx)) := by
  intro i j h
  have hdvd : ∀ k : ℕ, (2 : ℤ) ^ k ∣ (i - j) := by
    intro k
    have hk : _root_.RHTower.wCharge (2 ^ k) i = _root_.RHTower.wCharge (2 ^ k) j := congrFun h k
    have hz : _root_.RHTower.wCharge (2 ^ k) (i - j) = 0 := by
      have : _root_.RHTower.wCharge (2 ^ k) (i - j)
          = _root_.RHTower.wCharge (2 ^ k) i - _root_.RHTower.wCharge (2 ^ k) j := by
        rw [sub_eq_add_neg, _root_.RHTower.wCharge_add, _root_.RHTower.wCharge_neg, sub_eq_add_neg]
      rw [this, hk, sub_self]
    have := (_root_.RHTower.wCharge_eq_zero_iff (n := 2 ^ k) (i - j)).mp hz
    simpa using this
  have : i - j = 0 := eq_zero_of_forall_two_pow_dvd hdvd
  linarith

end RHTower
end GaloisForLFunctions
