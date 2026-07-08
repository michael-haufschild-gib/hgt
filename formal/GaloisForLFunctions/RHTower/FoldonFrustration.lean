/-
Frustration of a reflection-symmetric zero configuration, and how deep the mod-`2^k` deck ladder
must climb to see it.

The frustration of a configuration is the integer total order `Σ mᵢ` of its off-line zeros — the
same integer index whose mod-`2^k` reduction is the deck class of the `2^k`-rung
(`SignatureParity`).  Off-line zeros carry reflection symmetries (the functional equation `s ↦ 1−s`
and complex conjugation `s ↦ s̄`), and a configuration invariant under a *free* action of a finite
symmetry group `G` has total order divisible by `|G|`.  When `|G| = 2^k`, the frustration is
divisible by `2^k`, so its deck class is trivial at every rung `j ≤ k`: the ladder is **blind** to a
reflection-symmetric frustration up to its symmetry depth, and a single `2^k`-orbit first becomes
visible at rung `k+1` (its deck class there is `−1`).

The general divisibility `|G| ∣ Σ mᵢ` for a free action is the enabling tool (an orbit-decomposition
fact: each orbit has `|G|` points and `m` is constant on it).  The residual question the route leaves
open — whether the frustration recursion up the line is contractive (short-range folding) or only
marginally so (long-range) — is analytic and not reachable here; this module fixes the algebra of the
symmetry-depth blindness exactly.
-/
import GaloisForLFunctions.RHTower.SignatureParity

open scoped BigOperators
open Complex MulAction

namespace RHTower

/-! ### §1 Free-action divisibility of an invariant weighted sum -/

/-- **A free finite-group action divides the invariant weighted sum.**  If a finite group `G` acts
freely on a finite type `α` and `m : α → ℕ` is `G`-invariant, then `|G| ∣ Σ_a m a`: the type
decomposes into orbits, each with exactly `|G|` points (free ⟹ trivial stabilizer) on which `m` is
constant, so each orbit contributes `|G|·m(rep)`. -/
theorem card_group_dvd_weighted_sum {G α : Type*} [Group G] [Fintype G] [Fintype α]
    [MulAction G α] [DecidableEq α]
    (hfree : ∀ (g : G) (a : α), g • a = a → g = 1)
    (m : α → ℕ) (hm : ∀ (g : G) (a : α), m (g • a) = m a) :
    Fintype.card G ∣ ∑ a, m a := by
  classical
  have horbcard : ∀ b : α, Fintype.card (orbit G b) = Fintype.card G := by
    intro b
    have hstab : Fintype.card (stabilizer G b) = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨1, fun g => Subtype.ext (hfree g.1 b g.2)⟩
    have hkey := card_orbit_mul_card_stabilizer_eq_card_group G b
    rw [hstab, mul_one] at hkey
    exact hkey
  have hconst : ∀ (b : α) (x : orbit G b), m (x : α) = m b := by
    intro b x
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]; exact hm g b
  rw [Fintype.sum_equiv (selfEquivSigmaOrbits G α) m
      (fun p => m ((selfEquivSigmaOrbits G α).symm p)) (fun a => by simp)]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have hc : ∀ b : orbit G ω.out, m ((selfEquivSigmaOrbits G α).symm ⟨ω, b⟩) = m ω.out := by
    intro b
    rw [show ((selfEquivSigmaOrbits G α).symm ⟨ω, b⟩) = (b : α) from rfl]
    exact hconst ω.out b
  rw [Finset.sum_congr rfl (fun b _ => hc b), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, horbcard]
  exact dvd_mul_right _ _

/-! ### §2 Ladder-depth arithmetic -/

/-- Divisibility by `2^k` makes the deck class trivial at rung `k`: `2^k ∣ index ⟹ deckRed(2^k) = 1`. -/
theorem deckRed_eq_one_of_two_pow_dvd (k : ℕ) {idx : ℤ} (h : (2 : ℤ) ^ k ∣ idx) :
    deckRed (2 ^ k) idx = 1 := by
  rw [deckRed_eq_one_iff (by positivity : 0 < 2 ^ k)]
  exact_mod_cast h

/-- **A single `2^k`-orbit first becomes visible at rung `k+1`.**  Its deck class there is `−1`:
`deckRed(2^{k+1})(2^k) = exp(πi) = −1`. -/
theorem deckRed_two_pow_next_visible (k : ℕ) : deckRed (2 ^ (k + 1)) ((2 : ℤ) ^ k) = -1 := by
  have hexp : 2 * (Real.pi : ℂ) * I * (((2 : ℤ) ^ k : ℤ) : ℂ) / ((2 ^ (k + 1) : ℕ) : ℂ)
      = (Real.pi : ℂ) * I := by
    have h2 : ((2 ^ (k + 1) : ℕ) : ℂ) = 2 * (2 : ℂ) ^ k := by push_cast; ring
    have hk : (((2 : ℤ) ^ k : ℤ) : ℂ) = (2 : ℂ) ^ k := by push_cast; ring
    rw [h2, hk]
    have hne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  rw [deckRed, hexp, Complex.exp_pi_mul_I]

/-- Below the symmetry depth the ladder is blind: `2^k ∣ index` makes the deck class trivial at every
rung `j ≤ k`. -/
theorem deckRed_eq_one_below_depth (k : ℕ) {idx : ℤ} (hdvd : (2 : ℤ) ^ k ∣ idx)
    {j : ℕ} (hj : j ≤ k) : deckRed (2 ^ j) idx = 1 :=
  deckRed_eq_one_of_two_pow_dvd j (dvd_trans (pow_dvd_pow 2 hj) hdvd)

/-! ### §3 Frustration and the symmetry-depth blindness -/

/-- The frustration of a configuration: the integer total order of its zeros. -/
def foldonFrustration {ι : Type*} (s : Finset ι) (m : ι → ℕ) : ℤ := ((∑ i ∈ s, m i : ℕ) : ℤ)

/-- **The parity rung is blind to a reflection pair.**  A configuration invariant under a
fixed-point-free reflection involution matching multiplicities has even frustration, so its deck
class value at rung `1` is trivial: the mod-2 flux is blind to reflection-paired off-line zeros. -/
theorem frustration_invisible_rung_one {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (σ : ι → ι) (m : ι → ℕ)
    (hσs : ∀ i ∈ s, σ i ∈ s) (hσσ : ∀ i ∈ s, σ (σ i) = i)
    (hfix : ∀ i ∈ s, σ i ≠ i) (hm : ∀ i ∈ s, m (σ i) = m i) :
    deckRed 2 (foldonFrustration s m) = 1 := by
  rw [foldonFrustration]
  exact reflection_paired_deckRed_two_eq_one s σ m hσs hσσ hfix hm

/-- **The ladder is blind up to the reflection symmetry depth.**  A configuration invariant under a
*free* action of a finite reflection group `G` of order `2^k`, with matching multiplicities, has
frustration divisible by `2^k`; hence its deck class is trivial at every rung `j ≤ k`.  The deeper the
reflection symmetry of the off-line buckling, the higher the ladder must climb to detect it. -/
theorem frustration_invisible_below_reflection_depth {G α : Type*} [Group G] [Fintype G]
    [Fintype α] [MulAction G α] [DecidableEq α] {k : ℕ} (hcard : Fintype.card G = 2 ^ k)
    (hfree : ∀ (g : G) (a : α), g • a = a → g = 1)
    (m : α → ℕ) (hm : ∀ (g : G) (a : α), m (g • a) = m a)
    {j : ℕ} (hj : j ≤ k) :
    deckRed (2 ^ j) (foldonFrustration Finset.univ m) = 1 := by
  have hdvd : (2 : ℤ) ^ k ∣ foldonFrustration Finset.univ m := by
    have h := card_group_dvd_weighted_sum hfree m hm
    rw [hcard] at h
    unfold foldonFrustration
    exact_mod_cast h
  exact deckRed_eq_one_below_depth k hdvd hj

/-- **The first rung that sees a pure `2^k`-orbit.**  A configuration whose frustration is a single
reflection orbit of size `2^k` is invisible to rungs `≤ k` but visible at rung `k+1`, where its deck
class is `−1` — the exact resolution the ladder needs to resolve a symmetry-depth-`k` frustration. -/
theorem frustration_orbit_visibility (k : ℕ) :
    (∀ j ≤ k, deckRed (2 ^ j) ((2 : ℤ) ^ k) = 1) ∧ deckRed (2 ^ (k + 1)) ((2 : ℤ) ^ k) = -1 :=
  ⟨fun _ hj => deckRed_eq_one_below_depth k dvd_rfl hj, deckRed_two_pow_next_visible k⟩

end RHTower
