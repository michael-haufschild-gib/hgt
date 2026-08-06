import GaloisForLFunctions.HTGeometry.RationalPoleOrder
import GaloisForLFunctions.HTGeometry.PolynomialShift

/-!
# A telescoped difference has no single-pole orbit

Assembling the pieces: the poles of a rational function along one integer orbit form a finite set,
that set has two jumps if it is nonempty, and at a jump one of the two terms of the telescoped
difference is regular while the other is not, so the difference has a pole there.  Two jumps give
two poles.

Hence if the telescoped difference has at most one pole on an orbit, the function has none there —
the discrete-residue obstruction to rational summability, in the form the atomic scaled-digamma
theorem uses.

The shift enters only through its effect on pole position, so it appears as the hypothesis that the
shifted function is regular exactly one step along.
-/

open scoped BigOperators

namespace GaloisForLFunctions

variable {K : Type*} [Field K]

/-! ## Regularity under negation and subtraction -/

theorem regularAt_neg_iff {a : RatFunc K} {w : K} : RegularAt (-a) w ↔ RegularAt a w := by
  constructor
  · intro h
    simpa using h.neg
  · exact RegularAt.neg

theorem not_regularAt_sub_of_not_regularAt {a b : RatFunc K} {w : K}
    (ha : ¬ RegularAt a w) (hb : RegularAt b w) : ¬ RegularAt (b - a) w := by
  intro hcon
  exact ha (by
    have : a = b - (b - a) := by ring
    rw [this]
    exact hb.sub hcon)

theorem not_regularAt_sub_of_not_regularAt' {a b : RatFunc K} {w : K}
    (ha : ¬ RegularAt a w) (hb : RegularAt b w) : ¬ RegularAt (a - b) w := by
  intro hcon
  refine not_regularAt_sub_of_not_regularAt ha hb ?_
  rw [show b - a = -(a - b) by ring]
  exact hcon.neg

/-! ## The finite pole set on an orbit -/

theorem finite_orbit_poles [CharZero K] (g : RatFunc K) (c : K) :
    {n : ℤ | ¬ RegularAt g (c + n)}.Finite := by
  refine Set.Finite.subset (finite_support_poleOrder_orbit g c) ?_
  intro n hn
  rw [Set.mem_setOf_eq] at hn
  rw [Function.mem_support]
  intro hzero
  exact hn ((regularAt_iff_poleOrder_eq_zero g (c + n)).mpr hzero)

/-! ## The obstruction -/

/-- **No single-pole orbit for a telescoped difference.**  If `gs` is regular exactly one step
along from `g`, and the difference `gs - g` has at most one pole on the orbit `c + ℤ`, then `g` is
regular at every point of that orbit. -/
theorem regularAt_orbit_of_telescoped_pole_subsingleton [CharZero K] (g gs : RatFunc K) (c : K)
    (hshift : ∀ w : K, RegularAt gs w ↔ RegularAt g (w + 1))
    (D : Set ℤ) (hD : ∀ n : ℤ, ¬ RegularAt (gs - g) (c + n) → n ∈ D)
    (hsub : D.Subsingleton) : ∀ n : ℤ, RegularAt g (c + n) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨n₀, hn₀⟩ := hcon
  set S : Finset ℤ := (finite_orbit_poles g c).toFinset with hS
  have hmemS : ∀ n : ℤ, n ∈ S ↔ ¬ RegularAt g (c + n) := by
    intro n
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hSne : S.Nonempty := ⟨n₀, (hmemS n₀).mpr hn₀⟩
  have hpole : ∀ n : ℤ, ¬ ((n ∈ S) ↔ (n + 1 ∈ S)) → ¬ RegularAt (gs - g) (c + n) := by
    intro n hjump
    have hstep : RegularAt gs (c + n) ↔ RegularAt g (c + n + 1) := hshift (c + n)
    have hcast : ((n : K) + 1) = ((n + 1 : ℤ) : K) := by push_cast; ring
    by_cases hn : n ∈ S
    · have hnot : n + 1 ∉ S := fun hcontra => hjump ⟨fun _ => hcontra, fun _ => hn⟩
      have hgs : RegularAt gs (c + n) := by
        rw [hstep, add_assoc, hcast]
        exact not_not.mp (fun h => hnot ((hmemS (n + 1)).mpr h))
      exact not_regularAt_sub_of_not_regularAt ((hmemS n).mp hn) hgs
    · have hyes : n + 1 ∈ S := by
        by_contra hcontra
        exact hjump ⟨fun h => absurd h hn, fun h => absurd h hcontra⟩
      have hgreg : RegularAt g (c + n) := not_not.mp fun h => hn ((hmemS n).mpr h)
      have hgspole : ¬ RegularAt gs (c + n) := by
        rw [hstep, add_assoc, hcast]
        exact (hmemS (n + 1)).mp hyes
      exact not_regularAt_sub_of_not_regularAt' hgspole hgreg
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_jumps S hSne
  exact hab (hsub (hD a (hpole a ha)) (hD b (hpole b hb)))

/-! ## A single orbit pole blocks summability -/

/-- **A rational function with exactly one pole on an integer orbit is not a telescoped
difference.**  This is the discrete-residue obstruction in the form the atomic scaled-digamma
theorem applies it: the combination produced by a hypothetical differential dependence has a single
pole in the class `-h_i/ω + ℤ`, so it cannot be rationally summable. -/
theorem not_telescoped_of_unique_orbit_pole [CharZero K] (r : RatFunc K) (p₀ : K)
    (hpole : ¬ RegularAt r p₀)
    (hunique : ∀ n : ℤ, n ≠ 0 → RegularAt r (p₀ + n)) :
    ¬ ∃ g gs : RatFunc K, (∀ w : K, RegularAt gs w ↔ RegularAt g (w + 1)) ∧ r = gs - g := by
  rintro ⟨g, gs, hshift, rfl⟩
  have hD : ∀ n : ℤ, ¬ RegularAt (gs - g) (p₀ + n) → n ∈ ({0} : Set ℤ) := by
    intro n hn
    by_contra hne
    exact hn (hunique n (by simpa using hne))
  have hreg := regularAt_orbit_of_telescoped_pole_subsingleton g gs p₀ hshift ({0} : Set ℤ) hD
    Set.subsingleton_singleton
  have h0 : RegularAt g p₀ := by simpa using hreg 0
  have h1 : RegularAt g (p₀ + 1) := by simpa using hreg 1
  exact hpole (((hshift p₀).mpr h1).sub h0)

end GaloisForLFunctions
