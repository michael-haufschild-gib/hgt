import Mathlib

/-!
# §VII (14): lifting a function on the quotient to the total space

§VII (14) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "We let `f` be a smooth compactly supported function on `J_S` such that
  `∑_{q ∈ O_S^*} f(q g) = h(g)` for all `g ∈ C_S`.  The existence of such an `f` follows from the
  discreteness of `O_S^*` in `J_S`."

Discreteness enters only through the existence of a strict fundamental domain: if every point has
exactly one translate in `s`, then the restriction of `h` to `s` is such an `f`, and the sum has a
single non-zero term.  That is proved here for an arbitrary group action, in both the `•` form and
the multiplicative form Connes writes.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **§VII (14).**  The restriction of an invariant function to a strict fundamental domain
periodizes back to it. -/
theorem connes_periodization_lift {G Γ : Type*} [Group Γ] [MulAction Γ G] {s : Set G}
    (hs : ∀ g : G, ∃! γ : Γ, γ • g ∈ s) {h : G → ℂ}
    (hinv : ∀ (γ : Γ) (g : G), h (γ • g) = h g) (g : G) :
    (∑' γ : Γ, Set.indicator s h (γ • g)) = h g := by
  obtain ⟨γ₀, hγ₀, huniq⟩ := hs g
  have hsingle : ∀ γ : Γ, γ ≠ γ₀ → Set.indicator s h (γ • g) = 0 := by
    intro γ hγ
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hγ (huniq γ hmem)
  rw [tsum_eq_single γ₀ hsingle, Set.indicator_of_mem hγ₀, hinv]

/-- **§VII (14), in Connes' multiplicative notation.**  For a discrete subgroup given by an index
family `q : Γ → G` acting by multiplication, `f = 1_s · h` satisfies `∑_γ f(q γ · g) = h(g)`. -/
theorem connes_periodization_lift_mul {G Γ : Type*} [Group G] [Group Γ] {ι : Γ → G} {s : Set G}
    (hs : ∀ g : G, ∃! γ : Γ, ι γ * g ∈ s) {h : G → ℂ}
    (hinv : ∀ (γ : Γ) (g : G), h (ι γ * g) = h g) (g : G) :
    (∑' γ : Γ, Set.indicator s h (ι γ * g)) = h g := by
  obtain ⟨γ₀, hγ₀, huniq⟩ := hs g
  have hsingle : ∀ γ : Γ, γ ≠ γ₀ → Set.indicator s h (ι γ * g) = 0 := by
    intro γ hγ
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hγ (huniq γ hmem)
  rw [tsum_eq_single γ₀ hsingle, Set.indicator_of_mem hγ₀, hinv]

/-- The lift is supported in the fundamental domain, which is Connes' "compactly supported"
requirement once the fundamental domain is chosen relatively compact. -/
theorem connes_periodization_lift_support {G : Type*} {s : Set G} {h : G → ℂ} {x : G}
    (hx : x ∉ s) : Set.indicator s h x = 0 :=
  Set.indicator_of_notMem hx h

end

end GaloisForLFunctions.RHTower
