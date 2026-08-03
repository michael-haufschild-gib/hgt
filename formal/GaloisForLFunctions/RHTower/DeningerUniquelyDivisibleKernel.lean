import GaloisForLFunctions.RHTower.DeningerDivisibleFiberFiniteCoverInvariance

/-!
# Unique divisibility passes to the kernel over a torsion-free quotient

If every element of `R` has a unique `n`-th root and `f : R →* A` lands in a torsion-free group,
then `ker f` again has unique `n`-th roots: the root of an element of the kernel is forced into
the kernel, because its image is an `n`-th root of `1`.

Combined with the finite-cover invariance of a divisible kernel, this gives the two group-theoretic
clauses of the Baumslag free-rational Milnor packet: the kernel is uniquely divisible, and it has
no nontrivial finite quotient.

* `DeningerUniquelyDivisible` is the unique-root property.
* `deningerKer_uniquelyDivisible` is the descent to the kernel.
* `deningerKer_noFiniteQuotient` is the resulting triviality of finite quotients.
-/

namespace RHTower

section UniquelyDivisible

universe u v

variable {R : Type u} {A : Type v} [Group R] [Group A]

/-- Every element has a unique `n`-th root for every `n ≥ 1`. -/
def DeningerUniquelyDivisible (R : Type u) [Group R] : Prop :=
  ∀ n : ℕ, 0 < n → ∀ r : R, ∃! x : R, x ^ n = r

/-- Unique divisibility implies divisibility. -/
theorem deningerPowerDivisible_of_uniquelyDivisible
    (h : DeningerUniquelyDivisible R) : DeningerPowerDivisible R := by
  intro n hn r
  obtain ⟨x, hx, -⟩ := h n hn r
  exact ⟨x, hx⟩

/-- **Unique roots descend to the kernel.**  If the target is torsion-free, the `n`-th root of an
element of the kernel lies in the kernel, and it is unique there. -/
theorem deningerKer_uniquelyDivisible (f : R →* A)
    (hR : DeningerUniquelyDivisible R)
    (hA : ∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1) :
    DeningerUniquelyDivisible (f.ker : Subgroup R) := by
  intro n hn k
  obtain ⟨x, hx, huniq⟩ := hR n hn (k : R)
  have hxk : x ∈ f.ker := by
    have : f x ^ n = 1 := by
      rw [← map_pow, hx]
      exact k.2
    exact hA (f x) n hn this
  refine ⟨⟨x, hxk⟩, ?_, ?_⟩
  · exact Subtype.ext (by simpa using hx)
  · intro y hy
    refine Subtype.ext ?_
    refine huniq (y : R) ?_
    simpa using congrArg (Subtype.val) hy

/-- **No finite quotient.**  The kernel of a homomorphism from a uniquely divisible group to a
torsion-free group admits no nontrivial homomorphism to a finite group. -/
theorem deningerKer_noFiniteQuotient (f : R →* A)
    (hR : DeningerUniquelyDivisible R)
    (hA : ∀ (a : A) (n : ℕ), 0 < n → a ^ n = 1 → a = 1) :
    DeningerNoFiniteQuotient (f.ker : Subgroup R) :=
  deningerNoFiniteQuotient_of_powerDivisible
    (deningerPowerDivisible_of_uniquelyDivisible (deningerKer_uniquelyDivisible f hR hA))

end UniquelyDivisible

end RHTower
