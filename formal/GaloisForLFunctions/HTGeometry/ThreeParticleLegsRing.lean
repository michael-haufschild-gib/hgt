import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basis

/-!
# Three-particle tensor legs over an arbitrary commutative ring

A two-particle matrix acts on the first two or on the last two factors of a triple tensor product.
These two embeddings are the only structure the Sutherland linearisation of a regular braid family
needs, and they make sense over any commutative ring.

The key rigidity is the kernel of the identity Sutherland map: if the two embeddings of a
two-particle matrix agree on the triple product, that matrix is a scalar.  Three instantiations of
the entrywise identity give it — vanishing off the diagonal in each label separately, then
constancy along the diagonal.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {κ : Type*} [DecidableEq κ] {R : Type*} [CommRing R]

/-- Right-associated triple tensor index. -/
abbrev TripleIndex (κ : Type*) := κ × (κ × κ)

/-- A two-particle matrix acting on the first two tensor factors. -/
def legLeft (A : Matrix (κ × κ) (κ × κ) R) :
    Matrix (TripleIndex κ) (TripleIndex κ) R :=
  Matrix.of fun i j => A (i.1, i.2.1) (j.1, j.2.1) * (1 : Matrix κ κ R) i.2.2 j.2.2

/-- A two-particle matrix acting on the last two tensor factors. -/
def legRight (A : Matrix (κ × κ) (κ × κ) R) :
    Matrix (TripleIndex κ) (TripleIndex κ) R :=
  Matrix.of fun i j => (1 : Matrix κ κ R) i.1 j.1 * A i.2 j.2

@[simp]
theorem legLeft_apply (A : Matrix (κ × κ) (κ × κ) R) (i j : TripleIndex κ) :
    legLeft A i j = A (i.1, i.2.1) (j.1, j.2.1) * (1 : Matrix κ κ R) i.2.2 j.2.2 := rfl

@[simp]
theorem legRight_apply (A : Matrix (κ × κ) (κ × κ) R) (i j : TripleIndex κ) :
    legRight A i j = (1 : Matrix κ κ R) i.1 j.1 * A i.2 j.2 := rfl

@[simp]
theorem legLeft_one : legLeft (1 : Matrix (κ × κ) (κ × κ) R) = 1 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  by_cases hc : c = c'
  · subst hc
    by_cases hab : (a, b) = (a', b')
    · have ha : a = a' := congrArg Prod.fst hab
      have hb : b = b' := congrArg Prod.snd hab
      subst ha; subst hb
      simp
    · have hne : ((a, b, c) : TripleIndex κ) ≠ (a', b', c) := by
        intro h
        exact hab (by
          have h1 : a = a' := congrArg Prod.fst h
          have h2 : b = b' := congrArg (fun z => z.2.1) h
          simp [h1, h2])
      simp [hab, hne]
  · have hne : ((a, b, c) : TripleIndex κ) ≠ (a', b', c') := by
      intro h
      exact hc (congrArg (fun z => z.2.2) h)
    simp [hc, hne]

@[simp]
theorem legRight_one : legRight (1 : Matrix (κ × κ) (κ × κ) R) = 1 := by
  ext ⟨a, b, c⟩ ⟨a', b', c'⟩
  by_cases ha : a = a'
  · subst ha
    by_cases hbc : (b, c) = (b', c')
    · have h1 : b = b' := congrArg Prod.fst hbc
      have h2 : c = c' := congrArg Prod.snd hbc
      subst h1; subst h2
      simp
    · have hne : ((a, b, c) : TripleIndex κ) ≠ (a, b', c') := by
        intro h
        exact hbc (congrArg Prod.snd h)
      simp [hbc, hne]
  · have hne : ((a, b, c) : TripleIndex κ) ≠ (a', b', c') := by
      intro h
      exact ha (congrArg Prod.fst h)
    simp [ha, hne]

theorem legLeft_add (A B : Matrix (κ × κ) (κ × κ) R) :
    legLeft (A + B) = legLeft A + legLeft B := by
  ext i j; simp [add_mul]

theorem legRight_add (A B : Matrix (κ × κ) (κ × κ) R) :
    legRight (A + B) = legRight A + legRight B := by
  ext i j; simp [mul_add]

theorem legLeft_smul (c : R) (A : Matrix (κ × κ) (κ × κ) R) :
    legLeft (c • A) = c • legLeft A := by
  ext i j; simp [mul_assoc]

theorem legRight_smul (c : R) (A : Matrix (κ × κ) (κ × κ) R) :
    legRight (c • A) = c • legRight A := by
  ext i j; simp [mul_left_comm]

/-- **Kernel of the identity Sutherland map.**  If the two tensor embeddings of a two-particle
matrix agree, the matrix is a scalar multiple of the identity. -/
theorem eq_smul_one_of_legRight_eq_legLeft [Nonempty κ]
    {Y : Matrix (κ × κ) (κ × κ) R} (h : legRight Y = legLeft Y) :
    ∃ c : R, Y = c • 1 := by
  obtain ⟨a₀⟩ := ‹Nonempty κ›
  have H : ∀ a b c a' b' c' : κ,
      (1 : Matrix κ κ R) a a' * Y (b, c) (b', c') =
        Y (a, b) (a', b') * (1 : Matrix κ κ R) c c' := by
    intro a b c a' b' c'
    exact congrFun (congrFun h (a, b, c)) (a', b', c')
  have hsecond : ∀ u v u' v' : κ, v ≠ v' → Y (u, v) (u', v') = 0 := by
    intro u v u' v' hv
    have := H a₀ u v a₀ u' v'
    simpa [Matrix.one_apply, hv] using this
  have hfirst : ∀ u v u' v' : κ, u ≠ u' → Y (u, v) (u', v') = 0 := by
    intro u v u' v' hu
    have := H u v a₀ u' v' a₀
    simpa [Matrix.one_apply, hu] using this.symm
  have hdiag : ∀ a b c : κ, Y (b, c) (b, c) = Y (a, b) (a, b) := by
    intro a b c
    have := H a b c a b c
    simpa [Matrix.one_apply] using this
  refine ⟨Y (a₀, a₀) (a₀, a₀), ?_⟩
  ext ⟨u, v⟩ ⟨u', v'⟩
  by_cases huv : ((u, v) : κ × κ) = (u', v')
  · have hu : u = u' := congrArg Prod.fst huv
    have hv : v = v' := congrArg Prod.snd huv
    subst hu; subst hv
    have h1 : Y (u, v) (u, v) = Y (a₀, u) (a₀, u) := hdiag a₀ u v
    have h2 : Y (a₀, u) (a₀, u) = Y (a₀, a₀) (a₀, a₀) := hdiag a₀ a₀ u
    simp [h1, h2]
  · have hne : u ≠ u' ∨ v ≠ v' := by
      by_cases hu : u = u'
      · exact Or.inr fun hv => huv (by simp [hu, hv])
      · exact Or.inl hu
    rcases hne with hu | hv
    · simp [huv, hfirst u v u' v' hu]
    · simp [huv, hsecond u v u' v' hv]

end GaloisForLFunctions.HTGeometry
