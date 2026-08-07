import GaloisForLFunctions.HTGeometry.CDGABarCancel

/-!
# The double sum of the bar square

The square of the bar differential on three or more factors is a double sum: an outer split of the
target degree and, inside it, either a further split of the first part — that is the head applied
twice — or a split of the second part — that is the head after the tail.  Both are indexed by the
triples of degrees the two multiplications consume, and both read the same component of the
argument, so they can be compared term by term.

* `HTGeometry.BarTriple` : the triples of degrees two multiplications consume.
* `HTGeometry.barTripleOfFirst`, `HTGeometry.barTripleOfSecond` : the two reindexings.
* `HTGeometry.barTele` : the component of the argument both sides read.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  (Z : ℕ → Type u) [∀ n, AddCommGroup (Z n)] [∀ n, Module R (Z n)]

/-- The ways a shifted degree is consumed by two multiplications of three adjacent factors. -/
abbrev BarTriple (c : ℕ) : Type := {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + t.2.2 + 2 = c}

/-- An outer split together with a split of its first part is a triple. -/
def barTripleOfFirst {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.1) : BarTriple c :=
  ⟨(s.2.1.1, s.2.1.2, s.1.1.2), by
    obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
    have h1 : a + a' + 1 = c := hs
    have h2 : v + v' + 1 = a := hv
    show v + v' + a' + 2 = c
    omega⟩

/-- A triple is an outer split together with a split of its first part. -/
def barFirstOfTriple {c : ℕ} (t : BarTriple c) : Σ s : BarSplit c, BarSplit s.1.1 :=
  ⟨⟨(t.1.1 + t.1.2.1 + 1, t.1.2.2), by
    obtain ⟨⟨a, b, d⟩, ht⟩ := t
    have h : a + b + d + 2 = c := ht
    show a + b + 1 + d + 1 = c
    omega⟩, ⟨(t.1.1, t.1.2.1), rfl⟩⟩

/-- An outer split together with a split of its second part is a triple. -/
def barTripleOfSecond {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.2) : BarTriple c :=
  ⟨(s.1.1.1, s.2.1.1, s.2.1.2), by
    obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
    have h1 : a + a' + 1 = c := hs
    have h2 : v + v' + 1 = a' := hv
    show a + v + v' + 2 = c
    omega⟩

/-- A triple is an outer split together with a split of its second part. -/
def barSecondOfTriple {c : ℕ} (t : BarTriple c) : Σ s : BarSplit c, BarSplit s.1.2 :=
  ⟨⟨(t.1.1, t.1.2.1 + t.1.2.2 + 1), by
    obtain ⟨⟨a, b, d⟩, ht⟩ := t
    have h : a + b + d + 2 = c := ht
    show a + (b + d + 1) + 1 = c
    omega⟩, ⟨(t.1.2.1, t.1.2.2), rfl⟩⟩

theorem barTripleOfFirst_barFirstOfTriple {c : ℕ} (t : BarTriple c) :
    barTripleOfFirst (barFirstOfTriple t) = t := by
  obtain ⟨⟨a, b, d⟩, h⟩ := t
  rfl

theorem barFirstOfTriple_barTripleOfFirst {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.1) :
    barFirstOfTriple (barTripleOfFirst s) = s := by
  obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
  have ha : v + v' + 1 = a := hv
  subst ha
  rfl

theorem barTripleOfSecond_barSecondOfTriple {c : ℕ} (t : BarTriple c) :
    barTripleOfSecond (barSecondOfTriple t) = t := by
  obtain ⟨⟨a, b, d⟩, h⟩ := t
  rfl

theorem barSecondOfTriple_barTripleOfSecond {c : ℕ} (s : Σ s : BarSplit c, BarSplit s.1.2) :
    barSecondOfTriple (barTripleOfSecond s) = s := by
  obtain ⟨⟨⟨a, a'⟩, hs⟩, ⟨⟨v, v'⟩, hv⟩⟩ := s
  have ha : v + v' + 1 = a' := hv
  subst ha
  rfl

/-- **The component of the argument that both halves of the square read**, with its three shifted
factors separated. -/
noncomputable def barTele (u u' w e : ℕ) :
    TensorProduct R (barShiftFamily ε u)
        (TensorCarrier (R := R) (barShiftFamily ε)
          (TensorCarrier (R := R) (barShiftFamily ε) Z) (u' + (w + e)))
      →ₗ[R] TensorProduct R (barShiftFamily ε u)
        (TensorProduct R (barShiftFamily ε u') (TensorProduct R (barShiftFamily ε w) (Z e))) :=
  TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u))
    ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε u'))
        (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = w + e} =>
          TensorProduct R (barShiftFamily ε q.1.1) (Z q.1.2)) ⟨(w, e), rfl⟩)).comp
      (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = u' + (w + e)} =>
        TensorProduct R (barShiftFamily ε q.1.1)
          (TensorCarrier (R := R) (barShiftFamily ε) Z q.1.2)) ⟨(u', w + e), rfl⟩))

end GaloisForLFunctions.HTGeometry
