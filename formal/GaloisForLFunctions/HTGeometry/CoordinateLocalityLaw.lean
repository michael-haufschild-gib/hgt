import GaloisForLFunctions.HTGeometry.SpectralCausality

/-!
# Coordinate locality: closure properties and the factorization law

Locality of a configuration function on a coordinate set is the standing hypothesis of the
spectral-causality contrast theorems, and it was consumed everywhere and produced nowhere.  It is
in fact an entirely structural condition: it is monotone in the coordinate set, closed under
composition, sums and products, holds for constants and coordinate evaluations, and — the sharp
statement — a function is local on `S` exactly when it factors through the restriction of
configurations to `S`.

The factorization criterion is what makes the interface usable: to produce locality one exhibits
the factored function, and the criterion returns the hypothesis the causality theorems consume.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {ι A R R' : Type*}

/-! ## Structural closure -/

/-- Every configuration function is local on all coordinates. -/
theorem coordinateLocalOn_univ (f : (ι → A) → R) :
    CoordinateLocalOn (Set.univ : Set ι) f := by
  intro x y h
  have hxy : x = y := funext fun i => h i (Set.mem_univ i)
  rw [hxy]

/-- Constants are local on every coordinate set, in particular on the empty one. -/
theorem coordinateLocalOn_const (S : Set ι) (r : R) :
    CoordinateLocalOn S (fun _ : ι → A => r) :=
  fun _ _ _ => rfl

/-- Locality is monotone in the coordinate set. -/
theorem CoordinateLocalOn.mono {S T : Set ι} {f : (ι → A) → R}
    (hf : CoordinateLocalOn S f) (hST : S ⊆ T) :
    CoordinateLocalOn T f :=
  fun x y h => hf x y fun i hi => h i (hST hi)

/-- Evaluation at a coordinate is local on that single coordinate. -/
theorem coordinateLocalOn_apply (i : ι) :
    CoordinateLocalOn ({i} : Set ι) (fun x : ι → A => x i) :=
  fun _ _ h => h i rfl

/-- Locality passes through any post-composition. -/
theorem CoordinateLocalOn.comp {S : Set ι} {f : (ι → A) → R}
    (hf : CoordinateLocalOn S f) (g : R → R') :
    CoordinateLocalOn S (fun x => g (f x)) :=
  fun x y h => congrArg g (hf x y h)

theorem CoordinateLocalOn.add [Add R] {S : Set ι} {f g : (ι → A) → R}
    (hf : CoordinateLocalOn S f) (hg : CoordinateLocalOn S g) :
    CoordinateLocalOn S (fun x => f x + g x) := by
  intro x y h
  show f x + g x = f y + g y
  rw [hf x y h, hg x y h]

theorem CoordinateLocalOn.mul [Mul R] {S : Set ι} {f g : (ι → A) → R}
    (hf : CoordinateLocalOn S f) (hg : CoordinateLocalOn S g) :
    CoordinateLocalOn S (fun x => f x * g x) := by
  intro x y h
  show f x * g x = f y * g y
  rw [hf x y h, hg x y h]

theorem CoordinateLocalOn.neg [Neg R] {S : Set ι} {f : (ι → A) → R}
    (hf : CoordinateLocalOn S f) :
    CoordinateLocalOn S (fun x => -f x) := by
  intro x y h
  show -f x = -f y
  rw [hf x y h]

theorem CoordinateLocalOn.sub [Sub R] {S : Set ι} {f g : (ι → A) → R}
    (hf : CoordinateLocalOn S f) (hg : CoordinateLocalOn S g) :
    CoordinateLocalOn S (fun x => f x - g x) := by
  intro x y h
  show f x - g x = f y - g y
  rw [hf x y h, hg x y h]

/-- A finite sum of functions local on one coordinate set is local on it. -/
theorem coordinateLocalOn_finsetSum [AddCommMonoid R] {S : Set ι} {κ : Type*}
    (s : Finset κ) (term : κ → (ι → A) → R)
    (h : ∀ c ∈ s, CoordinateLocalOn S (term c)) :
    CoordinateLocalOn S (fun x => ∑ c ∈ s, term c x) := by
  intro x y hxy
  exact Finset.sum_congr rfl fun c hc => h c hc x y hxy

/-! ## The factorization law -/

/-- Anything computed from the restricted configuration is local on the restriction set. -/
theorem coordinateLocalOn_of_factor {S : Set ι} (F : (S → A) → R) :
    CoordinateLocalOn S (fun x : ι → A => F (fun i : S => x i.1)) := by
  intro x y h
  have hrestrict : (fun i : S => x i.1) = (fun i : S => y i.1) :=
    funext fun i => h i.1 i.2
  exact congrArg F hrestrict

/-- **Coordinate locality is factorization.**  A configuration function is local on `S` exactly
when it is computed from the restriction of the configuration to `S`. -/
theorem coordinateLocalOn_iff_exists_factor [Nonempty A] {S : Set ι} {f : (ι → A) → R} :
    CoordinateLocalOn S f ↔ ∃ F : (S → A) → R, ∀ x, f x = F (fun i : S => x i.1) := by
  classical
  constructor
  · intro hf
    refine ⟨fun g => f (fun i => if h : i ∈ S then g ⟨i, h⟩ else Classical.arbitrary A),
      fun x => ?_⟩
    apply hf
    intro i hi
    simp [hi]
  · rintro ⟨F, hF⟩
    intro x y h
    rw [hF x, hF y]
    exact congrArg F (funext fun i => h i.1 i.2)

end GaloisForLFunctions.HTGeometry
