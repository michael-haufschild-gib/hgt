import GaloisForLFunctions.RHTower.CriticalDiscEulerOrbitDensity

/-!
# Pointed translation groupoid of the Euler increment action

A dense translation action has a one-point maximal Hausdorff continuous quotient, but passing to
the coarse quotient discards the arrows.  This file defines the elementary translation groupoid
arrow type and proves that the total source fibre at any pointed object is canonically equivalent
to the acting subgroup itself.  It then specializes this exact recovery statement to the genuine
critical-disc Euler increment group.
-/

noncomputable section

namespace RHTower

open Complex ComplexConjugate

/-- An arrow `x -> y` in the translation action groupoid of an additive subgroup `G`.  The arrow
retains the actual group element producing the translation. -/
structure TranslationArrow {V : Type*} [AddGroup V] (G : AddSubgroup V) (x y : V) where
  displacement : G
  target_eq : y = x + displacement

namespace TranslationArrow

variable {V : Type*} [AddGroup V] (G : AddSubgroup V)

@[ext]
theorem ext {x y : V} (f g : TranslationArrow G x y)
    (h : f.displacement = g.displacement) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity arrow. -/
def id (x : V) : TranslationArrow G x x :=
  ⟨0, by simp⟩

/-- Composition of translation arrows. -/
def comp {x y z : V} (f : TranslationArrow G x y) (g : TranslationArrow G y z) :
    TranslationArrow G x z :=
  ⟨f.displacement + g.displacement, by
    calc
      z = y + (g.displacement : V) := g.target_eq
      _ = (x + (f.displacement : V)) + (g.displacement : V) := by
        exact congrArg (fun t : V => t + (g.displacement : V)) f.target_eq
      _ = x + ((f.displacement + g.displacement : G) : V) := by
        simp [add_assoc]⟩

/-- Every translation arrow is invertible. -/
def inv {x y : V} (f : TranslationArrow G x y) : TranslationArrow G y x :=
  ⟨-f.displacement, by
    calc
      x = (x + (f.displacement : V)) + (-(f.displacement : V)) := by
        simp [add_assoc]
      _ = y + (-(f.displacement : V)) := by
        exact congrArg (fun t : V => t + (-(f.displacement : V))) f.target_eq.symm
      _ = y + ((-f.displacement : G) : V) := by simp⟩

@[simp]
theorem displacement_id (x : V) : (id G x).displacement = 0 := rfl

@[simp]
theorem displacement_comp {x y z : V}
    (f : TranslationArrow G x y) (g : TranslationArrow G y z) :
    (comp G f g).displacement = f.displacement + g.displacement := rfl

@[simp]
theorem displacement_inv {x y : V} (f : TranslationArrow G x y) :
    (inv G f).displacement = -f.displacement := rfl

/-- Left identity law. -/
theorem id_comp {x y : V} (f : TranslationArrow G x y) :
    comp G (id G x) f = f := by
  apply ext
  simp

/-- Right identity law. -/
theorem comp_id {x y : V} (f : TranslationArrow G x y) :
    comp G f (id G y) = f := by
  apply ext
  simp

/-- Associativity of arrow composition. -/
theorem comp_assoc {w x y z : V}
    (f : TranslationArrow G w x) (g : TranslationArrow G x y)
    (h : TranslationArrow G y z) :
    comp G (comp G f g) h = comp G f (comp G g h) := by
  apply ext
  simp [add_assoc]

/-- Inverse followed by the original arrow is the identity. -/
theorem inv_comp {x y : V} (f : TranslationArrow G x y) :
    comp G (inv G f) f = id G y := by
  apply ext
  simp

/-- The original arrow followed by its inverse is the identity. -/
theorem comp_inv {x y : V} (f : TranslationArrow G x y) :
    comp G f (inv G f) = id G x := by
  apply ext
  simp

/-- Translation actions are free: every loop has zero displacement. -/
theorem loop_displacement_eq_zero {x : V} (f : TranslationArrow G x x) :
    f.displacement = 0 := by
  apply Subtype.ext
  have h := f.target_eq
  simpa using add_left_cancel (show x + (f.displacement : V) = x + 0 by simpa using h.symm)

end TranslationArrow

/-- Total fibre of all arrows with a fixed source object. -/
def TranslationSourceFiber {V : Type*} [AddGroup V] (G : AddSubgroup V) (x : V) :=
  Σ y : V, TranslationArrow G x y

/-- The pointed source fibre of a translation groupoid recovers the acting subgroup exactly. -/
def translationSourceFiberEquiv {V : Type*} [AddGroup V]
    (G : AddSubgroup V) (x : V) : TranslationSourceFiber G x ≃ G where
  toFun a := a.2.displacement
  invFun g := ⟨x + g, ⟨g, rfl⟩⟩
  left_inv := by
    rintro ⟨y, ⟨g, hg⟩⟩
    subst y
    rfl
  right_inv := by
    intro g
    rfl

/-- Abstract coarse-quotient collapse for a dense additive translation subgroup. -/
theorem continuous_denseTranslationInvariant_eq_base
    {V Y : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [TopologicalSpace Y] [T2Space Y]
    (G : AddSubgroup V) (hdense : closure (G : Set V) = Set.univ)
    (A : V → Y) (hA : Continuous A)
    (hinvariant : ∀ x g, g ∈ G → A (x + g) = A x)
    (x : V) : A x = A 0 := by
  have hshift : Continuous (fun v : V => A (x + v)) :=
    hA.comp (continuous_const.add continuous_id)
  have hclosed : IsClosed {v : V | A (x + v) = A x} :=
    isClosed_eq hshift continuous_const
  have hG : (G : Set V) ⊆ {v : V | A (x + v) = A x} := by
    intro g hg
    exact hinvariant x g hg
  have hall : {v : V | A (x + v) = A x} = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hdense]
    exact closure_minimal hG hclosed
  have hx := Set.eq_univ_iff_forall.mp hall (-x)
  simpa using hx.symm

/-- The actual critical-disc pointed Euler action groupoid has source fibre exactly equal to the
genuine nonlinear Euler increment group, even after deleting any finite set of primes. -/
def criticalDiscEulerSourceFiberEquiv
    (r : ℝ) (S : Finset Nat.Primes) (epsilon : ℝ)
    (x : C(CriticalClosedDisc r, ℂ)) :
    TranslationSourceFiber (criticalDiscRealEulerIncrementGroup r S epsilon) x ≃
      criticalDiscRealEulerIncrementGroup r S epsilon :=
  translationSourceFiberEquiv _ x

/-- Coarse-versus-pointed separation on the actual analytic critical-disc fibre: the given
continuous invariant collapses to its base value, while the pointed action groupoid still has a
source fibre canonically equivalent to the full genuine Euler increment group. -/
theorem criticalDisc_coarse_collapses_pointed_recovers
    {r₀ r₁ epsilon : ℝ} (S : Finset Nat.Primes)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (A : C(CriticalClosedDisc r₀, ℂ) → Y) (hA : Continuous A)
    (hinvariant : ∀ x g,
      g ∈ criticalDiscRealEulerIncrementGroup r₀ S epsilon → A (x + g) = A x)
    (f : ℂ → ℂ)
    (hr₀ : 0 ≤ r₀) (hr01 : r₀ < r₁) (hr1 : r₁ < 1 / 2)
    (hepsilon : 0 < epsilon)
    (hf : DiffContOnCl ℂ f (Metric.ball (1 / 2 : ℂ) r₁))
    (hodd : ∀ z ∈ Metric.closedBall (1 / 2 : ℂ) r₀, f (1 - z) = -f z)
    (hschwarz : ∀ z : ℂ, f (conj z) = conj (f z)) :
    A (criticalDiscRestriction f r₀
      (hf.continuousOn_ball.mono (Metric.closedBall_subset_closedBall hr01.le))) = A 0 ∧
      Nonempty
        (TranslationSourceFiber (criticalDiscRealEulerIncrementGroup r₀ S epsilon) 0 ≃
          criticalDiscRealEulerIncrementGroup r₀ S epsilon) := by
  constructor
  · exact criticalDisc_continuous_finiteUnitInvariant_eq_base
      S A hA hinvariant f hr₀ hr01 hr1 hepsilon hf hodd hschwarz
  · exact ⟨criticalDiscEulerSourceFiberEquiv r₀ S epsilon 0⟩

end RHTower
