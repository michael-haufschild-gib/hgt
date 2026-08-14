import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.CharP.Algebra

/-!
# The field of fractions of the entire functions on a complex space

Entire functions on a complex normed space form an integral domain: a product vanishing identically
forces one factor to vanish on a neighbourhood, and the identity theorem propagates that to the
whole space.  Their fraction field is the carrier on which a complex torus `ℂ^n / Λ` and its isogeny
protocols act.

Unlike the codiscrete-germ carrier used in one variable, this construction is available in every
dimension: it needs no description of the polar set, and in particular no Cousin or Oka theorem.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The entire functions on a complex normed space. -/
def entireSubring : Subring (V → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ f Set.univ}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  neg_mem' := fun hf => hf.neg

variable {V}

theorem analyticOnNhd_of_mem_entireSubring {f : V → ℂ} (hf : f ∈ entireSubring V) :
    AnalyticOnNhd ℂ f Set.univ := hf

theorem mem_entireSubring {f : V → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    f ∈ entireSubring V := hf

/-- **Entire functions form a domain.**  A product vanishing identically forces one factor to vanish
near a point, and the identity theorem propagates that everywhere. -/
instance : NoZeroDivisors (entireSubring V) := by
  classical
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hane : ∃ z : V, (a : V → ℂ) z ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact ha (Subtype.ext (funext hcon))
  obtain ⟨z₀, hz₀⟩ := hane
  have hzero : ∀ z : V, (a : V → ℂ) z * (b : V → ℂ) z = 0 := by
    intro z
    have := congrArg (fun g : entireSubring V => (g : V → ℂ) z) hab
    simpa using this
  have hcont : ContinuousAt (a : V → ℂ) z₀ :=
    ((analyticOnNhd_of_mem_entireSubring a.2) z₀ (Set.mem_univ _)).continuousAt
  have hnear : ∀ᶠ z in 𝓝 z₀, (a : V → ℂ) z ≠ 0 := hcont.eventually_ne hz₀
  have hbzero : ∀ᶠ z in 𝓝 z₀, (b : V → ℂ) z = 0 := by
    filter_upwards [hnear] with z hz
    rcases mul_eq_zero.mp (hzero z) with h | h
    · exact absurd h hz
    · exact h
  have hb : Set.EqOn (b : V → ℂ) 0 Set.univ :=
    (analyticOnNhd_of_mem_entireSubring b.2).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z₀) hbzero
  exact Subtype.ext (funext fun z => hb (Set.mem_univ z))

instance : IsDomain (entireSubring V) := NoZeroDivisors.to_isDomain _

/-- **The field of fractions of the entire functions.** -/
def EntireField (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] : Type _ :=
  FractionRing (entireSubring V)

variable (V)

noncomputable instance : Field (EntireField V) :=
  inferInstanceAs (Field (FractionRing (entireSubring V)))

noncomputable instance : Algebra (entireSubring V) (EntireField V) :=
  inferInstanceAs (Algebra (entireSubring V) (FractionRing (entireSubring V)))

instance : IsFractionRing (entireSubring V) (EntireField V) :=
  inferInstanceAs (IsFractionRing (entireSubring V) (FractionRing (entireSubring V)))

variable {V}

/-- An entire function, as an element of the entire fraction field. -/
noncomputable def ofEntire (f : V → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ) : EntireField V :=
  algebraMap (entireSubring V) (EntireField V) ⟨f, hf⟩

theorem ofEntire_injective {f g : V → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (h : ofEntire f hf = ofEntire g hg) : f = g := by
  have := IsFractionRing.injective (entireSubring V) (EntireField V) h
  exact congrArg Subtype.val this

/-- The complex constants, as entire functions. -/
noncomputable def constEntireRing (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ℂ →+* entireSubring V where
  toFun c := ⟨fun _ => c, analyticOnNhd_const⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The complex constants of the entire fraction field. -/
noncomputable def constEntire (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ℂ →+* EntireField V :=
  (algebraMap (entireSubring V) (EntireField V)).comp (constEntireRing V)

theorem constEntire_apply (c : ℂ) :
    constEntire V c = ofEntire (fun _ : V => c) analyticOnNhd_const := rfl

theorem constEntire_injective : Function.Injective (constEntire V) := by
  intro c d h
  rw [constEntire_apply, constEntire_apply] at h
  have hf := ofEntire_injective (V := V) (f := fun _ => c) (g := fun _ => d)
    analyticOnNhd_const analyticOnNhd_const h
  exact congrFun hf 0

end GaloisForLFunctions.HTGeometry
