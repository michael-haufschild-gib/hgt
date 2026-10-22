import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Vanishing on a basis and the amplitude of a direct image

A presheaf whose sections vanish on every open of a basis has vanishing stalks: every germ is
already the germ of a section over a basis open.  Hence the associated sheaf is zero, and for a
family of presheaves indexed by cohomological degree — the presheaves `U ↦ H^q(a^{-1}U, E)` whose
sheafifications are the cohomology sheaves of a derived direct image — vanishing on a basis in the
degrees outside a window forces the sheaves to vanish there.

For the arithmetic base the basis is the cofinite one: the basic opens of `Spec ℤ` are a basis, the
generic point lies in every nonempty one, and the closed point of a prime `p` lies in exactly those
`D(N)` with `p ∤ N`.

* `deningerStalk_eq_zero_of_basis` : vanishing on a basis kills the stalks.
* `deningerPushforwardStalk_eq_zero_of_basis` : the direct-image form of `(1)` ⟹ `(2)`.
* `deningerAmplitude_of_basis` : the amplitude window statement.
* `deningerZariskiBasis`, `deningerGenericPoint_mem_basicOpen`,
  `deningerClosedPoint_mem_basicOpen_iff` : the cofinite arithmetic basis.
-/

namespace RHTower

open CategoryTheory TopologicalSpace Opposite

section BasisVanishing

variable {X : TopCat} {B : Set (Opens X)}

/-- **Vanishing on a basis kills the stalks.**  Every germ is the germ of a section over a basis
open, and those sections are zero. -/
theorem deningerStalk_eq_zero_of_basis (F : TopCat.Presheaf AddCommGrpCat X)
    (hB : Opens.IsBasis B)
    (hvanish : ∀ U ∈ B, ∀ t : ToType (F.obj (op U)), t = 0) (x : X)
    (s : ToType (F.stalk x)) : s = 0 := by
  obtain ⟨V, hxV, hVB, t, ht⟩ := F.exists_mem_germ_eq_of_isBasis hB x s
  rw [← ht, hvanish V hVB t, map_zero]

/-- **The direct-image form.**  If the sections of a presheaf over the preimages of a basis vanish,
then the stalks of its direct image vanish. -/
theorem deningerPushforwardStalk_eq_zero_of_basis {S : TopCat} (a : X ⟶ S)
    (G : TopCat.Presheaf AddCommGrpCat X) {B : Set (Opens S)} (hB : Opens.IsBasis B)
    (hvanish : ∀ U ∈ B, ∀ t : ToType (G.obj (op ((Opens.map a).obj U))), t = 0) (x : S)
    (s : ToType (((TopCat.Presheaf.pushforward AddCommGrpCat a).obj G).stalk x)) : s = 0 :=
  deningerStalk_eq_zero_of_basis ((TopCat.Presheaf.pushforward AddCommGrpCat a).obj G) hB hvanish x s

/-- **`(1)` implies `(2)`.**  If for every degree outside the window the sections over the basis
vanish, then the associated sheaves of those degrees have vanishing stalks, hence are zero: the
amplitude of the direct image is determined on the basis. -/
theorem deningerAmplitude_of_basis (H : ℤ → TopCat.Presheaf AddCommGrpCat X)
    (hB : Opens.IsBasis B) (r s : ℤ)
    (hvanish : ∀ q : ℤ, (q < r ∨ s < q) → ∀ U ∈ B, ∀ t : ToType ((H q).obj (op U)), t = 0)
    (q : ℤ) (hq : q < r ∨ s < q) (x : X) (t : ToType ((H q).stalk x)) : t = 0 :=
  deningerStalk_eq_zero_of_basis (H q) hB (hvanish q hq) x t

end BasisVanishing

section ArithmeticBasis

open PrimeSpectrum

/-- **The cofinite arithmetic basis.**  The basic opens `D(N) = Spec ℤ[1/N]` form a basis of the
arithmetic base. -/
theorem deningerZariskiBasis :
    Opens.IsBasis (Set.range (basicOpen : ℤ → Opens (PrimeSpectrum ℤ))) :=
  isBasis_basic_opens

/-- The generic point of the arithmetic base. -/
def deningerGenericPoint : PrimeSpectrum ℤ :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- **The generic point lies in every nonempty basic open.** -/
theorem deningerGenericPoint_mem_basicOpen {N : ℤ} (hN : N ≠ 0) :
    deningerGenericPoint ∈ basicOpen N := by
  rw [mem_basicOpen]
  intro hcon
  exact hN (Ideal.mem_bot.mp hcon)

/-- The closed point attached to a prime. -/
def deningerClosedPoint (p : ℤ) (hp : Prime p) : PrimeSpectrum ℤ :=
  ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp⟩

/-- **A closed point lies in exactly the basic opens whose parameter it does not divide.** -/
theorem deningerClosedPoint_mem_basicOpen_iff {p : ℤ} (hp : Prime p) (N : ℤ) :
    deningerClosedPoint p hp ∈ basicOpen N ↔ ¬ p ∣ N := by
  rw [mem_basicOpen]
  constructor
  · intro h hdvd
    exact h (Ideal.mem_span_singleton.mpr hdvd)
  · intro h hmem
    exact h (Ideal.mem_span_singleton.mp hmem)

end ArithmeticBasis

end RHTower
