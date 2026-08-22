import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# The ramification dictionary for a valuation subring of a normal extension

mathlib carries Hilbert's ramification theory for Dedekind domains (`Ideal.inertia`,
`Ideal.card_inertia_eq_ramificationIdxIn`) and, separately, the decomposition and inertia subgroups
of a valuation subring (`ValuationSubring.inertiaSubgroup`); it does not connect them.  This module
is the bridge, for an arbitrary base field of a normal extension — which is what makes it usable at
every intermediate field, not just at the bottom one.

Let `S` be a Dedekind domain with fraction field `L`, and let `W` be a valuation subring of `L`
containing `S`.  Write `centerPrime` for the prime of `S` contracted from the maximal ideal of `W`.

```text
mem_iff_exists_div        ** x ∈ W ↔ x = a / s with a s : S and s off the centre **
valuationSubringAtPrime_eq   W is exactly the localization of S at its centre
```

The first is the engine: `S` localized at the centre is a valuation subring of `L` of Krull
dimension one, it is contained in `W`, and a valuation subring of dimension one below a proper
valuation subring is equal to it.

With that, for a Galois action of `Gal(L/F)` on `S` compatible with the one on `L`:

```text
smul_valuationSubring_eq   ideal inertia stabilises W
smul_sub_mem_maximalIdeal  ideal inertia acts trivially on the residue field of W
inertia_eq_map             ** the ideal inertia group IS the valuation inertia group **
natCard_inertia_eq_natCard_inertiaSubgroup
```

The proof of the second inclusion needs no localization at all: an inertia element `g` satisfies
`g • x − x ∈ P` for every `x`, so `g` preserves the complement of `P`, and the numerator of
`g • (a/s) − a/s` is `(g•a − a)s − a(g•s − s) ∈ P` while its denominator `(g•s)s` is off `P`.

Combined with mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` this gives `|I| = e` for the
inertia group of *any* subfield over which `L` is Galois, which is the input the collision count of
a critical horizon needs.  The reverse inequality `|I| ≤ e` is
`TameInertiaOrderBound.natCard_le_addVal_of_smul_eq` and does not need any of this.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing IsDedekindDomain
open scoped Pointwise

section ResidueTrivial

variable {F L : Type*} [Field F] [Field L] [Algebra F L] (W : ValuationSubring L)

/-- A valuation-theoretic inertia element moves every element of the ring into the maximal
ideal. -/
theorem smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup
    {g : W.decompositionSubgroup F} (hg : g ∈ W.inertiaSubgroup F) (y : W) :
    g • y - y ∈ maximalIdeal W := by
  have h : g • IsLocalRing.residue W y = IsLocalRing.residue W y :=
    congrArg (fun e : IsLocalRing.ResidueField W ≃+* IsLocalRing.ResidueField W =>
      e (IsLocalRing.residue W y)) (MonoidHom.mem_ker.1 hg)
  refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
  rw [map_sub, sub_eq_zero, ← h]
  exact (IsLocalRing.ResidueField.residue_smul (R := W) (W.decompositionSubgroup F) g y).symm

end ResidueTrivial

variable {S L : Type*} [CommRing S] [IsDedekindDomain S]
variable [Field L] [Algebra S L] [IsFractionRing S L]
variable (W : ValuationSubring L) (hSW : ∀ x : S, algebraMap S L x ∈ W)

/-- The integral closure, landed inside the valuation subring. -/
def toValuationSubring : S →+* W :=
  RingHom.codRestrict (algebraMap S L) W.toSubring hSW

@[simp] theorem coe_toValuationSubring (x : S) :
    ((toValuationSubring W hSW x : W) : L) = algebraMap S L x := rfl

/-- The prime of `S` cut out by the valuation. -/
def centerPrime : Ideal S := (maximalIdeal W).comap (toValuationSubring W hSW)

instance centerPrime_isPrime : (centerPrime W hSW).IsPrime :=
  Ideal.comap_isPrime _ _

theorem mem_centerPrime_iff (x : S) :
    x ∈ centerPrime W hSW ↔ toValuationSubring W hSW x ∈ maximalIdeal W := Iff.rfl

/-- An element of `S` outside the centre maps to a unit of the valuation subring. -/
theorem isUnit_toValuationSubring_of_notMem {x : S} (hx : x ∉ centerPrime W hSW) :
    IsUnit (toValuationSubring W hSW x) :=
  IsLocalRing.notMem_maximalIdeal.mp hx

theorem inv_mem_of_notMem_centerPrime {x : S} (hx : x ∉ centerPrime W hSW) :
    (algebraMap S L x)⁻¹ ∈ W := by
  obtain ⟨y, hy⟩ := (isUnit_toValuationSubring_of_notMem W hSW hx).exists_right_inv
  have hxy : algebraMap S L x * (y : L) = 1 := congrArg Subtype.val hy
  have : (algebraMap S L x)⁻¹ = (y : L) := inv_eq_of_mul_eq_one_right hxy
  rw [this]
  exact y.property

theorem centerPrime_ne_bot (hW : W ≠ ⊤) : centerPrime W hSW ≠ ⊥ := by
  intro hbot
  apply hW
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, t, ht, hx⟩ := IsFractionRing.div_surjective (A := S) x
  have hane : a ∉ centerPrime W hSW ∨ algebraMap S L a = 0 := by
    by_cases ha0 : a = 0
    · exact Or.inr (by rw [ha0, map_zero])
    · refine Or.inl ?_
      rw [hbot]
      simpa using ha0
  have htne : t ∉ centerPrime W hSW := by
    rw [hbot]
    simp only [Ideal.mem_bot]
    exact nonZeroDivisors.ne_zero ht
  rw [← hx, div_eq_mul_inv]
  rcases hane with ha | ha
  · exact mul_mem (hSW a) (inv_mem_of_notMem_centerPrime W hSW htne)
  · rw [ha, zero_mul]
    exact zero_mem W

/-- The centre of the valuation, as a height-one prime of `S`. -/
def centerHeightOne (hW : W ≠ ⊤) : IsDedekindDomain.HeightOneSpectrum S :=
  ⟨centerPrime W hSW, centerPrime_isPrime W hSW, centerPrime_ne_bot W hSW hW⟩

@[simp] theorem centerHeightOne_asIdeal (hW : W ≠ ⊤) :
    (centerHeightOne W hSW hW).asIdeal = centerPrime W hSW := rfl

/-- **The valuation subring is the localization of `S` at its centre.** -/
theorem valuationSubringAtPrime_eq (hW : W ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L
        (centerHeightOne W hSW hW) = W := by
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ hW
  rintro x ⟨a, s, hs, rfl⟩
  have hsn : s ∉ centerPrime W hSW := hs
  exact mul_mem (hSW a) (inv_mem_of_notMem_centerPrime W hSW hsn)

/-- **Membership in the valuation subring is being a fraction with denominator off the centre.** -/
theorem mem_iff_exists_div (hW : W ≠ ⊤) (x : L) :
    x ∈ W ↔ ∃ a s : S, s ∉ centerPrime W hSW ∧
      algebraMap S L a / algebraMap S L s = x := by
  constructor
  · intro hx
    rw [← valuationSubringAtPrime_eq W hSW hW] at hx
    obtain ⟨a, s, hs, rfl⟩ := hx
    exact ⟨a, s, hs, div_eq_mul_inv _ _⟩
  · rintro ⟨a, s, hs, rfl⟩
    rw [div_eq_mul_inv]
    exact mul_mem (hSW a) (inv_mem_of_notMem_centerPrime W hSW hs)


/-- A quotient with numerator in the centre and denominator off it lies in the maximal ideal. -/
theorem mem_maximalIdeal_of_mul_eq {y : W} {n d : S}
    (hn : n ∈ centerPrime W hSW) (hd : d ∉ centerPrime W hSW)
    (hy : (y : L) * algebraMap S L d = algebraMap S L n) :
    y ∈ maximalIdeal W := by
  obtain ⟨u, hu⟩ := (isUnit_toValuationSubring_of_notMem W hSW hd).exists_right_inv
  have hyd : y * toValuationSubring W hSW d = toValuationSubring W hSW n := Subtype.ext hy
  have hyu : y = toValuationSubring W hSW n * u := by
    calc y = y * (toValuationSubring W hSW d * u) := by rw [hu, mul_one]
      _ = y * toValuationSubring W hSW d * u := by ring
      _ = toValuationSubring W hSW n * u := by rw [hyd]
  rw [hyu]
  exact Ideal.mul_mem_right _ _ hn


section Galois

variable {F : Type*} [Field F] [Algebra F L]
variable [MulSemiringAction (L ≃ₐ[F] L) S]
variable (hact : ∀ (g : L ≃ₐ[F] L) (x : S), algebraMap S L (g • x) = g • algebraMap S L x)

include hact

/-- An ideal-inertia element preserves the centre. -/
theorem notMem_centerPrime_smul {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) {x : S}
    (hx : x ∉ centerPrime W hSW) : g • x ∉ centerPrime W hSW := by
  intro hmem
  exact hx (by simpa using Ideal.sub_mem _ hmem (hg x))

/-- **Ideal inertia stabilises the valuation subring.** -/
theorem smul_valuationSubring_eq (hW : W ≠ ⊤) {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) :
    g • W = W := by
  have key : ∀ (h : L ≃ₐ[F] L), h ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L) →
      ∀ y ∈ W, h • y ∈ W := by
    intro h hh y hy
    obtain ⟨a, s, hs, rfl⟩ := (mem_iff_exists_div W hSW hW y).mp hy
    have hnum : h • algebraMap S L a = algebraMap S L (h • a) := (hact h a).symm
    have hden : h • algebraMap S L s = algebraMap S L (h • s) := (hact h s).symm
    have : h • (algebraMap S L a / algebraMap S L s)
        = algebraMap S L (h • a) / algebraMap S L (h • s) := by
      rw [← hnum, ← hden]
      exact map_div₀ (h : L ≃+* L) _ _
    rw [this]
    exact (mem_iff_exists_div W hSW hW _).mpr
      ⟨h • a, h • s, notMem_centerPrime_smul W hSW hact hh hs, rfl⟩
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact key g hg a ha
  · intro hx
    refine ⟨g⁻¹ • x, key g⁻¹ (inv_mem hg) x hx, ?_⟩
    simp

/-- The decomposition-group element attached to an ideal-inertia element. -/
def toDecomposition (hW : W ≠ ⊤) {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) :
    W.decompositionSubgroup F :=
  ⟨g, smul_valuationSubring_eq W hSW hact hW hg⟩

@[simp] theorem coe_smul_toDecomposition (hW : W ≠ ⊤) {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) (y : W) :
    ((toDecomposition W hSW hact hW hg • y : W) : L) = g • (y : L) := rfl

/-- **Ideal inertia acts trivially on the residue field of the valuation subring.** -/
theorem smul_sub_mem_maximalIdeal (hW : W ≠ ⊤) {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) (y : W) :
    toDecomposition W hSW hact hW hg • y - y ∈ maximalIdeal W := by
  obtain ⟨a, s, hs, hy⟩ := (mem_iff_exists_div W hSW hW (y : L)).mp y.property
  have hs0 : algebraMap S L s ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := (FaithfulSMul.algebraMap_injective S L) (by simpa using h)
    rw [this]
    exact Ideal.zero_mem _
  have hys : (y : L) * algebraMap S L s = algebraMap S L a := by
    field_simp at hy
    rw [hy]
    ring
  refine mem_maximalIdeal_of_mul_eq W hSW
    (n := (g • a) * s - a * (g • s)) (d := (g • s) * s) ?_ ?_ ?_
  · have h1 : (g • a - a) * s ∈ centerPrime W hSW := Ideal.mul_mem_right _ _ (hg a)
    have h2 : a * (g • s - s) ∈ centerPrime W hSW := Ideal.mul_mem_left _ _ (hg s)
    have : (g • a) * s - a * (g • s) = (g • a - a) * s - a * (g • s - s) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  · intro hmem
    rcases (Ideal.IsPrime.mem_or_mem (centerPrime_isPrime W hSW) hmem) with h | h
    · exact notMem_centerPrime_smul W hSW hact hg hs h
    · exact hs h
  · have hga : g • algebraMap S L a = algebraMap S L (g • a) := (hact g a).symm
    have hgs : g • algebraMap S L s = algebraMap S L (g • s) := (hact g s).symm
    have hgys : (g • (y : L)) * algebraMap S L (g • s) = algebraMap S L (g • a) := by
      rw [← hga, ← hgs, ← smul_mul' , hys]
    push_cast [map_sub, map_mul]
    rw [coe_smul_toDecomposition]
    linear_combination (algebraMap S L s) * hgys - (algebraMap S L (g • s)) * hys
/-- Ideal inertia lands in the valuation-theoretic inertia group. -/
theorem toDecomposition_mem_inertiaSubgroup (hW : W ≠ ⊤) {g : L ≃ₐ[F] L}
    (hg : g ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L)) :
    toDecomposition W hSW hact hW hg ∈ W.inertiaSubgroup F := by
  refine MonoidHom.mem_ker.2 (RingEquiv.ext ?_)
  refine (IsLocalRing.residue_surjective (R := W)).forall.2 fun a => ?_
  change toDecomposition W hSW hact hW hg • IsLocalRing.residue W a = IsLocalRing.residue W a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub]
  exact (IsLocalRing.residue_eq_zero_iff _).2 (smul_sub_mem_maximalIdeal W hSW hact hW hg a)

/-- Valuation-theoretic inertia lands in ideal inertia. -/
theorem coe_mem_inertia_of_mem_inertiaSubgroup
    {g : W.decompositionSubgroup F} (hg : g ∈ W.inertiaSubgroup F) :
    (g : L ≃ₐ[F] L) ∈ (centerPrime W hSW).inertia (L ≃ₐ[F] L) := by
  intro x
  show toValuationSubring W hSW ((g : L ≃ₐ[F] L) • x - x) ∈ maximalIdeal W
  have hcoe : ((toValuationSubring W hSW ((g : L ≃ₐ[F] L) • x - x) : W) : L)
      = ((g • (toValuationSubring W hSW x) : W) : L) - ((toValuationSubring W hSW x : W) : L) := by
    show algebraMap S L ((g : L ≃ₐ[F] L) • x - x) = _
    rw [map_sub, hact]
    rfl
  have : toValuationSubring W hSW ((g : L ≃ₐ[F] L) • x - x)
      = g • (toValuationSubring W hSW x) - toValuationSubring W hSW x := Subtype.ext hcoe
  rw [this]
  exact smul_sub_mem_maximalIdeal_of_mem_inertiaSubgroup W hg _

/-- **The ideal-theoretic and valuation-theoretic inertia groups agree.** -/
theorem inertia_eq_map (hW : W ≠ ⊤) :
    (centerPrime W hSW).inertia (L ≃ₐ[F] L)
      = (W.inertiaSubgroup F).map (W.decompositionSubgroup F).subtype := by
  apply le_antisymm
  · intro g hg
    exact ⟨toDecomposition W hSW hact hW hg,
      toDecomposition_mem_inertiaSubgroup W hSW hact hW hg, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact coe_mem_inertia_of_mem_inertiaSubgroup W hSW hact hg

/-- **The two inertia groups have the same cardinality.** -/
theorem natCard_inertia_eq_natCard_inertiaSubgroup (hW : W ≠ ⊤) :
    Nat.card ((centerPrime W hSW).inertia (L ≃ₐ[F] L)) = Nat.card (W.inertiaSubgroup F) := by
  rw [inertia_eq_map W hSW hact hW]
  exact (Nat.card_congr ((W.inertiaSubgroup F).equivMapOfInjective
    (W.decompositionSubgroup F).subtype (Subgroup.subtype_injective _)).toEquiv).symm

end Galois

end

end ValuationInertia
end GaloisForLFunctions.HTGeometry
