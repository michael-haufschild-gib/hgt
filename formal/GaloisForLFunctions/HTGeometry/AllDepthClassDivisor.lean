import GaloisForLFunctions.HTGeometry.AllDepthSimultaneousLift

/-!
# Divisors invariant along a period subgroup

The pair-face signature of a member of the all-depth class is a function on `ℂ` invariant along the
period subgroup of its pair, with finitely many nonzero classes.  This file collects the elementary
algebra of such divisors: they form an additive group, they descend to the quotient, a line sum in a
direction of infinite order modulo the subgroup can be antidifferenced, and the corresponding
one-step difference operator is injective.

* `DivInvariant`, `DivFiniteClasses` and their closure properties;
* **`exists_antidifference_of_orbitSum_zero`**;
* **`eq_of_shiftDiff_eq`** — the one-step difference is injective on such divisors.
-/

open scoped BigOperators Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A divisor invariant along a subgroup. -/
def DivInvariant (H : AddSubgroup ℂ) (D : ℂ → ℂ) : Prop := ∀ p, ∀ g ∈ H, D (p + g) = D p

/-- A divisor with finitely many nonzero classes modulo a subgroup. -/
def DivFiniteClasses (H : AddSubgroup ℂ) (D : ℂ → ℂ) : Prop :=
  ∃ S : Finset ℂ, ∀ p, D p ≠ 0 → ∃ q ∈ S, p - q ∈ H

theorem DivInvariant.sub {H : AddSubgroup ℂ} {D E : ℂ → ℂ} (hD : DivInvariant H D)
    (hE : DivInvariant H E) : DivInvariant H (fun p => D p - E p) := by
  intro p g hg
  show D (p + g) - E (p + g) = D p - E p
  rw [hD p g hg, hE p g hg]

theorem DivInvariant.add {H : AddSubgroup ℂ} {D E : ℂ → ℂ} (hD : DivInvariant H D)
    (hE : DivInvariant H E) : DivInvariant H (fun p => D p + E p) := by
  intro p g hg
  show D (p + g) + E (p + g) = D p + E p
  rw [hD p g hg, hE p g hg]

theorem DivFiniteClasses.sub {H : AddSubgroup ℂ} {D E : ℂ → ℂ} (hD : DivFiniteClasses H D)
    (hE : DivFiniteClasses H E) : DivFiniteClasses H (fun p => D p - E p) := by
  classical
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S ∪ T, fun p hp => ?_⟩
  by_cases hd : D p = 0
  · have he : E p ≠ 0 := by
      intro hcon
      exact hp (by show D p - E p = 0; rw [hd, hcon, sub_self])
    obtain ⟨q, hq, hmem⟩ := hT p he
    exact ⟨q, Finset.mem_union_right _ hq, hmem⟩
  · obtain ⟨q, hq, hmem⟩ := hS p hd
    exact ⟨q, Finset.mem_union_left _ hq, hmem⟩

theorem DivFiniteClasses.add {H : AddSubgroup ℂ} {D E : ℂ → ℂ} (hD : DivFiniteClasses H D)
    (hE : DivFiniteClasses H E) : DivFiniteClasses H (fun p => D p + E p) := by
  classical
  obtain ⟨S, hS⟩ := hD
  obtain ⟨T, hT⟩ := hE
  refine ⟨S ∪ T, fun p hp => ?_⟩
  by_cases hd : D p = 0
  · have he : E p ≠ 0 := by
      intro hcon
      exact hp (by show D p + E p = 0; rw [hd, hcon, add_zero])
    obtain ⟨q, hq, hmem⟩ := hT p he
    exact ⟨q, Finset.mem_union_right _ hq, hmem⟩
  · obtain ⟨q, hq, hmem⟩ := hS p hd
    exact ⟨q, Finset.mem_union_left _ hq, hmem⟩

/-! ## Descent to the quotient -/

/-- The descent of an invariant divisor to the quotient. -/
def divQuotient (H : AddSubgroup ℂ) (D : ℂ → ℂ) : (ℂ ⧸ H) → ℂ :=
  fun x => D (Quotient.out x)

theorem divQuotient_mk {H : AddSubgroup ℂ} {D : ℂ → ℂ} (hD : DivInvariant H D) (p : ℂ) :
    divQuotient H D (QuotientAddGroup.mk p) = D p := by
  have hmk : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H)) : ℂ ⧸ H)
      = QuotientAddGroup.mk p := QuotientAddGroup.out_eq' _
  have hmem : Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H) - p ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp hmk
  have := hD p _ hmem
  rw [show p + (Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H) - p)
    = Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H) from by ring] at this
  exact this

theorem exists_finset_support_divQuotient {H : AddSubgroup ℂ} {D : ℂ → ℂ}
    (hfin : DivFiniteClasses H D) :
    ∃ S : Finset (ℂ ⧸ H), ∀ x, divQuotient H D x ≠ 0 → x ∈ S := by
  classical
  obtain ⟨S, hS⟩ := hfin
  refine ⟨S.image (fun q => (QuotientAddGroup.mk q : ℂ ⧸ H)), fun x hx => ?_⟩
  obtain ⟨q, hq, hmem⟩ := hS (Quotient.out x) hx
  refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
  have : (QuotientAddGroup.mk (Quotient.out x) : ℂ ⧸ H) = QuotientAddGroup.mk q :=
    QuotientAddGroup.eq_iff_sub_mem.mpr hmem
  rw [← this]
  exact QuotientAddGroup.out_eq' x

/-! ## Antidifferencing a vanishing line sum -/

set_option maxHeartbeats 800000 in
/-- **A divisor with vanishing line sums in an infinite-order direction is a one-step
difference.** -/
theorem exists_antidifference_of_orbitSum_zero {H : AddSubgroup ℂ} {t : ℂ} {D : ℂ → ℂ}
    (hinv : DivInvariant H D) (hfin : DivFiniteClasses H D)
    (ht : ∀ n : ℤ, n • t ∈ H → n = 0)
    (hzero : ∀ p : ℂ, ∑ᶠ n : ℤ, D (p + n • t) = 0) :
    ∃ C : ℂ → ℂ, DivInvariant H C ∧ DivFiniteClasses H C ∧
      ∀ p, C (p - t) - C p = D p := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_support_divQuotient hfin
  set tq : ℂ ⧸ H := QuotientAddGroup.mk t with htq
  have hmk_smul : ∀ (n : ℤ) (p : ℂ),
      (QuotientAddGroup.mk p : ℂ ⧸ H) + n • tq = QuotientAddGroup.mk (p + n • t) := by
    intro n p
    rw [htq, ← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add]
  have htqfree : ∀ n : ℤ, n • tq = 0 → n = 0 := by
    intro n hn
    refine ht n ?_
    rw [htq, ← QuotientAddGroup.mk_zsmul] at hn
    have : n • t - 0 ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp (by simpa using hn)
    simpa using this
  have hlines : ∀ x : ℂ ⧸ H, ∑ᶠ n : ℤ, divQuotient H D (x + n • tq) = 0 := by
    intro x
    have hterm : ∀ n : ℤ, divQuotient H D (x + n • tq) = D (Quotient.out x + n • t) := by
      intro n
      have hx : x = (QuotientAddGroup.mk (Quotient.out x) : ℂ ⧸ H) :=
        (QuotientAddGroup.out_eq' x).symm
      calc divQuotient H D (x + n • tq)
          = divQuotient H D (QuotientAddGroup.mk (Quotient.out x + n • t)) := by
            rw [← hmk_smul n (Quotient.out x), ← hx]
        _ = D (Quotient.out x + n • t) := divQuotient_mk hinv _
    rw [finsum_congr hterm]
    exact hzero (Quotient.out x)
  obtain ⟨S', hS'⟩ := exists_finset_support_lineTail htqfree hS hlines
  refine ⟨fun p => lineTail tq (divQuotient H D) (QuotientAddGroup.mk p), ?_, ?_, ?_⟩
  · intro p g hg
    show lineTail tq (divQuotient H D) (QuotientAddGroup.mk (p + g))
      = lineTail tq (divQuotient H D) (QuotientAddGroup.mk p)
    congr 1
    refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
    rw [show p + g - p = g from by ring]
    exact hg
  · refine ⟨S'.image Quotient.out, fun p hp => ?_⟩
    have hmem : (QuotientAddGroup.mk p : ℂ ⧸ H) ∈ S' := hS' _ hp
    refine ⟨Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H),
      Finset.mem_image.mpr ⟨_, hmem, rfl⟩, ?_⟩
    have hout : (QuotientAddGroup.mk
        (Quotient.out (QuotientAddGroup.mk p : ℂ ⧸ H)) : ℂ ⧸ H) = QuotientAddGroup.mk p :=
      QuotientAddGroup.out_eq' _
    have hsub := QuotientAddGroup.eq_iff_sub_mem.mp hout.symm
    exact hsub
  · intro p
    have hstep := lineTail_sub (w := tq) (D := divQuotient H D) htqfree hS
      (QuotientAddGroup.mk p)
    have harg : (QuotientAddGroup.mk p : ℂ ⧸ H) - tq = QuotientAddGroup.mk (p - t) := by
      rw [htq, ← QuotientAddGroup.mk_sub]
    rw [harg, divQuotient_mk hinv] at hstep
    exact hstep

/-! ## Injectivity of the one-step difference -/

/-- **The one-step difference in an infinite-order direction is injective on divisors with
finitely many classes.** -/
theorem eq_zero_of_shiftDiff_eq_zero {H : AddSubgroup ℂ} {t : ℂ} {C : ℂ → ℂ}
    (hfin : DivFiniteClasses H C)
    (ht : ∀ n : ℤ, n • t ∈ H → n = 0)
    (hzero : ∀ p, C (p - t) - C p = 0) (p : ℂ) : C p = 0 := by
  classical
  obtain ⟨S, hS⟩ := hfin
  have hinvt : ∀ q : ℂ, C (q + t) = C q := by
    intro q
    have := hzero (q + t)
    rw [show q + t - t = q from by ring] at this
    linear_combination -this
  refine eq_zero_of_invariant_of_finite_classes (R := C) (S := S) (H := H) ?_ ht hinvt p
  intro q hq
  obtain ⟨r, hr, hmem⟩ := hS q hq
  exact ⟨r, hr, hmem⟩

end

end GaloisForLFunctions.HTGeometry
