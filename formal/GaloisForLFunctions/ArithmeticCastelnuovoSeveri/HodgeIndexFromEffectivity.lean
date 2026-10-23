import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolarSurfaceHodgeIndex

/-!
# Hodge index from effectivity: what a section count has to deliver

In Weil's proof the Hodge index theorem of `C × C` is not an estimate; it is forced by two facts
about **effective** divisors:

* **Riemann–Roch**: a class `D` with `D² > 0` has `nD` or `−nD` effective for large `n`
  (`h⁰(nD) + h⁰(K − nD) ≥ n²D²/2 + O(n)`);
* **ampleness**: an effective class orthogonal to the ample class `H + V` is numerically trivial.

This file isolates that logic on an abstract polar surface. An **effectivity** is a set `E` of
cycles; it satisfies the *Riemann–Roch axiom* if every class of positive square is effective up to
sign, and the *ample axiom* if every effective class orthogonal to `H + V` pairs to zero with
everything. Then (`exists_effectivity_iff_hodgeIndex`)

    Hodge index  ⟺  some effectivity satisfies both axioms,

with the **positive cone** `{x : x² ≥ 0, x·(H + V) ≥ 0}` as the canonical witness. The direction
`⇐` is the whole of Weil's dimension count; the direction `⇒` says that nothing weaker can work.
On the scaling surface of `ℤ` the problem of the section count is therefore exactly: *produce a
cone of arithmetic cycles with the two axioms*, without knowing the sign of the form in advance.

The naive candidate fails: the cone of the pole quadrant `aH + bV` (`a, b ≥ 0`) together with
nonnegative tests satisfies the ample axiom, but not the Riemann–Roch axiom as soon as one cycle
lies outside it, since `(H + V + εx)² > 0` for small `ε` (`not_riemannRoch_of_perturbation`):
positivity of tests is not effectivity on the surface.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

namespace PolarSurface

variable {C : Type*} [AddCommGroup C] [Module ℝ C] (S : PolarSurface C)

/-- **Riemann–Roch axiom**: every class of positive square is effective up to sign. -/
def RiemannRochAxiom (E : Set C) : Prop := ∀ x, 0 < S.pair x x → x ∈ E ∨ -x ∈ E

/-- **Ample axiom**: an effective class orthogonal to `H + V` is numerically trivial. -/
def AmpleAxiom (E : Set C) : Prop := ∀ x ∈ E, S.pair x S.ample = 0 → ∀ y, S.pair x y = 0

/-- The positive cone `{x : x² ≥ 0, x · (H + V) ≥ 0}`. -/
def positiveCone : Set C := {x | 0 ≤ S.pair x x ∧ 0 ≤ S.pair x S.ample}

/-- **Riemann–Roch and ampleness force the Hodge index.** -/
theorem ampleHodgeIndex_of_effectivity {E : Set C} (hRR : S.RiemannRochAxiom E)
    (hA : S.AmpleAxiom E) : S.AmpleHodgeIndex := by
  intro x hx
  by_contra hpos
  push Not at hpos
  rcases hRR x hpos with h | h
  · have := hA x h hx x; linarith
  · have hx' : S.pair (-x) S.ample = 0 := by simp [hx]
    have := hA (-x) h hx' (-x)
    simp only [map_neg, LinearMap.neg_apply, neg_neg] at this
    linarith

/-- Cauchy–Schwarz on the orthogonal complement of the ample class, under Hodge index. -/
theorem pair_sq_le_of_ampleHodgeIndex (h : S.AmpleHodgeIndex) {x y : C}
    (hx : S.pair x S.ample = 0) (hy : S.pair y S.ample = 0) :
    S.pair x y ^ 2 ≤ S.pair x x * S.pair y y := by
  have hq : ∀ t : ℝ, 0 ≤ (-S.pair y y) * (t * t) + (-2 * S.pair x y) * t + (-S.pair x x) := by
    intro t
    have hz : S.pair (x + t • y) S.ample = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hx, hy]
      ring
    have := h _ hz
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_comm y x] at this
    nlinarith [this]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **The positive cone is an effectivity with both axioms** under Hodge index. -/
theorem positiveCone_axioms (h : S.HodgeIndex) :
    S.RiemannRochAxiom S.positiveCone ∧ S.AmpleAxiom S.positiveCone := by
  have hamp := S.ampleHodgeIndex_iff_castelnuovoSeveri.mpr (S.hodgeIndex_iff_castelnuovoSeveri.mp h)
  refine ⟨fun x hx => ?_, fun x hx hxA y => ?_⟩
  · rcases le_total 0 (S.pair x S.ample) with h0 | h0
    · exact Or.inl ⟨hx.le, h0⟩
    · refine Or.inr ⟨by simpa using hx.le, by simpa using h0⟩
  · -- `x` is isotropic and orthogonal to the ample class, hence in the radical
    have hxx : S.pair x x = 0 := le_antisymm (hamp x hxA) hx.1
    set y' := y - (S.pair y S.ample / 2) • S.ample
    have hy' : S.pair y' S.ample = 0 := by
      simp only [y', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_ample_ample]
      ring
    have hcs := S.pair_sq_le_of_ampleHodgeIndex hamp hxA hy'
    rw [hxx, zero_mul] at hcs
    have hxy' : S.pair x y' = 0 := by nlinarith [sq_nonneg (S.pair x y')]
    have : S.pair x y = S.pair x y' + (S.pair y S.ample / 2) * S.pair x S.ample := by
      simp only [y', map_sub, map_smul, smul_eq_mul]; ring
    rw [this, hxy', hxA, mul_zero, add_zero]

/-- **Hodge index is exactly the existence of an effectivity with the Riemann–Roch and ample
axioms.** -/
theorem exists_effectivity_iff_hodgeIndex :
    S.HodgeIndex ↔ ∃ E : Set C, S.RiemannRochAxiom E ∧ S.AmpleAxiom E := by
  constructor
  · intro h; exact ⟨S.positiveCone, S.positiveCone_axioms h⟩
  · rintro ⟨E, hRR, hA⟩
    exact S.hodgeIndex_iff_castelnuovoSeveri.mpr
      (S.ampleHodgeIndex_iff_castelnuovoSeveri.mp (S.ampleHodgeIndex_of_effectivity hRR hA))

/-- **Effectivity is not positivity.** If a class `x` and its negative lie outside `E` for every
small multiple added to the ample class, `E` fails the Riemann–Roch axiom: `(H + V + εx)² > 0`
for small `ε > 0`. -/
theorem not_riemannRoch_of_perturbation {E : Set C} (x : C)
    (hout : ∀ ε : ℝ, 0 < ε → S.ample + ε • x ∉ E ∧ -(S.ample + ε • x) ∉ E) :
    ¬ S.RiemannRochAxiom E := by
  intro hRR
  -- choose `ε` with `2 + 2ε(x·A) + ε²x² > 0`
  set a := S.pair x S.ample
  set b := S.pair x x
  set ε : ℝ := 1 / (4 * (|a| + |b| + 1))
  have hε : 0 < ε := by positivity
  have hsq : 0 < S.pair (S.ample + ε • x) (S.ample + ε • x) := by
    have hexp : S.pair (S.ample + ε • x) (S.ample + ε • x) = 2 + 2 * ε * a + ε ^ 2 * b := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        S.pair_ample_ample, a, b, S.pair_comm S.ample x]
      ring
    rw [hexp]
    have hεa : |2 * ε * a| ≤ 1 / 2 := by
      rw [abs_mul, abs_mul, abs_of_pos hε, abs_two]
      have : ε * (|a| + |b| + 1) = 1 / 4 := by
        simp only [ε]; field_simp
      nlinarith [abs_nonneg a, abs_nonneg b]
    have hεb : |ε ^ 2 * b| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (by positivity : 0 < ε ^ 2)]
      have h4 : ε * (|a| + |b| + 1) = 1 / 4 := by
        simp only [ε]; field_simp
      have hε4 : ε ≤ 1 / 4 := by nlinarith [abs_nonneg a, abs_nonneg b]
      have hεb' : ε * |b| ≤ 1 / 4 := by nlinarith [abs_nonneg a, abs_nonneg b]
      nlinarith [abs_nonneg b, mul_le_mul_of_nonneg_left hεb' hε.le]
    linarith [neg_abs_le (2 * ε * a), neg_abs_le (ε ^ 2 * b)]
  rcases hRR _ hsq with h | h
  · exact (hout ε hε).1 h
  · exact (hout ε hε).2 h

end PolarSurface

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
