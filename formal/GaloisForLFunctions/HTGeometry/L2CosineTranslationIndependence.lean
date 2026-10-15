import GaloisForLFunctions.HTGeometry.L2TranslationPolynomialIndependence

/-!
# Independence survives reflection symmetrization

Opposite arithmetic translates of a nonzero complex L² vector form an independent
family. Translating a putative relation by its largest shift places the two halves
at disjoint indices of the ordinary arithmetic translation family.
-/

open Complex MeasureTheory
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

private theorem translate_add (a b : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    RHTower.MellinL2.additiveTranslationUnitary a
      (RHTower.MellinL2.additiveTranslationUnitary b f) =
        RHTower.MellinL2.additiveTranslationUnitary (a + b) f := by
  change Lp.compMeasurePreserving _ (RHTower.MellinL2.realTranslation_measurePreserving a)
      (Lp.compMeasurePreserving _ (RHTower.MellinL2.realTranslation_measurePreserving b) f) =
    Lp.compMeasurePreserving _ (RHTower.MellinL2.realTranslation_measurePreserving (a + b)) f
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      ((RHTower.MellinL2.realTranslation_measurePreserving b).comp
        (RHTower.MellinL2.realTranslation_measurePreserving a)),
    Lp.coeFn_compMeasurePreserving f (RHTower.MellinL2.realTranslation_measurePreserving (a + b))]
    with x hx hy
  rw [hx, hy]
  simp [RHTower.MellinL2.realTranslationEquiv, Function.comp_apply]

private theorem independent_disjoint_pair_sums
    {ι κ M : Type*} [Fintype ι] [AddCommGroup M] [Module ℂ M]
    {v : κ → M} (hv : LinearIndependent ℂ v) (p q : ι → κ)
    (hp : Function.Injective p) (hpq : ∀ i j, p i ≠ q j) :
    LinearIndependent ℂ (fun i => v (p i) + v (q i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let d : κ →₀ ℂ := ∑ j, (Finsupp.single (p j) (c j) + Finsupp.single (q j) (c j))
  have hd : Finsupp.linearCombination ℂ v d = 0 := by
    simpa only [d, map_sum, map_add, Finsupp.linearCombination_single, smul_add] using hc
  have hz : d = 0 := (linearIndependent_iffₛ.mp hv) d 0 (hd.trans (map_zero _).symm)
  have hi := congrArg (fun z : κ →₀ ℂ => z (p i)) hz
  have hq : ∀ j, q j ≠ p i := fun j h => hpq i j h.symm
  simpa [d, Finsupp.single_apply, hq, hp.eq_iff] using hi

/-- Symmetric arithmetic translates remain independent. -/
theorem linearIndependent_arithmetic_cosine_translates (n : ℕ) {h : ℝ} (hh : h ≠ 0)
    {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ≠ 0) :
    LinearIndependent ℂ (fun i : Fin n =>
      RHTower.MellinL2.additiveTranslationUnitary (((i : ℝ) + 1) * h) f +
        RHTower.MellinL2.additiveTranslationUnitary (-(((i : ℝ) + 1) * h)) f) := by
  classical
  let g := RHTower.MellinL2.additiveTranslationUnitary (-(n : ℝ) * h) f
  have hg : g ≠ 0 := by
    intro hz
    exact hf ((RHTower.MellinL2.additiveTranslationUnitary (-(n : ℝ) * h)).injective
      (hz.trans (map_zero _).symm))
  let p : Fin n → Fin (2 * n + 1) := fun i => ⟨n + i.val + 1, by omega⟩
  let q : Fin n → Fin (2 * n + 1) := fun i => ⟨n - (i.val + 1), by omega⟩
  have hp : Function.Injective p := by
    intro i j hij
    have hv := congrArg Fin.val hij
    apply Fin.ext
    dsimp [p] at hv
    omega
  have hpq : ∀ i j, p i ≠ q j := by
    intro i j hij
    have hv := congrArg Fin.val hij
    dsimp [p, q] at hv
    omega
  have hv := independent_disjoint_pair_sums
    (linearIndependent_arithmetic_L2_translates (2 * n + 1) hh hg) p q hp hpq
  have hplus (i : Fin n) :
      RHTower.MellinL2.additiveTranslationUnitary ((p i : ℝ) * h) g =
        RHTower.MellinL2.additiveTranslationUnitary (((i : ℝ) + 1) * h) f := by
    change RHTower.MellinL2.additiveTranslationUnitary ((p i : ℝ) * h)
      (RHTower.MellinL2.additiveTranslationUnitary (-(n : ℝ) * h) f) = _
    rw [translate_add]
    apply congrArg (fun r : ℝ => RHTower.MellinL2.additiveTranslationUnitary r f)
    simp only [p, Nat.cast_add, Nat.cast_one]
    ring
  have hminus (i : Fin n) :
      RHTower.MellinL2.additiveTranslationUnitary ((q i : ℝ) * h) g =
        RHTower.MellinL2.additiveTranslationUnitary (-(((i : ℝ) + 1) * h)) f := by
    change RHTower.MellinL2.additiveTranslationUnitary ((q i : ℝ) * h)
      (RHTower.MellinL2.additiveTranslationUnitary (-(n : ℝ) * h) f) = _
    rw [translate_add]
    apply congrArg (fun r : ℝ => RHTower.MellinL2.additiveTranslationUnitary r f)
    simp only [q, Nat.cast_sub (by omega : i.val + 1 ≤ n), Nat.cast_add,
      Nat.cast_one]
    ring
  simpa only [hplus, hminus] using hv

end GaloisForLFunctions.HTGeometry
