import GaloisForLFunctions.RHTower.DeningerFreeGroupIsolated

/-!
# Distinct basis elements of a free group stay disjoint under conjugation

No conjugate of a nonzero power of a basis element is a power of a different one: the conjugate is
short, so the conjugacy criterion puts the conjugator in the factor of the first element, and then
the conjugate lies in two different factor images, hence in the trivial base group.

* `deningerFreeGroup_conj_disjoint` : the disjointness.
-/

namespace RHTower

open Monoid Monoid.PushoutI RootAdjunction

universe u

/-- **No conjugate of a nonzero power of a basis element is a power of another one.** -/
theorem deningerFreeGroup_conj_disjoint (ι : Type u) (i j : ι) (hij : i ≠ j) (w : FreeGroup ι)
    (c : ℤ) (hc : c ≠ 0) (k : ℤ) :
    w⁻¹ * (FreeGroup.of i) ^ c * w ≠ (FreeGroup.of j) ^ k := by
  classical
  intro hcon
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty (deningerFreeMap ι)
    (fun _ p q _ => Subsingleton.elim p q)
  have hEqi : deningerFreeGroupEquiv ι (FreeGroup.of i) =
      PushoutI.of (φ := deningerFreeMap ι) i deningerRootGen.{u} :=
    deningerFreeToPushout_of ι i
  have hEqj : deningerFreeGroupEquiv ι (FreeGroup.of j) =
      PushoutI.of (φ := deningerFreeMap ι) j deningerRootGen.{u} :=
    deningerFreeToPushout_of ι j
  set v : deningerFreeFactor ι i := deningerRootGen.{u} ^ c with hv
  have hvne : v ≠ 1 := fun h => hc (deningerRootGen_order c h)
  have hvr : v ∉ (deningerFreeMap ι i).range := by
    rintro ⟨p, hp⟩
    refine hvne ?_
    rw [← hp, Subsingleton.elim p 1, map_one]
  have himg : (deningerFreeGroupEquiv ι w)⁻¹ *
      PushoutI.of (φ := deningerFreeMap ι) i v * (deningerFreeGroupEquiv ι w) =
      PushoutI.of (φ := deningerFreeMap ι) j (deningerRootGen.{u} ^ k) := by
    have h1 := congrArg (deningerFreeGroupEquiv ι) hcon
    rw [map_mul, map_mul, map_inv, map_zpow, map_zpow, hEqi, hEqj] at h1
    rw [← map_zpow, ← map_zpow] at h1
    exact h1
  have hshort : deningerLen d ((deningerFreeGroupEquiv ι w)⁻¹ *
      PushoutI.of (φ := deningerFreeMap ι) i v * (deningerFreeGroupEquiv ι w)) ≤ 1 := by
    rw [himg]
    exact deningerLen_of_le_one (d := d) j _
  obtain ⟨x, hx⟩ | ⟨x', p, hp⟩ :=
    deningerShortConj_cases (d := d) i v hvr (deningerFreeGroupEquiv ι w) hshort
  · have hcross : PushoutI.of (φ := deningerFreeMap ι) i (x⁻¹ * v * x) =
        PushoutI.of (φ := deningerFreeMap ι) j (deningerRootGen.{u} ^ k) := by
      rw [← himg, hx, map_mul, map_mul, map_inv]
    obtain ⟨q, hq⟩ := deningerOf_eq_cross (d := d)
      (fun _ p q _ => Subsingleton.elim p q) i j hij _ _ hcross
    refine hvne ?_
    have h2 : x⁻¹ * v * x = 1 := by
      rw [← hq, Subsingleton.elim q 1, map_one]
    calc v = x * (x⁻¹ * v * x) * x⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · refine hvne ?_
    have h2 : x'⁻¹ * v * x' = 1 := by
      rw [hp, Subsingleton.elim p 1, map_one]
    calc v = x' * (x'⁻¹ * v * x') * x'⁻¹ := by group
      _ = 1 := by rw [h2]; group

end RHTower
