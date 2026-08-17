import GaloisForLFunctions.RHTower.ProlateSharpMassRatio
import GaloisForLFunctions.RHTower.ProlateIndexedProfileRungLimit

/-!
# A forbidden-region anchor for the central amplitude

The Hermite function `phi_(2n)` has finitely many zeros, because it is a nonzero polynomial times a
Gaussian.  So every interval beyond the classical turning point `sqrt(4n+1)` contains a point where
it does not vanish, and such a point can be fixed once and for all as the *anchor* of the mode.

In the rescaled variable the anchor sits at a fixed height, so the rung profile limit compares the
endpoint-normalized radial datum at the anchor with its central value:

```text
R(x_0/sqrt c) / R(0)  →  phi_(2n)(x_0) / phi_(2n)(0)  ≠  0 .
```

This is the comparison that converts a bound on the amplitude in the forbidden region into a bound
on the central amplitude, with no loss of any power of the bandwidth.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

/-- The Hermite function does not vanish identically on any interval. -/
theorem exists_hermiteFun_ne_zero_Ioo (m : ℕ) {A B : ℝ} (hAB : A < B) :
    ∃ x ∈ Ioo A B, hermiteFun m x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  set P : Polynomial ℝ := (Polynomial.hermite m).map (Int.castRingHom ℝ) with hP
  have hPmonic : P.Monic := (Polynomial.hermite_monic m).map _
  have heval : ∀ x : ℝ, Polynomial.aeval x (Polynomial.hermite m) = P.eval x := by
    intro x
    rw [hP, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rfl
  have hroot : {y : ℝ | P.IsRoot y}.Infinite := by
    have hinj : Set.InjOn (fun x : ℝ => Real.sqrt 2 * x) (Ioo A B) := by
      intro x _ y _ hxy
      have h2 : Real.sqrt 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ h2 hxy
    have himg : ((fun x : ℝ => Real.sqrt 2 * x) '' Ioo A B).Infinite :=
      (Set.Ioo_infinite hAB).image hinj
    refine himg.mono ?_
    rintro y ⟨x, hx, rfl⟩
    have h := hcon x hx
    have hexp : Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)) ≠ 0 := (Real.exp_pos _).ne'
    have hval : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)
        * Real.exp (-((Real.sqrt 2 * x) ^ 2 / 4)) = 0 := h
    have hz : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m) = 0 := by
      rcases mul_eq_zero.1 hval with h1 | h2
      · exact h1
      · exact absurd h2 hexp
    show P.IsRoot (Real.sqrt 2 * x)
    rw [Polynomial.IsRoot, ← heval]
    exact hz
  exact hPmonic.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ hroot)

/-- A point beyond the classical turning point at which the Hermite function of the rung does not
vanish. -/
def prolateAnchor (n : ℕ) : ℝ :=
  Classical.choose (exists_hermiteFun_ne_zero_Ioo (2 * n)
    (A := 2 * Real.sqrt (4 * (n : ℝ) + 1)) (B := 2 * Real.sqrt (4 * (n : ℝ) + 1) + 1)
    (by linarith))

theorem prolateAnchor_spec (n : ℕ) :
    prolateAnchor n ∈ Ioo (2 * Real.sqrt (4 * (n : ℝ) + 1))
        (2 * Real.sqrt (4 * (n : ℝ) + 1) + 1) ∧
      hermiteFun (2 * n) (prolateAnchor n) ≠ 0 :=
  Classical.choose_spec (exists_hermiteFun_ne_zero_Ioo (2 * n)
    (A := 2 * Real.sqrt (4 * (n : ℝ) + 1)) (B := 2 * Real.sqrt (4 * (n : ℝ) + 1) + 1)
    (by linarith))

theorem prolateAnchor_pos (n : ℕ) : 0 < prolateAnchor n := by
  have h := (prolateAnchor_spec n).1.1
  have hs : (0 : ℝ) ≤ Real.sqrt (4 * (n : ℝ) + 1) := Real.sqrt_nonneg _
  linarith

theorem hermiteFun_prolateAnchor_ne_zero (n : ℕ) :
    hermiteFun (2 * n) (prolateAnchor n) ≠ 0 := (prolateAnchor_spec n).2

/-- **The anchor comparison.**  The endpoint-normalized radial datum at the anchor, relative to its
central value, converges to the corresponding Hermite quotient, which is nonzero. -/
theorem tendsto_anchor_ratio (n : ℕ) :
    Tendsto (fun a : ℝ =>
        hermiteFun (2 * n) 0
          * ((signedModeRadialData a n).R
              (prolateAnchor n / Real.sqrt (signedModeRadialBandwidth a))
            / (signedModeRadialData a n).R 0))
      atTop (𝓝 (hermiteFun (2 * n) (prolateAnchor n))) := by
  have hK : 0 < prolateAnchor n := prolateAnchor_pos n
  have hmem : prolateAnchor n ∈ Icc (0 : ℝ) (prolateAnchor n) := ⟨hK.le, le_rfl⟩
  have hbase := tendsto_indexedOscillatorProfile_hermiteRung n hK (prolateAnchor n) hmem
  have hmap : Filter.map (Subtype.val :
      GaloisForLFunctions.RHTower.ProlatePositiveAperture → ℝ) atTop = atTop := by
    refine Filter.map_val_atTop_of_Ici_subset (a := (1 : ℝ)) (s := {x : ℝ | 0 < x}) ?_
    intro x hx
    have hx1 : (1 : ℝ) ≤ x := hx
    exact lt_of_lt_of_le zero_lt_one hx1
  rw [← hmap, Filter.tendsto_map'_iff]
  exact hbase

end RHTower

end
