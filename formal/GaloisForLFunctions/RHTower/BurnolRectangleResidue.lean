import GaloisForLFunctions.RHTower.BurnolIntegrand
import GaloisForLFunctions.HTGeometry.RectangleResidueTheorem
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Burnol's rectangle: the residue identity

Brick R2 of Theorem 5.2.  The general-order rectangle residue theorem
(`rectangleIntegral'_eq_sum_laurentCoeff`) is applied to Burnol's integrand

`H(s) = G(s)·ζ(Z)/(ζ(s)·(Z−s))`

on a rectangle whose interior contains `Z`, the point `1`, the finitely many zeros of `ζ` it meets,
and the finitely many singularities of `G`.

The pole set is taken *large*: it contains `1` and the singular points of `G` even when the
integrand turns out to be regular there.  This is deliberate — in Lean `G = N/(s(1−s))` is
junk-valued at `0` and `1`, so it is literally not `AnalyticAt` there even though the singularity is
removable, and it is far easier to show that the Laurent coefficient vanishes (the meromorphic order
is nonnegative) than to repair the value.

## Main results

* `zetaZeroFinset`, `burnolPoleSet`
* `rectangleIntegral'_burnolIntegrand` — the residue identity.
* `meromorphicOrderAt_burnolIntegrand` — `ord H = ord G − ord ζ` away from `Z`.
* `laurentCoeff_burnolIntegrand_eq_zero_of_le` — a criterion for a point to contribute no residue.
-/

open Complex Set Topology Filter MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The pole set -/

/-- The zeros of `ζ` inside a rectangle, as a `Finset`. -/
def zetaZeroFinset (z w : ℂ) : Finset ℂ :=
  (finite_riemannZeta_zeros_rectangle z w).toFinset

theorem mem_zetaZeroFinset {z w s : ℂ} :
    s ∈ zetaZeroFinset z w ↔ s ∈ Rectangle z w ∧ riemannZeta s = 0 := by
  rw [zetaZeroFinset, Set.Finite.mem_toFinset]
  exact Iff.rfl

/-- The pole set of Burnol's integrand on a rectangle: the point `Z`, the point `1`, the prescribed
singularities of `G`, and the zeros of `ζ` the rectangle meets. -/
def burnolPoleSet (z w Z : ℂ) (Pbad : Finset ℂ) : Finset ℂ :=
  insert Z (insert 1 (Pbad ∪ zetaZeroFinset z w))

theorem mem_burnolPoleSet {z w Z p : ℂ} {Pbad : Finset ℂ} :
    p ∈ burnolPoleSet z w Z Pbad ↔
      p = Z ∨ p = 1 ∨ p ∈ Pbad ∨ p ∈ zetaZeroFinset z w := by
  simp [burnolPoleSet]

/-! ## The residue identity -/

/-- **The rectangle residue identity for Burnol's integrand.** -/
theorem rectangleIntegral'_burnolIntegrand {G : ℂ → ℂ} {Z z w : ℂ} {Pbad : Finset ℂ}
    (hz : z.re ≤ w.re) (hw : z.im ≤ w.im)
    (hGmero : ∀ s : ℂ, MeromorphicAt G s)
    (hGana : ∀ s ∈ Rectangle z w, s ∉ Pbad → s ≠ 1 → AnalyticAt ℂ G s)
    (hnbhd : ∀ p ∈ burnolPoleSet z w Z Pbad, Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (burnolIntegrand G Z) z w
      = ∑ p ∈ burnolPoleSet z w Z Pbad, laurentCoeff (burnolIntegrand G Z) p (-1) := by
  refine rectangleIntegral'_eq_sum_laurentCoeff hz hw hnbhd
    (fun p _ => meromorphicAt_burnolIntegrand (hGmero p)) ?_
  intro s hs hsP
  rw [mem_burnolPoleSet] at hsP
  push Not at hsP
  obtain ⟨hsZ, hs1, hsbad, hszero⟩ := hsP
  have hζ : riemannZeta s ≠ 0 := by
    intro h
    exact hszero (mem_zetaZeroFinset.2 ⟨hs, h⟩)
  exact analyticAt_burnolIntegrand (hGana s hs hsbad hs1) hζ hs1 hsZ

/-! ## Orders and vanishing residues -/

/-- Away from `Z`, the order of the integrand is the order of `G` minus the order of `ζ`. -/
theorem meromorphicOrderAt_burnolIntegrand {G : ℂ → ℂ} {Z p : ℂ}
    (hG : MeromorphicAt G p) (hZ : riemannZeta Z ≠ 0) (hpZ : p ≠ Z) :
    meromorphicOrderAt (burnolIntegrand G Z) p
      = meromorphicOrderAt G p - meromorphicOrderAt riemannZeta p := by
  have hζm : MeromorphicAt riemannZeta p := meromorphicAt_riemannZeta_everywhere p
  have hlin : AnalyticAt ℂ (fun u : ℂ => Z - u) p := analyticAt_const.sub analyticAt_id
  have hlinne : (fun u : ℂ => Z - u) p ≠ 0 := by
    simpa using sub_ne_zero.2 (Ne.symm hpZ)
  have hfun : burnolIntegrand G Z
      = (G * fun _ : ℂ => riemannZeta Z) / (riemannZeta * fun u : ℂ => Z - u) := by
    funext u
    simp [burnolIntegrand, Pi.div_apply, Pi.mul_apply]
  rw [hfun, meromorphicOrderAt_div
    (hG.mul analyticAt_const.meromorphicAt) (hζm.mul hlin.meromorphicAt)]
  congr 1
  · rw [mul_comm]
    exact meromorphicOrderAt_mul_of_ne_zero (g := fun _ : ℂ => riemannZeta Z)
      analyticAt_const hZ
  · rw [meromorphicOrderAt_mul hζm hlin.meromorphicAt,
      (hlin.meromorphicOrderAt_eq), hlin.analyticOrderAt_eq_zero.2 hlinne]
    simp

/-! ### Order arithmetic in `WithTop ℤ` -/

theorem withTop_sub_nonneg_of_le {x : WithTop ℤ} {m : ℤ} (h : (m : WithTop ℤ) ≤ x) :
    (0 : WithTop ℤ) ≤ x - (m : WithTop ℤ) := by
  induction x with
  | top => simp
  | coe n =>
      have hmn : m ≤ n := by exact_mod_cast h
      have h0 : (0 : ℤ) ≤ n - m := by omega
      exact_mod_cast h0

/-- An analytic function has nonnegative meromorphic order. -/
theorem meromorphicOrderAt_nonneg_of_analyticAt {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    (0 : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  rw [hf.meromorphicOrderAt_eq]
  induction analyticOrderAt f p with
  | top => simp
  | coe n => simp

/-- An analytic function vanishing at a point has meromorphic order at least one there. -/
theorem one_le_meromorphicOrderAt_of_eq_zero {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p)
    (h : f p = 0) : ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  rw [hf.meromorphicOrderAt_eq]
  have hne : analyticOrderAt f p ≠ 0 := by simp [hf.analyticOrderAt_eq_zero, h]
  induction hx : analyticOrderAt f p with
  | top => simp
  | coe n =>
      have hn : n ≠ 0 := by rintro rfl; exact hne (by simp [hx])
      have h1 : (1 : ℤ) ≤ (n : ℤ) := by omega
      simpa using h1

/-- A point contributes no residue as soon as the order of the integrand there is nonnegative. -/
theorem laurentCoeff_burnolIntegrand_eq_zero_of_le {G : ℂ → ℂ} {Z p : ℂ}
    (hG : MeromorphicAt G p) (hord : 0 ≤ meromorphicOrderAt (burnolIntegrand G Z) p) :
    laurentCoeff (burnolIntegrand G Z) p (-1) = 0 :=
  laurentCoeff_eq_zero_of_meromorphicOrderAt_nonneg (meromorphicAt_burnolIntegrand hG) hord
    (by norm_num)

/-- **The vanishing criterion used at `0`, at `1` and at the trivial zeros.**  If the order of `G`
at `p` is at least the order of `ζ` there, the integrand is regular at `p` and contributes no
residue. -/
theorem laurentCoeff_burnolIntegrand_eq_zero_of_order_ge {G : ℂ → ℂ} {Z p : ℂ} {m : ℤ}
    (hG : MeromorphicAt G p) (hZ : riemannZeta Z ≠ 0) (hpZ : p ≠ Z)
    (hζord : meromorphicOrderAt riemannZeta p = (m : WithTop ℤ))
    (hGord : (m : WithTop ℤ) ≤ meromorphicOrderAt G p) :
    laurentCoeff (burnolIntegrand G Z) p (-1) = 0 := by
  refine laurentCoeff_burnolIntegrand_eq_zero_of_le hG ?_
  rw [meromorphicOrderAt_burnolIntegrand hG hZ hpZ, hζord]
  exact withTop_sub_nonneg_of_le hGord

end

end RHTower
