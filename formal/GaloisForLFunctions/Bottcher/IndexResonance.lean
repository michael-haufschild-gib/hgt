/-
# Index formula × resonance: the generic resonance pinning is impossible across the cycle

This file welds the **holomorphic fixed-point index formula** (`IndexFormula.sum_index_fixedPoints_eq_zero`)
to the **resonance pinning** (`ResonanceOrder.resonance_order`) — the two halves of the Zdunik-free route to
the connected-case natural-boundary obstruction (the dynamical core of `hGtr` and the hRigid
`TranscendentalOverAdjoin`).

`resonance_order` says: at a period-`p` point `z` with a continuation `g` of `φ_c` satisfying the Böttcher
functional equation `g∘f^[p] = g^{2^p}`, `g z` a `(2^p-1)`-th root of unity, and `g-g(z)` vanishing to
order `n`, the multiplier is *pinned*, `λ_z^n = 2^p`. In the generic `n = 1` case this is `λ_z = 2^p`
exactly.

The index formula says the multiplier spectrum is non-degenerate: not every fixed point of `f_c^[p]` can
have multiplier `2^p` (`exists_fixedPoint_multiplier_ne_two_pow`). So the two cannot both hold across the
whole cycle: **a hypothetical relation cannot present an everywhere-good, simple (`n=1`) continuation at
every fixed point of `f_c^[p]`.** Some fixed point must be a genuine natural-boundary point — no analytic
continuation with a simple root-of-unity value. This localises the obstruction algebraically, with no
ergodic (Lyapunov/Zdunik) input: the failure point is forced by a residue identity.

New file (hRigid / connected lane, Zdunik-free route). Consumes only `IndexFormula`, `ResonanceOrder`,
and the iterate-analyticity layer.
-/
import GaloisForLFunctions.Bottcher.IndexFormula
import GaloisForLFunctions.Bottcher.IndexEstimate
import GaloisForLFunctions.Bottcher.ResonanceOrder
import GaloisForLFunctions.Bottcher.CoverConstruction

open Polynomial Filter Topology Set Finset

namespace Bottcher

/-- `f_c^[p] - X` is nonzero (degree `2^p ≥ 1` for `p ≥ 1`). -/
theorem fixedPointPoly_ne_zero (c : ℂ) {p : ℕ} (hp : 1 ≤ p) : fixedPointPoly c p ≠ 0 := by
  intro h
  have hdeg := fixedPointPoly_natDegree c hp
  rw [h, natDegree_zero] at hdeg
  have hpos : (0 : ℕ) < 2 ^ p := by positivity
  omega

/-- **The index formula kills the generic resonance pinning across the whole cycle.** Suppose `f_c^[p] - X`
is separable (no parabolic period-`p` cycle) and, at *every* fixed point `z` of `f_c^[p]`, there is an
analytic `g` with the Böttcher functional equation `g∘f^[p] = g^{2^p}` near `z`, value `g z = ζ` a nonzero
`(2^p-1)`-th root of unity, and *simple* contact `analyticOrderAt (g - ζ) z = 1`. Then `False`.

By `resonance_order` (with `n = 1`) each such `z` has multiplier `λ_z = 2^p`; but
`exists_fixedPoint_multiplier_ne_two_pow` produces a fixed point with `λ_z ≠ 2^p` — contradiction. So no
relation can yield an everywhere-good simple continuation on the period-`p` cycle: at least one fixed point
is a genuine natural boundary of `φ_c`. This is the Zdunik-free localisation of the connected obstruction —
the failure is forced by the residue identity, not by an ergodic multiplier-variation argument. -/
theorem not_forall_simple_resonant (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (hgood : ∀ z ∈ (fixedPointPoly c p).roots.toFinset,
      ∃ (g : ℂ → ℂ) (ζ : ℂ), AnalyticAt ℂ g z ∧ g z = ζ ∧ ζ ≠ 0 ∧ ζ ^ (2 ^ p) = ζ ∧
        (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p)) ∧
        analyticOrderAt (fun y => g y - ζ) z = (1 : ℕ∞)) :
    False := by
  obtain ⟨z, hz, hne⟩ := exists_fixedPoint_multiplier_ne_two_pow c hp hsep
  obtain ⟨g, ζ, hg, hgz, hζ0, hζ, heq, hord⟩ := hgood z hz
  have hFz : (quadratic c)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp (Multiset.mem_toFinset.mp hz)
  have hF : AnalyticAt ℂ ((quadratic c)^[p]) z := analyticOnNhd_quadratic_iterate c p z (mem_univ z)
  have hlam : HasDerivAt ((quadratic c)^[p])
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) z := hasDerivAt_quadratic_iterate c z p
  have hres := resonance_order (d := 2 ^ p) (n := 1) (Nat.one_le_pow p 2 (by norm_num))
    hF hg hFz hlam hgz hζ0 hζ heq hord
  rw [pow_one] at hres
  apply hne
  rw [hres]; push_cast; ring

/-- **The root-of-unity value is automatic.** If `g ∘ f^[p] = g^{2^p}` near a fixed point `z` of `f^[p]`,
then `g z ^ {2^p} = g z` (evaluate the functional equation at the fixed point). So `g z` is a
`(2^p-1)`-th root of unity whenever it is nonzero — no separate hypothesis needed. -/
theorem pow_eq_self_of_funEq {c : ℂ} {p : ℕ} {g : ℂ → ℂ} {z : ℂ}
    (hFz : (quadratic c)^[p] z = z)
    (heq : (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p))) :
    g z ^ (2 ^ p) = g z := by
  have hpt : g ((quadratic c)^[p] z) = g z ^ (2 ^ p) := heq.eq_of_nhds
  rw [hFz] at hpt
  exact hpt.symm

/-- **Per-point multiplier pinning.** At a fixed point `z` of `f_c^[p]` carrying a *simple* (`n = 1`) good
continuation `g` of `φ_c` (Böttcher functional equation, nonzero value `g z`), the multiplier is pinned to
`2^p`: `resonance_order` with `n = 1`. The `(2^p-1)`-th-root-of-unity condition on `g z` is derived from
the functional equation (`pow_eq_self_of_funEq`), not assumed. -/
theorem multiplier_eq_two_pow_of_good (c : ℂ) {p : ℕ} {z : ℂ}
    (hFz : (quadratic c)^[p] z = z)
    {g : ℂ → ℂ} {ζ : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z = ζ) (hζ0 : ζ ≠ 0)
    (heq : (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p)))
    (hord : analyticOrderAt (fun y => g y - ζ) z = (1 : ℕ∞)) :
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p := by
  have hζ : ζ ^ (2 ^ p) = ζ := by rw [← hgz]; exact pow_eq_self_of_funEq hFz heq
  have hF : AnalyticAt ℂ ((quadratic c)^[p]) z := analyticOnNhd_quadratic_iterate c p z (mem_univ z)
  have hlam : HasDerivAt ((quadratic c)^[p])
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) z := hasDerivAt_quadratic_iterate c z p
  have hres := resonance_order (d := 2 ^ p) (n := 1) (Nat.one_le_pow p 2 (by norm_num))
    hF hg hFz hlam hgz hζ0 hζ heq hord
  rw [pow_one] at hres
  rw [hres]; push_cast; ring

/-- **The index-formula obstruction, reduced to branch data + the no-attracting-fixed-point geometry.**
This is the consumable endpoint of the Zdunik-free route. Suppose `f_c^[p] - X` is separable (`p ≥ 1`),
and the period-`p` cycle splits into:
* the bulk `roots ∖ B`, at each point of which a relation's continuation `g` is **good and simple** —
  analytic with the Böttcher functional equation, a nonzero `(2^p-1)`-th-root-of-unity value, and order-`1`
  contact (`hbranch`); `resonance_order` then pins each bulk multiplier to `2^p`;
* a finite exceptional set `B` of **repelling fixed points** of `f_c` (`hrep`), whose total index mass is
  small (`hsmall`, automatic for large `p` since the bulk `≍ 2^p` dominates `≍ (2/‖2z‖)^p`).
Then `False`.

So a relation cannot present good simple continuations on the whole bulk while `B` is repelling — the
residue identity forbids it, with no ergodic input. The remaining work to discharge an actual relation is
exactly: produce the bulk branches from the relation (the existing `ConnectedTranscendence`/
`BranchContinuation` branch machinery, off the finite discriminant locus) and identify `B` with the
repelling fixed points (the no-attracting-fixed-point parameters). -/
theorem false_of_branches_and_repelling (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hB : B ⊆ (fixedPointPoly c p).roots.toFinset)
    (hbranch : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        ∃ (g : ℂ → ℂ) (ζ : ℂ), AnalyticAt ℂ g z ∧ g z = ζ ∧ ζ ≠ 0 ∧
          (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p)) ∧
          analyticOrderAt (fun y => g y - ζ) z = (1 : ℕ∞))
    (hrep : ∀ z ∈ B, quadratic c z = z ∧ 1 < ‖2 * z‖ ^ p)
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False := by
  refine false_of_pinned_bulk_repelling c hp hsep B hB ?_ hrep hsmall
  intro z hz
  obtain ⟨g, ζ, hg, hgz, hζ0, heq, hord⟩ := hbranch z hz
  have hFz : (quadratic c)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp
      (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1)
  exact multiplier_eq_two_pow_of_good c hFz hg hgz hζ0 heq hord

end Bottcher
