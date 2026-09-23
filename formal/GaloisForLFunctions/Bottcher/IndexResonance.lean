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

/-- **Order-`1` from a nonzero derivative.** If `g` is analytic at `z` with `g z = ζ` and `deriv g z ≠ 0`,
then `g - ζ` vanishes to order exactly `1` at `z`. Translating to `0` and applying the order-`1` Taylor
factorization `g(w) - ζ = (w - z)·u(w)` with `u z = deriv g z ≠ 0`. This makes the simple-contact clause of
the resonance pinning dischargeable from the generic simple-root condition `deriv g z ≠ 0`, with no explicit
`analyticOrderAt` reasoning. -/
theorem analyticOrderAt_eq_one_of_deriv_ne {g : ℂ → ℂ} {z ζ : ℂ}
    (hg : AnalyticAt ℂ g z) (hgz : g z = ζ) (hd : deriv g z ≠ 0) :
    analyticOrderAt (fun y => g y - ζ) z = (1 : ℕ∞) := by
  set h : ℂ → ℂ := fun y => g y - ζ with hh
  have han : AnalyticAt ℂ h z := hg.sub analyticAt_const
  have hhz : h z = 0 := by simp [hh, hgz]
  have hderivh : deriv h z = deriv g z := by rw [hh]; exact deriv_sub_const ζ
  set φ : ℂ → ℂ := fun y => y - z with hφ
  have hφz : φ z = 0 := by simp [hφ]
  have hφan : AnalyticAt ℂ φ z := analyticAt_id.sub analyticAt_const
  have hφderiv : HasDerivAt φ 1 z := by simpa [hφ] using (hasDerivAt_id z).sub_const z
  have hsub0 : AnalyticAt ℂ (fun w : ℂ => w + z) 0 := analyticAt_id.add analyticAt_const
  have hsh : AnalyticAt ℂ (fun w => h (w + z)) 0 := han.comp_of_eq hsub0 (by simp)
  obtain ⟨F, hFan, hFeq⟩ := hsh.exists_eventuallyEq_sum_add_pow_mul 1
  have htend : Tendsto φ (𝓝 z) (𝓝 0) := by
    have : Tendsto φ (𝓝 z) (𝓝 (φ z)) := (hφan.continuousAt).tendsto
    rwa [hφz] at this
  set u : ℂ → ℂ := fun y => F (φ y) with hu
  have huan : AnalyticAt ℂ u z := hFan.comp_of_eq hφan hφz
  have huz0 : u z = F 0 := by show F (φ z) = F 0; rw [hφz]
  have hfac : h =ᶠ[𝓝 z] fun y => (y - z) ^ (1 : ℕ) • u y := by
    filter_upwards [htend.eventually hFeq] with y hy
    have hyz : φ y + z = y := by simp [hφ]
    rw [hyz, Finset.sum_range_one, iteratedDeriv_zero] at hy
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_smul, pow_one] at hy
    rw [show h (0 + z) = (0 : ℂ) from by rw [zero_add, hhz], zero_add] at hy
    rw [hy]
    show φ y • F (φ y) = (y - z) ^ (1 : ℕ) • F (φ y)
    simp only [pow_one, hφ]
  have hHD : HasDerivAt (fun y => (y - z) ^ (1 : ℕ) • u y) (F 0) z := by
    have hsub : HasDerivAt (fun y : ℂ => y - z) 1 z := (hasDerivAt_id z).sub_const z
    have hF0 : HasDerivAt F (deriv F 0) (φ z) := by rw [hφz]; exact hFan.differentiableAt.hasDerivAt
    have h2 : HasDerivAt u (deriv F 0) z := by
      have := HasDerivAt.comp z hF0 hφderiv
      simpa [hu, Function.comp_def] using this
    have hmul := hsub.mul h2
    simp only [pow_one, smul_eq_mul, sub_self, one_mul, zero_mul, add_zero, huz0] at hmul ⊢
    exact hmul
  have hduniq : F 0 = deriv h z :=
    (hHD.congr_of_eventuallyEq hfac).unique (han.differentiableAt.hasDerivAt)
  have huz : u z ≠ 0 := by rw [huz0, hduniq, hderivh]; exact hd
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) by simp, han.analyticOrderAt_eq_natCast]
  exact ⟨u, huan, huz, hfac⟩

/-- **Per-point multiplier pinning.** At a fixed point `z` of `f_c^[p]` carrying a *simple* good
continuation `g` of `φ_c` (Böttcher functional equation, nonzero value `g z`, nonzero derivative
`deriv g z`), the multiplier is pinned to `2^p`: `resonance_order` with `n = 1`. The
`(2^p-1)`-th-root-of-unity condition (`pow_eq_self_of_funEq`) and the order-`1` contact
(`analyticOrderAt_eq_one_of_deriv_ne`) are both derived — only the natural simple-root data is assumed. -/
theorem multiplier_eq_two_pow_of_good (c : ℂ) {p : ℕ} {z : ℂ}
    (hFz : (quadratic c)^[p] z = z)
    {g : ℂ → ℂ} {ζ : ℂ} (hg : AnalyticAt ℂ g z) (hgz : g z = ζ) (hζ0 : ζ ≠ 0)
    (heq : (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p)))
    (hgd : deriv g z ≠ 0) :
    (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) = (2 : ℂ) ^ p := by
  have hord : analyticOrderAt (fun y => g y - ζ) z = (1 : ℕ∞) :=
    analyticOrderAt_eq_one_of_deriv_ne hg hgz hgd
  have hζ : ζ ^ (2 ^ p) = ζ := by rw [← hgz]; exact pow_eq_self_of_funEq hFz heq
  have hF : AnalyticAt ℂ ((quadratic c)^[p]) z := analyticOnNhd_quadratic_iterate c p z (mem_univ z)
  have hlam : HasDerivAt ((quadratic c)^[p])
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) z := hasDerivAt_quadratic_iterate c z p
  have hres := resonance_order (d := 2 ^ p) (n := 1) (Nat.one_le_pow p 2 (by norm_num))
    hF hg hFz hlam hgz hζ0 hζ heq hord
  rw [pow_one] at hres
  rw [hres]; push_cast; ring

/-- A fixed point of `f_c` is a root of `f_c^[p] - X` (period `1` divides `p`). Feeds `B ⊆ roots`. -/
theorem fixed_mem_fixedPointPoly_roots {c z : ℂ} {p : ℕ} (hp : 1 ≤ p) (h : quadratic c z = z) :
    z ∈ (fixedPointPoly c p).roots.toFinset := by
  rw [Multiset.mem_toFinset, mem_roots (fixedPointPoly_ne_zero c hp), fixedPointPoly_isRoot_iff]
  exact Function.iterate_fixed h p

/-- A repelling fixed point (`‖2z‖ > 1`) of `f_c` has `‖2z‖^p > 1` for `p ≥ 1`. Feeds `hrep`. -/
theorem one_lt_norm_two_mul_pow {z : ℂ} {p : ℕ} (hp : 1 ≤ p) (h : 1 < ‖2 * z‖) :
    1 < ‖2 * z‖ ^ p := by
  calc (1 : ℝ) = 1 ^ p := (one_pow p).symm
    _ < ‖2 * z‖ ^ p := by
        apply pow_lt_pow_left₀ h (by norm_num) (by omega)

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
          deriv g z ≠ 0)
    (hrep : ∀ z ∈ B, quadratic c z = z ∧ 1 < ‖2 * z‖ ^ p)
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False := by
  refine false_of_pinned_bulk_repelling c hp hsep B hB ?_ hrep hsmall
  intro z hz
  obtain ⟨g, ζ, hg, hgz, hζ0, heq, hgd⟩ := hbranch z hz
  have hFz : (quadratic c)^[p] z = z := by
    rw [← fixedPointPoly_isRoot_iff]
    exact (mem_roots (fixedPointPoly_ne_zero c hp)).mp
      (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hz).1)
  exact multiplier_eq_two_pow_of_good c hFz hg hgz hζ0 heq hgd

/-- **The connected-case obstruction with the no-attracting-fixed-point carve-out made explicit.** The
exceptional set `B` is a finite set of **repelling fixed points** of `f_c` (`f_c z = z`, `‖2z‖ > 1`); `B ⊆
roots` and the per-element `hrep` are then automatic (`fixed_mem_fixedPointPoly_roots`,
`one_lt_norm_two_mul_pow`). So a relation that supplies natural simple branches at every cycle point off `B`
is impossible whenever the exceptional mass is small (true for large `p`, `eventually_exceptional_mass_small`).
This is the cleanest statement of the index route for parameters with no attracting fixed point: the obstruction
is reduced to **just** the bulk branches (from the relation) + the repelling fixed-point geometry. -/
theorem false_of_branches_repelling_fixed (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hsep : (fixedPointPoly c p).Separable)
    (B : Finset ℂ) (hBfix : ∀ z ∈ B, quadratic c z = z) (hBrep : ∀ z ∈ B, 1 < ‖2 * z‖)
    (hbranch : ∀ z ∈ (fixedPointPoly c p).roots.toFinset \ B,
        ∃ (g : ℂ → ℂ) (ζ : ℂ), AnalyticAt ℂ g z ∧ g z = ζ ∧ ζ ≠ 0 ∧
          (fun y => g ((quadratic c)^[p] y)) =ᶠ[𝓝 z] (fun y => g y ^ (2 ^ p)) ∧
          deriv g z ≠ 0)
    (hsmall : ((2 : ℝ) ^ p - 1) * ∑ z ∈ B, (‖2 * z‖ ^ p - 1)⁻¹
      < (((fixedPointPoly c p).roots.toFinset \ B).card : ℝ)) :
    False := by
  refine false_of_branches_and_repelling c hp hsep B ?_ hbranch ?_ hsmall
  · intro z hz; exact fixed_mem_fixedPointPoly_roots hp (hBfix z hz)
  · intro z hz; exact ⟨hBfix z hz, one_lt_norm_two_mul_pow hp (hBrep z hz)⟩

end Bottcher
