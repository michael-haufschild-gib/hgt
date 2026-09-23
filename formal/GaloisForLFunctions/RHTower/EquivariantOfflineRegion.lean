import GaloisForLFunctions.RHTower.EquivariantRootDissolution

/-!
# Equivariant structure is free on symmetric regions off the critical line

A `lineReflect`-invariant open set `U` disjoint from the critical line splits into a
mirror pair: its left part is exactly the `lineReflect`-image of its right part
(`offline_symm_left_eq_mirror_image`).  On such a set, Schwarz-equivariant analytic
structure for a carrier with the real functional equation `f ∘ lineReflect = conj ∘ f`
is *free*: it is determined by, and constructed from, plain analytic data on the right
part alone, by gluing with the Schwarz mirror.

* `exists_equivariant_root_iff_offline` — an equivariant analytic `n`-th root on `U`
  exists iff a plain analytic `n`-th root exists on `U ∩ rightHalf`.  No sign
  condition, no parity condition, any `n`.
* `equivariant_coherentTower_offline_iff` — the same at the pro level: an equivariant
  coherent ℤ₂-tower on `U` exists iff a plain coherent tower exists on `U ∩ rightHalf`.

Together with the symmetric-window dichotomy (`exists_equivariant_root_iff_orders_dvd`:
divisibility ∧ anchor sign) and the boundary classification (`equivariant_pow_root_iff`:
winding divisibility ∧ sign bit), this completes the region-level obstruction map of
the equivariant root theory: the seam-sign bit can obstruct only where the region meets
the line or where a boundary loop crosses it; away from the seam the equivariant theory
*is* the plain theory on half the region.
-/

namespace RHTower

open Complex Set Metric

/-- Membership transport across the mirror: on a `lineReflect`-invariant set,
`s ∈ U ↔ lineReflect s ∈ U`. -/
theorem mem_of_lineReflect_symm {U : Set ℂ} (hUsym : lineReflect ⁻¹' U = U) {s : ℂ} :
    lineReflect s ∈ U ↔ s ∈ U := Set.ext_iff.mp hUsym s

/-- **A symmetric region off the line is a mirror pair.**  The left part of a
`lineReflect`-invariant set is exactly the mirror image of its right part. -/
theorem offline_symm_left_eq_mirror_image {U : Set ℂ}
    (hUsym : lineReflect ⁻¹' U = U) :
    {s ∈ U | s.re < 1 / 2} = lineReflect '' {s ∈ U | 1 / 2 < s.re} := by
  ext s
  constructor
  · rintro ⟨hsU, hslt⟩
    refine ⟨lineReflect s, ⟨(mem_of_lineReflect_symm hUsym).mpr hsU, ?_⟩,
      lineReflect_involutive s⟩
    rw [lineReflect_re]; linarith
  · rintro ⟨w, ⟨hwU, hwgt⟩, rfl⟩
    refine ⟨(mem_of_lineReflect_symm hUsym).mpr hwU, ?_⟩
    rw [lineReflect_re]; linarith

/-- The Schwarz mirror gluing of a function analytic on the right part of a symmetric
off-line region is analytic on the whole region: right-part points read the function
itself, left-part points its Schwarz reflection through the line. -/
theorem mirrorGlue_analyticOnNhd_offline {g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (hg : AnalyticOnNhd ℂ g (U ∩ rightHalf)) :
    AnalyticOnNhd ℂ (mirrorGlue g) U := by
  intro s hs
  rcases lt_or_gt_of_ne (Ne.symm (hUoff s hs)) with hgt | hlt
  · refine (hg s ⟨hs, hgt⟩).congr ?_
    refine Filter.eventually_of_mem (isOpen_rightHalf.mem_nhds hgt) fun z hz => ?_
    simp only [mirrorGlue, if_pos (mem_rightHalf.mp hz)]
  · have hmem : s ∈ lineReflect ⁻¹' (U ∩ rightHalf) := by
      refine ⟨(mem_of_lineReflect_symm hUsym).mpr hs, ?_⟩
      show 1 / 2 < (lineReflect s).re
      rw [lineReflect_re]; linarith
    refine (mirrorRoot_analyticOnNhd (hU.inter isOpen_rightHalf) hg s hmem).congr ?_
    have hopen : IsOpen (lineReflect ⁻¹' rightHalf) :=
      isOpen_rightHalf.preimage continuous_lineReflect
    have hmem' : s ∈ lineReflect ⁻¹' rightHalf := hmem.2
    refine Filter.eventually_of_mem (hopen.mem_nhds hmem') fun z hz => ?_
    have hzlt : ¬(1 / 2 < z.re) := by
      have h1 : 1 / 2 < (lineReflect z).re := hz
      rw [lineReflect_re] at h1; linarith
    simp only [mirrorGlue, if_neg hzlt]

/-- The mirror gluing of a right-part `n`-th root is an `n`-th root on the whole
symmetric off-line region, for carriers with the real functional equation. -/
theorem mirrorGlue_pow_offline {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hpow : ∀ s ∈ U ∩ rightHalf, g s ^ n = f s) :
    ∀ s ∈ U, mirrorGlue g s ^ n = f s := by
  intro s hs
  show (if 1 / 2 < s.re then g s else mirrorRoot g s) ^ n = f s
  rcases lt_or_gt_of_ne (Ne.symm (hUoff s hs)) with hgt | hlt
  · rw [if_pos hgt]
    exact hpow s ⟨hs, hgt⟩
  · rw [if_neg (by linarith : ¬(1 / 2 < s.re))]
    refine mirrorRoot_pow hsym hpow s ?_
    refine ⟨(mem_of_lineReflect_symm hUsym).mpr hs, ?_⟩
    show 1 / 2 < (lineReflect s).re
    rw [lineReflect_re]; linarith

/-- The mirror gluing of a function agreeing with a symmetric carrier on the right part
agrees with the carrier on the whole symmetric off-line region: the real functional
equation supplies the left part. -/
theorem mirrorGlue_eq_offline {f g : ℂ → ℂ} {U : Set ℂ}
    (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (h : ∀ s ∈ U ∩ rightHalf, g s = f s) :
    ∀ s ∈ U, mirrorGlue g s = f s := by
  intro s hs
  show (if 1 / 2 < s.re then g s else mirrorRoot g s) = f s
  rcases lt_or_gt_of_ne (Ne.symm (hUoff s hs)) with hgt | hlt
  · rw [if_pos hgt]
    exact h s ⟨hs, hgt⟩
  · rw [if_neg (by linarith : ¬(1 / 2 < s.re))]
    have hmem : lineReflect s ∈ U ∩ rightHalf := by
      refine ⟨(mem_of_lineReflect_symm hUsym).mpr hs, ?_⟩
      rw [mem_rightHalf, lineReflect_re]; linarith
    show (starRingEnd ℂ) (g (lineReflect s)) = f s
    rw [h _ hmem, hsym s, Complex.conj_conj]

/-- The mirror gluing intertwines squaring on a symmetric off-line region. -/
theorem mirrorGlue_sq_offline {g₁ g₂ : ℂ → ℂ} {U : Set ℂ}
    (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (h : ∀ s ∈ U ∩ rightHalf, g₂ s ^ (2 : ℕ) = g₁ s) :
    ∀ s ∈ U, mirrorGlue g₂ s ^ (2 : ℕ) = mirrorGlue g₁ s := by
  intro s hs
  show (if 1 / 2 < s.re then g₂ s else mirrorRoot g₂ s) ^ (2 : ℕ) =
    (if 1 / 2 < s.re then g₁ s else mirrorRoot g₁ s)
  rcases lt_or_gt_of_ne (Ne.symm (hUoff s hs)) with hgt | hlt
  · rw [if_pos hgt, if_pos hgt]
    exact h s ⟨hs, hgt⟩
  · rw [if_neg (by linarith : ¬(1 / 2 < s.re)), if_neg (by linarith : ¬(1 / 2 < s.re))]
    show ((starRingEnd ℂ) (g₂ (lineReflect s))) ^ (2 : ℕ) = (starRingEnd ℂ) (g₁ (lineReflect s))
    rw [← map_pow]
    congr 1
    refine h _ ⟨(mem_of_lineReflect_symm hUsym).mpr hs, ?_⟩
    show 1 / 2 < (lineReflect s).re
    rw [lineReflect_re]; linarith

/-- **Equivariant roots are free off the seam.**  On a `lineReflect`-invariant open set
disjoint from the critical line, a carrier with the real functional equation admits a
Schwarz-equivariant analytic `n`-th root exactly when it admits a plain analytic
`n`-th root on the right part: the plain root extends by its own Schwarz mirror, and
conversely restriction forgets equivariance.  No sign clause and no parity clause
appear — the seam-sign bit is an invariant of the seam, invisible to regions that
avoid it. -/
theorem exists_equivariant_root_iff_offline {f : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hU : IsOpen U) (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s)) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = f s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s) ↔
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (U ∩ rightHalf) ∧
        ∀ s ∈ U ∩ rightHalf, g s ^ n = f s := by
  constructor
  · rintro ⟨h, hha, hhp, -⟩
    exact ⟨h, hha.mono Set.inter_subset_left, fun s hs => hhp s hs.1⟩
  · rintro ⟨g, hga, hgp⟩
    exact ⟨mirrorGlue g, mirrorGlue_analyticOnNhd_offline hU hUsym hUoff hga,
      mirrorGlue_pow_offline hUsym hUoff hsym hgp,
      fun s hs => mirrorGlue_equivariant g s (hUoff s hs)⟩

/-- **Equivariant coherent towers are free off the seam.**  On a `lineReflect`-invariant
open set disjoint from the critical line, a carrier with the real functional equation
carries a Schwarz-equivariant coherent ℤ₂-tower exactly when its right part carries a
plain one: level-wise mirror gluing is coherent because the gluing intertwines
squaring.  The pro-level seam-sign obstruction is likewise an invariant of the seam
alone. -/
theorem equivariant_coherentTower_offline_iff {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2)
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s)) :
    (∃ S : CoherentTower f U, ∀ k, ∀ s ∈ U, mirrorRoot (S.level k) s = S.level k s) ↔
      Nonempty (CoherentTower f (U ∩ rightHalf)) := by
  constructor
  · rintro ⟨S, -⟩
    exact ⟨⟨S.level, fun s hs => S.level_zero s hs.1,
      fun k => (S.analytic k).mono Set.inter_subset_left,
      fun k s hs => S.sq k s hs.1⟩⟩
  · rintro ⟨T⟩
    refine ⟨⟨fun k => mirrorGlue (T.level k),
      mirrorGlue_eq_offline hUsym hUoff hsym T.level_zero,
      fun k => mirrorGlue_analyticOnNhd_offline hU hUsym hUoff (T.analytic k),
      fun k => mirrorGlue_sq_offline hUsym hUoff (T.sq k)⟩,
      fun k s hs => mirrorGlue_equivariant (T.level k) s (hUoff s hs)⟩

/-- The off-line freeness for ξ: on any `lineReflect`-invariant open set avoiding the
critical line, the Schwarz-equivariant `n`-th root theory of ξ is the plain root
theory of its right part. -/
theorem xi_equivariant_root_iff_offline {U : Set ℂ} {n : ℕ}
    (hU : IsOpen U) (hUsym : lineReflect ⁻¹' U = U) (hUoff : ∀ s ∈ U, s.re ≠ 1 / 2) :
    (∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ s ∈ U, h s ^ n = xi s) ∧
      ∀ s ∈ U, mirrorRoot h s = h s) ↔
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (U ∩ rightHalf) ∧
        ∀ s ∈ U ∩ rightHalf, g s ^ n = xi s :=
  exists_equivariant_root_iff_offline hU hUsym hUoff xi_lineReflect

end RHTower
