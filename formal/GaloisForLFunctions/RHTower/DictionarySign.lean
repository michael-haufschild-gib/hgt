/-
Doc 33 §1 (task #131, item 2 — the (K1) capstone): deck class = sign product of Ξ.

The seam-continuation step of doc 33's outline dissolves: choose the second chart root
to be the LINE MIRROR of the first, `mirrorRoot g = conj ∘ g ∘ lineReflect`. It is
analytic on the mirrored chart (`mirrorRoot_analyticOnNhd`, Schwarz reflection through
`DifferentiableAt.conj_conj`), it is again a root of any carrier satisfying the real
functional equation `f ∘ lineReflect = conj ∘ f` (`mirrorRoot_pow` — ξ satisfies it by
`xi_one_sub` + `xi_conj`), and at on-line basepoints the chart ratio is
`g(p)/conj(g(p)) = sign Ξ(p)` pointwise (`sq_conj_ratio_of_pos/neg`). Since the deck
class is independent of the chart-root choice (`deckClass_root_indep`), the class of ANY
root pair on a mirror-symmetric cover equals the sign product:

* `deckClass_mirror_eq_sign_product` — pointwise, generic carrier;
* `xi_deckClass_eq_sign_product` — **(K1)**: for arbitrary analytic square roots of ξ on
  a chart and its mirror, `deckClass = sign Ξ(p₊) · sign Ξ(p₋)` — the k = 1 rung datum
  IS the classical sign-change reading of Ξ.
-/
import GaloisForLFunctions.RHTower.DictionaryBase
import GaloisForLFunctions.RHTower.WindowRelation
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.RHTower.DeckMultiZero

namespace RHTower

open Set Complex Metric

theorem continuous_lineReflect : Continuous lineReflect := by
  unfold lineReflect
  exact continuous_const.sub Complex.continuous_conj

theorem lineReflect_im (z : ℂ) : (lineReflect z).im = z.im := by
  simp [lineReflect]

theorem lineReflect_eq_self_iff {z : ℂ} : lineReflect z = z ↔ z.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    rw [lineReflect_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · rw [lineReflect_re, h]
      norm_num
    · exact lineReflect_im z

/-- The line-mirror of a local root: the Schwarz reflection through the critical line. -/
noncomputable def mirrorRoot (g : ℂ → ℂ) : ℂ → ℂ :=
  fun s => (starRingEnd ℂ) (g (lineReflect s))

theorem mirrorRoot_apply_line {g : ℂ → ℂ} {p : ℂ} (hp : p.re = 1 / 2) :
    mirrorRoot g p = (starRingEnd ℂ) (g p) := by
  simp only [mirrorRoot, lineReflect_eq_self_iff.mpr hp]

/-- The mirror of an analytic function on `U` is analytic on the mirrored chart. -/
theorem mirrorRoot_analyticOnNhd {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) :
    AnalyticOnNhd ℂ (mirrorRoot g) (lineReflect ⁻¹' U) := by
  have hV : IsOpen (lineReflect ⁻¹' U) := hU.preimage continuous_lineReflect
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hV
  have hd : DifferentiableAt ℂ g (lineReflect z) := (hg _ hz).differentiableAt
  have hF := hd.conj_conj
  have hpt : (starRingEnd ℂ) (lineReflect z) = 1 - z := by
    simp [lineReflect, map_sub, map_one]
  rw [hpt] at hF
  have haff : DifferentiableAt ℂ (fun s : ℂ => 1 - s) z :=
    (differentiableAt_const 1).sub differentiableAt_id
  have hcomp := hF.comp z haff
  have hfun : (⇑(starRingEnd ℂ) ∘ g ∘ ⇑(starRingEnd ℂ)) ∘ (fun s : ℂ => 1 - s)
      = mirrorRoot g := by
    funext s
    simp [mirrorRoot, lineReflect, Function.comp, map_sub, map_one]
  rw [hfun] at hcomp
  exact hcomp.differentiableWithinAt

/-- The mirror of a root is a root, for carriers with the real functional equation. -/
theorem mirrorRoot_pow {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hsym : ∀ s, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hroot : ∀ s ∈ U, g s ^ n = f s) :
    ∀ s ∈ lineReflect ⁻¹' U, mirrorRoot g s ^ n = f s := by
  intro s hs
  calc mirrorRoot g s ^ n = (starRingEnd ℂ) (g (lineReflect s) ^ n) := by
        simp only [mirrorRoot, map_pow]
    _ = (starRingEnd ℂ) (f (lineReflect s)) := by rw [hroot _ hs]
    _ = f s := by rw [hsym s, Complex.conj_conj]

/-- ξ satisfies the real functional equation across the critical line. -/
theorem xi_lineReflect (s : ℂ) : xi (lineReflect s) = (starRingEnd ℂ) (xi s) := by
  simp only [lineReflect]
  rw [xi_one_sub ((starRingEnd ℂ) s), xi_conj]

/-- **Reality of Ξ**: ξ is real on the critical line. -/
theorem xi_im_eq_zero_on_line {p : ℂ} (hp : p.re = 1 / 2) : (xi p).im = 0 := by
  have hfix : lineReflect p = p := lineReflect_eq_self_iff.mpr hp
  have h : (starRingEnd ℂ) (xi p) = xi p := by
    rw [← xi_lineReflect, hfix]
  exact Complex.conj_eq_iff_im.mp h

/-- **Pointwise sign reading** (generic carrier): the deck class of a root against its
own mirror equals the product of the carrier's signs at the on-line basepoints. -/
theorem deckClass_mirror_eq_sign_product {f g : ℂ → ℂ} {pP pM : ℂ}
    (hP2 : g pP ^ (2 : ℕ) = f pP) (hM2 : g pM ^ (2 : ℕ) = f pM)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hPim : (f pP).im = 0) (hMim : (f pM).im = 0)
    (hPre : (f pP).re ≠ 0) (hMre : (f pM).re ≠ 0) :
    deckClass g (mirrorRoot g) pP pM
      = (if 0 < (f pP).re then 1 else -1) * (if 0 < (f pM).re then 1 else -1) := by
  rw [deckClass, mirrorRoot_apply_line hPline, mirrorRoot_apply_line hMline]
  rcases lt_or_gt_of_ne hPre with hP | hP
  · rw [sq_conj_ratio_of_neg hP2 hPim hP, if_neg (not_lt.mpr hP.le)]
    rcases lt_or_gt_of_ne hMre with hM | hM
    · rw [sq_conj_ratio_of_neg hM2 hMim hM, if_neg (not_lt.mpr hM.le)]
      norm_num
    · rw [sq_conj_ratio_of_pos hM2 hMim hM, if_pos hM]
      norm_num
  · rw [sq_conj_ratio_of_pos hP2 hPim hP, if_pos hP]
    rcases lt_or_gt_of_ne hMre with hM | hM
    · rw [sq_conj_ratio_of_neg hM2 hMim hM, if_neg (not_lt.mpr hM.le)]
      norm_num
    · rw [sq_conj_ratio_of_pos hM2 hMim hM, if_pos hM]
      norm_num

/-- **(K1), the dictionary base case**: for ANY analytic square roots `g₁` of ξ on an
open preconnected chart `U` and `g₂` on its mirror, with basepoints on the critical
line where ξ does not vanish, the deck class is the sign product of Ξ — the k = 1 rung
datum is the classical sign-change reading. -/
theorem xi_deckClass_eq_sign_product {g₁ g₂ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ (2 : ℕ) = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ (2 : ℕ) = xi s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hxP : xi pP ≠ 0) (hxM : xi pM ≠ 0) :
    deckClass g₁ g₂ pP pM
      = (if 0 < (xi pP).re then 1 else -1) * (if 0 < (xi pM).re then 1 else -1) := by
  have hVopen : IsOpen (lineReflect ⁻¹' U) := hU.preimage continuous_lineReflect
  have hVeq : lineReflect ⁻¹' U = lineReflect '' U := by
    ext z
    constructor
    · intro h
      exact ⟨lineReflect z, h, lineReflect_involutive z⟩
    · rintro ⟨w, hw, rfl⟩
      simpa [Set.mem_preimage, lineReflect_involutive] using hw
  have hVc : IsPreconnected (lineReflect ⁻¹' U) := by
    rw [hVeq]
    exact hUc.image _ continuous_lineReflect.continuousOn
  have hfixP : lineReflect pP = pP := lineReflect_eq_self_iff.mpr hPline
  have hfixM : lineReflect pM = pM := lineReflect_eq_self_iff.mpr hMline
  have hpPV : pP ∈ lineReflect ⁻¹' U := by
    rw [Set.mem_preimage, hfixP]; exact hpP
  have hpMV : pM ∈ lineReflect ⁻¹' U := by
    rw [Set.mem_preimage, hfixM]; exact hpM
  have hmg : AnalyticOnNhd ℂ (mirrorRoot g₁) (lineReflect ⁻¹' U) :=
    mirrorRoot_analyticOnNhd hU hg₁
  have hmp : ∀ s ∈ lineReflect ⁻¹' U, mirrorRoot g₁ s ^ (2 : ℕ) = xi s :=
    mirrorRoot_pow xi_lineReflect hp₁
  have htrans := deckClass_root_indep (f := xi) (by norm_num : (0 : ℕ) < 2)
    hU hUc hVopen hVc hg₁ hg₁ hmg hg₂ hp₁ hp₁ hmp hp₂
    hpP hpPV hpM hpMV hxP hxM
  rw [htrans]
  have hPre : (xi pP).re ≠ 0 := by
    intro h0
    exact hxP (Complex.ext (by simpa using h0)
      (by simpa using xi_im_eq_zero_on_line hPline))
  have hMre : (xi pM).re ≠ 0 := by
    intro h0
    exact hxM (Complex.ext (by simpa using h0)
      (by simpa using xi_im_eq_zero_on_line hMline))
  exact deckClass_mirror_eq_sign_product (hp₁ pP hpP) (hp₁ pM hpM) hPline hMline
    (xi_im_eq_zero_on_line hPline) (xi_im_eq_zero_on_line hMline) hPre hMre

/-! ### The odd-enclosed-count clause: sign product = parity of the enclosed order -/

theorem conj_mem_slitPlane_iff {w : ℂ} :
    (starRingEnd ℂ) w ∈ Complex.slitPlane ↔ w ∈ Complex.slitPlane := by
  simp [Complex.mem_slitPlane_iff]

/-- For a center on the critical line, the line mirror acts on the recentered variable
as `w ↦ −conj w`. -/
theorem lineReflect_sub_center {a : ℂ} (ha : a.re = 1 / 2) (z : ℂ) :
    lineReflect z - a = -(starRingEnd ℂ) (z - a) := by
  have hca : (starRingEnd ℂ) a = 1 - a := by
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, Complex.one_re, ha]
      norm_num
    · rw [Complex.conj_im, Complex.sub_im, Complex.one_im]
      ring
  simp only [lineReflect]
  rw [map_sub, hca]
  ring

theorem dist_lineReflect_center {a : ℂ} (ha : a.re = 1 / 2) (z : ℂ) :
    dist (lineReflect z) a = dist z a := by
  rw [Complex.dist_eq, Complex.dist_eq, lineReflect_sub_center ha, norm_neg,
    Complex.norm_conj]

/-- For a center on the critical line, the mirror of the right slit-annulus chart is
the left slit-annulus chart. -/
theorem lineReflect_preimage_chartRA {a : ℂ} (ha : a.re = 1 / 2) (r₀ R : ℝ) :
    lineReflect ⁻¹' chartRA a r₀ R = chartLA a r₀ R := by
  ext z
  simp only [Set.mem_preimage, chartRA, chartLA, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_sdiff, mem_ball, mem_closedBall]
  rw [dist_lineReflect_center ha]
  have hslit : lineReflect z - a ∈ Complex.slitPlane ↔ a - z ∈ Complex.slitPlane := by
    rw [lineReflect_sub_center ha]
    have hneg : -(starRingEnd ℂ) (z - a) = (starRingEnd ℂ) (a - z) := by
      rw [map_sub, map_sub]
      ring
    rw [hneg, conj_mem_slitPlane_iff]
  rw [hslit]

/-- **(K1), the count clause**: on a critical-line-centered window enclosing zeros of ξ
of total multiplicity `Σ mᵢ` (peeled factorization on the ball), the sign product of Ξ
at the two seam basepoints equals `(−1)^{Σ mᵢ}` — the classical statement "Ξ changes
sign across the window iff the enclosed zero count is odd", machine-checked with no
argument principle: the sign product IS the deck class (`xi_deckClass_eq_sign_product`)
and the deck class counts the enclosed order (`deckClass_multi_zero`). -/
theorem xi_sign_product_eq_parity {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (ha : a.re = 1 / 2)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, xi z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = xi z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = xi z) :
    (if 0 < (xi (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re then (1 : ℂ) else -1)
      * (if 0 < (xi (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re then (1 : ℂ) else -1)
      = (-1) ^ (∑ i ∈ s, m i) := by
  classical
  set ε : ℝ := (r₀ + R) / 2 with hε_def
  have hεr : r₀ < ε := by rw [hε_def]; linarith
  have hεR : ε < R := by rw [hε_def]; linarith
  have hεpos : 0 < ε := lt_of_le_of_lt h0 hεr
  set pP : ℂ := a + ((ε : ℝ) : ℂ) * I with hpP_def
  set pM : ℂ := a - ((ε : ℝ) : ℂ) * I with hpM_def
  have hPsub : pP - a = ((ε : ℝ) : ℂ) * I := by rw [hpP_def]; ring
  have hMsub : pM - a = -(((ε : ℝ) : ℂ) * I) := by rw [hpM_def]; ring
  have hnorm : ‖((ε : ℝ) : ℂ) * I‖ = ε := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hεpos]
  have hPmem : pP ∈ chartRA a r₀ R := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, hPsub]
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      simpa using hεpos.ne'
    · rw [mem_ball, Complex.dist_eq, hPsub, hnorm]
      exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hPsub, hnorm, not_le]
      exact hεr
  have hMmem : pM ∈ chartRA a r₀ R := by
    refine ⟨?_, ?_, ?_⟩
    · rw [Set.mem_setOf_eq, hMsub]
      refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      simpa using hεpos.ne'
    · rw [mem_ball, Complex.dist_eq, hMsub, norm_neg, hnorm]
      exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hMsub, norm_neg, hnorm, not_le]
      exact hεr
  have hPline : pP.re = 1 / 2 := by rw [hpP_def]; simp [ha]
  have hMline : pM.re = 1 / 2 := by rw [hpM_def]; simp [ha]
  have hxiNe : ∀ z, z ∈ ball a R → r₀ < ‖z - a‖ → xi z ≠ 0 := by
    intro z hzball hzfar
    rw [hfact z hzball]
    refine mul_ne_zero ?_ (hh0 z hzball)
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    refine pow_ne_zero _ ?_
    intro hzi
    rw [sub_eq_zero] at hzi
    rw [hzi] at hzfar
    exact absurd (hρ i hi) (not_le.mpr hzfar)
  have hxP : xi pP ≠ 0 := hxiNe pP hPmem.2.1 (by rw [hPsub, hnorm]; exact hεr)
  have hxM : xi pM ≠ 0 := hxiNe pM hMmem.2.1 (by rw [hMsub, norm_neg, hnorm]; exact hεr)
  have hmirror : lineReflect ⁻¹' chartRA a r₀ R = chartLA a r₀ R :=
    lineReflect_preimage_chartRA ha r₀ R
  have hG₂' : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' chartRA a r₀ R) := by
    rw [hmirror]; exact hG₂
  have hpG₂' : ∀ z ∈ lineReflect ⁻¹' chartRA a r₀ R, G₂ z ^ (2 : ℕ) = xi z := by
    rw [hmirror]; exact hpG₂
  have hsign := xi_deckClass_eq_sign_product (isOpen_chartRA a r₀ R)
    (isPreconnected_chartRA a h0) hG₁ hG₂' hpG₁ hpG₂' hPmem hMmem hPline hMline hxP hxM
  have hcount : deckClass G₁ G₂ pP pM
      = exp (2 * (Real.pi : ℂ) * I * (∑ i ∈ s, (m i : ℂ)) / 2) :=
    deckClass_multi_zero s ρ m h0 hrR (by norm_num) hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂
  rw [← hsign, hcount]
  have hcast : (∑ i ∈ s, (m i : ℂ)) = ((∑ i ∈ s, m i : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hexp : (2 : ℂ) * Real.pi * I * ((∑ i ∈ s, m i : ℕ) : ℂ) / 2
      = ((∑ i ∈ s, m i : ℕ) : ℂ) * (Real.pi * I) := by ring
  rw [hexp, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **(K2) at the base level: the sign product reads L(W), the ON-LINE count.** For a
reflection-closed enclosed configuration with reflection-invariant multiplicities, the
off-line zeros pair up and cancel mod 2, so the sign product — the k = 1 deck class —
equals `(−1)^{L(W)}`: the rung datum counts only the on-line zeros. This is the window
identity D = L + 2N (`window_identity`) realized as cocycle arithmetic. -/
theorem xi_sign_product_eq_onLine_parity {t : Finset ℂ} {m : ℂ → ℕ}
    {h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (ha : a.re = 1 / 2)
    (hclosed : ∀ z ∈ t, lineReflect z ∈ t)
    (hminv : ∀ z ∈ t, m (lineReflect z) = m z)
    (hρ : ∀ z ∈ t, ‖z - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, xi z = (∏ ρ ∈ t, (z - ρ) ^ m ρ) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ (2 : ℕ) = xi z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ (2 : ℕ) = xi z) :
    (if 0 < (xi (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re then (1 : ℂ) else -1)
      * (if 0 < (xi (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re then (1 : ℂ) else -1)
      = (-1) ^ (∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z) := by
  have h1 := xi_sign_product_eq_parity t (fun z => z) m h0 hrR ha hρ hh hh0 hfact
    hG₁ hG₂ hpG₁ hpG₂
  rw [h1, window_identity hclosed hminv, pow_add, pow_mul]
  norm_num

/-- **The deck class is blind to the on/off-line split.** Two enclosed configurations
with equal TOTAL multiplicity produce equal deck classes at every level `n`: positions
never enter `deckClass_multi_zero`'s value. Hence deck data — at all levels, together
with the sign product it determines — cannot separate `L` from `D` beyond their sum:
the discriminant (DISC) bit is the minimal additional instrument that reads `N mod 2`
on dominated windows. -/
theorem deckClass_blind_to_split {ι κ : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    (s' : Finset κ) (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f f' h h' G₁ G₂ G₁' G₂' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} (hn : 0 < n)
    (htot : ∑ i ∈ s, m i = ∑ j ∈ s', m' j)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀) (hρ' : ∀ j ∈ s', ‖ρ' j - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hfact' : ∀ z ∈ ball a R, f' z = (∏ j ∈ s', (z - ρ' j) ^ m' j) * h' z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z)
    (hG₁' : AnalyticOnNhd ℂ G₁' (chartRA a r₀ R))
    (hG₂' : AnalyticOnNhd ℂ G₂' (chartLA a r₀ R))
    (hpG₁' : ∀ z ∈ chartRA a r₀ R, G₁' z ^ n = f' z)
    (hpG₂' : ∀ z ∈ chartLA a r₀ R, G₂' z ^ n = f' z) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      = deckClass G₁' G₂' (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
  rw [deckClass_multi_zero s ρ m h0 hrR hn hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂,
    deckClass_multi_zero s' ρ' m' h0 hrR hn hρ' hh' hh0' hfact' hG₁' hG₂' hpG₁' hpG₂']
  have hc : (∑ i ∈ s, (m i : ℂ)) = ∑ j ∈ s', (m' j : ℂ) := by
    exact_mod_cast htot
  rw [hc]

end RHTower
