/-
Doc 22 §2's named WIRING GAP (task #143): the seam-side L-transport, in Lean.

Doc 22 §2 needed TWO transports to move the window relation from ξ to the finite
carrier: the deck side (D-invariant) — banked as `SeamTransport.lean` via the
homotopy engine — and the seam side (L-invariant on slit-adjacent charts), "the
one unproven wiring piece, same shape as #131's dictionary". This module closes
it, in exactly #131's shape: the k = 1 seam datum IS the sign product of the real
carrier at the two on-line basepoints (`DictionarySign`'s (K1)), and domination
at those TWO POINTS alone forces the sign products of ξ and the truncation to
agree. No homotopy; the sign dictionary carries the transport.

* `pos_iff_of_abs_sub_lt`, `re_pos_iff_of_dominated` — the atomic transport:
  domination at a real value forces equal sign;
  `left/right_ne_zero_of_norm_sub_lt` — domination forces nonvanishing.
* `sign_product_eq_of_dominated` — the two-point seam transport of the (K1) datum.
* `im_eq_zero_on_line_of_realFE`, `mirrorRoot_pow_of_mem`,
  `deckClass_eq_sign_product_of_realFE` — (K1) generalized off ξ: any carrier
  with the real FE on the mirrored chart reads its k = 1 deck class as the sign
  product (localizes `xi_deckClass_eq_sign_product`; the local real FE is what
  the strip-only `completedGN` FE can supply).
* `completedGN_lineReflect`, `completedGN_im_eq_zero_on_line` — the concrete
  completed truncation has the real FE across the line and is real on it.
* `xi_completedGN_sign_product_eq` — the seam datum of ξ equals the truncation's
  under two-point domination.
* `anneal_seam_L_transport` — **the L-transport**: on a strip chart, the k = 1
  deck class of ξ's root data equals that of `completedGN`'s, given domination
  at only the two on-line basepoints. Doc 22 §2's gap, closed on the actual
  objects.

Complementarity: `seam_transport` (deck side) needs chart-wide domination and
transports every level 2^k; this module needs 2-point domination and transports
the k = 1 seam reading. Together they are the two invariants of the window
relation (ID), both now reading off the concrete finite carrier.
-/
import GaloisForLFunctions.RHTower.DictionarySign
import GaloisForLFunctions.RHTower.ZetaCarrier

namespace RHTower

open Complex

/-! ### §1 Atomic sign transport under domination -/

/-- Domination transports positivity on the reals. -/
theorem pos_iff_of_abs_sub_lt {x y : ℝ} (h : |x - y| < |y|) : 0 < x ↔ 0 < y := by
  rcases abs_lt.mp h with ⟨h1, h2⟩
  rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [abs_of_neg hy] at h1 h2
    constructor <;> intro <;> linarith
  · rw [hy, sub_zero, abs_zero] at h
    exact absurd h (not_lt.mpr (abs_nonneg x))
  · rw [abs_of_pos hy] at h1 h2
    constructor <;> intro <;> linarith

theorem left_ne_zero_of_norm_sub_lt {a b : ℂ} (h : ‖a - b‖ < ‖b‖) : a ≠ 0 := by
  rintro rfl
  simp at h

theorem right_ne_zero_of_norm_sub_lt {a b : ℂ} (h : ‖a - b‖ < ‖b‖) : b ≠ 0 := by
  rintro rfl
  simp at h
  exact absurd h (not_lt.mpr (norm_nonneg a))

/-- Domination at a pair of REAL values forces equal signs. -/
theorem re_pos_iff_of_dominated {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0)
    (h : ‖a - b‖ < ‖b‖) : (0 < a.re ↔ 0 < b.re) := by
  have ha' : a = ((a.re : ℝ) : ℂ) := Complex.ext rfl (by simp [ha])
  have hb' : b = ((b.re : ℝ) : ℂ) := Complex.ext rfl (by simp [hb])
  rw [ha', hb', ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real] at h
  exact pos_iff_of_abs_sub_lt h

/-! ### §2 Two-point seam transport of the sign product -/

/-- The (K1) sign product transports under domination at the two basepoint values. -/
theorem sign_product_eq_of_dominated {fP fM gP gM : ℂ}
    (hfP : fP.im = 0) (hfM : fM.im = 0) (hgP : gP.im = 0) (hgM : gM.im = 0)
    (hdP : ‖fP - gP‖ < ‖gP‖) (hdM : ‖fM - gM‖ < ‖gM‖) :
    ((if 0 < fP.re then (1 : ℂ) else -1) * (if 0 < fM.re then 1 else -1))
      = ((if 0 < gP.re then 1 else -1) * (if 0 < gM.re then 1 else -1)) := by
  rw [if_congr (re_pos_iff_of_dominated hfP hgP hdP) rfl rfl,
    if_congr (re_pos_iff_of_dominated hfM hgM hdM) rfl rfl]

/-! ### §3 Generic reality-on-line and the localized mirror root -/

/-- A carrier with the real FE at an on-line point is real there. -/
theorem im_eq_zero_on_line_of_realFE {f : ℂ → ℂ} {p : ℂ} (hp : p.re = 1 / 2)
    (hFE : f (lineReflect p) = (starRingEnd ℂ) (f p)) : (f p).im = 0 := by
  have hfix : lineReflect p = p := lineReflect_eq_self_iff.mpr hp
  rw [hfix] at hFE
  exact Complex.conj_eq_iff_im.mp hFE.symm

/-- Localized `mirrorRoot_pow`: the real FE is needed only on the mirrored chart. -/
theorem mirrorRoot_pow_of_mem {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (hsym : ∀ s ∈ lineReflect ⁻¹' U, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hroot : ∀ s ∈ U, g s ^ n = f s) :
    ∀ s ∈ lineReflect ⁻¹' U, mirrorRoot g s ^ n = f s := by
  intro s hs
  calc mirrorRoot g s ^ n = (starRingEnd ℂ) (g (lineReflect s) ^ n) := by
        simp only [mirrorRoot, map_pow]
    _ = (starRingEnd ℂ) (f (lineReflect s)) := by rw [hroot _ hs]
    _ = f s := by rw [hsym s hs, Complex.conj_conj]

/-! ### §4 Generic (K1) for carriers with a chart-local real FE -/

/-- **(K1), generic carrier**: for any carrier satisfying the real FE on the mirrored
chart, the k = 1 deck class of any root pair is the sign product at the on-line
basepoints (localizes `xi_deckClass_eq_sign_product` off ξ). -/
theorem deckClass_eq_sign_product_of_realFE {f g₁ g₂ : ℂ → ℂ} {U : Set ℂ}
    (hsym : ∀ s ∈ lineReflect ⁻¹' U, f (lineReflect s) = (starRingEnd ℂ) (f s))
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = f s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = f s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hxP : f pP ≠ 0) (hxM : f pM ≠ 0) :
    deckClass g₁ g₂ pP pM
      = (if 0 < (f pP).re then 1 else -1) * (if 0 < (f pM).re then 1 else -1) := by
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
  have hmp : ∀ s ∈ lineReflect ⁻¹' U, mirrorRoot g₁ s ^ 2 = f s :=
    mirrorRoot_pow_of_mem hsym hp₁
  have htrans := deckClass_root_indep (f := f) (by norm_num : (0 : ℕ) < 2)
    hU hUc hVopen hVc hg₁ hg₁ hmg hg₂ hp₁ hp₁ hmp hp₂
    hpP hpPV hpM hpMV hxP hxM
  rw [htrans]
  have hPim : (f pP).im = 0 := im_eq_zero_on_line_of_realFE hPline (hsym pP hpPV)
  have hMim : (f pM).im = 0 := im_eq_zero_on_line_of_realFE hMline (hsym pM hpMV)
  have hPre : (f pP).re ≠ 0 := by
    intro h0
    exact hxP (Complex.ext (by simpa using h0) (by simpa using hPim))
  have hMre : (f pM).re ≠ 0 := by
    intro h0
    exact hxM (Complex.ext (by simpa using h0) (by simpa using hMim))
  exact deckClass_mirror_eq_sign_product (hp₁ pP hpP) (hp₁ pM hpM) hPline hMline
    hPim hMim hPre hMre

/-! ### §5 The concrete completed carrier has the real FE on the strip -/

/-- The completed truncation satisfies the real FE across the critical line, on the
strip. -/
theorem completedGN_lineReflect {N : ℕ} {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    completedGN N (lineReflect s) = (starRingEnd ℂ) (completedGN N s) := by
  have hc0 : 0 < ((starRingEnd ℂ) s).re := by rwa [Complex.conj_re]
  have hc1 : ((starRingEnd ℂ) s).re < 1 := by rwa [Complex.conj_re]
  rw [show lineReflect s = 1 - (starRingEnd ℂ) s from rfl,
    completedGN_one_sub hc0 hc1, completedGN_conj]

/-- Reality of the completed truncation on the critical line. -/
theorem completedGN_im_eq_zero_on_line {N : ℕ} {p : ℂ} (hp : p.re = 1 / 2) :
    (completedGN N p).im = 0 :=
  im_eq_zero_on_line_of_realFE hp
    (completedGN_lineReflect (by rw [hp]; norm_num) (by rw [hp]; norm_num))

/-! ### §6 The L-transport capstones -/

/-- The (K1) seam datum of ξ equals that of the completed truncation under
domination at the two on-line basepoints alone. -/
theorem xi_completedGN_sign_product_eq {N : ℕ} {pP pM : ℂ}
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hdomP : ‖xi pP - completedGN N pP‖ < ‖completedGN N pP‖)
    (hdomM : ‖xi pM - completedGN N pM‖ < ‖completedGN N pM‖) :
    ((if 0 < (xi pP).re then (1 : ℂ) else -1) * (if 0 < (xi pM).re then 1 else -1))
      = ((if 0 < (completedGN N pP).re then 1 else -1)
          * (if 0 < (completedGN N pM).re then 1 else -1)) :=
  sign_product_eq_of_dominated (xi_im_eq_zero_on_line hPline)
    (xi_im_eq_zero_on_line hMline) (completedGN_im_eq_zero_on_line hPline)
    (completedGN_im_eq_zero_on_line hMline) hdomP hdomM

/-- **Seam L-transport** (doc 22 §2's named wiring gap): on a strip chart, the k = 1
deck class of ξ's root data equals that of the concrete completed truncation's,
given domination at ONLY the two on-line basepoints. The seam side of the ANNEAL
reduction — no homotopy, the sign dictionary carries it. -/
theorem anneal_seam_L_transport {N : ℕ} {g₁ g₂ G₁ G₂ : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUstrip : ∀ z ∈ U, 0 < z.re ∧ z.re < 1)
    (hg₁ : AnalyticOnNhd ℂ g₁ U) (hg₂ : AnalyticOnNhd ℂ g₂ (lineReflect ⁻¹' U))
    (hG₁ : AnalyticOnNhd ℂ G₁ U) (hG₂ : AnalyticOnNhd ℂ G₂ (lineReflect ⁻¹' U))
    (hp₁ : ∀ s ∈ U, g₁ s ^ 2 = xi s) (hp₂ : ∀ s ∈ lineReflect ⁻¹' U, g₂ s ^ 2 = xi s)
    (hP₁ : ∀ s ∈ U, G₁ s ^ 2 = completedGN N s)
    (hP₂ : ∀ s ∈ lineReflect ⁻¹' U, G₂ s ^ 2 = completedGN N s)
    {pP pM : ℂ} (hpP : pP ∈ U) (hpM : pM ∈ U)
    (hPline : pP.re = 1 / 2) (hMline : pM.re = 1 / 2)
    (hdomP : ‖xi pP - completedGN N pP‖ < ‖completedGN N pP‖)
    (hdomM : ‖xi pM - completedGN N pM‖ < ‖completedGN N pM‖) :
    deckClass g₁ g₂ pP pM = deckClass G₁ G₂ pP pM := by
  have hxP : xi pP ≠ 0 := left_ne_zero_of_norm_sub_lt hdomP
  have hxM : xi pM ≠ 0 := left_ne_zero_of_norm_sub_lt hdomM
  have hcP : completedGN N pP ≠ 0 := right_ne_zero_of_norm_sub_lt hdomP
  have hcM : completedGN N pM ≠ 0 := right_ne_zero_of_norm_sub_lt hdomM
  have hsym : ∀ s ∈ lineReflect ⁻¹' U,
      completedGN N (lineReflect s) = (starRingEnd ℂ) (completedGN N s) := by
    intro s hs
    have hmem := hUstrip _ hs
    rw [lineReflect_re] at hmem
    exact completedGN_lineReflect (by linarith [hmem.2]) (by linarith [hmem.1])
  rw [xi_deckClass_eq_sign_product hU hUc hg₁ hg₂ hp₁ hp₂ hpP hpM hPline hMline hxP hxM,
    deckClass_eq_sign_product_of_realFE hsym hU hUc hG₁ hG₂ hP₁ hP₂ hpP hpM
      hPline hMline hcP hcM]
  exact xi_completedGN_sign_product_eq hPline hMline hdomP hdomM

end RHTower
