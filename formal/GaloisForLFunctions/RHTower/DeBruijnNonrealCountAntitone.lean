import GaloisForLFunctions.RHTower.DeBruijnNonrealCountLocal
import GaloisForLFunctions.RHTower.KiKimLeeUniformReality
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor

/-!
# The nonreal zero count of the de Bruijn–Newman flow is nonincreasing

For `t > 0` let `N(t)` be the number of nonreal zeros of `H_t`, counted with multiplicity; it is
finite by Ki–Kim–Lee.  The function `N` is nonincreasing on `(0, ∞)`
(`nonrealZeroCount_antitoneOn`).

Fix `0 < t₁ < 1/8`.  By the uniform Ki–Kim–Lee reality and de Bruijn's strip bound, for `t` near
`t₁` every nonreal zero of `H_t` lies in a fixed disc `|z| < R` whose circle is zero-free for `H_{t₁}`.
Small discs around the finitely many zeros of `H_{t₁}` in it carry, for `t` near `t₁`, the same
counts as for `H_{t₁}`; their counts add up to the count of the large disc, so no zero of `H_t` in
`|z| < R` lies outside them.  Discs around nonreal zeros avoid the real axis, and by the forward
local model the discs around real zeros contain only real zeros of `H_t` for `t` slightly larger
than `t₁` (`exists_ball_real_zeros_forward`).  Hence `N(t₁) ≤ N(t)` for `t` near `t₁`, and
`N(t) = N(t₁)` for `t` slightly larger than `t₁` (`exists_local_nonrealZeroCount`).  A lower
semicontinuous integer function that is right-locally nonincreasing is nonincreasing
(`le_of_local_right_and_lsc`).  For `t ≥ 1/8` all zeros are real.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-- The number of nonreal zeros of `H_t`, with multiplicity (`0` for `t ≤ 0`). -/
def nonrealZeroCount (t : ℝ) : ℕ :=
  if ht : 0 < t then
    ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset, zeroMult (riemannHeat t) z
  else 0

theorem nonrealZeroCount_eq {t : ℝ} (ht : 0 < t) :
    nonrealZeroCount t =
      ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset, zeroMult (riemannHeat t) z :=
  dif_pos ht

/-! ## Counting with discs -/

/-- A finite sum of positive integers over a finite set equals the sum over a disjoint family of
subsets only if the family covers the set. -/
theorem subset_biUnion_of_sum_eq {E : Finset ℂ} {Z : Finset ℂ} {W : ℂ → Finset ℂ} {m : ℂ → ℕ}
    (hm : ∀ z ∈ Z, 1 ≤ m z) (hsub : ∀ e ∈ E, W e ⊆ Z)
    (hdisj : (E : Set ℂ).PairwiseDisjoint W)
    (hsum : ∑ z ∈ Z, m z = ∑ e ∈ E, ∑ z ∈ W e, m z) : Z ⊆ E.biUnion W := by
  classical
  have hbsub : E.biUnion W ⊆ Z := Finset.biUnion_subset.mpr hsub
  have hb := Finset.sum_biUnion hdisj (f := m)
  have hsd := Finset.sum_sdiff hbsub (f := m)
  rw [hb] at hsd
  have hzero : ∑ z ∈ Z \ E.biUnion W, m z = 0 := by omega
  intro z hz
  by_contra hn
  have hmem : z ∈ Z \ E.biUnion W := Finset.mem_sdiff.mpr ⟨hz, hn⟩
  have h1 := Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) hmem
  have := hm z hz
  omega

/-- **Disc counts bound the nonreal count.** Let disjoint discs `B(e, r_e)`, `e ∈ E`, avoid the
real axis and have zero-free circles for `H_t` (`t > 0`), with disc counts `n_e`.  Then
`Σ n_e ≤ N(t)`, with equality if every nonreal zero of `H_t` lies in one of the discs. -/
theorem sum_le_nonrealZeroCount {t : ℝ} (ht : 0 < t) {E : Finset ℂ} {r : ℂ → ℝ} {n : ℂ → ℕ}
    (hr : ∀ e ∈ E, 0 < r e) (havoid : ∀ e ∈ E, ∀ w ∈ ball e (r e), w.im ≠ 0)
    (hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')))
    (hsph : ∀ e ∈ E, ∀ w ∈ sphere e (r e), riemannHeat t w ≠ 0)
    (hn : ∀ e ∈ E, zeroSumBall (riemannHeat t) e (r e) = (n e : ℂ)) :
    ∑ e ∈ E, n e ≤ nonrealZeroCount t ∧
      ((∀ w, riemannHeat t w = 0 → w.im ≠ 0 → ∃ e ∈ E, w ∈ ball e (r e)) →
        nonrealZeroCount t = ∑ e ∈ E, n e) := by
  classical
  have hdiff := differentiable_riemannHeat ht.le
  have hZ : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), riemannHeat t z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (riemannHeat t) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat t) ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hr e he) (by linarith [hr e he] : r e < 2 * r e)
      isOpen_univ (subset_univ _) hdiff.differentiableOn (hsph e he)
  choose! Z hZball hZzero hZsum using hZ
  set F := (riemannHeat_nonreal_zeros_finite ht).toFinset with hF
  have hZF : ∀ e ∈ E, Z e ⊆ F := by
    intro e he z hz
    rw [hF, Set.Finite.mem_toFinset]
    exact ⟨(hZzero e he z (hZball e he z hz)).mpr hz, havoid e he z (hZball e he z hz)⟩
  have hpd : (E : Set ℂ).PairwiseDisjoint Z := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hZball e he z hz) (hZball e' he' z hz')
  have hnZ : ∀ e ∈ E, ∑ ρ ∈ Z e, zeroMult (riemannHeat t) ρ = n e := by
    intro e he
    have h := hZsum e he
    rw [hn e he] at h
    exact_mod_cast h.symm
  have hsumE : ∑ e ∈ E, n e = ∑ z ∈ E.biUnion Z, zeroMult (riemannHeat t) z := by
    rw [Finset.sum_biUnion hpd]
    exact Finset.sum_congr rfl fun e he => (hnZ e he).symm
  have hbsub : E.biUnion Z ⊆ F := Finset.biUnion_subset.mpr hZF
  rw [nonrealZeroCount_eq ht, ← hF]
  refine ⟨by rw [hsumE]; exact Finset.sum_le_sum_of_subset hbsub, fun hcover => ?_⟩
  have hFsub : F ⊆ E.biUnion Z := by
    intro w hw
    rw [hF, Set.Finite.mem_toFinset] at hw
    obtain ⟨e, he, hwb⟩ := hcover w hw.1 hw.2
    exact Finset.mem_biUnion.mpr ⟨e, he, (hZzero e he w hwb).mp hw.1⟩
  rw [hsumE, Finset.Subset.antisymm hFsub hbsub]

/-! ## The local behaviour of the count -/

/-- A positive lower bound for the distances between distinct points of a finite set. -/
theorem exists_pos_sep (E : Finset ℂ) : ∃ d > 0, ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → d ≤ dist e e' := by
  classical
  rcases (E.offDiag).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun e he₁ e' he' hne => ?_⟩
    have : (e, e') ∈ E.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne⟩
    rw [he] at this; simp at this
  · refine ⟨E.offDiag.inf' hne (fun pr => dist pr.1 pr.2), ?_, fun e he₁ e' he' hne' => ?_⟩
    · refine (Finset.lt_inf'_iff hne).mpr fun pr hpr => ?_
      obtain ⟨-, -, hpr⟩ := Finset.mem_offDiag.mp hpr
      exact dist_pos.mpr hpr
    · have hmem : (e, e') ∈ E.offDiag := Finset.mem_offDiag.mpr ⟨he₁, he', hne'⟩
      exact Finset.inf'_le (fun pr : ℂ × ℂ => dist pr.1 pr.2) hmem

/-- Zeros of `H_t` have `|Im z| ≤ 1/2` (de Bruijn's strip). -/
theorem abs_im_le_half_of_riemannHeat_eq_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : riemannHeat t z = 0) : |z.im| ≤ 1 / 2 := by
  have h := riemannHeat_zeros_im_sq_le ht hz
  have h2 : z.im ^ 2 ≤ (1 / 2) ^ 2 := h.trans (max_le (by linarith) (by norm_num))
  exact abs_le_of_sq_le_sq' h2 (by norm_num) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)

/-- **Local behaviour of the count.** For `0 < t₁ < 1/8` there is `δ > 0` with `N(t₁) ≤ N(s)` for
`|s − t₁| < δ`, `s > 0`, and `N(s) ≤ N(t₁)` for `t₁ < s < t₁ + δ`. -/
theorem exists_local_nonrealZeroCount {t₁ : ℝ} (ht₁ : 0 < t₁) (ht₁8 : t₁ < 1 / 8) :
    ∃ δ > 0, (∀ s, |s - t₁| < δ → 0 < s → nonrealZeroCount t₁ ≤ nonrealZeroCount s) ∧
      (∀ s, t₁ < s → s < t₁ + δ → nonrealZeroCount s ≤ nonrealZeroCount t₁) := by
  classical
  -- (1) the nonreal zeros near `t₁` lie in a fixed disc
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real_uniform (t₀ := t₁ / 2) (by linarith)
  set X := max X₀ 0 + 1 with hXdef
  have hinside : ∀ t ∈ Icc (t₁ / 2) (1 / 8), ∀ z, riemannHeat t z = 0 → z.im ≠ 0 → ‖z‖ < X := by
    intro t htI z hz him
    have htpos : 0 < t := by linarith [htI.1]
    have hre : |z.re| < X₀ := lt_of_not_ge fun h => him (hX₀ t htI z hz h)
    have him2 := abs_im_le_half_of_riemannHeat_eq_zero htpos hz
    have h3 := Complex.norm_le_abs_re_add_abs_im z
    have hX : X₀ ≤ max X₀ 0 := le_max_left _ _
    linarith
  -- (2) a zero-free circle `|z| = R` with `X < R < X + 1`
  have han : AnalyticOnNhd ℂ (riemannHeat t₁) (closedBall 0 (X + 1)) := fun z _ =>
    (differentiable_riemannHeat ht₁.le).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top ht₁.le z (analyticOrderAt_eq_top.mpr h))
  obtain ⟨R, hRI, hRn⟩ := (Set.Ioo_infinite (by linarith : X < X + 1)).exists_notMem_finset
    (hfin.toFinset.image (fun z => ‖z‖))
  have hRX : X < R := hRI.1
  have hR1 : R < X + 1 := hRI.2
  have hRpos : 0 < R := by have : 0 ≤ max X₀ 0 := le_max_right _ _; linarith
  have hsphR : ∀ w ∈ sphere (0 : ℂ) R, riemannHeat t₁ w ≠ 0 := by
    intro w hw h0
    rw [mem_sphere, dist_zero_right] at hw
    apply hRn
    refine Finset.mem_image.mpr ⟨w, ?_, hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨by rw [mem_closedBall, dist_zero_right]; linarith, h0⟩
  -- (3) the zeros of `H_{t₁}` in `|z| < R`
  set E := hfin.toFinset.filter (fun z => ‖z‖ < R) with hE
  have hmemE : ∀ z, z ∈ E ↔ riemannHeat t₁ z = 0 ∧ ‖z‖ < R := by
    intro z
    rw [hE, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨-, h0⟩, hz⟩; exact ⟨h0, hz⟩
    · rintro ⟨h0, hz⟩
      exact ⟨⟨by rw [mem_closedBall, dist_zero_right]; linarith, h0⟩, hz⟩
  -- (4) radii
  choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq ht₁ e
  choose ρ₁ hρ₁ hρ₁prop using fun e : ℂ => exists_ball_real_zeros_forward ht₁ e.re
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  set A : ℂ → ℝ := fun e => min (min (ρ₀ e) (ρ₁ e)) (min (d / 3) ((R - ‖e‖) / 2)) with hAdef
  set r : ℂ → ℝ := fun e => if e.im = 0 then A e else min (A e) (|e.im| / 2) with hrdef
  have hrA : ∀ e, r e ≤ A e := by
    intro e; simp only [hrdef]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hApos : ∀ e ∈ E, 0 < A e := by
    intro e he
    have hR := ((hmemE e).mp he).2
    exact lt_min (lt_min (hρ₀ e) (hρ₁ e)) (lt_min (by positivity) (by linarith))
  have hrpos : ∀ e ∈ E, 0 < r e := by
    intro e he
    simp only [hrdef]
    split_ifs with h
    · exact hApos e he
    · exact lt_min (hApos e he) (by have := abs_pos.mpr h; linarith)
  have hr₀ : ∀ e, r e ≤ ρ₀ e := fun e =>
    (hrA e).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hr₁ : ∀ e, r e ≤ ρ₁ e := fun e =>
    (hrA e).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrd : ∀ e, r e ≤ d / 3 := fun e =>
    (hrA e).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : ∀ e, r e ≤ (R - ‖e‖) / 2 := fun e =>
    (hrA e).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrim : ∀ e, e.im ≠ 0 → r e ≤ |e.im| / 2 := by
    intro e h; simp only [hrdef, if_neg h]; exact min_le_right _ _
  -- (5) geometry of the discs
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    linarith [hrd e, hrd e']
  have havoid : ∀ e, e.im ≠ 0 → ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e h w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have := hrim e h
    have hpos := abs_pos.mpr h
    linarith
  have hinR : ∀ e ∈ E, ∀ w ∈ ball e (r e), w ∈ ball (0 : ℂ) R := by
    intro e he w hw
    have hR := ((hmemE e).mp he).2
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w e
    linarith [hrR e]
  -- (6) counts near `t₁`
  have hbig := eventually_zeroSumBall_riemannHeat_eq_of_sphere ht₁ hRpos hsphR
  have hsmall : ∀ᶠ s in 𝓝 t₁, ∀ e ∈ E,
      zeroSumBall (riemannHeat s) e (r e) = (zeroMult (riemannHeat t₁) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), riemannHeat s w ≠ 0 :=
    (Filter.eventually_all_finset E).mpr fun e he => (hρ₀prop e (r e) (hrpos e he) (hr₀ e)).2.2
  have hcountE : zeroSumBall (riemannHeat t₁) 0 R =
      ∑ e ∈ E, (zeroMult (riemannHeat t₁) e : ℂ) := by
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) (differentiable_riemannHeat ht₁.le).differentiableOn hsphR
    have hZE : Z = E := by
      ext z
      constructor
      · intro hz
        have hb := hZb z hz
        refine (hmemE z).mpr ⟨(hZz z hb).mpr hz, ?_⟩
        rwa [mem_ball, dist_zero_right] at hb
      · intro hz
        obtain ⟨h0, hR⟩ := (hmemE z).mp hz
        exact (hZz z (by rw [mem_ball, dist_zero_right]; exact hR)).mp h0
    rw [hZs, hZE]
  -- (7) the real discs
  have hreal : ∀ e ∈ E, e.im = 0 → ∃ δ > 0, ∀ s, t₁ < s → s < t₁ + δ →
      ∀ w ∈ ball e (r e), riemannHeat s w = 0 → w.im = 0 := by
    intro e he him
    obtain ⟨δ, hδ, h⟩ := hρ₁prop e (r e) (hrpos e he) (hr₁ e)
    have he' : ((e.re : ℝ) : ℂ) = e := Complex.ext (by simp) (by simp [him])
    rw [he'] at h
    exact ⟨δ, hδ, h⟩
  choose! δr hδr hδrprop using hreal
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ : ∃ δ₂ > 0, ∀ e ∈ E, e.im = 0 → δ₂ ≤ δr e := by
    rcases (E.filter (fun e => e.im = 0)).eq_empty_or_nonempty with h | h
    · refine ⟨1, one_pos, fun e he him => ?_⟩
      have : e ∈ E.filter (fun e => e.im = 0) := Finset.mem_filter.mpr ⟨he, him⟩
      rw [h] at this; simp at this
    · refine ⟨(E.filter (fun e => e.im = 0)).inf' h δr, ?_, fun e he him => ?_⟩
      · refine (Finset.lt_inf'_iff h).mpr fun e he => ?_
        obtain ⟨he, him⟩ := Finset.mem_filter.mp he
        exact hδr e he him
      · exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨he, him⟩)
  obtain ⟨δ₀, hδ₀, hδ₀ev⟩ := Metric.eventually_nhds_iff.mp (hbig.and hsmall)
  set δ := min (min δ₀ δ₂) (min (t₁ / 2) (1 / 8 - t₁)) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₀ hδ₂) (lt_min (by linarith) (by linarith))
  set Enr := E.filter (fun e => e.im ≠ 0) with hEnr
  have hEnr_sub : ∀ e ∈ Enr, e ∈ E ∧ e.im ≠ 0 := fun e he => Finset.mem_filter.mp he
  -- the count at `t₁`
  have hN₁ : nonrealZeroCount t₁ = ∑ e ∈ Enr, zeroMult (riemannHeat t₁) e := by
    refine ((sum_le_nonrealZeroCount ht₁ (E := Enr) (r := r)
      (n := fun e => zeroMult (riemannHeat t₁) e)
      (fun e he => hrpos e (hEnr_sub e he).1)
      (fun e he => havoid e (hEnr_sub e he).2)
      (fun e he e' he' hne => hdisj e (hEnr_sub e he).1 e' (hEnr_sub e' he').1 hne)
      (fun e he => (hρ₀prop e (r e) (hrpos e (hEnr_sub e he).1) (hr₀ e)).1)
      (fun e he => (hρ₀prop e (r e) (hrpos e (hEnr_sub e he).1) (hr₀ e)).2.1)).2 ?_)
    intro w hw0 hwim
    have hwX := hinside t₁ ⟨by linarith, by linarith⟩ w hw0 hwim
    refine ⟨w, Finset.mem_filter.mpr ⟨(hmemE w).mpr ⟨hw0, by linarith⟩, hwim⟩,
      mem_ball_self (hrpos w ((hmemE w).mpr ⟨hw0, by linarith⟩))⟩
  refine ⟨δ, hδpos, fun s hs hs0 => ?_, fun s hts hst => ?_⟩
  · -- lower semicontinuity
    have hsd : dist s t₁ < δ₀ := by
      rw [Real.dist_eq]; exact hs.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    obtain ⟨-, hsm⟩ := hδ₀ev hsd
    rw [hN₁]
    exact (sum_le_nonrealZeroCount hs0 (E := Enr) (r := r)
      (n := fun e => zeroMult (riemannHeat t₁) e)
      (fun e he => hrpos e (hEnr_sub e he).1)
      (fun e he => havoid e (hEnr_sub e he).2)
      (fun e he e' he' hne => hdisj e (hEnr_sub e he).1 e' (hEnr_sub e' he').1 hne)
      (fun e he => (hsm e (hEnr_sub e he).1).2)
      (fun e he => (hsm e (hEnr_sub e he).1).1)).1
  · -- right-local constancy
    have hsd : dist s t₁ < δ₀ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have h1 : δ ≤ δ₀ := (min_le_left _ _).trans (min_le_left _ _)
      linarith
    obtain ⟨⟨hbs, hbsph⟩, hsm⟩ := hδ₀ev hsd
    have hs0 : 0 < s := by linarith
    have hsI : s ∈ Icc (t₁ / 2) (1 / 8) := by
      constructor
      · linarith
      · have : δ ≤ 1 / 8 - t₁ := (min_le_right _ _).trans (min_le_right _ _)
        linarith
    -- every zero of `H_s` in `|z| < R` lies in one of the small discs
    have hdiffs := differentiable_riemannHeat hs0.le
    obtain ⟨Zb, hZbb, hZbz, hZbs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) hdiffs.differentiableOn hbsph
    have hZe : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
        (∀ z ∈ ball e (r e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
        zeroSumBall (riemannHeat s) e (r e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
      fun e he => exists_zeroSet_zeroSumBall (hrpos e he) (by linarith [hrpos e he] : r e < 2 * r e)
        isOpen_univ (subset_univ _) hdiffs.differentiableOn (hsm e he).2
    choose! W hWb hWz hWs using hZe
    have hWsub : ∀ e ∈ E, W e ⊆ Zb := by
      intro e he z hz
      have hb := hWb e he z hz
      exact (hZbz z (hinR e he z hb)).mp ((hWz e he z hb).mpr hz)
    have hWdisj : (E : Set ℂ).PairwiseDisjoint W := by
      intro e he e' he' hne
      refine Finset.disjoint_left.mpr fun z hz hz' => ?_
      exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hWb e he z hz) (hWb e' he' z hz')
    have hsumN : ∑ z ∈ Zb, zeroMult (riemannHeat s) z =
        ∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z := by
      have h1 : ((∑ z ∈ Zb, zeroMult (riemannHeat s) z : ℕ) : ℂ) =
          ((∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z : ℕ) : ℂ) := by
        push_cast
        rw [← hZbs, hbs, hcountE]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [← hWs e he, (hsm e he).1]
      exact_mod_cast h1
    have hcov := subset_biUnion_of_sum_eq (fun z hz => one_le_zeroMult_riemannHeat hs0.le
      ((hZbz z (hZbb z hz)).mpr hz)) hWsub hWdisj hsumN
    have hcover : ∀ w, riemannHeat s w = 0 → w.im ≠ 0 → ∃ e ∈ Enr, w ∈ ball e (r e) := by
      intro w hw0 hwim
      have hwX := hinside s hsI w hw0 hwim
      have hwb : w ∈ ball (0 : ℂ) R := by rw [mem_ball, dist_zero_right]; linarith
      obtain ⟨e, he, hwe⟩ := Finset.mem_biUnion.mp (hcov ((hZbz w hwb).mp hw0))
      have hweb := hWb e he w hwe
      refine ⟨e, Finset.mem_filter.mpr ⟨he, fun him => hwim ?_⟩, hweb⟩
      refine hδrprop e he him s hts ?_ w hweb hw0
      have : δ ≤ δr e := ((min_le_left _ _).trans (min_le_right _ _)).trans (hδ₂le e he him)
      linarith
    have hNs := (sum_le_nonrealZeroCount hs0 (E := Enr) (r := r)
      (n := fun e => zeroMult (riemannHeat t₁) e)
      (fun e he => hrpos e (hEnr_sub e he).1)
      (fun e he => havoid e (hEnr_sub e he).2)
      (fun e he e' he' hne => hdisj e (hEnr_sub e he).1 e' (hEnr_sub e' he').1 hne)
      (fun e he => (hsm e (hEnr_sub e he).1).2)
      (fun e he => (hsm e (hEnr_sub e he).1).1)).2 hcover
    rw [hNs, hN₁]

/-! ## Real induction -/

/-- **Real induction.** An `ℕ`-valued function on `[a, b]` that does not increase just to the right
of any point, and does not drop just to the left of any point, satisfies `N b ≤ N a`. -/
theorem le_of_local_right_and_lsc {N : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b)
    (hright : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, t < s → s < t + δ → N s ≤ N t)
    (hlsc : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, t - δ < s → s < t → N t ≤ N s) : N b ≤ N a := by
  set S := {t ∈ Icc a b | ∀ u ∈ Icc a t, N u ≤ N a} with hS
  have haS : a ∈ S := ⟨⟨le_rfl, hab⟩, fun u hu => by rw [le_antisymm hu.2 hu.1]⟩
  have hbdd : BddAbove S := ⟨b, fun t ht => ht.1.2⟩
  set c := sSup S with hc
  have hac : a ≤ c := le_csSup hbdd haS
  have hcb : c ≤ b := csSup_le ⟨a, haS⟩ fun t ht => ht.1.2
  -- every point below `c` is controlled
  have hbelow : ∀ u ∈ Ico a c, N u ≤ N a := by
    intro u hu
    obtain ⟨t, htS, hut⟩ := exists_lt_of_lt_csSup ⟨a, haS⟩ hu.2
    exact htS.2 u ⟨hu.1, hut.le⟩
  have hcS : c ∈ S := by
    refine ⟨⟨hac, hcb⟩, fun u hu => ?_⟩
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · exact hbelow u ⟨hu.1, hlt⟩
    · rw [heq]
      rcases lt_or_eq_of_le hac with hac' | hac'
      · obtain ⟨δ, hδ, hl⟩ := hlsc c ⟨hac, hcb⟩
        set u' := max a (c - δ / 2)
        have hu'1 : c - δ < u' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
        have hu'2 : u' < c := max_lt hac' (by linarith)
        exact (hl u' hu'1 hu'2).trans (hbelow u' ⟨le_max_left _ _, hu'2⟩)
      · rw [← hac']
  rcases lt_or_eq_of_le hcb with hlt | heq
  · exfalso
    obtain ⟨δ, hδ, hr⟩ := hright c ⟨hac, hcb⟩
    set c' := min b (c + δ / 2)
    have hcc' : c < c' := lt_min hlt (by linarith)
    have hc'S : c' ∈ S := by
      refine ⟨⟨by linarith, min_le_left _ _⟩, fun u hu => ?_⟩
      rcases le_or_gt u c with huc | huc
      · exact hcS.2 u ⟨hu.1, huc⟩
      · have hu2 : u < c + δ := lt_of_le_of_lt hu.2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
        exact (hr u huc hu2).trans (hcS.2 c ⟨hac, le_rfl⟩)
    have := le_csSup hbdd hc'S
    linarith
  · rw [← heq]
    exact hcS.2 c ⟨hac, le_rfl⟩

/-! ## The theorem -/

theorem nonrealZeroCount_eq_zero_of_le {t : ℝ} (ht : 1 / 8 ≤ t) : nonrealZeroCount t = 0 := by
  have htpos : 0 < t := by linarith
  rw [nonrealZeroCount_eq htpos]
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  exfalso
  have h := riemannHeat_zeros_im_sq_le htpos hz.1
  rw [max_eq_right (by linarith)] at h
  exact hz.2 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg _)))

/-- **The nonreal zero count of the de Bruijn–Newman flow is nonincreasing** on `(0, ∞)`. -/
theorem nonrealZeroCount_antitoneOn : AntitoneOn nonrealZeroCount (Ioi 0) := by
  intro a ha b _ hab
  refine le_of_local_right_and_lsc hab (fun t ht => ?_) (fun t ht => ?_)
  · have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    rcases lt_or_ge t (1 / 8) with h8 | h8
    · obtain ⟨δ, hδ, -, hr⟩ := exists_local_nonrealZeroCount htpos h8
      exact ⟨δ, hδ, hr⟩
    · exact ⟨1, one_pos, fun s hts _ => by
        rw [nonrealZeroCount_eq_zero_of_le (by linarith)]; exact Nat.zero_le _⟩
  · have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    rcases lt_or_ge t (1 / 8) with h8 | h8
    · obtain ⟨δ, hδ, hl, -⟩ := exists_local_nonrealZeroCount htpos h8
      refine ⟨min δ t, lt_min hδ htpos, fun s hs1 hs2 => hl s ?_ ?_⟩
      · rw [abs_lt]; constructor <;> linarith [min_le_left δ t]
      · linarith [min_le_right δ t]
    · exact ⟨1, one_pos, fun s _ _ => by rw [nonrealZeroCount_eq_zero_of_le h8]; exact Nat.zero_le _⟩

end

end RHTower.DeBruijn
