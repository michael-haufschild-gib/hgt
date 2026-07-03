/-
# Chain-overlap connectivity: the lobe clause (task #140, step 3a)

The scaffold–lobe overlap of the wedge-slit chain is identified exactly: pushing both sides to
the section through the iterate identities and applying the section's injectivity forces the
parameters to agree, so

  `σ_k''(arcAnnulus ra RW α β) ∩ SL_k''(annulusSet ra rb) = σ_k''(arcAnnulus ra rb α β)`

— the `σ_k`-image of a connected arc annulus, hence preconnected with no component analysis.
This discharges the final clause of `ChainOverlapsConnected` unconditionally; the consecutive
scaffold clauses (the fold/antipode analysis) follow in the next steps.

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.W4LinWinding
import GaloisForLFunctions.Bottcher.BottcherTowerData
import GaloisForLFunctions.Bottcher.CoverConstruction

open Complex Set

namespace Bottcher

/-- **Scaffold–lobe overlap identification.**  A common point of the depth-`k` scaffold arc
and the depth-`k` lobe has equal parameters (`S.inj` after pushing through `f^[k]`), so the
overlap is exactly the scaffold image of the thin arc annulus. -/
theorem scaffold_lobe_overlap_eq {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    {ra rb RW α β : ℝ} (hrloRa : rlo < ra) (hra0 : 0 < ra) (hrab : ra < rb)
    (hrbRW : rb < RW) (hRWR : RW < R₀)
    {σk SLk : ℂ → ℂ} {k : ℕ}
    (hitσ : ∀ v ∈ arcAnnulus ra RW α β, (quadratic c)^[k] (σk v) = S.T v)
    (hitL : ∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SLk v) = S.T v)
    (hmatch : ∀ v ∈ arcAnnulus ra rb α β, SLk v = σk v) :
    σk '' arcAnnulus ra RW α β ∩ SLk '' annulusSet ra rb
      = σk '' arcAnnulus ra rb α β := by
  have hraRW : ra < RW := lt_trans hrab hrbRW
  ext z
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, v, hv, hveq⟩
    -- push both parameters to the section
    have h1 : S.T w = S.T v := by
      rw [← hitσ w hw, ← hitL v hv, hveq]
    have hwann : w ∈ annulusSet rlo R₀ := by
      have h2 := arcAnnulus_subset α β hra0 hraRW hw
      exact ⟨lt_trans hrloRa h2.1, lt_trans h2.2 hRWR⟩
    have hvann : v ∈ annulusSet rlo R₀ :=
      ⟨lt_trans hrloRa hv.1, lt_trans (lt_trans hv.2 hrbRW) hRWR⟩
    have hwv : w = v := S.inj hwann hvann h1
    -- the parameter sits in the thin arc annulus
    obtain ⟨ξ, ⟨h2, _, h4, h5⟩, rfl⟩ := hw
    refine ⟨Complex.exp ξ, ⟨ξ, ⟨h2, ?_, h4, h5⟩, rfl⟩, rfl⟩
    have h6 : ‖Complex.exp ξ‖ < rb := by
      rw [← hwv] at hv
      exact hv.2
    rw [Complex.norm_exp] at h6
    calc ξ.re = Real.log (Real.exp ξ.re) := (Real.log_exp _).symm
      _ < Real.log rb := Real.log_lt_log (Real.exp_pos _) h6
  · rintro ⟨w, hw, rfl⟩
    have hwA : w ∈ arcAnnulus ra RW α β :=
      arcAnnulus_mono_radius (by linarith) (le_of_lt hrbRW) hw
    refine ⟨⟨w, hwA, rfl⟩, w, ?_, (hmatch w hw).symm ▸ rfl⟩
    · exact arcAnnulus_subset α β hra0 hrab hw

/-- **The lobe clause of `ChainOverlapsConnected` is unconditional**: the scaffold–lobe
overlap is the continuous image of a connected arc annulus. -/
theorem scaffold_lobe_overlap_preconnected {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    {ra rb RW α β : ℝ} (hrloRa : rlo < ra) (hra0 : 0 < ra) (hrab : ra < rb)
    (hrbRW : rb < RW) (hRWR : RW < R₀) (hαβ : α < β)
    {σk SLk : ℂ → ℂ} {k : ℕ}
    (han : AnalyticOnNhd ℂ σk (arcAnnulus ra RW α β))
    (hitσ : ∀ v ∈ arcAnnulus ra RW α β, (quadratic c)^[k] (σk v) = S.T v)
    (hitL : ∀ v ∈ annulusSet ra rb, (quadratic c)^[k] (SLk v) = S.T v)
    (hmatch : ∀ v ∈ arcAnnulus ra rb α β, SLk v = σk v) :
    IsPreconnected (σk '' arcAnnulus ra RW α β ∩ SLk '' annulusSet ra rb) := by
  rw [scaffold_lobe_overlap_eq S hrloRa hra0 hrab hrbRW hRWR hitσ hitL hmatch]
  apply (isConnected_arcAnnulus hra0 hrab hαβ).isPreconnected.image
  exact (han.mono (arcAnnulus_mono_radius (by linarith) (le_of_lt hrbRW))).continuousOn

end Bottcher

namespace Bottcher

/-- **Fold decomposition of the squaring window.**  A point of the slit arc whose square also
lies in the slit arc sits in one of (at most) three fold slots `m ∈ {0, 1, 2}` — the arc
annuli with angular windows `(α, β) ∩ ((α, β) + mπ)/…` — provided the window has the standard
width `7π/4` and the base angle is normalized to `[−π/4, 7π/4]`.  The slots are pairwise
π/8-separated, so the squaring window has at most three connected components. -/
theorem sq_window_decomposition {ra RW α β : ℝ} (hra1 : 1 < ra) (hRW1 : 1 ≤ RW)
    (hβ : β = α + 7 * Real.pi / 4)
    (hαlo : -(Real.pi / 4) ≤ α) (hαhi : α ≤ 7 * Real.pi / 4) :
    {w : ℂ | w ∈ arcAnnulus ra RW α β ∧ w ^ 2 ∈ arcAnnulus ra RW α β}
      = arcAnnulus ra (Real.sqrt RW) (max α (α / 2)) (min β (β / 2))
        ∪ arcAnnulus ra (Real.sqrt RW) (max α (α / 2 + Real.pi)) (min β (β / 2 + Real.pi))
        ∪ arcAnnulus ra (Real.sqrt RW)
            (max α (α / 2 + 2 * Real.pi)) (min β (β / 2 + 2 * Real.pi)) := by
  have hπ := Real.pi_pos
  have hRW0 : (0:ℝ) < RW := by linarith
  have hlogra : (0:ℝ) < Real.log ra := Real.log_pos hra1
  have hlogRW0 : (0:ℝ) ≤ Real.log RW := Real.log_nonneg hRW1
  have hlogsqrt : Real.log (Real.sqrt RW) = Real.log RW / 2 := Real.log_sqrt (le_of_lt hRW0)
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨⟨ξ, ⟨hr1, hr2, hi1, hi2⟩, rfl⟩, ⟨η, ⟨hs1, hs2, hj1, hj2⟩, hsq⟩⟩
    have h2ξ : Complex.exp ξ ^ 2 = Complex.exp (2 * ξ) := by
      rw [sq, ← Complex.exp_add]
      ring_nf
    rw [h2ξ] at hsq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hsq
    have hnre : η.re = 2 * ξ.re := by
      rw [hn]
      simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
        Complex.intCast_im]
    have hnim : η.im = 2 * ξ.im + n * (2 * Real.pi) := by
      rw [hn]
      simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
        Complex.intCast_im]
    -- the fold index is one of 0, −1, −2
    have hn1 : (-3 : ℝ) < n := by nlinarith [hj1, hi2, hnim]
    have hn2 : (n : ℝ) < 1 := by nlinarith [hj2, hi1, hnim]
    have hn3 : (-3 : ℤ) < n := by exact_mod_cast hn1
    have hn4 : n < (1 : ℤ) := by exact_mod_cast hn2
    have hre2 : ξ.re < Real.log (Real.sqrt RW) := by
      rw [hlogsqrt]
      rw [hnre] at hs2
      linarith
    interval_cases n
    · -- n = −2 : fold slot m = 2
      right
      refine ⟨ξ, ⟨hr1, hre2, ?_, ?_⟩, rfl⟩
      · rw [max_lt_iff]
        refine ⟨hi1, ?_⟩
        have h1 : η.im = 2 * ξ.im - 2 * (2 * Real.pi) := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj1
        linarith
      · rw [lt_min_iff]
        refine ⟨hi2, ?_⟩
        have h1 : η.im = 2 * ξ.im - 2 * (2 * Real.pi) := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj2
        linarith
    · -- n = −1 : fold slot m = 1
      left; right
      refine ⟨ξ, ⟨hr1, hre2, ?_, ?_⟩, rfl⟩
      · rw [max_lt_iff]
        refine ⟨hi1, ?_⟩
        have h1 : η.im = 2 * ξ.im - 2 * Real.pi := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj1
        linarith
      · rw [lt_min_iff]
        refine ⟨hi2, ?_⟩
        have h1 : η.im = 2 * ξ.im - 2 * Real.pi := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj2
        linarith
    · -- n = 0 : fold slot m = 0
      left; left
      refine ⟨ξ, ⟨hr1, hre2, ?_, ?_⟩, rfl⟩
      · rw [max_lt_iff]
        refine ⟨hi1, ?_⟩
        have h1 : η.im = 2 * ξ.im := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj1
        linarith
      · rw [lt_min_iff]
        refine ⟨hi2, ?_⟩
        have h1 : η.im = 2 * ξ.im := by
          rw [hnim]; push_cast; ring
        rw [h1] at hj2
        linarith
  · -- each slot is inside the squaring window
    have hbase : ∀ m : ℤ, ∀ ξ : ℂ,
        Real.log ra < ξ.re → ξ.re < Real.log (Real.sqrt RW) →
        max α (α / 2 + m * Real.pi) < ξ.im → ξ.im < min β (β / 2 + m * Real.pi) →
        Complex.exp ξ ∈ arcAnnulus ra RW α β ∧
          Complex.exp ξ ^ 2 ∈ arcAnnulus ra RW α β := by
      intro m ξ h1 h2 h3 h4
      rw [max_lt_iff] at h3
      rw [lt_min_iff] at h4
      have h2' : ξ.re < Real.log RW := by
        rw [hlogsqrt] at h2
        linarith
      constructor
      · exact ⟨ξ, ⟨h1, h2', h3.1, h4.1⟩, rfl⟩
      · refine ⟨2 * ξ - m * (2 * Real.pi * Complex.I), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
        · show Real.log ra < (2 * ξ - m * (2 * Real.pi * Complex.I)).re
          simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
            Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
          nlinarith
        · show (2 * ξ - m * (2 * Real.pi * Complex.I)).re < Real.log RW
          simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
            Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
          rw [hlogsqrt] at h2
          nlinarith
        · show α < (2 * ξ - m * (2 * Real.pi * Complex.I)).im
          simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
            Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
          nlinarith [h3.2]
        · show (2 * ξ - m * (2 * Real.pi * Complex.I)).im < β
          simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.intCast_re,
            Complex.intCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
          nlinarith [h4.2]
        · rw [Complex.exp_sub]
          have h5 : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
            Complex.exp_int_mul_two_pi_mul_I m
          rw [h5, div_one, sq, ← Complex.exp_add]
          ring_nf
    rintro ((⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩ | ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩) |
      ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · exact hbase 0 ξ h1 h2 (by simpa using h3) (by simpa using h4)
    · exact hbase 1 ξ h1 h2 (by push_cast; simpa using h3) (by push_cast; simpa using h4)
    · exact hbase 2 ξ h1 h2 (by push_cast; simpa using h3) (by push_cast; simpa using h4)

end Bottcher

namespace Bottcher

/-- **Local agreement of two sections of the quadratic iterate.**  Two functions with the same
`f_c^[n]`-projection near `w₀` that agree at `w₀` — whose common value has a `0`-free forward
orbit below depth `n` — agree on a neighbourhood of `w₀`: the iterate is a local homeomorphism
at a noncritical point (`exists_openPartialHomeomorph_of_hasStrictDerivAt`), and local sections
through the same point coincide.  This is the openness half of the clopen equality-locus
argument for the fold components. -/
theorem sections_eventuallyEq_of_orbit_ne_zero {c : ℂ} {n : ℕ}
    {h₁ h₂ P : ℂ → ℂ} {w₀ : ℂ}
    (hc₁ : ContinuousAt h₁ w₀) (hc₂ : ContinuousAt h₂ w₀)
    (hp₁ : ∀ᶠ w in nhds w₀, (quadratic c)^[n] (h₁ w) = P w)
    (hp₂ : ∀ᶠ w in nhds w₀, (quadratic c)^[n] (h₂ w) = P w)
    (heq : h₁ w₀ = h₂ w₀)
    (hnc : ∀ k, k < n → (quadratic c)^[k] (h₁ w₀) ≠ 0) :
    ∀ᶠ w in nhds w₀, h₁ w = h₂ w := by
  have hd : (∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] (h₁ w₀)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact mul_ne_zero two_ne_zero (hnc k (Finset.mem_range.mp hk))
  obtain ⟨φ, hzsrc, hφeq⟩ := exists_openPartialHomeomorph_of_hasStrictDerivAt
    (hasStrictDerivAt_quadratic_iterate c n (h₁ w₀)) hd
  have h2src : h₂ w₀ ∈ φ.source := heq ▸ hzsrc
  have hm₁ : ∀ᶠ w in nhds w₀, h₁ w ∈ φ.source :=
    hc₁.eventually_mem (φ.open_source.mem_nhds hzsrc)
  have hm₂ : ∀ᶠ w in nhds w₀, h₂ w ∈ φ.source :=
    hc₂.eventually_mem (φ.open_source.mem_nhds h2src)
  filter_upwards [hm₁, hm₂, hp₁, hp₂] with w hw₁ hw₂ hq₁ hq₂
  apply φ.injOn hw₁ hw₂
  show φ (h₁ w) = φ (h₂ w)
  rw [hφeq]
  show (quadratic c)^[n] (h₁ w) = (quadratic c)^[n] (h₂ w)
  rw [hq₁, hq₂]

end Bottcher

namespace Bottcher

/-- The Green level of the `k`-th image: `G(f^[k] z) = 2^k · G(z)`. -/
theorem greenFunctionDyn_iterate (c z : ℂ) (k : ℕ) :
    greenFunctionDyn c ((quadratic c)^[k] z) = 2 ^ k * greenFunctionDyn c z := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', greenFunctionDyn_quadratic, ih, pow_succ]
      ring

/-- **No critical orbit at working levels.**  A point at Green level `t / 2^j` with
`t ∈ (5h/4, 7h/4)` has a `0`-free forward orbit up to depth `j`: hitting `0` at step `k ≤ j`
would force `t = 2^{j−k} h`, but no power of two lies in `(5/4, 7/4)`.  This feeds the
noncriticality hypothesis of `sections_eventuallyEq_of_orbit_ne_zero` on every fold slot. -/
theorem scaffold_orbit_ne_zero {c z : ℂ} {j k : ℕ} {t : ℝ}
    (hh0 : 0 < greenFunctionDyn c 0)
    (hlev : greenFunctionDyn c z = t / 2 ^ j)
    (hlo : 5 * greenFunctionDyn c 0 / 4 < t) (hhi : t < 7 * greenFunctionDyn c 0 / 4)
    (hk : k ≤ j) :
    (quadratic c)^[k] z ≠ 0 := by
  intro h0
  set h : ℝ := greenFunctionDyn c 0 with hhdef
  have h1 : greenFunctionDyn c ((quadratic c)^[k] z) = 2 ^ k * (t / 2 ^ j) := by
    rw [greenFunctionDyn_iterate, hlev]
  rw [h0, ← hhdef] at h1
  -- `t = 2^{j−k} · h`
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hsplit : (2:ℝ) ^ j = 2 ^ k * 2 ^ (j - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have ht : t = h * 2 ^ (j - k) := by
    have h2 : h * 2 ^ j = 2 ^ k * t := by
      field_simp at h1
      linarith
    rw [hsplit] at h2
    have h3 : 2 ^ k * (h * 2 ^ (j - k)) = 2 ^ k * t := by ring_nf; ring_nf at h2; linarith
    exact (mul_left_cancel₀ (ne_of_gt h2k) h3).symm
  rcases Nat.lt_or_ge k j with hkj | hkj
  · have h4 : (2:ℝ) ≤ 2 ^ (j - k) := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (j - k) := by
            apply pow_le_pow_right₀ (by norm_num)
            omega
    nlinarith
  · have h5 : j = k := le_antisymm hkj hk
    rw [h5] at ht
    simp at ht
    nlinarith

/-- **Adjacent fold slots cannot both agree.**  If the doubling identity
`σ_{j+1}(w²) = σ_j(w)` held on two ADJACENT fold slots (`m` and `m+1`), an antipodal pair
`(w, −w)` spanning them would give `σ_j(w) = σ_{j+1}(w²) = σ_{j+1}((−w)²) = σ_j(−w)`, against
the injectivity of `σ_j` — the kill that pins the agreement locus to a single slot. -/
theorem not_both_adjacent_folds_agree {ra RW α β : ℝ} {m : ℤ}
    (hra1 : 1 < ra) (hraRW : ra ^ 2 < RW) (hβ : β = α + 7 * Real.pi / 4)
    {σj σj1 : ℂ → ℂ}
    (hinj : Set.InjOn σj (arcAnnulus ra RW α β))
    (hAm : max α (α / 2 + m * Real.pi) < min β (β / 2 + m * Real.pi))
    (hAm1 : max α (α / 2 + (m + 1) * Real.pi) < min β (β / 2 + (m + 1) * Real.pi))
    (hag : ∀ w ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (α / 2 + m * Real.pi)) (min β (β / 2 + m * Real.pi)), σj1 (w ^ 2) = σj w)
    (hag1 : ∀ w ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (α / 2 + (m + 1) * Real.pi)) (min β (β / 2 + (m + 1) * Real.pi)),
      σj1 (w ^ 2) = σj w) : False := by
  have hπ := Real.pi_pos
  have hra0 : (0:ℝ) < ra := by linarith
  have hRW1 : (1:ℝ) < RW := by nlinarith
  have hsqrt : ra < Real.sqrt RW := (Real.lt_sqrt (le_of_lt hra0)).mpr hraRW
  have hsqRW : Real.sqrt RW ≤ RW := by
    nlinarith [Real.sq_sqrt (le_of_lt (lt_trans one_pos hRW1)),
      Real.sqrt_nonneg RW, Real.one_le_sqrt.mpr (le_of_lt hRW1)]
  have hlogs : Real.log ra < Real.log (Real.sqrt RW) :=
    Real.log_lt_log hra0 hsqrt
  have hlogRW : Real.log (Real.sqrt RW) ≤ Real.log RW :=
    Real.log_le_log (Real.sqrt_pos.mpr (by linarith)) hsqRW
  -- angular position of the antipodal pair
  rw [max_lt_iff, lt_min_iff] at hAm hAm1
  set t : ℝ := (max α (α / 2 + m * Real.pi) + min (β - Real.pi) (β / 2 + m * Real.pi)) / 2
    with htdef
  have htlo : max α (α / 2 + m * Real.pi) < t := by
    rw [htdef]
    have h1 : max α (α / 2 + m * Real.pi) < min (β - Real.pi) (β / 2 + m * Real.pi) := by
      rw [max_lt_iff, lt_min_iff]
      constructor
      · constructor
        · linarith [hAm.1.2, hAm1.2.1]
        · linarith [hAm.1.2]
      · constructor
        · push_cast at hAm1 ⊢
          linarith [hAm1.2.1]
        · linarith [hAm.1.2]
    rw [max_lt_iff] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  have hthi : t < min (β - Real.pi) (β / 2 + m * Real.pi) := by
    rw [htdef]
    have h1 : max α (α / 2 + m * Real.pi) < min (β - Real.pi) (β / 2 + m * Real.pi) := by
      rw [max_lt_iff, lt_min_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · linarith [hAm.1.2, hAm1.2.1]
      · linarith [hAm.1.2]
      · push_cast at hAm1 ⊢
        linarith [hAm1.2.1]
      · linarith [hAm.1.2]
    rw [lt_min_iff] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2, le_max_left α (α / 2 + m * Real.pi),
      le_max_right α (α / 2 + m * Real.pi)]
  -- the pair
  set ρ : ℝ := (Real.log ra + Real.log (Real.sqrt RW)) / 2 with hρdef
  set ξ : ℂ := (ρ : ℂ) + (t : ℂ) * Complex.I with hξdef
  have hξre : ξ.re = ρ := by simp [hξdef]
  have hξim : ξ.im = t := by simp [hξdef]
  have hρlo : Real.log ra < ρ := by rw [hρdef]; linarith
  have hρhi : ρ < Real.log (Real.sqrt RW) := by rw [hρdef]; linarith
  rw [lt_min_iff] at hthi
  rw [max_lt_iff] at htlo
  have hw : Complex.exp ξ ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (α / 2 + m * Real.pi)) (min β (β / 2 + m * Real.pi)) := by
    refine ⟨ξ, ⟨by rw [hξre]; exact hρlo, by rw [hξre]; exact hρhi, ?_, ?_⟩, rfl⟩
    · rw [hξim, max_lt_iff]; exact htlo
    · rw [hξim, lt_min_iff]
      constructor
      · linarith [hthi.1]
      · exact hthi.2
  have hw' : Complex.exp (ξ + Real.pi * Complex.I) ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (α / 2 + (m + 1) * Real.pi)) (min β (β / 2 + (m + 1) * Real.pi)) := by
    refine ⟨ξ + Real.pi * Complex.I, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · show Real.log ra < (ξ + Real.pi * Complex.I).re
      simp [hξdef]
      linarith
    · show (ξ + Real.pi * Complex.I).re < Real.log (Real.sqrt RW)
      simp [hξdef]
      linarith
    · show max α (α / 2 + (m + 1) * Real.pi) < (ξ + Real.pi * Complex.I).im
      have him : (ξ + Real.pi * Complex.I).im = t + Real.pi := by simp [hξdef]
      rw [him, max_lt_iff]
      constructor
      · linarith [htlo.1]
      · push_cast
        linarith [htlo.2]
    · show (ξ + Real.pi * Complex.I).im < min β (β / 2 + (m + 1) * Real.pi)
      have him : (ξ + Real.pi * Complex.I).im = t + Real.pi := by simp [hξdef]
      rw [him, lt_min_iff]
      constructor
      · linarith [hthi.1]
      · push_cast
        linarith [hthi.2]
  -- the negation identity and the kill
  have hneg : Complex.exp (ξ + Real.pi * Complex.I) = -Complex.exp ξ := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hsq : Complex.exp (ξ + Real.pi * Complex.I) ^ 2 = Complex.exp ξ ^ 2 := by
    rw [hneg]; ring
  have h1 := hag _ hw
  have h2 := hag1 _ hw'
  rw [hsq] at h2
  have h3 : σj (Complex.exp ξ) = σj (Complex.exp (ξ + Real.pi * Complex.I)) := by
    rw [← h1, ← h2]
  -- both points lie in the base arc
  have hsubA : ∀ {L U : ℝ}, α ≤ L → U ≤ β →
      arcAnnulus ra (Real.sqrt RW) L U ⊆ arcAnnulus ra RW α β := by
    intro L U hL hU w hw
    obtain ⟨ζ, ⟨g1, g2, g3, g4⟩, rfl⟩ := hw
    exact ⟨ζ, ⟨g1, lt_of_lt_of_le g2 (by
      calc Real.log (Real.sqrt RW) ≤ Real.log RW := hlogRW), by linarith, by linarith⟩, rfl⟩
  have hwA : Complex.exp ξ ∈ arcAnnulus ra RW α β :=
    hsubA (le_max_left _ _) (min_le_left _ _) hw
  have hw'A : Complex.exp (ξ + Real.pi * Complex.I) ∈ arcAnnulus ra RW α β :=
    hsubA (le_max_left _ _) (min_le_left _ _) hw'
  have h4 : Complex.exp ξ = Complex.exp (ξ + Real.pi * Complex.I) := hinj hwA hw'A h3
  rw [hneg] at h4
  have h5 : (2 : ℂ) * Complex.exp ξ = 0 := by linear_combination h4
  have h6 : Complex.exp ξ = 0 := by
    field_simp at h5
    exact h5
  exact Complex.exp_ne_zero ξ h6

end Bottcher
