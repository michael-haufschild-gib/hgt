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
  have h2j : (0:ℝ) < 2 ^ j := by positivity
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hsplit : (2:ℝ) ^ j = 2 ^ k * 2 ^ (j - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  have ht : t = h * 2 ^ (j - k) := by
    have h2 : h * 2 ^ j = 2 ^ k * t := by
      field_simp at h1
      linarith
    rw [hsplit] at h2
    have h3 : 2 ^ k * (h * 2 ^ (j - k)) = 2 ^ k * t := by
      ring_nf
      ring_nf at h2
      linarith
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
theorem not_both_adjacent_folds_agree {ra RW α β a b : ℝ}
    (hra1 : 1 < ra) (hraRW : ra ^ 2 < RW) (hβ : β = α + 7 * Real.pi / 4)
    {σj σj1 : ℂ → ℂ}
    (hinj : Set.InjOn σj (arcAnnulus ra RW α β))
    (hAm : max α a < min β b)
    (hAm1 : max α (a + Real.pi) < min β (b + Real.pi))
    (hag : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) (max α a) (min β b), σj1 (w ^ 2) = σj w)
    (hag1 : ∀ w ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (a + Real.pi)) (min β (b + Real.pi)),
      σj1 (w ^ 2) = σj w) : False := by
  have hπ := Real.pi_pos
  have hra0 : (0:ℝ) < ra := by linarith
  have hRW1 : (1:ℝ) < RW := by nlinarith
  have hRW0 : (0:ℝ) < RW := by linarith
  have hsqrt : ra < Real.sqrt RW := (Real.lt_sqrt (le_of_lt hra0)).mpr hraRW
  have hsqRW : Real.sqrt RW ≤ RW := by
    nlinarith [Real.sq_sqrt (le_of_lt hRW0), Real.sqrt_nonneg RW,
      sq_nonneg (Real.sqrt RW - 1)]
  have hlogs : Real.log ra < Real.log (Real.sqrt RW) :=
    Real.log_lt_log hra0 hsqrt
  have hlogRW : Real.log (Real.sqrt RW) ≤ Real.log RW :=
    Real.log_le_log (Real.sqrt_pos.mpr hRW0) hsqRW
  -- destructure the nonemptiness of both slots
  simp only [max_lt_iff, lt_min_iff] at hAm hAm1
  -- the antipodal-pair angular interval
  have hLU : max α (a) < min (β - Real.pi) (b) := by
    simp only [max_lt_iff, lt_min_iff]
    refine ⟨⟨by rw [hβ]; linarith, by linarith [hAm1.1.2]⟩, hAm.2.1, hAm.2.2⟩
  set t : ℝ := (max α (a)
    + min (β - Real.pi) (b)) / 2 with htdef
  have htL : max α (a) < t := by
    rw [htdef]
    linarith [hLU]
  have htU : t < min (β - Real.pi) (b) := by
    rw [htdef]
    linarith [hLU]
  have ht1 : α < t := lt_of_le_of_lt (le_max_left _ _) htL
  have ht2 : a < t := lt_of_le_of_lt (le_max_right _ _) htL
  have ht3 : t < β - Real.pi := lt_of_lt_of_le htU (min_le_left _ _)
  have ht4 : t < b := lt_of_lt_of_le htU (min_le_right _ _)
  -- the pair
  set ρ : ℝ := (Real.log ra + Real.log (Real.sqrt RW)) / 2 with hρdef
  set ξ : ℂ := (ρ : ℂ) + (t : ℂ) * Complex.I with hξdef
  have hρlo : Real.log ra < ρ := by rw [hρdef]; linarith
  have hρhi : ρ < Real.log (Real.sqrt RW) := by rw [hρdef]; linarith
  have hξre : ξ.re = ρ := by simp [hξdef]
  have hξim : ξ.im = t := by simp [hξdef]
  have hw : Complex.exp ξ ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (a)) (min β (b)) := by
    refine ⟨ξ, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · rw [hξre]; exact hρlo
    · rw [hξre]; exact hρhi
    · rw [hξim]; exact htL
    · rw [hξim, lt_min_iff]
      exact ⟨by linarith, ht4⟩
  have hw' : Complex.exp (ξ + Real.pi * Complex.I) ∈ arcAnnulus ra (Real.sqrt RW)
      (max α (a + Real.pi)) (min β (b + Real.pi)) := by
    have hre' : (ξ + Real.pi * Complex.I).re = ρ := by simp [hξdef]
    have him' : (ξ + Real.pi * Complex.I).im = t + Real.pi := by simp [hξdef]
    refine ⟨ξ + Real.pi * Complex.I, ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · rw [hre']; exact hρlo
    · rw [hre']; exact hρhi
    · rw [him', max_lt_iff]
      constructor
      · linarith
      · linarith
    · rw [him', lt_min_iff]
      constructor
      · linarith
      · linarith
  -- the negation identity and the kill
  have hneg : Complex.exp (ξ + Real.pi * Complex.I) = -Complex.exp ξ := by
    rw [Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hsq : Complex.exp (ξ + Real.pi * Complex.I) ^ 2 = Complex.exp ξ ^ 2 := by
    rw [hneg]
    ring
  have h1 := hag _ hw
  have h2 := hag1 _ hw'
  rw [hsq] at h2
  have h3 : σj (Complex.exp ξ) = σj (Complex.exp (ξ + Real.pi * Complex.I)) := by
    rw [← h1, ← h2]
  have hsubA : ∀ {L U : ℝ}, α ≤ L → U ≤ β →
      arcAnnulus ra (Real.sqrt RW) L U ⊆ arcAnnulus ra RW α β := by
    intro L U hL hU w hwm
    obtain ⟨ζ, ⟨g1, g2, g3, g4⟩, rfl⟩ := hwm
    exact ⟨ζ, ⟨g1, lt_of_lt_of_le g2 hlogRW, by linarith, by linarith⟩, rfl⟩
  have hwA : Complex.exp ξ ∈ arcAnnulus ra RW α β :=
    hsubA (le_max_left _ _) (min_le_left _ _) hw
  have hw'A : Complex.exp (ξ + Real.pi * Complex.I) ∈ arcAnnulus ra RW α β :=
    hsubA (le_max_left _ _) (min_le_left _ _) hw'
  have h4 : Complex.exp ξ = Complex.exp (ξ + Real.pi * Complex.I) := hinj hwA hw'A h3
  rw [hneg] at h4
  have h5 : (2 : ℂ) * Complex.exp ξ = 0 := by linear_combination h4
  have h6 : Complex.exp ξ = 0 := by
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h two_ne_zero
    · exact h
  exact Complex.exp_ne_zero ξ h6

end Bottcher

namespace Bottcher

/-- **All-or-nothing agreement on a preconnected open set.**  If agreement of `h₁, h₂` at a
point of `W` propagates to a neighbourhood (the covering-section property supplied by
`sections_eventuallyEq_of_orbit_ne_zero`) and both functions are continuous on `W`, then the
agreement locus of `W` is everything or nothing — the clopen dichotomy pinning each fold slot
entirely inside or entirely outside the overlap. -/
theorem agree_locus_all_or_none {W : Set ℂ} (hWc : IsPreconnected W)
    {h₁ h₂ : ℂ → ℂ}
    (hc₁ : ∀ w ∈ W, ContinuousAt h₁ w) (hc₂ : ∀ w ∈ W, ContinuousAt h₂ w)
    (hloc : ∀ w ∈ W, h₁ w = h₂ w → ∀ᶠ v in nhds w, h₁ v = h₂ v) :
    (∀ w ∈ W, h₁ w = h₂ w) ∨ (∀ w ∈ W, h₁ w ≠ h₂ w) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨w₁, hw₁W, hw₁⟩, w₂, hw₂W, hw₂⟩ := hcon
  set u : Set ℂ := {x | ∀ᶠ y in nhds x, h₁ y = h₂ y} with hudef
  set v : Set ℂ := {x | ∀ᶠ y in nhds x, h₁ y ≠ h₂ y} with hvdef
  have huo : IsOpen u := isOpen_setOf_eventually_nhds
  have hvo : IsOpen v := isOpen_setOf_eventually_nhds
  have hcover : W ⊆ u ∪ v := by
    intro w hw
    by_cases heq : h₁ w = h₂ w
    · exact Or.inl (hloc w hw heq)
    · right
      have hce : ContinuousAt (fun x => h₁ x - h₂ x) w := (hc₁ w hw).sub (hc₂ w hw)
      have hne : (fun x => h₁ x - h₂ x) w ≠ 0 := sub_ne_zero_of_ne heq
      filter_upwards [hce.eventually_ne hne] with y hy
      exact fun h => hy (by rw [h, sub_self])
  have hWu : (W ∩ u).Nonempty := ⟨w₂, hw₂W, hloc w₂ hw₂W hw₂⟩
  have hWv : (W ∩ v).Nonempty := by
    refine ⟨w₁, hw₁W, ?_⟩
    have hce : ContinuousAt (fun x => h₁ x - h₂ x) w₁ := (hc₁ w₁ hw₁W).sub (hc₂ w₁ hw₁W)
    have hne : (fun x => h₁ x - h₂ x) w₁ ≠ 0 := sub_ne_zero_of_ne hw₁
    filter_upwards [hce.eventually_ne hne] with y hy
    exact fun h => hy (by rw [h, sub_self])
  obtain ⟨x, hxW, hxu, hxv⟩ := hWc u v huo hvo hcover hWu hWv
  obtain ⟨y, hy1, hy2⟩ := (hxu.and hxv).exists
  exact hy2 hy1

end Bottcher

namespace Bottcher

/-- **The consecutive scaffold overlap is preconnected** (task #140, L5 assembly).  Under the
level window `5h/4 < log ra`, `log RW < 7h/2`, the normalized slit position
`α ∈ [−π/4, 7π/4]` with exact width `β − α = 7π/4`, and the certified fold-1 doubling window,
the overlap `σ_j''A ∩ σ_{j+1}''A` equals `σ_j''S₁` — the image of the certified fold slot:

* forcing pins every overlap point to the agreement locus of `σ_{j+1}∘sq` and `σ_j`;
* the squaring window decomposes into fold slots `S₀ ∪ S₁ ∪ S₂`;
* agreement is all-or-nothing per slot (covering sections at noncritical levels);
* the doubling window certifies agreement on `S₁`, and the antipode argument kills `S₀`, `S₂`
  (each adjacent to `S₁`). -/
theorem scaffold_scaffold_overlap_preconnected
    {c : ℂ} {rlo R₀ : ℝ} (S : TowerSection c rlo R₀)
    {ra RW α β J₁ J₂ : ℝ} {σj σj1 : ℂ → ℂ} {j : ℕ}
    (hrlo : 1 < rlo) (hra : rlo < ra) (hraRW : ra ^ 2 < RW) (hRWR : RW < R₀)
    (hh0 : 0 < greenFunctionDyn c 0)
    (hra54 : 5 * greenFunctionDyn c 0 / 4 ≤ Real.log ra)
    (hRW72 : Real.log RW ≤ 7 * greenFunctionDyn c 0 / 2)
    (hβ : β = α + 7 * Real.pi / 4)
    (hαlo : -(Real.pi / 4) ≤ α) (hαhi : α ≤ 7 * Real.pi / 4)
    (hPj : ScaffoldProps c S.T (arcAnnulus ra RW α β) j σj)
    (hPj1 : ScaffoldProps c S.T (arcAnnulus ra RW α β) (j + 1) σj1)
    (_hαJ₁ : α ≤ J₁) (hJ₁J₂ : J₁ < J₂) (hJ₂β : J₂ ≤ β)
    (hJ₁dbl : α ≤ 2 * J₁ - 2 * Real.pi) (hJ₂dbl : 2 * J₂ - 2 * Real.pi ≤ β)
    (hdbl : ∀ w ∈ arcAnnulus ra (Real.sqrt RW) J₁ J₂, σj1 (w ^ 2) = σj w) :
    IsPreconnected (σj '' arcAnnulus ra RW α β ∩ σj1 '' arcAnnulus ra RW α β) := by
  classical
  have hπ := Real.pi_pos
  obtain ⟨hanj, hlevj, hinjj, _hdnej, hitj⟩ := hPj
  obtain ⟨hanj1, hlevj1, _hinjj1, _hdnej1, hitj1⟩ := hPj1
  set A : Set ℂ := arcAnnulus ra RW α β with hAdef
  have hra1 : (1:ℝ) < ra := by linarith
  have hra0 : (0:ℝ) < ra := by linarith
  have hRW1 : (1:ℝ) ≤ RW := by nlinarith
  have hRW0 : (0:ℝ) < RW := by linarith
  have hraRW' : ra < RW := by nlinarith
  have hsqrt : ra < Real.sqrt RW := (Real.lt_sqrt (le_of_lt hra0)).mpr hraRW
  have hAopen : IsOpen A := isOpen_arcAnnulus _ _ _ _
  have hAsub : A ⊆ annulusSet ra RW := arcAnnulus_subset _ _ hra0 hraRW'
  have hAann : ∀ v ∈ A, v ∈ annulusSet rlo R₀ := fun v hv =>
    ⟨lt_trans hra (hAsub hv).1, lt_trans (hAsub hv).2 hRWR⟩
  -- the three fold slots
  set S₀ : Set ℂ := arcAnnulus ra (Real.sqrt RW) (max α (α / 2)) (min β (β / 2)) with hS₀def
  set S₁ : Set ℂ := arcAnnulus ra (Real.sqrt RW)
    (max α (α / 2 + Real.pi)) (min β (β / 2 + Real.pi)) with hS₁def
  set S₂ : Set ℂ := arcAnnulus ra (Real.sqrt RW)
    (max α (α / 2 + 2 * Real.pi)) (min β (β / 2 + 2 * Real.pi)) with hS₂def
  have hdec : {w : ℂ | w ∈ A ∧ w ^ 2 ∈ A} = S₀ ∪ S₁ ∪ S₂ :=
    sq_window_decomposition hra1 hRW1 hβ hαlo hαhi
  have hWsubA : ∀ {w : ℂ}, w ∈ A → w ^ 2 ∈ A → w ∈ S₀ ∪ S₁ ∪ S₂ := by
    intro w h1 h2
    rw [← hdec]
    exact ⟨h1, h2⟩
  have hslotW : ∀ {w : ℂ}, w ∈ S₀ ∪ S₁ ∪ S₂ → w ∈ A ∧ w ^ 2 ∈ A := by
    intro w hw
    rw [← hdec] at hw
    exact hw
  -- local propagation of agreement on the squaring window
  have hloc : ∀ w₀ : ℂ, w₀ ∈ A → w₀ ^ 2 ∈ A → σj1 (w₀ ^ 2) = σj w₀ →
      ∀ᶠ w in nhds w₀, σj1 (w ^ 2) = σj w := by
    intro w₀ hw₀A hw₀sq heq
    have hWopen : IsOpen {w : ℂ | w ∈ A ∧ w ^ 2 ∈ A} := by
      have h1 : Continuous fun w : ℂ => w ^ 2 := continuous_pow 2
      exact hAopen.inter (hAopen.preimage h1)
    have hWnhds : {w : ℂ | w ∈ A ∧ w ^ 2 ∈ A} ∈ nhds w₀ :=
      hWopen.mem_nhds ⟨hw₀A, hw₀sq⟩
    have hp₁ : ∀ᶠ w in nhds w₀, (quadratic c)^[j + 1] (σj1 (w ^ 2)) = S.T (w ^ 2) := by
      filter_upwards [hWnhds] with w hw
      exact hitj1 (w ^ 2) hw.2
    have hp₂ : ∀ᶠ w in nhds w₀, (quadratic c)^[j + 1] (σj w) = S.T (w ^ 2) := by
      filter_upwards [hWnhds] with w hw
      have hwann := hAann w hw.1
      have hw2ann := hAann (w ^ 2) hw.2
      have h1 : (quadratic c)^[j + 1] (σj w) = quadratic c (S.T w) := by
        rw [Function.iterate_succ_apply', hitj w hw.1]
      rw [h1, quadratic_apply, ← S.fe w hwann hw2ann]
    have hc₁ : ContinuousAt (fun w : ℂ => σj1 (w ^ 2)) w₀ := by
      have h1 : ContinuousAt σj1 (w₀ ^ 2) := (hanj1 _ hw₀sq).continuousAt
      exact ContinuousAt.comp (f := fun w : ℂ => w ^ 2) h1 ((continuous_pow 2).continuousAt)
    have hc₂ : ContinuousAt σj w₀ := (hanj _ hw₀A).continuousAt
    -- noncriticality at the common value
    have hlev := hlevj w₀ hw₀A
    have htlo : 5 * greenFunctionDyn c 0 / 4 < Real.log ‖w₀‖ := by
      have h1 := (hAsub hw₀A).1
      have h2 : Real.log ra < Real.log ‖w₀‖ := Real.log_lt_log hra0 h1
      linarith
    have hthi : Real.log ‖w₀‖ < 7 * greenFunctionDyn c 0 / 4 := by
      have h1 : ‖w₀ ^ 2‖ < RW := (hAsub hw₀sq).2
      rw [norm_pow] at h1
      have hw₀pos : (0:ℝ) < ‖w₀‖ := lt_trans hra0 (hAsub hw₀A).1
      have h2 : Real.log (‖w₀‖ ^ 2) < Real.log RW :=
        Real.log_lt_log (by nlinarith) h1
      rw [Real.log_pow] at h2
      push_cast at h2
      linarith
    have hnc : ∀ k, k < j + 1 → (quadratic c)^[k] (σj w₀) ≠ 0 := by
      intro k hk
      exact scaffold_orbit_ne_zero hh0 hlev htlo hthi (by omega)
    have heq' : (fun w : ℂ => σj1 (w ^ 2)) w₀ = σj w₀ := heq
    have hnc' : ∀ k, k < j + 1 → (quadratic c)^[k] ((fun w : ℂ => σj1 (w ^ 2)) w₀) ≠ 0 := by
      intro k hk
      show (quadratic c)^[k] (σj1 (w₀ ^ 2)) ≠ 0
      rw [heq]
      exact hnc k hk
    exact sections_eventuallyEq_of_orbit_ne_zero hc₁ hc₂ hp₁ hp₂ heq' hnc'
  -- per-slot dichotomy
  have hdich : ∀ (T : Set ℂ), T ⊆ S₀ ∪ S₁ ∪ S₂ → IsPreconnected T →
      (∀ w ∈ T, σj1 (w ^ 2) = σj w) ∨ (∀ w ∈ T, σj1 (w ^ 2) ≠ σj w) := by
    intro T hTsub hTconn
    apply agree_locus_all_or_none hTconn
    · intro w hw
      have h1 := hslotW (hTsub hw)
      have h2 : ContinuousAt σj1 (w ^ 2) := (hanj1 _ h1.2).continuousAt
      exact ContinuousAt.comp (f := fun w : ℂ => w ^ 2) h2 ((continuous_pow 2).continuousAt)
    · intro w hw
      exact (hanj _ (hslotW (hTsub hw)).1).continuousAt
    · intro w hw heq
      have h1 := hslotW (hTsub hw)
      exact hloc w h1.1 h1.2 heq
  -- the certified window sits in slot 1
  have hwinsub : arcAnnulus ra (Real.sqrt RW) J₁ J₂ ⊆ S₁ := by
    rintro w ⟨ξ, ⟨g1, g2, g3, g4⟩, rfl⟩
    refine ⟨ξ, ⟨g1, g2, ?_, ?_⟩, rfl⟩
    · rw [max_lt_iff]
      constructor
      · linarith
      · linarith
    · rw [lt_min_iff]
      constructor
      · linarith
      · linarith
  have hwinne : (arcAnnulus ra (Real.sqrt RW) J₁ J₂).Nonempty :=
    (isConnected_arcAnnulus hra0 hsqrt hJ₁J₂).nonempty
  have hS₁conn : IsPreconnected S₁ := by
    rcases hwinne with ⟨w, hw⟩
    have hne := hwinsub hw
    obtain ⟨ξ, ⟨_, _, g3, g4⟩, _⟩ := hne
    exact (isConnected_arcAnnulus hra0 hsqrt (lt_trans g3 g4)).isPreconnected
  have hS₁sub : S₁ ⊆ S₀ ∪ S₁ ∪ S₂ := fun w hw => Or.inl (Or.inr hw)
  -- slot 1 agrees everywhere
  have hE₁ : ∀ w ∈ S₁, σj1 (w ^ 2) = σj w := by
    rcases hdich S₁ hS₁sub hS₁conn with h | h
    · exact h
    · obtain ⟨w, hw⟩ := hwinne
      exact absurd (hdbl w hw) (h w (hwinsub hw))
  -- slot-1 angular nonemptiness for the antipode kills
  have hS₁ne : max α (α / 2 + Real.pi) < min β (β / 2 + Real.pi) := by
    obtain ⟨w, hw⟩ := hwinne
    obtain ⟨ξ, ⟨_, _, g3, g4⟩, _⟩ := hwinsub hw
    exact lt_trans g3 g4
  -- the agreement locus avoids slots 0 and 2
  have hE₀ : ∀ w ∈ S₀, σj1 (w ^ 2) ≠ σj w := by
    have hS₀sub : S₀ ⊆ S₀ ∪ S₁ ∪ S₂ := fun w hw => Or.inl (Or.inl hw)
    by_cases hne : max α (α / 2) < min β (β / 2)
    · rcases hdich S₀ hS₀sub (isConnected_arcAnnulus hra0 hsqrt hne).isPreconnected with h | h
      · exfalso
        exact not_both_adjacent_folds_agree (a := α / 2) (b := β / 2)
          hra1 hraRW hβ hinjj hne hS₁ne h hE₁
      · exact h
    · intro w hw
      exfalso
      obtain ⟨ξ, ⟨_, _, g3, g4⟩, _⟩ := hw
      exact hne (lt_trans g3 g4)
  have hE₂ : ∀ w ∈ S₂, σj1 (w ^ 2) ≠ σj w := by
    have hS₂sub : S₂ ⊆ S₀ ∪ S₁ ∪ S₂ := fun w hw => Or.inr hw
    by_cases hne : max α (α / 2 + 2 * Real.pi) < min β (β / 2 + 2 * Real.pi)
    · rcases hdich S₂ hS₂sub (isConnected_arcAnnulus hra0 hsqrt hne).isPreconnected with h | h
      · exfalso
        have hba : α / 2 + Real.pi + Real.pi = α / 2 + 2 * Real.pi := by ring
        have hbb : β / 2 + Real.pi + Real.pi = β / 2 + 2 * Real.pi := by ring
        exact not_both_adjacent_folds_agree (a := α / 2 + Real.pi) (b := β / 2 + Real.pi)
          hra1 hraRW hβ hinjj hS₁ne (by rw [hba, hbb]; exact hne)
          hE₁ (by rw [hba, hbb]; exact h)
      · exact h
    · intro w hw
      exfalso
      obtain ⟨ξ, ⟨_, _, g3, g4⟩, _⟩ := hw
      exact hne (lt_trans g3 g4)
  -- the overlap is exactly the σj-image of slot 1
  have hover : σj '' A ∩ σj1 '' A = σj '' S₁ := by
    ext z
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, v, hv, hveq⟩
      have hforce : v = w ^ 2 := by
        have hfam : ∀ n : ℕ, (fun k : ℕ => if k = j then σj else σj1) n
            = if n = j then σj else σj1 := fun _ => rfl
        apply scaffold_overlap_forcing (σ := fun k : ℕ => if k = j then σj else σj1)
          (j := j) S hrlo hra hraRW' hRWR ?_ ?_ ?_ ?_ hv hw ?_
        · simpa using hlevj
        · intro u hu
          simpa [Nat.succ_ne_self] using hlevj1 u hu
        · simpa using hitj
        · intro u hu
          simpa [Nat.succ_ne_self] using hitj1 u hu
        · simpa [Nat.succ_ne_self] using hveq
      rw [hforce] at hveq hv
      have hwslot := hWsubA hw hv
      rcases hwslot with (h0 | h1) | h2
      · exact absurd hveq (hE₀ w h0)
      · exact ⟨w, h1, rfl⟩
      · exact absurd hveq (hE₂ w h2)
    · rintro ⟨w, hw, rfl⟩
      have h1 := hslotW (hS₁sub hw)
      exact ⟨⟨w, h1.1, rfl⟩, w ^ 2, h1.2, hE₁ w hw⟩
  rw [hover]
  apply hS₁conn.image
  apply (hanj.mono ?_).continuousOn
  intro w hw
  exact (hslotW (hS₁sub hw)).1

end Bottcher

namespace Bottcher

/-- Arc annuli are invariant under a full-turn shift of the angular window. -/
theorem arcAnnulus_shift_two_pi (r R α β : ℝ) :
    arcAnnulus r R (α + 2 * Real.pi) (β + 2 * Real.pi) = arcAnnulus r R α β := by
  ext w
  constructor
  · rintro ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨ξ - 2 * Real.pi * Complex.I, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show Real.log r < (ξ - 2 * Real.pi * Complex.I).re
      simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show (ξ - 2 * Real.pi * Complex.I).re < Real.log R
      simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show α < (ξ - 2 * Real.pi * Complex.I).im
      simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show (ξ - 2 * Real.pi * Complex.I).im < β
      simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · rw [Complex.exp_sub]
      have h5 : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I 1
        simpa [mul_comm, mul_assoc] using this
      rw [h5, div_one]
  · rintro ⟨ξ, ⟨h1, h2, h3, h4⟩, rfl⟩
    refine ⟨ξ + 2 * Real.pi * Complex.I, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show Real.log r < (ξ + 2 * Real.pi * Complex.I).re
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show (ξ + 2 * Real.pi * Complex.I).re < Real.log R
      simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show α + 2 * Real.pi < (ξ + 2 * Real.pi * Complex.I).im
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · show (ξ + 2 * Real.pi * Complex.I).im < β + 2 * Real.pi
      simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
      linarith
    · rw [Complex.exp_add]
      have h5 : Complex.exp (2 * Real.pi * Complex.I) = 1 := by
        have := Complex.exp_int_mul_two_pi_mul_I 1
        simpa [mul_comm, mul_assoc] using this
      rw [h5, mul_one]

end Bottcher

namespace Bottcher

/-- **The sharp scale of a filled Julia set**: `K_c ⊆ closedBall 0 (√‖c‖ + 1)`.  This is the
load-bearing scale of the comparable-norm pair regime: the deep pieces of a `c₁`-tower live at
`K_{c₁}`-scale `~√‖c₁‖`, so a second Julia set is norm-separated from them exactly when
`√(2‖c₂‖) + 1` stays below the tower floor — the linear gap.  At comparable norms the two
scales coincide, and separation must come from steering or harmonic-mass integrality (OP16). -/
theorem filledJulia_subset_closedBall_sqrt (c : ℂ) :
    filledJulia c ⊆ Metric.closedBall 0 (Real.sqrt ‖c‖ + 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hlt
  push Not at hlt
  set s : ℝ := Real.sqrt ‖c‖ with hsdef
  have hs0 : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ‖c‖ := Real.sq_sqrt (norm_nonneg c)
  set d : ℝ := ‖z‖ - (s + 1) with hddef
  have hd0 : (0:ℝ) < d := by rw [hddef]; linarith
  have hgrow : ∀ n : ℕ, ‖z‖ + n * d ≤ ‖(quadratic c)^[n] z‖ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        set w := (quadratic c)^[m] z with hwdef
        have hmd : (0:ℝ) ≤ (m : ℝ) * d := by positivity
        have hw1' : (1:ℝ) ≤ ‖w‖ := by
          have h1 : s + 1 + d = ‖z‖ := by rw [hddef]; ring
          linarith [ih]
        have hstep : ‖w‖ ^ 2 - ‖c‖ ≤ ‖quadratic c w‖ := by
          have h1 : ‖w ^ 2‖ ≤ ‖w ^ 2 + c‖ + ‖c‖ := by
            calc ‖w ^ 2‖ = ‖w ^ 2 + c + -c‖ := by ring_nf
              _ ≤ ‖w ^ 2 + c‖ + ‖-c‖ := norm_add_le _ _
              _ = ‖w ^ 2 + c‖ + ‖c‖ := by rw [norm_neg]
          rw [quadratic_apply]
          rw [norm_pow] at h1
          linarith
        have hws : 1 + ((m : ℝ) + 1) * d ≤ ‖w‖ - s := by
      
      
          have h1 : s + 1 + d = ‖z‖ := by rw [hddef]; ring
          nlinarith [ih]
        have hprod : (1 + ((m : ℝ) + 1) * d) * ‖w‖ ≤ (‖w‖ - s) * (‖w‖ + s) := by
          apply mul_le_mul hws (by linarith) (by linarith) (by linarith)
        have hkey : ‖z‖ + ((m : ℝ) + 1) * d ≤ ‖w‖ ^ 2 - ‖c‖ := by
          have h2 : (‖w‖ - s) * (‖w‖ + s) = ‖w‖ ^ 2 - s ^ 2 := by ring
          have h3 : (1 + ((m : ℝ) + 1) * d) * ‖w‖
              = ‖w‖ + ((m : ℝ) + 1) * d * ‖w‖ := by ring
          have h4 : ((m : ℝ) + 1) * d ≤ ((m : ℝ) + 1) * d * ‖w‖ := by
            nlinarith [hd0, hw1']
          rw [← hs2]
          nlinarith [ih, hprod]
        push_cast
        linarith
  rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz
  obtain ⟨C, hC⟩ := hz
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - ‖z‖) / d)
  have h1 := hC ((quadratic c)^[n] z) ⟨n, rfl⟩
  have h2 := hgrow n
  have h3 : C - ‖z‖ < n * d := by
    rw [div_lt_iff₀ hd0] at hn
    linarith
  linarith

end Bottcher
