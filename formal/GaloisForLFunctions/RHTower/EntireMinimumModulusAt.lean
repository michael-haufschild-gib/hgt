import GaloisForLFunctions.RHTower.EntireMinimumModulus
import GaloisForLFunctions.HTGeometry.AnalyticRootFactor
import GaloisForLFunctions.HTGeometry.PolyaFreeBasePoint

/-!
# The minimum modulus at an arbitrary centre, and the displacement floor

Translating the argument moves the minimum-modulus theorem off the origin.  This matters for the
composition estimates, where the relevant circle surrounds an interior base point rather than the
centre of the large disc.

Applied to the difference quotient of a function at that base point, the translated theorem produces
a *displacement* floor: a radius on whose circle `‖g z - g c‖` is bounded below by the radius times
the quotient's floor.  The displacement floor is what places a disc in the image.
-/

open Complex Metric Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- **The minimum modulus at an arbitrary centre.**  The statement of
`exists_radius_norm_ge_of_analytic` with the origin replaced by an arbitrary point, obtained by
translating the function. -/
theorem exists_radius_norm_ge_of_analytic_at {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    {R R' Mf H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall c R' ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, f z = 0)
    (hMf : ∀ z : ℂ, ‖z - c‖ = R' → ‖f z‖ ≤ Mf)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (0 < Mf → f c ≠ 0 →
        ((∑ a ∈ T, m a : ℕ) : ℝ) * Real.log ((R' - R) / R) ≤ Real.log (Mf / ‖f c‖)) ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z - c‖ = s → H ^ (∑ a ∈ T, m a) * L ≤ ‖f z‖) := by
  have hshift : Continuous (fun ζ : ℂ => c + ζ) := continuous_const.add continuous_id
  have hUcopen : IsOpen ((fun ζ : ℂ => c + ζ) ⁻¹' U) := hU.preimage hshift
  have hballc : closedBall (0 : ℂ) R' ⊆ (fun ζ : ℂ => c + ζ) ⁻¹' U := by
    intro ζ hζ
    have hζ' : ‖ζ‖ ≤ R' := by simpa using mem_closedBall_iff_norm.mp hζ
    refine hball ?_
    rw [mem_closedBall_iff_norm]
    simpa using hζ'
  have hfc : AnalyticOnNhd ℂ (fun ζ : ℂ => f (c + ζ)) ((fun ζ : ℂ => c + ζ) ⁻¹' U) := by
    refine AnalyticOnNhd.comp hf ?_ ?_
    · exact fun ζ _ => analyticAt_const.add analyticAt_id
    · exact fun ζ hζ => hζ
  have hnzc : ∀ a ∈ (fun ζ : ℂ => c + ζ) ⁻¹' U, ¬ ∀ᶠ ζ in 𝓝 a, f (c + ζ) = 0 := by
    intro a ha hcon
    refine hnz (c + a) ha ?_
    have htend : Filter.Tendsto (fun w : ℂ => w - c) (𝓝 (c + a)) (𝓝 a) := by
      have h₀ : Filter.Tendsto (fun w : ℂ => w - c) (𝓝 (c + a)) (𝓝 (c + a - c)) :=
        (continuous_id.sub continuous_const).tendsto (c + a)
      simpa using h₀
    filter_upwards [htend.eventually hcon] with w hw
    simpa using hw
  have hMfc : ∀ ζ : ℂ, ‖ζ‖ = R' → ‖f (c + ζ)‖ ≤ Mf := by
    intro ζ hζ
    exact hMf (c + ζ) (by simpa using hζ)
  obtain ⟨T, m, L, hL, hcount, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic (A := A) hUcopen hR h2R hballc hfc hnzc hMfc hH hB0 hBR
  refine ⟨T, m, L, hL, ?_, ?_⟩
  · intro hMf0 hfc0
    have := hcount hMf0 (by simpa using hfc0)
    simpa using this
  · intro hgap
    obtain ⟨s, hs, hfloor⟩ := hcircle hgap
    refine ⟨s, hs, ?_⟩
    intro z hz
    have := hfloor (z - c) (by simpa using hz)
    simpa using this

/-! ## The displacement factor -/

/-- **The displacement factor.**  For a function that is nowhere locally equal to its value at `c`,
the displacement `g - g c` factors as `(· - c)` times an analytic function which is itself nowhere
locally zero. -/
theorem exists_displacement_factor {g : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hcU : c ∈ U) (hg : AnalyticOnNhd ℂ g U)
    (hnc : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, g z = g c) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧ (∀ z ∈ U, g z - g c = (z - c) * h z) ∧
      ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, h z = 0 := by
  have hshift : AnalyticOnNhd ℂ (fun z => g z - g c) U := hg.sub analyticOnNhd_const
  have hroot : (fun z => g z - g c) c = 0 := by simp
  have hne : ¬ ∀ᶠ z in 𝓝 c, g z - g c = 0 := by
    intro hcon
    refine hnc c hcU ?_
    filter_upwards [hcon] with z hz
    exact sub_eq_zero.mp hz
  obtain ⟨h, hhan, hfac⟩ := exists_global_factor_of_root hshift hcU hroot hne
  refine ⟨h, hhan, hfac, ?_⟩
  intro a ha hcon
  refine hnc a ha ?_
  have hUmem : ∀ᶠ z in 𝓝 a, z ∈ U := hU.mem_nhds ha
  filter_upwards [hcon, hUmem] with z hz hzU
  have := hfac z hzU
  rw [hz, mul_zero] at this
  exact sub_eq_zero.mp this

/-- **The displacement floor from a floor for the factor.**  On a circle of radius `s` about `c`, a
lower bound `μ` for the displacement factor gives the lower bound `s · μ` for the displacement
itself. -/
theorem displacement_floor_of_factor {g h : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {s μ : ℝ}
    (hfac : ∀ z ∈ U, g z - g c = (z - c) * h z)
    (hsub : ∀ z : ℂ, ‖z - c‖ = s → z ∈ U)
    (hfloor : ∀ z : ℂ, ‖z - c‖ = s → μ ≤ ‖h z‖) :
    ∀ z : ℂ, ‖z - c‖ = s → s * μ ≤ ‖g z - g c‖ := by
  intro z hz
  rw [hfac z (hsub z hz), norm_mul, hz]
  have hs0 : 0 ≤ s := by
    rw [← hz]
    exact norm_nonneg _
  exact mul_le_mul_of_nonneg_left (hfloor z hz) hs0

/-- **A radius with a displacement floor.**  Combining the translated minimum modulus with the
displacement factor: on some circle of radius `s` in the window, `‖g z - g c‖ ≥ s · H^n · L`. -/
theorem exists_radius_displacement_floor {g h : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    {R R' Mh H A B : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall c R' ⊆ U)
    (hhan : AnalyticOnNhd ℂ h U) (hhnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, h z = 0)
    (hfac : ∀ z ∈ U, g z - g c = (z - c) * h z)
    (hMh : ∀ z : ℂ, ‖z - c‖ = R' → ‖h z‖ ≤ Mh)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) (hBR' : B ≤ R') :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B, ∀ z : ℂ, ‖z - c‖ = s →
          s * (H ^ (∑ a ∈ T, m a) * L) ≤ ‖g z - g c‖) := by
  have hBle : B ≤ R' := hBR'
  obtain ⟨T, m, L, hL, _, hcircle⟩ :=
    exists_radius_norm_ge_of_analytic_at (A := A) hU hR h2R hball hhan hhnz hMh hH hB0 hBR
  refine ⟨T, m, L, hL, ?_⟩
  intro hgap
  obtain ⟨s, hs, hfloor⟩ := hcircle hgap
  obtain ⟨hsA, hsB⟩ := Set.mem_Icc.mp hs
  refine ⟨s, hs, ?_⟩
  refine displacement_floor_of_factor hfac ?_ hfloor
  intro z hz
  refine hball ?_
  rw [mem_closedBall_iff_norm, hz]
  linarith [hsB, hBle]

/-! ## The disc in the image -/

/-- **The composition disc from analytic hypotheses.**  On some circle of radius `s` in the window
the displacement floor is `s · H^n · L`, and the quantitative open mapping theorem at the base point
`c` then puts the ball of half that radius about `g c` inside the image of the large disc.

The base point is free: only `‖c‖ + B ≤ S` is required, so `c` may sit near the boundary of the
large disc, which is exactly the regime in which the displacement floor is of the order of the
maximum modulus. -/
theorem exists_radius_ball_subset_image {g h : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    {R R' Mh H A B S : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (h2R : 2 * R < R')
    (hball : closedBall c R' ⊆ U)
    (hhan : AnalyticOnNhd ℂ h U) (hhnz : ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, h z = 0)
    (hfac : ∀ z ∈ U, g z - g c = (z - c) * h z)
    (hMh : ∀ z : ℂ, ‖z - c‖ = R' → ‖h z‖ ≤ Mh)
    (hH : 0 < H) (hB0 : 0 ≤ B) (hBR : B < R) (hBR' : B ≤ R') (hA : 0 < A)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S)) (hcS : ‖c‖ + B ≤ S)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c) :
    ∃ (T : Finset ℂ) (m : ℂ → ℕ) (L : ℝ), 0 < L ∧
      (2 * ((∑ a ∈ T, m a : ℕ) : ℝ) * H < B - A →
        ∃ s ∈ Set.Icc A B,
          ball (g c) (s * (H ^ (∑ a ∈ T, m a) * L) / 2) ⊆ g '' closedBall (0 : ℂ) S) := by
  obtain ⟨T, m, L, hL, hfloorexists⟩ :=
    exists_radius_displacement_floor (A := A) hU hR h2R hball hhan hhnz hfac hMh hH hB0 hBR hBR'
  refine ⟨T, m, L, hL, ?_⟩
  intro hgap
  obtain ⟨s, hs, hfloor⟩ := hfloorexists hgap
  obtain ⟨hsA, hsB⟩ := Set.mem_Icc.mp hs
  refine ⟨s, hs, ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le hA hsA
  have hcs : ‖c‖ + s ≤ S := by linarith
  have hsphere : ∀ z ∈ sphere c s, s * (H ^ (∑ a ∈ T, m a) * L) ≤ ‖g z - g c‖ := by
    intro z hz
    exact hfloor z (by simpa [mem_sphere_iff_norm] using hz)
  exact ball_subset_image_of_circle_floor_at hs0 hcs hgS hsphere hnc

/-! ## An explicit displacement floor

When the displacement factor is zero free on the disc — that is, when `g` takes the value `g c` only
at `c` there — no zero extraction is needed and the Borel--Carathéodory anchor bound applies
directly.  The resulting floor is completely explicit in `‖g' c‖` and the local maximum. -/

/-- The displacement factor at the base point is the derivative. -/
theorem deriv_eq_displacement_factor {g h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z) :
    deriv g c = h c := by
  have hcmem : c ∈ ball c R := mem_ball_self hR
  have hhc : HasDerivAt h (deriv h c) c := (hhan c hcmem).differentiableAt.hasDerivAt
  have hprod : HasDerivAt (fun z : ℂ => (z - c) * h z) (1 * h c + (c - c) * deriv h c) c :=
    ((hasDerivAt_id c).sub_const c).mul hhc
  have hsum : HasDerivAt (fun z : ℂ => g c + (z - c) * h z)
      (0 + (1 * h c + (c - c) * deriv h c)) c :=
    (hasDerivAt_const c (g c)).add hprod
  have hval : (0 : ℂ) + (1 * h c + (c - c) * deriv h c) = h c := by ring
  rw [hval] at hsum
  have heq : g =ᶠ[nhds c] fun z => g c + (z - c) * h z := by
    filter_upwards [isOpen_ball.mem_nhds hcmem] with z hz
    have := hfac z hz
    linear_combination this
  exact (hsum.congr_of_eventuallyEq heq).deriv

/-- **An explicit displacement floor.**  If the displacement factor is zero free and bounded by `M`
on the disc of radius `R` about `c`, then on the circle of radius `r < R`

  `‖g z - g c‖ ≥ r · ‖g' c‖ · (M / ‖g' c‖) ^ (-2r/(R-r))`. -/
theorem displacement_floor_explicit {g h : ℂ → ℂ} {c : ℂ} {R r M : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hhsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hhc : 0 < ‖h c‖) (hcM : ‖h c‖ < M)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z) :
    ∀ z : ℂ, ‖z - c‖ = r →
      r * (‖h c‖ * Real.exp (-(2 * Real.log (M / ‖h c‖) * r / (R - r)))) ≤ ‖g z - g c‖ := by
  have hlow := norm_lower_bound_of_anchor hr hrR hhan hhne hhsup hhc hcM (le_refl ‖h c‖)
  intro z hz
  have hzball : z ∈ ball c R := by
    rw [mem_ball_iff_norm, hz]
    exact hrR
  have hzclosed : z ∈ closedBall c r := by
    rw [mem_closedBall_iff_norm, hz]
  rw [hfac z hzball, norm_mul, hz]
  exact mul_le_mul_of_nonneg_left (hlow z hzclosed) hr

/-- **The composition disc with an explicit radius.**  The image of the large disc contains the ball
about `g c` of radius half the explicit displacement floor. -/
theorem ball_subset_image_explicit {g h : ℂ → ℂ} {c : ℂ} {R r M S : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcS : ‖c‖ + r ≤ S)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hhsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hhc : 0 < ‖h c‖) (hcM : ‖h c‖ < M)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c) :
    ball (g c) (r * (‖h c‖ * Real.exp (-(2 * Real.log (M / ‖h c‖) * r / (R - r)))) / 2)
      ⊆ g '' closedBall (0 : ℂ) S := by
  refine ball_subset_image_of_circle_floor_at hr hcS hgS ?_ hnc
  intro z hz
  exact displacement_floor_explicit (le_of_lt hr) hrR hhan hhne hhsup hhc hcM hfac z
    (by simpa [mem_sphere_iff_norm] using hz)

/-- **The composition disc, in terms of the derivative.**  The auxiliary factor is eliminated: the
image of the large disc contains the ball about `g c` of radius

  `(r/2) · ‖g' c‖ · (M / ‖g' c‖) ^ (-2r/(R-r))`,

where `M` bounds the difference quotient on the disc of radius `R` about `c`. -/
theorem ball_subset_image_of_deriv {g h : ℂ → ℂ} {c : ℂ} {R r M S : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcS : ‖c‖ + r ≤ S)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hhsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hhc : 0 < ‖h c‖) (hcM : ‖h c‖ < M)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c) :
    ball (g c)
        (r * (‖deriv g c‖ * Real.exp (-(2 * Real.log (M / ‖deriv g c‖) * r / (R - r)))) / 2)
      ⊆ g '' closedBall (0 : ℂ) S := by
  have hR0 : 0 < R := lt_trans hr hrR
  have hd : deriv g c = h c := deriv_eq_displacement_factor hR0 hhan hfac
  rw [hd]
  exact ball_subset_image_explicit hr hrR hcS hgS hhan hhne hhsup hhc hcM hfac hnc

/-- **The explicit composition transfer.**  A bound for `f ∘ g` on the large disc bounds `f` on the
whole disc of radius `ρ` about `g c`, for every `ρ` below the explicit disc radius. -/
theorem norm_le_of_explicit_disc {f g h : ℂ → ℂ} {c : ℂ} {R r M S ρ K : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcS : ‖c‖ + r ≤ S)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hhsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hhc : 0 < ‖h c‖) (hcM : ‖h c‖ < M)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c)
    (hρ : 0 < ρ)
    (hρlt : ρ < r * (‖h c‖ * Real.exp (-(2 * Real.log (M / ‖h c‖) * r / (R - r)))) / 2)
    (hf : AnalyticOnNhd ℂ f (closedBall (g c) ρ))
    (hK : ∀ z ∈ closedBall (0 : ℂ) S, ‖f (g z)‖ ≤ K) :
    ∀ w ∈ closedBall (g c) ρ, ‖f w‖ ≤ K := by
  have himg := ball_subset_image_explicit hr hrR hcS hgS hhan hhne hhsup hhc hcM hfac hnc
  refine norm_le_of_sphere_subset_image hρ hf ?_ hK
  refine subset_trans ?_ himg
  intro w hw
  have hdist : dist w (g c) = ρ := by
    simpa [mem_sphere_iff_norm, dist_eq_norm] using hw
  simp only [mem_ball, hdist]
  exact hρlt

/-- **Explicit composition growth.**  If the outer function exceeds `K` anywhere on the explicit
disc about `g c`, the composition exceeds `K` somewhere on the large disc. -/
theorem exists_norm_comp_gt_explicit {f g h : ℂ → ℂ} {c : ℂ} {R r M S ρ K : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcS : ‖c‖ + r ≤ S)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hhsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M)
    (hhc : 0 < ‖h c‖) (hcM : ‖h c‖ < M)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c)
    (hρ : 0 < ρ)
    (hρlt : ρ < r * (‖h c‖ * Real.exp (-(2 * Real.log (M / ‖h c‖) * r / (R - r)))) / 2)
    (hf : AnalyticOnNhd ℂ f (closedBall (g c) ρ))
    {w₀ : ℂ} (hw₀ : w₀ ∈ closedBall (g c) ρ) (hlarge : K < ‖f w₀‖) :
    ∃ z ∈ closedBall (0 : ℂ) S, K < ‖f (g z)‖ := by
  by_contra hcon
  have hall : ∀ z ∈ closedBall (0 : ℂ) S, ‖f (g z)‖ ≤ K := by
    intro z hz
    by_contra hc
    exact hcon ⟨z, hz, not_le.mp hc⟩
  exact absurd (norm_le_of_explicit_disc hr hrR hcS hgS hhan hhne hhsup hhc hcM hfac hnc hρ hρlt
    hf hall w₀ hw₀) (not_le.mpr hlarge)

/-! ## Feeding the explicit transfer from a logarithmic-derivative defect

The two quantities the explicit disc radius depends on are the derivative at the base point and the
local supremum of the difference quotient.  A bound on the logarithmic-derivative defect controls the
first; the maximum principle controls the second. -/

/-- **A logarithmic-derivative defect bounds the derivative below.**  If `‖z g'(z)/g(z) - ν‖ ≤ ε ν`
then `‖g' z‖ ≥ (1-ε) ν ‖g z‖ / ‖z‖`. -/
theorem norm_deriv_ge_of_defect {g : ℂ → ℂ} {z : ℂ} {ν ε : ℝ}
    (hz : z ≠ 0) (hg : g z ≠ 0) (hν : 0 ≤ ν)
    (hdef : ‖z * deriv g z / g z - (ν : ℂ)‖ ≤ ε * ν) :
    (1 - ε) * ν * ‖g z‖ / ‖z‖ ≤ ‖deriv g z‖ := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hg0 : 0 < ‖g z‖ := norm_pos_iff.mpr hg
  have hnorm : ‖z * deriv g z / g z‖ = ‖z‖ * ‖deriv g z‖ / ‖g z‖ := by
    rw [norm_div, norm_mul]
  have hnu : ‖(ν : ℂ)‖ = ν := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hν]
  have hlow : ν - ε * ν ≤ ‖z * deriv g z / g z‖ := by
    have h := norm_sub_norm_le ((ν : ℂ)) (z * deriv g z / g z)
    rw [hnu] at h
    have h' : ‖(ν : ℂ) - z * deriv g z / g z‖ = ‖z * deriv g z / g z - (ν : ℂ)‖ := by
      rw [norm_sub_rev]
    rw [h'] at h
    linarith [hdef, h]
  rw [hnorm] at hlow
  rw [div_le_iff₀ hz0]
  have hmul : (ν - ε * ν) * ‖g z‖ ≤ ‖z‖ * ‖deriv g z‖ := by
    rw [le_div_iff₀ hg0] at hlow
    linarith [hlow]
  nlinarith [hmul, hz0, hg0]

/-- **The maximum principle bounds the difference quotient.**  On the closed disc of radius `R'`
about `c`, the displacement factor is at most `(Mloc + ‖g c‖) / R'`, where `Mloc` bounds `g` on the
boundary circle. -/
theorem norm_displacement_factor_le {g h : ℂ → ℂ} {c : ℂ} {R' Mloc : ℝ} (hR' : 0 < R')
    (hhan : AnalyticOnNhd ℂ h (closedBall c R'))
    (hfac : ∀ z ∈ closedBall c R', g z - g c = (z - c) * h z)
    (hM : ∀ w : ℂ, ‖w - c‖ = R' → ‖g w‖ ≤ Mloc) :
    ∀ z ∈ closedBall c R', ‖h z‖ ≤ (Mloc + ‖g c‖) / R' := by
  refine norm_le_of_sphere_bound_centre hR' hhan ?_
  intro w hw
  have hwn : ‖w - c‖ = R' := by simpa [mem_sphere_iff_norm] using hw
  have hwmem : w ∈ closedBall c R' := by
    rw [mem_closedBall_iff_norm, hwn]
  have hval := hfac w hwmem
  have hnorm : ‖g w - g c‖ = R' * ‖h w‖ := by
    rw [hval, norm_mul, hwn]
  have hbound : ‖g w - g c‖ ≤ Mloc + ‖g c‖ := by
    calc ‖g w - g c‖ ≤ ‖g w‖ + ‖g c‖ := norm_sub_le _ _
      _ ≤ Mloc + ‖g c‖ := by linarith [hM w hwn]
  rw [le_div_iff₀ hR']
  rw [hnorm] at hbound
  linarith

/-- The anchor radius is monotone in the anchor. -/
theorem anchor_radius_mono {M x y r R : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hyM : y ≤ M)
    (hr : 0 ≤ r) (hrR : r < R) :
    x * Real.exp (-(2 * Real.log (M / x) * r / (R - r)))
      ≤ y * Real.exp (-(2 * Real.log (M / y) * r / (R - r))) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hM : 0 < M := lt_of_lt_of_le hy hyM
  have hk : 0 ≤ r / (R - r) := div_nonneg hr (by linarith)
  have hrewrite : ∀ t : ℝ, 0 < t →
      Real.exp (-(2 * Real.log (M / t) * r / (R - r)))
        = (t / M) ^ (2 * (r / (R - r))) := by
    intro t ht
    have hlog : Real.log (M / t) = -Real.log (t / M) := by
      rw [← Real.log_inv, inv_div]
    rw [hlog, Real.rpow_def_of_pos (div_pos ht hM)]
    congr 1
    field_simp
  have hxM : 0 < x / M := div_pos hx hM
  have hyM' : 0 < y / M := div_pos hy hM
  rw [hrewrite x hx, hrewrite y hy]
  have hbase : x / M ≤ y / M := by gcongr
  have hpow : (x / M) ^ (2 * (r / (R - r))) ≤ (y / M) ^ (2 * (r / (R - r))) :=
    Real.rpow_le_rpow (le_of_lt hxM) hbase (by linarith)
  have hpx : (0 : ℝ) ≤ (x / M) ^ (2 * (r / (R - r))) := Real.rpow_nonneg (le_of_lt hxM) _
  nlinarith [hpow, hpx, hxy, hx]

/-- **The composition disc from a logarithmic-derivative defect.**  The disc radius is explicit in
the defect data: with `D = (1-ε)·ν·‖g c‖/‖c‖` bounding the derivative below and `M` a strict bound
for the difference quotient, the image of the large disc contains the ball about `g c` of radius
`r · D · (M/D)^{-2r/(R-r)} / 2`. -/
theorem ball_subset_image_of_defect {g h : ℂ → ℂ} {c : ℂ} {R r S ν ε M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hcS : ‖c‖ + r ≤ S)
    (hgS : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) S))
    (hhan : AnalyticOnNhd ℂ h (ball c R))
    (hhne : ∀ z ∈ ball c R, h z ≠ 0)
    (hfac : ∀ z ∈ ball c R, g z - g c = (z - c) * h z)
    (hsupM : ∀ z ∈ ball c R, ‖h z‖ < M)
    (hc0 : c ≠ 0) (hgc : g c ≠ 0) (hν : 0 ≤ ν)
    (hdef : ‖c * deriv g c / g c - (ν : ℂ)‖ ≤ ε * ν)
    (hDpos : 0 < (1 - ε) * ν * ‖g c‖ / ‖c‖)
    (hnc : ¬ ∀ᶠ z in 𝓝 c, g z = g c) :
    ball (g c)
        (r * ((1 - ε) * ν * ‖g c‖ / ‖c‖
          * Real.exp (-(2 * Real.log (M / ((1 - ε) * ν * ‖g c‖ / ‖c‖)) * r / (R - r)))) / 2)
      ⊆ g '' closedBall (0 : ℂ) S := by
  have hR0 : 0 < R := lt_trans hr hrR
  have hcball : c ∈ ball c R := mem_ball_self hR0
  have hd : deriv g c = h c := deriv_eq_displacement_factor hR0 hhan hfac
  have hDlow : (1 - ε) * ν * ‖g c‖ / ‖c‖ ≤ ‖h c‖ := by
    rw [← hd]
    exact norm_deriv_ge_of_defect hc0 hgc hν hdef
  have hhc : 0 < ‖h c‖ := lt_of_lt_of_le hDpos hDlow
  have hcM : ‖h c‖ < M := hsupM c hcball
  have hsup : ∀ z ∈ ball c R, ‖h z‖ ≤ M := fun z hz => le_of_lt (hsupM z hz)
  have hbig := ball_subset_image_explicit hr hrR hcS hgS hhan hhne hsup hhc hcM hfac hnc
  refine subset_trans (Metric.ball_subset_ball ?_) hbig
  have hmono := anchor_radius_mono (M := M) (x := (1 - ε) * ν * ‖g c‖ / ‖c‖) (y := ‖h c‖)
    (r := r) (R := R) hDpos hDlow (le_of_lt hcM) (le_of_lt hr) hrR
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hstep : r * ((1 - ε) * ν * ‖g c‖ / ‖c‖
      * Real.exp (-(2 * Real.log (M / ((1 - ε) * ν * ‖g c‖ / ‖c‖)) * r / (R - r))))
      ≤ r * (‖h c‖ * Real.exp (-(2 * Real.log (M / ‖h c‖) * r / (R - r)))) :=
    mul_le_mul_of_nonneg_left hmono hr0
  linarith

end RHTower
