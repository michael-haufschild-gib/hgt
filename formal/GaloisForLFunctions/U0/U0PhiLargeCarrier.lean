/-
# The far carrier at every sharp parameter, and the exterior Julia geometry

Sharp-threshold parameterization of the far carrier: the annulus becomes the b-dependent
`annWB b = {1 < ‖z‖ < rB b}`, and the far-field entry runs on the monotone-escape comparison
(`U0MonotoneEscape`) instead of a geometric rate — one quadratic step from the annulus clears
the escape fixed point (`‖b‖ − rB² > xStar ‖b‖`, exactly the sharp clearance), and above the
fixed point the real comparison orbit `t ↦ t² − ‖b‖` grows linearly and exceeds every bound.
This is what reaches arbitrarily close to `‖b‖ = 2+√2`, where the escape rate degenerates.

Kept verbatim from the `‖b‖ ≥ 4` pass (tower-lane geometry, thresholds unchanged):

* `zero_not_mem_filledJulia_large` — every `‖b‖ > 2` is an escape parameter;
* `filledJulia_exterior` — for `‖b‖ ≥ 4` the WHOLE filled Julia set lies outside the closed unit
  disk.  (Below `2+√2` this must fail at some parameters — `U0WindowObstruction`; between, the
  dichotomy is directional — `U0DichotomyWitness`.)
-/
import GaloisForLFunctions.U0.U0PhiLargeWindow
import GaloisForLFunctions.U0.U0PhiFourFarCarrier
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Complex Set Metric Polynomial Bottcher U0NaturalBoundary U0MonotoneEscape
open U0PhiLargeWindow U0PhiFourFarCarrier

namespace U0PhiLargeCarrier

/-- **Every `‖b‖ > 2` is an escape parameter**: `b = f_b(0)` itself already satisfies the
geometric escape criterion. -/
theorem zero_not_mem_filledJulia_large {b : ℂ} (hb : 2 < ‖b‖) : (0 : ℂ) ∉ filledJulia b := by
  intro h0
  have h1 : (quadratic b)^[1] (0 : ℂ) ∈ filledJulia b := filledJulia_forward h0 1
  have hval : (quadratic b)^[1] (0 : ℂ) = b := by
    rw [Function.iterate_one]
    show (0 : ℂ) ^ (2 : ℕ) + b = b
    ring
  rw [hval] at h1
  exact not_mem_filledJulia (le_refl ‖b‖) hb h1

/-- **The filled Julia set of a large parameter avoids the closed unit disk.**  For `‖b‖ ≥ 4` and
`‖z‖ ≤ 1`: `‖f(z)‖ ≥ ‖b‖ − 1`, so `‖f²(z)‖ ≥ (‖b‖−1)² − ‖b‖ ≥ ‖b‖ > 2` and the orbit escapes.
Hence every point of `K_b` has modulus `> 1` — the entire tower geometry at large `‖b‖` lives
inside `u₀`'s domain `{|z| > 1}`. -/
theorem filledJulia_exterior {b : ℂ} (hb : 4 ≤ ‖b‖) {z : ℂ} (hz : z ∈ filledJulia b) :
    1 < ‖z‖ := by
  by_contra hle
  push Not at hle
  have hfz : ‖b‖ - 1 ≤ ‖quadratic b z‖ := by
    have htri : ‖b‖ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := by
      calc ‖b‖ = ‖z ^ (2 : ℕ) + b - z ^ (2 : ℕ)‖ := by ring_nf
        _ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := norm_sub_le _ _
    have hp : ‖z ^ (2 : ℕ)‖ = ‖z‖ ^ (2 : ℕ) := norm_pow z 2
    show ‖b‖ - 1 ≤ ‖z ^ (2 : ℕ) + b‖
    nlinarith [htri, hle, norm_nonneg z]
  have hffz : ‖b‖ ≤ ‖quadratic b (quadratic b z)‖ ∧ 2 < ‖quadratic b (quadratic b z)‖ := by
    have htri : ‖(quadratic b z) ^ (2 : ℕ)‖ ≤ ‖(quadratic b z) ^ (2 : ℕ) + b‖ + ‖b‖ :=
      norm_le_add_norm_add _ _
    have hp : ‖(quadratic b z) ^ (2 : ℕ)‖ = ‖quadratic b z‖ ^ (2 : ℕ) := norm_pow _ 2
    have hgoal : ‖b‖ ≤ ‖(quadratic b z) ^ (2 : ℕ) + b‖ := by
      nlinarith [htri, hfz, hb]
    exact ⟨hgoal, by show (2 : ℝ) < ‖(quadratic b z) ^ (2 : ℕ) + b‖; nlinarith [hgoal, hb]⟩
  have h2 : (quadratic b)^[2] z ∈ filledJulia b := filledJulia_forward hz 2
  have hval : (quadratic b)^[2] z = quadratic b (quadratic b z) := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [hval] at h2
  exact not_mem_filledJulia hffz.1 hffz.2 h2

/-! ## The b-dependent window annulus -/

/-- **The sharp window annulus** `{1 < ‖z‖ < rB b}` — b-dependent, nonempty exactly above the
sharp threshold where `rB b > 1`. -/
noncomputable def annWB (b : ℂ) : Set ℂ := ball (0 : ℂ) (rB b) ∩ Ext

theorem annWB_subset_ball {b : ℂ} : annWB b ⊆ ball (0 : ℂ) (rB b) := inter_subset_left

theorem annWB_subset_Ext {b : ℂ} : annWB b ⊆ Ext := inter_subset_right

theorem isOpen_annWB (b : ℂ) : IsOpen (annWB b) :=
  isOpen_ball.inter U0NaturalBoundary.isOpen_Ext

theorem isPreconnected_annWB {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    IsPreconnected (annWB b) :=
  isPreconnected_annulus_of_one_lt (one_lt_rB hb)

theorem annWB_nonempty {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) : (annWB b).Nonempty := by
  have hr := one_lt_rB hb
  refine ⟨(((1 + rB b) / 2 : ℝ) : ℂ), ?_, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · show 1 < ‖(((1 + rB b) / 2 : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith

theorem annWB_infinite {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) : (annWB b).Infinite :=
  infinite_of_isOpen_nonempty (isOpen_annWB b) (annWB_nonempty hb)

/-! ## The parameterized escape map and its far image -/

/-- The escape map at parameter `b`: one step into the far field, then `m` more. -/
noncomputable def pMapB (b : ℂ) (m : ℕ) : ℂ → ℂ := fun z => (quadratic b)^[m] (quadratic b z)

/-! ### The polynomial witness for `pMapB` -/

noncomputable def pPolyB (b : ℂ) (m : ℕ) : Polynomial ℂ :=
  (quadraticPolyIterate b m).comp (quadraticPoly b)

theorem pPolyB_eval (b : ℂ) (m : ℕ) (z : ℂ) : (pPolyB b m).eval z = pMapB b m z := by
  rw [pPolyB, eval_comp, quadraticPolyIterate_eval]
  show (quadratic b)^[m] ((quadraticPoly b).eval z) = pMapB b m z
  have h : (quadraticPoly b).eval z = quadratic b z := by
    rw [quadraticPoly]
    simp [quadratic_apply]
  rw [h]
  rfl

theorem quadraticPoly_monic_B (b : ℂ) : (quadraticPoly b).Monic := by
  rw [quadraticPoly]
  monicity!

theorem quadraticPolyIterate_monic_B (b : ℂ) (m : ℕ) : (quadraticPolyIterate b m).Monic := by
  induction m with
  | zero =>
    show (X : Polynomial ℂ).Monic
    exact monic_X
  | succ m ih =>
    show ((quadraticPoly b).comp (quadraticPolyIterate b m)).Monic
    refine Monic.comp (quadraticPoly_monic_B b) ih ?_
    rw [quadraticPolyIterate_natDegree]
    exact pow_ne_zero m two_ne_zero

theorem pPolyB_monic (b : ℂ) (m : ℕ) : (pPolyB b m).Monic := by
  refine Monic.comp (quadraticPolyIterate_monic_B b m) (quadraticPoly_monic_B b) ?_
  rw [quadraticPoly_natDegree]
  norm_num

theorem pPolyB_natDegree (b : ℂ) (m : ℕ) : (pPolyB b m).natDegree = 2 ^ (m + 1) := by
  rw [pPolyB, natDegree_comp, quadraticPolyIterate_natDegree, quadraticPoly_natDegree, pow_succ]

theorem pPolyB_natDegree_ne_zero (b : ℂ) (m : ℕ) : (pPolyB b m).natDegree ≠ 0 := by
  rw [pPolyB_natDegree]
  exact pow_ne_zero _ two_ne_zero

theorem pMapB_mem_farB {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) {z : ℂ}
    (hz : z ∈ annWB b) : pMapB b m z ∈ farB b :=
  farB_iterate (norm_gt_two hb) m (quadB_mem_farB hb (annWB_subset_ball hz))

/-- The dyadic pullback chain lands on `pMapB` on the whole sharp disk. -/
theorem phiB_pow_pMapB_of_mem_ball {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) (rB b)) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b (pMapB b m z) :=
  phiB_pow_iterate hb hz m

/-- The dyadic pullback identity with disk membership carried by the point subtype. -/
theorem phiB_pow_pMapB_on_ball {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ)
    (z : ball (0 : ℂ) (rB b)) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b (pMapB b m z) :=
  phiB_pow_pMapB_of_mem_ball hb m z.property

/-- The dyadic pullback identity with both sharpness and disk membership carried by subtypes. -/
theorem phiB_pow_pMapB_on_sharpBall (b : {b : ℂ // 2 + Real.sqrt 2 < ‖b‖}) (m : ℕ)
    (z : ball (0 : ℂ) (rB (b : ℂ))) :
    phiB (b : ℂ) z ^ (2 ^ (m + 1)) = bottcherCoord (b : ℂ) (pMapB (b : ℂ) m z) :=
  phiB_pow_pMapB_of_mem_ball b.property m z.property

/-- The dyadic pullback chain lands on `pMapB`, with the sharp parameter regime and annulus
membership carried by the parameter types. -/
theorem phiB_pow_pMapB (b : {b : ℂ // 2 + Real.sqrt 2 < ‖b‖}) (m : ℕ)
    (z : annWB (b : ℂ)) :
    phiB (b : ℂ) z ^ (2 ^ (m + 1)) = bottcherCoord (b : ℂ) (pMapB (b : ℂ) m z) :=
  phiB_pow_pMapB_of_mem_ball b.property m (annWB_subset_ball z.property)

/-- The dyadic pullback identity with annulus membership carried by the point subtype. -/
theorem phiB_pow_pMapB_on_annWB {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ)
    (z : annWB b) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b (pMapB b m z) :=
  phiB_pow_pMapB ⟨b, hb⟩ m z

/-- The dyadic pullback identity from explicit sharpness and annulus-membership facts. -/
theorem phiB_pow_pMapB_of_mem_annWB {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ)
    {z : ℂ} (hz : z ∈ annWB b) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b (pMapB b m z) :=
  phiB_pow_pMapB ⟨b, hb⟩ m ⟨z, hz⟩

theorem quadratic_analyticOnNhd_univ_B (b : ℂ) : AnalyticOnNhd ℂ (quadratic b) univ := by
  have h : AnalyticOnNhd ℂ (fun z : ℂ => z ^ (2 : ℕ) + b) univ :=
    (analyticOnNhd_id.pow 2).add analyticOnNhd_const
  have he : (quadratic b) = fun z : ℂ => z ^ (2 : ℕ) + b := by
    funext z; exact quadratic_apply b z
  rw [he]
  exact h

theorem pMapB_analyticOnNhd (b : ℂ) (m : ℕ) : AnalyticOnNhd ℂ (pMapB b m) univ := by
  induction m with
  | zero =>
    have he : pMapB b 0 = quadratic b := by
      funext z; simp [pMapB]
    rw [he]
    exact quadratic_analyticOnNhd_univ_B b
  | succ m ih =>
    have he : pMapB b (m + 1) = (quadratic b) ∘ (pMapB b m) := by
      funext z
      simp only [pMapB, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact (quadratic_analyticOnNhd_univ_B b).comp ih (mapsTo_univ _ _)

/-- The chain-rule derivative of `pMapB` is nonzero on the annulus. -/
theorem pMapB_hasDerivAt_ne_zero {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) {z : ℂ}
    (hz : z ∈ annWB b) :
    ∃ d : ℂ, HasDerivAt (pMapB b m) d z ∧ d ≠ 0 := by
  have hz0 : z ≠ 0 := by
    intro h0
    have h1 : (1 : ℝ) < ‖z‖ := annWB_subset_Ext hz
    rw [h0] at h1
    simp at h1
    linarith
  have hq : HasDerivAt (quadratic b) (2 * z) z := by
    have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + b) ((2 : ℕ) * z ^ (2 - 1)) z :=
      (hasDerivAt_pow 2 z).add_const b
    have he : (quadratic b) = fun w : ℂ => w ^ (2 : ℕ) + b := by
      funext w; exact quadratic_apply b w
    rw [he]
    convert h using 1
    push_cast
    ring
  induction m with
  | zero =>
    refine ⟨2 * z, ?_, by
      intro h
      rcases mul_eq_zero.mp h with h2 | h2
      · norm_num at h2
      · exact hz0 h2⟩
    have he : pMapB b 0 = quadratic b := by
      funext w; simp [pMapB]
    rw [he]
    exact hq
  | succ m ih =>
    obtain ⟨d, hd, hdne⟩ := ih
    have hfar : pMapB b m z ∈ farB b := pMapB_mem_farB hb m hz
    have hne : pMapB b m z ≠ 0 := farB_ne_zero (norm_gt_two hb) hfar
    have hqm : HasDerivAt (quadratic b) (2 * pMapB b m z) (pMapB b m z) := by
      have h : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + b) ((2 : ℕ) * (pMapB b m z) ^ (2 - 1))
          (pMapB b m z) := (hasDerivAt_pow 2 (pMapB b m z)).add_const b
      have he : (quadratic b) = fun w : ℂ => w ^ (2 : ℕ) + b := by
        funext w; exact quadratic_apply b w
      rw [he]
      convert h using 1
      push_cast
      ring
    refine ⟨2 * pMapB b m z * d, ?_, by
      intro h
      rcases mul_eq_zero.mp h with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact hne h3
      · exact hdne h2⟩
    have he : pMapB b (m + 1) = (quadratic b) ∘ (pMapB b m) := by
      funext w
      simp only [pMapB, Function.comp_apply]
      rw [Function.iterate_succ_apply']
    rw [he]
    exact hqm.comp z hd

theorem pMapB_deriv_ne_zero {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) {z : ℂ}
    (hz : z ∈ annWB b) :
    deriv (pMapB b m) z ≠ 0 := by
  obtain ⟨d, hd, hdne⟩ := pMapB_hasDerivAt_ne_zero hb m hz
  rw [hd.deriv]
  exact hdne

/-- **The far image of the sharp carrier is open, with no sharpness hypothesis.**
This is purely polynomial: `pMapB b m` is evaluation of the positive-degree polynomial `pPolyB b m`,
so the open mapping theorem applies on every `annWB b`.  Sharpness is still needed elsewhere for
nonemptiness and far-entry facts, but not for openness. -/
theorem isOpen_pMapB_image {b : ℂ} (m : ℕ) : IsOpen (pMapB b m '' annWB b) := by
  have hfun : pMapB b m = fun z => Polynomial.eval z (pPolyB b m) := by
    funext z
    exact (pPolyB_eval b m z).symm
  rw [hfun]
  exact (Polynomial.isOpenQuotientMap_eval (pPolyB b m) (pPolyB_natDegree_ne_zero b m)).isOpenMap
    _ (isOpen_annWB b)

theorem isPreconnected_pMapB_image {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) :
    IsPreconnected (pMapB b m '' annWB b) :=
  (isPreconnected_annWB hb).image _
    (((pMapB_analyticOnNhd b m).continuousOn).mono (subset_univ _))

theorem pMapB_image_nonempty {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) :
    (pMapB b m '' annWB b).Nonempty :=
  Set.Nonempty.image _ (annWB_nonempty hb)

theorem pMapB_image_infinite {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (m : ℕ) :
    (pMapB b m '' annWB b).Infinite :=
  infinite_of_isOpen_nonempty (isOpen_pMapB_image m) (pMapB_image_nonempty hb m)

/-! ## The far-field entry by monotone escape -/

/-- **Norm comparison with the real escape dynamics**: the orbit norm dominates the iterates of
`t ↦ t² − ‖b‖` from any starting level above the fixed point. -/
theorem iterate_norm_ge {b : ℂ} (hb : 2 < ‖b‖) {s : ℝ} (hs : xStar ‖b‖ ≤ s)
    {w : ℂ} (hw : s ≤ ‖w‖) (m : ℕ) :
    (fun t => t ^ (2 : ℕ) - ‖b‖)^[m] s ≤ ‖(quadratic b)^[m] w‖ := by
  induction m generalizing s w with
  | zero => simpa using hw
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hxs0 : (0 : ℝ) ≤ xStar ‖b‖ :=
      le_of_lt (lt_trans one_pos (one_lt_xStar (by linarith)))
    have hgs : xStar ‖b‖ ≤ s ^ (2 : ℕ) - ‖b‖ := by
      have := step_ge (show (0:ℝ) < ‖b‖ by linarith) hs
      linarith
    have hstep : s ^ (2 : ℕ) - ‖b‖ ≤ ‖quadratic b w‖ := by
      have htri : ‖w ^ (2 : ℕ)‖ ≤ ‖w ^ (2 : ℕ) + b‖ + ‖b‖ := norm_le_add_norm_add _ _
      have hp : ‖w ^ (2 : ℕ)‖ = ‖w‖ ^ (2 : ℕ) := norm_pow w 2
      show s ^ (2 : ℕ) - ‖b‖ ≤ ‖w ^ (2 : ℕ) + b‖
      nlinarith [htri, hw, hs, hxs0,
        mul_nonneg (sub_nonneg.mpr hw) (show (0:ℝ) ≤ ‖w‖ + s by linarith)]
    exact ih hgs hstep

/-- **The far carrier exists at every sharp parameter**: for `m` large the image clears the
Böttcher far bound of `b`.  The entry is by monotone escape — one step from the annulus clears
the fixed point (`‖b‖ − rB² > xStar`), then the linear growth of the comparison orbit exceeds
the (abstract) far bound.  No rate constant appears; this is what works arbitrarily close to
the sharp threshold. -/
theorem exists_far_carrier_B {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    ∃ m : ℕ, ∀ w ∈ pMapB b m '' annWB b,
      bottcherFarBound b (zero_not_mem_filledJulia_large (norm_gt_two hb)) < ‖w‖ := by
  set M : ℝ := bottcherFarBound b (zero_not_mem_filledJulia_large (norm_gt_two hb)) with hM
  have hb2 : 2 < ‖b‖ := norm_gt_two hb
  have hb0 : (0 : ℝ) < ‖b‖ := by linarith
  have hcl := xStar_lt_of_sharp hb
  set s₀ : ℝ := ‖b‖ - rB b ^ (2 : ℕ) with hs₀
  have hs₀gt : xStar ‖b‖ < s₀ := by
    have hrsq := rB_sq_le hb
    rw [hs₀]
    linarith
  obtain ⟨m, hm⟩ := exists_iterate_gt hb0 hs₀gt M
  refine ⟨m, ?_⟩
  rintro w ⟨z, hz, rfl⟩
  have hz' : ‖z‖ < rB b := by
    have := annWB_subset_ball hz
    simpa [mem_ball, dist_zero_right] using this
  have hfirst : s₀ ≤ ‖quadratic b z‖ := by
    have htri : ‖b‖ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := by
      calc ‖b‖ = ‖z ^ (2 : ℕ) + b - z ^ (2 : ℕ)‖ := by ring_nf
        _ ≤ ‖z ^ (2 : ℕ) + b‖ + ‖z ^ (2 : ℕ)‖ := norm_sub_le _ _
    have hp : ‖z ^ (2 : ℕ)‖ = ‖z‖ ^ (2 : ℕ) := norm_pow z 2
    have hzr : ‖z‖ ^ (2 : ℕ) ≤ rB b ^ (2 : ℕ) := by
      nlinarith [hz', norm_nonneg z, one_lt_rB hb]
    show s₀ ≤ ‖z ^ (2 : ℕ) + b‖
    rw [hs₀]
    nlinarith [htri, hzr]
  have hcomp := iterate_norm_ge hb2 hs₀gt.le hfirst m
  calc M < (fun t => t ^ (2 : ℕ) - ‖b‖)^[m] s₀ := hm
    _ ≤ ‖(quadratic b)^[m] (quadratic b z)‖ := hcomp
    _ = ‖pMapB b m z‖ := rfl

end U0PhiLargeCarrier
