import GaloisForLFunctions.RHTower.XiExceptionalPointFoldLaw
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRouche
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount
import GaloisForLFunctions.RHTower.XiCosineShiftDefectDisks

/-!
# Persistence of defects of the cosine producer

The defect laws of `cos(hD)Ξ` proved so far are upper bounds: every non-real zero of the producer
lies in the defect disk of a zero of `ξ` deeper than `h`. This module gives the converse in the
quadratic regime: an off-line zero forces a defect pair as long as the rest of `Ξ` varies little
over the shift `±ih`.

**Theorem** (`cosineShift_exists_nonreal_zero_of_quadratic_factor`). Let `f = q·g` with `f, g`
entire and `q(z) = (z − γ)² + b²`, `b > 0`. Fix `0 ≤ h < b` and put `c = √(b² − h²)`,
`z₀ = γ − ci`. Suppose that on the circle `|z − z₀| = c/2` we have `g(z) ≠ 0` and
`|g(z ± ih) − g(z)| ≤ θ|g(z)|`, with `29θb² < 3(b² − h²)`. Then `(f(z + ih) + f(z − ih))/2` has a
zero `z` with `|z − z₀| < c/2`; in particular `Im z < −c/2` and `|Re z − γ| < c/2`.

**Proof.** `½(q(z + ih) + q(z − ih)) = (z − γ)² + c² = (z − z₀)(z − z̄₀)`, so
`A_h − g·(z − z₀)(z − z̄₀) = ½[q(z + ih)(g(z + ih) − g(z)) + q(z − ih)(g(z − ih) − g(z))]`. On the
circle `|q(z ± ih)| ≤ 29b²/4` and `|(z − z₀)(z − z̄₀)| ≥ 3c²/4`, so Rouché against the model
`g·(z − z₀)(z − z̄₀)`, which vanishes at `z₀`, gives a zero of `A_h` inside.

For `Ξ` (`cosProducer_exists_nonreal_zero_of_offline_zero`): if `Ξ(γ − ib) = 0`, i.e.
`ρ = ½ + b + iγ` is a zero of `ξ`, the quotient `g = Ξ/q` is entire (`xiPairQuotient`), and the
same conclusion holds for `cos(hD)Ξ`. So the depth-`h` producer keeps a defect pair near `γ` until
`h` comes within `O(θ)` of the offset `b`.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Rouché in existence form -/

/-- **Rouché, existence form.** If `‖G − F‖ < ‖F‖` on the circle `|z − c| = r` and `F` vanishes
inside, then so does `G`. -/
theorem exists_zero_mem_ball_of_norm_sub_lt {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hbd : ∀ z ∈ sphere c r, ‖G z - F z‖ < ‖F z‖) {z₀ : ℂ} (hz₀ : z₀ ∈ ball c r)
    (hF0 : F z₀ = 0) : ∃ z ∈ ball c r, G z = 0 := by
  by_contra hno
  push Not at hno
  obtain ⟨hFne, hGne⟩ := RiemannGaussian.ne_zero_on_sphere_of_norm_sub_lt hbd
  have heq := RiemannGaussian.circleIntegral_logDeriv_eq_of_norm_sub_lt hF hG hr.le hbd
  have hsub : closedBall c (r + 1) ⊆ (univ : Set ℂ) := subset_univ _
  obtain ⟨ZG, hZGb, hZGz, hZGs⟩ := exists_zeroSet_zeroSumBall (t := r) (R := r + 1) hr
    (by linarith) isOpen_univ hsub hG.differentiableOn hGne
  obtain ⟨ZF, hZFb, hZFz, hZFs⟩ := exists_zeroSet_zeroSumBall (t := r) (R := r + 1) hr
    (by linarith) isOpen_univ hsub hF.differentiableOn hFne
  have hZGe : ZG = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    exact hno ρ (hZGb ρ hρ) ((hZGz ρ (hZGb ρ hρ)).mpr hρ)
  have hz₀Z : z₀ ∈ ZF := (hZFz z₀ hz₀).mp hF0
  -- the zero of `F` has positive multiplicity
  have hFan : AnalyticOnNhd ℂ F univ := hF.differentiableOn.analyticOnNhd isOpen_univ
  have hmult : 1 ≤ zeroMult F z₀ := by
    have hne0 : analyticOrderAt F z₀ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hFan z₀ (mem_univ _), hF0⟩
    have hnetop : analyticOrderAt F z₀ ≠ ⊤ := by
      intro htop
      have hev : F =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.mp htop
      have hall := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ z₀) hev
      obtain ⟨w, hw⟩ : ∃ w, w ∈ sphere c r := ⟨c + r, by simp [abs_of_pos hr]⟩
      exact hFne w hw (hall (mem_univ w))
    unfold zeroMult
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hn, ENat.toNat_coe]
    rw [← hn] at hne0
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  have hsumF : 1 ≤ ∑ ρ ∈ ZF, zeroMult F ρ :=
    hmult.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hz₀Z)
  have hG0 : zeroSumBall G c r = 0 := by rw [hZGs, hZGe, Finset.sum_empty]
  have hFG : zeroSumBall G c r = zeroSumBall F c r := by
    unfold zeroSumBall; rw [heq]
  rw [hFG, hZFs] at hG0
  have : ∑ ρ ∈ ZF, zeroMult F ρ = 0 := by exact_mod_cast hG0
  omega

/-! ## The quadratic persistence law -/

/-- **Persistence of a defect pair.** -/
theorem cosineShift_exists_nonreal_zero_of_quadratic_factor {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {γ b h θ : ℝ} (hb : 0 < b) (hh : 0 ≤ h)
    (hhb : h < b) (hfac : ∀ z, f z = ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2),
      g z ≠ 0 ∧ ‖g (z + h * I) - g z‖ ≤ θ * ‖g z‖ ∧ ‖g (z - h * I) - g z‖ ≤ θ * ‖g z‖)
    (hθ : 29 * θ * b ^ 2 < 3 * (b ^ 2 - h ^ 2)) :
    ∃ z : ℂ, (f (z + h * I) + f (z - h * I)) / 2 = 0 ∧
      z.im < -(Real.sqrt (b ^ 2 - h ^ 2) / 2) ∧ |z.re - γ| < Real.sqrt (b ^ 2 - h ^ 2) / 2 := by
  set c : ℝ := Real.sqrt (b ^ 2 - h ^ 2) with hcdef
  have hbh : 0 < b ^ 2 - h ^ 2 := by nlinarith
  have hc : 0 < c := Real.sqrt_pos.mpr hbh
  have hc2 : c ^ 2 = b ^ 2 - h ^ 2 := Real.sq_sqrt hbh.le
  have hcb : c ≤ b := by nlinarith
  set z₀ : ℂ := (γ : ℂ) - (c : ℂ) * I with hz₀
  set F : ℂ → ℂ := fun z => g z * ((z - γ) ^ 2 + (c : ℂ) ^ 2) with hFdef
  set G : ℂ → ℂ := fun z => (f (z + h * I) + f (z - h * I)) / 2 with hGdef
  have hFd : Differentiable ℂ F := hg.mul (by fun_prop)
  have hGd : Differentiable ℂ G :=
    ((hf.comp (differentiable_id.add_const _)).add
      (hf.comp (differentiable_id.sub_const _))).div_const 2
  have hF0 : F z₀ = 0 := by
    simp only [hFdef, hz₀]
    have : ((γ : ℂ) - (c : ℂ) * I - γ) ^ 2 + (c : ℂ) ^ 2 = 0 := by
      ring_nf; rw [I_sq]; ring
    rw [this, mul_zero]
  -- the comparison identity
  have hid : ∀ z, G z - F z = ((((z + h * I) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z + h * I) - g z) +
      (((z - h * I) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z - h * I) - g z)) / 2 := by
    intro z
    simp only [hGdef, hFdef, hfac]
    have hc2' : (c : ℂ) ^ 2 = (b : ℂ) ^ 2 - (h : ℂ) ^ 2 := by exact_mod_cast hc2
    rw [hc2']
    ring_nf; rw [I_sq]; ring
  have hbound : ∀ z ∈ sphere z₀ (c / 2), ‖G z - F z‖ < ‖F z‖ := by
    intro z hz
    obtain ⟨hgz, hplus, hminus⟩ := hsph z hz
    have hgpos : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
    have hθ0 : 0 ≤ θ := by
      by_contra hneg
      push Not at hneg
      have := (norm_nonneg _).trans hplus
      nlinarith
    have hzz : ‖z - z₀‖ = c / 2 := by simpa using hz
    have hz0g : ‖z₀ - (γ : ℂ)‖ = c := by
      simp only [hz₀, sub_sub_cancel_left, norm_neg, norm_mul, norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hc]
    have hq : ∀ s : ℝ, |s| ≤ h → ‖((z + s * I) - γ) ^ 2 + (b : ℂ) ^ 2‖ ≤ 29 * b ^ 2 / 4 := by
      intro s hs
      have h1 : ‖(z + s * I) - γ‖ ≤ 5 * b / 2 := by
        have : (z + s * I) - γ = (z - z₀) + (z₀ - γ) + s * I := by ring
        rw [this]
        have hsI : ‖(s : ℂ) * I‖ = |s| := by simp
        calc ‖(z - z₀) + (z₀ - γ) + s * I‖ ≤ ‖z - z₀‖ + ‖z₀ - γ‖ + ‖(s : ℂ) * I‖ :=
              norm_add₃_le
          _ ≤ c / 2 + c + h := by rw [hzz, hz0g, hsI]; linarith
          _ ≤ 5 * b / 2 := by linarith
      calc ‖((z + s * I) - γ) ^ 2 + (b : ℂ) ^ 2‖ ≤ ‖(z + s * I) - γ‖ ^ 2 + ‖(b : ℂ) ^ 2‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_pow]
        _ ≤ (5 * b / 2) ^ 2 + b ^ 2 := by
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]
            gcongr
        _ = 29 * b ^ 2 / 4 := by ring
    have hqp := hq h (by rw [abs_of_nonneg hh])
    have hqm := hq (-h) (by rw [abs_neg, abs_of_nonneg hh])
    have hqm' : ‖((z - h * I) - γ) ^ 2 + (b : ℂ) ^ 2‖ ≤ 29 * b ^ 2 / 4 := by
      have e : (z + ((-h : ℝ) : ℂ) * I) = z - h * I := by push_cast; ring
      rw [e] at hqm; exact hqm
    have hGF : ‖G z - F z‖ ≤ θ * ‖g z‖ * (29 * b ^ 2 / 4) := by
      rw [hid z, norm_div, Complex.norm_ofNat]
      have ha := norm_add_le ((((z + h * I) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z + h * I) - g z))
        ((((z - h * I) - γ) ^ 2 + (b : ℂ) ^ 2) * (g (z - h * I) - g z))
      rw [norm_mul, norm_mul] at ha
      have hp : ‖((z + h * I) - γ) ^ 2 + (b : ℂ) ^ 2‖ * ‖g (z + h * I) - g z‖ ≤
          29 * b ^ 2 / 4 * (θ * ‖g z‖) :=
        mul_le_mul hqp hplus (norm_nonneg _) (by positivity)
      have hm : ‖((z - h * I) - γ) ^ 2 + (b : ℂ) ^ 2‖ * ‖g (z - h * I) - g z‖ ≤
          29 * b ^ 2 / 4 * (θ * ‖g z‖) :=
        mul_le_mul hqm' hminus (norm_nonneg _) (by positivity)
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hP : 3 * c ^ 2 / 4 ≤ ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := by
      have hfac2 : (z - γ) ^ 2 + (c : ℂ) ^ 2 = (z - z₀) * (z - ((γ : ℂ) + c * I)) := by
        simp only [hz₀]; ring_nf; rw [I_sq]; ring
      have hfar : 3 * c / 2 ≤ ‖z - ((γ : ℂ) + c * I)‖ := by
        have e : z - ((γ : ℂ) + c * I) = (z - z₀) - (2 * c : ℝ) * I := by
          simp only [hz₀]; push_cast; ring
        rw [e]
        have h2 : ‖((2 * c : ℝ) : ℂ) * I‖ = 2 * c := by
          rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
        have := norm_sub_norm_le (((2 * c : ℝ) : ℂ) * I) (z - z₀)
        rw [h2, hzz, norm_sub_rev] at this
        linarith
      rw [hfac2, norm_mul, hzz]
      nlinarith
    have hFz : ‖F z‖ = ‖g z‖ * ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := by
      simp only [hFdef, norm_mul]
    rw [hFz]
    calc ‖G z - F z‖ ≤ θ * ‖g z‖ * (29 * b ^ 2 / 4) := hGF
      _ = ‖g z‖ * (29 * θ * b ^ 2 / 4) := by ring
      _ < ‖g z‖ * (3 * c ^ 2 / 4) := by
          apply mul_lt_mul_of_pos_left _ hgpos
          rw [hc2]; linarith
      _ ≤ ‖g z‖ * ‖(z - γ) ^ 2 + (c : ℂ) ^ 2‖ := mul_le_mul_of_nonneg_left hP hgpos.le
  obtain ⟨z, hzball, hGz⟩ := exists_zero_mem_ball_of_norm_sub_lt hFd hGd (by linarith) hbound
    (mem_ball_self (by linarith)) hF0
  have hzb : ‖z - z₀‖ < c / 2 := by simpa [dist_eq_norm] using hzball
  refine ⟨z, hGz, ?_, ?_⟩
  · have him : |(z - z₀).im| ≤ ‖z - z₀‖ := abs_im_le_norm _
    have hz0im : z₀.im = -c := by simp [hz₀]
    have : (z - z₀).im = z.im + c := by rw [sub_im, hz0im]; ring
    rw [this] at him
    have := (abs_le.mp him).2
    linarith
  · have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := abs_re_le_norm _
    have hz0re : z₀.re = γ := by simp [hz₀]
    rw [sub_re, hz0re] at hre
    linarith

/-! ## The log-derivative form -/

/-- **Grönwall on a segment.** If `‖g'‖ ≤ M‖g‖` on a convex set containing `z` and `z + v`, then
`‖g(z + v) − g(z)‖ ≤ M‖v‖ e^{M‖v‖} ‖g(z)‖`. -/
theorem norm_sub_le_of_norm_deriv_le_mul {g : ℂ → ℂ} (hg : Differentiable ℂ g) {S : Set ℂ}
    (hS : Convex ℝ S) {M : ℝ} (hM : 0 ≤ M) (hder : ∀ w ∈ S, ‖deriv g w‖ ≤ M * ‖g w‖)
    {z v : ℂ} (hz : z ∈ S) (hzv : z + v ∈ S) :
    ‖g (z + v) - g z‖ ≤ M * ‖v‖ * Real.exp (M * ‖v‖) * ‖g z‖ := by
  set u : ℝ → ℂ := fun t => g (z + (t : ℂ) * v) with hu
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, z + (t : ℂ) * v ∈ S := by
    intro t ht
    have := hS.add_smul_mem hz hzv ht
    simpa [Complex.real_smul] using this
  have hderiv : ∀ t : ℝ, HasDerivAt u (deriv g (z + (t : ℂ) * v) * v) t := by
    intro t
    have hin : HasDerivAt (fun t : ℝ => z + (t : ℂ) * v) v t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const v).const_add z
    exact ((hg _).hasDerivAt).comp t hin
  have hK : 0 ≤ M * ‖v‖ := by positivity
  -- Grönwall
  have hgr : ∀ t ∈ Icc (0 : ℝ) 1, ‖u t‖ ≤ ‖g z‖ * Real.exp (M * ‖v‖ * t) := by
    intro t ht
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := u)
      (f' := fun t => deriv g (z + (t : ℂ) * v) * v) (δ := ‖g z‖) (K := M * ‖v‖) (ε := 0)
      (a := 0) (b := 1) (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ => (hderiv t).hasDerivWithinAt) (by simp [hu])
      (fun t ht => by
        rw [norm_mul, add_zero]
        have := hder _ (hmem t (Ico_subset_Icc_self ht))
        calc ‖deriv g (z + (t : ℂ) * v)‖ * ‖v‖ ≤ M * ‖g (z + (t : ℂ) * v)‖ * ‖v‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = M * ‖v‖ * ‖u t‖ := by simp only [hu]; ring) t ht
    rwa [gronwallBound_ε0, sub_zero] at this
  -- mean value on `[0, 1]`
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := u)
    (f' := fun t => deriv g (z + (t : ℂ) * v) * v)
    (C := M * ‖v‖ * Real.exp (M * ‖v‖) * ‖g z‖)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      rw [norm_mul]
      have h1 := hder _ (hmem t ht')
      have h2 := hgr t ht'
      have h3 : Real.exp (M * ‖v‖ * t) ≤ Real.exp (M * ‖v‖) := by
        apply Real.exp_le_exp.mpr
        nlinarith [ht'.2]
      calc ‖deriv g (z + (t : ℂ) * v)‖ * ‖v‖ ≤ M * ‖u t‖ * ‖v‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ M * (‖g z‖ * Real.exp (M * ‖v‖)) * ‖v‖ := by
            gcongr
            exact h2.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        _ = M * ‖v‖ * Real.exp (M * ‖v‖) * ‖g z‖ := by ring)
  simpa [hu] using hmv

/-- **Persistence, log-derivative form.** If `‖g'‖ ≤ M‖g‖` on the closed disk of radius
`c/2 + h` about `z₀ = γ − ci`, `g ≠ 0` on the circle `|z − z₀| = c/2`, and
`29 Mh e^{Mh} b² < 3(b² − h²)`, then `(f(z + ih) + f(z − ih))/2` has a zero `z` with
`Im z < −c/2` and `|Re z − γ| < c/2`. -/
theorem cosineShift_exists_nonreal_zero_of_logDeriv_bound {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) {γ b h M : ℝ} (hb : 0 < b) (hh : 0 ≤ h)
    (hhb : h < b) (hM : 0 ≤ M) (hfac : ∀ z, f z = ((z - γ) ^ 2 + (b : ℂ) ^ 2) * g z)
    (hder : ∀ w ∈ closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h), ‖deriv g w‖ ≤ M * ‖g w‖)
    (hne : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2), g z ≠ 0)
    (hθ : 29 * (M * h * Real.exp (M * h)) * b ^ 2 < 3 * (b ^ 2 - h ^ 2)) :
    ∃ z : ℂ, (f (z + h * I) + f (z - h * I)) / 2 = 0 ∧
      z.im < -(Real.sqrt (b ^ 2 - h ^ 2) / 2) ∧ |z.re - γ| < Real.sqrt (b ^ 2 - h ^ 2) / 2 := by
  refine cosineShift_exists_nonreal_zero_of_quadratic_factor hf hg hb hh hhb hfac
    (fun z hz => ⟨hne z hz, ?_, ?_⟩) hθ
  all_goals
    have hS := convex_closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
      (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h)
    have hzS : z ∈ closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h) := by
      rw [mem_closedBall]; rw [mem_sphere] at hz; linarith
    have hhI : ‖(h : ℂ) * I‖ = h := by
      rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh]
  · have hzv : z + (h : ℂ) * I ∈ closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h) := by
      rw [mem_closedBall, dist_eq_norm]; rw [mem_sphere, dist_eq_norm] at hz
      have : z + (h : ℂ) * I - ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I) =
          (z - ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)) + (h : ℂ) * I := by ring
      rw [this]
      exact (norm_add_le _ _).trans (by rw [hz, hhI])
    have := norm_sub_le_of_norm_deriv_le_mul hg hS hM hder hzS hzv
    rwa [hhI] at this
  · have hzv : z + (-(h : ℂ) * I) ∈ closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h) := by
      rw [mem_closedBall, dist_eq_norm]; rw [mem_sphere, dist_eq_norm] at hz
      have : z + (-(h : ℂ) * I) - ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I) =
          (z - ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)) + (-(h : ℂ) * I) := by ring
      rw [this]
      have hn : ‖-(h : ℂ) * I‖ = h := by rw [neg_mul, norm_neg, hhI]
      exact (norm_add_le _ _).trans (by rw [hz, hn])
    have := norm_sub_le_of_norm_deriv_le_mul hg hS hM hder hzS hzv
    have hn : ‖-(h : ℂ) * I‖ = h := by rw [neg_mul, norm_neg, hhI]
    rw [hn] at this
    have e : z + (-(h : ℂ) * I) = z - (h : ℂ) * I := by ring
    rwa [e] at this

/-! ## The persistence law for `Ξ` -/

/-- The quotient of `Ξ` by the quadratic factor of a conjugate pair of zeros `γ ∓ ib`. -/
def xiPairQuotient (γ b : ℝ) : ℂ → ℂ :=
  dslope (dslope XiC ((γ : ℂ) - b * I)) ((γ : ℂ) + b * I)

theorem differentiable_xiPairQuotient (γ b : ℝ) : Differentiable ℂ (xiPairQuotient γ b) := by
  have h1 : Differentiable ℂ (dslope XiC ((γ : ℂ) - b * I)) := by
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope univ_mem]
    exact differentiable_XiC.differentiableOn
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope univ_mem).mpr h1.differentiableOn

/-- If `Ξ(γ − ib) = 0`, then `Ξ(z) = ((z − γ)² + b²)·xiPairQuotient γ b z`. -/
theorem XiC_eq_quadratic_mul_xiPairQuotient {γ b : ℝ} (hb : 0 < b)
    (hz : XiC ((γ : ℂ) - b * I) = 0) (z : ℂ) :
    XiC z = ((z - γ) ^ 2 + (b : ℂ) ^ 2) * xiPairQuotient γ b z := by
  set a : ℂ := (γ : ℂ) - b * I with ha
  set a' : ℂ := (γ : ℂ) + b * I with ha'
  have hconj : a' = (starRingEnd ℂ) a := by
    simp only [ha, ha', map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I]; ring
  have hz' : XiC a' = 0 := by rw [hconj, XiC_conj', hz, map_zero]
  have hne : a' ≠ a := by
    intro h
    have := congrArg Complex.im h
    simp only [ha, ha', add_im, sub_im, Complex.ofReal_im, mul_im, Complex.ofReal_re, I_im,
      I_re, mul_one, mul_zero, add_zero, zero_add, zero_sub] at this
    linarith
  have hd : dslope XiC a a' = 0 := by
    rw [dslope_of_ne _ hne, slope, hz', hz, vsub_self, smul_zero]
  have e1 := sub_smul_dslope_of_zero hz z
  have e2 := sub_smul_dslope_of_zero hd z
  rw [smul_eq_mul] at e1 e2
  rw [← e1, ← e2]
  unfold xiPairQuotient
  rw [← ha, ← ha']
  have hq : (z - a) * (z - a') = (z - γ) ^ 2 + (b : ℂ) ^ 2 := by
    simp only [ha, ha']; ring_nf; rw [I_sq]; ring
  rw [← hq]; ring

/-- **Persistence of defects for `Ξ`.** If `ρ = ½ + b + iγ` is a zero of `ξ` (`Ξ(γ − ib) = 0`)
and the quotient `g = Ξ/((z − γ)² + b²)` moves by at most `θ|g(z)|` under the shifts `±ih` on the
circle `|z − z₀| = c/2`, `z₀ = γ − ci`, `c = √(b² − h²)`, with `29θb² < 3(b² − h²)`, then
`cos(hD)Ξ` has a non-real zero `z` with `Im z < −c/2` and `|Re z − γ| < c/2`. -/
theorem cosProducer_exists_nonreal_zero_of_offline_zero {γ b h θ : ℝ} (hb : 0 < b) (hh : 0 ≤ h)
    (hhb : h < b) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hsph : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2),
      xiPairQuotient γ b z ≠ 0 ∧
        ‖xiPairQuotient γ b (z + h * I) - xiPairQuotient γ b z‖ ≤ θ * ‖xiPairQuotient γ b z‖ ∧
        ‖xiPairQuotient γ b (z - h * I) - xiPairQuotient γ b z‖ ≤ θ * ‖xiPairQuotient γ b z‖)
    (hθ : 29 * θ * b ^ 2 < 3 * (b ^ 2 - h ^ 2)) :
    ∃ z : ℂ, cosProducer h z = 0 ∧
      z.im < -(Real.sqrt (b ^ 2 - h ^ 2) / 2) ∧ |z.re - γ| < Real.sqrt (b ^ 2 - h ^ 2) / 2 :=
  cosineShift_exists_nonreal_zero_of_quadratic_factor differentiable_XiC
    (differentiable_xiPairQuotient γ b) hb hh hhb (XiC_eq_quadratic_mul_xiPairQuotient hb hz)
    hsph hθ

/-- **Persistence of defects for `Ξ`, log-derivative form.** If `ρ = ½ + b + iγ` is a zero of `ξ`,
the quotient `g = Ξ/((z − γ)² + b²)` satisfies `‖g'‖ ≤ M‖g‖` on the disk of radius `c/2 + h`
about `γ − ci` and does not vanish on the circle of radius `c/2`, and
`29 Mh e^{Mh} b² < 3(b² − h²)`, then `cos(hD)Ξ` has a non-real zero within `c/2` of `γ − ci`. -/
theorem cosProducer_exists_nonreal_zero_of_logDeriv_bound {γ b h M : ℝ} (hb : 0 < b)
    (hh : 0 ≤ h) (hhb : h < b) (hM : 0 ≤ M) (hz : XiC ((γ : ℂ) - b * I) = 0)
    (hder : ∀ w ∈ closedBall ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2 + h),
      ‖deriv (xiPairQuotient γ b) w‖ ≤ M * ‖xiPairQuotient γ b w‖)
    (hne : ∀ z ∈ sphere ((γ : ℂ) - (Real.sqrt (b ^ 2 - h ^ 2) : ℂ) * I)
        (Real.sqrt (b ^ 2 - h ^ 2) / 2), xiPairQuotient γ b z ≠ 0)
    (hθ : 29 * (M * h * Real.exp (M * h)) * b ^ 2 < 3 * (b ^ 2 - h ^ 2)) :
    ∃ z : ℂ, cosProducer h z = 0 ∧
      z.im < -(Real.sqrt (b ^ 2 - h ^ 2) / 2) ∧ |z.re - γ| < Real.sqrt (b ^ 2 - h ^ 2) / 2 :=
  cosineShift_exists_nonreal_zero_of_logDeriv_bound differentiable_XiC
    (differentiable_xiPairQuotient γ b) hb hh hhb hM (XiC_eq_quadratic_mul_xiPairQuotient hb hz)
    hder hne hθ

end

end RHTower
