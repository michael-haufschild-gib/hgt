import GaloisForLFunctions.RHTower.WeilProducerZetaQuotientBohrRecurrence

/-!
# An unavoidable reciprocal obstruction below the pole

The literal reciprocal of every full-positive system is unbounded on each
half-plane `Re s > x` with `1/2 < x < 1`. Its unique zero at `1` cannot recur,
whereas a bounded Dirichlet continuation would make that zero recur.
This does not obstruct the required bounded zeta quotient: zeta cancels this zero.
-/

open Complex Filter Topology Set Metric

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem not_bounded_of_unique_zero_one {b : ℕ → ℂ} {G : ℂ → ℂ} {x : ℝ}
    (hx : 1 / 2 < x) (hx1 : x < 1)
    (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hsum : LSeriesSummable b (2 : ℂ))
    (hGL : ∀ s : ℂ, 2 < s.re → G s = LSeries b s)
    (hzero : ∀ s : ℂ, 1 / 2 < s.re → (G s = 0 ↔ s = 1)) :
    ¬ ∃ M : ℝ, ∀ s : ℂ, x < s.re → ‖G s‖ ≤ M := by
  rintro ⟨M, hM⟩
  let r : ℝ := (1 - x) / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hxr : x < 1 - r := by dsimp [r]; linarith
  have hG1 : G 1 = 0 := (hzero 1 (by norm_num)).mpr rfl
  have hdisk : ∀ z ∈ closedBall (1 : ℂ) r, x < z.re := by
    intro z hz
    have h := abs_le.mp ((abs_re_le_norm (z - 1)).trans (mem_closedBall_iff_norm.mp hz))
    simp only [sub_re, one_re] at h
    linarith [h.1]
  have hGdx : DifferentiableOn ℂ G {s : ℂ | x < s.re} :=
    hGd.mono fun _ hs => hx.trans hs
  have hsphere : ∀ z ∈ sphere (1 : ℂ) r, G z ≠ 0 := by
    intro z hz h0
    have hz1 := (hzero z (hx.trans (hdisk z (sphere_subset_closedBall hz)))).mp h0
    have hd := mem_sphere.mp hz
    rw [hz1, dist_self] at hd
    linarith
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (1 : ℂ) r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le)
    (hGdx.continuousOn.mono fun z hz => hdisk z (sphere_subset_closedBall hz)).norm
  let m : ℝ := ‖G z₀‖
  have hm : 0 < m := norm_pos_iff.mpr (hsphere z₀ hz₀)
  have hfloor : ∀ z ∈ sphere (1 : ℂ) r, m ≤ ‖G z‖ := fun z hz => isMinOn_iff.mp hmin z hz
  have hap := GaloisForLFunctions.isStripAlmostPeriodicOn_of_bounded_LSeries
    (l' := 1 - r) (u := 3) (u₀ := 2) hxr (by linarith) (by norm_num)
    hsum hGdx hM hGL (m / 3) (by positivity)
  obtain ⟨L, -, hperiod⟩ := hap
  obtain ⟨τ, hτ, hnear⟩ := hperiod 2
  have hstrip : ∀ z ∈ closedBall (1 : ℂ) r,
      |z.re - ((1 - r) + 3) / 2| ≤ (3 - (1 - r)) / 2 := by
    intro z hz
    have h := abs_le.mp ((abs_re_le_norm (z - 1)).trans (mem_closedBall_iff_norm.mp hz))
    simp only [sub_re, one_re] at h
    exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  have hU : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hshift : DifferentiableOn ℂ (fun z => G (z + τ * I)) (closedBall (1 : ℂ) r) := by
    intro z hz
    have hz' : x < (z + τ * I).re := by simpa using hdisk z hz
    exact (((hGdx _ hz').differentiableAt (hU.mem_nhds hz')).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  obtain ⟨z, hz, hz0⟩ := DeBruijn.exists_zero_of_norm_lt_sphere_on hr hshift fun z hz => by
    have h1 := hnear 1 (hstrip 1 (mem_closedBall_self hr.le))
    rw [hG1, sub_zero] at h1
    have h2 := hnear z (hstrip z (sphere_subset_closedBall hz))
    have h3 := hfloor z hz
    have h4 := norm_sub_norm_le (G z) (G (z + τ * I))
    rw [norm_sub_rev] at h4
    show ‖G (1 + τ * I)‖ < ‖G (z + τ * I)‖
    linarith
  have hzH : 1 / 2 < (z + τ * I).re := by
    have := hx.trans (hdisk z (ball_subset_closedBall hz))
    simpa using this
  have heq := (hzero _ hzH).mp hz0
  have him : z.im + τ = 0 := by
    have := congrArg Complex.im heq
    simpa using this
  have himlt : |z.im| < r := by
    have hn := mem_ball_iff_norm.mp hz
    have hi := abs_im_le_norm (z - 1)
    simp only [sub_im, one_im, sub_zero] at hi
    exact hi.trans_lt hn
  have := (abs_lt.mp himlt).1
  linarith [hτ.1]

/-- Every full-positive system has the literal reciprocal, and that reciprocal
is unbounded on every strict half-plane crossing the point `1`. No additional
coefficient or analytic premise is supplied. -/
theorem exists_reciprocal_unbounded_below_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ x : ℝ, 1 / 2 < x → x < 1 →
        ¬ ∃ M : ℝ, ∀ s : ℂ, x < s.re → ‖G s‖ ≤ M := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have hA : DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  obtain ⟨Φ, hΦd, -, hΦid⟩ := hH.herglotz
  obtain ⟨κ, P, hκ, hPd, hGL⟩ := exists_reciprocalZeta_primitive hH
    (by simp [lam'] : lam' 1 = 0) hA hΦd hΦid
  let G : ℂ → ℂ := fun s => κ * ((s - 1) * cexp (P s))
  have hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    ((((hasDerivAt_id' s).sub_const 1).mul (hPd s hs).cexp).const_mul κ).differentiableAt
      |>.differentiableWithinAt
  refine ⟨G, hGd, hGL, fun x hx hx1 => ?_⟩
  apply not_bounded_of_unique_zero_one (b := producerMobius lam') hx hx1 hGd
    (LSeries_producerMobius hH.summable (s := 2) (by norm_num)).1
  · intro s hs
    exact (hGL s (by linarith)).trans (LSeries_producerMobius hH.summable (by linarith : 1 < s.re)).2.symm
  · intro s _
    simp only [G, mul_eq_zero, hκ, Complex.exp_ne_zero, or_false, false_or, sub_eq_zero]

end RHTower.WeilSingularArithmetic
