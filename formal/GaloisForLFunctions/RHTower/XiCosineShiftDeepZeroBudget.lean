import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointCriterion

/-!
# The nonreal zeros of `cos(hD)Ξ` are bounded by the zeros of `ξ` deeper than `h`

For `h ∈ ℝ` let `A_h(z) = (Ξ(z + ih) + Ξ(z − ih))/2 = cos(hD)Ξ(z)`. A zero `ρ = β + iγ` of `ξ`
corresponds to the zero `γ − i(β − ½)` of `Ξ`.

**Theorem** (`sum_zeroMult_cosShiftXi_le`). Suppose only finitely many zeros of `ξ` satisfy
`β < ½ − h`, say `D_h` of them counted with multiplicity. Then the nonreal zeros of `A_h` have
total multiplicity at most `2·D_h`, the number of zeros of `ξ` with `|β − ½| > h`. The bound holds
for every `h`, although real-rootedness of `A_h` is not monotone in `h`.

**Proof.** The Hadamard polynomials `R_n` of `Ξ` (`DeBruijn.xiRealApprox`) converge locally
uniformly to `Ξ`, and their roots are zeros of `Ξ`. So their shift averages converge to `A_h`, and
by the generalized Hermite–Biehler count (`nonrealRootCount_shiftAvg_le`) each has at most
`2·#{roots with Im > h} ≤ 2·D_h` nonreal roots. Hurwitz's theorem on discs isolating the nonreal
zeros of `A_h` transfers the bound.
-/

open Complex Filter Topology Set Polynomial Metric

namespace RHTower.CosineDefectBudget

open GaloisForLFunctions.HTGeometry RHTower.DeBruijn

noncomputable section

/-- The cosine shift `cos(hD)Ξ`. -/
def cosShiftXi (h : ℝ) (z : ℂ) : ℂ := (XiC (z + h * I) + XiC (z - h * I)) / 2

theorem differentiable_XiC' : Differentiable ℂ XiC := fun z =>
  (XiC_analytic z (mem_univ z)).differentiableAt

theorem differentiable_cosShiftXi (h : ℝ) : Differentiable ℂ (cosShiftXi h) := by
  unfold cosShiftXi
  have hX := differentiable_XiC'
  fun_prop

theorem XiC_neg' (z : ℂ) : XiC (-z) = XiC z := by
  change xi (1 / 2 + (-z) * I) = xi (1 / 2 + z * I)
  rw [show (1 : ℂ) / 2 + (-z) * I = 1 - (1 / 2 + z * I) by ring]
  exact xi_one_sub _

theorem cosShiftXi_zero_ne (h : ℝ) : cosShiftXi h 0 ≠ 0 := by
  unfold cosShiftXi
  rw [zero_sub, XiC_neg', zero_add, ← two_mul, mul_div_cancel_left₀ _ two_ne_zero]
  change xi (1 / 2 + (h : ℂ) * I * I) ≠ 0
  rw [mul_assoc, I_mul_I]
  apply xi_ne_zero_of_im_sq_le
  simp

theorem analyticOrderAt_cosShiftXi_ne_top (h : ℝ) (w : ℂ) : analyticOrderAt (cosShiftXi h) w ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ (cosShiftXi h) univ := fun z _ =>
    (differentiable_cosShiftXi h).analyticAt z
  have h0 : analyticOrderAt (cosShiftXi h) 0 ≠ ⊤ := by
    rw [(han 0 (mem_univ 0)).analyticOrderAt_eq_zero.mpr (cosShiftXi_zero_ne h)]
    exact ENat.zero_ne_top
  exact han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 0) (mem_univ w) h0

/-! ## The approximants -/

theorem tendstoLocallyUniformly_half {ι : Type*} {p : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : TendstoLocallyUniformly F f p) :
    TendstoLocallyUniformly (fun n z => F n z / 2) (fun z => f z / 2) p := by
  rw [Metric.tendstoLocallyUniformly_iff] at hF ⊢
  intro ε hε x
  obtain ⟨t, ht, hev⟩ := hF ε hε x
  refine ⟨t, ht, ?_⟩
  filter_upwards [hev] with n hn y hy
  have := hn y hy
  rw [dist_eq_norm] at this ⊢
  rw [← sub_div, norm_div, Complex.norm_ofNat]
  linarith [norm_nonneg (f y - F n y)]

theorem tendstoLocallyUniformly_shiftAvg_xiRealApprox (h : ℝ) :
    TendstoLocallyUniformly (fun n z => ((shiftAvg h (xiRealApprox n)).map Complex.ofRealHom).eval z)
      (cosShiftXi h) atTop := by
  have hloc := tendstoLocallyUniformly_xiRealApprox
  rw [riemannHeat_zero_eq_XiC] at hloc
  have h1 := hloc.comp (fun z : ℂ => z + h * I) (continuous_id.add continuous_const)
  have h2 := hloc.comp (fun z : ℂ => z - h * I) (continuous_id.sub continuous_const)
  have h3 := tendstoLocallyUniformly_half (h1.add h2)
  refine (h3.congr_right fun z => ?_).congr fun n z => ?_
  · simp [cosShiftXi, Function.comp_def]
  · simp only [eval_map_shiftAvg, Pi.add_apply, Function.comp_def]

/-- The copies of zeros `ρ` of `ξ` with `β < ½ − h`, i.e. `Im(γ − i(β − ½)) > h`. -/
def deepCopies (h : ℝ) : Set XiZeroCopy := {q | h < (xiSpectralPoint q).im}

theorem nonrealRootCount_shiftAvg_xiRealApprox_le {h : ℝ} (hS : (deepCopies h).Finite) (n : ℕ) :
    nonrealRootCount (shiftAvg h (xiRealApprox n)) ≤ 2 * hS.toFinset.card := by
  classical
  refine (nonrealRootCount_shiftAvg_le (xiRealApprox_ne_zero n) h).trans ?_
  gcongr
  set T := xiPairedCopyFinset (xiConjClosedFinset n)
  rw [map_xiRealApprox, roots_C_mul _ XiC_zero_ne_zero, roots_xiZeroPoly, Multiset.filter_map,
    Multiset.card_map, ← Finset.filter_val, Finset.card_val]
  refine Finset.card_le_card fun q hq => ?_
  rw [Finset.mem_filter] at hq
  rw [Set.Finite.mem_toFinset]
  exact hq.2

/-- **Defects of the cosine producer are bounded by deep zeros.** For every finite set `E` of
nonreal points, `Σ_{e∈E} ord_e cos(hD)Ξ ≤ 2·#{zeros ρ of ξ with β < ½ − h}`. -/
theorem sum_zeroMult_cosShiftXi_le {h : ℝ} (hS : (deepCopies h).Finite) (E : Finset ℂ)
    (hE : ∀ e ∈ E, e.im ≠ 0) :
    ∑ e ∈ E, zeroMult (cosShiftXi h) e ≤ 2 * hS.toFinset.card := by
  classical
  have hfin := analyticOrderAt_cosShiftXi_ne_top h
  have hdiff := differentiable_cosShiftXi h
  choose ρ₀ hρ₀ hρ₀prop using fun e => exists_radius_zeroSumBall_eq_zeroMult hdiff hfin e
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  set r : ℂ → ℝ := fun e => min (ρ₀ e) (min (|e.im| / 2) (d / 3)) with hrdef
  have hrpos : ∀ e ∈ E, 0 < r e := fun e he =>
    lt_min (hρ₀ e) (lt_min (by have := abs_pos.mpr (hE e he); linarith) (by linarith))
  have havoid : ∀ e ∈ E, ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e he w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have hr2 : r e ≤ |e.im| / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hpos := abs_pos.mpr (hE e he)
    linarith
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    have h3 : r e ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    have h4 : r e' ≤ d / 3 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set F : ℕ → ℂ → ℂ := fun n z => ((shiftAvg h (xiRealApprox n)).map Complex.ofRealHom).eval z
    with hFdef
  have hF : ∀ n, Differentiable ℂ (F n) := fun n => Polynomial.differentiable _
  have hconv := tendstoLocallyUniformly_shiftAvg_xiRealApprox h
  have hev : ∀ e ∈ E, ∀ᶠ n in atTop,
      zeroSumBall (F n) e (r e) = (zeroMult (cosShiftXi h) e : ℂ) ∧
        ∀ w ∈ sphere e (r e), F n w ≠ 0 := by
    intro e he
    obtain ⟨hsph, hcount⟩ := hρ₀prop e (r e) (hrpos e he) (min_le_left _ _)
    have h1 := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly hF hdiff hconv (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph
    have h2 := eventually_ne_zero_on_sphere hdiff.continuous hconv (hrpos e he).le hsph
    filter_upwards [h1, h2] with n hn1 hn2
    exact ⟨by rw [hn1, hcount], hn2⟩
  have hF0 : ∀ᶠ n in atTop, F n 0 ≠ 0 :=
    ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ 0)).eventually_ne
      (cosShiftXi_zero_ne h)
  obtain ⟨n, hn, hn0⟩ := (((Filter.eventually_all_finset E).mpr hev).and hF0).exists
  set B := (shiftAvg h (xiRealApprox n)).map Complex.ofRealHom with hB
  have hB0 : B ≠ 0 := by
    intro h0
    apply hn0
    simp only [hFdef]
    rw [← hB, h0, eval_zero]
  have hsum := sum_le_card_nonreal_roots hB0 (E := E) (r := r)
    (n := fun e => zeroMult (cosShiftXi h) e) hrpos havoid hdisj
    (fun e he => (hn e he).2) (fun e he => (hn e he).1)
  rw [← nonrealRootCount_eq] at hsum
  exact hsum.trans (nonrealRootCount_shiftAvg_xiRealApprox_le hS n)

/-- **Finitely many deep zeros give finitely many defects.** If only finitely many zeros of `ξ`
satisfy `β < ½ − h`, then `cos(hD)Ξ` has finitely many nonreal zeros, and their total multiplicity
is at most the number of zeros of `ξ` with `|β − ½| > h` (twice the deep count). -/
theorem finite_nonreal_zeros_cosShiftXi {h : ℝ} (hS : (deepCopies h).Finite) :
    ∃ hZ : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite,
      ∑ e ∈ hZ.toFinset, zeroMult (cosShiftXi h) e ≤ 2 * hS.toFinset.card := by
  classical
  have hZ : {z : ℂ | cosShiftXi h z = 0 ∧ z.im ≠ 0}.Finite := by
    by_contra hinf
    obtain ⟨E, hEsub, hEcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * hS.toFinset.card + 1)
    have hle := sum_zeroMult_cosShiftXi_le hS E fun e he => (hEsub he).2
    have hge : 2 * hS.toFinset.card + 1 ≤ ∑ e ∈ E, zeroMult (cosShiftXi h) e := by
      calc 2 * hS.toFinset.card + 1 = ∑ _e ∈ E, 1 := by simp [hEcard]
        _ ≤ ∑ e ∈ E, zeroMult (cosShiftXi h) e := Finset.sum_le_sum fun e he =>
            one_le_zeroMult_of_eq_zero (differentiable_cosShiftXi h)
              (analyticOrderAt_cosShiftXi_ne_top h) (hEsub he).1
    omega
  exact ⟨hZ, sum_zeroMult_cosShiftXi_le hS _ fun e he => (hZ.mem_toFinset.mp he).2⟩

/-- Without deep zeros there are no defects: if no zero of `ξ` has `β < ½ − h`, then every zero of
`cos(hD)Ξ` is real. -/
theorem cosShiftXi_zero_im_eq_zero_of_no_deep {h : ℝ} (hno : deepCopies h = ∅) {z : ℂ}
    (hz : cosShiftXi h z = 0) : z.im = 0 := by
  classical
  by_contra hzim
  have hS : (deepCopies h).Finite := by rw [hno]; exact Set.finite_empty
  have hle := sum_zeroMult_cosShiftXi_le hS {z} (by simpa using hzim)
  have hcard : hS.toFinset.card = 0 := by
    rw [Finset.card_eq_zero, Set.Finite.toFinset_eq_empty]; exact hno
  rw [hcard, Finset.sum_singleton] at hle
  have := one_le_zeroMult_of_eq_zero (differentiable_cosShiftXi h)
    (analyticOrderAt_cosShiftXi_ne_top h) hz
  omega

end

end RHTower.CosineDefectBudget
