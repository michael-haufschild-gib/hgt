import GaloisForLFunctions.SurfaceOfSpecZ.TheOtherSideAtEveryBohrDenseSet
import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEverySamplingSet

/-!
# The width law at every Bohr-dense set

`BohrDenseSetsSampleEveryAttainedTop` with growth: if `2 Re S(u) ≥ −K e^{su}` on a set `T` that is
Bohr-dense at `+∞`, `s ≥ 0`, then no tempered configuration without real zeros has an attained top
right of `½ + s` (`exists_re_gt_of_bddBelow_exp_of_isBohrDenseAtTop`): at depth `b > s` the bound
still makes the top layer `≥ −o(1)` on `T` (`topTrace_nonneg_of_isBohrDenseAtTop_exp`), hence `≥ 0`
on `ℝ`, and the mean-zero argument applies (`false_of_topTrace_nonneg`).

For `ζ`, modulo the approach to the line: the zero width is `≤ s` iff `2 Re S(u) ≥ −K e^{su}` on a
Bohr-dense set of log-degrees (`zetaZeroWidth_le_iff_bddBelow_exp_isBohrDense_of_zerosApproachLine`),
in particular iff `P(n) ≤ A(n) + K n^s` on a set of runs of integers
(`zetaZeroWidth_le_iff_bddBelow_rpow_integer_runs_of_zerosApproachLine`); this is
`TheWidthLawAtEverySamplingSet` at every Bohr-dense sample. Without `ZerosApproachLine` the same
bound is the abscissa law above `s`, `Θ − ½ ≤ max(s, Θ∞ − ½)`
(`re_le_of_finite_of_bddBelow_exp_isBohrDense`).
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- **A nonnegative top layer without real exponents vanishes**, against a nonzero top
coefficient. -/
theorem false_of_topTrace_nonneg {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) {z₀ : ℂ}
    (hz₀re : z₀.re = b) (hz₀ : evenCoeff Z (boxSpline 1 3) z₀ ≠ 0)
    (hnn : ∀ t, 0 ≤ topTrace Z b t) : False := by
  have hgc := continuous_topTraceC (b := b) hZ
  have hga := isBohrAlmostPeriodic_topTraceC (b := b) hZ
  have hg0 := eq_zero_of_bohrMean_eq_zero_of_nonneg hgc hga
    (fun t => by rw [← topTrace_eq_re]; exact hnn t) (fun t => topTraceC_im t)
    (bohrMean_topTraceC hZ hreal)
  have hcoef := bohrCoefficient_topTraceC (b := b) hZ hz₀re
  have h0 : topTraceC Z b = fun _ => 0 := funext hg0
  rw [h0] at hcoef
  unfold bohrCoefficient at hcoef
  simp only [zero_mul] at hcoef
  rw [bohrMean_zero] at hcoef
  exact hz₀ hcoef.symm

/-- **The top layer is nonnegative** under a lower bound `−K e^{su}`, `s < b`, on a Bohr-dense set. -/
theorem topTrace_nonneg_of_isBohrDenseAtTop_exp {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) {s : ℝ} (hsb : s < b) {T : Set ℝ} (hT : IsBohrDenseAtTop T) {K : ℝ}
    (hK : ∀ u ∈ T, -(K * Real.exp (s * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re)
    (v : ℝ) : 0 ≤ topTrace Z b v := by
  have hE := summable_norm_evenCoeff_spline hZ
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 5 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS⟩ := exists_finset_topTraceC_approx (b := b) hZ hδ
  have h1 := (tendsto_normTrace_sub_topTrace hZ h).eventually
    (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  have hlim : Tendsto (fun u : ℝ => |K| * Real.exp ((s - b) * u)) atTop (𝓝 0) := by
    have h0 := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : s - b < 0))).const_mul |K|
    simpa [Function.comp_def] using h0
  have h2 := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨U, hU⟩ := eventually_atTop.mp (h1.and h2)
  obtain ⟨u, huT, hUu, hph⟩ := hT (S.image Complex.im) v (δ / (E + 1)) U (by positivity)
  obtain ⟨hu1, hu2⟩ := hU u hUu
  have hn : -δ ≤ normTrace Z b u := by
    have hk := hK u huT
    unfold normTrace
    have e : Real.exp (s * u) * Real.exp (-(b * u)) = Real.exp ((s - b) * u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : -(|K| * Real.exp ((s - b) * u)) ≤
        2 * (lagStructure Z (boxSpline 1 3) u).re * Real.exp (-(b * u)) := by
      have h4 : -(K * Real.exp (s * u)) * Real.exp (-(b * u)) ≤
          2 * (lagStructure Z (boxSpline 1 3) u).re * Real.exp (-(b * u)) :=
        mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le
      have h5 : -(|K| * Real.exp ((s - b) * u)) ≤ -(K * Real.exp (s * u)) * Real.exp (-(b * u)) := by
        rw [neg_mul, mul_assoc, e]
        exact neg_le_neg (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le)
      linarith
    linarith
  have htu : -(2 * δ) ≤ topTrace Z b u := by linarith [hu1.2]
  have hPP : ‖∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v‖ ≤ δ := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ z ∈ S, (topTerm Z b z u - topTerm Z b z v)‖
        ≤ ∑ z ∈ S, ‖topTerm Z b z u - topTerm Z b z v‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z‖ * (δ / (E + 1)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          unfold topTerm
          split_ifs with hzb
          · rw [← mul_sub, norm_mul]
            exact mul_le_mul_of_nonneg_left (hph z.im (Finset.mem_image_of_mem _ hz)).le
              (norm_nonneg _)
          · simp only [sub_self, norm_zero]; positivity
      _ = (∑ z ∈ S, ‖evenCoeff Z (boxSpline 1 3) z‖) * (δ / (E + 1)) := by rw [Finset.sum_mul]
      _ ≤ E * (δ / (E + 1)) :=
          mul_le_mul_of_nonneg_right (hE.sum_le_tsum S fun _ _ => norm_nonneg _) (by positivity)
      _ ≤ δ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hdiff : ‖topTraceC Z b u - topTraceC Z b v‖ ≤ 3 * δ := by
    have hPu := hS S le_rfl u
    have hPv := hS S le_rfl v
    have e : topTraceC Z b u - topTraceC Z b v =
        (topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v) -
            (topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v) := by ring
    rw [e]
    calc ‖(topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v) -
            (topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v)‖
        ≤ ‖(topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u) +
          (∑ z ∈ S, topTerm Z b z u - ∑ z ∈ S, topTerm Z b z v)‖ +
            ‖topTraceC Z b v - ∑ z ∈ S, topTerm Z b z v‖ := norm_sub_le _ _
      _ ≤ (δ + δ) + δ := add_le_add ((norm_add_le _ _).trans (add_le_add hPu hPP)) hPv
      _ = 3 * δ := by ring
  have hre : topTrace Z b u - topTrace Z b v ≤ 3 * δ := by
    rw [topTrace_eq_re, topTrace_eq_re, ← Complex.sub_re]
    exact (Complex.re_le_norm _).trans hdiff
  linarith

/-- **No attained top right of `½ + s`** under a lower bound `−K e^{su}` on a Bohr-dense set. -/
theorem exists_re_gt_of_bddBelow_exp_of_isBohrDenseAtTop {T : Set ℝ} (hT : IsBohrDenseAtTop T)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K s : ℝ}
    (hK : ∀ u ∈ T, -(K * Real.exp (s * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re)
    (hs0 : 0 ≤ s) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hρs : 1 / 2 + s < ρ₀.re) :
    ∃ ρ ∈ Z.carrier, ρ₀.re < ρ.re := by
  by_contra hno
  push Not at hno
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hsb : s < b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hno _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hno _ h; simp at h1; rw [hbdef]; linarith
  have hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0 := by
    intro z hz hzre hzim
    have hzb : z = (b : ℂ) := Complex.ext (by simpa using hzre) (by simpa using hzim)
    rcases mem_of_evenCoeff_ne_zero hz with h' | h'
    · rw [hzb] at h'; exact hnoreal _ h' (by simp)
    · rw [hzb, Complex.conj_ofReal] at h'; exact hnoreal _ h' (by simp)
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  exact false_of_topTrace_nonneg hZ hreal (by simp [hbdef]) hz₀
    (topTrace_nonneg_of_isBohrDenseAtTop_exp hZ htop hsb hT hK)

/-! ### For `ζ`, modulo the approach to the line -/

/-- **The width law at every Bohr-dense set.** Modulo `ZerosApproachLine`, the zero width of `ζ` is
`≤ s` iff the spline traces are `≥ −K e^{su}` on a Bohr-dense set of `u ≥ 0`. -/
theorem zetaZeroWidth_le_iff_bddBelow_exp_isBohrDense_of_zerosApproachLine
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) {T : Set ℝ} (hT : IsBohrDenseAtTop T)
    (hT0 : ∀ u ∈ T, 0 ≤ u) {s : ℝ} (hs0 : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ K : ℝ, ∀ u ∈ T,
      -(K * Real.exp (s * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
  constructor
  · intro hwid
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun u hu => ?_⟩
    exact neg_le_of_abs_le (abs_two_re_lagStructure_le_exp_of_width temperedConfig_zetaZeroConfig
      (a := s) ((zetaZeroWidth_le_iff_re_le hs0).mp hwid) (hT0 u hu))
  · rintro ⟨K, hK⟩
    exact zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper hZ hs0
      fun ρ₀ hρ₀ hρs => exists_re_gt_of_bddBelow_exp_of_isBohrDenseAtTop hT zetaZeroConfig
        temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hK hs0 hρ₀ hρs

/-- **The width law on runs of integers.** Modulo `ZerosApproachLine`, the zero width of `ζ` is
`≤ s` iff `2 Re S(log n) ≥ −K n^s` (equivalently `P(n) ≤ A(n) + K n^s`) on a set of runs of
integers. -/
theorem zetaZeroWidth_le_iff_bddBelow_rpow_integer_runs_of_zerosApproachLine
    (hZ : _root_.RHTower.BacklundConverse.ZerosApproachLine) (D : Set ℕ)
    (hD : ∀ L U : ℝ, ∃ x : ℕ, U ≤ x ∧ ∀ n : ℕ, x ≤ n → (n : ℝ) ≤ Real.exp L * x → n ∈ D)
    {s : ℝ} (hs0 : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ K : ℝ, ∀ n ∈ D, 1 ≤ n →
      -(K * (n : ℝ) ^ s) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re := by
  constructor
  · intro hwid
    refine ⟨∑' z, ‖evenCoeff zetaZeroConfig (boxSpline 1 3) z‖, fun n _ hn => ?_⟩
    have h := abs_two_re_lagStructure_le_exp_of_width temperedConfig_zetaZeroConfig (a := s)
      ((zetaZeroWidth_le_iff_re_le hs0).mp hwid) (Real.log_natCast_nonneg n)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show Real.exp (s * Real.log n) = (n : ℝ) ^ s by
      rw [Real.rpow_def_of_pos hn0, mul_comm]] at h
    exact neg_le_of_abs_le h
  · rintro ⟨K, hK⟩
    -- transport the bound from `log n` to the runs of `u` (`log(n+1) − log n ≤ 1/n`)
    have hb3 := contDiff_boxSpline (r := 1) one_pos 2
    have hbs := boxSpline_support (r := 1) one_pos 3
    set C := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ * ‖z‖ with hCdef
    have hC0 : 0 ≤ C := tsum_nonneg fun _ => by positivity
    set T : Set ℝ := {u | 1 ≤ u ∧ ⌊Real.exp u⌋₊ ∈ D} with hTdef
    have hT : IsBohrDenseAtTop T := by
      refine isBohrDenseAtTop_of_long_intervals fun L U => ?_
      obtain ⟨x, hx, hxD⟩ := hD L (Real.exp (max U 1))
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (Real.exp_pos _) hx
      have hlx : max U 1 ≤ Real.log x := by
        have := Real.log_le_log (Real.exp_pos _) hx; rwa [Real.log_exp] at this
      refine ⟨Real.log x, le_trans (le_max_left U 1) hlx, fun u hu => ⟨?_, ?_⟩⟩
      · linarith [hu.1, le_max_right U 1]
      · apply hxD
        · apply Nat.le_floor
          calc ((x : ℕ) : ℝ) = Real.exp (Real.log x) := (Real.exp_log hx0).symm
            _ ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
        · calc (⌊Real.exp u⌋₊ : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
            _ ≤ Real.exp (Real.log x + L) := Real.exp_le_exp.mpr hu.2
            _ = Real.exp L * x := by rw [Real.exp_add, Real.exp_log hx0]; ring
    have hTK : ∀ u ∈ T, -((|K| + 4 * C) * Real.exp (s * u)) ≤
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re := by
      rintro u ⟨hu1, hn⟩
      set n := ⌊Real.exp u⌋₊ with hndef
      have he : (2 : ℝ) ≤ Real.exp u := by have := Real.add_one_le_exp u; linarith
      have hn1 : Real.exp u < n + 1 := Nat.lt_floor_add_one _
      have hnle : (n : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
      have hnpos : (1 : ℝ) ≤ n := by linarith
      have hn1' : 1 ≤ n := by exact_mod_cast hnpos
      have hK1 := hK n hn hn1'
      have hlogn : Real.log n ≤ u := by
        rw [← Real.log_exp u]; exact Real.log_le_log (by linarith) hnle
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hnpos
      have hgap : u - Real.log n ≤ 1 / n := by
        have h1 : u ≤ Real.log (n + 1) := by
          rw [← Real.log_exp u]; exact Real.log_le_log (Real.exp_pos _) hn1.le
        have h2 : Real.log (n + 1) - Real.log n ≤ 1 / n := by
          have hn0 : (n : ℝ) ≠ 0 := (show (0 : ℝ) < n by linarith).ne'
          rw [← Real.log_div (show (0 : ℝ) < n + 1 by linarith).ne' hn0]
          have := Real.log_le_sub_one_of_pos
            (show 0 < ((n : ℝ) + 1) / n from div_pos (by linarith) (by linarith))
          have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by rw [div_sub_one hn0]; congr 1; ring
          linarith
        linarith
      have hL := norm_lagStructure_sub_le temperedConfig_zetaZeroConfig hb3 (by positivity) hbs
        hlog0 hlogn
      have hfac : (u - Real.log n) * Real.exp (u / 2) ≤ 2 := by
        have hpos : 0 < Real.exp (u / 2) := Real.exp_pos _
        have hsq : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
          rw [← Real.exp_add]; ring_nf
        have h1 : 1 ≤ Real.exp (u / 2) := Real.one_le_exp (by linarith)
        have hn2 : Real.exp u ≤ 2 * n := by linarith
        calc (u - Real.log n) * Real.exp (u / 2) ≤ (1 / n) * Real.exp (u / 2) :=
              mul_le_mul_of_nonneg_right hgap hpos.le
          _ ≤ 2 := by
              rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
              nlinarith
      have hdiff : |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re -
          2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log n)).re| ≤ 4 * C := by
        rw [← mul_sub, abs_mul, abs_two, ← Complex.sub_re]
        have h1 := (Complex.abs_re_le_norm _).trans hL
        have h2 : C * (u - Real.log n) * Real.exp (u / 2) ≤ C * 2 := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfac hC0
        linarith
      -- `n^s ≤ e^{su}` and `1 ≤ e^{su}`
      have hns : (n : ℝ) ^ s ≤ Real.exp (s * u) := by
        rw [Real.rpow_def_of_pos (by linarith), mul_comm]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogn hs0)
      have hes : 1 ≤ Real.exp (s * u) := Real.one_le_exp (by positivity)
      have h3 : -(K * (n : ℝ) ^ s) ≥ -(|K| * Real.exp (s * u)) := by
        have := mul_le_mul (le_abs_self K) hns (by positivity) (abs_nonneg K)
        linarith
      have h4 : 4 * C ≤ 4 * C * Real.exp (s * u) := le_mul_of_one_le_right (by positivity) hes
      linarith [(abs_le.mp hdiff).1]
    exact zetaZeroWidth_le_of_zerosApproachLine_of_noDeeper hZ hs0
      fun ρ₀ hρ₀ hρs => exists_re_gt_of_bddBelow_exp_of_isBohrDenseAtTop hT zetaZeroConfig
        temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hTK hs0 hρ₀ hρs

/-- **The abscissa law above `s` from a Bohr-dense bound.** Without `ZerosApproachLine`: a lower bound
`−K e^{su}` on a Bohr-dense set of log-degrees makes every finite layer of zeros of `ζ` right of a
level `½ + h`, `h ≥ s`, empty; equivalently `Θ − ½ ≤ max(s, Θ∞ − ½)`. -/
theorem re_le_of_finite_of_bddBelow_exp_isBohrDense {T : Set ℝ} (hT : IsBohrDenseAtTop T)
    {K s : ℝ} (hs0 : 0 ≤ s)
    (hK : ∀ u ∈ T, -(K * Real.exp (s * u)) ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re)
    {h : ℝ} (hsh : s ≤ h)
    (hF : {q : _root_.RHTower.XiZeroCopy | 1 / 2 + h < (q.1 : ℂ).re}.Finite) :
    ∀ q : _root_.RHTower.XiZeroCopy, (q.1 : ℂ).re ≤ 1 / 2 + h :=
  re_le_of_finite_of_noDeeper (fun _ hρ₀ hρs => exists_re_gt_of_bddBelow_exp_of_isBohrDenseAtTop hT
    zetaZeroConfig temperedConfig_zetaZeroConfig zetaZeroConfig_im_ne_zero' hK hs0 hρ₀ hρs) hsh hF

end GaloisForLFunctions.SurfaceOfSpecZ
