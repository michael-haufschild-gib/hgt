import GaloisForLFunctions.SurfaceOfSpecZ.TheLowerSideSeesTheSignOfTheTopLayer
import GaloisForLFunctions.SurfaceOfSpecZ.TheSamplingSetsOfTheTopLayer
import GaloisForLFunctions.HTGeometry.BohrUniqueness
import GaloisForLFunctions.HTGeometry.BohrParseval
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance

/-!
# Bohr-dense sets sample every attained top

A set `T ⊂ ℝ` of log-degrees is *Bohr-dense at `+∞`* if beyond every bound it approximates every
finite family of phases `(e^{iλv})_{λ∈S}` (`IsBohrDenseAtTop`). Every such set samples every attained
top layer: if `2 Re S(u) ≥ −K` on `T` and the maximal real part `½ + b` is attained, a tempered
configuration without real zeros is pure (`onLine_of_bddBelow_of_isBohrDenseAtTop`).

The top layer `F_top(u) = Σ_{Re z = b} e_z e^{i Im z · u}` is almost periodic and real. Since
`F − F_top → 0` for the normalized trace `F = 2 Re S e^{−bu}`, the lower bound makes `F_top ≥ −ε`
far out on `T`, and Bohr density transports this to every point: `F_top ≥ 0` on `ℝ`
(`topTrace_nonneg_of_isBohrDenseAtTop`). Without real zeros its mean vanishes
(`bohrMean_topTraceC`), so `F_top = 0` (`eq_zero_of_bohrMean_eq_zero_of_nonneg`), against its
Bohr coefficient `e_{ρ₀ − ½} ≠ 0` at the top zero.

Sets containing arbitrarily long intervals are Bohr-dense (`isBohrDenseAtTop_of_long_intervals`),
and so are the log-degrees of any `D ⊂ ℕ` containing every integer of `[x, e^L x]` for arbitrarily
large `x` and `L` (`onLine_of_bddBelow_integer_runs_of_max`): attained tops need no density of the
sample, only long runs of it. One Frobenius `{n log q}` is not
Bohr-dense: the phase `e^{2πiu/log q}` is `1` on it.
-/

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-- `T` is **Bohr-dense at `+∞`**: beyond every bound it approximates every finite family of
phases `e^{iλv}`. -/
def IsBohrDenseAtTop (T : Set ℝ) : Prop :=
  ∀ (S : Finset ℝ) (v η U : ℝ), 0 < η → ∃ u ∈ T, U ≤ u ∧
    ∀ lam ∈ S, ‖bohrExp lam u - bohrExp lam v‖ < η

/-! ### Means of finite sums -/

theorem bohrMean_finset_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℂ}
    (hc : ∀ i, Continuous (F i)) (ha : ∀ i, _root_.HTGeometry.IsBohrAlmostPeriodic (F i)) :
    bohrMean (fun t => ∑ i ∈ S, F i t) = ∑ i ∈ S, bohrMean (F i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp only [Finset.sum_empty]; exact bohrMean_zero
  · intro i S hi ih
    simp only [Finset.sum_insert hi]
    rw [bohrMean_add (hc i) (ha i) (continuous_finsetSum _ fun j _ => hc j)
      (isBohrAlmostPeriodic_sum S (fun j _ => hc j) (fun j _ => ha j)), ih]

theorem bohrCoefficient_finset_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℂ}
    (hc : ∀ i, Continuous (F i)) (ha : ∀ i, _root_.HTGeometry.IsBohrAlmostPeriodic (F i))
    (lam : ℝ) :
    bohrCoefficient (fun t => ∑ i ∈ S, F i t) lam = ∑ i ∈ S, bohrCoefficient (F i) lam := by
  unfold bohrCoefficient
  have e : (fun t => (∑ i ∈ S, F i t) * bohrChar lam t) =
      fun t => ∑ i ∈ S, F i t * bohrChar lam t := by
    funext t; rw [Finset.sum_mul]
  rw [e]
  exact bohrMean_finset_sum S (F := fun i t => F i t * bohrChar lam t)
    (fun i => (hc i).mul (continuous_bohrChar lam))
    (fun i => isBohrAlmostPeriodic_mul_bohrChar (hc i) (ha i) lam)

/-! ### The top layer as an almost periodic function -/

section TopLayer

variable {Z : ZeroConfig} {b : ℝ}

/-- A term of the top layer: `e_z e^{i Im z · u}` if `Re z = b`. -/
def topTerm (Z : ZeroConfig) (b : ℝ) (z : ℂ) (u : ℝ) : ℂ :=
  if z.re = b then evenCoeff Z (boxSpline 1 3) z * bohrExp z.im u else 0

/-- The complex top layer `Σ_{Re z = b} e_z e^{i Im z · u}`. -/
def topTraceC (Z : ZeroConfig) (b u : ℝ) : ℂ := ∑' z, topTerm Z b z u

theorem bohrExp_apply (lam u : ℝ) : bohrExp lam u = cexp (((lam * u : ℝ) : ℂ) * I) := by
  unfold bohrExp bohrChar; congr 2; push_cast; ring

theorem cexp_sub_mul_eq_bohrExp {z : ℂ} (hz : z.re = b) (u : ℝ) :
    cexp ((z - b) * u) = bohrExp z.im u := by
  rw [bohrExp_apply]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hz]

theorem topTrace_eq_re (Z : ZeroConfig) (b u : ℝ) : topTrace Z b u = (topTraceC Z b u).re := by
  unfold topTrace topTraceC topTerm
  congr 1
  refine tsum_congr fun z => ?_
  split_ifs with h
  · rw [cexp_sub_mul_eq_bohrExp h]
  · rfl

theorem norm_topTerm_le (z : ℂ) (u : ℝ) :
    ‖topTerm Z b z u‖ ≤ ‖evenCoeff Z (boxSpline 1 3) z‖ := by
  unfold topTerm
  split_ifs
  · rw [norm_mul, bohrExp, norm_bohrChar, mul_one]
  · simp

theorem topTerm_eq_of_re (z : ℂ) (h : z.re = b) :
    topTerm Z b z = fun u => evenCoeff Z (boxSpline 1 3) z * bohrExp z.im u := by
  funext u; simp [topTerm, h]

theorem topTerm_eq_of_ne (z : ℂ) (h : z.re ≠ b) : topTerm Z b z = fun _ => 0 := by
  funext u; simp [topTerm, h]

theorem continuous_topTerm (z : ℂ) : Continuous (topTerm Z b z) := by
  by_cases h : z.re = b
  · rw [topTerm_eq_of_re z h]; exact continuous_const.mul (continuous_bohrExp _)
  · rw [topTerm_eq_of_ne z h]; exact continuous_const

theorem isBohrAlmostPeriodic_topTerm (z : ℂ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (topTerm Z b z) := by
  by_cases h : z.re = b
  · rw [topTerm_eq_of_re z h]
    exact isBohrAlmostPeriodic_const_mul _ (isBohrAlmostPeriodic_bohrExp _)
  · rw [topTerm_eq_of_ne z h]; exact isBohrAlmostPeriodic_const 0

theorem summable_topTerm (hZ : TemperedConfig Z) (u : ℝ) :
    Summable fun z => topTerm Z b z u :=
  Summable.of_norm_bounded (summable_norm_evenCoeff_spline hZ) fun z => norm_topTerm_le z u

theorem continuous_topTraceC (hZ : TemperedConfig Z) : Continuous (topTraceC Z b) :=
  continuous_tsum (fun z => continuous_topTerm z) (summable_norm_evenCoeff_spline hZ)
    fun z u => norm_topTerm_le z u

/-- **Uniform approximation** of the top layer by finite sums. -/
theorem exists_finset_topTraceC_approx (hZ : TemperedConfig Z) {ε : ℝ} (hε : 0 < ε) :
    ∃ S₀ : Finset ℂ, ∀ S : Finset ℂ, S₀ ⊆ S → ∀ u,
      ‖topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u‖ ≤ ε := by
  have hE := summable_norm_evenCoeff_spline hZ
  have htail := tendsto_tsum_compl_atTop_zero (fun z => ‖evenCoeff Z (boxSpline 1 3) z‖)
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp (htail.eventually (gt_mem_nhds hε))
  refine ⟨S₀, fun S hS u => ?_⟩
  have h1 : ∑' z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z‖ < ε := hS₀ S hS
  have hs := summable_topTerm (b := b) hZ u
  have hsn : Summable fun z => ‖topTerm Z b z u‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun z => norm_topTerm_le z u) hE
  have heq : topTraceC Z b u - ∑ z ∈ S, topTerm Z b z u =
      ∑' z : {x // x ∉ S}, topTerm Z b z u := by
    rw [topTraceC, ← hs.sum_add_tsum_subtype_compl S]; ring
  rw [heq]
  calc ‖∑' z : {x // x ∉ S}, topTerm Z b z u‖ ≤ ∑' z : {x // x ∉ S}, ‖topTerm Z b z u‖ :=
        norm_tsum_le_tsum_norm (hsn.subtype _)
    _ ≤ ∑' z : {x // x ∉ S}, ‖evenCoeff Z (boxSpline 1 3) z‖ :=
        Summable.tsum_le_tsum (fun z => norm_topTerm_le _ _) (hsn.subtype _) (hE.subtype _)
    _ ≤ ε := h1.le

theorem isBohrAlmostPeriodic_topTraceC (hZ : TemperedConfig Z) :
    _root_.HTGeometry.IsBohrAlmostPeriodic (topTraceC Z b) := by
  refine _root_.HTGeometry.isBohrAlmostPeriodic_of_uniform_approx fun ε hε => ?_
  obtain ⟨S, hS⟩ := exists_finset_topTraceC_approx (b := b) hZ hε
  exact ⟨fun u => ∑ z ∈ S, topTerm Z b z u,
    isBohrAlmostPeriodic_sum S (fun z _ => continuous_topTerm z)
      (fun z _ => isBohrAlmostPeriodic_topTerm z), fun u => hS S le_rfl u⟩

theorem continuous_topTerm_sum (S : Finset ℂ) :
    Continuous fun u => ∑ z ∈ S, topTerm Z b z u :=
  continuous_finsetSum _ fun z _ => continuous_topTerm z

theorem isBohrAlmostPeriodic_topTerm_sum (S : Finset ℂ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun u => ∑ z ∈ S, topTerm Z b z u :=
  isBohrAlmostPeriodic_sum S (fun z _ => continuous_topTerm z)
    (fun z _ => isBohrAlmostPeriodic_topTerm z)

/-- The Bohr coefficients of a top term. -/
theorem bohrCoefficient_topTerm (z : ℂ) (lam : ℝ) :
    bohrCoefficient (topTerm Z b z) lam =
      if z.re = b ∧ lam = z.im then evenCoeff Z (boxSpline 1 3) z else 0 := by
  by_cases h : z.re = b
  · rw [topTerm_eq_of_re z h]
    unfold bohrCoefficient
    have e : (fun t => evenCoeff Z (boxSpline 1 3) z * bohrExp z.im t * bohrChar lam t) =
        fun t => evenCoeff Z (boxSpline 1 3) z * (bohrExp z.im t * bohrChar lam t) := by
      funext t; ring
    rw [e, bohrMean_const_mul (f := fun t => bohrExp z.im t * bohrChar lam t) _
      ((continuous_bohrExp _).mul (continuous_bohrChar lam))
      (isBohrAlmostPeriodic_mul_bohrChar (continuous_bohrExp _) (isBohrAlmostPeriodic_bohrExp _)
        lam)]
    have hc := bohrCoefficient_bohrExp z.im lam
    unfold bohrCoefficient at hc
    rw [hc]
    by_cases hl : lam = z.im
    · simp [h, hl]
    · simp [h, hl]
  · rw [topTerm_eq_of_ne z h]
    unfold bohrCoefficient
    simp only [zero_mul]
    rw [bohrMean_zero]
    simp [h]

/-- **The top layer has mean zero** when it contains no real exponent. -/
theorem bohrMean_topTraceC (hZ : TemperedConfig Z)
    (hreal : ∀ z, evenCoeff Z (boxSpline 1 3) z ≠ 0 → z.re = b → z.im ≠ 0) :
    bohrMean (topTraceC Z b) = 0 := by
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨S, hS⟩ := exists_finset_topTraceC_approx (b := b) hZ hε
  have hP : bohrMean (fun t => ∑ z ∈ S, topTerm Z b z t) = 0 := by
    rw [bohrMean_finset_sum S (fun z => continuous_topTerm z)
      (fun z => isBohrAlmostPeriodic_topTerm z)]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h : z.re = b
    · by_cases he : evenCoeff Z (boxSpline 1 3) z = 0
      · have : topTerm Z b z = fun _ => 0 := by funext u; simp [topTerm, he]
        rw [this]; exact bohrMean_zero
      · rw [topTerm_eq_of_re z h,
          bohrMean_const_mul _ (continuous_bohrExp _) (isBohrAlmostPeriodic_bohrExp _)]
        have : bohrMean (bohrExp z.im) = 0 := by
          unfold bohrExp
          rw [bohrMean_bohrChar, if_neg (neg_ne_zero.mpr (hreal z he h))]
        rw [this, mul_zero]
    · rw [topTerm_eq_of_ne z h]; exact bohrMean_zero
  have h := norm_bohrMean_sub_le (continuous_topTraceC hZ) (isBohrAlmostPeriodic_topTraceC hZ)
    (continuous_topTerm_sum S) (isBohrAlmostPeriodic_topTerm_sum S) (fun t => hS S le_rfl t)
  rw [hP, sub_zero] at h
  linarith

theorem conj_bohrExp (lam u : ℝ) : conj (bohrExp lam u) = bohrExp (-lam) u := by
  rw [bohrExp_apply, bohrExp_apply, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

/-- **The top layer is real**: its terms at `z` and `z̄` are conjugate. -/
theorem topTraceC_im (u : ℝ) : (topTraceC Z b u).im = 0 := by
  have hconj : conj (topTraceC Z b u) = topTraceC Z b u := by
    unfold topTraceC
    rw [Complex.conj_tsum]
    have hinv : Function.Involutive (conj : ℂ → ℂ) := Complex.conj_conj
    rw [← (hinv.toPerm _).tsum_eq (fun z => topTerm Z b z u)]
    refine tsum_congr fun z => ?_
    simp only [Function.Involutive.coe_toPerm]
    unfold topTerm
    by_cases h : z.re = b
    · have h' : (conj z).re = b := by simpa using h
      rw [if_pos h, if_pos h', map_mul, conj_bohrExp, ← evenCoeff_conj, Complex.conj_im]
    · have h' : ¬ (conj z).re = b := by simpa using h
      rw [if_neg h, if_neg h', map_zero]
  exact Complex.conj_eq_iff_im.mp hconj

end TopLayer

/-! ### Bohr density transports the lower bound -/

/-- **The top layer is nonnegative** under a lower bound on a Bohr-dense set. -/
theorem topTrace_nonneg_of_isBohrDenseAtTop {Z : ZeroConfig} (hZ : TemperedConfig Z) {b : ℝ}
    (h : TopDepth Z b) (hb0 : 0 < b) {T : Set ℝ} (hT : IsBohrDenseAtTop T) {K : ℝ}
    (hK : ∀ u ∈ T, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) (v : ℝ) :
    0 ≤ topTrace Z b v := by
  have hE := summable_norm_evenCoeff_spline hZ
  set E := ∑' z, ‖evenCoeff Z (boxSpline 1 3) z‖ with hEdef
  have hE0 : 0 ≤ E := tsum_nonneg fun _ => norm_nonneg _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / 5 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨S, hS⟩ := exists_finset_topTraceC_approx (b := b) hZ hδ
  have h1 := (tendsto_normTrace_sub_topTrace hZ h).eventually
    (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  have hlim : Tendsto (fun u : ℝ => |K| * Real.exp (-(b * u))) atTop (𝓝 0) := by
    have h0 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hb0)).const_mul |K|
    simpa [Function.comp_def] using h0
  have h2 := hlim.eventually (gt_mem_nhds hδ)
  obtain ⟨U, hU⟩ := eventually_atTop.mp (h1.and h2)
  obtain ⟨u, huT, hUu, hph⟩ := hT (S.image Complex.im) v (δ / (E + 1)) U (by positivity)
  obtain ⟨hu1, hu2⟩ := hU u hUu
  have hn : -δ ≤ normTrace Z b u := by
    have hk := hK u huT
    unfold normTrace
    have h3 : -|K| * Real.exp (-(b * u)) ≤
        2 * (lagStructure Z (boxSpline 1 3) u).re * Real.exp (-(b * u)) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (Real.exp_pos _).le
    have h4 : -|K| * Real.exp (-(b * u)) = -(|K| * Real.exp (-(b * u))) := by ring
    linarith
  have htu : -(2 * δ) ≤ topTrace Z b u := by
    linarith [hu1.2]
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

/-- **Bohr-dense sets sample every attained top.** A lower bound `2 Re S(u) ≥ −K` on a set `T` that
is Bohr-dense at `+∞` puts every zero of a tempered configuration without real zeros on the line,
provided the maximal real part is attained. -/
theorem onLine_of_bddBelow_of_isBohrDenseAtTop {T : Set ℝ} (hT : IsBohrDenseAtTop T)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ u ∈ T, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  rcases (half_le_of_max hρ₀ hmax).eq_or_lt with h | h
  · exact onLine_of_max_eq_half hmax h.symm
  exfalso
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 < b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
    · have h1 := hmax _ h; simp at h1; rw [hbdef]; linarith
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
  have hgc := continuous_topTraceC (b := b) hZ
  have hga := isBohrAlmostPeriodic_topTraceC (b := b) hZ
  have hg0 := eq_zero_of_bohrMean_eq_zero_of_nonneg hgc hga
    (fun t => by
      rw [← topTrace_eq_re]; exact topTrace_nonneg_of_isBohrDenseAtTop hZ htop hb0 hT hK t)
    (fun t => topTraceC_im t) (bohrMean_topTraceC hZ hreal)
  set z₀ : ℂ := ρ₀ - 1 / 2 with hz₀def
  have hz₀re : z₀.re = b := by simp [z₀, hbdef]
  have hcoef0 : bohrCoefficient (topTraceC Z b) z₀.im = 0 := by
    have : topTraceC Z b = fun _ => 0 := funext hg0
    rw [this]; unfold bohrCoefficient; simp only [zero_mul]; exact bohrMean_zero
  have hle : ‖evenCoeff Z (boxSpline 1 3) z₀‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨S₀, hS₀⟩ := exists_finset_topTraceC_approx (b := b) hZ hε
    classical
    have hS := hS₀ (insert z₀ S₀) (Finset.subset_insert _ _)
    have hcoefP : bohrCoefficient (fun t => ∑ z ∈ insert z₀ S₀, topTerm Z b z t) z₀.im =
        evenCoeff Z (boxSpline 1 3) z₀ := by
      rw [bohrCoefficient_finset_sum _ (fun z => continuous_topTerm z)
        (fun z => isBohrAlmostPeriodic_topTerm z)]
      rw [Finset.sum_eq_single z₀]
      · rw [bohrCoefficient_topTerm, if_pos ⟨hz₀re, rfl⟩]
      · intro z _ hne
        rw [bohrCoefficient_topTerm, if_neg]
        rintro ⟨h1, h2⟩
        exact hne (Complex.ext (by rw [h1, hz₀re]) h2.symm)
      · intro hn; exact absurd (Finset.mem_insert_self _ _) hn
    have hd := norm_bohrCoefficient_sub_le hgc hga (continuous_topTerm_sum _)
      (isBohrAlmostPeriodic_topTerm_sum _) (fun t => hS t) z₀.im
    rw [hcoef0, hcoefP, zero_sub, norm_neg] at hd
    linarith
  exact hz₀ (norm_le_zero_iff.mp hle)

/-! ### Long intervals -/

/-- **Long runs are Bohr-dense.** A set containing intervals of every length beyond every bound is
Bohr-dense at `+∞`: the almost periods of `Σ_λ |e^{iλt} − e^{iλv}|²` meet every long interval. -/
theorem isBohrDenseAtTop_of_long_intervals {T : Set ℝ}
    (hT : ∀ L U : ℝ, ∃ a, U ≤ a ∧ Set.Icc a (a + L) ⊆ T) : IsBohrDenseAtTop T := by
  intro S v η U hη
  set g : ℝ → ℂ := fun t => ∑ lam ∈ S,
    (bohrExp lam t - bohrExp lam v) * conj (bohrExp lam t - bohrExp lam v) with hg
  have hdc : ∀ lam, Continuous fun t => bohrExp lam t - bohrExp lam v := fun lam =>
    (continuous_bohrExp lam).sub continuous_const
  have hda : ∀ lam, _root_.HTGeometry.IsBohrAlmostPeriodic fun t => bohrExp lam t - bohrExp lam v :=
    fun lam => isBohrAlmostPeriodic_sub (continuous_bohrExp lam) (isBohrAlmostPeriodic_bohrExp lam)
      continuous_const (isBohrAlmostPeriodic_const _)
  have hga : _root_.HTGeometry.IsBohrAlmostPeriodic g :=
    isBohrAlmostPeriodic_sum S (fun lam _ => (hdc lam).mul (Complex.continuous_conj.comp (hdc lam)))
      (fun lam _ => isBohrAlmostPeriodic_mul (hdc lam) (hda lam)
        (Complex.continuous_conj.comp (hdc lam)) (isBohrAlmostPeriodic_conj (hda lam)))
  obtain ⟨L, hL, hτ⟩ := hga (η ^ 2 / 2) (by positivity)
  obtain ⟨a, hUa, hsub⟩ := hT L (U + |v| + 1)
  obtain ⟨τ, hτmem, hτg⟩ := hτ (a - v)
  refine ⟨v + τ, hsub ⟨by linarith [hτmem.1], by linarith [hτmem.2]⟩, ?_, fun lam hlam => ?_⟩
  · linarith [hτmem.1, abs_nonneg v]
  have hgv : g v = 0 := by simp [hg]
  have hgu := hτg v
  rw [hgv, sub_zero] at hgu
  -- `g(v + τ) = Σ_λ ‖d_λ‖²`
  have hsq : ∀ lam, (bohrExp lam (v + τ) - bohrExp lam v) *
      conj (bohrExp lam (v + τ) - bohrExp lam v) =
        ((‖bohrExp lam (v + τ) - bohrExp lam v‖ ^ 2 : ℝ) : ℂ) := by
    intro lam
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hgsum : g (v + τ) = ((∑ lam ∈ S, ‖bohrExp lam (v + τ) - bohrExp lam v‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hg, hsq]; push_cast; rfl
  rw [hgsum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hgu
  have hone : ‖bohrExp lam (v + τ) - bohrExp lam v‖ ^ 2 ≤ η ^ 2 / 2 :=
    le_trans (Finset.single_le_sum (f := fun lam => ‖bohrExp lam (v + τ) - bohrExp lam v‖ ^ 2)
      (fun _ _ => sq_nonneg _) hlam) hgu
  have hlt : ‖bohrExp lam (v + τ) - bohrExp lam v‖ ^ 2 < η ^ 2 := by
    have : 0 < η ^ 2 := by positivity
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hη.le hlt

/-- **Long runs sample every attained top.** -/
theorem onLine_of_bddBelow_long_intervals_of_max {T : Set ℝ}
    (hT : ∀ L U : ℝ, ∃ a, U ≤ a ∧ Set.Icc a (a + L) ⊆ T)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ u ∈ T, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  onLine_of_bddBelow_of_isBohrDenseAtTop (isBohrDenseAtTop_of_long_intervals hT) Z hZ hnoreal hρ₀
    hmax hK

/-! ### Runs of integers -/

/-- **Runs of integers sample every attained top.** If `D ⊂ ℕ` contains every integer of
`[x, e^L x]` for arbitrarily large `x` and `L`, a lower bound on the spline traces at the degrees of
`D` puts every zero of a tempered configuration without real zeros on the line, provided the top is
attained. The bound passes from `log n` to the interval by the Lipschitz estimate
(`norm_lagStructure_sub_le`), since `log(n + 1) − log n ≤ 1/n`. Such `D` may have density zero
and no power-saving gaps. -/
theorem onLine_of_bddBelow_integer_runs_of_max (D : Set ℕ)
    (hD : ∀ L U : ℝ, ∃ x : ℕ, U ≤ x ∧ ∀ n : ℕ, x ≤ n → (n : ℝ) ≤ Real.exp L * x → n ∈ D)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {ρ₀ : ℂ}
    (hρ₀ : ρ₀ ∈ Z.carrier) (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) {K : ℝ}
    (hK : ∀ n ∈ D, -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  set C := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖ with hCdef
  have hC0 : 0 ≤ C := tsum_nonneg fun _ => by positivity
  set T : Set ℝ := {u | 1 ≤ u ∧ ⌊Real.exp u⌋₊ ∈ D} with hTdef
  refine onLine_of_bddBelow_long_intervals_of_max (T := T) ?_ Z hZ hnoreal hρ₀ hmax
    (K := K + 4 * C) ?_
  · intro L U
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
  · rintro u ⟨hu1, hn⟩
    set n := ⌊Real.exp u⌋₊ with hndef
    have hK1 := hK n hn
    have he : (2 : ℝ) ≤ Real.exp u := by have := Real.add_one_le_exp u; linarith
    have hn1 : Real.exp u < n + 1 := Nat.lt_floor_add_one _
    have hnle : (n : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos _).le
    have hnpos : (1 : ℝ) ≤ n := by linarith
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
    have hL := norm_lagStructure_sub_le hZ hb3 (by positivity) hbs hlog0 hlogn
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
    have hdiff : |2 * (lagStructure Z (boxSpline 1 3) u).re -
        2 * (lagStructure Z (boxSpline 1 3) (Real.log n)).re| ≤ 4 * C := by
      rw [← mul_sub, abs_mul, abs_two, ← Complex.sub_re]
      have h1 := (Complex.abs_re_le_norm _).trans hL
      have h2 : C * (u - Real.log n) * Real.exp (u / 2) ≤ C * 2 := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hfac hC0
      linarith
    linarith [(abs_le.mp hdiff).1]

end GaloisForLFunctions.SurfaceOfSpecZ
