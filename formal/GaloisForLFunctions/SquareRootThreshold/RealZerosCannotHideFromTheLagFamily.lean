import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyDecidesTheCriticalLine

/-!
# Real zeros cannot hide from the lag family; GRH for Dirichlet `L`-functions

The one-parameter criterion `onLine_iff_lag_twoBump_nonneg` assumes that there are no real
zeros. Dirichlet `L`-functions of real characters might have real zeros, but real zeros cannot
hide from the family.

* **Real zeros carry positive weight at the center `0`**
  (`re_evenCoeff_modScaledBump_zero_pos`). For a real zero `½ + δ`, the merged coefficient of
  `e^{δv}` in `2 Re S(v)` is `2m h_w(−iδ)²`, and `h_w(−iδ)` is real and nonzero.
* **A positive real top cannot hide under a one-sided bound** (`re_le_zero_of_re_tsum_exp_le`).
  Suppose `Re Σ_t q_t e^{λ_t v} ≤ M` for `v ≥ 0`, `Re λ_t ≤ σ`, and `σ > 0` is itself an exponent.
  Then `Re q_σ ≤ 0`. Along `s ↓ σ` the Abel means `(s − σ) ∫_0^∞ e^{−sv} Σ_t q_t e^{λ_t v} dv`
  tend to `q_σ`, while the bound makes their real parts at most `(s − σ) M/s`.
* **Excluding the real exponents first** (`evenCoeff_eq_zero_of_lag_nonneg`). Let `δ*` be the
  largest real right exponent. Landau's theorem at level `δ*`
  (`evenCoeff_eq_zero_of_difference_nonneg_above`) removes every exponent to its right. Then `δ*`
  is the top, and its positive coefficient contradicts the one-sided bound. With no real right
  exponent left, Landau at level `0` removes the rest.

**One parameter decides the line** (`onLine_iff_lag_twoBump_nonneg_of_lt_one`) for every tempered
configuration with zeros in `Re ρ < 1`, and every width at which `h_w` vanishes at no off-line
zero.

**GRH** (`grh_iff_lag_primeWindow_nonneg`). For every primitive `χ` modulo `q > 1`, all but
countably many widths `w ∈ (0, ½ log 2)`, and every `V ≥ 0`, all nontrivial zeros of `L(s, χ)`
lie on the critical line iff the twisted window functional of `κ_w(t + v/2) − κ_w(t − v/2)` is
nonnegative at every lag `v ≥ V`. Each lag is one real inequality on the twisted primes of one
dyadic window, whether or not `L(s, χ)` has real zeros.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Real zeros carry positive weight -/

/-- **Real zeros carry positive weight at the center `0`.** -/
theorem re_evenCoeff_modScaledBump_zero_pos (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) {x : ℂ}
    (hx : (1 / 2 + x) ∈ Z.carrier) (him : x.im = 0) :
    0 < (evenCoeff Z (modScaledBump w 0) x).re := by
  have hxc : conj x = x := Complex.ext (by simp) (by simp [him])
  rw [evenCoeff_modScaledBump_zero Z hw hx, hxc, Set.indicator_of_mem hx]
  set h := paperFT (scaledBump w) (-(I * x)) with hh
  have hreal : conj h = h := by
    rw [hh, conj_paperFT_scaledBump, ← paperFT_scaledBump_neg w (conj (-(I * x)))]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, hxc]
    ring
  have hne : h ≠ 0 := by
    have hx' : -(I * x) = ((-x.re : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [him]
    have h1 := norm_paperFT_scaledBump_I_mul_ge hw (-x.re)
    have h2 : (0 : ℝ) < ∫ u, weilBump u := weilBump.integral_pos
    intro h0
    rw [← hx', ← hh, h0, norm_zero] at h1
    have : 0 < 4 * w * (Real.exp (-(w * |-x.re|)) * ∫ u, weilBump u) := by positivity
    linarith
  have hhre : h = (h.re : ℂ) := Complex.ext rfl (by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    simp; linarith)
  have hre0 : h.re ≠ 0 := fun h0 => hne (by rw [hhre, h0, Complex.ofReal_zero])
  have hm : (1 : ℝ) ≤ Z.mult (1 / 2 + x) := by exact_mod_cast Z.one_le_mult _ hx
  rw [hhre, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have : 0 < h.re ^ 2 := by positivity
  nlinarith

/-! ### A positive real top cannot hide under a one-sided bound -/

/-- **A positive real top cannot hide under a one-sided bound.** Let `Σ_t |q_t| < ∞`,
`Re λ_t ≤ σ` with `σ > 0`, and let `σ = λ_{t₁}` be an exponent with `t₁` unique. If
`Re Σ_t q_t e^{λ_t v} ≤ M` for all `v ≥ 0`, then `Re q_{t₁} ≤ 0`. -/
theorem re_le_zero_of_re_tsum_exp_le {ι : Type*} [Countable ι] {lam q : ι → ℂ}
    (hq : Summable fun t => ‖q t‖) {σ : ℝ} (hσ : 0 < σ) (hA : ∀ t, (lam t).re ≤ σ) (t₁ : ι)
    (h₁ : lam t₁ = σ) (hinj : ∀ t, lam t = lam t₁ → t = t₁) {M : ℝ}
    (hM : ∀ v : ℝ, 0 ≤ v → (∑' t, q t * cexp (lam t * v)).re ≤ M) : (q t₁).re ≤ 0 := by
  classical
  -- the Abel means tend to `q_{t₁}`
  have hlimG : Tendsto (fun s : ℝ => ((s : ℂ) - σ) * resolventSum lam q s) (𝓝[>] σ)
      (𝓝 (q t₁)) := by
    have hrw : ∀ s : ℝ, ((s : ℂ) - σ) * resolventSum lam q s =
        ∑' t, q t * (((s : ℂ) - σ) / ((s : ℂ) - lam t)) := fun s => by
      rw [resolventSum, ← tsum_mul_left]
      exact tsum_congr fun t => by ring
    simp_rw [hrw]
    rw [← tsum_ite_eq t₁ q]
    refine tendsto_tsum_of_dominated_convergence hq (fun t => ?_) ?_
    · by_cases ht : t = t₁
      · subst ht
        rw [if_pos rfl]
        have : ∀ᶠ s : ℝ in 𝓝[>] σ, q t * (((s : ℂ) - σ) / ((s : ℂ) - lam t)) = q t := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          have hne : (s : ℂ) - σ ≠ 0 := by
            rw [sub_ne_zero]; exact_mod_cast (ne_of_gt (show σ < s from hs))
          rw [h₁, div_self hne, mul_one]
        exact tendsto_const_nhds.congr' (this.mono fun s h => h.symm)
      · rw [if_neg ht]
        have hne : (σ : ℂ) - lam t ≠ 0 := sub_ne_zero.mpr fun h => ht (hinj t (h₁.trans h).symm)
        have h1 : Tendsto (fun s : ℝ => ((s : ℂ) - σ) / ((s : ℂ) - lam t)) (𝓝 σ)
            (𝓝 ((((σ : ℝ) : ℂ) - σ) / ((σ : ℂ) - lam t))) :=
          ((Complex.continuous_ofReal.tendsto σ).sub tendsto_const_nhds).div
            ((Complex.continuous_ofReal.tendsto σ).sub tendsto_const_nhds) hne
        simpa using ((h1.const_mul (q t)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with s hs t
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [norm_div]
      have hpos : 0 < s - σ := by linarith [show σ < s from hs]
      have hnum : ‖(s : ℂ) - σ‖ = s - σ := by
        rw [show (s : ℂ) - σ = ((s - σ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hpos]
      have hden : s - σ ≤ ‖(s : ℂ) - lam t‖ := by
        have := Complex.re_le_norm ((s : ℂ) - lam t)
        simp only [Complex.sub_re, Complex.ofReal_re] at this
        linarith [hA t]
      rw [hnum, div_le_one₀ (hpos.trans_le hden)]
      exact hden
  -- the Abel means have real part at most `(s − σ) M / s`
  have hbound : ∀ s : ℝ, σ < s →
      (((s : ℂ) - σ) * resolventSum lam q s).re ≤ (s - σ) * (M / s) := by
    intro s hs
    have hs0 : 0 < s := hσ.trans hs
    set G : ℝ → ℂ := fun u => ∑' t, q t * cexp (lam t * u) with hG
    have hL : ∫ u in Ioi (0 : ℝ), G u * cexp (-(s : ℂ) * u) = resolventSum lam q s :=
      integral_tsum_exp_mul_exp_neg hq (A := σ) hA (s := s) (by simpa using hs)
    have hGn : ∀ u : ℝ, 0 ≤ u → ‖G u‖ ≤ (∑' t, ‖q t‖) * Real.exp (σ * u) := fun u hu => by
      rw [hG, ← tsum_mul_right]
      refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun t => ?_) ?_
        (hq.mul_right _))
      · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => by
          rw [norm_mul, Complex.norm_exp]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact mul_le_mul_of_nonneg_right (hA t) hu)) (norm_nonneg _)) (hq.mul_right _)
      · rw [norm_mul, Complex.norm_exp]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
          exact mul_le_mul_of_nonneg_right (hA t) hu)) (norm_nonneg _)
      · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun t => by
          rw [norm_mul, Complex.norm_exp]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
            simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
            exact mul_le_mul_of_nonneg_right (hA t) hu)) (norm_nonneg _)) (hq.mul_right _)
    have hint : IntegrableOn (fun u : ℝ => G u * cexp (-(s : ℂ) * u)) (Ioi 0) := by
      have hdom : IntegrableOn (fun u : ℝ => (∑' t, ‖q t‖) * Real.exp ((σ - s) * u)) (Ioi 0) :=
        (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
      refine hdom.mono' ?_ ?_
      · have hcont : ContinuousOn G (Ioi 0) := fun x hx => by
          have hx0 : (0 : ℝ) < x := hx
          have hon : ContinuousOn G (Ioo 0 (x + 1)) :=
            continuousOn_tsum (u := fun t => ‖q t‖ * Real.exp (σ * (x + 1)))
              (fun t => by fun_prop) (hq.mul_right _) fun t u hu => by
                rw [norm_mul, Complex.norm_exp]
                refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
                simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
                  sub_zero]
                have hu0 : 0 < u := hu.1
                have hu1 : u < x + 1 := hu.2
                nlinarith [hA t]
          exact (hon.continuousAt (Ioo_mem_nhds hx0 (by linarith))).continuousWithinAt
        exact (hcont.mul (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(s : ℂ) * u).re = -s * u := by simp
        rw [hre]
        calc ‖G u‖ * Real.exp (-s * u) ≤ (∑' t, ‖q t‖) * Real.exp (σ * u) * Real.exp (-s * u) :=
              mul_le_mul_of_nonneg_right (hGn u (le_of_lt hu)) (Real.exp_pos _).le
          _ = (∑' t, ‖q t‖) * Real.exp ((σ - s) * u) := by
              rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [← hL, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im, sub_zero, zero_mul, sub_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have hre := integral_re hint
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    have hpt : ∀ u ∈ Ioi (0 : ℝ), (G u * cexp (-(s : ℂ) * u)).re ≤ M * Real.exp (-s * u) := by
      intro u hu
      have e : cexp (-(s : ℂ) * u) = ((Real.exp (-s * u) : ℝ) : ℂ) := by
        rw [Complex.ofReal_exp]; push_cast; ring_nf
      rw [e, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (hM u (le_of_lt hu)) (Real.exp_pos _).le
    calc ∫ u in Ioi (0 : ℝ), (G u * cexp (-(s : ℂ) * u)).re
        ≤ ∫ u in Ioi (0 : ℝ), M * Real.exp (-s * u) :=
          setIntegral_mono_on hint.re ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M)
            measurableSet_Ioi hpt
      _ = M / s := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero]
          field_simp
  -- conclude
  have hlim0 : Tendsto (fun s : ℝ => (s - σ) * (M / s)) (𝓝[>] σ) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => (s - σ) * (M / s)) (𝓝 σ) (𝓝 ((σ - σ) * (M / σ))) :=
      ((continuous_id.sub continuous_const).tendsto σ).mul
        (tendsto_const_nhds.div (continuous_id.tendsto σ) hσ.ne')
    simpa using this.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto ((Complex.continuous_re.tendsto _).comp hlimG) hlim0
    (eventually_nhdsWithin_of_forall fun s hs => hbound s hs)

/-! ### One parameter decides the line, real zeros included -/

/-- **No right exponent survives.** For a tempered configuration with zeros in `Re ρ < 1`, if
the tests `κ_w(t + v/2) − κ_w(t − v/2)` are Weil nonnegative at every lag `v ≥ V`, then
`D(z) = 0` for every exponent with `Re z > 0`. -/
theorem evenCoeff_eq_zero_of_lag_nonneg (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w) {V : ℝ}
    (hm : ∀ v : ℝ, V ≤ v → 0 ≤ (Z.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re)
    {z : ℂ} (hz : 0 < z.re) : evenCoeff Z (modScaledBump w 0) z = 0 := by
  classical
  set b := modScaledBump w 0 with hbdef
  have hb : ContDiff ℝ 2 b := contDiff_modScaledBump_two w 0
  have hbs := modScaledBump_support hw 0
  -- the real right exponents
  set R := (finite_evenCoeff_line Z b 0).toFinset.filter fun x => 0 < x.re with hR
  have hmemR : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.im = 0 → 0 < x.re → x ∈ R := fun x hx him hre =>
    Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr ⟨hx, him⟩, hre⟩
  have hhalf : ∀ x : ℂ, evenCoeff Z b x ≠ 0 → x.re < 1 / 2 := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · have := hlt _ h; simp at this; linarith
    · have := hlt _ h; simp at this; linarith
  by_cases hRne : R.Nonempty
  · exfalso
    obtain ⟨x₀, hx₀R, hmax⟩ := R.exists_max_image Complex.re hRne
    obtain ⟨hx₀L, hx₀pos⟩ := Finset.mem_filter.mp hx₀R
    obtain ⟨hx₀, hx₀im⟩ := (Set.Finite.mem_toFinset _).mp hx₀L
    -- Landau above `δ* = Re x₀`
    have habove : ∀ y : ℂ, x₀.re < y.re → evenCoeff Z b y = 0 := fun y hy =>
      evenCoeff_eq_zero_of_difference_nonneg_above Z hZ hb hbs hx₀pos.le (hhalf x₀ hx₀)
        (fun x hx him => by
          by_contra h
          push Not at h
          exact absurd (hmax x (hmemR x hx him (hx₀pos.trans h))) (not_le.mpr h)) hm hy
    -- the positive coefficient at `δ*` contradicts the one-sided bound
    set ι : Set ℂ := {z | evenCoeff Z b z ≠ 0} with hι
    haveI : Countable ι := (countable_evenCoeff_support Z b).to_subtype
    have hD0 : Summable fun z : ℂ => ‖evenCoeff Z b z‖ := by
      have h0 := (two_re_lagStructure_eq Z hZ hb hbs 0).1.norm
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
      exact h0
    have hle : ∀ t : ι, ((t : ℂ)).re ≤ x₀.re := fun t => by
      by_contra h
      exact t.2 (habove _ (not_le.mp h))
    obtain ⟨M, -, hMb⟩ := exists_two_re_lagStructure_le Z hZ hb hbs hm
    have hx₀eq : (x₀ : ℂ) = (x₀.re : ℂ) := Complex.ext (by simp) (by simp [hx₀im])
    have hrep : ∀ v : ℝ, 0 ≤ v →
        (∑' t : ι, evenCoeff Z b t * cexp ((t : ℂ) * v)).re ≤ M := fun v hv => by
      have hsub : Function.support (fun z : ℂ => evenCoeff Z b z * cexp (z * v)) ⊆ ι :=
        fun z hz h0 => hz (show evenCoeff Z b z * cexp (z * v) = 0 by rw [h0, zero_mul])
      rw [tsum_subtype_eq_of_support_subset hsub, ← (two_re_lagStructure_eq Z hZ hb hbs v).2,
        Complex.ofReal_re]
      exact hMb v hv
    have hpos := re_evenCoeff_modScaledBump_zero_pos Z hw
      ((mem_of_evenCoeff_ne_zero hx₀).elim id fun h => by
        rwa [show conj x₀ = x₀ from Complex.ext (by simp) (by simp [hx₀im])] at h) hx₀im
    have hnonpos := re_le_zero_of_re_tsum_exp_le (ι := ι) (lam := fun t => (t : ℂ))
      (q := fun t => evenCoeff Z b t) (hD0.subtype ι) hx₀pos hle ⟨x₀, hx₀⟩ hx₀eq
      (fun t ht => Subtype.ext ht) hrep
    exact absurd hnonpos (not_le.mpr hpos)
  · exact evenCoeff_eq_zero_of_difference_nonneg_above Z hZ hb hbs le_rfl (by norm_num)
      (fun x hx him => by
        by_contra h
        push Not at h
        exact hRne ⟨x, hmemR x hx him h⟩) hm hz

/-- **One parameter decides the line.** Let `Z` be tempered with all zeros in `Re ρ < 1`, `w > 0`
a width whose transform vanishes at no `γ_ρ` of an off-line zero, and `V ∈ ℝ`. All zeros lie on
the critical line iff `Re W ≥ 0` on every test `κ_w(t + v/2) − κ_w(t − v/2)`, `v ≥ V`. -/
theorem onLine_iff_lag_twoBump_nonneg_of_lt_one (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) (V : ℝ) :
    (∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) ↔ ∀ v : ℝ, V ≤ v →
      0 ≤ (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re := by
  refine ⟨fun hon _ _ => weil_nonneg_of_onLine Z hon _, fun h ρ hρ => ?_⟩
  by_contra hre
  obtain ⟨t, ht, -⟩ := exists_rightZero_of_offLine Z hρ hre
  have hgt : paperFT (scaledBump w) (gammaOf t) ≠ 0 := hgood t ht.1 (by linarith [ht.2])
  have hz : (1 / 2 + (t - 1 / 2)) ∈ Z.carrier := by rw [add_sub_cancel]; exact ht.1
  have hzre : 0 < (t - 1 / 2).re := by simp; linarith [ht.2]
  have h0 := evenCoeff_eq_zero_of_lag_nonneg Z hZ hlt hw h hzre
  rw [evenCoeff_modScaledBump_zero Z hw hz] at h0
  have hγt : -(I * (t - 1 / 2)) = gammaOf t := by
    rw [gammaOf, Complex.div_I]; ring
  rw [hγt] at h0
  have hm : (1 : ℝ) ≤ Z.mult (1 / 2 + (t - 1 / 2)) := by exact_mod_cast Z.one_le_mult _ hz
  have hsum : ((Z.mult (1 / 2 + (t - 1 / 2)) : ℂ) +
      Z.carrier.indicator (fun ρ => (Z.mult ρ : ℂ)) (1 / 2 + conj (t - 1 / 2))) ≠ 0 := by
    intro h1
    have h2 := congrArg Complex.re h1
    by_cases hc : (1 / 2 + conj (t - 1 / 2)) ∈ Z.carrier
    · rw [Set.indicator_of_mem hc, Complex.add_re, Complex.natCast_re, Complex.natCast_re,
        Complex.zero_re] at h2
      linarith [(Nat.cast_nonneg (Z.mult (1 / 2 + conj (t - 1 / 2))) : (0 : ℝ) ≤ _)]
    · rw [Set.indicator_of_notMem hc, Complex.add_re, Complex.natCast_re, Complex.zero_re] at h2
      linarith
  exact (mul_ne_zero hsum (pow_ne_zero 2 hgt)) h0

/-! ### GRH for Dirichlet `L`-functions -/

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **GRH by one inequality per dyadic window.** Let `χ` be primitive modulo `q > 1`. For all but
countably many widths `w ∈ (0, ½ log 2)` and every `V ≥ 0`, every nontrivial zero of `L(s, χ)`
lies on the critical line iff the twisted window functional of the autocorrelation of
`κ_w(t + v/2) − κ_w(t − v/2)` is nonnegative at every lag `v ≥ V`. -/
theorem grh_iff_lag_primeWindow_nonneg (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      ∀ V : ℝ, 0 ≤ V →
        ((∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
          ∀ v : ℝ, V ≤ v →
            0 ≤ (lagPrimeWindowRHSchi (ThmE.parity χ) q (ThmE.coeff χ) v w
              (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
                (twoBump (modScaledBump w 0) v (-1)))).re) := by
  refine ⟨_, countable_bad_widths (ThmE.LZeros (ThmE.LSeam_of hq hprim)),
    fun w hw hw2 hwE V hV => ?_⟩
  have hgood : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re ≠ 1 / 2 →
      paperFT (scaledBump w) (gammaOf ρ) ≠ 0 := fun ρ hρ hre h0 => hwE ⟨hw, ρ, hρ, hre, h0⟩
  have hlt : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re < 1 := fun ρ hρ => by
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    exact h.2
  refine (onLine_iff_lag_twoBump_nonneg_of_lt_one _ (temperedConfig_LZeros hq hprim) hlt hw hgood
    V).trans (forall_congr' fun v => imp_congr_right fun hv => ?_)
  have h := tsum_vonMangoldt_twoBump_eq_window (modScaledBump_support hw 0) hw2 (hV.trans hv)
    (-1) (ThmE.coeff χ) fun n => starRingEnd ℂ (ThmE.coeff χ n)
  beta_reduce at h
  rw [LZeros_W_eq_literatureRHSchi hq hprim (f := twoBump (modScaledBump w 0) v (-1))
    (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support hw 0)) v (-1)), ThmE.literatureRHSchi, lagPrimeWindowRHSchi, h]

end GaloisForLFunctions.SquareRootThreshold
