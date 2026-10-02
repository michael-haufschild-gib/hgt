import GaloisForLFunctions.RHTower.WeilProducerReciprocalZetaAtomOrder
import GaloisForLFunctions.HTGeometry.HalfPlaneMellinAnalytic
import GaloisForLFunctions.RHTower.WeilProducerMobiusCancellation
import GaloisForLFunctions.HTGeometry.LogCesaroAbelMellin

/-!
# Möbius resonance happens only at atoms of mass one

Let `lam` be a full-cone producer, `μ_lam` its Möbius function (the Dirichlet coefficients of
`1/F_lam`) and `μ_lam({a})` the atom of its boundary measure at `a`.

**Theorem** (`boundaryMeasure_le_one_of_twistedMobius_log`).  Suppose the twisted normalized Möbius
sums grow logarithmically at frequency `a`:

`Σ_{n ≤ x} μ_lam(n) n^{−½−ia} = c·log x + o(log x)`.

Then `μ_lam({a}) ≤ 1`.  If moreover `μ_lam({a}) < 1`, then `c = 0`.

So the Möbius function of a producer resonates at the critical scale only at atoms of mass exactly
one.  Fractional atoms are Möbius-silent, and atoms of mass `> 1` forbid logarithmic growth.  The
prime-number error resonates at every atom (MUST-658).  For `lam = Λ` (a producer under RH) the
atoms are zero multiplicities, and `c` is the residue `1/ζ'(½+ia)` at a simple zero.

**Proof.**
1. *Mellin.*  On real `β > 2`, Abel summation gives
   `Σ μ_lam(n) n^{−½−ia−β} = β ∫_1^∞ A(x) x^{−β−1} dx`, with `A` the twisted partial sum.
2. *Continuation.*  `β² ∫_1^∞ A(x) x^{−β−1} dx` is holomorphic on `Re β > 0`, because
   `A = O(log x)`.  `β G(½+ia+β)` is holomorphic there too, and the two agree on `β > 2`.
3. *Abel.*  The logarithmic Abelian theorem gives `b G(½+b+ia) → c` as `b → 0⁺`.
4. *Radial law.*  `|G(½+b+ia)| = b^{−μ_lam{a}+o(1)}` (MUST-660) forces both conclusions.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

/-- The twisted normalized Möbius partial sum `Σ_{1 ≤ n ≤ x} μ_lam(n) n^{−½−ia}`. -/
def twistedMobiusSum (lam : ℕ → ℝ) (a x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
    producerMobius (fun n => if 2 ≤ n then lam n else 0) k * (k : ℂ) ^ (-((1 / 2 : ℂ) + a * I))

theorem measurable_twistedMobiusSum (lam : ℕ → ℝ) (a : ℝ) : Measurable (twistedMobiusSum lam a) :=
  (measurable_from_nat (f := fun m : ℕ => ∑ k ∈ Finset.Icc 1 m,
    producerMobius (fun n => if 2 ≤ n then lam n else 0) k *
      (k : ℂ) ^ (-((1 / 2 : ℂ) + a * I)))).comp Nat.measurable_floor

theorem norm_twistedMobiusSum_le {lam : ℕ → ℝ} (a : ℝ) {x X : ℝ} (hxX : x ≤ X) :
    ‖twistedMobiusSum lam a x‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊X⌋₊,
      ‖producerMobius (fun n => if 2 ≤ n then lam n else 0) k‖ := by
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k hk => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.floor_le_floor hxX)) fun _ _ _ => norm_nonneg _)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hk0]
  simp only [neg_add_rev, add_re, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, neg_zero, zero_add]
  norm_num
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk1) (by norm_num)

theorem intervalIntegrable_twistedMobiusSum (lam : ℕ → ℝ) (a : ℝ) (y : ℝ) :
    IntervalIntegrable (twistedMobiusSum lam a) volume 1 y := by
  rcases le_total 1 y with h | h
  · refine (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr ?_
    refine Measure.integrableOn_of_bounded (M := ∑ k ∈ Finset.Icc 1 ⌊y⌋₊,
      ‖producerMobius (fun n => if 2 ≤ n then lam n else 0) k‖) measure_Icc_lt_top.ne
      (measurable_twistedMobiusSum lam a).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx =>
      norm_twistedMobiusSum_le a hx.2)
  · refine ((intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr ?_).symm
    refine Measure.integrableOn_of_bounded (M := ∑ k ∈ Finset.Icc 1 ⌊(1 : ℝ)⌋₊,
      ‖producerMobius (fun n => if 2 ≤ n then lam n else 0) k‖) measure_Icc_lt_top.ne
      (measurable_twistedMobiusSum lam a).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx =>
      norm_twistedMobiusSum_le a hx.2)

/-- **Möbius resonance only at unit atoms.**  If the twisted normalized Möbius sums of a full-cone
producer satisfy `Σ_{n ≤ x} μ_lam(n) n^{−½−ia} = c log x + o(log x)`, then `μ_lam({a}) ≤ 1`, and
`c = 0` whenever `μ_lam({a}) < 1`. -/
theorem boundaryMeasure_le_one_of_twistedMobius_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a : ℝ) {c : ℂ}
    (hA : Tendsto (fun x : ℝ => twistedMobiusSum lam a x / (Real.log x : ℂ)) atTop (𝓝 c)) :
    (boundaryMeasure hW).real {a} ≤ 1 ∧ ((boundaryMeasure hW).real {a} < 1 → c = 0) := by
  set lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0 with hlam'
  set μl : ℕ → ℂ := producerMobius lam' with hμl
  obtain ⟨G, hGd, hGL, hrad⟩ := tendsto_log_norm_reciprocalZeta_div_log hW
  have hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam' n| / (n : ℝ) ^ σ :=
    (herglotzWeilPositive_of_weilPositiveFull hW).summable
  set w₀ : ℂ := (1 / 2 : ℂ) + a * I with hw₀
  set f : ℕ → ℂ := fun k => μl k * (k : ℂ) ^ (-w₀) with hf
  set A : ℝ → ℂ := twistedMobiusSum lam a with hAdef
  have hfnorm : ∀ k : ℕ, ‖f k‖ ≤ ‖μl k‖ := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hf, hμl, producerMobius_zero]
    · rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      rw [show (k : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl, Complex.norm_cpow_eq_rpow_re_of_pos hk0]
      simp only [hw₀, neg_add_rev, add_re, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, neg_zero, zero_add]
      norm_num
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hk) (by norm_num)
  -- Step 1: the Mellin identity on real `β > 2`
  have hmellin : ∀ β : ℝ, 2 < β → (β : ℂ) * GaloisForLFunctions.HTGeometry.halfPlaneMellin A
      ((β : ℂ) + 1) = G (w₀ + β) := by
    intro β hβ
    obtain ⟨S, hS⟩ : ∃ S, HasSum (fun n : ℕ => ‖μl n‖ * (n : ℝ) ^ (-(2 : ℝ))) S :=
      ⟨_, (summable_norm_producerMobius_mul_rpow hsum).hasSum⟩
    have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖f k‖) =O[atTop]
        fun n : ℕ => (n : ℝ) ^ (2 : ℝ) := by
      refine Asymptotics.IsBigO.of_bound S (Eventually.of_forall fun n => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ ∑ k ∈ Finset.Icc 1 n,
            ‖μl k‖ * (k : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (2 : ℝ) := by
            refine Finset.sum_le_sum fun k hk => ?_
            obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
            have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
            have : 1 ≤ (k : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (2 : ℝ) := by
              rw [Real.rpow_neg hk0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
              exact Real.rpow_le_rpow hk0.le (by exact_mod_cast hkn) (by norm_num)
            calc ‖f k‖ ≤ ‖μl k‖ := hfnorm k
              _ ≤ ‖μl k‖ * ((k : ℝ) ^ (-(2 : ℝ)) * (n : ℝ) ^ (2 : ℝ)) :=
                  le_mul_of_one_le_right (norm_nonneg _) this
              _ = _ := by ring
        _ = (∑ k ∈ Finset.Icc 1 n, ‖μl k‖ * (k : ℝ) ^ (-(2 : ℝ))) * (n : ℝ) ^ (2 : ℝ) := by
            rw [Finset.sum_mul]
        _ ≤ S * (n : ℝ) ^ (2 : ℝ) := mul_le_mul_of_nonneg_right
            (hS.summable.sum_le_tsum _ (fun _ _ => by positivity) |>.trans_eq hS.tsum_eq)
            (by positivity)
    have hL := LSeries_eq_mul_integral' f (r := 2) (by norm_num) (s := (β : ℂ))
      (by simpa using hβ) hO
    have hre : 1 < (w₀ + β).re := by simp [hw₀]; linarith
    obtain ⟨hμs, hμ⟩ := LSeries_producerMobius hsum hre
    have hLS : LSeries f β = G (w₀ + β) := by
      rw [hGL _ hre, ← hμ, LSeries, LSeries]
      refine tsum_congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hf]
        simp only
        rw [Complex.cpow_add _ _ (by exact_mod_cast hn), Complex.cpow_neg, div_eq_mul_inv,
          div_eq_mul_inv, mul_inv]
        ring
    rw [← hLS, hL]
    rfl
  -- Step 2: holomorphy on `Re β > 0`
  set U : Set ℂ := {β : ℂ | 0 < β.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  set H₁ : ℂ → ℂ := fun β => β ^ 2 * GaloisForLFunctions.HTGeometry.halfPlaneMellin A (β + 1)
    with hH₁
  set H₂ : ℂ → ℂ := fun β => β * G (w₀ + β) with hH₂
  have hlogbd : ∀ ρ : ℝ, 0 < ρ → ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ‖A x‖ ≤ x ^ ρ * Real.log x := by
    intro ρ hρ
    have h1 : ∀ᶠ x in atTop, ‖A x / (Real.log x : ℂ)‖ ≤ ‖c‖ + 1 :=
      hA.norm.eventually (ge_mem_nhds (by linarith))
    have h2 : ∀ᶠ x : ℝ in atTop, ‖c‖ + 1 ≤ x ^ ρ :=
      (tendsto_rpow_atTop hρ).eventually (eventually_ge_atTop _)
    obtain ⟨X, hX⟩ := eventually_atTop.mp ((h1.and h2).and (eventually_gt_atTop (1 : ℝ)))
    refine ⟨max X 2, le_trans one_le_two (le_max_right _ _), fun x hx => ?_⟩
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hX x (le_trans (le_max_left _ _) hx)
    have hl : 0 < Real.log x := Real.log_pos hx3
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, div_le_iff₀ hl] at hx1
    exact hx1.trans (mul_le_mul_of_nonneg_right hx2 hl.le)
  have hH₁d : DifferentiableOn ℂ H₁ U := by
    intro β hβ
    have hβ' : 0 < β.re := hβ
    obtain ⟨X, hX1, hXb⟩ := hlogbd (β.re / 2) (by positivity)
    have hmel := GaloisForLFunctions.HTGeometry.differentiableAt_halfPlaneMellin hX1
      (fun y _ => intervalIntegrable_twistedMobiusSum lam a y) hXb
      (w := β + 1) (by simp; linarith)
    exact ((differentiableAt_id.pow 2).mul (hmel.comp β
      (differentiableAt_id.add_const 1))).differentiableWithinAt
  have hH₂d : DifferentiableOn ℂ H₂ U := by
    intro β hβ
    have hβ' : 0 < β.re := hβ
    have hre : 1 / 2 < (w₀ + β).re := by simp [hw₀]; linarith
    have hGa : DifferentiableAt ℂ G (w₀ + β) :=
      hGd.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre)
    exact (differentiableAt_id.mul (hGa.comp β (differentiableAt_id.const_add w₀))).differentiableWithinAt
  -- Step 3: identity theorem along real points
  have heqU : EqOn H₁ H₂ U := by
    set z₀ : ℂ := (7 / 2 : ℂ) with hz₀
    have hz₀U : z₀ ∈ U := by show (0 : ℝ) < (z₀).re; norm_num [hz₀]
    refine (hH₁d.analyticOnNhd hUopen).eqOn_of_preconnected_of_frequently_eq
      (hH₂d.analyticOnNhd hUopen) hUconn hz₀U ?_
    set u : ℕ → ℂ := fun n => ((7 / 2 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ) with hu
    have hz₀r : z₀ = ((7 / 2 : ℝ) : ℂ) := by rw [hz₀]; push_cast; ring
    have hut : Tendsto u atTop (𝓝[≠] z₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h2 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
          tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
        have h0 : Tendsto (fun n : ℕ => (7 / 2 : ℝ) + 1 / ((n : ℝ) + 2)) atTop (𝓝 (7 / 2)) := by
          have := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop h2
          simpa using (tendsto_const_nhds (x := (7 / 2 : ℝ))).add this
        rw [hz₀r]
        exact (Complex.continuous_ofReal.tendsto _).comp h0
      · show u n ≠ z₀
        rw [hz₀r, hu]
        intro h
        have h' := Complex.ofReal_injective h
        have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
        linarith
    refine hut.frequently (Frequently.of_forall fun n => ?_)
    have hβ : 2 < (7 / 2 + 1 / ((n : ℝ) + 2) : ℝ) := by
      have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by positivity
      linarith
    simp only [hH₁, hH₂, hu]
    rw [sq, mul_assoc, hmellin _ hβ]
  -- Step 4: the Abelian limit
  have habel := GaloisForLFunctions.LogCesaro.tendsto_sq_mul_integral_of_tendsto_div_log
    ((measurable_twistedMobiusSum lam a).aestronglyMeasurable)
    (fun X => ⟨_, fun x hx => norm_twistedMobiusSum_le a hx.2⟩) hA
  have hlim : Tendsto (fun b : ℝ => (b : ℂ) * G (w₀ + b)) (𝓝[>] 0) (𝓝 c) := by
    refine habel.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with b hb
    have hb0 : 0 < b := hb
    have h1 := heqU (show (0 : ℝ) < ((b : ℂ)).re by simpa using hb0)
    simp only [hH₁, hH₂] at h1
    rw [← h1]
    push_cast
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans one_pos hx)
    rw [Complex.ofReal_cpow hx0]
    push_cast
    ring_nf
    exact mul_comm _ _
  -- Step 5: the radial law
  have hpt : ∀ b : ℝ, w₀ + b = (((1 / 2 + b : ℝ)) : ℂ) + a * I := fun b => by
    rw [hw₀]; push_cast; ring
  have hr := hrad a
  have hLtop : Tendsto (fun b : ℝ => Real.log (1 / b)) (𝓝[>] 0) atTop := by
    refine (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun b => ?_
    simp [one_div, Real.log_inv]
  have hnorm := hlim.norm
  constructor
  · by_contra hgt
    push Not at hgt
    set δ : ℝ := ((boundaryMeasure hW).real {a} - 1) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hev1 : ∀ᶠ b in 𝓝[>] (0 : ℝ),
        1 + δ < Real.log ‖G ((((1 / 2 + b : ℝ)) : ℂ) + a * I)‖ / Real.log (1 / b) :=
      hr.eventually (lt_mem_nhds (by rw [hδ]; linarith))
    have hev2 : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), ‖((b : ℝ) : ℂ) * G (w₀ + b)‖ < ‖c‖ + 1 :=
      hnorm.eventually (gt_mem_nhds (by linarith))
    have hev3 : ∀ᶠ b in 𝓝[>] (0 : ℝ), Real.log (‖c‖ + 1) < δ * Real.log (1 / b) :=
      (hLtop.const_mul_atTop hδ0).eventually (eventually_gt_atTop _)
    obtain ⟨b, ⟨⟨h1, h2⟩, h3⟩, hb⟩ :=
      ((hev1.and hev2).and hev3).and self_mem_nhdsWithin |>.exists
    have hb0 : 0 < b := hb
    have hLb : 0 < Real.log (1 / b) := by
      have := hLtop.eventually (eventually_gt_atTop (0 : ℝ))
      by_contra hneg
      push Not at hneg
      have hc1 : 0 ≤ Real.log (‖c‖ + 1) := Real.log_nonneg (by linarith [norm_nonneg c])
      nlinarith
    rw [lt_div_iff₀ hLb, ← hpt] at h1
    have hGpos : 0 < ‖G (w₀ + b)‖ := by
      by_contra h0
      push Not at h0
      have : ‖G (w₀ + b)‖ = 0 := le_antisymm h0 (norm_nonneg _)
      rw [this, Real.log_zero] at h1
      nlinarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0] at h2
    have hlog2 : Real.log (b * ‖G (w₀ + b)‖) < Real.log (‖c‖ + 1) :=
      Real.log_lt_log (by positivity) h2
    rw [Real.log_mul hb0.ne' hGpos.ne', show Real.log b = -Real.log (1 / b) by
      rw [one_div, Real.log_inv, neg_neg]] at hlog2
    nlinarith
  · intro hlt
    set δ : ℝ := (1 - (boundaryMeasure hW).real {a}) / 2 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hev1 : ∀ᶠ b in 𝓝[>] (0 : ℝ),
        Real.log ‖G ((((1 / 2 + b : ℝ)) : ℂ) + a * I)‖ / Real.log (1 / b) < 1 - δ :=
      hr.eventually (gt_mem_nhds (by rw [hδ]; linarith))
    have hbound : Tendsto (fun b : ℝ => b ^ δ) (𝓝[>] 0) (𝓝 0) := by
      have h := (Real.continuousAt_rpow_const 0 δ (Or.inr hδ0.le)).tendsto
      rw [Real.zero_rpow hδ0.ne'] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hsq : Tendsto (fun b : ℝ => ‖(b : ℂ) * G (w₀ + b)‖) (𝓝[>] 0) (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
      filter_upwards [hev1, self_mem_nhdsWithin, hLtop.eventually (eventually_gt_atTop 0)]
        with b h1 hb hLb
      have hb0 : 0 < b := hb
      rw [div_lt_iff₀ hLb, ← hpt] at h1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
      rcases (norm_nonneg (G (w₀ + b))).eq_or_lt with h0 | hpos
      · rw [← h0, mul_zero]; positivity
      · have : Real.log (b * ‖G (w₀ + b)‖) ≤ Real.log (b ^ δ) := by
          rw [Real.log_mul hb0.ne' hpos.ne', Real.log_rpow hb0, show Real.log b =
            -Real.log (1 / b) by rw [one_div, Real.log_inv, neg_neg]]
          nlinarith
        exact (Real.log_le_log_iff (by positivity) (by positivity)).mp this
    have := tendsto_nhds_unique hnorm hsq
    exact norm_eq_zero.mp this

end RHTower.WeilSpectral

end
