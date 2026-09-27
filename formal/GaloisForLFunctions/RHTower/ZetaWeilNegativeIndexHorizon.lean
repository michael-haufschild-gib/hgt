import GaloisForLFunctions.RHTower.ZetaWeilFormHeightReduction

/-!
# The negative index of the level-`a` Weil form of `ζ` is bounded by its off-line pairs below `exp(O(e^a))`

Bombieri showed that, if `ζ` has finitely many zeros off the critical line, the number of negative
eigenvalues of Weil's quadratic functional on a large enough truncation is the number of off-line
pairs.  This module proves an unconditional, level-wise upper bound with an explicit horizon.

**Theorem** (`zeta_weil_negative_index_le`).  There is `A₀` such that for every level `a > 0`
and threshold `0 < ε ≤ 1`, every finite-dimensional space `V` of polar-constrained `C²` tests
supported in `[-a, a]` with `Re W(f, f) < -ε ∫|f|²` on `V ∖ {0}` satisfies
`dim V ≤ #{off-line pairs of ζ with |γ| ≤ H(A₀, a, ε)}`, where
`log H(A₀, a, ε) ≤ 7000 e^a + 7 log A₀ + 7 log(1/ε) + 150` (`log_inertiaHorizonHeight_le`).

Each off-line pair `{ρ, 1 - ρ̄}` contributes at most one negative square, whatever its multiplicity,
and pairs above the archimedean horizon contribute none.

**Proof.**
* **Node conditions** (`zeta_re_W_ge_neg_eps_of_nodes`).  If `h_f(x_ρ) = h_f(x̄_ρ)` at every off-line
  zero below `H`, then `Re W(f, f) ≥ -ε ∫|f|²`.  The splitting `W(f, f) = W(f, g) + (W(f, f) - W(f, g))`
  of `ZetaWeilFormHeightReduction` is used with kernel width `b = ε e^{-2E}/(8A₀)`.
  - The symbol side costs `E(4be^E)² ≤ ε/8` (`inertia_symbol_error_le`).
  - At an off-line zero below `H`, the node condition makes the summand `m_ρ|h_f(x_ρ)|² Re q_b(x_ρ)²`.
    Its phase error is at most `2b² m_ρ|h_f(x_ρ)|²` (`re_Wsummand_smoothedTest_ge_of_node`).
  - A plain Bessel bound with the unconditional density `A₀ log(H + 4)` below `H`
    (`offLineDensityBoundBelow_of_local_count`) sums the phase error to at most `ε/3`
    (`inertia_phase_error_le`).
  - The tail above `H` costs `ε/3` (`inertia_tail_le`).
* **Linear algebra.**  `f ↦ (h_f(x_ρ) - h_f(x̄_ρ))` over one representative `ρ` of each off-line pair
  below `H` (`offLinePairsBelow`) is injective on `V`: on its kernel the node conditions hold at
  every off-line zero below `H`, because `x_{1 - ρ̄} = x̄_ρ`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Node conditions: the smoothed zero side without depth hypotheses -/

/-- If `h_f(x_ρ) = h_f(x̄_ρ)`, the summand of `W(f, g)` at a zero of ordinate at most any height is
at least `-2b² m_ρ |h_f(x_ρ)|²`, and it is nonnegative on the critical line. -/
theorem re_Wsummand_smoothedTest_ge_of_node (Z : ZeroConfig) {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hnode : paperFT f (gammaOf ρ) = paperFT f (conj (gammaOf ρ))) :
    -(2 * b ^ 2 * (if ρ.re ≠ 1 / 2 then (Z.mult ρ : ℝ) * ‖paperFT f (gammaOf ρ)‖ ^ 2 else 0)) ≤
      (Z.Wsummand f (smoothedTest b f) ρ).re := by
  set A := paperFT f (gammaOf ρ) with hA
  set x := gammaOf ρ with hx
  obtain ⟨r, hr, -, -⟩ := kernelQ_real hb hb1 ρ.im
  have hst := Z.strip ρ hρ
  have hy : |ρ.re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  have hxγ : x - (ρ.im : ℂ) = I * ((1 / 2 - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hx, WeilEF.gammaOf_re]
    · simp [hx, WeilEF.gammaOf_im]
  have hnxγ : ‖x - (ρ.im : ℂ)‖ = |ρ.re - 1 / 2| := by
    rw [hxγ, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hlip := norm_kernelQ_sub_le hb hb1 (z₁ := x) (z₂ := (ρ.im : ℂ)) (by
    rw [hnxγ]; nlinarith [abs_nonneg (ρ.re - 1 / 2)])
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, mul_one] at hlip
  rw [hr, hnxγ] at hlip
  set d := kernelQ b x - r with hd
  have hqd : kernelQ b x = r + d := by rw [hd]; ring
  have hdn : ‖d‖ ≤ b := by
    refine hlip.trans ?_
    nlinarith [abs_nonneg (ρ.re - 1 / 2)]
  -- `Re (r + d)² ≥ -2|d|²`
  have hrec : -(2 * ‖d‖ ^ 2) ≤ ((kernelQ b x) ^ 2).re := by
    rw [hqd]
    have e : (((r : ℂ) + d) ^ 2).re = r ^ 2 + 2 * r * d.re + (d.re ^ 2 - d.im ^ 2) := by
      simp [sq, Complex.mul_re]; ring
    rw [e]
    have hre : |d.re| ≤ ‖d‖ := Complex.abs_re_le_norm d
    have hn2 : ‖d‖ ^ 2 = d.re ^ 2 + d.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [sq_nonneg (r + d.re), abs_nonneg d.re, sq_abs d.re]
  rw [Wsummand_smoothedTest Z hb.le hf hfc, ← hnode, ← hA]
  have hAA : A * conj A = ((‖A‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [show ((Z.mult ρ : ℕ) : ℂ) = ((Z.mult ρ : ℝ) : ℂ) by push_cast; rfl, hAA,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hA2 := sq_nonneg ‖A‖
  split_ifs with hoff
  · have h1 : -(2 * b ^ 2) ≤ ((kernelQ b x) ^ 2).re := by
      have : ‖d‖ ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdn 2
      linarith
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hm hA2)
    nlinarith
  · push Not at hoff
    have hd0 : d = 0 := by
      have : ‖d‖ ≤ 0 := by
        refine hlip.trans ?_
        rw [hoff, sub_self, abs_zero, mul_zero]
      exact norm_le_zero_iff.mp this
    have hc : ((kernelQ b x) ^ 2).re = r ^ 2 := by
      rw [hqd, hd0, add_zero, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hc]
    simp only [mul_zero, neg_zero]
    positivity

/-- The local count gives off-line density at most `A₀ log(H + 4)` below height `H`. -/
theorem offLineDensityBoundBelow_of_local_count (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {H : ℝ} (hH : 0 ≤ H) :
    OffLineDensityBoundBelow Z H (A₀ * Real.log (H + 4)) := by
  classical
  intro t s hs
  have hlog0 : 0 ≤ A₀ * Real.log (H + 4) :=
    mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
  rw [← Finset.sum_filter_add_sum_filter_not s (fun ρ : Z.carrier => |(ρ : ℂ).im| ≤ H)]
  have hnot : ∑ ρ ∈ s.filter (fun ρ : Z.carrier => ¬|(ρ : ℂ).im| ≤ H), lowOffMult Z H ρ = 0 :=
    Finset.sum_eq_zero fun ρ hρ => by
      unfold lowOffMult; rw [if_neg (Finset.mem_filter.mp hρ).2]
  rw [hnot, add_zero]
  set s' := s.filter (fun ρ : Z.carrier => |(ρ : ℂ).im| ≤ H) with hs'
  rcases s'.eq_empty_or_nonempty with he | ⟨ρ₀, hρ₀⟩
  · rw [he, Finset.sum_empty]; exact hlog0
  have hρ₀' := Finset.mem_filter.mp hρ₀
  have hwin := hs ρ₀ hρ₀'.1
  have ht : |t| ≤ H + 1 := by
    have := abs_le.mp hρ₀'.2
    rw [abs_le]; constructor <;> linarith [hwin.1, hwin.2]
  have hcount : ∑ ρ ∈ s', (Z.mult ρ : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
    refine le_trans ?_ (hloc t)
    have hfin : (Z.window t (t + 1)).Finite := Z.finite_window t (t + 1)
    unfold ZeroConfig.N
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hsub : s'.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
      intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨ρ, hρ, rfl⟩ := hx
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ.2, hs ρ (Finset.mem_filter.mp hρ).1⟩
    have h := Finset.sum_le_sum_of_subset (f := Z.mult) hsub
    rw [Finset.sum_map] at h
    exact_mod_cast h
  calc ∑ ρ ∈ s', lowOffMult Z H ρ ≤ ∑ ρ ∈ s', (Z.mult ρ : ℝ) := by
        refine Finset.sum_le_sum fun ρ _ => ?_
        unfold lowOffMult; split_ifs
        · exact offLineMult_le Z ρ
        · exact Nat.cast_nonneg _
    _ ≤ A₀ * Real.log (|t| + 3) := hcount
    _ ≤ A₀ * Real.log (H + 4) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact Real.log_le_log (by positivity) (by linarith)

/-- **The smoothed zero side under node conditions.**  If `h_f(x_ρ) = h_f(x̄_ρ)` at every off-line
zero of ordinate at most `H`, then
`Re W(f, g) ≥ -[2b² · (K_{⌈a⌉}(½)/4) · 10 A₀ log(H+4)/c₀ · ∫|f|² + e^a(∫|f|)² e·400²/b⁶ ·
24A₀ log 3/(1 + H)]`: no depth or density hypothesis is needed. -/
theorem re_W_smoothedTest_ge_of_nodes (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {H a b : ℝ} (hH : 0 ≤ H)
    (ha : 0 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) {f : ℝ → ℂ} (hf : Continuous f)
    (hfs : ∀ u, f u ≠ 0 → |u| ≤ a)
    (hnode : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → ρ.re ≠ 1 / 2 →
      paperFT f (gammaOf ρ) = paperFT f (conj (gammaOf ρ))) :
    -(2 * b ^ 2 * (plateauGramConst ⌈a⌉₊ (1 / 2) / 4 * (10 * (A₀ * Real.log (H + 4))) /
          unitWeightFloor * ∫ u, ‖f u‖ ^ 2) +
        Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) *
          (24 * A₀ * Real.log 3 / (1 + H))) ≤
      (Z.W f (smoothedTest b f)).re := by
  set J := ⌈a⌉₊ with hJ
  have hfsJ : ∀ u, f u ≠ 0 → |u| ≤ J := fun u hu => (hfs u hu).trans (Nat.le_ceil a)
  have hfc : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hfs
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  set B2 := plateauGramConst J (1 / 2) / 4 * (10 * (A₀ * Real.log (H + 4))) / unitWeightFloor * F
    with hB2
  set K := Real.exp a * (∫ u, ‖f u‖) ^ 2 * (Real.exp 1 * 400 ^ 2 / b ^ 6) with hK
  set T := 24 * A₀ * Real.log 3 / (1 + H) with hT
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hDlow := offLineDensityBoundBelow_of_local_count Z hA₀ hloc hH
  have hηlow : ∀ ρ ∈ Z.carrier, |ρ.im| ≤ H → |ρ.re - 1 / 2| ≤ 1 / 2 := fun ρ hρ _ => by
    have hst := Z.strip ρ hρ
    rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  have f2 : ∀ s : Finset Z.carrier, ∑ ρ ∈ s, lowPhaseErr Z H f (fun σ => gammaOf σ) ρ ≤ B2 :=
    fun s => sum_low_off_mult_norm_sq_le Z hηlow hDlow J hf hfsJ (fun σ => gammaOf σ)
      (fun σ => WeilEF.gammaOf_re _)
      (fun σ => by rw [WeilEF.gammaOf_im, abs_sub_comm]) s
  obtain ⟨hs4, t4⟩ := highTailErr_summable_le Z hA₀ hloc hH
  have hK0 : 0 ≤ K := by positivity
  have hB20 : 0 ≤ B2 := by
    have := plateauGramConst_nonneg J (1 / 2)
    have := unitWeightFloor_pos
    have : 0 ≤ Real.log (H + 4) := Real.log_nonneg (by linarith)
    have : 0 ≤ A₀ := by linarith
    positivity
  have hT0 : 0 ≤ T := by
    have : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have : 0 ≤ A₀ := by linarith
    positivity
  set E : Z.carrier → ℝ := fun ρ => 2 * b ^ 2 * lowPhaseErr Z H f (fun σ => gammaOf σ) ρ +
    K * highTailErr Z H ρ with hE
  have hE0 : ∀ ρ, 0 ≤ E ρ := fun ρ => by
    have := lowPhaseErr_nonneg Z H f (fun σ => gammaOf σ) ρ
    have := highTailErr_nonneg Z H ρ
    simp only [hE]; positivity
  have hEfin : ∀ s : Finset Z.carrier, ∑ ρ ∈ s, E ρ ≤ 2 * b ^ 2 * B2 + K * T := by
    intro s
    have h4 : ∑ ρ ∈ s, highTailErr Z H ρ ≤ T :=
      (hs4.sum_le_tsum s fun ρ _ => highTailErr_nonneg Z H ρ).trans t4
    simp only [hE]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left (f2 s) (by positivity : (0 : ℝ) ≤ 2 * b ^ 2)
    have := mul_le_mul_of_nonneg_left h4 hK0
    linarith
  have hEs : Summable E := summable_of_sum_le hE0 hEfin
  have hEt := hEs.tsum_le_of_sum_le hEfin
  have hterm : ∀ ρ : Z.carrier, -E ρ ≤ (Z.Wsummand f (smoothedTest b f) ρ).re := by
    intro ρ
    simp only [hE]
    unfold lowPhaseErr highTailErr
    by_cases hlow : |(ρ : ℂ).im| ≤ H
    · rw [if_pos hlow, mul_zero, add_zero]
      have hnode' : paperFT f (gammaOf ρ) = paperFT f (conj (gammaOf ρ)) := by
        by_cases hon : (ρ : ℂ).re = 1 / 2
        · have : conj (gammaOf (ρ : ℂ)) = gammaOf ρ := by
            apply Complex.ext
            · simp [WeilEF.gammaOf_re]
            · simp [WeilEF.gammaOf_im, hon]
          rw [this]
        · exact hnode ρ ρ.2 hlow hon
      have h := re_Wsummand_smoothedTest_ge_of_node Z hb hb1 hf hfc ρ.2 hnode'
      by_cases hon : (ρ : ℂ).re = 1 / 2
      · have hand : ¬(|(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2) := fun h => h.2 hon
        rw [if_neg hand]
        simp only [ne_eq, hon, not_true_eq_false, if_false, mul_zero, neg_zero] at h ⊢
        exact h
      · rw [if_pos ⟨hlow, hon⟩]
        rw [if_pos hon] at h
        exact h
    · have hand : ¬(|(ρ : ℂ).im| ≤ H ∧ (ρ : ℂ).re ≠ 1 / 2) := fun h => hlow h.1
      rw [if_neg hand, if_neg hlow, mul_zero, zero_add]
      have h := re_Wsummand_smoothedTest_ge_high Z ha hb hb1 hf hfs ρ.2
      have e : K * ((Z.mult (ρ : ℂ) : ℝ) / (1 + |(ρ : ℂ).im|) ^ 4) =
          (Z.mult (ρ : ℂ) : ℝ) * (Real.exp a * (∫ u, ‖f u‖) ^ 2) *
            (Real.exp 1 * 400 ^ 2 / (b ^ 6 * (1 + |(ρ : ℂ).im|) ^ 4)) := by
        rw [hK]; field_simp
      rw [e]
      exact h
  have hbound : 2 * b ^ 2 * B2 + K * T =
      2 * b ^ 2 * (plateauGramConst ⌈a⌉₊ (1 / 2) / 4 * (10 * (A₀ * Real.log (H + 4))) /
          unitWeightFloor * F) + K * T := by rw [hB2, hJ]
  by_cases hW : Summable (fun ρ : Z.carrier => Z.Wsummand f (smoothedTest b f) ρ)
  · rw [ZeroConfig.W, Complex.re_tsum hW]
    have hre : Summable (fun ρ : Z.carrier => (Z.Wsummand f (smoothedTest b f) ρ).re) :=
      (Complex.hasSum_re hW.hasSum).summable
    have hle := Summable.tsum_le_tsum hterm hEs.neg hre
    rw [tsum_neg] at hle
    linarith
  · rw [ZeroConfig.W, tsum_eq_zero_of_not_summable hW, Complex.zero_re]
    have : 0 ≤ 2 * b ^ 2 * B2 + K * T := by positivity
    linarith

/-! ### Parameters at threshold `ε` -/

/-- The kernel width `b = ε e^{-2E}/(8A₀)` at threshold `ε`. -/
def inertiaKernelWidth (A₀ a ε : ℝ) : ℝ := ε * Real.exp (-(2 * zetaHorizonExp a)) / (8 * A₀)

/-- The inertia horizon `H = 6(a+1)e^{a+1}·400²·24A₀ log 3/(ε b⁶)`. -/
def inertiaHorizonHeight (A₀ a ε : ℝ) : ℝ :=
  3 * (2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3)) /
    (ε * inertiaKernelWidth A₀ a ε ^ 6)

theorem inertiaKernelWidth_pos {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (hε : 0 < ε) :
    0 < inertiaKernelWidth A₀ a ε := by
  unfold inertiaKernelWidth; have : 0 < A₀ := by linarith
  positivity

theorem inertiaKernelWidth_le {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (hε1 : ε ≤ 1) :
    inertiaKernelWidth A₀ a ε ≤ 1 / 8 := by
  unfold inertiaKernelWidth
  have he : Real.exp (-(2 * zetaHorizonExp a)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [zetaHorizonExp_pos a])
  rw [div_le_iff₀ (by linarith)]
  have := mul_le_mul hε1 he (Real.exp_pos _).le zero_le_one
  nlinarith

theorem inertiaHorizonHeight_pos {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) (hε : 0 < ε) :
    0 < inertiaHorizonHeight A₀ a ε := by
  unfold inertiaHorizonHeight
  have := inertiaKernelWidth_pos (a := a) hA₀ hε
  have : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have : 0 < A₀ := by linarith
  positivity

/-- The symbol error at threshold `ε` is at most `ε/8`. -/
theorem inertia_symbol_error_le {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    horizonExponent (Real.exp (2 * (a + 2))) *
      (4 * inertiaKernelWidth A₀ a ε * Real.exp (horizonExponent (Real.exp (2 * (a + 2))))) ^ 2 ≤
        ε / 8 := by
  have hE : zetaHorizonExp a = horizonExponent (Real.exp (2 * (a + 2))) := rfl
  rw [← hE]
  set E := zetaHorizonExp a
  have hE0 := zetaHorizonExp_pos a
  have hA0 : 0 < A₀ := by linarith
  have e : 4 * inertiaKernelWidth A₀ a ε * Real.exp E = ε * Real.exp (-E) / (2 * A₀) := by
    unfold inertiaKernelWidth
    rw [show 4 * (ε * Real.exp (-(2 * E)) / (8 * A₀)) * Real.exp E =
      ε * (Real.exp (-(2 * E)) * Real.exp E) / (2 * A₀) by ring, ← Real.exp_add]
    ring_nf
  rw [e]
  have hexp : E * Real.exp (-E) ^ 2 ≤ 1 / 2 := by
    rw [← Real.exp_nat_mul]
    have h := Real.add_one_le_exp (2 * E)
    have hpos := Real.exp_pos (2 * E)
    have e2 : Real.exp ((2 : ℕ) * -E) = 1 / Real.exp (2 * E) := by
      rw [one_div, ← Real.exp_neg]; congr 1; push_cast; ring
    rw [e2, mul_one_div, div_le_iff₀ hpos]
    linarith
  have hA2 : 1 ≤ (2 * A₀) ^ 2 := by nlinarith
  calc E * (ε * Real.exp (-E) / (2 * A₀)) ^ 2
      = ε ^ 2 * (E * Real.exp (-E) ^ 2) / (2 * A₀) ^ 2 := by ring
    _ ≤ ε ^ 2 * (1 / 2) / (2 * A₀) ^ 2 := by gcongr
    _ ≤ ε ^ 2 * (1 / 2) / 4 := by
        gcongr
        nlinarith
    _ ≤ ε / 8 := by nlinarith

/-! ### The phase error at threshold `ε` -/

theorem zetaHorizonExp_eq (a : ℝ) : zetaHorizonExp a = 10 + 68 * Real.exp (a + 2) := by
  unfold zetaHorizonExp horizonExponent
  rw [show 2 * (a + 2) = (a + 2) + (a + 2) by ring, Real.exp_add,
    Real.sqrt_mul_self (Real.exp_pos _).le]

theorem zetaHorizonExp_ge {a : ℝ} (ha : 0 ≤ a) :
    214 ≤ zetaHorizonExp a ∧ 68 * Real.exp (a + 2) ≤ zetaHorizonExp a ∧
      2 * a + 20 ≤ zetaHorizonExp a := by
  rw [zetaHorizonExp_eq]
  have h := Real.add_one_le_exp (a + 2)
  refine ⟨by nlinarith, by linarith, by nlinarith⟩

/-- `(2J + 1) e^{J+1} ≤ E²` for `J = ⌈a⌉`. -/
theorem plateau_growth_le {a : ℝ} (ha : 0 ≤ a) :
    (2 * (⌈a⌉₊ : ℝ) + 1) * Real.exp (⌈a⌉₊ + 1) ≤ zetaHorizonExp a ^ 2 := by
  obtain ⟨h1, h2, -⟩ := zetaHorizonExp_ge ha
  have hJ : (⌈a⌉₊ : ℝ) < a + 1 := Nat.ceil_lt_add_one ha
  have he : Real.exp ((⌈a⌉₊ : ℝ) + 1) ≤ Real.exp (a + 2) := Real.exp_le_exp.mpr (by linarith)
  have h3 := Real.add_one_le_exp (a + 2)
  have hJ3 : 2 * (⌈a⌉₊ : ℝ) + 1 ≤ zetaHorizonExp a := by nlinarith
  have he' : Real.exp ((⌈a⌉₊ : ℝ) + 1) ≤ zetaHorizonExp a := by nlinarith [Real.exp_pos (a + 2)]
  have h0 : 0 ≤ 2 * (⌈a⌉₊ : ℝ) + 1 := by positivity
  calc (2 * (⌈a⌉₊ : ℝ) + 1) * Real.exp (⌈a⌉₊ + 1) ≤ zetaHorizonExp a * zetaHorizonExp a :=
        mul_le_mul hJ3 he' (Real.exp_pos _).le (by linarith)
    _ = zetaHorizonExp a ^ 2 := by ring

/-- `H(A₀, a, ε) ≤ (8A₀)⁷ e^{13E}/ε⁷`. -/
theorem inertiaHorizonHeight_le {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) (hε : 0 < ε) :
    inertiaHorizonHeight A₀ a ε ≤ (8 * A₀) ^ 7 * Real.exp (13 * zetaHorizonExp a) / ε ^ 7 := by
  obtain ⟨h1, -, h3⟩ := zetaHorizonExp_ge ha
  set E := zetaHorizonExp a with hE
  have hA0 : 0 < A₀ := by linarith
  have hK : 3 * (2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3)) ≤
      Real.exp E * (8 * A₀) := by
    obtain ⟨h5, h4, h6, -, he2, he1⟩ := exp_numeric_bounds
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num); linarith
    have h2a : 2 * (a + 1) ≤ Real.exp (a + 1) := by
      have h1' := mul_le_mul (Real.add_one_le_exp a) he1 (by norm_num) (Real.exp_pos a).le
      have : Real.exp (a + 1) = Real.exp a * Real.exp 1 := Real.exp_add _ _
      linarith
    have h400 : (400 : ℝ) ^ 2 ≤ Real.exp 12 := by
      rw [show (12 : ℝ) = 6 + 6 by norm_num, Real.exp_add]; nlinarith
    have hE' : 2 * a + 20 ≤ E := h3
    have hprod : Real.exp (a + 1) * Real.exp a * Real.exp 1 * Real.exp 12 * Real.exp 4 =
        Real.exp (2 * a + 18) := by
      simp only [← Real.exp_add]; ring_nf
    have hb : Real.exp (2 * a + 18) ≤ Real.exp E := Real.exp_le_exp.mpr (by linarith)
    have hpos : ∀ x, 0 < Real.exp x := Real.exp_pos
    calc 3 * (2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3))
        ≤ 3 * (Real.exp (a + 1) * Real.exp a * Real.exp 1 * Real.exp 12 * (Real.exp 4 * A₀ * 2)) := by
          gcongr
      _ = Real.exp (2 * a + 18) * (6 * A₀) := by rw [← hprod]; ring
      _ ≤ Real.exp E * (8 * A₀) := by
          apply mul_le_mul hb (by linarith) (by positivity) (hpos _).le
  have hb6 : 1 / (ε * inertiaKernelWidth A₀ a ε ^ 6) = (8 * A₀) ^ 6 * Real.exp (12 * E) / ε ^ 7 := by
    unfold inertiaKernelWidth
    rw [← hE, div_pow, mul_pow, ← Real.exp_nat_mul]
    have e : Real.exp ((6 : ℕ) * -(2 * E)) = 1 / Real.exp (12 * E) := by
      rw [one_div, ← Real.exp_neg]; congr 1; push_cast; ring
    rw [e]
    field_simp
  have hH : inertiaHorizonHeight A₀ a ε ≤ (8 * A₀) ^ 7 * Real.exp (13 * E) / ε ^ 7 := by
    unfold inertiaHorizonHeight
    rw [div_eq_mul_one_div, hb6]
    have e13 : Real.exp (13 * E) = Real.exp E * Real.exp (12 * E) := by
      rw [← Real.exp_add]; ring_nf
    rw [e13]
    have : 0 < (8 * A₀) ^ 6 * Real.exp (12 * E) / ε ^ 7 := by positivity
    calc 3 * (2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 * (24 * A₀ * Real.log 3)) *
          ((8 * A₀) ^ 6 * Real.exp (12 * E) / ε ^ 7)
        ≤ Real.exp E * (8 * A₀) * ((8 * A₀) ^ 6 * Real.exp (12 * E) / ε ^ 7) :=
          mul_le_mul_of_nonneg_right hK this.le
      _ = (8 * A₀) ^ 7 * (Real.exp E * Real.exp (12 * E)) / ε ^ 7 := by ring
  exact hH

/-- `ε log(H + 4) ≤ 70 E A₀` at the inertia horizon. -/
theorem eps_mul_log_inertiaHorizon_le {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ε * Real.log (inertiaHorizonHeight A₀ a ε + 4) ≤ 70 * zetaHorizonExp a * A₀ := by
  obtain ⟨h1, -, h3⟩ := zetaHorizonExp_ge ha
  set E := zetaHorizonExp a with hE
  have hA0 : 0 < A₀ := by linarith
  have hHpos := inertiaHorizonHeight_pos (a := a) hA₀ ha hε
  have hH := inertiaHorizonHeight_le hA₀ ha hε
  rw [← hE] at hH
  -- `H ≥ 1`, so `H + 4 ≤ 5H`
  have hH1 : 1 ≤ inertiaHorizonHeight A₀ a ε := by
    unfold inertiaHorizonHeight
    have hb := inertiaKernelWidth_le (a := a) hA₀ hε1
    have hb0 := inertiaKernelWidth_pos (a := a) hA₀ hε
    have hl3 : 1 ≤ Real.log 3 := by
      have := Real.add_one_le_exp (1 : ℝ)
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hb6 : inertiaKernelWidth A₀ a ε ^ 6 ≤ 1 := pow_le_one₀ hb0.le (by linarith)
    have hden : ε * inertiaKernelWidth A₀ a ε ^ 6 ≤ 1 := by nlinarith [pow_pos hb0 6]
    rw [le_div_iff₀ (by positivity), one_mul]
    have : 1 ≤ 2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 := by
      have := Real.one_le_exp ha
      have := Real.one_le_exp (zero_le_one : (0 : ℝ) ≤ 1)
      have : (1 : ℝ) ≤ 2 * (a + 1) := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
        _ ≤ 2 * (a + 1) * Real.exp a * Real.exp 1 * 400 ^ 2 := by gcongr; norm_num
    have : 1 ≤ 24 * A₀ * Real.log 3 := by nlinarith
    nlinarith
  have hlog : Real.log (inertiaHorizonHeight A₀ a ε + 4) ≤
      Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E + 7 * Real.log (1 / ε) := by
    have h5 : inertiaHorizonHeight A₀ a ε + 4 ≤ 5 * ((8 * A₀) ^ 7 * Real.exp (13 * E) / ε ^ 7) := by
      linarith
    have hpos : 0 < (8 * A₀) ^ 7 * Real.exp (13 * E) / ε ^ 7 := by positivity
    calc Real.log (inertiaHorizonHeight A₀ a ε + 4)
        ≤ Real.log (5 * ((8 * A₀) ^ 7 * Real.exp (13 * E) / ε ^ 7)) :=
          Real.log_le_log (by linarith) h5
      _ = Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E + 7 * Real.log (1 / ε) := by
          rw [Real.log_mul (by norm_num) hpos.ne', Real.log_div (by positivity) (by positivity),
            Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_pow,
            Real.log_exp, one_div, Real.log_inv]
          push_cast; ring
  have hεlog : ε * Real.log (1 / ε) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (x := 1 / ε) (by positivity)
    have : ε * (1 / ε - 1) ≤ 1 := by rw [mul_sub, mul_one_div_cancel hε.ne']; linarith
    nlinarith
  have hl8 : Real.log (8 * A₀) ≤ 8 * A₀ := by
    have := Real.log_le_sub_one_of_pos (x := 8 * A₀) (by positivity); linarith
  have hl5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (x := (5 : ℝ)) (by norm_num); linarith
  have hlog0 : 0 ≤ Real.log (8 * A₀) := Real.log_nonneg (by linarith)
  have hl1 : 0 ≤ Real.log (1 / ε) := by
    rw [one_div, Real.log_inv]; linarith [Real.log_nonpos hε.le hε1]
  calc ε * Real.log (inertiaHorizonHeight A₀ a ε + 4)
      ≤ ε * (Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E + 7 * Real.log (1 / ε)) :=
        mul_le_mul_of_nonneg_left hlog hε.le
    _ ≤ 4 + 7 * (8 * A₀) + 13 * E + 7 := by
        have e : ε * (Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E + 7 * Real.log (1 / ε)) =
            ε * (Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E) + 7 * (ε * Real.log (1 / ε)) := by
          ring
        rw [e]
        have hin : 0 ≤ Real.log 5 + 7 * Real.log (8 * A₀) + 13 * E := by
          have := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num); nlinarith
        have := mul_le_of_le_one_left hin hε1
        nlinarith
    _ ≤ 70 * E * A₀ := by nlinarith

/-- `7700 E³ e^{-4E} ≤ 1/3` for `E ≥ 214`. -/
theorem cube_mul_exp_neg_le {E : ℝ} (hE : 214 ≤ E) :
    7700 * E ^ 3 * Real.exp (-(4 * E)) ≤ 1 / 3 := by
  have h := Real.pow_div_factorial_le_exp (x := 4 * E) (by linarith) 5
  have hpos := Real.exp_pos (4 * E)
  have hexp : Real.exp (-(4 * E)) = 1 / Real.exp (4 * E) := by rw [Real.exp_neg, one_div]
  rw [hexp, mul_one_div, div_le_iff₀ hpos]
  have hf : ((5 : ℕ).factorial : ℝ) = 120 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hE0 : 0 < E := by linarith
  have h2 : 7700 * E ^ 3 * 3 ≤ (4 * E) ^ 5 / 120 := by
    rw [le_div_iff₀ (by norm_num)]
    have : 7700 * 3 * 120 ≤ 1024 * E ^ 2 := by nlinarith
    nlinarith [pow_pos hE0 3]
  linarith

/-- The phase error at threshold `ε` is at most `(ε/3)∫|f|²`. -/
theorem inertia_phase_error_le {A₀ a ε F : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hF : 0 ≤ F) :
    2 * inertiaKernelWidth A₀ a ε ^ 2 * (plateauGramConst ⌈a⌉₊ (1 / 2) / 4 *
        (10 * (A₀ * Real.log (inertiaHorizonHeight A₀ a ε + 4))) / unitWeightFloor * F) ≤
      ε / 3 * F := by
  obtain ⟨h214, -, -⟩ := zetaHorizonExp_ge ha
  set E := zetaHorizonExp a with hE
  set L := Real.log (inertiaHorizonHeight A₀ a ε + 4) with hL
  have hεL := eps_mul_log_inertiaHorizon_le hA₀ ha hε hε1
  rw [← hE, ← hL] at hεL
  have hgrow := plateau_growth_le ha
  rw [← hE] at hgrow
  have hcube := cube_mul_exp_neg_le h214
  have hc₀ := unitWeightFloor_ge
  have hc₀0 := unitWeightFloor_pos
  have hA0 : 0 < A₀ := by linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [inertiaHorizonHeight_pos (a := a) hA₀ ha hε])
  have hG : plateauGramConst ⌈a⌉₊ (1 / 2) / 4 =
      (2 * (⌈a⌉₊ : ℝ) + 1) * Real.exp (⌈a⌉₊ + 1) * 168 := by
    unfold plateauGramConst; ring_nf
  have hb2 : inertiaKernelWidth A₀ a ε ^ 2 = ε ^ 2 * Real.exp (-(4 * E)) / (64 * A₀ ^ 2) := by
    unfold inertiaKernelWidth
    rw [← hE, div_pow, mul_pow, ← Real.exp_nat_mul]
    congr 2
    · congr 1; push_cast; ring
    · ring
  rw [hG, hb2]
  set P := (2 * (⌈a⌉₊ : ℝ) + 1) * Real.exp (⌈a⌉₊ + 1) with hP
  have hP0 : 0 ≤ P := by positivity
  have hX := Real.exp_pos (-(4 * E))
  -- rewrite as `ε · (εL) · e^{-4E} P · 1680/(32 A₀ c₀) · F`
  have e : 2 * (ε ^ 2 * Real.exp (-(4 * E)) / (64 * A₀ ^ 2)) *
      (P * 168 * (10 * (A₀ * L)) / unitWeightFloor * F) =
      ε * ((ε * L) * (Real.exp (-(4 * E)) * P) * 1680 / (32 * A₀ * unitWeightFloor)) * F := by
    field_simp; ring
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ hF
  refine mul_le_mul_of_nonneg_left ?_ hε.le
  rw [div_le_iff₀ (by positivity)]
  have h1 : (ε * L) * (Real.exp (-(4 * E)) * P) ≤ (70 * E * A₀) * (Real.exp (-(4 * E)) * E ^ 2) := by
    apply mul_le_mul hεL (mul_le_mul_of_nonneg_left hgrow hX.le) (by positivity) (by positivity)
  have h2 : (70 * E * A₀) * (Real.exp (-(4 * E)) * E ^ 2) * 1680 =
      A₀ * (7700 * E ^ 3 * Real.exp (-(4 * E))) * (70 * 1680 / 7700) := by ring
  have h3 : A₀ * (7700 * E ^ 3 * Real.exp (-(4 * E))) * (70 * 1680 / 7700) ≤
      A₀ * (1 / 3) * (70 * 1680 / 7700) := by
    gcongr
  have h4 : A₀ * (1 / 3) * (70 * 1680 / 7700) ≤ 1 / 3 * (32 * A₀ * unitWeightFloor) := by
    nlinarith
  nlinarith

/-- The tail at the inertia horizon is at most `(ε/3)∫|f|²`. -/
theorem inertia_tail_le {A₀ a ε F N₁ : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 < a) (hε : 0 < ε)
    (hN : N₁ ^ 2 ≤ 2 * a * F) :
    Real.exp a * N₁ ^ 2 * (Real.exp 1 * 400 ^ 2 / inertiaKernelWidth A₀ a ε ^ 6) *
      (24 * A₀ * Real.log 3 / (1 + inertiaHorizonHeight A₀ a ε)) ≤ ε / 3 * F := by
  have hb := inertiaKernelWidth_pos (a := a) hA₀ hε
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA0 : 0 < A₀ := by linarith
  set Q := Real.exp a * (Real.exp 1 * 400 ^ 2 / inertiaKernelWidth A₀ a ε ^ 6) *
    (24 * A₀ * Real.log 3) with hQ
  have hQ0 : 0 < Q := by positivity
  have hH : inertiaHorizonHeight A₀ a ε = 6 * (a + 1) * Q / ε := by
    unfold inertiaHorizonHeight; rw [hQ]; field_simp; ring
  have hH0 : 0 < 1 + inertiaHorizonHeight A₀ a ε := by rw [hH]; positivity
  have e : Real.exp a * N₁ ^ 2 * (Real.exp 1 * 400 ^ 2 / inertiaKernelWidth A₀ a ε ^ 6) *
      (24 * A₀ * Real.log 3 / (1 + inertiaHorizonHeight A₀ a ε)) =
      Q * N₁ ^ 2 / (1 + inertiaHorizonHeight A₀ a ε) := by rw [hQ]; field_simp
  rw [e, div_le_iff₀ hH0, hH]
  have h1 : Q * N₁ ^ 2 ≤ Q * (2 * a * F) := mul_le_mul_of_nonneg_left hN hQ0.le
  have hF : 0 ≤ F := by nlinarith [sq_nonneg N₁]
  have e2 : ε / 3 * F * (1 + 6 * (a + 1) * Q / ε) = ε / 3 * F + 2 * (a + 1) * Q * F := by
    field_simp; ring
  rw [e2]
  have : 0 ≤ ε / 3 * F := by positivity
  nlinarith

/-- **Node conditions give ε-positivity.**  Let `A₀` be a local-count constant for `ζ`.  If a
polar-constrained `C²` test `f` on `[-a, a]` satisfies `h_f(x_ρ) = h_f(x̄_ρ)` at every off-line zero
of ordinate at most `H(A₀, a, ε)`, then `Re W(f, f) ≥ -ε ∫|f|²`. -/
theorem zeta_re_W_ge_neg_eps_of_nodes {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0) (hm : paperFT f (-(I / 2)) = 0)
    (hnode : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ inertiaHorizonHeight A₀ a ε →
      ρ.re ≠ 1 / 2 → paperFT f (gammaOf ρ) = paperFT f (conj (gammaOf ρ))) :
    -(ε * ∫ u, ‖f u‖ ^ 2) ≤ (zetaZeroConfig.W f f).re := by
  set b := inertiaKernelWidth A₀ a ε with hbdef
  set H := inertiaHorizonHeight A₀ a ε with hHdef
  have hb := inertiaKernelWidth_pos (a := a) hA₀ hε
  have hb1 : b ≤ 1 := (inertiaKernelWidth_le (a := a) hA₀ hε1).trans (by norm_num)
  have hH0 : 0 ≤ H := (inertiaHorizonHeight_pos hA₀ ha.le hε).le
  have hfs' : ∀ u, f u ≠ 0 → |u| ≤ a := fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))
  set F := ∫ u, ‖f u‖ ^ 2 with hF
  have hF0 : 0 ≤ F := integral_nonneg fun _ => sq_nonneg _
  have hsym := re_W_sub_W_smoothedTest_ge hb hb1 hf hfs hp hm
  have hzero := re_W_smoothedTest_ge_of_nodes zetaZeroConfig hA₀ hloc hH0 ha.le hb hb1
    hf.continuous hfs' hnode
  have hsymE := inertia_symbol_error_le (a := a) hA₀ hε hε1
  have hsym' : -(ε / 8 * F) ≤ (zetaZeroConfig.W f f - zetaZeroConfig.W f (smoothedTest b f)).re := by
    refine le_trans ?_ hsym
    have := mul_le_mul_of_nonneg_right hsymE hF0
    linarith
  have hN : (∫ u, ‖f u‖) ^ 2 ≤ 2 * a * F :=
    sq_integral_norm_le_of_abs_support hf.continuous ha fun x hx => by
      by_contra h; exact absurd (hfs' x h) (not_le.mpr hx)
  have htail := inertia_tail_le (ε := ε) hA₀ ha hε hN
  have hphase := inertia_phase_error_le hA₀ ha.le hε hε1 hF0
  have hsplit : (zetaZeroConfig.W f f).re = (zetaZeroConfig.W f (smoothedTest b f)).re +
      (zetaZeroConfig.W f f - zetaZeroConfig.W f (smoothedTest b f)).re := by
    rw [Complex.sub_re]; ring
  rw [hsplit]
  nlinarith

/-! ### The finite-level inertia bound -/

/-- The off-line zeros with `β > ½` and `|γ| ≤ H`: one representative of each off-line pair
`{ρ, 1 - ρ̄}` below height `H`. -/
def offLinePairsBelow (Z : ZeroConfig) (H : ℝ) : Finset ℂ :=
  (Z.finite_window (-H - 1) H).toFinset.filter (fun ρ => 1 / 2 < ρ.re ∧ |ρ.im| ≤ H)

theorem mem_offLinePairsBelow {Z : ZeroConfig} {H : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hre : 1 / 2 < ρ.re) (him : |ρ.im| ≤ H) : ρ ∈ offLinePairsBelow Z H := by
  unfold offLinePairsBelow
  rw [Finset.mem_filter, Set.Finite.mem_toFinset]
  refine ⟨⟨hρ, ?_, ?_⟩, hre, him⟩ <;> linarith [(abs_le.mp him).1, (abs_le.mp him).2]

theorem paperFT_add_of_compact {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    paperFT (f + g) z = paperFT f z + paperFT g z := by
  rw [paperFT_def, paperFT_def, paperFT_def, ← integral_add (integrable_mul_cexp hf hfc z)
    (integrable_mul_cexp hg hgc z)]
  congr 1 with u
  simp only [Pi.add_apply]
  ring

theorem paperFT_smul (c : ℂ) (f : ℝ → ℂ) (z : ℂ) : paperFT (c • f) z = c * paperFT f z := by
  rw [paperFT_def, paperFT_def, ← integral_const_mul]
  congr 1 with u
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The finite-level inertia bound for `ζ`.**  There is `A₀` such that for every level `a > 0`
and threshold `0 < ε ≤ 1`: every finite-dimensional space `V` of polar-constrained `C²` tests
supported in `[-a, a]` on which `Re W(f, f) < -ε ∫|f|²` for `f ≠ 0` has
`dim V ≤ #{off-line pairs of ζ with |γ| ≤ H(A₀, a, ε)}`, where
`log H(A₀, a, ε) ≤ 7000 e^a + 7 log A₀ + 7 log(1/ε) + 150` (`log_inertiaHorizonHeight_le`).

Each off-line pair contributes at most one negative square, whatever its multiplicity, and only
the pairs below the archimedean horizon contribute.

**Proof.**  The map `f ↦ (h_f(x_ρ) - h_f(x̄_ρ))_ρ` over the representatives `ρ` is injective on `V`.
On its kernel the node conditions hold at every off-line zero below `H`, since the reflected zero
has `x_{1-ρ̄} = x̄_ρ`, so `Re W(f, f) ≥ -ε ∫|f|²` (`zeta_re_W_ge_neg_eps_of_nodes`). -/
theorem zeta_weil_negative_index_le_of_local_count {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (zetaZeroConfig.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∀ a ε : ℝ, 0 < a → 0 < ε → ε ≤ 1 →
      ∀ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V →
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) →
      (∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)) →
      Module.finrank ℂ V ≤ (offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card := by
  intro a ε ha hε hε1 V hVfin hV hneg
  set S := offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε) with hS
  have hcont : ∀ f : V, Continuous (f : ℝ → ℂ) := fun f => (hV f f.2).1.continuous
  have hcomp : ∀ f : V, HasCompactSupport (f : ℝ → ℂ) := fun f =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hV f f.2).2.1
  let Λ : V →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun f ρ => paperFT (f : ℝ → ℂ) (gammaOf ρ) - paperFT (f : ℝ → ℂ) (conj (gammaOf ρ))
      map_add' := fun f g => by
        funext ρ
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [paperFT_add_of_compact (hcont f) (hcomp f) (hcont g) (hcomp g),
          paperFT_add_of_compact (hcont f) (hcomp f) (hcont g) (hcomp g)]
        ring
      map_smul' := fun c f => by
        funext ρ
        simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [paperFT_smul, paperFT_smul]
        ring }
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    rw [LinearMap.mem_ker] at hf
    by_contra hf0
    have hf0' : (f : ℝ → ℂ) ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨hfd, hfs, hp, hm⟩ := hV f f.2
    have hnode : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ inertiaHorizonHeight A₀ a ε →
        ρ.re ≠ 1 / 2 → paperFT (f : ℝ → ℂ) (gammaOf ρ) =
          paperFT (f : ℝ → ℂ) (conj (gammaOf ρ)) := by
      intro ρ hρ hH hoff
      have hΛ : ∀ σ : S, paperFT (f : ℝ → ℂ) (gammaOf σ) -
          paperFT (f : ℝ → ℂ) (conj (gammaOf σ)) = 0 := fun σ => congrFun hf σ
      rcases lt_or_gt_of_ne hoff with hlt | hgt
      · have hσ : reflect ρ ∈ S := mem_offLinePairsBelow (zetaZeroConfig.reflect_mem ρ hρ)
          (by simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith)
          (by rwa [Tail.reflect_im])
        have h := hΛ ⟨reflect ρ, hσ⟩
        simp only [Tail.gammaOf_reflect, Complex.conj_conj] at h
        exact (sub_eq_zero.mp h).symm
      · have h := hΛ ⟨ρ, mem_offLinePairsBelow hρ hgt hH⟩
        exact sub_eq_zero.mp h
    have hge := zeta_re_W_ge_neg_eps_of_nodes hA₀ hloc ha hε hε1 hfd hfs hp hm hnode
    have hlt := hneg f f.2 hf0'
    linarith
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

/-- The inertia bound with the unconditional local-count constant of `ζ`. -/
theorem zeta_weil_negative_index_le :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ a ε : ℝ, 0 < a → 0 < ε → ε ≤ 1 →
      ∀ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V →
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) →
      (∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)) →
      Module.finrank ℂ V ≤ (offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, zeta_weil_negative_index_le_of_local_count hA₀ hloc⟩

/-- `log H(A₀, a, ε) ≤ 7000 e^a + 7 log A₀ + 7 log(1/ε) + 150`. -/
theorem log_inertiaHorizonHeight_le {A₀ a ε : ℝ} (hA₀ : 1 ≤ A₀) (ha : 0 ≤ a) (hε : 0 < ε) :
    Real.log (inertiaHorizonHeight A₀ a ε) ≤
      7000 * Real.exp a + 7 * Real.log A₀ + 7 * Real.log (1 / ε) + 150 := by
  have hH := inertiaHorizonHeight_le hA₀ ha hε
  have hHpos := inertiaHorizonHeight_pos (a := a) hA₀ ha hε
  have hA0 : 0 < A₀ := by linarith
  obtain ⟨-, -, -, -, he2, -⟩ := exp_numeric_bounds
  have hE : 13 * zetaHorizonExp a ≤ 130 + 6630 * Real.exp a := by
    rw [zetaHorizonExp_eq, show a + 2 = a + 2 by rfl, Real.exp_add]
    nlinarith [Real.exp_pos a]
  have hl8 : Real.log 8 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (x := (8 : ℝ)) (by norm_num)
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  calc Real.log (inertiaHorizonHeight A₀ a ε)
      ≤ Real.log ((8 * A₀) ^ 7 * Real.exp (13 * zetaHorizonExp a) / ε ^ 7) :=
        Real.log_le_log hHpos hH
    _ = 7 * (Real.log 8 + Real.log A₀) + 13 * zetaHorizonExp a + 7 * Real.log (1 / ε) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
          (Real.exp_pos _).ne', Real.log_pow, Real.log_pow, Real.log_exp,
          Real.log_mul (by norm_num) hA0.ne', one_div, Real.log_inv]
        push_cast; ring
    _ ≤ 7000 * Real.exp a + 7 * Real.log A₀ + 7 * Real.log (1 / ε) + 150 := by
        linarith [Real.one_le_exp ha]

end RHTower
