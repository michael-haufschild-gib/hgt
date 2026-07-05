/-
Charge conservation for the deck cocycle (MWM lane, M1 arc — task #117).

The deck class is a DEFORMATION INVARIANT, with no argument principle and no covering
machinery: if `f` is closer to `g` than `g` is to zero on both annulus charts
(`‖f − g‖ < ‖g‖`, the Rouché-flavored domination), then the principal branch
`r = exp((1/n)·log(f/g))` is a GLOBAL nonvanishing n-th root of `f/g` on both charts —
`f/g` lands in `B(1,1) ⊆ slitPlane` — so multiplying any roots of `g` by `r` produces
roots of `f`, and `deckClass_mul_global` says the class does not move.

* `deckClass_step` — the conservation step: dominated perturbation transports roots and
  preserves the class.
* `deckClass_perturb` — both-roots-given form: ANY roots of `f` and ANY roots of `g`
  have the same class under domination.
* `deckClass_chain` — finite deformation chains: roots of `F 0` transport to roots of
  `F N` with the same class along consecutive dominations.
* `deckClass_deformation_invariant` — the capstone: the charge of `F N` (read from any
  roots) equals the charge of `F 0`. Enclosed multiplicity mod n cannot change while no
  zero touches the charts — the conservation law the M1 program runs on.
-/
import GaloisForLFunctions.RHTower.DeckAssembly
import GaloisForLFunctions.U0.U0LogBoundGeneral

namespace RHTower

open Complex Metric

/-! ### The dominated ratio lands in the slit plane -/

/-- A complex number within distance `1` of `1` has positive real part. -/
theorem mem_slitPlane_of_norm_sub_one_lt {w : ℂ} (h : ‖w - 1‖ < 1) : w ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have h1 : |(w - 1).re| ≤ ‖w - 1‖ := abs_re_le_norm _
  have h2 : (w - 1).re = w.re - 1 := by simp [Complex.sub_re]
  rw [h2] at h1
  have h3 : |w.re - 1| < 1 := lt_of_le_of_lt h1 h
  have h4 := abs_lt.mp h3
  linarith [h4.1]

/-- Under the domination `‖f z − g z‖ < ‖g z‖`, the base function does not vanish. -/
theorem right_ne_zero_of_close {f g : ℂ → ℂ} {z : ℂ}
    (h : ‖f z - g z‖ < ‖g z‖) : g z ≠ 0 := by
  intro h0
  rw [h0, sub_zero, norm_zero] at h
  exact absurd h (not_lt.mpr (norm_nonneg _))

/-- Under the domination `‖f z − g z‖ < ‖g z‖`, the perturbed function does not vanish. -/
theorem left_ne_zero_of_close {f g : ℂ → ℂ} {z : ℂ}
    (h : ‖f z - g z‖ < ‖g z‖) : f z ≠ 0 := by
  intro h0
  rw [h0, zero_sub, norm_neg] at h
  exact lt_irrefl _ h

/-- Under the domination, the ratio `f z / g z` lies in `B(1,1) ⊆ slitPlane`. -/
theorem ratio_mem_slitPlane {f g : ℂ → ℂ} {z : ℂ} (h : ‖f z - g z‖ < ‖g z‖) :
    f z / g z ∈ slitPlane := by
  have hg0 : g z ≠ 0 := right_ne_zero_of_close h
  refine mem_slitPlane_of_norm_sub_one_lt ?_
  rw [div_sub_one hg0, norm_div]
  exact (div_lt_one (norm_pos_iff.mpr hg0)).mpr h

/-! ### The global correction root -/

/-- The principal-branch `n`-th root of the ratio `f/g`. -/
noncomputable def ratioRoot (f g : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun z => exp ((n : ℂ)⁻¹ * log (f z / g z))

theorem ratioRoot_ne_zero (f g : ℂ → ℂ) (n : ℕ) (z : ℂ) : ratioRoot f g n z ≠ 0 :=
  exp_ne_zero _

theorem ratioRoot_pow {f g : ℂ → ℂ} {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hf : f z ≠ 0) (hg : g z ≠ 0) :
    ratioRoot f g n z ^ n = f z / g z := by
  have hq : f z / g z ≠ 0 := div_ne_zero hf hg
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [ratioRoot, ← exp_nat_mul]
  have harg : (n : ℂ) * ((n : ℂ)⁻¹ * log (f z / g z)) = log (f z / g z) := by
    field_simp
  rw [harg, exp_log hq]

theorem ratioRoot_analyticAt {f g : ℂ → ℂ} (n : ℕ) {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hg0 : g z ≠ 0)
    (hslit : f z / g z ∈ slitPlane) :
    AnalyticAt ℂ (ratioRoot f g n) z := by
  have hdiv : AnalyticAt ℂ (fun w => f w / g w) z := hf.div hg hg0
  have hlog : AnalyticAt ℂ (fun w => log (f w / g w)) z := hdiv.clog hslit
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (n : ℂ)⁻¹) z := analyticAt_const
  show AnalyticAt ℂ (fun w => exp ((n : ℂ)⁻¹ * log (f w / g w))) z
  exact (hconst.mul hlog).cexp

/-! ### Basepoint membership -/

/-- The upper basepoint `a + (R/2)i` lies in both charts. -/
theorem basepointP_mem_charts {a : ℂ} {R : ℝ} (hR : 0 < R) :
    a + ((R / 2 : ℝ) : ℂ) * I ∈ chartR a R ∩ chartL a R := by
  have hR2 : (0 : ℝ) < R / 2 := by positivity
  have hball : a + ((R / 2 : ℝ) : ℂ) * I ∈ ball a R := by
    rw [mem_ball, Complex.dist_eq]
    have e : a + ((R / 2 : ℝ) : ℂ) * I - a = ((R / 2 : ℝ) : ℂ) * I := by ring
    rw [e, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
    linarith
  have him : (a + ((R / 2 : ℝ) : ℂ) * I - a).im = R / 2 := by
    have e : a + ((R / 2 : ℝ) : ℂ) * I - a = ((R / 2 : ℝ) : ℂ) * I := by ring
    rw [e]
    simp
  refine ⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [him]; exact hR2.ne')), hball⟩,
    ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hball⟩⟩
  have e : (a - (a + ((R / 2 : ℝ) : ℂ) * I)).im = -((a + ((R / 2 : ℝ) : ℂ) * I - a).im) := by
    simp
  rw [e, him]
  simpa using hR2.ne'

/-- The lower basepoint `a − (R/2)i` lies in both charts. -/
theorem basepointM_mem_charts {a : ℂ} {R : ℝ} (hR : 0 < R) :
    a - ((R / 2 : ℝ) : ℂ) * I ∈ chartR a R ∩ chartL a R := by
  have hR2 : (0 : ℝ) < R / 2 := by positivity
  have hball : a - ((R / 2 : ℝ) : ℂ) * I ∈ ball a R := by
    rw [mem_ball, Complex.dist_eq]
    have e : a - ((R / 2 : ℝ) : ℂ) * I - a = -(((R / 2 : ℝ) : ℂ) * I) := by ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
    linarith
  have him : (a - ((R / 2 : ℝ) : ℂ) * I - a).im = -(R / 2) := by
    have e : a - ((R / 2 : ℝ) : ℂ) * I - a = -(((R / 2 : ℝ) : ℂ) * I) := by ring
    rw [e]
    simp
  refine ⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [him]; simpa using hR2.ne')), hball⟩,
    ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hball⟩⟩
  have e : a - (a - ((R / 2 : ℝ) : ℂ) * I) = ((R / 2 : ℝ) : ℂ) * I := by ring
  rw [e]
  have him2 : (((R / 2 : ℝ) : ℂ) * I).im = R / 2 := by simp
  rw [him2]
  exact hR2.ne'

/-! ### The conservation step -/

/-- **Conservation step.** If `f` is dominated-close to `g` on both charts
(`‖f − g‖ < ‖g‖`), then any roots of `g` transport to roots of `f` — multiply by the
global correction root of `f/g` — with the SAME deck class. The charge cannot move
under a dominated perturbation. -/
theorem deckClass_step {f g G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = g z) (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = g z)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R, ‖f z - g z‖ < ‖g z‖) :
    ∃ H₁ H₂ : ℂ → ℂ, AnalyticOnNhd ℂ H₁ (chartR a R) ∧ AnalyticOnNhd ℂ H₂ (chartL a R) ∧
      (∀ z ∈ chartR a R, H₁ z ^ n = f z) ∧ (∀ z ∈ chartL a R, H₂ z ^ n = f z) ∧
      deckClass H₁ H₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  refine ⟨fun z => G₁ z * ratioRoot f g n z, fun z => G₂ z * ratioRoot f g n z,
    ?_, ?_, ?_, ?_,
    deckClass_mul_global (ratioRoot_ne_zero f g n _) (ratioRoot_ne_zero f g n _)⟩
  · intro z hz
    have hzU : z ∈ chartR a R ∪ chartL a R := Set.mem_union_left _ hz
    have hcl := hclose z hzU
    have hgan : AnalyticAt ℂ g z :=
      ((hG₁ z hz).pow n).congr (Filter.eventually_of_mem
        ((isOpen_chartR a R).mem_nhds hz) (fun y hy => hpG₁ y hy))
    exact (hG₁ z hz).mul (ratioRoot_analyticAt n (hf z hzU) hgan
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  · intro z hz
    have hzU : z ∈ chartR a R ∪ chartL a R := Set.mem_union_right _ hz
    have hcl := hclose z hzU
    have hgan : AnalyticAt ℂ g z :=
      ((hG₂ z hz).pow n).congr (Filter.eventually_of_mem
        ((isOpen_chartL a R).mem_nhds hz) (fun y hy => hpG₂ y hy))
    exact (hG₂ z hz).mul (ratioRoot_analyticAt n (hf z hzU) hgan
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  · intro z hz
    have hcl := hclose z (Set.mem_union_left _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₁ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]
  · intro z hz
    have hcl := hclose z (Set.mem_union_right _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₂ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]

/-- **Perturbation invariance, both-roots-given form.** Under domination, ANY roots of
`f` and ANY roots of `g` on the two charts have the same deck class. -/
theorem deckClass_perturb {f g F₁ F₂ G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} {n : ℕ}
    (hR : 0 < R) (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (chartR a R ∪ chartL a R))
    (hF₁ : AnalyticOnNhd ℂ F₁ (chartR a R)) (hF₂ : AnalyticOnNhd ℂ F₂ (chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpF₁ : ∀ z ∈ chartR a R, F₁ z ^ n = f z) (hpF₂ : ∀ z ∈ chartL a R, F₂ z ^ n = f z)
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = g z) (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = g z)
    (hclose : ∀ z ∈ chartR a R ∪ chartL a R, ‖f z - g z‖ < ‖g z‖) :
    deckClass F₁ F₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHG⟩ :=
    deckClass_step hn hf hG₁ hG₂ hpG₁ hpG₂ hclose
  have hPP := basepointP_mem_charts (a := a) hR
  have hPM := basepointM_mem_charts (a := a) hR
  have hfP : f (a + ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    left_ne_zero_of_close (hclose _ (Set.mem_union_left _ hPP.1))
  have hfM : f (a - ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    left_ne_zero_of_close (hclose _ (Set.mem_union_left _ hPM.1))
  rw [← hHG]
  exact deckClass_root_indep hn (isOpen_chartR a R) (isPreconnected_chartR a hR)
    (isOpen_chartL a R) (isPreconnected_chartL a hR)
    hH₁ hF₁ hH₂ hF₂ hpH₁ hpF₁ hpH₂ hpF₂
    hPP.1 hPP.2 hPM.1 hPM.2 hfP hfM

/-! ### Deformation chains -/

/-- **Chain transport.** Along a finite chain of consecutive dominations, roots of `F 0`
transport to roots of `F N` with the same deck class. -/
theorem deckClass_chain {F : ℕ → ℂ → ℂ} {G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} {n : ℕ} {N : ℕ}
    (hn : 0 < n)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hclose : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖F (i + 1) z - F i z‖ < ‖F i z‖) :
    ∃ H₁ H₂ : ℂ → ℂ, AnalyticOnNhd ℂ H₁ (chartR a R) ∧ AnalyticOnNhd ℂ H₂ (chartL a R) ∧
      (∀ z ∈ chartR a R, H₁ z ^ n = F N z) ∧ (∀ z ∈ chartL a R, H₂ z ^ n = F N z) ∧
      deckClass H₁ H₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  induction N with
  | zero => exact ⟨G₁, G₂, hG₁, hG₂, hpG₁, hpG₂, rfl⟩
  | succ N ih =>
    obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHG⟩ :=
      ih (fun i hi0 hiN => hFan i hi0 (hiN.trans (Nat.le_succ N)))
        (fun i hi => hclose i (Nat.lt_succ_of_lt hi))
    obtain ⟨K₁, K₂, hK₁, hK₂, hpK₁, hpK₂, hKH⟩ :=
      deckClass_step hn (hFan (N + 1) (Nat.succ_pos N) le_rfl) hH₁ hH₂ hpH₁ hpH₂
        (hclose N (Nat.lt_succ_self N))
    exact ⟨K₁, K₂, hK₁, hK₂, hpK₁, hpK₂, hKH.trans hHG⟩

/-- **Charge conservation.** Along a finite chain of consecutive dominations, the deck
class of ANY roots of the endpoint `F N` equals the class of ANY roots of the start
`F 0`: enclosed multiplicity mod `n` cannot change while no zero touches the charts. -/
theorem deckClass_deformation_invariant {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R : ℝ} {n : ℕ} {N : ℕ} (hR : 0 < R) (hn : 0 < n)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hclose : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖F (i + 1) z - F i z‖ < ‖F i z‖)
    (hFNP : F N (a + ((R / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hFNM : F N (a - ((R / 2 : ℝ) : ℂ) * I) ≠ 0) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHG⟩ :=
    deckClass_chain hn hFan hG₁ hG₂ hpG₁ hpG₂ hclose
  have hPP := basepointP_mem_charts (a := a) hR
  have hPM := basepointM_mem_charts (a := a) hR
  rw [← hHG]
  exact deckClass_root_indep hn (isOpen_chartR a R) (isPreconnected_chartR a hR)
    (isOpen_chartL a R) (isPreconnected_chartL a hR)
    hH₁ hK₁ hH₂ hK₂ hpH₁ hpK₁ hpH₂ hpK₂
    hPP.1 hPP.2 hPM.1 hPM.2 hFNP hFNM

end RHTower

namespace RHTower

open Complex Metric

/-- Quantitative version of the dominated-ratio step: if the relative error is at
most `r < 1`, the principal log of `f/g` is controlled by the sharp `log(1+w)`
bound from the U0 window analysis. -/
theorem ratio_log_norm_le_of_relative_close {f g : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : r < 1) (hg : g z ≠ 0) (hrel : ‖(f z - g z) / g z‖ ≤ r) :
    ‖Complex.log (f z / g z)‖ ≤ (1 - r)⁻¹ * ‖(f z - g z) / g z‖ := by
  have hratio : f z / g z = 1 + (f z - g z) / g z := by
    field_simp [hg]
    ring
  rw [hratio]
  exact U0LogBoundGeneral.norm_clog_one_add_le_of_le hr hrel

end RHTower

namespace RHTower

open Complex Metric

/-- **Charge conservation with endpoint nonvanishing discharged.** For a positive
finite deformation chain, the final domination step already proves that the
endpoint is nonzero at the two deck basepoints, so callers of the both-roots-given
invariant do not have to certify those two nonvanishing facts separately. -/
theorem deckClass_deformation_invariant_of_pos_chain
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R : ℝ} {n : ℕ} {N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hclose : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖F (i + 1) z - F i z‖ < ‖F i z‖) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hPP := basepointP_mem_charts (a := a) hR
  have hPM := basepointM_mem_charts (a := a) hR
  have hFNP : F (N' + 1) (a + ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    left_ne_zero_of_close (hclose N' (Nat.lt_succ_self N') _ (Set.mem_union_left _ hPP.1))
  have hFNM : F (N' + 1) (a - ((R / 2 : ℝ) : ℂ) * I) ≠ 0 :=
    left_ne_zero_of_close (hclose N' (Nat.lt_succ_self N') _ (Set.mem_union_left _ hPM.1))
  exact deckClass_deformation_invariant hR hn hFan hG₁ hG₂ hK₁ hK₂ hpG₁ hpG₂ hpK₁ hpK₂
    hclose hFNP hFNM

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative-error charge conservation.** For a positive finite deformation chain,
relative `r < 1` closeness at every step implies deck-class conservation and gives
the U0 principal-log bound for each correction ratio. -/
theorem deckClass_deformation_invariant_of_relative_pos_chain
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R r : ℝ} {n N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hr : r < 1)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hbase : ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R, F i z ≠ 0)
    (hrel : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) ∧
      ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (F (i + 1) z / F i z)‖ ≤
          (1 - r)⁻¹ * ‖(F (i + 1) z - F i z) / F i z‖ := by
  have hclose : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖F (i + 1) z - F i z‖ < ‖F i z‖ := by
    intro i hi z hz
    have hFi0 : F i z ≠ 0 := hbase i hi z hz
    have hnormFi : 0 < ‖F i z‖ := norm_pos_iff.mpr hFi0
    have hdiv : ‖F (i + 1) z - F i z‖ / ‖F i z‖ ≤ r := by
      simpa [norm_div] using hrel i hi z hz
    have hmul : ‖F (i + 1) z - F i z‖ ≤ r * ‖F i z‖ :=
      (div_le_iff₀ hnormFi).mp hdiv
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hr hnormFi)
  constructor
  · exact deckClass_deformation_invariant_of_pos_chain hR hn hN hFan hG₁ hG₂ hK₁ hK₂
      hpG₁ hpG₂ hpK₁ hpK₂ hclose
  · intro i hi z hz
    exact ratio_log_norm_le_of_relative_close (f := F (i + 1)) (g := F i) hr
      (hbase i hi z hz) (hrel i hi z hz)

end RHTower

namespace RHTower

open Complex Metric

/-- Relative `r < 1` control propagates nonvanishing through a finite chain.  Once
level `0` is nonzero on a set, every later level up to `N` is nonzero there, because
each step stays strictly inside the previous value's norm. -/
theorem relative_chain_nonzero_of_base {F : ℕ → ℂ → ℂ} {S : Set ℂ} {r : ℝ} {N : ℕ}
    (hr : r < 1) (hF0 : ∀ z ∈ S, F 0 z ≠ 0)
    (hrel : ∀ i, i < N → ∀ z ∈ S, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r) :
    ∀ i, i ≤ N → ∀ z ∈ S, F i z ≠ 0 := by
  intro i hi
  induction i with
  | zero =>
      exact hF0
  | succ i ih =>
      intro z hz
      have hiN : i < N := Nat.lt_of_succ_le hi
      have hprev : F i z ≠ 0 := ih (Nat.le_of_succ_le hi) z hz
      have hnormFi : 0 < ‖F i z‖ := norm_pos_iff.mpr hprev
      have hdiv : ‖F (i + 1) z - F i z‖ / ‖F i z‖ ≤ r := by
        simpa [norm_div] using hrel i hiN z hz
      have hmul : ‖F (i + 1) z - F i z‖ ≤ r * ‖F i z‖ :=
        (div_le_iff₀ hnormFi).mp hdiv
      exact left_ne_zero_of_close (f := F (i + 1)) (g := F i) (z := z)
        (lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hr hnormFi))

/-- **Relative-error charge conservation with chain nonvanishing discharged from
level 0.** The caller supplies only a level-0 nonvanishing certificate; relative
`r < 1` control propagates the nonvanishing needed by the existing U0 log-bound
transport, which then gives deck-class conservation and the same principal-log bounds. -/
theorem deckClass_deformation_invariant_of_relative_base_chain
    {F : ℕ → ℂ → ℂ} {G₁ G₂ K₁ K₂ : ℂ → ℂ}
    {a : ℂ} {R r : ℝ} {n N : ℕ} (hR : 0 < R) (hn : 0 < n) (hN : 0 < N)
    (hr : r < 1)
    (hFan : ∀ i, 0 < i → i ≤ N → AnalyticOnNhd ℂ (F i) (chartR a R ∪ chartL a R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartR a R)) (hK₂ : AnalyticOnNhd ℂ K₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = F 0 z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = F 0 z)
    (hpK₁ : ∀ z ∈ chartR a R, K₁ z ^ n = F N z)
    (hpK₂ : ∀ z ∈ chartL a R, K₂ z ^ n = F N z)
    (hF0 : ∀ z ∈ chartR a R ∪ chartL a R, F 0 z ≠ 0)
    (hrel : ∀ i, i < N →
      ∀ z ∈ chartR a R ∪ chartL a R, ‖(F (i + 1) z - F i z) / F i z‖ ≤ r) :
    deckClass K₁ K₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
        deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) ∧
      ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R,
        ‖Complex.log (F (i + 1) z / F i z)‖ ≤
          (1 - r)⁻¹ * ‖(F (i + 1) z - F i z) / F i z‖ := by
  have hbase : ∀ i, i < N → ∀ z ∈ chartR a R ∪ chartL a R, F i z ≠ 0 := by
    intro i hi
    exact relative_chain_nonzero_of_base (F := F) (S := chartR a R ∪ chartL a R)
      hr hF0 hrel i (Nat.le_of_lt hi)
  exact deckClass_deformation_invariant_of_relative_pos_chain hR hn hN hr hFan hG₁ hG₂
    hK₁ hK₂ hpG₁ hpG₂ hpK₁ hpK₂ hbase hrel

end RHTower
