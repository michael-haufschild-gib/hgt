/-
The counting substitute (MWM lane, M9 — task #128): exact zero-counting and a
Hurwitz-type stability theorem with NO argument principle, via the large-n deck-class
trick — and the PINNING LEMMA (doc 16 §1) as its first consumer.

The trick: enclosed multiplicity sums are concrete naturals, so comparing deck classes
at level n = N_f + N_g + 1 (bigger than both) pins EQUALITY of the counts outright —
a residue below the modulus determines the number. No a priori bounds, no contours.

* `exists_annulus_roots` — the root construction of `deckClass_multi_zero`, exposed:
  a peeled function has analytic n-th roots on the two slit annulus charts.
* `nat_eq_of_exp_eq` — equal classes at level n force equal counts below n.
* `enclosed_count_eq_of_close` — **the Rouché substitute**: a dominated perturbation
  (`‖f − g‖ < ‖g‖` on the annulus charts) preserves the exact enclosed multiplicity
  count.
* `pinned_zero_on_line` — **the pinning lemma**: if the reference has a single SIMPLE
  zero at a point ρ₀ of the critical line, then any dominated FE∧real perturbation
  has its (unique) nearby zero ON the line: the reflected point is also a zero in the
  hole, and a count of 1 leaves no room for two.
-/
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.DeckHomotopy

namespace RHTower

open Complex Metric

/-- **Root existence on the annulus charts.** A function peeled as
`g = ∏ (z−ρᵢ)^{mᵢ} · h` on the ball, with all `ρᵢ` in the hole and `h` nonvanishing,
has analytic `n`-th roots on both slit annulus charts. (The construction inside
`deckClass_multi_zero`, exposed.) -/
theorem exists_annulus_roots {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {g h : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} (hn : 0 < n)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, g z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z) :
    ∃ G₁ G₂ : ℂ → ℂ, AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) ∧
      AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) ∧
      (∀ z ∈ chartRA a r₀ R, G₁ z ^ n = g z) ∧
      (∀ z ∈ chartLA a r₀ R, G₂ z ^ n = g z) := by
  have hchart_far : ∀ z, z ∈ ball a R \ closedBall a r₀ → ∀ i ∈ s,
      ‖ρ i - a‖ < ‖z - a‖ := by
    intro z hz i hi
    have h1 : r₀ < ‖z - a‖ := by
      have h2 := hz.2
      rw [mem_closedBall, Complex.dist_eq, not_le] at h2
      exact h2
    exact lt_of_le_of_lt (hρ i hi) h1
  have hchart_ne : ∀ z, z ∈ ball a R \ closedBall a r₀ → z ≠ a := by
    intro z hz
    have h1 : r₀ < ‖z - a‖ := by
      have h2 := hz.2
      rw [mem_closedBall, Complex.dist_eq, not_le] at h2
      exact h2
    intro hza
    rw [hza] at h1
    simp at h1
    linarith
  -- the h-root on the ball
  have hZloc : ∀ N : ℕ, {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h w = 0}.Finite := by
    intro N
    have hempty : {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h w = 0} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw
      exact hh0 w hw.1
    rw [hempty]
    exact Set.finite_empty
  obtain ⟨r, hran, hrpow⟩ :=
    (exists_root_iff_orders_dvd hn isOpen_ball (convex_ball a R)
      (mem_ball_self (lt_of_le_of_lt h0 hrR))
      hh (hh0 a (mem_ball_self (lt_of_le_of_lt h0 hrR))) hZloc).mpr
      (fun w hw h0' => absurd h0' (hh0 w hw))
  refine ⟨fun z => (∏ i ∈ s, (monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z)) * r z,
    fun z => (∏ i ∈ s, (monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z)) * r z,
    ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine AnalyticAt.mul ?_ (hran z hz.2.1)
    refine Finset.analyticAt_fun_prod s (fun i hi => ?_)
    exact (monoRoot₁_analyticOnNhd a (m i) n z hz.1).mul
      (corrRoot_analyticAt (m i) n (hchart_ne z hz.2) (hchart_far z hz.2 i hi))
  · intro z hz
    refine AnalyticAt.mul ?_ (hran z hz.2.1)
    refine Finset.analyticAt_fun_prod s (fun i hi => ?_)
    exact (monoRoot₂_analyticOnNhd a (m i) n z hz.1).mul
      (corrRoot_analyticAt (m i) n (hchart_ne z hz.2) (hchart_far z hz.2 i hi))
  · intro z hz
    rw [mul_pow, ← Finset.prod_pow, hrpow z hz.2.1, hfact z hz.2.1]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mul_pow, monoRoot₁_pow hn hz.1, corrRoot_pow hn (hchart_far z hz.2 i hi),
      ← mul_pow, ← shifted_factor (hchart_ne z hz.2)]
  · intro z hz
    rw [mul_pow, ← Finset.prod_pow, hrpow z hz.2.1, hfact z hz.2.1]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mul_pow, monoRoot₂_pow hn hz.1, corrRoot_pow hn (hchart_far z hz.2 i hi),
      ← mul_pow, ← shifted_factor (hchart_ne z hz.2)]

private theorem nat_eq_of_exp_eq_aux {n A B : ℕ} (hn : 0 < n) (hAB : A ≤ B) (hB : B < n)
    (h : exp (2 * (Real.pi : ℂ) * I * (A : ℂ) / n) =
      exp (2 * (Real.pi : ℂ) * I * (B : ℂ) / n)) : A = B := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hAB
  have hsplit : exp (2 * (Real.pi : ℂ) * I * ((A + d : ℕ) : ℂ) / n) =
      exp (2 * (Real.pi : ℂ) * I * (A : ℂ) / n) *
        exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / n) := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit] at h
  have h1 : exp (2 * (Real.pi : ℂ) * I * (A : ℂ) / n) *
      exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / n) =
      exp (2 * (Real.pi : ℂ) * I * (A : ℂ) / n) * 1 := by
    rw [mul_one, ← h]
  have h2 : exp (2 * (Real.pi : ℂ) * I * (d : ℂ) / n) = 1 :=
    mul_left_cancel₀ (exp_ne_zero _) h1
  have hdvd : n ∣ d := (exp_two_pi_mul_div_eq_one_iff hn d).mp h2
  have hd0 : d = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
  omega

/-- Equal deck classes at level `n` force equal counts below `n`. -/
theorem nat_eq_of_exp_eq {n A B : ℕ} (hn : 0 < n) (hA : A < n) (hB : B < n)
    (h : exp (2 * (Real.pi : ℂ) * I * (A : ℂ) / n) =
      exp (2 * (Real.pi : ℂ) * I * (B : ℂ) / n)) : A = B := by
  rcases le_total A B with hle | hle
  · exact nat_eq_of_exp_eq_aux hn hle hB h
  · exact (nat_eq_of_exp_eq_aux hn hle hA h.symm).symm

/-- **The Rouché substitute.** A dominated perturbation on the annulus charts
(`‖f − g‖ < ‖g‖`) preserves the EXACT enclosed multiplicity count — Hurwitz-type
stability with no argument principle: compare deck classes at level
`n = N_f + N_g + 1`. -/
theorem enclosed_count_eq_of_close {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (ρ : ι → ℂ) (m : ι → ℕ) (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f g h h' : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀) (hρ' : ∀ j ∈ t, ‖ρ' j - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfactg : ∀ z ∈ ball a R, g z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hfactf : ∀ z ∈ ball a R, f z = (∏ j ∈ t, (z - ρ' j) ^ m' j) * h' z)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖f z - g z‖ < ‖g z‖) :
    ∑ j ∈ t, m' j = ∑ i ∈ s, m i := by
  set n : ℕ := (∑ j ∈ t, m' j) + (∑ i ∈ s, m i) + 1 with hn_def
  have hn : 0 < n := by omega
  obtain ⟨G₁, G₂, hG₁, hG₂, hpG₁, hpG₂⟩ :=
    exists_annulus_roots s ρ m h0 hrR hn hρ hh hh0 hfactg
  have hsubR : chartRA a r₀ R ⊆ ball a R := fun z hz => hz.2.1
  have hsubL : chartLA a r₀ R ⊆ ball a R := fun z hz => hz.2.1
  have hfan : AnalyticOnNhd ℂ f (ball a R) := by
    intro z hz
    have han : AnalyticAt ℂ (fun w => (∏ j ∈ t, (w - ρ' j) ^ m' j) * h' w) z :=
      (Finset.analyticAt_fun_prod t (fun j _ =>
        (analyticAt_id.sub analyticAt_const).pow _)).mul (hh' z hz)
    exact han.congr (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz)
      (fun w hw => (hfactf w hw).symm))
  have hgan : AnalyticOnNhd ℂ g (ball a R) := by
    intro z hz
    have han : AnalyticAt ℂ (fun w => (∏ i ∈ s, (w - ρ i) ^ m i) * h w) z :=
      (Finset.analyticAt_fun_prod s (fun i _ =>
        (analyticAt_id.sub analyticAt_const).pow _)).mul (hh z hz)
    exact han.congr (Filter.eventually_of_mem (isOpen_ball.mem_nhds hz)
      (fun w hw => (hfactg w hw).symm))
  -- roots of f from roots of g via the global correction root
  have hH₁an : AnalyticOnNhd ℂ (fun z => G₁ z * ratioRoot f g n z) (chartRA a r₀ R) := by
    intro z hz
    have hcl := hclose z (Set.mem_union_left _ hz)
    exact (hG₁ z hz).mul (ratioRoot_analyticAt n (hfan z (hsubR hz)) (hgan z (hsubR hz))
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  have hH₂an : AnalyticOnNhd ℂ (fun z => G₂ z * ratioRoot f g n z) (chartLA a r₀ R) := by
    intro z hz
    have hcl := hclose z (Set.mem_union_right _ hz)
    exact (hG₂ z hz).mul (ratioRoot_analyticAt n (hfan z (hsubL hz)) (hgan z (hsubL hz))
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  have hpH₁ : ∀ z ∈ chartRA a r₀ R, (G₁ z * ratioRoot f g n z) ^ n = f z := by
    intro z hz
    have hcl := hclose z (Set.mem_union_left _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₁ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]
  have hpH₂ : ∀ z ∈ chartLA a r₀ R, (G₂ z * ratioRoot f g n z) ^ n = f z := by
    intro z hz
    have hcl := hclose z (Set.mem_union_right _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₂ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]
  -- the two classes
  have hclassG := deckClass_multi_zero s ρ m h0 hrR hn hρ hh hh0 hfactg hG₁ hG₂ hpG₁ hpG₂
  have hclassH := deckClass_multi_zero t ρ' m' h0 hrR hn hρ' hh' hh0' hfactf
    hH₁an hH₂an hpH₁ hpH₂
  rw [← Nat.cast_sum] at hclassG hclassH
  have heq : deckClass (fun z => G₁ z * ratioRoot f g n z)
      (fun z => G₂ z * ratioRoot f g n z)
      (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      deckClass G₁ G₂
      (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) :=
    deckClass_mul_global (ratioRoot_ne_zero f g n _) (ratioRoot_ne_zero f g n _)
  have hexp : exp (2 * (Real.pi : ℂ) * I * ((∑ j ∈ t, m' j : ℕ) : ℂ) / n) =
      exp (2 * (Real.pi : ℂ) * I * ((∑ i ∈ s, m i : ℕ) : ℂ) / n) := by
    rw [← hclassH, ← hclassG, ← heq]
  exact nat_eq_of_exp_eq hn (by omega) (by omega) hexp

/-- **The pinning lemma** (doc 16 §1, formal). If the reference `g` has a single
SIMPLE zero at a point `ρ₀` of the critical line, and `f` is a dominated perturbation
that carries the FE ∧ reality symmetry (`f(1 − s̄) = conj f(s)` on the ball), then
every zero of `f` in the hole lies ON the critical line: the reflection of a zero is a
zero, and a total count of `1` leaves no room for an off-line pair. -/
theorem pinned_zero_on_line {κ : Type*} (t : Finset κ) (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f g h h' : ℂ → ℂ} {ρ₀ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ₀ : (1 : ℂ) - (starRingEnd ℂ) ρ₀ = ρ₀)
    (hsym : ∀ z ∈ ball ρ₀ R, f (1 - (starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hh : AnalyticOnNhd ℂ h (ball ρ₀ R)) (hh0 : ∀ z ∈ ball ρ₀ R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball ρ₀ R)) (hh0' : ∀ z ∈ ball ρ₀ R, h' z ≠ 0)
    (hfactg : ∀ z ∈ ball ρ₀ R, g z = (z - ρ₀) * h z)
    (hρ' : ∀ j ∈ t, ‖ρ' j - ρ₀‖ ≤ r₀)
    (hfactf : ∀ z ∈ ball ρ₀ R, f z = (∏ j ∈ t, (z - ρ' j) ^ m' j) * h' z)
    (hclose : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖f z - g z‖ < ‖g z‖) :
    ∀ j ∈ t, m' j ≠ 0 → (1 : ℂ) - (starRingEnd ℂ) (ρ' j) = ρ' j := by
  classical
  -- the count is 1
  have hfactg' : ∀ z ∈ ball ρ₀ R,
      g z = (∏ _i ∈ ({0} : Finset ℕ), (z - ρ₀) ^ (1 : ℕ)) * h z := by
    intro z hz
    rw [hfactg z hz]
    simp
  have hρs : ∀ i ∈ ({0} : Finset ℕ), ‖(fun _ => ρ₀) i - ρ₀‖ ≤ r₀ := by
    intro i _
    simpa using h0
  have hcount : ∑ j ∈ t, m' j = 1 := by
    have hc := enclosed_count_eq_of_close ({0} : Finset ℕ) t (fun _ => ρ₀) (fun _ => 1)
      ρ' m' h0 hrR hρs hρ' hh hh0 hh' hh0' hfactg' hfactf hclose
    simpa using hc
  intro j₀ hj₀ hm₀
  by_contra hne
  set q : ℂ := (1 : ℂ) - (starRingEnd ℂ) (ρ' j₀) with hq_def
  -- the reflected point is in the hole
  have hqd : ‖q - ρ₀‖ = ‖ρ' j₀ - ρ₀‖ := by
    have e : q - ρ₀ = (starRingEnd ℂ) (ρ₀ - ρ' j₀) := by
      have h2 : (starRingEnd ℂ) ρ₀ = 1 - ρ₀ := by
        linear_combination -hρ₀
      rw [hq_def, map_sub, h2]
      ring
    rw [e, RCLike.norm_conj, norm_sub_rev]
  have hρ'ball : ρ' j₀ ∈ ball ρ₀ R := by
    rw [mem_ball, Complex.dist_eq]
    exact lt_of_le_of_lt (hρ' j₀ hj₀) hrR
  have hqball : q ∈ ball ρ₀ R := by
    rw [mem_ball, Complex.dist_eq, hqd]
    exact lt_of_le_of_lt (hρ' j₀ hj₀) hrR
  -- f vanishes at ρ' j₀, hence at the reflected point q
  have hfρ' : f (ρ' j₀) = 0 := by
    rw [hfactf _ hρ'ball]
    refine mul_eq_zero_of_left (Finset.prod_eq_zero hj₀ ?_) _
    rw [sub_self]
    exact zero_pow hm₀
  have hfq : f q = 0 := by
    have := hsym _ hρ'ball
    rw [← hq_def] at this
    rw [this, hfρ', map_zero]
  -- q is one of the listed zeros, with positive multiplicity
  obtain ⟨j₁, hj₁, hzero⟩ : ∃ j₁ ∈ t, (q - ρ' j₁) ^ m' j₁ = 0 := by
    have hq0 := hfq
    rw [hfactf q hqball] at hq0
    rcases mul_eq_zero.mp hq0 with hp | hcontra
    · exact Finset.prod_eq_zero_iff.mp hp
    · exact absurd hcontra (hh0' q hqball)
  have hm₁ : m' j₁ ≠ 0 := by
    intro h0'
    rw [h0', pow_zero] at hzero
    exact one_ne_zero hzero
  have hval : ρ' j₁ = q := by
    have hs0 := (pow_eq_zero_iff hm₁).mp hzero
    exact (sub_eq_zero.mp hs0).symm
  have hjne : j₁ ≠ j₀ := by
    intro hEq
    rw [hEq] at hval
    exact hne hval.symm
  -- two distinct indices with positive multiplicity contradict count 1
  have hpair : ({j₁, j₀} : Finset κ) ⊆ t := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hj₁
    · rw [Finset.mem_singleton.mp hx]
      exact hj₀
  have hle := Finset.sum_le_sum_of_subset hpair (f := m')
  rw [Finset.sum_pair hjne] at hle
  omega

end RHTower

namespace RHTower

open Complex Metric

/-- Real-part form of `pinned_zero_on_line`: the public boundary is the geometric
critical-line condition rather than the algebraic reflection equation. -/
theorem pinned_zero_re_eq_half {κ : Type*} (t : Finset κ) (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f g h h' : ℂ → ℂ} {ρ₀ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hρ₀re : ρ₀.re = 1 / 2)
    (hsym : ∀ z ∈ ball ρ₀ R, f (1 - (starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hh : AnalyticOnNhd ℂ h (ball ρ₀ R)) (hh0 : ∀ z ∈ ball ρ₀ R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball ρ₀ R)) (hh0' : ∀ z ∈ ball ρ₀ R, h' z ≠ 0)
    (hfactg : ∀ z ∈ ball ρ₀ R, g z = (z - ρ₀) * h z)
    (hρ' : ∀ j ∈ t, ‖ρ' j - ρ₀‖ ≤ r₀)
    (hfactf : ∀ z ∈ ball ρ₀ R, f z = (∏ j ∈ t, (z - ρ' j) ^ m' j) * h' z)
    (hclose : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖f z - g z‖ < ‖g z‖) :
    ∀ j ∈ t, m' j ≠ 0 → (ρ' j).re = 1 / 2 := by
  have hρ₀ : (1 : ℂ) - (starRingEnd ℂ) ρ₀ = ρ₀ := by
    apply Complex.ext
    · simp [Complex.sub_re, hρ₀re]
      norm_num
    · simp [Complex.sub_im]
  intro j hj hm
  have hfix := pinned_zero_on_line t ρ' m' h0 hrR hρ₀ hsym hh hh0 hh' hh0' hfactg hρ'
    hfactf hclose j hj hm
  have hre := congrArg Complex.re hfix
  simp [Complex.sub_re] at hre
  linarith

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative Rouché substitute.** Relative `η < 1` closeness on the annulus charts
preserves the enclosed multiplicity count and gives the U0 principal-log bound for
the correction ratio on the same charts. -/
theorem enclosed_count_eq_of_relative_close {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (ρ : ι → ℂ) (m : ι → ℕ) (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f g h h' : ℂ → ℂ} {a : ℂ} {r₀ R η : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hη : η < 1)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀) (hρ' : ∀ j ∈ t, ‖ρ' j - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball a R)) (hh0' : ∀ z ∈ ball a R, h' z ≠ 0)
    (hfactg : ∀ z ∈ ball a R, g z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hfactf : ∀ z ∈ ball a R, f z = (∏ j ∈ t, (z - ρ' j) ^ m' j) * h' z)
    (hg0 : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, g z ≠ 0)
    (hrel : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖(f z - g z) / g z‖ ≤ η) :
    (∑ j ∈ t, m' j = ∑ i ∈ s, m i) ∧
      ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
        ‖Complex.log (f z / g z)‖ ≤ (1 - η)⁻¹ * ‖(f z - g z) / g z‖ := by
  have hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖f z - g z‖ < ‖g z‖ := by
    intro z hz
    have hz0 : g z ≠ 0 := hg0 z hz
    have hnorm : 0 < ‖g z‖ := norm_pos_iff.mpr hz0
    have hdiv : ‖f z - g z‖ / ‖g z‖ ≤ η := by
      simpa [norm_div] using hrel z hz
    have hmul : ‖f z - g z‖ ≤ η * ‖g z‖ := (div_le_iff₀ hnorm).mp hdiv
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hnorm)
  constructor
  · exact enclosed_count_eq_of_close s t ρ m ρ' m' h0 hrR hρ hρ' hh hh0 hh' hh0'
      hfactg hfactf hclose
  · intro z hz
    exact ratio_log_norm_le_of_relative_close hη (hg0 z hz) (hrel z hz)

end RHTower

namespace RHTower

open Complex Metric

/-- **Relative pinning lemma.** If the reference has one simple critical-line zero and
the perturbation is FE-real plus relatively `η < 1` close on the annulus charts,
then every counted perturbation zero lies on the critical line; the same certificate
also controls the principal-log correction ratio by the U0 bound. -/
theorem pinned_zero_re_eq_half_of_relative_close {κ : Type*} (t : Finset κ)
    (ρ' : κ → ℂ) (m' : κ → ℕ)
    {f g h h' : ℂ → ℂ} {ρ₀ : ℂ} {r₀ R η : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hη : η < 1) (hρ₀re : ρ₀.re = 1 / 2)
    (hsym : ∀ z ∈ ball ρ₀ R, f (1 - (starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hh : AnalyticOnNhd ℂ h (ball ρ₀ R)) (hh0 : ∀ z ∈ ball ρ₀ R, h z ≠ 0)
    (hh' : AnalyticOnNhd ℂ h' (ball ρ₀ R)) (hh0' : ∀ z ∈ ball ρ₀ R, h' z ≠ 0)
    (hfactg : ∀ z ∈ ball ρ₀ R, g z = (z - ρ₀) * h z)
    (hρ' : ∀ j ∈ t, ‖ρ' j - ρ₀‖ ≤ r₀)
    (hfactf : ∀ z ∈ ball ρ₀ R, f z = (∏ j ∈ t, (z - ρ' j) ^ m' j) * h' z)
    (hg0 : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, g z ≠ 0)
    (hrel : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖(f z - g z) / g z‖ ≤ η) :
    (∀ j ∈ t, m' j ≠ 0 → (ρ' j).re = 1 / 2) ∧
      ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R,
        ‖Complex.log (f z / g z)‖ ≤ (1 - η)⁻¹ * ‖(f z - g z) / g z‖ := by
  have hclose : ∀ z ∈ chartRA ρ₀ r₀ R ∪ chartLA ρ₀ r₀ R, ‖f z - g z‖ < ‖g z‖ := by
    intro z hz
    have hz0 : g z ≠ 0 := hg0 z hz
    have hnorm : 0 < ‖g z‖ := norm_pos_iff.mpr hz0
    have hdiv : ‖f z - g z‖ / ‖g z‖ ≤ η := by
      simpa [norm_div] using hrel z hz
    have hmul : ‖f z - g z‖ ≤ η * ‖g z‖ := (div_le_iff₀ hnorm).mp hdiv
    exact lt_of_le_of_lt hmul (by simpa using mul_lt_mul_of_pos_right hη hnorm)
  constructor
  · exact pinned_zero_re_eq_half t ρ' m' h0 hrR hρ₀re hsym hh hh0 hh' hh0' hfactg hρ'
      hfactf hclose
  · intro z hz
    exact ratio_log_norm_le_of_relative_close hη (hg0 z hz) (hrel z hz)

end RHTower
