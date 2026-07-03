/-
The deck-cocycle assembly (MWM lane, A3 chunk 3; task #113).

Capstone: `deckClass_single_zero` — for ANY local `n`-th roots of a peeled function
`f = (z−a)^m · h` (h analytic nonvanishing on a ball) on the two standard slit charts,
the deck class at the basepoints `a ± (R/2)i` equals `exp(2πi·m/n)`: the coarse box
invariant `w_n` COUNTS THE ENCLOSED ORDER mod n, machine-checked with no argument
principle. Route: chart geometry (star-convex slit charts, translated half-plane
overlaps), the generalized monomial dictionary at `a ± εi`, an analytic root of `h` on
the ball (Arc A root existence, vacuous zero set), `deckClass_mul_global`, and
`deckClass_root_indep`.
-/
import GaloisForLFunctions.RHTower.DeckMonomial
import GaloisForLFunctions.RHTower.RootExistence

namespace RHTower

open Complex Metric

/-! ### Chart geometry -/

/-- Right slit chart around `a`, inside the ball of radius `R`. -/
def chartR (a : ℂ) (R : ℝ) : Set ℂ := {z | z - a ∈ slitPlane} ∩ ball a R

/-- Left slit chart around `a`, inside the ball of radius `R`. -/
def chartL (a : ℂ) (R : ℝ) : Set ℂ := {z | a - z ∈ slitPlane} ∩ ball a R

/-- Upper overlap piece. -/
def overlapU (a : ℂ) (R : ℝ) : Set ℂ := {z | 0 < (z - a).im} ∩ ball a R

/-- Lower overlap piece. -/
def overlapD (a : ℂ) (R : ℝ) : Set ℂ := {z | (z - a).im < 0} ∩ ball a R

theorem isOpen_chartR (a : ℂ) (R : ℝ) : IsOpen (chartR a R) :=
  (isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).inter isOpen_ball

theorem isOpen_chartL (a : ℂ) (R : ℝ) : IsOpen (chartL a R) :=
  (isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter isOpen_ball

theorem isOpen_overlapU (a : ℂ) (R : ℝ) : IsOpen (overlapU a R) :=
  (isOpen_lt continuous_const (Complex.continuous_im.comp
    (continuous_id.sub continuous_const))).inter isOpen_ball

theorem isOpen_overlapD (a : ℂ) (R : ℝ) : IsOpen (overlapD a R) :=
  (isOpen_lt (Complex.continuous_im.comp
    (continuous_id.sub continuous_const)) continuous_const).inter isOpen_ball

theorem convex_upperShift (a : ℂ) : Convex ℝ {z : ℂ | 0 < (z - a).im} := by
  have himg : {z : ℂ | 0 < (z - a).im} = (fun w => a + w) '' {w : ℂ | 0 < w.im} := by
    ext z
    constructor
    · intro hz
      exact ⟨z - a, hz, by ring⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [himg]
  exact (convex_halfSpace_im_gt 0).translate a

theorem convex_lowerShift (a : ℂ) : Convex ℝ {z : ℂ | (z - a).im < 0} := by
  have himg : {z : ℂ | (z - a).im < 0} = (fun w => a + w) '' {w : ℂ | w.im < 0} := by
    ext z
    constructor
    · intro hz
      exact ⟨z - a, hz, by ring⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [himg]
  exact (convex_halfSpace_im_lt 0).translate a

theorem isPreconnected_overlapU (a : ℂ) (R : ℝ) : IsPreconnected (overlapU a R) :=
  ((convex_upperShift a).inter (convex_ball a R)).isPreconnected

theorem isPreconnected_overlapD (a : ℂ) (R : ℝ) : IsPreconnected (overlapD a R) :=
  ((convex_lowerShift a).inter (convex_ball a R)).isPreconnected

/-- The unballed right slit chart is star-convex about `a + c` for real `c > 0`. -/
theorem starConvex_slitChartR (a : ℂ) {c : ℝ} (hc : 0 < c) :
    StarConvex ℝ (a + (c : ℂ)) {z | z - a ∈ slitPlane} := by
  intro z hz t s ht hs hts
  have hz' : z - a ∈ slitPlane := hz
  have hts' : (t : ℂ) + (s : ℂ) = 1 := by exact_mod_cast hts
  have hkey : (t • (a + (c : ℂ)) + s • z) - a =
      ((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (z - a) := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination a * hts'
  show (t • (a + (c : ℂ)) + s • z) - a ∈ slitPlane
  rw [hkey]
  have hre : (((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (z - a)).re = t * c + s * (z - a).re := by
    simp [Complex.add_re, Complex.mul_re]
  have him : (((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (z - a)).im = s * (z - a).im := by
    simp [Complex.add_im, Complex.mul_im]
  rcases Complex.mem_slitPlane_iff.mp hz' with h | h
  · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hre]
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · have hs1 : s = 1 := by linarith
      rw [← ht0, hs1]
      simpa using h
    · nlinarith [mul_nonneg hs h.le]
  · rcases eq_or_lt_of_le hs with hs0 | hspos
    · have ht1 : t = 1 := by linarith
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [hre, ← hs0, ht1]
      simpa using hc
    · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [him]
      exact mul_ne_zero hspos.ne' h

/-- The unballed left slit chart is star-convex about `a − c` for real `c > 0`. -/
theorem starConvex_slitChartL (a : ℂ) {c : ℝ} (hc : 0 < c) :
    StarConvex ℝ (a - (c : ℂ)) {z | a - z ∈ slitPlane} := by
  intro z hz t s ht hs hts
  have hz' : a - z ∈ slitPlane := hz
  have hts' : (t : ℂ) + (s : ℂ) = 1 := by exact_mod_cast hts
  have hkey : a - (t • (a - (c : ℂ)) + s • z) =
      ((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (a - z) := by
    simp only [Complex.real_smul]
    push_cast
    linear_combination (-a) * hts'
  show a - (t • (a - (c : ℂ)) + s • z) ∈ slitPlane
  rw [hkey]
  have hre : (((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (a - z)).re = t * c + s * (a - z).re := by
    simp [Complex.add_re, Complex.mul_re]
  have him : (((t * c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (a - z)).im = s * (a - z).im := by
    simp [Complex.add_im, Complex.mul_im]
  rcases Complex.mem_slitPlane_iff.mp hz' with h | h
  · refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hre]
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · have hs1 : s = 1 := by linarith
      rw [← ht0, hs1]
      simpa using h
    · nlinarith [mul_nonneg hs h.le]
  · rcases eq_or_lt_of_le hs with hs0 | hspos
    · have ht1 : t = 1 := by linarith
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [hre, ← hs0, ht1]
      simpa using hc
    · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
      rw [him]
      exact mul_ne_zero hspos.ne' h

theorem center_mem_chartR (a : ℂ) {R : ℝ} (hR : 0 < R) :
    a + ((R / 2 : ℝ) : ℂ) ∈ chartR a R := by
  constructor
  · show a + ((R / 2 : ℝ) : ℂ) - a ∈ slitPlane
    have : a + ((R / 2 : ℝ) : ℂ) - a = ((R / 2 : ℝ) : ℂ) := by ring
    rw [this]
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.ofReal_re]
    positivity
  · rw [mem_ball, Complex.dist_eq]
    have : a + ((R / 2 : ℝ) : ℂ) - a = ((R / 2 : ℝ) : ℂ) := by ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith

theorem center_mem_chartL (a : ℂ) {R : ℝ} (hR : 0 < R) :
    a - ((R / 2 : ℝ) : ℂ) ∈ chartL a R := by
  constructor
  · show a - (a - ((R / 2 : ℝ) : ℂ)) ∈ slitPlane
    have : a - (a - ((R / 2 : ℝ) : ℂ)) = ((R / 2 : ℝ) : ℂ) := by ring
    rw [this]
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    simp only [Complex.ofReal_re]
    positivity
  · rw [mem_ball, Complex.dist_eq]
    have : a - ((R / 2 : ℝ) : ℂ) - a = -((R / 2 : ℝ) : ℂ) := by ring
    rw [this, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith

theorem isPreconnected_chartR (a : ℂ) {R : ℝ} (hR : 0 < R) :
    IsPreconnected (chartR a R) := by
  have hmem := center_mem_chartR a hR
  have hstar : StarConvex ℝ (a + ((R / 2 : ℝ) : ℂ)) (chartR a R) :=
    (starConvex_slitChartR a (by positivity : (0:ℝ) < R / 2)).inter
      ((convex_ball a R).starConvex hmem.2)
  exact (hstar.isPathConnected hmem).isConnected.isPreconnected

theorem isPreconnected_chartL (a : ℂ) {R : ℝ} (hR : 0 < R) :
    IsPreconnected (chartL a R) := by
  have hmem := center_mem_chartL a hR
  have hstar : StarConvex ℝ (a - ((R / 2 : ℝ) : ℂ)) (chartL a R) :=
    (starConvex_slitChartL a (by positivity : (0:ℝ) < R / 2)).inter
      ((convex_ball a R).starConvex hmem.2)
  exact (hstar.isPathConnected hmem).isConnected.isPreconnected

/-- The two charts overlap in exactly the two half-plane pieces. -/
theorem chart_inter_eq (a : ℂ) (R : ℝ) :
    chartR a R ∩ chartL a R = overlapU a R ∪ overlapD a R := by
  ext z
  simp only [chartR, chartL, overlapU, overlapD, Set.mem_inter_iff, Set.mem_union,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h₁, hb⟩, ⟨h₂, -⟩⟩
    rcases Complex.mem_slitPlane_iff.mp h₁ with hre₁ | him₁
    · rcases Complex.mem_slitPlane_iff.mp h₂ with hre₂ | him₂
      · exfalso
        have hflip : (a - z).re = -((z - a).re) := by
          simp [Complex.sub_re]
        rw [hflip] at hre₂
        linarith
      · have hflip : (a - z).im = -((z - a).im) := by
          simp [Complex.sub_im]
        rw [hflip] at him₂
        have hne : (z - a).im ≠ 0 := fun h0 => him₂ (by rw [h0, neg_zero])
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inr ⟨h, hb⟩
        · exact Or.inl ⟨h, hb⟩
    · rcases lt_or_gt_of_ne him₁ with h | h
      · exact Or.inr ⟨h, hb⟩
      · exact Or.inl ⟨h, hb⟩
  · rintro (⟨him, hb⟩ | ⟨him, hb⟩)
    · refine ⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr him.ne'), hb⟩,
        ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hb⟩⟩
      have hflip : (a - z).im = -((z - a).im) := by
        simp [Complex.sub_im]
      rw [hflip]
      exact neg_ne_zero.mpr him.ne'
    · refine ⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr him.ne), hb⟩,
        ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hb⟩⟩
      have hflip : (a - z).im = -((z - a).im) := by
        simp [Complex.sub_im]
      rw [hflip]
      exact neg_ne_zero.mpr him.ne

/-! ### The generalized monomial dictionary at `a ± εi` -/

theorem deckClass_monomial' (a : ℂ) (m n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    deckClass (monoRoot₁ a m n) (monoRoot₂ a m n)
      (a + (ε : ℂ) * I) (a - (ε : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * m / n) := by
  have hε0 : (ε : ℝ) ≠ 0 := hε.ne'
  have e₁ : a + (ε : ℂ) * I - a = (ε : ℝ) * I := by ring
  have e₂ : a - (a + (ε : ℂ) * I) = (ε : ℝ) * (-I) := by ring
  have e₃ : a - (ε : ℂ) * I - a = (ε : ℝ) * (-I) := by ring
  have e₄ : a - (a - (ε : ℂ) * I) = (ε : ℝ) * I := by ring
  have l₁ : Complex.log ((ε : ℝ) * I) = Real.log ε + Complex.log I :=
    Complex.log_ofReal_mul hε I_ne_zero
  have l₂ : Complex.log ((ε : ℝ) * (-I)) = Real.log ε + Complex.log (-I) :=
    Complex.log_ofReal_mul hε (neg_ne_zero.mpr I_ne_zero)
  simp only [deckClass, monoRoot₁, monoRoot₂]
  rw [e₁, e₂, e₃, e₄, l₁, l₂, log_I, log_neg_I, ← exp_sub, ← exp_sub, ← exp_sub]
  congr 1
  ring

/-! ### The capstone -/

/-- **Zero-counting meaning of the deck cocycle.** If `f = (z−a)^m · h` on the ball
`B(a,R)` with `h` analytic and nonvanishing there, then ANY local analytic `n`-th roots
of `f` on the two slit charts have deck class `exp(2πi·m/n)` at the basepoints
`a ± (R/2)i` — the enclosed order mod `n`, with no argument principle. -/
theorem deckClass_single_zero {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    {m n : ℕ} (hn : 0 < n)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (z - a) ^ m * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartR a R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartL a R))
    (hpG₁ : ∀ z ∈ chartR a R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartL a R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + ((R / 2 : ℝ) : ℂ) * I) (a - ((R / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * m / n) := by
  -- an analytic n-th root of h on the ball (vacuous zero set)
  have hZloc : ∀ N : ℕ, {s ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h s = 0}.Finite := by
    intro N
    have : {s ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h s = 0} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hs
      exact hh0 s hs.1
    rw [this]
    exact Set.finite_empty
  obtain ⟨r, hran, hrpow⟩ :=
    (exists_root_iff_orders_dvd hn isOpen_ball (convex_ball a R) (mem_ball_self hR)
      hh (hh0 a (mem_ball_self hR)) hZloc).mpr
      (fun ρ hρ h0 => absurd h0 (hh0 ρ hρ))
  -- basepoints and their memberships
  set pP := a + ((R / 2 : ℝ) : ℂ) * I with hpP_def
  set pM := a - ((R / 2 : ℝ) : ℂ) * I with hpM_def
  have hR2 : (0 : ℝ) < R / 2 := by positivity
  have hR2C : ((R / 2 : ℝ) : ℂ) ≠ 0 := by
    simpa using hR2.ne'
  have hballP : pP ∈ ball a R := by
    rw [hpP_def, mem_ball, Complex.dist_eq]
    have : a + ((R / 2 : ℝ) : ℂ) * I - a = ((R / 2 : ℝ) : ℂ) * I := by ring
    rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
    linarith
  have hballM : pM ∈ ball a R := by
    rw [hpM_def, mem_ball, Complex.dist_eq]
    have : a - ((R / 2 : ℝ) : ℂ) * I - a = -(((R / 2 : ℝ) : ℂ) * I) := by ring
    rw [this, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hR2]
    linarith
  have himP : (pP - a).im = R / 2 := by
    rw [hpP_def]
    have : a + ((R / 2 : ℝ) : ℂ) * I - a = ((R / 2 : ℝ) : ℂ) * I := by ring
    rw [this]
    simp
  have himM : (pM - a).im = -(R / 2) := by
    rw [hpM_def]
    have : a - ((R / 2 : ℝ) : ℂ) * I - a = -(((R / 2 : ℝ) : ℂ) * I) := by ring
    rw [this]
    simp
  have hPmemR : pP ∈ chartR a R :=
    ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [himP]; positivity)), hballP⟩
  have hPmemL : pP ∈ chartL a R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hballP⟩
    have : (a - pP).im = -((pP - a).im) := by
      simp [Complex.sub_im]
    rw [this, himP]
    simpa using hR2.ne'
  have hMmemR : pM ∈ chartR a R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hballM⟩
    rw [himM]
    simpa using hR2.ne'
  have hMmemL : pM ∈ chartL a R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hballM⟩
    have : (a - pM).im = -((pM - a).im) := by
      simp [Complex.sub_im]
    rw [this, himM]
    simp only [neg_neg]
    positivity
  -- f does not vanish at the basepoints
  have hfP : f pP ≠ 0 := by
    rw [hfact pP hballP]
    refine mul_ne_zero (pow_ne_zero _ ?_) (hh0 pP hballP)
    have : pP - a = ((R / 2 : ℝ) : ℂ) * I := by rw [hpP_def]; ring
    rw [this]
    exact mul_ne_zero hR2C I_ne_zero
  have hfM : f pM ≠ 0 := by
    rw [hfact pM hballM]
    refine mul_ne_zero (pow_ne_zero _ ?_) (hh0 pM hballM)
    have : pM - a = -(((R / 2 : ℝ) : ℂ) * I) := by rw [hpM_def]; ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero hR2C I_ne_zero)
  -- reference roots on the charts
  set g₁ : ℂ → ℂ := fun z => monoRoot₁ a m n z * r z with hg₁_def
  set g₂ : ℂ → ℂ := fun z => monoRoot₂ a m n z * r z with hg₂_def
  have hg₁an : AnalyticOnNhd ℂ g₁ (chartR a R) := fun z hz =>
    (monoRoot₁_analyticOnNhd a m n z hz.1).mul (hran z hz.2)
  have hg₂an : AnalyticOnNhd ℂ g₂ (chartL a R) := fun z hz =>
    (monoRoot₂_analyticOnNhd a m n z hz.1).mul (hran z hz.2)
  have hpg₁ : ∀ z ∈ chartR a R, g₁ z ^ n = f z := by
    intro z hz
    rw [hg₁_def]
    simp only
    rw [mul_pow, monoRoot₁_pow hn hz.1, hrpow z hz.2, ← hfact z hz.2]
  have hpg₂ : ∀ z ∈ chartL a R, g₂ z ^ n = f z := by
    intro z hz
    rw [hg₂_def]
    simp only
    rw [mul_pow, monoRoot₂_pow hn hz.1, hrpow z hz.2, ← hfact z hz.2]
  -- r does not vanish at the basepoints
  have hrP : r pP ≠ 0 := fun h0 => (hh0 pP hballP) (by
    rw [← hrpow pP hballP, h0, zero_pow hn.ne'])
  have hrM : r pM ≠ 0 := fun h0 => (hh0 pM hballM) (by
    rw [← hrpow pM hballM, h0, zero_pow hn.ne'])
  -- assemble
  have step1 : deckClass G₁ G₂ pP pM = deckClass g₁ g₂ pP pM :=
    deckClass_root_indep hn (isOpen_chartR a R) (isPreconnected_chartR a hR)
      (isOpen_chartL a R) (isPreconnected_chartL a hR)
      hg₁an hG₁ hg₂an hG₂ hpg₁ hpG₁ hpg₂ hpG₂
      hPmemR hPmemL hMmemR hMmemL hfP hfM
  have step2 : deckClass g₁ g₂ pP pM =
      deckClass (monoRoot₁ a m n) (monoRoot₂ a m n) pP pM := by
    rw [hg₁_def, hg₂_def]
    exact deckClass_mul_global hrP hrM
  rw [step1, step2, hpP_def, hpM_def]
  exact deckClass_monomial' a m n hR2

end RHTower
