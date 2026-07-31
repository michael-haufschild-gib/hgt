/-
Multi-zero additivity of the deck cocycle (MWM lane, A3 extension; task #113+).

Capstone: `deckClass_multi_zero` — on an annulus a < |z−a| < R whose inner hole contains
finitely many zeros ρᵢ (orders mᵢ) of f = ∏(z−ρᵢ)^{mᵢ}·h, ANY local n-th roots of f on
the two slit annulus charts have deck class exp(2πi·(Σmᵢ)/n): **the cocycle is additive
over enclosed zeros**, with no argument principle.

The mechanism that keeps it cheap: for an off-center zero, z−ρ = (z−a)·u(z) with
u(z) = 1 − (ρ−a)/(z−a) mapping the whole annulus into B(1,1) ⊆ slitPlane — so the
correction root exp((m/n)·log u) is GLOBAL and nonvanishing, hence invisible to the deck
class (`deckClass_mul_global`); each enclosed zero contributes exactly its monomial class
at the common anchor a (`deckClass_monomial'`), and the classes multiply
(`deckClass_prod`). Chart preconnectedness comes from polar parametrization: the slit
annulus is the continuous image of a convex rectangle.
-/
import GaloisForLFunctions.RHTower.DeckAssembly

namespace RHTower

open Complex Metric

/-! ### Algebra: the deck class is multiplicative -/

theorem deckClass_mul (F F' G G' : ℂ → ℂ) (pP pM : ℂ) :
    deckClass (fun z => F z * F' z) (fun z => G z * G' z) pP pM =
      deckClass F G pP pM * deckClass F' G' pP pM := by
  simp only [deckClass]
  rw [← div_mul_div_comm (F pP) (G pP), ← div_mul_div_comm (F pM) (G pM),
    ← div_mul_div_comm]

theorem deckClass_prod {ι : Type*} (s : Finset ι) (F G : ι → ℂ → ℂ) (pP pM : ℂ) :
    deckClass (fun z => ∏ i ∈ s, F i z) (fun z => ∏ i ∈ s, G i z) pP pM =
      ∏ i ∈ s, deckClass (F i) (G i) pP pM := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deckClass]
  | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      rw [← ih, ← deckClass_mul]

/-! ### The slit annulus charts -/

/-- Right slit annulus chart. -/
def chartRA (a : ℂ) (r₀ R : ℝ) : Set ℂ :=
  {z | z - a ∈ slitPlane} ∩ (ball a R \ closedBall a r₀)

/-- Left slit annulus chart. -/
def chartLA (a : ℂ) (r₀ R : ℝ) : Set ℂ :=
  {z | a - z ∈ slitPlane} ∩ (ball a R \ closedBall a r₀)

theorem isOpen_chartRA (a : ℂ) (r₀ R : ℝ) : IsOpen (chartRA a r₀ R) :=
  (isOpen_slitPlane.preimage (continuous_id.sub continuous_const)).inter
    (isOpen_ball.sdiff isClosed_closedBall)

theorem isOpen_chartLA (a : ℂ) (r₀ R : ℝ) : IsOpen (chartLA a r₀ R) :=
  (isOpen_slitPlane.preimage (continuous_const.sub continuous_id)).inter
    (isOpen_ball.sdiff isClosed_closedBall)

/-- Polar parametrization map. -/
noncomputable def polarMap (a : ℂ) : ℝ × ℝ → ℂ :=
  fun p => a + (p.1 : ℂ) * exp ((p.2 : ℂ) * I)

theorem continuous_polarMap (a : ℂ) : Continuous (polarMap a) := by
  refine continuous_const.add (Continuous.mul ?_ ?_)
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

theorem norm_polarMap_sub {a : ℂ} {p : ℝ × ℝ} (hp : 0 < p.1) :
    ‖polarMap a p - a‖ = p.1 := by
  rw [polarMap]
  have : a + (p.1 : ℂ) * exp ((p.2 : ℂ) * I) - a = (p.1 : ℂ) * exp ((p.2 : ℂ) * I) := by
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem isPreconnected_chartRA (a : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    IsPreconnected (chartRA a r₀ R) := by
  have himg : chartRA a r₀ R =
      polarMap a '' (Set.Ioo r₀ R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    ext z
    constructor
    · rintro ⟨hslit, hball, hout⟩
      have hz0 : z - a ≠ 0 := slitPlane_ne_zero hslit
      refine ⟨(‖z - a‖, (z - a).arg), ⟨⟨?_, ?_⟩, ⟨neg_pi_lt_arg _, ?_⟩⟩, ?_⟩
      · simpa [Complex.dist_eq] using hout
      · simpa [mem_ball, Complex.dist_eq] using hball
      · rcases lt_or_eq_of_le (arg_le_pi (z - a)) with h | h
        · exact h
        · exfalso
          rcases Complex.mem_slitPlane_iff.mp hslit with hre | him
          · have := (Complex.arg_eq_pi_iff.mp h).1
            linarith
          · exact him (Complex.arg_eq_pi_iff.mp h).2
      · show a + (‖z - a‖ : ℂ) * exp (((z - a).arg : ℂ) * I) = z
        rw [Complex.norm_mul_exp_arg_mul_I]
        ring
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ₁, hρ₂⟩, ⟨hθ₁, hθ₂⟩⟩, rfl⟩
      have hρpos : 0 < ρ := lt_of_le_of_lt h0 hρ₁
      have hnorm : ‖polarMap a (ρ, θ) - a‖ = ρ := norm_polarMap_sub hρpos
      refine ⟨?_, ?_, ?_⟩
      · show polarMap a (ρ, θ) - a ∈ slitPlane
        have hval : polarMap a (ρ, θ) - a = (ρ : ℂ) * exp ((θ : ℂ) * I) := by
          rw [polarMap]; ring
        rw [hval]
        by_cases hsin : Real.sin θ = 0
        · have hθ0 : θ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hθ₁ hθ₂).mp hsin
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          rw [hθ0]
          simpa using hρpos
        · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
          have him : ((ρ : ℂ) * exp ((θ : ℂ) * I)).im = ρ * Real.sin θ := by
            rw [Complex.mul_im]
            simp only [Complex.ofReal_re, Complex.ofReal_im,
              Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
          rw [him]
          exact mul_ne_zero hρpos.ne' hsin
      · rw [mem_ball, Complex.dist_eq, hnorm]
        exact hρ₂
      · rw [mem_closedBall, Complex.dist_eq, hnorm]
        simpa using hρ₁
  rw [himg]
  exact (((convex_Ioo r₀ R).prod (convex_Ioo (-Real.pi) Real.pi)).isPreconnected).image
    _ (continuous_polarMap a).continuousOn

theorem isPreconnected_chartLA (a : ℂ) {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    IsPreconnected (chartLA a r₀ R) := by
  have himg : chartLA a r₀ R =
      polarMap a '' (Set.Ioo r₀ R ×ˢ Set.Ioo 0 (2 * Real.pi)) := by
    ext z
    constructor
    · rintro ⟨hslit, hball, hout⟩
      have hslit' : -(z - a) ∈ slitPlane := by
        have : a - z = -(z - a) := by ring
        rw [← this]
        exact hslit
      have hz0 : z - a ≠ 0 := by
        intro h
        rw [h, neg_zero] at hslit'
        exact Complex.slitPlane_ne_zero hslit' rfl
      have hz0' : -(z - a) ≠ 0 := neg_ne_zero.mpr hz0
      refine ⟨(‖z - a‖, (-(z - a)).arg + Real.pi), ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
      · simpa [Complex.dist_eq] using hout
      · simpa [mem_ball, Complex.dist_eq] using hball
      · have := neg_pi_lt_arg (-(z - a))
        linarith
      · have harglt : (-(z - a)).arg < Real.pi := by
          rcases lt_or_eq_of_le (arg_le_pi (-(z - a))) with h | h
          · exact h
          · exfalso
            rcases Complex.mem_slitPlane_iff.mp hslit' with hre | him
            · have := (Complex.arg_eq_pi_iff.mp h).1
              linarith
            · exact him (Complex.arg_eq_pi_iff.mp h).2
        linarith
      · show a + (‖z - a‖ : ℂ) * exp ((((-(z - a)).arg + Real.pi : ℝ) : ℂ) * I) = z
        have hexp : exp ((((-(z - a)).arg + Real.pi : ℝ) : ℂ) * I) =
            -exp ((((-(z - a)).arg : ℝ) : ℂ) * I) := by
          push_cast
          rw [add_mul, exp_add, exp_pi_mul_I]
          ring
        rw [hexp]
        have hnormeq : ‖z - a‖ = ‖-(z - a)‖ := (norm_neg _).symm
        rw [hnormeq]
        have := Complex.norm_mul_exp_arg_mul_I (-(z - a))
        rw [mul_neg, this]
        ring
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ₁, hρ₂⟩, ⟨hθ₁, hθ₂⟩⟩, rfl⟩
      have hρpos : 0 < ρ := lt_of_le_of_lt h0 hρ₁
      have hnorm : ‖polarMap a (ρ, θ) - a‖ = ρ := norm_polarMap_sub hρpos
      refine ⟨?_, ?_, ?_⟩
      · show a - polarMap a (ρ, θ) ∈ slitPlane
        have hval : a - polarMap a (ρ, θ) = (ρ : ℂ) * exp (((θ - Real.pi : ℝ) : ℂ) * I) := by
          rw [polarMap]
          push_cast
          rw [sub_mul, exp_sub, exp_pi_mul_I]
          field_simp
          ring
        rw [hval]
        by_cases hsin : Real.sin (θ - Real.pi) = 0
        · have hθπ : θ - Real.pi = 0 :=
            (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)).mp hsin
          refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
          rw [hθπ]
          simpa using hρpos
        · refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
          have him : ((ρ : ℂ) * exp (((θ - Real.pi : ℝ) : ℂ) * I)).im =
              ρ * Real.sin (θ - Real.pi) := by
            rw [Complex.mul_im]
            simp only [Complex.ofReal_re, Complex.ofReal_im,
              Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
          rw [him]
          exact mul_ne_zero hρpos.ne' hsin
      · rw [mem_ball, Complex.dist_eq, hnorm]
        exact hρ₂
      · rw [mem_closedBall, Complex.dist_eq, hnorm]
        simpa using hρ₁
  rw [himg]
  exact (((convex_Ioo r₀ R).prod (convex_Ioo 0 (2 * Real.pi))).isPreconnected).image
    _ (continuous_polarMap a).continuousOn

/-! ### The correction root for an off-center enclosed zero -/

theorem corr_mem_slitPlane {a ρ z : ℂ} (h : ‖ρ - a‖ < ‖z - a‖) :
    1 - (ρ - a) / (z - a) ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  have hq : ‖(ρ - a) / (z - a)‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) h)).mpr h
  have hre : |((ρ - a) / (z - a)).re| ≤ ‖(ρ - a) / (z - a)‖ :=
    Complex.abs_re_le_norm _
  have : (1 - (ρ - a) / (z - a)).re = 1 - ((ρ - a) / (z - a)).re := by
    simp [Complex.sub_re]
  rw [this]
  have := abs_le.mp hre
  linarith

/-- The global correction root `exp((m/n)·log(1 − (ρ−a)/(z−a)))`. -/
noncomputable def corrRoot (a ρ : ℂ) (m n : ℕ) : ℂ → ℂ :=
  fun z => exp ((m / n : ℂ) * log (1 - (ρ - a) / (z - a)))

theorem corrRoot_pow {a ρ z : ℂ} {m n : ℕ} (hn : 0 < n) (h : ‖ρ - a‖ < ‖z - a‖) :
    corrRoot a ρ m n z ^ n = (1 - (ρ - a) / (z - a)) ^ m := by
  have h0 : (1 : ℂ) - (ρ - a) / (z - a) ≠ 0 := slitPlane_ne_zero (corr_mem_slitPlane h)
  rw [corrRoot, ← exp_nat_mul]
  have harg : (n : ℂ) * ((m / n : ℂ) * log (1 - (ρ - a) / (z - a))) =
      (m : ℂ) * log (1 - (ρ - a) / (z - a)) := by
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  rw [harg, exp_nat_mul, exp_log h0]

theorem corrRoot_ne_zero (a ρ : ℂ) (m n : ℕ) (z : ℂ) : corrRoot a ρ m n z ≠ 0 :=
  exp_ne_zero _

theorem corrRoot_analyticAt {a ρ z : ℂ} (m n : ℕ) (hz : z ≠ a)
    (h : ‖ρ - a‖ < ‖z - a‖) : AnalyticAt ℂ (corrRoot a ρ m n) z := by
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  have hinner : AnalyticAt ℂ (fun w : ℂ => 1 - (ρ - a) / (w - a)) z := by
    refine analyticAt_const.sub (analyticAt_const.div ?_ hza)
    exact analyticAt_id.sub analyticAt_const
  have hlog : AnalyticAt ℂ (fun w : ℂ => log (1 - (ρ - a) / (w - a))) z :=
    hinner.clog (corr_mem_slitPlane h)
  have hconst : AnalyticAt ℂ (fun _ : ℂ => (m / n : ℂ)) z := analyticAt_const
  exact (hconst.mul hlog).cexp

/-- Off-center factorization on the punctured plane. -/
theorem shifted_factor {a ρ z : ℂ} (hz : z ≠ a) :
    z - ρ = (z - a) * (1 - (ρ - a) / (z - a)) := by
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

/-- Deck classes only see the four point values. -/
theorem deckClass_congr {F F' G G' : ℂ → ℂ} {pP pM : ℂ}
    (h1P : F pP = F' pP) (h1M : F pM = F' pM)
    (h2P : G pP = G' pP) (h2M : G pM = G' pM) :
    deckClass F G pP pM = deckClass F' G' pP pM := by
  simp only [deckClass, h1P, h1M, h2P, h2M]

/-- **Multi-zero additivity.** If `f = ∏ᵢ (z − ρᵢ)^{mᵢ} · h` on `ball a R` with every
`ρᵢ` inside `closedBall a r₀` and `h` analytic nonvanishing, then ANY local analytic
`n`-th roots of `f` on the two slit annulus charts have deck class
`exp(2πi·(Σᵢ mᵢ)/n)` at the basepoints `a ± ((r₀+R)/2)i`: the coarse cocycle counts the
TOTAL enclosed order mod `n`. No argument principle. -/
theorem deckClass_multi_zero {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} (hn : 0 < n)
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (ball a R)) (hh0 : ∀ z ∈ ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * (∑ i ∈ s, (m i : ℂ)) / n) := by
  classical
  set ε : ℝ := (r₀ + R) / 2 with hε_def
  have hεr : r₀ < ε := by rw [hε_def]; linarith
  have hεR : ε < R := by rw [hε_def]; linarith
  have hεpos : 0 < ε := lt_of_le_of_lt h0 hεr
  -- annulus membership facts
  have hchart_ball : ∀ z ∈ chartRA a r₀ R, z ∈ ball a R := fun z hz => hz.2.1
  have hchart_ballL : ∀ z ∈ chartLA a r₀ R, z ∈ ball a R := fun z hz => hz.2.1
  have hchart_far : ∀ z, z ∈ ball a R \ closedBall a r₀ → ∀ i ∈ s, ‖ρ i - a‖ < ‖z - a‖ := by
    intro z hz i hi
    have : r₀ < ‖z - a‖ := by
      have := hz.2
      rw [mem_closedBall, Complex.dist_eq, not_le] at this
      exact this
    exact lt_of_le_of_lt (hρ i hi) this
  have hchart_ne : ∀ z, z ∈ ball a R \ closedBall a r₀ → z ≠ a := by
    intro z hz
    have : r₀ < ‖z - a‖ := by
      have := hz.2
      rw [mem_closedBall, Complex.dist_eq, not_le] at this
      exact this
    intro hza
    rw [hza] at this
    simp at this
    linarith
  -- the h-root on the ball
  have hZloc : ∀ N : ℕ, {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h w = 0}.Finite := by
    intro N
    have : {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | h w = 0} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw
      exact hh0 w hw.1
    rw [this]
    exact Set.finite_empty
  obtain ⟨r, hran, hrpow⟩ :=
    (exists_root_iff_orders_dvd hn isOpen_ball (convex_ball a R)
      (mem_ball_self (lt_of_le_of_lt h0 hrR))
      hh (hh0 a (mem_ball_self (lt_of_le_of_lt h0 hrR))) hZloc).mpr
      (fun w hw h0' => absurd h0' (hh0 w hw))
  -- basepoints
  set pP := a + ((ε : ℝ) : ℂ) * I with hpP_def
  set pM := a - ((ε : ℝ) : ℂ) * I with hpM_def
  have hεC : ((ε : ℝ) : ℂ) ≠ 0 := by
    simpa using hεpos.ne'
  have hPsub : pP - a = ((ε : ℝ) : ℂ) * I := by rw [hpP_def]; ring
  have hMsub : pM - a = -(((ε : ℝ) : ℂ) * I) := by rw [hpM_def]; ring
  have hnormP : ‖pP - a‖ = ε := by
    rw [hPsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hεpos]
  have hnormM : ‖pM - a‖ = ε := by
    rw [hMsub, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hεpos]
  have hannP : pP ∈ ball a R \ closedBall a r₀ := by
    constructor
    · rw [mem_ball, Complex.dist_eq, hnormP]; exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hnormP, not_le]; exact hεr
  have hannM : pM ∈ ball a R \ closedBall a r₀ := by
    constructor
    · rw [mem_ball, Complex.dist_eq, hnormM]; exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hnormM, not_le]; exact hεr
  have himP : (pP - a).im = ε := by rw [hPsub]; simp
  have himM : (pM - a).im = -ε := by rw [hMsub]; simp
  have hPmemR : pP ∈ chartRA a r₀ R :=
    ⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [himP]; exact hεpos.ne')), hannP⟩
  have hPmemL : pP ∈ chartLA a r₀ R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannP⟩
    have : (a - pP).im = -((pP - a).im) := by simp [Complex.sub_im]
    rw [this, himP]
    exact neg_ne_zero.mpr hεpos.ne'
  have hMmemR : pM ∈ chartRA a r₀ R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannM⟩
    rw [himM]
    exact neg_ne_zero.mpr hεpos.ne'
  have hMmemL : pM ∈ chartLA a r₀ R := by
    refine ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannM⟩
    have : (a - pM).im = -((pM - a).im) := by simp [Complex.sub_im]
    rw [this, himM]
    simpa using hεpos.ne'
  -- f nonvanishing at the basepoints
  have hfactor_ne : ∀ p, p ∈ ball a R \ closedBall a r₀ → ∀ i ∈ s, p - ρ i ≠ 0 := by
    intro p hp i hi
    have hlt := hchart_far p hp i hi
    intro h0'
    rw [sub_eq_zero] at h0'
    rw [h0'] at hlt
    have : ‖ρ i - a‖ = ‖ρ i - a‖ := rfl
    exact lt_irrefl _ hlt
  have hfP : f pP ≠ 0 := by
    rw [hfact pP hannP.1]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (hfactor_ne pP hannP i hi)) (hh0 pP hannP.1)
  have hfM : f pM ≠ 0 := by
    rw [hfact pM hannM.1]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi =>
      pow_ne_zero _ (hfactor_ne pM hannM i hi)) (hh0 pM hannM.1)
  -- reference roots
  set g₁ : ℂ → ℂ := fun z =>
    (∏ i ∈ s, (monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z)) * r z with hg₁_def
  set g₂ : ℂ → ℂ := fun z =>
    (∏ i ∈ s, (monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z)) * r z with hg₂_def
  have hg₁an : AnalyticOnNhd ℂ g₁ (chartRA a r₀ R) := by
    intro z hz
    refine AnalyticAt.mul ?_ (hran z hz.2.1)
    refine Finset.analyticAt_fun_prod s (fun i hi => ?_)
    exact (monoRoot₁_analyticOnNhd a (m i) n z hz.1).mul
      (corrRoot_analyticAt (m i) n (hchart_ne z hz.2) (hchart_far z hz.2 i hi))
  have hg₂an : AnalyticOnNhd ℂ g₂ (chartLA a r₀ R) := by
    intro z hz
    refine AnalyticAt.mul ?_ (hran z hz.2.1)
    refine Finset.analyticAt_fun_prod s (fun i hi => ?_)
    exact (monoRoot₂_analyticOnNhd a (m i) n z hz.1).mul
      (corrRoot_analyticAt (m i) n (hchart_ne z hz.2) (hchart_far z hz.2 i hi))
  have hpg₁ : ∀ z ∈ chartRA a r₀ R, g₁ z ^ n = f z := by
    intro z hz
    rw [hg₁_def]
    simp only
    rw [mul_pow, ← Finset.prod_pow, hrpow z hz.2.1, hfact z hz.2.1]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mul_pow, monoRoot₁_pow hn hz.1, corrRoot_pow hn (hchart_far z hz.2 i hi),
      ← mul_pow, ← shifted_factor (hchart_ne z hz.2)]
  have hpg₂ : ∀ z ∈ chartLA a r₀ R, g₂ z ^ n = f z := by
    intro z hz
    rw [hg₂_def]
    simp only
    rw [mul_pow, ← Finset.prod_pow, hrpow z hz.2.1, hfact z hz.2.1]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [mul_pow, monoRoot₂_pow hn hz.1, corrRoot_pow hn (hchart_far z hz.2 i hi),
      ← mul_pow, ← shifted_factor (hchart_ne z hz.2)]
  -- r nonvanishing at basepoints
  have hrP : r pP ≠ 0 := fun h0' => (hh0 pP hannP.1) (by
    rw [← hrpow pP hannP.1, h0', zero_pow hn.ne'])
  have hrM : r pM ≠ 0 := fun h0' => (hh0 pM hannM.1) (by
    rw [← hrpow pM hannM.1, h0', zero_pow hn.ne'])
  -- assemble
  have step1 : deckClass G₁ G₂ pP pM = deckClass g₁ g₂ pP pM :=
    deckClass_root_indep hn (isOpen_chartRA a r₀ R) (isPreconnected_chartRA a h0)
      (isOpen_chartLA a r₀ R) (isPreconnected_chartLA a h0)
      hg₁an hG₁ hg₂an hG₂ hpg₁ hpG₁ hpg₂ hpG₂
      hPmemR hPmemL hMmemR hMmemL hfP hfM
  have step2 : deckClass g₁ g₂ pP pM =
      deckClass (fun z => ∏ i ∈ s, (monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z))
        (fun z => ∏ i ∈ s, (monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z)) pP pM := by
    rw [hg₁_def, hg₂_def]
    exact deckClass_mul_global hrP hrM
  have step3 : deckClass
      (fun z => ∏ i ∈ s, (monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z))
      (fun z => ∏ i ∈ s, (monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z)) pP pM =
      ∏ i ∈ s, deckClass (fun z => monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z)
        (fun z => monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z) pP pM :=
    deckClass_prod s _ _ pP pM
  have step4 : ∀ i ∈ s,
      deckClass (fun z => monoRoot₁ a (m i) n z * corrRoot a (ρ i) (m i) n z)
        (fun z => monoRoot₂ a (m i) n z * corrRoot a (ρ i) (m i) n z) pP pM =
      exp (2 * (Real.pi : ℂ) * I * (m i) / n) := by
    intro i hi
    rw [deckClass_mul_global (corrRoot_ne_zero a (ρ i) (m i) n pP)
      (corrRoot_ne_zero a (ρ i) (m i) n pM), hpP_def, hpM_def]
    exact deckClass_monomial' a (m i) n hεpos
  rw [step1, step2, step3, Finset.prod_congr rfl step4, ← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]

end RHTower

namespace RHTower

open Complex Metric

/-- The two slit annulus charts cover the annulus: a point off both slits is
real from both sides of the center, hence equals the center, which lies in the
hole. -/
theorem annulus_subset_charts {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) :
    ball a R \ closedBall a r₀ ⊆ chartRA a r₀ R ∪ chartLA a r₀ R := by
  intro z hz
  by_cases hR : z - a ∈ slitPlane
  · exact Or.inl ⟨hR, hz⟩
  · refine Or.inr ⟨?_, hz⟩
    rw [Complex.mem_slitPlane_iff] at hR
    have hre : (z - a).re ≤ 0 := le_of_not_gt fun hh => hR (Or.inl hh)
    have him : (z - a).im = 0 := by
      by_contra hh
      exact hR (Or.inr hh)
    show a - z ∈ slitPlane
    rw [Complex.mem_slitPlane_iff]
    rcases lt_or_eq_of_le hre with hlt | heq
    · left
      simp only [Complex.sub_re] at hlt ⊢
      linarith
    · exfalso
      have hza : z = a := by
        apply Complex.ext
        · simp only [Complex.sub_re] at heq
          linarith
        · simp only [Complex.sub_im] at him
          linarith
      exact hz.2 (by rw [hza]; exact mem_closedBall_self h0)

end RHTower
