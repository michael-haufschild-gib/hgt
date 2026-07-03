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
        push_cast at this ⊢
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

end RHTower
