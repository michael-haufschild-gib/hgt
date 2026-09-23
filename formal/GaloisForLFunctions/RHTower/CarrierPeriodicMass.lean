/-
The periodic mass of the finite carrier's root trace, built as a complete
object.

The mass is modulus-determined and ALL-OR-NOTHING: the pointwise `L²` density
of any root trace is `‖f‖` on the circle, so at even holonomy the self-pairing
attains exactly `2∮‖f‖`, and at odd holonomy every finitely-periodic probe is
annihilated — the periodic mass takes exactly the two values `{0, 2∮‖f‖}`,
independently of every choice.

For a line-symmetric member on a line-centered annulus the holonomy is the port
sign observable, so the mass law reads on two real numbers; a port sign change
moreover forces the member to vanish ON the symmetry line inside the closed
hole (the member is real on the vertical segment, and the segment through the
hole is where the intermediate value theorem places the zero).

The seam: an isolated odd-order zero of any member, dominated by the carrier on
one interior circle, forces the carrier's trace to flip there — the carrier's
periodic mass at that circle is zero.  The completed symmetrized member
instantiates every statement.
-/
import GaloisForLFunctions.RHTower.RootTraceHolonomy

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 The mass is modulus-determined -/

/-- The pointwise `L²` density of any root trace is the member's modulus. -/
theorem trace_normSq_eq_norm {f : ℂ → ℂ} {a : ℂ} {r : ℝ} {U : ℝ → ℂ}
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      Complex.normSq (U θ) = ‖f (circleMap a r θ)‖ := by
  intro θ hθ
  rw [Complex.normSq_eq_norm_sq, ← norm_pow, hUsq θ hθ]

/-- The circle's modulus mass is strictly positive for a member nonvanishing on
the annulus. -/
theorem circle_modulus_mass_pos {f : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ} (h0 : 0 ≤ r₀)
    (hr₀ : r₀ < r) (hrR : r < R)
    (hfc : ContinuousOn f (ball a R \ closedBall a r₀))
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0) :
    0 < ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
      ‖f (circleMap a r θ)‖ := by
  have hπ := Real.pi_pos
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith : -(Real.pi / 2) ≤ 3 * Real.pi / 2)]
    exact (hfc.comp (continuous_circleMap a r).continuousOn
      fun θ _ => circleMap_mem_annulus h0 hr₀ hrR θ).norm
  · intro θ _
    exact norm_pos_iff.mpr (hf0 _ (circleMap_mem_annulus h0 hr₀ hrR θ))
  · linarith

/-- **The self-pairing value at even holonomy**: the doubled trace pairs against
its own conjugate to exactly twice the circle's modulus mass.  The periodic
mass of a closed-up root trace is `2∮‖f‖` — independent of the chosen trace. -/
theorem doubledTrace_self_pairing_value {f : ℂ → ℂ} {a : ℂ} {r : ℝ} {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ))
    (hhol : U (3 * Real.pi / 2) = U (-(Real.pi / 2))) :
    ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace 1 U θ * (starRingEnd ℂ) (doubledTrace 1 U θ)
      = 2 * ((∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
          ‖f (circleMap a r θ)‖ : ℝ) : ℂ) := by
  have hπ := Real.pi_pos
  have hhol1 : U (3 * Real.pi / 2) = (1 : ℂ) * U (-(Real.pi / 2)) := by
    rw [one_mul]
    exact hhol
  have hdc := doubledTrace_continuousOn hUc hhol1
  have hpcont : ContinuousOn (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ))
      (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) :=
    Complex.continuous_conj.comp_continuousOn hdc
  have hpper : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ)) (θ + 2 * Real.pi)
        = (fun θ => (starRingEnd ℂ) (doubledTrace 1 U θ)) θ := by
    intro θ hθ
    have hval : doubledTrace 1 U (θ + 2 * Real.pi) = doubledTrace 1 U θ := by
      show (if θ + 2 * Real.pi ≤ 3 * Real.pi / 2 then U (θ + 2 * Real.pi)
          else 1 * U (θ + 2 * Real.pi - 2 * Real.pi))
        = if θ ≤ 3 * Real.pi / 2 then U θ else 1 * U (θ - 2 * Real.pi)
      rw [if_pos hθ.2]
      by_cases hc : θ + 2 * Real.pi ≤ 3 * Real.pi / 2
      · have hθeq : θ = -(Real.pi / 2) := le_antisymm (by linarith) hθ.1
        subst hθeq
        rw [if_pos hc, show -(Real.pi / 2) + 2 * Real.pi = 3 * Real.pi / 2
          by ring, hhol]
      · rw [if_neg hc, one_mul,
          show θ + 2 * Real.pi - 2 * Real.pi = θ by ring]
    show (starRingEnd ℂ) (doubledTrace 1 U (θ + 2 * Real.pi))
      = (starRingEnd ℂ) (doubledTrace 1 U θ)
    rw [hval]
  have hpair : (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
      doubledTrace 1 U θ * (starRingEnd ℂ) (doubledTrace 1 U θ))
      = (1 + 1) * ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
          U θ * (starRingEnd ℂ) (doubledTrace 1 U θ) :=
    doubledTrace_pairing hUc hhol1 hpcont hpper
  rw [hpair]
  have hEq : EqOn (fun θ => U θ * (starRingEnd ℂ) (doubledTrace 1 U θ))
      (fun θ => ((‖f (circleMap a r θ)‖ : ℝ) : ℂ))
      (uIcc (-(Real.pi / 2)) (3 * Real.pi / 2)) := by
    rw [uIcc_of_le (by linarith : -(Real.pi / 2) ≤ 3 * Real.pi / 2)]
    intro θ hθ
    show U θ * (starRingEnd ℂ) (doubledTrace 1 U θ)
      = ((‖f (circleMap a r θ)‖ : ℝ) : ℂ)
    have hval : doubledTrace 1 U θ = U θ := by
      show (if θ ≤ 3 * Real.pi / 2 then U θ else _) = U θ
      rw [if_pos hθ.2]
    rw [hval, Complex.mul_conj, trace_normSq_eq_norm hUsq θ hθ]
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_ofReal]
  norm_num

/-! ### §2 Trace existence from annulus data -/

/-- A member analytic and nonvanishing on the left slit chart carries an
analytic square root there. -/
theorem exists_chartLA_sqrt {f : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 < r₀)
    (hrR : r₀ < R)
    (hf : AnalyticOnNhd ℂ f (chartLA a r₀ R))
    (hf0 : ∀ z ∈ chartLA a r₀ R, f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (chartLA a r₀ R) ∧
      ∀ z ∈ chartLA a r₀ R, G z ^ (2 : ℕ) = f z := by
  obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
    (isOpen_chartLA a r₀ R) (isSimplyConnected_chartLA a h0 hrR) hf hf0
    (by norm_num : (2 : ℕ) ≠ 0)
  exact ⟨χ, hχan, hχpow⟩

/-- **Trace existence**: any member analytic and nonvanishing on the annulus
carries a continuous square-root trace along every interior circle. -/
theorem exists_circle_trace {f : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ} (h0 : 0 < r₀)
    (hr₀ : r₀ < r) (hrR : r < R)
    (hfan : AnalyticOnNhd ℂ f (ball a R \ closedBall a r₀))
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0) :
    ∃ U : ℝ → ℂ, ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
      ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        U θ ^ (2 : ℕ) = f (circleMap a r θ) := by
  have h0' : (0 : ℝ) ≤ r₀ := le_of_lt h0
  obtain ⟨G₁, hG₁, hpG₁⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hfan z hz.2) (fun z hz => hf0 z hz.2)
  obtain ⟨G₂, hG₂, hpG₂⟩ := exists_chartLA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hfan z hz.2) (fun z hz => hf0 z hz.2)
  have hfT : f (a + (r : ℂ) * I) ≠ 0 :=
    hf0 _ (top_port_mem_charts h0' hr₀ hrR).1.2
  have hG₂T : G₂ (a + (r : ℂ) * I) ≠ 0 := fun h => hfT (by
    rw [← hpG₂ _ (top_port_mem_charts h0' hr₀ hrR).2, h]; ring)
  exact ⟨rootTrace G₁ G₂ a r,
    rootTrace_continuousOn h0' hr₀ hrR hG₁ hG₂ hG₂T,
    rootTrace_sq h0' hr₀ hrR hpG₁ hpG₂ hfT⟩

/-! ### §3 Line symmetry: the holonomy is the port sign observable -/

/-- **The holonomy of a line-symmetric member is the port sign observable**:
positive product of the (real) port values closes every trace up; negative
product flips every trace. -/
theorem trace_holonomy_of_sign {μ : ℝ} {f : ℂ → ℂ} {a : ℂ} {r₀ r R : ℝ}
    (ha : a.re = μ) (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hfan : AnalyticOnNhd ℂ f (ball a R \ closedBall a r₀))
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0)
    (hsym : ∀ z ∈ ball a R \ closedBall a r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = f (circleMap a r θ)) :
    (0 < (f (a + (r : ℂ) * I)).re * (f (a - (r : ℂ) * I)).re →
      U (3 * Real.pi / 2) = U (-(Real.pi / 2))) ∧
    ((f (a + (r : ℂ) * I)).re * (f (a - (r : ℂ) * I)).re < 0 →
      U (3 * Real.pi / 2) = -U (-(Real.pi / 2))) := by
  have h0' : (0 : ℝ) ≤ r₀ := le_of_lt h0
  obtain ⟨G, hG, hpG⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hfan z hz.2) (fun z hz => hf0 z hz.2)
  have hG₂ := reflectedRoot_analyticOnNhd ha hG
  have hpG₂ := reflectedRoot_sq ha hsym hpG
  have hkey := continuous_trace_holonomy h0' hr₀ hrR hG hG₂ hpG hpG₂ hf0
    hUc hUsq
  have hpTre : (a + (r : ℂ) * I).re = μ := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, ha]
    ring
  have hpBre : (a - (r : ℂ) * I).re = μ := by
    rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, ha]
    ring
  have hTmem : a + (r : ℂ) * I ∈ ball a R \ closedBall a r₀ :=
    (top_port_mem_charts h0' hr₀ hrR).1.2
  have hBmem : a - (r : ℂ) * I ∈ ball a R \ closedBall a r₀ :=
    (bottom_port_mem_charts h0' hr₀ hrR).1.2
  have hGT : G (a + (r : ℂ) * I) ^ (2 : ℕ) = f (a + (r : ℂ) * I) :=
    hpG _ (top_port_mem_charts h0' hr₀ hrR).1
  have hGB : G (a - (r : ℂ) * I) ^ (2 : ℕ) = f (a - (r : ℂ) * I) :=
    hpG _ (bottom_port_mem_charts h0' hr₀ hrR).1
  constructor
  · intro hsign
    rw [hkey, deckClass_reflectedRoot_one_of_sign_pos hsym hpTre hpBre hTmem
      hBmem hGT hGB hsign, one_mul]
  · intro hsign
    rw [hkey, deckClass_reflectedRoot_neg_one_of_sign_change hsym hpTre hpBre
      hTmem hBmem hGT hGB hsign, neg_one_mul]

/-! ### §4 A port sign change vanishes on the line inside the hole -/

/-- **Sign change forces an on-line zero in the closed hole**: the member is
real on the symmetry line, continuous on the vertical segment through the hole,
and nonvanishing on the annulus — so a sign flip between the two ports places a
zero on the line at distance at most `r₀` from the center. -/
theorem exists_online_zero_of_port_sign_change {μ : ℝ} {f : ℂ → ℂ} {a : ℂ}
    {r₀ r R : ℝ} (ha : a.re = μ) (h0 : 0 ≤ r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hfc : ContinuousOn f (ball a R))
    (hsymb : ∀ z ∈ ball a R,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, f z ≠ 0)
    (hsign : (f (a + (r : ℂ) * I)).re * (f (a - (r : ℂ) * I)).re < 0) :
    ∃ t : ℝ, |t| ≤ r₀ ∧ f (a + (t : ℂ) * I) = 0 := by
  have hr : 0 < r := lt_of_le_of_lt h0 hr₀
  have hvert_re : ∀ t : ℝ, (a + (t : ℂ) * I).re = μ := by
    intro t
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, ha]
    ring
  have hseg : ∀ t : ℝ, |t| ≤ r → a + (t : ℂ) * I ∈ ball a R := by
    intro t ht
    rw [mem_ball, dist_eq_norm,
      show a + (t : ℂ) * I - a = (t : ℂ) * I by ring]
    simp only [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
    linarith
  have hφc : ContinuousOn (fun t : ℝ => (f (a + (t : ℂ) * I)).re)
      (Icc (-r) r) := by
    apply Complex.continuous_re.comp_continuousOn
    refine hfc.comp (continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).continuousOn ?_
    intro t ht
    exact hseg t (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hrmem : (r : ℝ) ∈ Icc (-r) r := ⟨by linarith, le_refl _⟩
  have hmrmem : (-r : ℝ) ∈ Icc (-r) r := ⟨le_refl _, by linarith⟩
  have hφmr : (f (a + ((-r : ℝ) : ℂ) * I)).re = (f (a - (r : ℂ) * I)).re := by
    rw [show a + ((-r : ℝ) : ℂ) * I = a - (r : ℂ) * I by push_cast; ring]
  have hfinish : ∀ t : ℝ, t ∈ Icc (-r) r →
      (f (a + (t : ℂ) * I)).re = 0 → ∃ t : ℝ, |t| ≤ r₀ ∧
        f (a + (t : ℂ) * I) = 0 := by
    intro t ht h0'
    have him : (f (a + (t : ℂ) * I)).im = 0 :=
      im_eq_zero_of_lineSymmetric_fixed (hvert_re t)
        (hsymb _ (hseg t (abs_le.mpr ⟨ht.1, ht.2⟩)))
    have hft : f (a + (t : ℂ) * I) = 0 := by
      apply Complex.ext
      · rw [Complex.zero_re]
        exact h0'
      · rw [Complex.zero_im]
        exact him
    refine ⟨t, ?_, hft⟩
    by_contra hfar
    push Not at hfar
    have hann : a + (t : ℂ) * I ∈ ball a R \ closedBall a r₀ := by
      refine ⟨hseg t (abs_le.mpr ⟨ht.1, ht.2⟩), ?_⟩
      intro hmem
      rw [mem_closedBall, dist_eq_norm,
        show a + (t : ℂ) * I - a = (t : ℂ) * I by ring] at hmem
      simp only [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs] at hmem
      linarith
    exact hf0 _ hann hft
  rcases mul_neg_iff.mp hsign with ⟨hpos, hneg⟩ | ⟨hneg, hpos⟩
  · have hmem : (0 : ℝ) ∈ Icc ((fun t : ℝ => (f (a + (t : ℂ) * I)).re) (-r))
        ((fun t : ℝ => (f (a + (t : ℂ) * I)).re) r) := by
      show (0 : ℝ) ∈ Icc ((f (a + ((-r : ℝ) : ℂ) * I)).re)
        ((f (a + (r : ℂ) * I)).re)
      rw [hφmr]
      exact ⟨le_of_lt hneg, le_of_lt hpos⟩
    obtain ⟨t, ht, h0'⟩ := isPreconnected_Icc.intermediate_value hmrmem hrmem
      hφc hmem
    exact hfinish t ht h0'
  · have hmem : (0 : ℝ) ∈ Icc ((fun t : ℝ => (f (a + (t : ℂ) * I)).re) r)
        ((fun t : ℝ => (f (a + (t : ℂ) * I)).re) (-r)) := by
      show (0 : ℝ) ∈ Icc ((f (a + (r : ℂ) * I)).re)
        ((f (a + ((-r : ℝ) : ℂ) * I)).re)
      rw [hφmr]
      exact ⟨le_of_lt hneg, le_of_lt hpos⟩
    obtain ⟨t, ht, h0'⟩ := isPreconnected_Icc.intermediate_value hrmem hmrmem
      hφc hmem
    exact hfinish t ht h0'

/-! ### §5 The finite carrier: existence and the mass law -/

/-- The finite carrier's root trace exists at every critical-line-centered
annulus on which the carrier does not vanish. -/
theorem exists_carrier_trace {N : ℕ} (hN : 1 ≤ N) {a : ℂ} {r₀ r R : ℝ}
    (ha : a.re = 1 / 2) (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hR : R ≤ 1 / 2)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, completedSEM N z ≠ 0) :
    ∃ U : ℝ → ℂ, ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)) ∧
      ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        U θ ^ (2 : ℕ) = completedSEM N (circleMap a r θ) :=
  exists_circle_trace h0 hr₀ hrR
    (fun z hz => completedSEM_analyticOnNhd_strip hN z
      (annulus_strip_of_center_half ha hR hz))
    hf0

/-- **The carrier's periodic mass, positive side**: a positive port product
closes every carrier trace up, and the self-pairing attains exactly twice the
carrier's circle modulus mass — which is strictly positive. -/
theorem carrier_periodic_mass_of_sign_pos {N : ℕ} (hN : 1 ≤ N) {a : ℂ}
    {r₀ r R : ℝ} (ha : a.re = 1 / 2) (h0 : 0 < r₀) (hr₀ : r₀ < r)
    (hrR : r < R) (hR : R ≤ 1 / 2)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, completedSEM N z ≠ 0)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = completedSEM N (circleMap a r θ))
    (hsign : 0 < (completedSEM N (a + (r : ℂ) * I)).re
      * (completedSEM N (a - (r : ℂ) * I)).re) :
    U (3 * Real.pi / 2) = U (-(Real.pi / 2)) ∧
    (∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace 1 U θ * (starRingEnd ℂ) (doubledTrace 1 U θ)
      = 2 * ((∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
          ‖completedSEM N (circleMap a r θ)‖ : ℝ) : ℂ)) ∧
    0 < ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2),
        ‖completedSEM N (circleMap a r θ)‖ := by
  have hfan : AnalyticOnNhd ℂ (completedSEM N)
      (ball a R \ closedBall a r₀) := fun z hz =>
    completedSEM_analyticOnNhd_strip hN z
      (annulus_strip_of_center_half ha hR hz)
  have hsym := completedSEM_lineSymmetric_on_annulus (N := N) (r₀ := r₀) ha hR
  have hhol := (trace_holonomy_of_sign (μ := 1 / 2) ha h0 hr₀ hrR hfan hf0
    hsym hUc hUsq).1 hsign
  exact ⟨hhol, doubledTrace_self_pairing_value hUc hUsq hhol,
    circle_modulus_mass_pos (le_of_lt h0) hr₀ hrR hfan.continuousOn hf0⟩

/-- **The carrier's periodic mass, negative side**: a port sign change flips
every carrier trace, annihilates every finitely-periodic probe — the periodic
mass is zero — and forces the carrier to vanish ON the critical line inside
the closed hole. -/
theorem carrier_periodic_mass_of_sign_neg {N : ℕ} (hN : 1 ≤ N) {a : ℂ}
    {r₀ r R : ℝ} (ha : a.re = 1 / 2) (h0 : 0 < r₀) (hr₀ : r₀ < r)
    (hrR : r < R) (hR : R ≤ 1 / 2)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, completedSEM N z ≠ 0)
    {U : ℝ → ℂ}
    (hUc : ContinuousOn U (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hUsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      U θ ^ (2 : ℕ) = completedSEM N (circleMap a r θ))
    (hsign : (completedSEM N (a + (r : ℂ) * I)).re
      * (completedSEM N (a - (r : ℂ) * I)).re < 0) :
    U (3 * Real.pi / 2) = -U (-(Real.pi / 2)) ∧
    (∀ p : ℝ → ℂ,
      ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        p (θ + 2 * Real.pi) = p θ) →
      ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace (-1) U θ * p θ = 0) ∧
    ∃ t : ℝ, |t| ≤ r₀ ∧ completedSEM N (a + (t : ℂ) * I) = 0 := by
  have hfan : AnalyticOnNhd ℂ (completedSEM N)
      (ball a R \ closedBall a r₀) := fun z hz =>
    completedSEM_analyticOnNhd_strip hN z
      (annulus_strip_of_center_half ha hR hz)
  have hsym := completedSEM_lineSymmetric_on_annulus (N := N) (r₀ := r₀) ha hR
  have hhol := (trace_holonomy_of_sign (μ := 1 / 2) ha h0 hr₀ hrR hfan hf0
    hsym hUc hUsq).2 hsign
  have hstrip : ∀ z ∈ ball a R, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    have hb : ‖z - a‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
    have habs : |z.re - a.re| ≤ ‖z - a‖ := by
      have h := Complex.abs_re_le_norm (z - a)
      rwa [Complex.sub_re] at h
    rw [ha] at habs
    rw [abs_le] at habs
    constructor
    · linarith [habs.1]
    · linarith [habs.2]
  have hsymball : ∀ z ∈ ball a R, completedSEM N (lineReflection (1 / 2) z)
      = (starRingEnd ℂ) (completedSEM N z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hstrip z hz
    rw [lineReflection_half]
    exact completedSEM_lineReflection h1 h2
  have hcball : ContinuousOn (completedSEM N) (ball a R) := fun z hz =>
    ((completedSEM_analyticOnNhd_strip hN z (hstrip z hz)).continuousAt).continuousWithinAt
  exact ⟨hhol,
    fun p hp hper => doubledTrace_pairing_eq_zero hUc hhol hp hper,
    exists_online_zero_of_port_sign_change ha (le_of_lt h0) hr₀ hrR hcball
      hsymball hf0 hsign⟩

/-! ### §6 The seam: an odd isolated zero empties the carrier's mass -/

/-- **The seam capstone**: an isolated odd-order zero of any member `g`, with a
carrier `F` nonvanishing on the annulus and dominating the deviation
`‖g − F‖ < ‖F‖` on one interior circle, flips EVERY continuous root trace of
the carrier there — the carrier's periodic mass at that circle is zero. -/
theorem carrier_mass_zero_of_odd_isolated_zero {g F : ℂ → ℂ} {ρ : ℂ}
    {r₀ r R : ℝ} (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hg : AnalyticOnNhd ℂ g (ball ρ R))
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → g z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt g ρ = m) (hodd : Odd m)
    (hFan : AnalyticOnNhd ℂ F (ball ρ R \ closedBall ρ r₀))
    (hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, F z ≠ 0)
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖g (circleMap ρ r θ) - F (circleMap ρ r θ)‖
        < ‖F (circleMap ρ r θ)‖)
    {V : ℝ → ℂ}
    (hVc : ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hVsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      V θ ^ (2 : ℕ) = F (circleMap ρ r θ)) :
    V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
    ∀ p : ℝ → ℂ,
      ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        p (θ + 2 * Real.pi) = p θ) →
      ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace (-1) V θ * p θ = 0 := by
  have h0' : (0 : ℝ) ≤ r₀ := le_of_lt h0
  have hg0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, g z ≠ 0 := by
    intro z hz
    refine hiso z hz.1 fun heq => ?_
    exact hz.2 (by rw [heq, mem_closedBall, dist_self]; exact h0')
  obtain ⟨W, hWc, hWsq⟩ := exists_circle_trace h0 hr₀ hrR
    (fun z hz => hg z hz.1) hg0
  obtain ⟨G₁, hG₁, hpG₁⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hg z hz.2.1) (fun z hz => hg0 z hz.2)
  obtain ⟨G₂, hG₂, hpG₂⟩ := exists_chartLA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hg z hz.2.1) (fun z hz => hg0 z hz.2)
  have hWhol := trace_holonomy_isolated_zero h0' hr₀ hrR hg hiso hm
    hG₁ hG₂ hpG₁ hpG₂ hWc hWsq
  rw [hodd.neg_one_pow] at hWhol
  obtain ⟨C₁, hC₁, hpC₁⟩ := exists_chartRA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hFan z hz.2) (fun z hz => hF0 z hz.2)
  obtain ⟨C₂, hC₂, hpC₂⟩ := exists_chartLA_sqrt h0 (lt_trans hr₀ hrR)
    (fun z hz => hFan z hz.2) (fun z hz => hF0 z hz.2)
  have hVhol := continuous_trace_holonomy h0' hr₀ hrR hC₁ hC₂ hpC₁ hpC₂ hF0
    hVc hVsq
  have hFT : F (ρ + (r : ℂ) * I) ≠ 0 :=
    hF0 _ (top_port_mem_charts h0' hr₀ hrR).1.2
  have hFB : F (ρ - (r : ℂ) * I) ≠ 0 :=
    hF0 _ (bottom_port_mem_charts h0' hr₀ hrR).1.2
  have hσpm := deckClass_level_two
    (hpC₁ _ (top_port_mem_charts h0' hr₀ hrR).1)
    (hpC₂ _ (top_port_mem_charts h0' hr₀ hrR).2)
    (hpC₁ _ (bottom_port_mem_charts h0' hr₀ hrR).1)
    (hpC₂ _ (bottom_port_mem_charts h0' hr₀ hrR).2) hFT hFB
  have htransfer := holonomy_eq_of_circle_domination (f := F) (g := g)
    hVc hWc hVsq hWsq hdom hVhol hWhol hσpm (Or.inr rfl)
  rw [← htransfer, neg_one_mul] at hVhol
  exact ⟨hVhol,
    fun p hp hper => doubledTrace_pairing_eq_zero hVc hVhol hp hper⟩

/-- **The seam at the completed zeta**: an isolated odd-order ξ-zero whose
annulus the finite carrier dominates on one interior circle empties the
carrier's periodic mass at that circle. -/
theorem carrier_mass_zero_of_odd_xi_zero {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    {r₀ r R : ℝ} (h0 : 0 < r₀) (hr₀ : r₀ < r) (hrR : r < R)
    (hstrip : ∀ z ∈ ball ρ R \ closedBall ρ r₀, 0 < z.re ∧ z.re < 1)
    (hiso : ∀ z ∈ ball ρ R, z ≠ ρ → xi z ≠ 0)
    {m : ℕ} (hm : analyticOrderAt xi ρ = m) (hodd : Odd m)
    (hF0 : ∀ z ∈ ball ρ R \ closedBall ρ r₀, completedSEM N z ≠ 0)
    (hdom : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      ‖xi (circleMap ρ r θ) - completedSEM N (circleMap ρ r θ)‖
        < ‖completedSEM N (circleMap ρ r θ)‖)
    {V : ℝ → ℂ}
    (hVc : ContinuousOn V (Icc (-(Real.pi / 2)) (3 * Real.pi / 2)))
    (hVsq : ∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
      V θ ^ (2 : ℕ) = completedSEM N (circleMap ρ r θ)) :
    V (3 * Real.pi / 2) = -V (-(Real.pi / 2)) ∧
    ∀ p : ℝ → ℂ,
      ContinuousOn p (Icc (-(Real.pi / 2)) (3 * Real.pi / 2 + 2 * Real.pi)) →
      (∀ θ ∈ Icc (-(Real.pi / 2)) (3 * Real.pi / 2),
        p (θ + 2 * Real.pi) = p θ) →
      ∫ θ in (-(Real.pi / 2))..(3 * Real.pi / 2 + 2 * Real.pi),
        doubledTrace (-1) V θ * p θ = 0 :=
  carrier_mass_zero_of_odd_isolated_zero h0 hr₀ hrR
    (xi_analyticOnNhd _) hiso hm hodd
    (fun z hz => completedSEM_analyticOnNhd_strip hN z (hstrip z hz))
    hF0 hdom hVc hVsq

end RHTower
