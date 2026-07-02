/-
# Winding-integral certificates for parametrized closed loops

The band-tower supply of `ExtendedNonSquare.q62_disconnected_of_towerData` certifies loop windings
by explicit integrals `∮ (γ − a)⁻¹ γ'`.  This file is the toolkit:

* `C1Loop` — a closed loop with continuous parametrization/velocity, `C¹` on `[0, 2π]`;
* `exists_int_windInt` — the winding integral is `2πi·ℤ` (running-log FTC, `exp = 1`);
* `windInt_eq_of_norm_sub_lt` / `windInt_eq_zero_of_norm_lt` — the `2π` lattice gap;
* `windInt_eq_on_preconnected` — constancy of `a ↦ ∮ (γ−a)⁻¹γ'` on preconnected sets avoiding the
  loop image (difference estimate + lattice gap + clopen propagation);
* `windInt_add_neg_eq_quadImage` — the quadratic pair rule
  `∮(γ−b)⁻¹γ' + ∮(γ+b)⁻¹γ' = ∮ dlog(f_c∘γ − f_c(b))` — the recursion transporting winding
  certificates down the inverse-branch tower.

Everything is elementary interval-integral analysis; no `π₁`, no homology.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Set Filter

namespace Bottcher

/-- A closed `C¹` loop: continuous parametrization `γ` and velocity `γ'`, differentiable on
`[0, 2π]`, closing up. -/
structure C1Loop where
  γ : ℝ → ℂ
  γ' : ℝ → ℂ
  cont : Continuous γ
  cont' : Continuous γ'
  deriv : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ
  closed : γ (2 * Real.pi) = γ 0

/-- The loop avoids the point `a` (at every parameter). -/
def C1Loop.Avoids (ℓ : C1Loop) (a : ℂ) : Prop := ∀ θ : ℝ, ℓ.γ θ ≠ a

/-- The winding integral `∮ (γ − a)⁻¹ γ'` of the loop about `a`. -/
noncomputable def windInt (ℓ : C1Loop) (a : ℂ) : ℂ :=
  ∫ θ in (0:ℝ)..(2 * Real.pi), (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ

theorem windInt_integrand_continuous (ℓ : C1Loop) {a : ℂ} (hA : ℓ.Avoids a) :
    Continuous (fun θ => (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ) := by
  have hne : ∀ θ : ℝ, ℓ.γ θ - a ≠ 0 := fun θ => sub_ne_zero.mpr (hA θ)
  exact ((ℓ.cont.sub continuous_const).inv₀ hne).mul ℓ.cont'

/-- **Integrality of the winding integral.**  For a closed `C¹` loop avoiding `a`, the winding
integral is an integer multiple of `2πi`: the running integral `E` makes `(γ − a)·exp(−E)`
constant, and closing the loop forces `exp(E(2π)) = 1`. -/
theorem exists_int_windInt (ℓ : C1Loop) {a : ℂ} (hA : ℓ.Avoids a) :
    ∃ n : ℤ, windInt ℓ a = (n : ℂ) * (2 * Real.pi * Complex.I) := by
  have hne : ∀ θ : ℝ, ℓ.γ θ - a ≠ 0 := fun θ => sub_ne_zero.mpr (hA θ)
  have hcont := windInt_integrand_continuous ℓ hA
  set E : ℝ → ℂ := fun u => ∫ θ in (0:ℝ)..u, (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ with hEdef
  have hE : ∀ u : ℝ, HasDerivAt E ((ℓ.γ u - a)⁻¹ * ℓ.γ' u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 u)
      hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  set W : ℝ → ℂ := fun u => (ℓ.γ u - a) * Complex.exp (-E u) with hWdef
  have hW : ∀ u ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt W 0 u := by
    intro u hu
    have h1 : HasDerivAt (fun v => ℓ.γ v - a) (ℓ.γ' u) u := (ℓ.deriv u hu).sub_const a
    have h2 : HasDerivAt (fun v => Complex.exp (-E v))
        (Complex.exp (-E u) * (-((ℓ.γ u - a)⁻¹ * ℓ.γ' u))) u :=
      HasDerivAt.cexp (HasDerivAt.neg (hE u))
    have hprod := HasDerivAt.mul h1 h2
    have hval : ℓ.γ' u * Complex.exp (-E u)
        + (ℓ.γ u - a) * (Complex.exp (-E u) * (-((ℓ.γ u - a)⁻¹ * ℓ.γ' u))) = 0 := by
      field_simp [hne u]
      ring
    rw [hval] at hprod
    exact hprod
  have hWint : (∫ u in (0:ℝ)..(2 * Real.pi), (0:ℂ)) = W (2 * Real.pi) - W 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu => hW u (by rwa [Set.uIcc_of_le (by positivity)] at hu))
      (continuous_const.intervalIntegrable _ _)
  rw [intervalIntegral.integral_zero] at hWint
  have hWeq : W (2 * Real.pi) = W 0 := sub_eq_zero.mp hWint.symm
  have hE0 : E 0 = 0 := intervalIntegral.integral_same
  have hW0 : W 0 = ℓ.γ 0 - a := by
    rw [hWdef]
    show (ℓ.γ 0 - a) * Complex.exp (-E 0) = ℓ.γ 0 - a
    rw [hE0, neg_zero, Complex.exp_zero, mul_one]
  have hW2π : W (2 * Real.pi) = (ℓ.γ 0 - a) * Complex.exp (-E (2 * Real.pi)) := by
    rw [hWdef]
    show (ℓ.γ (2 * Real.pi) - a) * Complex.exp (-E (2 * Real.pi)) = _
    rw [ℓ.closed]
  have hexp1 : Complex.exp (E (2 * Real.pi)) = 1 := by
    have h := hWeq
    rw [hW2π, hW0] at h
    have hcancel : Complex.exp (-E (2 * Real.pi)) = 1 :=
      mul_left_cancel₀ (hne 0) (by rw [h, mul_one])
    rw [Complex.exp_neg] at hcancel
    exact inv_eq_one.mp hcancel
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  refine ⟨n, ?_⟩
  show E (2 * Real.pi) = _
  rw [hn]

/-- **The `2π` lattice gap.**  Two winding integrals within distance `< 2π` are equal. -/
theorem windInt_eq_of_norm_sub_lt (ℓ₁ ℓ₂ : C1Loop) {a b : ℂ}
    (hA : ℓ₁.Avoids a) (hB : ℓ₂.Avoids b)
    (hlt : ‖windInt ℓ₁ a - windInt ℓ₂ b‖ < 2 * Real.pi) :
    windInt ℓ₁ a = windInt ℓ₂ b := by
  obtain ⟨n, hn⟩ := exists_int_windInt ℓ₁ hA
  obtain ⟨p, hp⟩ := exists_int_windInt ℓ₂ hB
  rw [hn, hp, ← sub_mul] at hlt
  rw [hn, hp]
  have h2π : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [show ((2:ℂ) * Real.pi * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I from by ring]
    at hlt ⊢
  rw [norm_mul, h2π] at hlt
  have hnp : n = p := by
    by_contra hne
    have hcast : ((n:ℂ) - p) = ((n - p : ℤ) : ℂ) := by push_cast; ring
    have hnz : (n - p : ℤ) ≠ 0 := sub_ne_zero.mpr hne
    have h1 : (1 : ℝ) ≤ ‖((n:ℂ) - p)‖ := by
      rw [hcast, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hnz
    nlinarith [Real.pi_pos]
  rw [hnp]

/-- **Small winding is zero.**  A winding integral of norm `< 2π` vanishes. -/
theorem windInt_eq_zero_of_norm_lt (ℓ : C1Loop) {a : ℂ} (hA : ℓ.Avoids a)
    (hlt : ‖windInt ℓ a‖ < 2 * Real.pi) : windInt ℓ a = 0 := by
  obtain ⟨n, hn⟩ := exists_int_windInt ℓ hA
  rw [hn] at hlt ⊢
  have h2π : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [show ((2:ℂ) * Real.pi * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I from by ring]
    at hlt ⊢
  rw [norm_mul, h2π] at hlt
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      rw [Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hne
    nlinarith [Real.pi_pos]
  rw [hn0]
  simp

/-- The image of a loop over one period is compact. -/
theorem C1Loop.isCompact_image (ℓ : C1Loop) :
    IsCompact (ℓ.γ '' Set.Icc (0:ℝ) (2 * Real.pi)) :=
  (isCompact_Icc).image ℓ.cont

/-- A velocity bound over the period. -/
theorem C1Loop.exists_velocity_bound (ℓ : C1Loop) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖ℓ.γ' θ‖ ≤ M := by
  obtain ⟨θ₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity)) (ℓ.cont'.norm.continuousOn
      (s := Set.Icc (0:ℝ) (2 * Real.pi)))
  exact ⟨‖ℓ.γ' θ₀‖, norm_nonneg _, fun θ hθ => hmax hθ⟩

/-- **Constancy of the winding on preconnected avoided sets.**  If `S` is preconnected and every
point of `S` is avoided by the loop, then `a ↦ windInt ℓ a` is constant on `S`.  Difference
estimate + `2π` lattice gap + clopen propagation through ball covers. -/
theorem windInt_eq_on_preconnected (ℓ : C1Loop) {S : Set ℂ} (hS : IsPreconnected S)
    (hSA : ∀ z ∈ S, ℓ.Avoids z) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    windInt ℓ a = windInt ℓ b := by
  obtain ⟨M, hM0, hM⟩ := ℓ.exists_velocity_bound
  -- local equality around any avoided point
  have hloc : ∀ z₀, ℓ.Avoids z₀ → ∃ ε > 0, ∀ z, ℓ.Avoids z → dist z z₀ < ε →
      windInt ℓ z = windInt ℓ z₀ := by
    intro z₀ hz₀A
    have hne : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ℓ.γ θ ≠ z₀ := fun θ _ => hz₀A θ
    obtain ⟨θ₁, hθ₁, hmin⟩ := isCompact_Icc.exists_isMinOn
      (Set.nonempty_Icc.mpr (by positivity : (0:ℝ) ≤ 2 * Real.pi))
      ((continuous_const.dist ℓ.cont).continuousOn
        (s := Set.Icc (0:ℝ) (2 * Real.pi)))
    set δ : ℝ := dist z₀ (ℓ.γ θ₁) with hδdef
    have hδpos : 0 < δ := dist_pos.mpr (fun h => hne θ₁ hθ₁ h.symm)
    have hδle : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), δ ≤ dist z₀ (ℓ.γ θ) :=
      fun θ hθ => hmin hθ
    have hM1 : (0:ℝ) < M + 1 := by linarith
    set ε : ℝ := min (δ / 2) (δ ^ 2 / (4 * (M + 1))) with hεdef
    have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
    refine ⟨ε, hεpos, ?_⟩
    intro z hzA hdist
    have hlow₀ : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), δ ≤ ‖ℓ.γ θ - z₀‖ := by
      intro θ hθ
      rw [show ‖ℓ.γ θ - z₀‖ = dist z₀ (ℓ.γ θ) from by rw [dist_comm, dist_eq_norm]]
      exact hδle θ hθ
    have hlow : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), δ / 2 ≤ ‖ℓ.γ θ - z‖ := by
      intro θ hθ
      have h1 : δ ≤ ‖ℓ.γ θ - z₀‖ := hlow₀ θ hθ
      have h2 : ‖ℓ.γ θ - z₀‖ - ‖z - z₀‖ ≤ ‖ℓ.γ θ - z‖ := by
        have h3 := norm_sub_norm_le (ℓ.γ θ - z₀) (z - z₀)
        have harr : (ℓ.γ θ - z₀) - (z - z₀) = ℓ.γ θ - z := by ring
        rw [harr] at h3
        linarith
      have h3 : ‖z - z₀‖ < δ / 2 := by
        rw [← dist_eq_norm]
        exact lt_of_lt_of_le hdist (min_le_left _ _)
      linarith
    have hdiffint : windInt ℓ z - windInt ℓ z₀
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            ((ℓ.γ θ - z)⁻¹ * ℓ.γ' θ - (ℓ.γ θ - z₀)⁻¹ * ℓ.γ' θ) :=
      (intervalIntegral.integral_sub
        ((windInt_integrand_continuous ℓ hzA).intervalIntegrable _ _)
        ((windInt_integrand_continuous ℓ hz₀A).intervalIntegrable _ _)).symm
    have hbound : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * Real.pi),
        ‖(ℓ.γ θ - z)⁻¹ * ℓ.γ' θ - (ℓ.γ θ - z₀)⁻¹ * ℓ.γ' θ‖
          ≤ (ε * (M + 1)) / ((δ / 2) * δ) := by
      intro θ hθ
      have hθI : θ ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at hθ
        exact ⟨le_of_lt hθ.1, hθ.2⟩
      have hnz : ℓ.γ θ - z ≠ 0 := sub_ne_zero.mpr (hzA θ)
      have hnz₀ : ℓ.γ θ - z₀ ≠ 0 := sub_ne_zero.mpr (hz₀A θ)
      have hkey : (ℓ.γ θ - z)⁻¹ * ℓ.γ' θ - (ℓ.γ θ - z₀)⁻¹ * ℓ.γ' θ
          = ((z - z₀) / ((ℓ.γ θ - z) * (ℓ.γ θ - z₀))) * ℓ.γ' θ := by
        field_simp
        ring
      rw [hkey, norm_mul, norm_div, norm_mul]
      have h1 : ‖z - z₀‖ ≤ ε := by
        rw [← dist_eq_norm]; exact le_of_lt hdist
      have h2 : (δ/2) * δ ≤ ‖ℓ.γ θ - z‖ * ‖ℓ.γ θ - z₀‖ :=
        mul_le_mul (hlow θ hθI) (hlow₀ θ hθI) (le_of_lt hδpos) (norm_nonneg _)
      have h3 : ‖ℓ.γ' θ‖ ≤ M + 1 := le_trans (hM θ hθI) (by linarith)
      have hpos2 : (0:ℝ) < (δ/2) * δ := by positivity
      calc ‖z - z₀‖ / (‖ℓ.γ θ - z‖ * ‖ℓ.γ θ - z₀‖) * ‖ℓ.γ' θ‖
          ≤ (ε / ((δ/2) * δ)) * (M + 1) := by
            apply mul_le_mul _ h3 (norm_nonneg _) (by positivity)
            exact div_le_div₀ (le_trans (norm_nonneg _) h1) h1 hpos2 h2
        _ = (ε * (M + 1)) / ((δ / 2) * δ) := by ring
    have hnorm : ‖windInt ℓ z - windInt ℓ z₀‖
        ≤ ((ε * (M + 1)) / ((δ / 2) * δ)) * |2 * Real.pi - 0| := by
      rw [hdiffint]
      exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hεbound : ε ≤ δ ^ 2 / (4 * (M + 1)) := min_le_right _ _
    have hfinal : ‖windInt ℓ z - windInt ℓ z₀‖ < 2 * Real.pi := by
      have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
        rw [sub_zero]; exact abs_of_pos (by positivity)
      rw [habs] at hnorm
      have hstep : (ε * (M + 1)) / ((δ / 2) * δ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 2)]
        have := mul_le_mul_of_nonneg_right hεbound (le_of_lt hM1)
        calc ε * (M + 1) * 2 ≤ (δ ^ 2 / (4 * (M + 1))) * (M + 1) * 2 := by nlinarith
          _ = δ ^ 2 / 2 := by field_simp; ring
          _ = 1 * ((δ / 2) * δ) := by ring
      have := le_trans hnorm (by nlinarith [Real.pi_pos] :
        ((ε * (M + 1)) / ((δ / 2) * δ)) * (2 * Real.pi) ≤ (1/2) * (2 * Real.pi))
      nlinarith [Real.pi_pos]
    exact windInt_eq_of_norm_sub_lt ℓ ℓ hzA hz₀A hfinal
  -- clopen propagation across the preconnected S via ball covers
  by_contra hcon
  choose ε hεpos hεspec using hloc
  set U : Set ℂ := ⋃ (z₀ : ℂ) (h : z₀ ∈ S ∧ windInt ℓ z₀ = windInt ℓ a),
    Metric.ball z₀ (ε z₀ (hSA z₀ h.1)) with hUdef
  set V : Set ℂ := ⋃ (z₀ : ℂ) (h : z₀ ∈ S ∧ windInt ℓ z₀ ≠ windInt ℓ a),
    Metric.ball z₀ (ε z₀ (hSA z₀ h.1)) with hVdef
  have hUo : IsOpen U := isOpen_iUnion (fun z₀ => isOpen_iUnion (fun _ => Metric.isOpen_ball))
  have hVo : IsOpen V := isOpen_iUnion (fun z₀ => isOpen_iUnion (fun _ => Metric.isOpen_ball))
  have hcover : S ⊆ U ∪ V := by
    intro z hz
    by_cases hw : windInt ℓ z = windInt ℓ a
    · exact Or.inl (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨⟨hz, hw⟩,
        Metric.mem_ball_self (hεpos z (hSA z hz))⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨⟨hz, hw⟩,
        Metric.mem_ball_self (hεpos z (hSA z hz))⟩⟩)
  have hSU : ∀ z ∈ S ∩ U, windInt ℓ z = windInt ℓ a := by
    rintro z ⟨hzS, hzU⟩
    obtain ⟨z₀, hz₀⟩ := Set.mem_iUnion.mp hzU
    obtain ⟨h₀, hball⟩ := Set.mem_iUnion.mp hz₀
    rw [hεspec z₀ (hSA z₀ h₀.1) z (hSA z hzS) (Metric.mem_ball.mp hball)]
    exact h₀.2
  have hSV : ∀ z ∈ S ∩ V, windInt ℓ z ≠ windInt ℓ a := by
    rintro z ⟨hzS, hzV⟩
    obtain ⟨z₀, hz₀⟩ := Set.mem_iUnion.mp hzV
    obtain ⟨h₀, hball⟩ := Set.mem_iUnion.mp hz₀
    rw [hεspec z₀ (hSA z₀ h₀.1) z (hSA z hzS) (Metric.mem_ball.mp hball)]
    exact h₀.2
  have hneU : (S ∩ U).Nonempty := by
    refine ⟨a, ha, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨⟨ha, rfl⟩,
      Metric.mem_ball_self (hεpos a (hSA a ha))⟩⟩⟩
  have hneV : (S ∩ V).Nonempty := by
    refine ⟨b, hb, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨⟨hb, fun h => hcon h.symm⟩,
      Metric.mem_ball_self (hεpos b (hSA b hb))⟩⟩⟩
  obtain ⟨w, hwS, hwU, hwV⟩ := hS U V hUo hVo hcover hneU hneV
  exact hSV w ⟨hwS, hwV⟩ (hSU w ⟨hwS, hwU⟩)

/-- The quadratic image loop `f_c ∘ γ` with chain-rule velocity `2γγ'`. -/
noncomputable def C1Loop.quadImage (ℓ : C1Loop) (c : ℂ) : C1Loop where
  γ := fun θ => quadratic c (ℓ.γ θ)
  γ' := fun θ => 2 * ℓ.γ θ * ℓ.γ' θ
  cont := (continuous_quadratic c).comp ℓ.cont
  cont' := (continuous_const.mul ℓ.cont).mul ℓ.cont'
  deriv := by
    intro θ hθ
    have h1 : HasDerivAt (quadratic c) (2 * ℓ.γ θ) (ℓ.γ θ) := by
      have h0 : HasDerivAt (fun x : ℂ => x ^ 2 + c) (2 * ℓ.γ θ) (ℓ.γ θ) := by
        simpa using (hasDerivAt_pow 2 (ℓ.γ θ)).add_const c
      exact h0
    exact h1.comp θ (ℓ.deriv θ hθ)
  closed := by simp only [ℓ.closed]

/-- **The quadratic pair rule.**  For a loop avoiding both square roots `±b` of `f_c(b) − c`,
`∮(γ−b)⁻¹γ' + ∮(γ+b)⁻¹γ' = ∮ d log (f_c∘γ − f_c(b))`.  This is the certificate-transport engine:
windings of the lift about a preimage pair sum to the winding of the image loop about the image
point. -/
theorem windInt_add_neg_eq_quadImage (ℓ : C1Loop) (c b : ℂ)
    (hb : ℓ.Avoids b) (hnb : ℓ.Avoids (-b)) :
    windInt ℓ b + windInt ℓ (-b) = windInt (ℓ.quadImage c) (quadratic c b) := by
  have hpt : ∀ θ : ℝ, (ℓ.γ θ - b)⁻¹ * ℓ.γ' θ + (ℓ.γ θ - (-b))⁻¹ * ℓ.γ' θ
      = (quadratic c (ℓ.γ θ) - quadratic c b)⁻¹ * (2 * ℓ.γ θ * ℓ.γ' θ) := by
    intro θ
    have hnzb : ℓ.γ θ - b ≠ 0 := sub_ne_zero.mpr (hb θ)
    have hnznb : ℓ.γ θ + b ≠ 0 := by
      intro h
      exact hnb θ (by linear_combination h)
    have hquad : quadratic c (ℓ.γ θ) - quadratic c b = (ℓ.γ θ - b) * (ℓ.γ θ + b) := by
      simp only [quadratic]
      ring
    rw [hquad, sub_neg_eq_add]
    field_simp
    ring
  rw [windInt, windInt, ← intervalIntegral.integral_add
    ((windInt_integrand_continuous ℓ hb).intervalIntegrable _ _)
    ((windInt_integrand_continuous ℓ hnb).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr (fun θ _ => hpt θ)

/-- Avoidance transport through the quadratic: the image loop avoids `f_c(b)` iff the loop avoids
both `±b`. -/
theorem C1Loop.quadImage_avoids (ℓ : C1Loop) (c b : ℂ)
    (hb : ℓ.Avoids b) (hnb : ℓ.Avoids (-b)) :
    (ℓ.quadImage c).Avoids (quadratic c b) := by
  intro θ h
  have h2 : (ℓ.γ θ - b) * (ℓ.γ θ + b) = 0 := by
    have hquad : quadratic c (ℓ.γ θ) - quadratic c b = (ℓ.γ θ - b) * (ℓ.γ θ + b) := by
      simp only [quadratic]; ring
    rw [← hquad]
    exact sub_eq_zero.mpr h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hb θ (sub_eq_zero.mp h3)
  · exact hnb θ (by linear_combination h3)

end Bottcher

namespace Bottcher
open Complex Set

/-- The round circle of radius `ρ` about `0` as a `C1Loop`. -/
noncomputable def circleLoop (ρ : ℝ) : C1Loop where
  γ := circleMap 0 ρ
  γ' := fun θ => circleMap 0 ρ θ * Complex.I
  cont := continuous_circleMap 0 ρ
  cont' := (continuous_circleMap 0 ρ).mul continuous_const
  deriv := fun θ _ => hasDerivAt_circleMap 0 ρ θ
  closed := by
    simpa using periodic_circleMap 0 ρ 0

/-- **Base winding of the round circle**: `∮ (z − a)⁻¹ dz = 2πi` about any interior point. -/
theorem windInt_circleLoop {ρ : ℝ} (_hρ : 0 < ρ) {a : ℂ} (ha : ‖a‖ < ρ) :
    windInt (circleLoop ρ) a = 2 * (Real.pi : ℂ) * Complex.I := by
  have hmem : a ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]; exact ha
  have hcirc := circleIntegral.integral_sub_inv_of_mem_ball hmem
  rw [circleIntegral] at hcirc
  rw [← hcirc]
  apply intervalIntegral.integral_congr
  intro θ _
  show ((circleLoop ρ).γ θ - a)⁻¹ * (circleLoop ρ).γ' θ
    = deriv (circleMap 0 ρ) θ • (circleMap 0 ρ θ - a)⁻¹
  rw [deriv_circleMap]
  show (circleMap 0 ρ θ - a)⁻¹ * (circleMap 0 ρ θ * Complex.I)
    = (circleMap 0 ρ θ * Complex.I) • (circleMap 0 ρ θ - a)⁻¹
  rw [smul_eq_mul]
  ring
/-- Norm bound over the period for any continuous function. -/
private theorem exists_norm_bound_Icc (f : ℝ → ℂ) (hf : Continuous f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖f θ‖ ≤ B := by
  obtain ⟨θ₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by positivity)) (hf.norm.continuousOn
      (s := Set.Icc (0:ℝ) (2 * Real.pi)))
  exact ⟨‖f θ₀‖, norm_nonneg _, fun θ hθ => hmax hθ⟩

/-- **The dog-on-a-leash lemma.**  If `g` stays pointwise closer to `ℓ` than `ℓ` is to `a`, the
two loops have the same winding about `a`.  Linear homotopy, uniform difference estimate, `2π`
lattice gap, clopen propagation over `[0, 1]`. -/
theorem windInt_eq_of_leash (ℓ g : C1Loop) (a : ℂ)
    (hle : ∀ θ : ℝ, ‖g.γ θ - ℓ.γ θ‖ < ‖ℓ.γ θ - a‖) :
    windInt g a = windInt ℓ a := by
  classical
  -- the linear homotopy
  let H : ℝ → C1Loop := fun t =>
    { γ := fun θ => ℓ.γ θ + (t : ℂ) * (g.γ θ - ℓ.γ θ)
      γ' := fun θ => ℓ.γ' θ + (t : ℂ) * (g.γ' θ - ℓ.γ' θ)
      cont := ℓ.cont.add (continuous_const.mul (g.cont.sub ℓ.cont))
      cont' := ℓ.cont'.add (continuous_const.mul (g.cont'.sub ℓ.cont'))
      deriv := fun θ hθ => (ℓ.deriv θ hθ).add
        (((g.deriv θ hθ).sub (ℓ.deriv θ hθ)).const_mul (t : ℂ))
      closed := by simp only [ℓ.closed, g.closed] }
  have hHγ : ∀ t θ, (H t).γ θ = ℓ.γ θ + (t : ℂ) * (g.γ θ - ℓ.γ θ) := fun t θ => rfl
  have hHγ' : ∀ t θ, (H t).γ' θ = ℓ.γ' θ + (t : ℂ) * (g.γ' θ - ℓ.γ' θ) := fun t θ => rfl
  -- pointwise margins on [0,1]
  have hmargin : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ θ : ℝ,
      ‖ℓ.γ θ - a‖ - ‖g.γ θ - ℓ.γ θ‖ ≤ ‖(H t).γ θ - a‖ := by
    intro t ht θ
    have harr : (H t).γ θ - a = (ℓ.γ θ - a) + (t:ℂ) * (g.γ θ - ℓ.γ θ) := by
      rw [hHγ]; ring
    have htri : ‖(ℓ.γ θ - a)‖ - ‖(t:ℂ) * (g.γ θ - ℓ.γ θ)‖ ≤ ‖(H t).γ θ - a‖ := by
      have h := norm_sub_norm_le (ℓ.γ θ - a) (-((t:ℂ) * (g.γ θ - ℓ.γ θ)))
      rw [norm_neg, sub_neg_eq_add, harr.symm] at h
      exact h
    have hnt : ‖(t:ℂ) * (g.γ θ - ℓ.γ θ)‖ ≤ ‖g.γ θ - ℓ.γ θ‖ := by
      rw [norm_mul]
      have h1 : ‖(t:ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact ht.2
      nlinarith [norm_nonneg (g.γ θ - ℓ.γ θ)]
    linarith
  have hAvoid : ∀ t ∈ Set.Icc (0:ℝ) 1, (H t).Avoids a := by
    intro t ht θ h0
    have h1 := hmargin t ht θ
    rw [h0] at h1
    simp only [sub_self, norm_zero] at h1
    linarith [hle θ]
  -- uniform margin and bounds over the period
  obtain ⟨θκ, hθκ, hκmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by positivity : (0:ℝ) ≤ 2 * Real.pi))
    (((ℓ.cont.sub continuous_const).norm.sub ((g.cont.sub ℓ.cont).norm)).continuousOn
      (s := Set.Icc (0:ℝ) (2 * Real.pi)))
  set κ : ℝ := ‖ℓ.γ θκ - a‖ - ‖g.γ θκ - ℓ.γ θκ‖ with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]; linarith [hle θκ]
  have hκle : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      κ ≤ ‖ℓ.γ θ - a‖ - ‖g.γ θ - ℓ.γ θ‖ := fun θ hθ => hκmin hθ
  have hκH : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      κ ≤ ‖(H t).γ θ - a‖ := fun t ht θ hθ =>
    le_trans (hκle θ hθ) (hmargin t ht θ)
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_bound_Icc _ (g.cont.sub ℓ.cont)
  obtain ⟨B₂, hB₂0, hB₂⟩ := exists_norm_bound_Icc _ ℓ.cont'
  obtain ⟨B₃, hB₃0, hB₃⟩ := exists_norm_bound_Icc _ (g.cont'.sub ℓ.cont')
  set C : ℝ := B₃ / κ + B₁ * (B₂ + B₃) / (κ * κ) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; positivity
  set ε : ℝ := Real.pi / (2 * Real.pi * (C + 1)) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  -- uniform local equality of the homotopy winding
  have hloc : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s ∈ Set.Icc (0:ℝ) 1, |t - s| < ε →
      windInt (H t) a = windInt (H s) a := by
    intro t ht s hs hts
    have hAt := hAvoid t ht
    have hAs := hAvoid s hs
    have hdiffint : windInt (H t) a - windInt (H s) a
        = ∫ θ in (0:ℝ)..(2 * Real.pi),
            (((H t).γ θ - a)⁻¹ * (H t).γ' θ - ((H s).γ θ - a)⁻¹ * (H s).γ' θ) :=
      (intervalIntegral.integral_sub
        ((windInt_integrand_continuous (H t) hAt).intervalIntegrable _ _)
        ((windInt_integrand_continuous (H s) hAs).intervalIntegrable _ _)).symm
    have hbound : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * Real.pi),
        ‖((H t).γ θ - a)⁻¹ * (H t).γ' θ - ((H s).γ θ - a)⁻¹ * (H s).γ' θ‖
          ≤ |t - s| * C := by
      intro θ hθ
      have hθI : θ ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at hθ
        exact ⟨le_of_lt hθ.1, hθ.2⟩
      have hκt : κ ≤ ‖(H t).γ θ - a‖ := hκH t ht θ hθI
      have hκs : κ ≤ ‖(H s).γ θ - a‖ := hκH s hs θ hθI
      have hnzt : (H t).γ θ - a ≠ 0 := sub_ne_zero.mpr (hAt θ)
      have hnzs : (H s).γ θ - a ≠ 0 := sub_ne_zero.mpr (hAs θ)
      have hPQ : (H t).γ' θ - (H s).γ' θ = ((t:ℂ) - s) * (g.γ' θ - ℓ.γ' θ) := by
        show (ℓ.γ' θ + (t:ℂ) * (g.γ' θ - ℓ.γ' θ))
            - (ℓ.γ' θ + (s:ℂ) * (g.γ' θ - ℓ.γ' θ)) = _
        ring
      have hYX : ((H s).γ θ - a) - ((H t).γ θ - a)
          = ((s:ℂ) - t) * (g.γ θ - ℓ.γ θ) := by
        show (ℓ.γ θ + (s:ℂ) * (g.γ θ - ℓ.γ θ) - a)
            - (ℓ.γ θ + (t:ℂ) * (g.γ θ - ℓ.γ θ) - a) = _
        ring
      have hsplit : ((H t).γ θ - a)⁻¹ * (H t).γ' θ - ((H s).γ θ - a)⁻¹ * (H s).γ' θ
          = ((H t).γ θ - a)⁻¹ * (((t:ℂ) - s) * (g.γ' θ - ℓ.γ' θ))
            + (((s:ℂ) - t) * (g.γ θ - ℓ.γ θ) / (((H t).γ θ - a) * ((H s).γ θ - a)))
              * (H s).γ' θ := by
        rw [← hPQ, ← hYX]
        set X : ℂ := (H t).γ θ - a
        set Y : ℂ := (H s).γ θ - a
        field_simp
        ring
      rw [hsplit]
      have hterm1 : ‖((H t).γ θ - a)⁻¹ * (((t:ℂ) - s) * (g.γ' θ - ℓ.γ' θ))‖
          ≤ |t - s| * (B₃ / κ) := by
        rw [norm_mul, norm_mul, norm_inv]
        have h1 : ‖((t:ℂ) - s)‖ = |t - s| := by
          rw [show ((t:ℂ) - s) = ((t - s : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs]
        rw [h1]
        have h2 : ‖((H t).γ θ - a)‖⁻¹ ≤ κ⁻¹ :=
          inv_anti₀ hκpos hκt
        have h3 : ‖g.γ' θ - ℓ.γ' θ‖ ≤ B₃ := hB₃ θ hθI
        calc ‖((H t).γ θ - a)‖⁻¹ * (|t - s| * ‖g.γ' θ - ℓ.γ' θ‖)
            ≤ κ⁻¹ * (|t - s| * B₃) := by
              apply mul_le_mul h2 _ (by positivity) (by positivity)
              exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
          _ = |t - s| * (B₃ / κ) := by field_simp
      have hterm2 : ‖(((s:ℂ) - t) * (g.γ θ - ℓ.γ θ)
            / (((H t).γ θ - a) * ((H s).γ θ - a))) * (H s).γ' θ‖
          ≤ |t - s| * (B₁ * (B₂ + B₃) / (κ * κ)) := by
        rw [norm_mul, norm_div, norm_mul, norm_mul]
        have h1 : ‖((s:ℂ) - t)‖ = |t - s| := by
          rw [show ((s:ℂ) - t) = ((s - t : ℝ) : ℂ) from by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        have h2 : ‖g.γ θ - ℓ.γ θ‖ ≤ B₁ := hB₁ θ hθI
        have h3 : κ * κ ≤ ‖(H t).γ θ - a‖ * ‖(H s).γ θ - a‖ :=
          mul_le_mul hκt hκs (le_of_lt hκpos) (norm_nonneg _)
        have h4 : ‖(H s).γ' θ‖ ≤ B₂ + B₃ := by
          rw [hHγ']
          calc ‖ℓ.γ' θ + (s:ℂ) * (g.γ' θ - ℓ.γ' θ)‖
              ≤ ‖ℓ.γ' θ‖ + ‖(s:ℂ) * (g.γ' θ - ℓ.γ' θ)‖ := norm_add_le _ _
            _ ≤ B₂ + B₃ := by
                have h5 : ‖(s:ℂ)‖ ≤ 1 := by
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
                  exact hs.2
                have h6 : ‖(s:ℂ) * (g.γ' θ - ℓ.γ' θ)‖ ≤ B₃ := by
                  rw [norm_mul]
                  nlinarith [norm_nonneg (g.γ' θ - ℓ.γ' θ), hB₃ θ hθI]
                have h7 := hB₂ θ hθI
                linarith
        rw [h1]
        have hpos : (0:ℝ) < κ * κ := by positivity
        calc |t - s| * ‖g.γ θ - ℓ.γ θ‖ / (‖(H t).γ θ - a‖ * ‖(H s).γ θ - a‖)
              * ‖(H s).γ' θ‖
            ≤ |t - s| * B₁ / (κ * κ) * (B₂ + B₃) := by
              apply mul_le_mul _ h4 (norm_nonneg _) (by positivity)
              exact div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) hpos h3
          _ = |t - s| * (B₁ * (B₂ + B₃) / (κ * κ)) := by ring
      calc ‖((H t).γ θ - a)⁻¹ * (((t:ℂ) - s) * (g.γ' θ - ℓ.γ' θ))
            + (((s:ℂ) - t) * (g.γ θ - ℓ.γ θ)
              / (((H t).γ θ - a) * ((H s).γ θ - a))) * (H s).γ' θ‖
          ≤ ‖((H t).γ θ - a)⁻¹ * (((t:ℂ) - s) * (g.γ' θ - ℓ.γ' θ))‖
            + ‖(((s:ℂ) - t) * (g.γ θ - ℓ.γ θ)
              / (((H t).γ θ - a) * ((H s).γ θ - a))) * (H s).γ' θ‖ := norm_add_le _ _
        _ ≤ |t - s| * (B₃ / κ) + |t - s| * (B₁ * (B₂ + B₃) / (κ * κ)) := by
            linarith [hterm1, hterm2]
        _ = |t - s| * C := by rw [hCdef]; ring
    have hnorm : ‖windInt (H t) a - windInt (H s) a‖
        ≤ (|t - s| * C) * |2 * Real.pi - 0| := by
      rw [hdiffint]
      exact intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hfinal : ‖windInt (H t) a - windInt (H s) a‖ < 2 * Real.pi := by
      have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
        rw [sub_zero]; exact abs_of_pos (by positivity)
      rw [habs] at hnorm
      have h1 : |t - s| * C * (2 * Real.pi) < ε * (C + 1) * (2 * Real.pi) := by
        have h2 : |t - s| * C ≤ |t - s| * (C + 1) := by nlinarith [abs_nonneg (t - s)]
        have h3 : |t - s| * (C + 1) < ε * (C + 1) := by nlinarith
        nlinarith [Real.pi_pos]
      have h4 : ε * (C + 1) * (2 * Real.pi) = Real.pi := by
        rw [hεdef]; field_simp
      nlinarith [Real.pi_pos]
    exact windInt_eq_of_norm_sub_lt (H t) (H s) hAt hAs hfinal
  -- clopen propagation over [0,1]
  have hW : windInt (H 1) a = windInt (H 0) a := by
    by_contra hcon
    set U : Set ℝ := ⋃ (t₀ : ℝ) (_ : t₀ ∈ Set.Icc (0:ℝ) 1
        ∧ windInt (H t₀) a = windInt (H 0) a), Metric.ball t₀ ε with hUdef
    set V : Set ℝ := ⋃ (t₀ : ℝ) (_ : t₀ ∈ Set.Icc (0:ℝ) 1
        ∧ windInt (H t₀) a ≠ windInt (H 0) a), Metric.ball t₀ ε with hVdef
    have hUo : IsOpen U := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball))
    have hVo : IsOpen V := isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball))
    have hcover : Set.Icc (0:ℝ) 1 ⊆ U ∪ V := by
      intro t ht
      by_cases hw : windInt (H t) a = windInt (H 0) a
      · exact Or.inl (Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨⟨ht, hw⟩,
          Metric.mem_ball_self hεpos⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨⟨ht, hw⟩,
          Metric.mem_ball_self hεpos⟩⟩)
    have hSU : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ U, windInt (H t) a = windInt (H 0) a := by
      rintro t ⟨htI, htU⟩
      obtain ⟨t₀, ht₀⟩ := Set.mem_iUnion.mp htU
      obtain ⟨h₀, hball⟩ := Set.mem_iUnion.mp ht₀
      have hd : |t - t₀| < ε := by
        rw [← Real.dist_eq]; exact Metric.mem_ball.mp hball
      rw [hloc t htI t₀ h₀.1 hd]
      exact h₀.2
    have hSV : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ V, windInt (H t) a ≠ windInt (H 0) a := by
      rintro t ⟨htI, htV⟩
      obtain ⟨t₀, ht₀⟩ := Set.mem_iUnion.mp htV
      obtain ⟨h₀, hball⟩ := Set.mem_iUnion.mp ht₀
      have hd : |t - t₀| < ε := by
        rw [← Real.dist_eq]; exact Metric.mem_ball.mp hball
      rw [hloc t htI t₀ h₀.1 hd]
      exact h₀.2
    have hI01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    have hI11 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
    have hneU : (Set.Icc (0:ℝ) 1 ∩ U).Nonempty :=
      ⟨0, hI01, Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨⟨hI01, rfl⟩,
        Metric.mem_ball_self hεpos⟩⟩⟩
    have hneV : (Set.Icc (0:ℝ) 1 ∩ V).Nonempty :=
      ⟨1, hI11, Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨⟨hI11, hcon⟩,
        Metric.mem_ball_self hεpos⟩⟩⟩
    obtain ⟨w, hwS, hwU, hwV⟩ := isPreconnected_Icc U V hUo hVo hcover hneU hneV
    exact hSV w ⟨hwS, hwV⟩ (hSU w ⟨hwS, hwU⟩)
  -- identify the endpoints
  have hg : windInt (H 1) a = windInt g a := by
    apply intervalIntegral.integral_congr
    intro θ _
    have h1 : (H 1).γ θ = g.γ θ := by
      show ℓ.γ θ + ((1:ℝ):ℂ) * (g.γ θ - ℓ.γ θ) = g.γ θ
      push_cast; ring
    have h2 : (H 1).γ' θ = g.γ' θ := by
      show ℓ.γ' θ + ((1:ℝ):ℂ) * (g.γ' θ - ℓ.γ' θ) = g.γ' θ
      push_cast; ring
    show ((H 1).γ θ - a)⁻¹ * (H 1).γ' θ = (g.γ θ - a)⁻¹ * g.γ' θ
    rw [h1, h2]
  have hℓ : windInt (H 0) a = windInt ℓ a := by
    apply intervalIntegral.integral_congr
    intro θ _
    have h1 : (H 0).γ θ = ℓ.γ θ := by
      show ℓ.γ θ + ((0:ℝ):ℂ) * (g.γ θ - ℓ.γ θ) = ℓ.γ θ
      push_cast; ring
    have h2 : (H 0).γ' θ = ℓ.γ' θ := by
      show ℓ.γ' θ + ((0:ℝ):ℂ) * (g.γ' θ - ℓ.γ' θ) = ℓ.γ' θ
      push_cast; ring
    show ((H 0).γ θ - a)⁻¹ * (H 0).γ' θ = (ℓ.γ θ - a)⁻¹ * ℓ.γ' θ
    rw [h1, h2]
  rw [← hg, ← hℓ]
  exact hW

end Bottcher

namespace Bottcher

/-- **The connector certificate.**  The winding vanishes at every point of a preconnected
avoided set that reaches arbitrarily far out: transport the value along the set to a point
beyond the loop's size, where it dies by the integral estimate.  This is the localization
instrument for lobe loops: a point in a co-branch connects to the far field through scaffold
pieces disjoint from the loop, so the loop does not wind around it. -/
theorem windInt_eq_zero_of_unbounded_connector (ℓ : C1Loop) {S : Set ℂ}
    (hS : IsPreconnected S) (hSA : ∀ z ∈ S, ℓ.Avoids z)
    (hSunb : ∀ R : ℝ, ∃ z ∈ S, R < ‖z‖)
    {p : ℂ} (hp : p ∈ S) : windInt ℓ p = 0 := by
  obtain ⟨Mv, hMv0, hMv⟩ := ℓ.exists_velocity_bound
  obtain ⟨Mγ, hMγ0, hMγ⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), ‖ℓ.γ θ‖ ≤ M := by
    obtain ⟨θ₀, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (Set.nonempty_Icc.mpr (by positivity)) (ℓ.cont.norm.continuousOn
        (s := Set.Icc (0:ℝ) (2 * Real.pi)))
    exact ⟨‖ℓ.γ θ₀‖, norm_nonneg _, fun θ hθ => hmax hθ⟩
  obtain ⟨q, hqS, hqfar⟩ := hSunb (Mγ + Mv + 1)
  have hqwind : windInt ℓ q = 0 := by
    apply windInt_eq_zero_of_norm_lt ℓ (hSA q hqS)
    have hbound : ∀ θ ∈ Set.uIoc (0:ℝ) (2 * Real.pi),
        ‖(ℓ.γ θ - q)⁻¹ * ℓ.γ' θ‖ ≤ Mv / (Mv + 1) := by
      intro θ hθ
      have hθI : θ ∈ Set.Icc (0:ℝ) (2 * Real.pi) := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)] at hθ
        exact ⟨le_of_lt hθ.1, hθ.2⟩
      have hlow : Mv + 1 ≤ ‖ℓ.γ θ - q‖ := by
        have h1 : ‖q‖ - ‖ℓ.γ θ‖ ≤ ‖ℓ.γ θ - q‖ := by
          have := norm_sub_norm_le q (ℓ.γ θ)
          rw [show ‖q - ℓ.γ θ‖ = ‖ℓ.γ θ - q‖ from norm_sub_rev q (ℓ.γ θ)] at this
          linarith
        have h3 : ‖ℓ.γ θ‖ ≤ Mγ := hMγ θ hθI
        linarith
      rw [norm_mul, norm_inv]
      have hnz : (0:ℝ) < ‖ℓ.γ θ - q‖ := by linarith
      calc ‖ℓ.γ θ - q‖⁻¹ * ‖ℓ.γ' θ‖
          ≤ (Mv + 1)⁻¹ * Mv := by
            apply mul_le_mul (inv_anti₀ (by linarith) hlow) (hMv θ hθI)
              (norm_nonneg _) (by positivity)
        _ = Mv / (Mv + 1) := by field_simp
    have hnorm : ‖windInt ℓ q‖ ≤ (Mv / (Mv + 1)) * |2 * Real.pi - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have habs : |2 * Real.pi - 0| = 2 * Real.pi := by
      rw [sub_zero]
      exact abs_of_pos (by positivity)
    rw [habs] at hnorm
    have hfrac : Mv / (Mv + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    calc ‖windInt ℓ q‖ ≤ (Mv / (Mv + 1)) * (2 * Real.pi) := hnorm
      _ < 1 * (2 * Real.pi) := by
          apply mul_lt_mul_of_pos_right hfrac (by positivity)
      _ = 2 * Real.pi := one_mul _
  rw [windInt_eq_on_preconnected ℓ hS hSA hp hqS, hqwind]

end Bottcher
