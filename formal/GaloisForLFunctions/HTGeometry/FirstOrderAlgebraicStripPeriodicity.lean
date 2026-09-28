import GaloisForLFunctions.HTGeometry.FirstOrderRelationLocalUniqueness
import GaloisForLFunctions.HTGeometry.ImStripTranslateCompactness
import GaloisForLFunctions.HTGeometry.BohrMeanInvariance
import GaloisForLFunctions.HTGeometry.BohrParseval
import GaloisForLFunctions.HTGeometry.BohrUniqueness

/-!
# A first-order algebraic almost-periodic strip function is periodic

Let `f` be holomorphic on the strip `|Im z| < η`, with relatively compact real translates on every
closed smaller strip, nonconstant, and satisfying an implicit first-order algebraic differential
equation `P(f, f') = 0`, `P ∈ ℂ[X][Y]` nonzero.  Then `f` has a nonzero real period, its Bohr
frequency group is infinite cyclic `λℤ`, `2π/|λ|` is a period, and the frequency rank is one.

The proof uses neither the normalization of the algebraic curve nor any classification of minimal
sets of surface flows.

1. A relation `Q` of least degree in `Y` has `∂_Y Q (f, f') ≢ 0`, so there is a real point `x₀`
   with `f'(x₀) ≠ 0` and `∂_Y Q (f(x₀), f'(x₀)) ≠ 0`.
2. For an `ε`-almost period `τ`, the open mapping theorem gives a small complex `c` with
   `f(x₀ + c) = f(x₀ + τ)`; local uniqueness for `Q(u, u') = 0` then makes the two translates
   `f(· + τ)` and `f(· + c)` equal on the whole strip.
3. If `c` is real, `τ - c` is a real period.  Otherwise, since `|Im c|` can be made arbitrarily
   small, the relation transports the values of `f` on the real line to a dense set of heights, so
   `|f|` never exceeds its supremum on the line; the maximum principle for translates makes `f`
   constant, contradicting `f'(x₀) ≠ 0`.
4. A real period confines the Bohr spectrum to a cyclic group; the uniqueness theorem for Bohr
   coefficients gives the period `2π/|λ|` of the generator.
-/

open Filter Topology Metric Set Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

variable {f : ℂ → ℂ} {η : ℝ}

/-! ## Step 1: a relation of least degree and a real anchor point -/

theorem exists_deriv_ne_zero_of_imStrip (hf : DifferentiableOn ℂ f (imStrip η))
    (hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂) :
    ∃ z ∈ imStrip η, deriv f z ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨z₁, h₁, z₂, h₂, hne⟩ := hnc
  exact hne ((isOpen_imStrip η).is_const_of_deriv_eq_zero (isPreconnected_imStrip η) hf
    (fun z hz => hall z hz) h₁ h₂)

/-- **A relation of least degree in `Y`.**  Its `Y`-derivative is not a relation. -/
theorem exists_relation_derivative_ne_zero (hf : DifferentiableOn ℂ f (imStrip η))
    (hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z ∈ imStrip η, relEval P (f z) (deriv f z) = 0) :
    ∃ Q : Polynomial (Polynomial ℂ), (∀ z ∈ imStrip η, relEval Q (f z) (deriv f z) = 0) ∧
      ∃ z ∈ imStrip η, relEval (derivative Q) (f z) (deriv f z) ≠ 0 := by
  classical
  have hex : ∃ d : ℕ, ∃ Q : Polynomial (Polynomial ℂ), Q ≠ 0 ∧
      (∀ z ∈ imStrip η, relEval Q (f z) (deriv f z) = 0) ∧ Q.natDegree = d :=
    ⟨_, P, hP, hrel, rfl⟩
  obtain ⟨Q, hQ0, hQrel, hQd⟩ := Nat.find_spec hex
  refine ⟨Q, hQrel, ?_⟩
  by_contra hall
  push Not at hall
  by_cases hd : Q.natDegree = 0
  · have hQC := eq_C_of_natDegree_eq_zero hd
    set q := Q.coeff 0 with hq
    have hq0 : q ≠ 0 := by
      intro h; apply hQ0; rw [hQC, h, map_zero]
    have hroot : ∀ z ∈ imStrip η, q.eval (f z) = 0 := by
      intro z hz
      have h1 := hQrel z hz
      rwa [hQC, relEval, Polynomial.map_C, eval_C, coe_evalRingHom] at h1
    obtain ⟨z₁, hz₁, hd₁⟩ := exists_deriv_ne_zero_of_imStrip hf hnc
    have hana : AnalyticAt ℂ f z₁ := (hf.analyticOnNhd (isOpen_imStrip η)) z₁ hz₁
    rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
    · apply hd₁
      have h1 : deriv f z₁ = deriv (fun _ => f z₁) z₁ := Filter.EventuallyEq.deriv_eq hconst
      simpa using h1
    · have hmem : {w : ℂ | q.eval w = 0} ∈ 𝓝 (f z₁) := hopen (by
        rw [Filter.mem_map]
        filter_upwards [(isOpen_imStrip η).mem_nhds hz₁] with z hz using hroot z hz)
      have hfin : {w : ℂ | q.eval w = 0}.Finite := by
        refine (q.roots.toFinset.finite_toSet).subset fun w hw => ?_
        simp only [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hq0, IsRoot.def]
        exact hw
      exact infinite_of_mem_nhds (f z₁) hmem hfin
  · have hder0 : derivative Q ≠ 0 := fun h => hd (derivative_eq_zero.mp h)
    have hlt : (derivative Q).natDegree < Nat.find hex := hQd ▸ natDegree_derivative_lt hd
    exact Nat.find_min hex hlt ⟨derivative Q, hder0, hall, rfl⟩

/-- Along a sequence of nonzero reals tending to zero, a property holding on the real line holds
frequently in the punctured neighbourhood of `0`. -/
theorem frequently_nhdsNE_zero_of_forall_real {p : ℂ → Prop} (h : ∀ x : ℝ, p x) :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ), p z := by
  have hu : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      simpa only [Complex.ofReal_zero] using this
    · simp only [mem_compl_iff, mem_singleton_iff, ofReal_eq_zero]
      positivity
  exact hu.frequently (Frequently.of_forall fun n => h _)

/-- An analytic function on the strip vanishing on the real line vanishes on the strip. -/
theorem eqOn_zero_of_forall_real {g : ℂ → ℂ} (hη : 0 < η)
    (hg : AnalyticOnNhd ℂ g (imStrip η)) (h : ∀ x : ℝ, g x = 0) : EqOn g 0 (imStrip η) :=
  hg.eqOn_zero_of_preconnected_of_frequently_eq_zero (isPreconnected_imStrip η)
    (by simpa [mem_imStrip] using hη) (frequently_nhdsNE_zero_of_forall_real h)

/-- **The real anchor point.** -/
theorem exists_real_anchor (hη : 0 < η) (hf : DifferentiableOn ℂ f (imStrip η))
    {Q : Polynomial (Polynomial ℂ)}
    (hQ : ∃ z ∈ imStrip η, relEval (derivative Q) (f z) (deriv f z) ≠ 0)
    (hd : ∃ z ∈ imStrip η, deriv f z ≠ 0) :
    ∃ x₀ : ℝ, deriv f x₀ ≠ 0 ∧ relEval (derivative Q) (f x₀) (deriv f x₀) ≠ 0 := by
  have hA : AnalyticOnNhd ℂ (deriv f) (imStrip η) :=
    (hf.deriv (isOpen_imStrip η)).analyticOnNhd (isOpen_imStrip η)
  have hF : AnalyticOnNhd ℂ f (imStrip η) := hf.analyticOnNhd (isOpen_imStrip η)
  have hB : AnalyticOnNhd ℂ (fun z => relEval (derivative Q) (f z) (deriv f z)) (imStrip η) :=
    fun z hz => analyticAt_relEval _ (hF z hz) (hA z hz)
  have hg : AnalyticOnNhd ℂ (fun z => deriv f z * relEval (derivative Q) (f z) (deriv f z))
      (imStrip η) := fun z hz => (hA z hz).mul (hB z hz)
  by_contra hall
  push Not at hall
  have hzero := eqOn_zero_of_forall_real hη hg fun x => by
    by_cases h1 : deriv f x = 0
    · simp [h1]
    · simp [hall x h1]
  obtain ⟨z₁, hz₁, hd₁⟩ := hd
  obtain ⟨z₂, hz₂, hQ₂⟩ := hQ
  have hnear : ∀ᶠ z in 𝓝 z₁, deriv f z ≠ 0 :=
    ((hA z₁ hz₁).continuousAt).eventually_ne hd₁
  have hBzero : ∀ᶠ z in 𝓝 z₁, relEval (derivative Q) (f z) (deriv f z) = 0 := by
    filter_upwards [hnear, (isOpen_imStrip η).mem_nhds hz₁] with z hz hzS
    have := hzero hzS
    simp only [Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left hz
  exact hQ₂ (hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_imStrip η) hz₁
    hBzero hz₂)

/-! ## Step 2: almost periods become exact complex translations -/

/-- **Translation pairs.**  For every `ρ > 0` there are a real `τ ≥ 1` and a complex `c` with
`‖c‖ < ρ` and `‖c‖ < η/8` such that `f(z + τ) = f(z + c)` on the strip `|Im z| < η/2`. -/
theorem exists_translation_pair (hη : 0 < η) (hf : DifferentiableOn ℂ f (imStrip η))
    (hap : IsImStripUniformlyAlmostPeriodic f η) {Q : Polynomial (Polynomial ℂ)}
    (hrel : ∀ z ∈ imStrip η, relEval Q (f z) (deriv f z) = 0) {x₀ : ℝ}
    (hd : deriv f x₀ ≠ 0) (hQ : relEval (derivative Q) (f x₀) (deriv f x₀) ≠ 0) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ τ : ℝ, 1 ≤ τ ∧ ∃ c : ℂ, ‖c‖ < ρ ∧ ‖c‖ < η / 8 ∧
      ∀ z ∈ imStrip (η / 2), f (z + τ) = f (z + c) := by
  obtain ⟨δ, hδ, huniq⟩ := eqOn_of_relEval_eq_zero hQ
  have hx₀ : (x₀ : ℂ) ∈ imStrip η := by simpa [mem_imStrip] using hη
  have hA : AnalyticOnNhd ℂ (deriv f) (imStrip η) :=
    (hf.deriv (isOpen_imStrip η)).analyticOnNhd (isOpen_imStrip η)
  -- continuity of the derivative at `x₀`
  obtain ⟨r', hr', hr'd⟩ : ∃ r' > 0, ∀ c : ℂ, ‖c‖ < r' → ‖deriv f (x₀ + c) - deriv f x₀‖ < δ := by
    have hc := (hA x₀ hx₀).continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨r', hr', h⟩ := hc δ hδ
    exact ⟨r', hr', fun c hc => by
      have := h (x := x₀ + c) (by simpa [dist_eq_norm] using hc)
      rwa [dist_eq_norm] at this⟩
  set ρ' := min ρ (min (η / 8) r') with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min (by linarith) hr')
  -- open mapping at `x₀`
  obtain ⟨δc, hδc, hopen⟩ : ∃ δc > 0, ∀ w : ℂ, ‖w - f x₀‖ < δc →
      ∃ c : ℂ, ‖c‖ < ρ' ∧ f (x₀ + c) = w := by
    have hana : AnalyticAt ℂ f x₀ := (hf.analyticOnNhd (isOpen_imStrip η)) x₀ hx₀
    rcases hana.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
    · exfalso
      apply hd
      have h1 : deriv f (x₀ : ℂ) = deriv (fun _ : ℂ => f x₀) (x₀ : ℂ) :=
        Filter.EventuallyEq.deriv_eq hconst
      simpa using h1
    · have hmem : f '' ball (x₀ : ℂ) ρ' ∈ 𝓝 (f x₀) := hmap (image_mem_map (ball_mem_nhds _ hρ'pos))
      obtain ⟨δc, hδc, hsub⟩ := Metric.mem_nhds_iff.mp hmem
      refine ⟨δc, hδc, fun w hw => ?_⟩
      obtain ⟨y, hy, hyw⟩ := hsub (by rwa [mem_ball, dist_eq_norm])
      refine ⟨y - x₀, ?_, by simpa using hyw⟩
      rwa [mem_ball, dist_eq_norm] at hy
  -- the almost period
  set R : ℝ := η / 4 with hR
  have hRpos : 0 < R := by positivity
  set ε := min (δc / 2) (min (δ / 2) (δ * R / 2)) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (lt_min (by linarith) (by positivity))
  obtain ⟨L, hL, hdense⟩ := (hap (η / 2) (by linarith)).exists_almostPeriod hεpos
  obtain ⟨τ, hτ, hτap⟩ := hdense 1
  refine ⟨τ, hτ.1, ?_⟩
  have hτval : ‖f (x₀ + τ) - f x₀‖ ≤ ε := hτap x₀ (by simp; positivity)
  obtain ⟨c, hc, hcval⟩ := hopen (f (x₀ + τ)) (by
    have : ε < δc := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    linarith)
  have hcρ : ‖c‖ < ρ := lt_of_lt_of_le hc (min_le_left _ _)
  have hcη : ‖c‖ < η / 8 := lt_of_lt_of_le hc ((min_le_right _ _).trans (min_le_left _ _))
  have hcr' : ‖c‖ < r' := lt_of_lt_of_le hc ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcρ, hcη, ?_⟩
  -- Cauchy's estimate for the derivative of the almost period
  have hball : closedBall (x₀ : ℂ) R ⊆ closedImStrip (η / 2) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 : |w.im| ≤ R := by
      have := Complex.abs_im_le_norm (w - x₀)
      simp only [sub_im, ofReal_im, sub_zero] at this
      linarith
    exact mem_closedImStrip.mpr (by linarith)
  have hderivτ : ‖deriv f (x₀ + τ) - deriv f x₀‖ ≤ ε / R := by
    set h : ℂ → ℂ := fun w => f (w + τ) - f w with hh
    have hhd : DifferentiableOn ℂ h (closedBall (x₀ : ℂ) R) := by
      intro w hw
      have hwS : w ∈ imStrip η := closedImStrip_subset_imStrip (by linarith) (hball hw)
      have hwτ : w + τ ∈ imStrip η := add_ofReal_mem_imStrip hwS τ
      exact (((hf.differentiableAt ((isOpen_imStrip η).mem_nhds hwτ)).comp w
        (differentiableAt_id.add_const _)).sub
        (hf.differentiableAt ((isOpen_imStrip η).mem_nhds hwS))).differentiableWithinAt
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos
      (hhd.diffContOnCl_ball (subset_refl _)) (C := ε)
      (fun w hw => hτap w (hball (sphere_subset_closedBall hw)))
    have hx₀S : (x₀ : ℂ) ∈ imStrip η := hx₀
    have hx₀τ : (x₀ : ℂ) + τ ∈ imStrip η := add_ofReal_mem_imStrip hx₀S τ
    have hd1 : DifferentiableAt ℂ (fun w => f (w + τ)) (x₀ : ℂ) :=
      (hf.differentiableAt ((isOpen_imStrip η).mem_nhds hx₀τ)).comp (x₀ : ℂ)
        (differentiableAt_id.add_const (τ : ℂ))
    have hd2 : DifferentiableAt ℂ f (x₀ : ℂ) := hf.differentiableAt ((isOpen_imStrip η).mem_nhds hx₀S)
    have hdh : deriv h x₀ = deriv f (x₀ + τ) - deriv f x₀ := by
      rw [hh, deriv_fun_sub hd1 hd2, deriv_comp_add_const]
    rwa [hdh] at hcauchy
  -- local uniqueness applied to the two translates
  have hU : IsOpen (imStrip (η / 2)) := isOpen_imStrip _
  have hx₀U : (x₀ : ℂ) ∈ imStrip (η / 2) := by simpa [mem_imStrip] using (by linarith : 0 < η / 2)
  have hcim : |c.im| < η / 8 := lt_of_le_of_lt (Complex.abs_im_le_norm c) hcη
  have hmemτ : ∀ z ∈ imStrip (η / 2), z + τ ∈ imStrip η := fun z hz =>
    imStrip_mono (by linarith) (add_ofReal_mem_imStrip hz τ)
  have hmemc : ∀ z ∈ imStrip (η / 2), z + c ∈ imStrip η := by
    intro z hz
    rw [mem_imStrip] at hz ⊢
    rw [add_im]
    calc |z.im + c.im| ≤ |z.im| + |c.im| := abs_add_le _ _
      _ < η := by linarith
  have hvd : DifferentiableOn ℂ (fun z => f (z + τ)) (imStrip (η / 2)) := fun z hz =>
    ((hf.differentiableAt ((isOpen_imStrip η).mem_nhds (hmemτ z hz))).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hwd : DifferentiableOn ℂ (fun z => f (z + c)) (imStrip (η / 2)) := fun z hz =>
    ((hf.differentiableAt ((isOpen_imStrip η).mem_nhds (hmemc z hz))).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  refine huniq hU (isPreconnected_imStrip _) hx₀U hvd hwd ?_ ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [deriv_comp_add_const]
    exact hrel _ (hmemτ z hz)
  · intro z hz
    rw [deriv_comp_add_const]
    exact hrel _ (hmemc z hz)
  · exact hcval.symm
  · have : ε < δ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by linarith)
    linarith
  · rw [deriv_comp_add_const]
    have h1 : ε / R ≤ δ / 2 := by
      rw [div_le_iff₀ hRpos]
      have := (min_le_right _ _).trans (min_le_right (δ / 2) (δ * R / 2))
      linarith
    linarith
  · rw [deriv_comp_add_const]
    exact hr'd c hcr'

/-! ## Step 3: a real translation pair is a real period -/

theorem exists_period_of_real_translation_pair (hη : 0 < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) {τ : ℝ} {c : ℂ} (hcim : c.im = 0) (hcτ : ‖c‖ < τ)
    (hpair : ∀ z ∈ imStrip (η / 2), f (z + τ) = f (z + c)) :
    ∃ p : ℝ, p ≠ 0 ∧ ∀ z ∈ imStrip η, f (z + p) = f z := by
  have hc : c = (c.re : ℂ) := by
    apply Complex.ext <;> simp [hcim]
  refine ⟨τ - c.re, ?_, ?_⟩
  · have := Complex.abs_re_le_norm c
    have := le_abs_self c.re
    intro h
    linarith
  have hF : AnalyticOnNhd ℂ f (imStrip η) := hf.analyticOnNhd (isOpen_imStrip η)
  have hshift : AnalyticOnNhd ℂ (fun z => f (z + ((τ - c.re : ℝ) : ℂ))) (imStrip η) :=
    fun z hz => (hF _ (add_ofReal_mem_imStrip hz _)).comp (analyticAt_id.add analyticAt_const)
  have h0 : (0 : ℂ) ∈ imStrip η := by simpa [mem_imStrip] using hη
  have heq : (fun z => f (z + ((τ - c.re : ℝ) : ℂ))) =ᶠ[𝓝 0] f := by
    filter_upwards [(isOpen_imStrip (η / 2)).mem_nhds (by simpa [mem_imStrip] using
      (by linarith : 0 < η / 2))] with z hz
    have hz' : z - (c.re : ℂ) ∈ imStrip (η / 2) := by simpa [mem_imStrip] using hz
    have h1 := hpair _ hz'
    rw [← hc] at h1
    have e1 : z - (c.re : ℂ) + (τ : ℂ) = z + ((τ - c.re : ℝ) : ℂ) := by push_cast; ring
    have e2 : z - (c.re : ℂ) + c = z := by rw [hc]; ring
    rw [e1, e2] at h1
    exact h1
  intro z hz
  exact hshift.eqOn_of_preconnected_of_eventuallyEq hF (isPreconnected_imStrip η) h0 heq hz

/-! ## Step 4: nonreal translation pairs transport the real line to dense heights -/

/-- Climbing and descending the heights `k · Im c` with one translation pair. -/
theorem exists_real_eq_of_translation_pair {τ : ℝ} {c : ℂ}
    (hpair : ∀ z ∈ imStrip (η / 2), f (z + τ) = f (z + c)) (k : ℤ)
    (hk : |(k : ℝ) * c.im| < η / 2) (x : ℝ) :
    ∃ x' : ℝ, f (x + ((k * c.im : ℝ) : ℂ) * I) = f x' := by
  have hup : ∀ n : ℕ, (n : ℝ) * |c.im| < η / 2 → ∀ x : ℝ,
      ∃ x' : ℝ, f (x + (((n : ℝ) * c.im : ℝ) : ℂ) * I) = f x' := by
    intro n
    induction n with
    | zero => intro _ x; exact ⟨x, by simp⟩
    | succ n ih =>
      intro hn x
      have hn' : (n : ℝ) * |c.im| < η / 2 := by
        have : (n : ℝ) * |c.im| ≤ ((n + 1 : ℕ) : ℝ) * |c.im| := by
          push_cast; nlinarith [abs_nonneg c.im]
        linarith
      set z : ℂ := ((x - c.re : ℝ) : ℂ) + (((n : ℝ) * c.im : ℝ) : ℂ) * I with hz
      have hzS : z ∈ imStrip (η / 2) := by
        rw [mem_imStrip]
        simp only [hz, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add,
          mul_one]
        rw [abs_mul, Nat.abs_cast]; exact hn'
      have h1 := hpair z hzS
      have e1 : z + c = x + ((((n + 1 : ℕ) : ℝ) * c.im : ℝ) : ℂ) * I := by
        rw [hz]
        conv_lhs => rw [← Complex.re_add_im c]
        push_cast; ring
      have e2 : z + τ = ((x - c.re + τ : ℝ) : ℂ) + (((n : ℝ) * c.im : ℝ) : ℂ) * I := by
        rw [hz]; push_cast; ring
      rw [e1, e2] at h1
      obtain ⟨x', hx'⟩ := ih hn' (x - c.re + τ)
      exact ⟨x', h1.symm.trans hx'⟩
  have hdown : ∀ n : ℕ, (n : ℝ) * |c.im| < η / 2 → ∀ x : ℝ,
      ∃ x' : ℝ, f (x + ((-((n : ℝ) * c.im) : ℝ) : ℂ) * I) = f x' := by
    intro n
    induction n with
    | zero => intro _ x; exact ⟨x, by simp⟩
    | succ n ih =>
      intro hn x
      have hn' : (n : ℝ) * |c.im| < η / 2 := by
        have : (n : ℝ) * |c.im| ≤ ((n + 1 : ℕ) : ℝ) * |c.im| := by
          push_cast; nlinarith [abs_nonneg c.im]
        linarith
      set z : ℂ := ((x - τ : ℝ) : ℂ) + ((-(((n + 1 : ℕ) : ℝ) * c.im) : ℝ) : ℂ) * I with hz
      have hzS : z ∈ imStrip (η / 2) := by
        rw [mem_imStrip]
        simp only [hz, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, zero_add,
          mul_one]
        rw [abs_neg, abs_mul, Nat.abs_cast]; exact hn
      have h1 := hpair z hzS
      have e1 : z + τ = x + ((-(((n + 1 : ℕ) : ℝ) * c.im) : ℝ) : ℂ) * I := by
        rw [hz]; push_cast; ring
      have e2 : z + c = ((x - τ + c.re : ℝ) : ℂ) + ((-((n : ℝ) * c.im)) : ℝ) * I := by
        rw [hz]
        conv_lhs => rw [← Complex.re_add_im c]
        push_cast; ring
      rw [e1, e2] at h1
      obtain ⟨x', hx'⟩ := ih hn' (x - τ + c.re)
      exact ⟨x', h1.trans hx'⟩
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · have hn : (n : ℝ) * |c.im| < η / 2 := by
      rw [abs_mul, Int.cast_natCast, Nat.abs_cast] at hk; exact hk
    simpa using hup n hn x
  · have hn : (n : ℝ) * |c.im| < η / 2 := by
      rw [abs_mul, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] at hk; exact hk
    obtain ⟨x', hx'⟩ := hdown n hn x
    exact ⟨x', by simpa [neg_mul] using hx'⟩

/-- **Nonreal translation pairs of vanishing height bound `|f|` by its supremum on the line.** -/
theorem norm_le_iSup_of_translation_pairs (hη : 0 < η) (hf : DifferentiableOn ℂ f (imStrip η))
    (hap : IsImStripUniformlyAlmostPeriodic f η)
    (hpairs : ∀ n : ℕ, ∃ τ : ℝ, ∃ c : ℂ, c.im ≠ 0 ∧ ‖c‖ < 1 / ((n : ℝ) + 1) ∧ ‖c‖ < η / 8 ∧
      ∀ z ∈ imStrip (η / 2), f (z + τ) = f (z + c)) :
    BddAbove (range fun x : ℝ => ‖f x‖) ∧
      ∀ z : ℂ, |z.im| ≤ η / 4 → ‖f z‖ ≤ ⨆ x : ℝ, ‖f x‖ := by
  have hc : ContinuousOn f (closedImStrip (η / 2)) :=
    hf.continuousOn.mono (closedImStrip_subset_imStrip (by linarith))
  obtain ⟨B, hB⟩ := (hap (η / 2) (by linarith)).exists_bound hc
  have hbdd : BddAbove (range fun x : ℝ => ‖f x‖) :=
    ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x (by simp; positivity)⟩
  refine ⟨hbdd, fun z hz => ?_⟩
  set M₀ := ⨆ x : ℝ, ‖f x‖
  set C := 2 * B / (η / 2 - 3 * η / 8) with hC
  have hlip := exists_lipschitz_closedImStrip (f := f) (η := η) (r := 3 * η / 8) (r' := η / 2)
    (by linarith) (by linarith) hf hB
  have hstep : ∀ n : ℕ, ‖f z‖ ≤ M₀ + C * (1 / ((n : ℝ) + 1)) := by
    intro n
    obtain ⟨τ, c, hcim, hcn, hcη, hpair⟩ := hpairs n
    set β := c.im with hβ
    have hβpos : 0 < |β| := abs_pos.mpr hcim
    have hβn : |β| < 1 / ((n : ℝ) + 1) := lt_of_le_of_lt (Complex.abs_im_le_norm c) hcn
    have hβη : |β| < η / 8 := lt_of_le_of_lt (Complex.abs_im_le_norm c) hcη
    set k : ℤ := round (z.im / β) with hk
    have hround : |z.im - k * β| ≤ |β| / 2 := by
      have h1 := abs_sub_round (z.im / β)
      have e : z.im - k * β = β * (z.im / β - k) := by field_simp
      rw [e, abs_mul]
      calc |β| * |z.im / β - k| ≤ |β| * (1 / 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |β| / 2 := by ring
    have hkβ : |(k : ℝ) * β| < η / 2 := by
      have := abs_sub_abs_le_abs_sub (k * β) z.im
      rw [abs_sub_comm] at hround
      have hzim : |z.im| ≤ η / 4 := hz
      linarith
    obtain ⟨x', hx'⟩ := exists_real_eq_of_translation_pair hpair k hkβ z.re
    set w : ℂ := (z.re : ℂ) + ((k * β : ℝ) : ℂ) * I with hw
    have hwim : w.im = k * β := by simp [hw]
    have hfw : ‖f w‖ ≤ M₀ := by
      rw [hw, hx']
      exact le_ciSup hbdd x'
    have hzw : ‖z - w‖ = |z.im - k * β| := by
      have e : z - w = ((z.im - k * β : ℝ) : ℂ) * I := by
        rw [hw]
        conv_lhs => rw [← Complex.re_add_im z]
        push_cast; ring
      rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hlipzw := hlip w z (by rw [hwim]; linarith [abs_nonneg ((k : ℝ) * β)])
      (by linarith)
    calc ‖f z‖ ≤ ‖f w‖ + ‖f z - f w‖ := norm_le_insert' _ _
      _ ≤ M₀ + C * ‖z - w‖ := by gcongr
      _ ≤ M₀ + C * (1 / ((n : ℝ) + 1)) := by
          have hC0 : 0 ≤ C := by
            rw [hC]
            have : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp; positivity))
            positivity
          rw [hzw]
          gcongr
          linarith
  have hlim : Tendsto (fun n : ℕ => M₀ + C * (1 / ((n : ℝ) + 1))) atTop (𝓝 M₀) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C).const_add M₀
  exact ge_of_tendsto' hlim hstep

/-! ## The periodicity theorem -/

/-- **A first-order algebraic almost-periodic strip function has a nonzero real period.** -/
theorem exists_real_period_of_firstOrderRelation (hη : 0 < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hap : IsImStripUniformlyAlmostPeriodic f η)
    (hnc : ∃ z₁ ∈ imStrip η, ∃ z₂ ∈ imStrip η, f z₁ ≠ f z₂)
    {P : Polynomial (Polynomial ℂ)} (hP : P ≠ 0)
    (hrel : ∀ z ∈ imStrip η, relEval P (f z) (deriv f z) = 0) :
    ∃ p : ℝ, p ≠ 0 ∧ ∀ z ∈ imStrip η, f (z + p) = f z := by
  obtain ⟨Q, hQrel, hQ⟩ := exists_relation_derivative_ne_zero hf hnc hP hrel
  obtain ⟨x₀, hd, hQx₀⟩ :=
    exists_real_anchor hη hf hQ (exists_deriv_ne_zero_of_imStrip hf hnc)
  by_contra hnp
  have hpairs : ∀ n : ℕ, ∃ τ : ℝ, ∃ c : ℂ, c.im ≠ 0 ∧ ‖c‖ < 1 / ((n : ℝ) + 1) ∧ ‖c‖ < η / 8 ∧
      ∀ z ∈ imStrip (η / 2), f (z + τ) = f (z + c) := by
    intro n
    obtain ⟨τ, hτ, c, hc, hcη, hpair⟩ :=
      exists_translation_pair hη hf hap hQrel hd hQx₀ (ρ := min (1 / ((n : ℝ) + 1)) (1 / 2))
        (lt_min (by positivity) (by norm_num))
    refine ⟨τ, c, fun hcim => hnp ?_, lt_of_lt_of_le hc (min_le_left _ _), hcη, hpair⟩
    exact exists_period_of_real_translation_pair hη hf hcim
      (by linarith [lt_of_lt_of_le hc (min_le_right _ _)]) hpair
  obtain ⟨hbdd, hle⟩ := norm_le_iSup_of_translation_pairs hη hf hap hpairs
  obtain ⟨c, hc⟩ := (hap (η / 4) (by linarith)).exists_const_of_norm_le_iSup (by positivity)
    (by linarith) hf hbdd hle
  have hx₀ : (x₀ : ℂ) ∈ imStrip (η / 4) := by simpa [mem_imStrip] using (by positivity : 0 < η / 4)
  apply hd
  have hconst : f =ᶠ[𝓝 (x₀ : ℂ)] fun _ => c := by
    filter_upwards [(isOpen_imStrip (η / 4)).mem_nhds hx₀] with z hz using hc z hz
  rw [hconst.deriv_eq]
  simp

end GaloisForLFunctions.HTGeometry
