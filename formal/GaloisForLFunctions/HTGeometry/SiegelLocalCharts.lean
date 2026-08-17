import GaloisForLFunctions.HTGeometry.SiegelChartAssembly
import GaloisForLFunctions.HTGeometry.PolydiscLocalSchwarz

/-!
# The chartwise Siegel assembly for locally holomorphic charts

The chart data of a Siegel argument for meromorphic functions is a *local* presentation: on the
polydisc around each centre a meromorphic function is a quotient of two holomorphic functions, and
neither of them extends anywhere else.  This module runs the whole chartwise assembly under that
hypothesis: holomorphy of the numerators and denominators on a polydisc strictly larger than the
contour, rather than on the whole space.

Everything downstream of the multi-index Schwarz estimate is already local — the closing mechanism
`eqOn_zero_of_family_siegel_gain` needs continuity only on the small polydiscs, and the chart
comparison `hcomp_of_transition` is purely metric — so only the Taylor-condition map and the gain
have to be rebuilt.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {n m : ℕ} {ι : Type*} [Fintype ι]

/-! ## Cauchy coefficients from continuity on the contour alone -/

/-- **The Cauchy coefficient is additive in the integrand**, needing the integrands only on the
contour. -/
theorem polydiscCoeff_add_of_torusContinuous {d : ℕ} {F G : (Fin d → ℂ) → ℂ} {c : Fin d → ℂ}
    {R : ℝ} (hR : 0 < R)
    (hF : Continuous fun θ : Fin d → ℝ => F (torusMap c (fun _ => R) θ))
    (hG : Continuous fun θ : Fin d → ℝ => G (torusMap c (fun _ => R) θ)) (m : Fin d → ℕ) :
    polydiscCoeff (fun ζ => F ζ + G ζ) c R m
      = polydiscCoeff F c R m + polydiscCoeff G c R m := by
  have hFi := polydiscCoeff_integrable (f := F) (c := c) (R := R) hF hR m
  have hGi := polydiscCoeff_integrable (f := G) (c := c) (R := R) hG hR m
  have hsplit : (fun ζ : Fin d → ℂ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • (F ζ + G ζ))
      = fun ζ : Fin d → ℂ => (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • F ζ
          + (∏ i, (ζ i - c i) ^ (m i + 1))⁻¹ • G ζ := by
    funext ζ
    rw [smul_add]
  rw [polydiscCoeff, polydiscCoeff, polydiscCoeff, hsplit, torusIntegral_add hFi hGi, smul_add]

/-! ## Local continuity and holomorphy of the cleared combination -/

/-- A function holomorphic on a polydisc is continuous on the distinguished boundary of every
smaller polydisc. -/
theorem continuous_torusComp_of_differentiableOn {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ}
    {R R₁ : ℝ} (hR : 0 ≤ R) (hRR₁ : R < R₁)
    (hf : DifferentiableOn ℂ f (polydiscSet c (fun _ => R₁))) :
    Continuous fun θ : Fin n → ℝ => f (torusMap c (fun _ => R) θ) :=
  hf.continuousOn.comp_continuous (continuous_torusMap c _)
    (torusMap_mem_polydiscSet (fun _ => hR) (fun _ => hRR₁))

theorem differentiableOn_finsetSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι' : Type*} (u : Finset ι') {f : ι' → E → ℂ} {s : Set E}
    (h : ∀ i, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun x => ∑ i ∈ u, f i x) s := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro i u hi ih
    simp only [Finset.sum_insert hi]
    exact (h i).add ih

theorem differentiableOn_finsetProd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι' : Type*} (u : Finset ι') {f : ι' → E → ℂ} {s : Set E}
    (h : ∀ i, DifferentiableOn ℂ (f i) s) :
    DifferentiableOn ℂ (fun x => ∏ i ∈ u, f i x) s := by
  classical
  refine Finset.induction_on u ?_ ?_
  · simp
  · intro i u hi ih
    simp only [Finset.prod_insert hi]
    exact (h i).mul ih

/-- The cleared combination of locally holomorphic chart data is locally holomorphic. -/
theorem differentiableOn_siegelHomCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A B : Fin (n + 1) → E → ℂ} {s : Set E}
    (hA : ∀ k, DifferentiableOn ℂ (A k) s) (hB : ∀ k, DifferentiableOn ℂ (B k) s)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    DifferentiableOn ℂ (siegelHomCombination A B m a) s := by
  refine differentiableOn_finsetSum _ fun β => ?_
  refine (differentiableOn_const _).mul ?_
  exact differentiableOn_finsetProd _ fun k => ((hA k).pow _).mul ((hB k).pow _)

/-! ## The chartwise Taylor-condition map, locally -/

/-- The chartwise Taylor-condition map for locally holomorphic chart data. -/
noncomputable def siegelHomCoeffMapLocal (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {R R₁ : ℝ} (hR : 0 < R) (hRR₁ : R < R₁)
    (hA : ∀ i k, DifferentiableOn ℂ (A i k) (polydiscSet (c i) (fun _ => R₁)))
    (hB : ∀ i k, DifferentiableOn ℂ (B i k) (polydiscSet (c i) (fun _ => R₁)))
    (S : Finset (Fin n → ℕ)) :
    ((Fin (n + 1) → Fin (m + 1)) → ℂ) →ₗ[ℂ] ((ι × S) → ℂ) where
  toFun a := fun p =>
    polydiscCoeff (siegelHomCombination (A p.1) (B p.1) m a) (c p.1) R (p.2 : Fin n → ℕ)
  map_add' a b := by
    funext p
    have hcont : ∀ d : (Fin (n + 1) → Fin (m + 1)) → ℂ,
        Continuous fun θ : Fin n → ℝ =>
          siegelHomCombination (A p.1) (B p.1) m d (torusMap (c p.1) (fun _ => R) θ) := by
      intro d
      exact continuous_torusComp_of_differentiableOn (R := R) (le_of_lt hR) hRR₁
        (differentiableOn_siegelHomCombination (hA p.1) (hB p.1) d)
    rw [siegelHomCombination_add]
    have hadd := polydiscCoeff_add_of_torusContinuous (F := siegelHomCombination (A p.1) (B p.1) m a)
      (G := siegelHomCombination (A p.1) (B p.1) m b) hR (hcont a) (hcont b) (p.2 : Fin n → ℕ)
    rw [hadd]
    rfl
  map_smul' t a := by
    funext p
    rw [siegelHomCombination_smul, polydiscCoeff_const_smul]
    rfl

/-! ## The chartwise gain and the chartwise vanishing -/

/-- **The chartwise Siegel gain for locally holomorphic chart data.** -/
theorem exists_ne_zero_chart_siegel_gain_local {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {R R₁ r : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) (hr : 0 ≤ r) (hrR : r < R)
    (hA : ∀ i k, DifferentiableOn ℂ (A i k) (polydiscSet (c i) (fun _ => R₁)))
    (hB : ∀ i k, DifferentiableOn ℂ (B i k) (polydiscSet (c i) (fun _ => R₁)))
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ M : ℝ, (∀ (i : ι) (t : Fin n → ℝ),
          ‖siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)‖ ≤ M) →
        ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelHomCombination (A i) (B i) m a (c i + y)‖
            ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
              ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := by
  classical
  obtain ⟨a, ha, hT⟩ :=
    exists_ne_zero_of_siegel_count (n := n) (m := m) (N := N) (lowDegreeIndices n N)
      (fun β hβ => mem_lowDegreeIndices.mp hβ)
      (siegelHomCoeffMapLocal (m := m) A B c hR hRR₁ hA hB (lowDegreeIndices n N)) hcount
  refine ⟨a, ha, ?_⟩
  intro M hM i y hy
  refine norm_le_of_polydiscCoeff_vanish_of_differentiableOn hR hRR₁
    (differentiableOn_siegelHomCombination (hA i) (hB i) a) hr hrR (hM i) ?_ hy
  intro β hβ
  have := congrFun hT (i, ⟨β, mem_lowDegreeIndices.mpr hβ⟩)
  simpa [siegelHomCoeffMapLocal] using this

/-- **The chartwise assembly for locally holomorphic chart data.** -/
theorem exists_ne_zero_chart_vanishing_local [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {R R₁ r C : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) (hr : 0 ≤ r) (hrR : r < R)
    (hA : ∀ i k, DifferentiableOn ℂ (A i k) (polydiscSet (c i) (fun _ => R₁)))
    (hB : ∀ i k, DifferentiableOn ℂ (B i k) (polydiscSet (c i) (fun _ => R₁)))
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (hcomp : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (M : ℝ),
      (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelHomCombination (A i) (B i) m a (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ),
        ‖siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)‖ ≤ C * M)
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        siegelHomCombination (A i) (B i) m a (c i + y) = 0 := by
  obtain ⟨a, ha, hgain⟩ :=
    exists_ne_zero_chart_siegel_gain_local (N := N) A B c hR hRR₁ hr hrR hA hB hcount
  refine ⟨a, ha, ?_⟩
  refine eqOn_zero_of_family_siegel_gain c (fun i => siegelHomCombination (A i) (B i) m a)
    (fun i => ?_) hr ?_ (hcomp a) hlt
  · -- continuity of the local representative on the small closed polydisc
    refine ((differentiableOn_siegelHomCombination (hA i) (hB i) a).continuousOn.comp
      (continuousOn_const.add continuousOn_id) ?_)
    intro y hy k
    have hyk : ‖y k‖ ≤ r := le_trans (norm_le_pi_norm y k) (by simpa using hy)
    refine Metric.mem_ball.mpr ?_
    have : dist ((c i + y) k) (c i k) = ‖y k‖ := by
      simp
    rw [this]
    exact lt_of_le_of_lt hyk (lt_trans hrR hRR₁)
  · intro M hM i y hy
    have := hgain M hM i y hy
    calc ‖siegelHomCombination (A i) (B i) m a (c i + y)‖
        ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
          ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := this
      _ = M * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
          ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) := by ring

/-- **The chartwise assembly with the geometric input in transition form, locally.** -/
theorem exists_ne_zero_chart_vanishing_of_transition_local [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {R R₁ r C : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) (hr : 0 ≤ r) (hrR : r < R)
    (hC : 0 ≤ C)
    (hA : ∀ i k, DifferentiableOn ℂ (A i k) (polydiscSet (c i) (fun _ => R₁)))
    (hB : ∀ i k, DifferentiableOn ℂ (B i k) (polydiscSet (c i) (fun _ => R₁)))
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (htrans : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ),
      ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
        siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A j) (B j) m a (c j + y))
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        siegelHomCombination (A i) (B i) m a (c i + y) = 0 :=
  exists_ne_zero_chart_vanishing_local (N := N) A B c hR hRR₁ hr hrR hA hB hcount
    (fun a => hcomp_of_transition (fun i => siegelHomCombination (A i) (B i) m a) c hC
      (htrans a)) hlt

/-! ## The algebraic relation -/

/-- **A nonzero polynomial relation among the chart quotients, from locally holomorphic chart
data.**  The relation holds at every point of a small polydisc at which the denominators of that
chart do not vanish, which is the whole polydisc off a proper analytic subset. -/
theorem exists_ne_zero_poly_eval_eq_zero_local [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (c : ι → (Fin n → ℂ)) {R R₁ r C : ℝ} (hR : 0 < R) (hRR₁ : R < R₁) (hr : 0 ≤ r) (hrR : r < R)
    (hC : 0 ≤ C)
    (hA : ∀ i k, DifferentiableOn ℂ (A i k) (polydiscSet (c i) (fun _ => R₁)))
    (hB : ∀ i k, DifferentiableOn ℂ (B i k) (polydiscSet (c i) (fun _ => R₁)))
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (htrans : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ),
      ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
        siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A j) (B j) m a (c j + y))
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ, P ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → (∀ k, B i k (c i + y) ≠ 0) →
        MvPolynomial.eval (fun k => A i k (c i + y) / B i k (c i + y)) P = 0 := by
  obtain ⟨a, ha, hvan⟩ :=
    exists_ne_zero_chart_vanishing_of_transition_local (N := N) A B c hR hRR₁ hr hrR hC
      hA hB hcount htrans hlt
  refine ⟨siegelPoly a, siegelPoly_ne_zero ha, ?_⟩
  intro i y hy hden
  have hcomb := siegelCombination_eq_zero_of_hom_eq_zero (A i) (B i) a (c i + y) hden
    (hvan i y hy)
  have heval := eval_siegelPoly_eq_siegelCombination
    (fun k w => A i k w / B i k w) a (c i + y)
  rw [heval]
  exact hcomb

end GaloisForLFunctions.HTGeometry
