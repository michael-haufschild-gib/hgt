import GaloisForLFunctions.RHTower.SquareRootAbelDirichletContinuation

/-!
# Square-root prefix continuation on the positive half-plane

The existing twice-Abel kernel gains enough decay from a square-root bound
on its weighted prefixes to continue the Dirichlet sum to `0 < Re(s)`.
This is an analytic implication; it does not assert such a bound for the
arithmetic source.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower
open GaloisForLFunctions.RHTower

/-- Square-root prefix growth improves the twice-Abel term to a summable power throughout the positive half-plane. -/
theorem norm_squareRootAbelDirichletTerm_le_of_sqrt_bound {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*Real.sqrt ((n:ℝ)+1))
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖squareRootAbelDirichletTerm A n s‖ ≤
      (2*C*(3*‖s‖*‖s+1‖+‖s‖))*((n:ℝ)+1)^(-(s.re+1)) := by
  have hx : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
  have hx0 : 0 < (n:ℝ)+1 := by positivity
  have hr : Real.sqrt ((n:ℝ)+2) ≤ 2*Real.sqrt ((n:ℝ)+1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [Real.sq_sqrt hx0.le,hx]
  have hAn : ‖A (n+1)‖ ≤ 2*C*Real.sqrt ((n:ℝ)+1) := by
    have hh := hA (n+1)
    push_cast at hh
    have hm := mul_le_mul_of_nonneg_left hr hC
    calc
      _ ≤ C*Real.sqrt ((n:ℝ)+2) := by
        rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring] at hh
        exact hh
      _ ≤ _ := by nlinarith only [hm]
  have hk := norm_squareRootAbelDirichletKernel_sub_succ_le hx hs
  rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring] at hk
  unfold squareRootAbelDirichletTerm
  rw [norm_mul]
  calc
    _ ≤ (2*C*Real.sqrt ((n:ℝ)+1))*
        ((3*‖s‖*‖s+1‖+‖s‖)*((n:ℝ)+1)^(-s.re-3/2)) :=
      mul_le_mul hAn hk (norm_nonneg _) (by positivity)
    _ = (2*C*(3*‖s‖*‖s+1‖+‖s‖))*
        (((n:ℝ)+1)^((1:ℝ)/2)*((n:ℝ)+1)^(-s.re-3/2)) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = _ := by
      rw [← Real.rpow_add hx0]
      congr 2
      ring

/-- Square-root-bounded weighted prefixes give locally uniform absolute continuation on Re(s)>0. -/
theorem summableLocallyUniformlyOn_squareRootAbelDirichletTerm_of_sqrt_bound
    {A : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ n, ‖A n‖ ≤ C*Real.sqrt ((n:ℝ)+1)) :
    SummableLocallyUniformlyOn (squareRootAbelDirichletTerm A) {s : ℂ | 0 < s.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl|hKne
  · exact ⟨fun _ => 0,summable_zero,by simp⟩
  obtain ⟨s₀,hs₀,hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨s₁,hs₁,hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  have hσ : 0 < s₀.re := hKsub hs₀
  let D : ℝ := 2*C*(3*‖s₁‖*(‖s₁‖+1)+‖s₁‖)
  refine ⟨fun n => D*((n:ℝ)+1)^(-(s₀.re+1)),
    (summable_shift_rpow_neg (by linarith)).mul_left D,?_⟩
  intro n s hs
  have hsr : s₀.re ≤ s.re := hmin hs
  have hsn : ‖s‖ ≤ ‖s₁‖ := hmax hs
  have hsn1 : ‖s+1‖ ≤ ‖s₁‖+1 :=
    (show ‖s+1‖ ≤ ‖s‖+1 by simpa using norm_add_le s 1).trans (by linarith)
  refine (norm_squareRootAbelDirichletTerm_le_of_sqrt_bound hC hA n (by linarith)).trans ?_
  apply mul_le_mul
  · dsimp [D]
    gcongr
  · exact Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (by linarith)
  · positivity
  · dsimp [D]
    positivity

/-- The same twice-Abel series is holomorphic on the full positive half-plane under a square-root prefix bound. -/
theorem analyticOnNhd_squareRootAbelDirichletSum_of_sqrt_bound {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*Real.sqrt ((n:ℝ)+1)) :
    AnalyticOnNhd ℂ (squareRootAbelDirichletSum A) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  apply (summableLocallyUniformlyOn_squareRootAbelDirichletTerm_of_sqrt_bound hC hA).differentiableOn hopen
  intro n s hs
  exact ((differentiable_squareRootAbelDirichletKernel (by positivity : 0 < (n:ℝ)+1) s).sub
    (differentiable_squareRootAbelDirichletKernel (by positivity : 0 < (n:ℝ)+2) s)).const_mul _

end RHTower
