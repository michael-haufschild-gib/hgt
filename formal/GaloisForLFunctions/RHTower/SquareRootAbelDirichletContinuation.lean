import GaloisForLFunctions.RHTower.SquareRootAbelDirichletKernel
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Holomorphic sum after two square-root Abel summations

A linearly bounded sequence of weighted prefixes supplies a locally uniformly
summable series on `Re(s)>1/2`. The construction uses the explicit weighted
Dirichlet kernel difference and its analytic power envelope.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower
open GaloisForLFunctions.RHTower

/-- One term of the twice-summed Dirichlet continuation. -/
def squareRootAbelDirichletTerm (A : ℕ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  A (n+1)*(squareRootAbelDirichletKernel ((n:ℝ)+1) s -
    squareRootAbelDirichletKernel ((n:ℝ)+2) s)

/-- The candidate continuation supplied by the weighted prefixes. -/
def squareRootAbelDirichletSum (A : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n, squareRootAbelDirichletTerm A n s

/-- Linear prefix growth leaves a summable power for `Re(s)>1/2`. -/
theorem norm_squareRootAbelDirichletTerm_le {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*((n:ℝ)+1))
    (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖squareRootAbelDirichletTerm A n s‖ ≤
      (2*C*(3*‖s‖*‖s+1‖+‖s‖))*((n:ℝ)+1)^(-(s.re+1/2)) := by
  have hx : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : 0 < (n:ℝ)+1 := by positivity
  have hAn : ‖A (n+1)‖ ≤ 2*C*((n:ℝ)+1) := by
    refine (hA (n+1)).trans ?_
    push_cast
    nlinarith [mul_nonneg hC (Nat.cast_nonneg (α := ℝ) n)]
  have hk := norm_squareRootAbelDirichletKernel_sub_succ_le hx hs
  rw [show (n:ℝ)+1+1=(n:ℝ)+2 by ring] at hk
  unfold squareRootAbelDirichletTerm
  rw [norm_mul]
  calc
    _ ≤ (2*C*((n:ℝ)+1))*
        ((3*‖s‖*‖s+1‖+‖s‖)*((n:ℝ)+1)^(-s.re-3/2)) :=
      mul_le_mul hAn hk (norm_nonneg _) (by positivity)
    _ = (2*C*(3*‖s‖*‖s+1‖+‖s‖))*
        (((n:ℝ)+1)^((1:ℝ))*((n:ℝ)+1)^(-s.re-3/2)) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by
      rw [← Real.rpow_add hx0]
      congr 2
      ring

/-- Absolute convergence throughout the strict half-plane. -/
theorem summable_squareRootAbelDirichletTerm {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*((n:ℝ)+1))
    {s : ℂ} (hs : (1/2:ℝ) < s.re) :
    Summable (fun n => squareRootAbelDirichletTerm A n s) := by
  apply Summable.of_norm_bounded
    ((summable_shift_rpow_neg (show 1 < s.re+1/2 by linarith)).mul_left _)
  intro n
  exact norm_squareRootAbelDirichletTerm_le hC hA n (by linarith)

/-- The power bound is uniform on each compact subset of the half-plane. -/
theorem summableLocallyUniformlyOn_squareRootAbelDirichletTerm {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*((n:ℝ)+1)) :
    SummableLocallyUniformlyOn (squareRootAbelDirichletTerm A)
      {s : ℂ | (1/2:ℝ) < s.re} := by
  apply SummableLocallyUniformlyOn_of_locally_bounded
    (isOpen_lt continuous_const Complex.continuous_re)
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨fun _ => 0, summable_zero, by simp⟩
  obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨s₁, hs₁, hmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  have hσ : (1/2:ℝ) < s₀.re := hKsub hs₀
  let D : ℝ := 2*C*(3*‖s₁‖*(‖s₁‖+1)+‖s₁‖)
  refine ⟨fun n => D*((n:ℝ)+1)^(-(s₀.re+1/2)),
    (summable_shift_rpow_neg (by linarith)).mul_left D, ?_⟩
  intro n s hs
  have hsr : s₀.re ≤ s.re := hmin hs
  have hsn : ‖s‖ ≤ ‖s₁‖ := hmax hs
  have hsn1 : ‖s+1‖ ≤ ‖s₁‖+1 := by
    calc
      _ ≤ ‖s‖+1 := by simpa using norm_add_le s 1
      _ ≤ _ := by linarith
  refine (norm_squareRootAbelDirichletTerm_le hC hA n (by linarith)).trans ?_
  apply mul_le_mul
  · dsimp [D]
    gcongr
  · exact Real.rpow_le_rpow_of_exponent_le
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  · positivity
  · dsimp [D]
    positivity

/-- Linear prefix growth yields a holomorphic candidate on the strict half-plane. -/
theorem analyticOnNhd_squareRootAbelDirichletSum {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*((n:ℝ)+1)) :
    AnalyticOnNhd ℂ (squareRootAbelDirichletSum A) {s : ℂ | (1/2:ℝ) < s.re} := by
  have hopen : IsOpen {s : ℂ | (1/2:ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  apply (summableLocallyUniformlyOn_squareRootAbelDirichletTerm hC hA).differentiableOn hopen
  intro n s hs
  exact ((differentiable_squareRootAbelDirichletKernel (by positivity : 0 < (n:ℝ)+1) s).sub
    (differentiable_squareRootAbelDirichletKernel (by positivity : 0 < (n:ℝ)+2) s)).const_mul _

end RHTower
