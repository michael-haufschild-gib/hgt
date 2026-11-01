import GaloisForLFunctions.RHTower.GammaRCubeFunctionalEquationAbundance
import GaloisForLFunctions.RHTower.TwinRigidityOffLineZero
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Functional-equation twins with arbitrarily right-hand zeros

The completed functional equation of `ζ³`, its principal parts, and any finite initial
segment of its Dirichlet coefficients do not impose a zero-free right half-plane.
A nonzero entire theta perturbation is nonzero somewhere on every real right ray by
Dirichlet uniqueness. Scaling it cancels the completed `ζ³` at that point.
-/

noncomputable section

open Complex Filter Topology MeasureTheory

namespace GaloisForLFunctions.SelbergClass

open RHTower.DegreeThreeHankel

/-- Shift a sequence indexed by `n + 1` to the usual Dirichlet indexing. -/
private def dirichletCoeffs (e : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => e n

private theorem summable_dirichletCoeffs {e : ℕ → ℂ} {C : ℝ}
    (he : ∀ n, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ 2) {s : ℂ} (hs : 3 < s.re) :
    LSeriesSummable (dirichletCoeffs e) s := by
  refine LSeriesSummable_of_le_const_mul_rpow hs ⟨C, fun n hn => ?_⟩
  cases n with
  | zero => exact (hn rfl).elim
  | succ n => simpa only [dirichletCoeffs, Nat.cast_add, Nat.cast_one,
      show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] using he n

private theorem lseries_dirichletCoeffs {e : ℕ → ℂ} {C : ℝ}
    (he : ∀ n, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ 2) {s : ℂ} (hs : 3 < s.re) :
    LSeries (dirichletCoeffs e) s =
      ∑' n : ℕ, e n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
  rw [LSeries, (summable_dirichletCoeffs he hs).tsum_eq_zero_add]
  simp only [LSeries.term_zero, zero_add]
  apply tsum_congr
  intro n
  simp only [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), dirichletCoeffs,
    Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.cpow_neg, div_eq_mul_inv]

/-- A nonzero polynomial-growth Dirichlet sequence cannot vanish on a real right ray. -/
private theorem exists_real_nonzero {e : ℕ → ℂ} {C : ℝ}
    (he : ∀ n, ‖e n‖ ≤ C * ((n : ℝ) + 1) ^ 2) (hne : e ≠ 0) (B : ℝ) :
    ∃ σ : ℝ, max B 3 < σ ∧ LSeries (dirichletCoeffs e) σ ≠ 0 := by
  by_contra! h
  have hev : (fun x : ℝ => LSeries (dirichletCoeffs e) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (max B 3)] with x hx
    exact h x hx
  rcases LSeries_eventually_eq_zero_iff'.mp hev with hz | htop
  · apply hne
    funext n
    exact hz (n + 1) (Nat.succ_ne_zero n)
  · have hle := (summable_dirichletCoeffs he (s := 4) (by norm_num)).abscissaOfAbsConv_le
    rw [htop] at hle
    exact (not_le_of_gt (EReal.coe_lt_top _)) hle

/-- The theta construction supplies independent entire Dirichlet completions beyond
every prescribed initial coefficient segment. -/
private theorem exists_entire_perturbation_family (N : ℕ) :
    ∃ e : ℕ → ℕ → ℂ, ∃ E : ℕ → ℂ → ℂ,
      LinearIndependent ℂ e ∧ ∀ j,
      (∀ n, n + 1 < N → e j n = 0) ∧
      (∃ C : ℝ, ∀ n, ‖e j n‖ ≤ C * ((n : ℝ) + 1) ^ 2) ∧
      Differentiable ℂ (E j) ∧ (∀ s, E j (1 - s) = E j s) ∧
      (∀ s : ℂ, 3 < s.re → E j s = LSeries (dirichletCoeffs (e j)) s * Gammaℝ s ^ 3) := by
  obtain ⟨e, hind, he⟩ := gammaRCube_theta_relations_vanishing_below N
  refine ⟨e, fun j => mellin (fun y : ℝ =>
    ∑' n, e j n * RHTower.gammaRPowKernel 2 (((n : ℝ) + 1) * y)), hind, fun j => ?_⟩
  obtain ⟨hlow, C, hC, hsym⟩ := he j
  have hC' : ∀ n, ‖e j n‖ ≤ C * ((n : ℝ) + 1) ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hC
  obtain ⟨hentire, hfe, hrep⟩ := RHTower.gammaRPow_theta_converse 2 (by norm_num) hC' hsym
  refine ⟨hlow, ⟨C, hC⟩, hentire, hfe, ?_⟩
  intro s hs
  rw [lseries_dirichletCoeffs hC hs]
  exact hrep s (by linarith)

/-- The coefficients of the cube of the Riemann zeta function. -/
def cubicZetaCoeffs (n : ℕ) : ℂ := RHTower.TwinRigidity.zetaPowCoeff 3 n

/-- Any finite coefficient prefix of `ζ³` is compatible with its completed functional
equation and poles, and with a real zero arbitrarily far to the right. Absolute
Dirichlet convergence holds throughout `Re s > 3`. -/
theorem exists_cubic_twin_with_right_hand_zero (N : ℕ) (B : ℝ) :
    ∃ a : ℕ → ℂ, ∃ F : ℂ → ℂ, ∃ σ : ℝ,
      a 1 = 1 ∧ (∀ n, n < N → a n = cubicZetaCoeffs n) ∧
      (∀ s : ℂ, 3 < s.re → LSeriesSummable a s) ∧
      Differentiable ℂ (fun s => F s - completedRiemannZeta s ^ 3) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s : ℂ, 3 < s.re → F s = LSeries a s * Gammaℝ s ^ 3) ∧
      max B 3 < σ ∧ F σ = 0 := by
  obtain ⟨es, Es, hind, hfam⟩ := exists_entire_perturbation_family (max N 2)
  obtain ⟨hlow, ⟨C, hC⟩, hE, hfe, hrep⟩ := hfam 0
  let e := es 0
  let E := Es 0
  obtain ⟨σ, hσ, hnonzero⟩ := exists_real_nonzero hC (hind.ne_zero 0) B
  have hσ3 : 3 < σ := (le_max_right B 3).trans_lt hσ
  have hEσ : E σ ≠ 0 := by
    rw [hrep σ (by simpa using hσ3)]
    exact mul_ne_zero hnonzero
      (pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (by simpa using (by linarith : 0 < σ))))
  let c : ℂ := -(completedRiemannZeta σ ^ 3) / E σ
  let a : ℕ → ℂ := cubicZetaCoeffs + c • dirichletCoeffs e
  let F : ℂ → ℂ := fun s => completedRiemannZeta s ^ 3 + c * E s
  have hsum (s : ℂ) (hs : 3 < s.re) : LSeriesSummable a s := by
    have hz : LSeriesSummable cubicZetaCoeffs s :=
      (RHTower.TwinRigidity.lseries_zetaPowCoeff 3 (by linarith)).1
    exact hz.add ((summable_dirichletCoeffs hC hs).smul c)
  have hcoeff (n : ℕ) (hn : n < max N 2) : a n = cubicZetaCoeffs n := by
    cases n with
    | zero => simp [a, dirichletCoeffs]
    | succ n => simp [a, dirichletCoeffs, hlow n hn]
  refine ⟨a, F, σ, ?_, ?_, hsum, ?_, ?_, ?_, hσ, ?_⟩
  · rw [hcoeff 1 (by omega)]
    simp only [cubicZetaCoeffs, RHTower.TwinRigidity.zetaPowCoeff_one, Complex.ofReal_one]
  · intro n hn
    exact hcoeff n (hn.trans_le (le_max_left N 2))
  · have heq : (fun s => F s - completedRiemannZeta s ^ 3) = fun s => c * E s := by
      funext s
      dsimp only [F]
      ring
    rw [heq]
    exact hE.const_mul c
  · intro s
    dsimp only [F]
    rw [completedRiemannZeta_one_sub, hfe]
  · intro s hs
    have hz := RHTower.TwinRigidity.lseries_zetaPowCoeff 3 (s := s) (by linarith)
    have hzsum : LSeriesSummable cubicZetaCoeffs s := hz.1
    have hzval : LSeries cubicZetaCoeffs s = riemannZeta s ^ 3 := hz.2
    have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hs; linarith
    have hG := Gammaℝ_ne_zero_of_re_pos (s := s) (by linarith)
    have hZ : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _ hG]
    dsimp only [F, a]
    rw [LSeries_add hzsum ((summable_dirichletCoeffs hC hs).smul c), LSeries_smul,
      hzval, hZ, hrep s hs, mul_pow]
    ring
  · dsimp only [F, c]
    rw [div_mul_cancel₀ _ hEσ]
    exact add_neg_cancel _

end GaloisForLFunctions.SelbergClass
