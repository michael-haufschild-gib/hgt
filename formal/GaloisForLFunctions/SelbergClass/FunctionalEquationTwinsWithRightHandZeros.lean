import GaloisForLFunctions.RHTower.GammaRCubeFunctionalEquationAbundance
import GaloisForLFunctions.RHTower.TwinRigidityOffLineZero
import GaloisForLFunctions.HTGeometry.EvaluationMinorGeneralDomain
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Functional-equation twins with arbitrarily right-hand zeros

The completed functional equation of `ζ³`, its principal parts, and any finite initial
segment of its Dirichlet coefficients do not impose a zero-free right half-plane.
Dirichlet uniqueness preserves independence of entire theta perturbations on every
real right ray. A nonsingular evaluation matrix then permits simultaneous cancellation
at arbitrarily many distinct points beyond any fixed bound.
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
    Nat.cast_succ, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.cpow_neg, div_eq_mul_inv]

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

/-- Dirichlet uniqueness preserves independence after restricting the completions to
any real right ray. This is what permits simultaneous zero interpolation. -/
private theorem independent_on_real_ray {k : ℕ} (e : Fin k → ℕ → ℂ)
    (E : Fin k → ℂ → ℂ) (hind : LinearIndependent ℂ e)
    (hsum : ∀ j s, 3 < s.re → LSeriesSummable (dirichletCoeffs (e j)) s)
    (hrep : ∀ j s, 3 < s.re →
      E j s = LSeries (dirichletCoeffs (e j)) s * Gammaℝ s ^ 3) (B : ℝ) :
    LinearIndependent ℂ (fun j => fun x : {σ : ℝ // max B 3 < σ} => E j x) := by
  classical
  rw [Fintype.linearIndependent_iff] at hind ⊢
  intro c hc
  let f : ℕ → ℂ := ∑ j, c j • dirichletCoeffs (e j)
  have hf (s : ℂ) (hs : 3 < s.re) : LSeriesSummable f s :=
    LSeriesSummable.sum fun j _ => (hsum j s hs).smul (c j)
  have hev : (fun x : ℝ => LSeries f x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (max B 3)] with x hx
    have hx3 : 3 < (x : ℂ).re := (le_max_right B 3).trans_lt hx
    have heval := congrFun hc ⟨x, hx⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at heval
    have hmul : LSeries f x * Gammaℝ x ^ 3 = 0 := by
      dsimp only [f]
      rw [LSeries_sum (fun j _ => (hsum j x hx3).smul (c j)), Finset.sum_mul]
      simp only [LSeries_smul]
      convert heval using 1
      exact Finset.sum_congr rfl fun j _ => by rw [hrep j x hx3]; ring
    exact (mul_eq_zero.mp hmul).resolve_right
      (pow_ne_zero 3 (Gammaℝ_ne_zero_of_re_pos (by linarith)))
  have hfzero : ∀ n, n ≠ 0 → f n = 0 := by
    rcases LSeries_eventually_eq_zero_iff'.mp hev with hz | htop
    · exact hz
    · have hle := (hf 4 (by norm_num)).abscissaOfAbsConv_le
      rw [htop] at hle
      exact ((not_le_of_gt (EReal.coe_lt_top _)) hle).elim
  apply hind c
  funext n
  have hz := hfzero (n + 1) (Nat.succ_ne_zero n)
  simpa only [f, Finset.sum_apply, Pi.smul_apply, dirichletCoeffs,
    smul_eq_mul, Pi.zero_apply] using hz

/-- The coefficients of the cube of the Riemann zeta function. -/
def cubicZetaCoeffs (n : ℕ) : ℂ := RHTower.TwinRigidity.zetaPowCoeff 3 n

/-- For every finite coefficient prefix and every real bound, a normalized twin of
`ζ³` has arbitrarily many distinct real zeros beyond that bound. The same functional
equation and principal parts survive, with absolute Dirichlet convergence on `Re s > 3`.
The points are chosen together with the twin; they are not prescribed in advance. -/
theorem exists_cubic_twin_with_many_right_hand_zeros (N k : ℕ) (B : ℝ) :
    ∃ a : ℕ → ℂ, ∃ F : ℂ → ℂ, ∃ σ : Fin k → ℝ,
      a 1 = 1 ∧ (∀ n, n < N → a n = cubicZetaCoeffs n) ∧
      (∀ s : ℂ, 3 < s.re → LSeriesSummable a s) ∧
      Differentiable ℂ (fun s => F s - completedRiemannZeta s ^ 3) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s : ℂ, 3 < s.re → F s = LSeries a s * Gammaℝ s ^ 3) ∧
      Function.Injective σ ∧ ∀ j, max B 3 < σ j ∧ F (σ j) = 0 := by
  classical
  obtain ⟨es, Es, hind, hfam⟩ := exists_entire_perturbation_family (max N 2)
  let e : Fin k → ℕ → ℂ := fun j => es j
  let E : Fin k → ℂ → ℂ := fun j => Es j
  have hi : LinearIndependent ℂ e := hind.comp Fin.val Fin.val_injective
  have heSum (j : Fin k) (s : ℂ) (hs : 3 < s.re) :
      LSeriesSummable (dirichletCoeffs (e j)) s := by
    obtain ⟨C, hC⟩ := (hfam (j : ℕ)).2.1
    exact summable_dirichletCoeffs hC hs
  have heRep (j : Fin k) (s : ℂ) (hs : 3 < s.re) :
      E j s = LSeries (dirichletCoeffs (e j)) s * Gammaℝ s ^ 3 :=
    (hfam (j : ℕ)).2.2.2.2 s hs
  obtain ⟨points, P, hinj, hdet, hP⟩ :=
    HTGeometry.exists_injective_evaluation_minor_of_linearIndependent _
      (independent_on_real_ray e E hi heSum heRep B)
  have hunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hdet
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
    (fun i => -(completedRiemannZeta (points i : ℝ) ^ 3))
  let b : ℕ → ℂ := ∑ j, c j • dirichletCoeffs (e j)
  let a : ℕ → ℂ := cubicZetaCoeffs + b
  let F : ℂ → ℂ := fun s => completedRiemannZeta s ^ 3 + ∑ j, c j * E j s
  have hbSum (s : ℂ) (hs : 3 < s.re) : LSeriesSummable b s :=
    LSeriesSummable.sum fun j _ => (heSum j s hs).smul (c j)
  have hbRep (s : ℂ) (hs : 3 < s.re) :
      (∑ j, c j * E j s) = LSeries b s * Gammaℝ s ^ 3 := by
    dsimp only [b]
    rw [LSeries_sum (fun j _ => (heSum j s hs).smul (c j)), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [LSeries_smul, heRep j s hs]
    ring
  have hcoeff (n : ℕ) (hn : n < max N 2) : a n = cubicZetaCoeffs n := by
    have hb : b n = 0 := by
      dsimp only [b]
      rw [Finset.sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      cases n with
      | zero => simp only [Pi.smul_apply, dirichletCoeffs, smul_zero]
      | succ n => simp only [Pi.smul_apply, dirichletCoeffs, e,
          (hfam (j : ℕ)).1 n hn, smul_zero]
    change cubicZetaCoeffs n + b n = cubicZetaCoeffs n
    rw [hb, add_zero]
  refine ⟨a, F, fun j => points j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcoeff 1 (by omega)]
    simp only [cubicZetaCoeffs, RHTower.TwinRigidity.zetaPowCoeff_one, Complex.ofReal_one]
  · intro n hn
    exact hcoeff n (hn.trans_le (le_max_left N 2))
  · intro s hs
    have hz : LSeriesSummable cubicZetaCoeffs s :=
      (RHTower.TwinRigidity.lseries_zetaPowCoeff 3 (by linarith)).1
    exact hz.add (hbSum s hs)
  · have heq : (fun s => F s - completedRiemannZeta s ^ 3) =
        fun s => ∑ j, c j * E j s := by
      funext s
      dsimp only [F]
      ring
    rw [heq]
    exact Differentiable.sum fun j _ => ((hfam (j : ℕ)).2.2.1).const_mul (c j)
  · intro s
    dsimp only [F]
    rw [completedRiemannZeta_one_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z : ℂ => c j * z) ((hfam (j : ℕ)).2.2.2.1 s)
  · intro s hs
    have hz := RHTower.TwinRigidity.lseries_zetaPowCoeff 3 (s := s) (by linarith)
    have hzSum : LSeriesSummable cubicZetaCoeffs s := hz.1
    have hzVal : LSeries cubicZetaCoeffs s = riemannZeta s ^ 3 := hz.2
    have hs0 : s ≠ 0 := by intro h; simp only [h, zero_re] at hs; linarith
    have hG := Gammaℝ_ne_zero_of_re_pos (s := s) (by linarith)
    have hZ : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs0, div_mul_cancel₀ _ hG]
    dsimp only [F, a]
    rw [LSeries_add hzSum (hbSum s hs), hzVal, hbRep s hs, hZ, mul_pow]
    ring
  · intro i j hij
    exact hinj (Subtype.ext hij)
  · intro i
    refine ⟨(points i).property, ?_⟩
    have hi := congrFun hc i
    have hcancel : (∑ j, c j * E j (points i : ℝ)) =
        -(completedRiemannZeta (points i : ℝ) ^ 3) := by
      simpa only [Matrix.mulVec, dotProduct, hP, mul_comm] using hi
    dsimp only [F]
    rw [hcancel, add_neg_cancel]


/-- A normalized twin agreeing with any finite prefix of `ζ³` can have a real zero
arbitrarily far to the right while retaining the completed functional equation and poles. -/
theorem exists_cubic_twin_with_right_hand_zero (N : ℕ) (B : ℝ) :
    ∃ a : ℕ → ℂ, ∃ F : ℂ → ℂ, ∃ σ : ℝ,
      a 1 = 1 ∧ (∀ n, n < N → a n = cubicZetaCoeffs n) ∧
      (∀ s : ℂ, 3 < s.re → LSeriesSummable a s) ∧
      Differentiable ℂ (fun s => F s - completedRiemannZeta s ^ 3) ∧
      (∀ s, F (1 - s) = F s) ∧
      (∀ s : ℂ, 3 < s.re → F s = LSeries a s * Gammaℝ s ^ 3) ∧
      max B 3 < σ ∧ F σ = 0 := by
  obtain ⟨a, F, σ, ha, hp, hs, he, hf, hr, _, hz⟩ :=
    exists_cubic_twin_with_many_right_hand_zeros N 1 B
  exact ⟨a, F, σ 0, ha, hp, hs, he, hf, hr, hz 0⟩

end GaloisForLFunctions.SelbergClass
