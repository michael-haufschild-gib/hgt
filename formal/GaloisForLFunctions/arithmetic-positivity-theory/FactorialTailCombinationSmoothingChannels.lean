import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialSpanTestMellinLowFrequency
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialTailSampling
import GaloisForLFunctions.«arithmetic-positivity-theory».SourceRelativeSchurMarginAndPerturbationCalculus
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzTailPrimePolarBudget
import GaloisForLFunctions.BiScaleUncertainty.FactorialMuntzWeilSmoothing
import GaloisForLFunctions.RHTower.NullRayDilationCriticality
import GaloisForLFunctions.RHTower.EvenSectorStripPositivity
import GaloisForLFunctions.RHTower.RiemannKernelStripLPMaximality
import GaloisForLFunctions.RHTower.CHMDGraphDivisorPairing

/-! Smoothing channels of the explicit formula for real combinations of the factorial tails.

For a real finite combination `g = ∑_{n ∈ S} d_n T_n` of literal correction tails and its
tail-by-tail mollification `g_k = ∑ d_n (η_k * T_n)`:
1. each `g_k` belongs to the decay class, with decay `C e^{-3|x|/2}` uniform in `k`, so the
   explicit formula `archPoleEnergy g_k = Re W(g_k, g_k) + T_Λ(g_k ⋆ g̃_k)` holds with the
   literal von Mangoldt atom pairing;
2. the readouts factor as `F_{g_k}(γ(s)) = κ_k(s) F_g(γ(s))` for `Re s > -1`, with
   `|κ_k| ≤ e` on the closed strip and `κ_k → 1`;
3. hence, by dominated convergence, the zero-side diagonal, the polar readouts, the spectral
   mass on every measurable frequency set, and the atom pairing (dominated by the prime
   majorant of order `7/4`) of `g_k` converge to those of `g`. -/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ComplexConjugate
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar

namespace GaloisForLFunctions.ArithmeticPositivityTheory

noncomputable section
set_option autoImplicit false

/-- A real finite combination `∑_{n ∈ S} d_n T_n` of literal correction tails. -/
def factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, d n * factorialMuntzCorrectedTail n x

/-- The tail-by-tail mollification `∑_{n ∈ S} d_n (η_k * T_n)`. -/
def factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ S, d n * factorialMuntzSmoothedTail n k x

/-- The complexified combination is the span test with coefficients `b_n = d_n a_n`. -/
theorem factorialTailCombination_ofReal_eq_spanTest (S : Finset ℕ) (d : ℕ → ℝ) :
    (fun x => (factorialTailCombination S d x : ℂ)) =
      factorialSpanTest S (fun n => (d n : ℂ) * (factorialTailAmplitude n : ℂ)) := by
  rw [← sum_factorialMuntzCorrectedTail_eq_factorialSpanTest]
  funext x
  simp [factorialTailCombination]

theorem expDecayTest_const_mul {F : ℝ → ℝ} (hF : ExpDecayTest F) (c : ℝ) :
    ExpDecayTest fun x => c * F x := by
  obtain ⟨hs, δ, C, hδ, hC, hb⟩ := hF
  refine ⟨contDiff_const.mul hs, δ, |c| * C, hδ, by positivity, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hb x
  have hd : deriv (fun x => c * F x) x = c * deriv F x :=
    deriv_const_mul c ((hs.differentiable (by norm_num)) x)
  refine ⟨?_, ?_⟩
  · rw [abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
  · rw [hd, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg c)

theorem expDecayTest_zero : ExpDecayTest fun _ : ℝ => (0 : ℝ) :=
  ⟨contDiff_const, 1, 0, one_pos, le_rfl, fun x => by simp⟩

theorem expDecayTest_finset_sum {ι : Type*} (S : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ S, ExpDecayTest (F i)) : ExpDecayTest fun x => ∑ i ∈ S, F i x := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using expDecayTest_zero
  | insert a s ha ih =>
    have h := (hF a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))
    refine (show (fun x => ∑ i ∈ insert a s, F i x) = F a + fun x => ∑ i ∈ s, F i x from ?_) ▸ h
    funext x
    rw [Finset.sum_insert ha]
    rfl

theorem factorialTailCombinationSmoothed_expDecayTest (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) :
    ExpDecayTest (factorialTailCombinationSmoothed S d k) :=
  expDecayTest_finset_sum S fun n _ =>
    expDecayTest_const_mul (factorialMuntzSmoothedTail_expDecayTest n k) (d n)

/-- A decay constant for the combination, uniform in the smoothing index. -/
def factorialTailCombinationDecayConstant (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, |d n| * (12 * Real.exp (3 / 2) / Real.sqrt ((n + 1 : ℕ) : ℝ))

theorem factorialTailCombinationDecayConstant_nonneg (S : Finset ℕ) (d : ℕ → ℝ) :
    0 ≤ factorialTailCombinationDecayConstant S d :=
  Finset.sum_nonneg fun n _ => by positivity

theorem abs_factorialTailCombinationSmoothed_le (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) (x : ℝ) :
    |factorialTailCombinationSmoothed S d k x| ≤
      factorialTailCombinationDecayConstant S d * Real.exp (-((3 / 2 : ℝ) * |x|)) := by
  unfold factorialTailCombinationSmoothed factorialTailCombinationDecayConstant
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (factorialMuntzSmoothedTail_exp_bound n k x) (abs_nonneg _)

theorem abs_factorialTailCombination_le (S : Finset ℕ) (d : ℕ → ℝ) (x : ℝ) :
    |factorialTailCombination S d x| ≤
      factorialTailCombinationDecayConstant S d * Real.exp (-((3 / 2 : ℝ) * |x|)) := by
  unfold factorialTailCombination factorialTailCombinationDecayConstant
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ((factorialMuntzCorrectedTail_exp_bound n x).trans ?_)
    (abs_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  have he : (1 : ℝ) ≤ Real.exp (3 / 2) := Real.one_le_exp (by norm_num)
  exact div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)

/-- **Readout factorization.** For `Re s > -1` the smoothed combination's tilted readout is the
kernel readout times the raw combination's readout. -/
theorem factorialTailCombinationSmoothed_readout (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) {s : ℂ}
    (hs : -1 < s.re) :
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
        (factorialTailCombination S d x : ℂ)) ∧
    Integrable (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
        (factorialTailCombinationSmoothed S d k x : ℂ)) ∧
    (∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) * (factorialTailCombinationSmoothed S d k x : ℂ))
      = factorialMuntzKernelReadout k s *
        ∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) * (factorialTailCombination S d x : ℂ) := by
  have hT (n : ℕ) := factorialMuntzCorrectedTail_readout_integrable n s hs
  have hU (n : ℕ) := (factorialMuntzSmoothedTail_readout n k s hs).1
  have he1 : (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (factorialTailCombination S d x : ℂ)) = fun x : ℝ => ∑ n ∈ S, (d n : ℂ) *
        (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (factorialMuntzCorrectedTail n x : ℂ)) := by
    funext x
    simp only [factorialTailCombination]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  have he2 : (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (factorialTailCombinationSmoothed S d k x : ℂ)) = fun x : ℝ => ∑ n ∈ S, (d n : ℂ) *
        (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (factorialMuntzSmoothedTail n k x : ℂ)) := by
    funext x
    simp only [factorialTailCombinationSmoothed]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [he1, he2]
  refine ⟨integrable_finsetSum _ fun n _ => (hT n).const_mul _,
    integrable_finsetSum _ fun n _ => (hU n).const_mul _, ?_⟩
  rw [integral_finsetSum _ fun n _ => (hU n).const_mul _,
    integral_finsetSum _ fun n _ => (hT n).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_const_mul, (factorialMuntzSmoothedTail_readout n k s hs).2]
  ring

theorem paperFT_gammaOf_eq_tilt (f : ℝ → ℂ) (s : ℂ) :
    paperFT f (gammaOf s) = ∫ x : ℝ, Complex.exp ((s - 1 / 2) * (x : ℂ)) * f x := by
  simp only [paperFT, gammaOf, mul_div_cancel₀ _ Complex.I_ne_zero, mul_comm]

theorem paperFT_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) {s : ℂ}
    (hs : -1 < s.re) :
    paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) (gammaOf s) =
      factorialMuntzKernelReadout k s *
        paperFT (fun x => (factorialTailCombination S d x : ℂ)) (gammaOf s) := by
  rw [paperFT_gammaOf_eq_tilt, paperFT_gammaOf_eq_tilt,
    (factorialTailCombinationSmoothed_readout S d k hs).2.2]

theorem paperFT_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) {s : ℂ} (hs : -1 < s.re) :
    paperFT (fun x => (factorialTailCombination S d x : ℂ)) (gammaOf s) =
      ∑ n ∈ S, (d n : ℂ) *
        paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf s) := by
  have hT (n : ℕ) := factorialMuntzCorrectedTail_readout_integrable n s hs
  rw [paperFT_gammaOf_eq_tilt]
  simp_rw [paperFT_gammaOf_eq_tilt]
  have he : (fun x : ℝ => Complex.exp ((s - 1 / 2) * (x : ℂ)) *
      (factorialTailCombination S d x : ℂ)) = fun x : ℝ => ∑ n ∈ S, (d n : ℂ) *
        (Complex.exp ((s - 1 / 2) * (x : ℂ)) * (factorialMuntzCorrectedTail n x : ℂ)) := by
    funext x
    simp only [factorialTailCombination]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring
  rw [he, integral_finsetSum _ fun n _ => (hT n).const_mul _]
  refine Finset.sum_congr rfl fun n _ => integral_const_mul _ _

/-- The zero-sampling square mass of a tail combination is summable. -/
theorem factorialTailCombination_zeroSquare_summable (S : Finset ℕ) (d : ℕ → ℝ) :
    Summable (zetaZeroSquareSummand fun x => (factorialTailCombination S d x : ℂ)) := by
  have hb : ∀ ρ : zetaZeroConfig.carrier,
      zetaZeroSquareSummand (fun x => (factorialTailCombination S d x : ℂ)) ρ ≤
        S.card * ∑ n ∈ S, d n ^ 2 *
          zetaZeroSquareSummand (fun x => (factorialMuntzCorrectedTail n x : ℂ)) ρ := by
    intro ρ
    have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
    unfold zetaZeroSquareSummand
    rw [paperFT_factorialTailCombination S d (by linarith only [hρ.1])]
    set m : ℝ := (zetaZeroConfig.mult ρ : ℝ)
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have h1 := norm_sum_le S fun n => (d n : ℂ) *
      paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf ρ)
    have h2 := sq_sum_le_card_mul_sum_sq (s := S) (f := fun n => ‖(d n : ℂ) *
      paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf ρ)‖)
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc m * ‖∑ n ∈ S, (d n : ℂ) *
          paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf ρ)‖ ^ 2 ≤
          m * (S.card * ∑ n ∈ S, ‖(d n : ℂ) *
            paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf ρ)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h3.trans h2) hm
      _ = S.card * ∑ n ∈ S, d n ^ 2 * (m *
          ‖paperFT (fun x => (factorialMuntzCorrectedTail n x : ℂ)) (gammaOf ρ)‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
          ring
  refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hb ?_
  exact (summable_sum fun n _ => (factorialTail_zeroSquare_summable n).mul_left _).mul_left _

theorem factorialMuntzKernelReadout_tendsto (s : ℂ) :
    Tendsto (fun k : ℕ => factorialMuntzKernelReadout k s) atTop (𝓝 1) :=
  mollifier_readout_tendsto s

/-- **Zero-side smoothing limit.** The literal zeta Weil diagonals of the smoothed
combinations converge to that of the raw combination. -/
theorem tendsto_W_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => zetaZeroConfig.W
      (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
      (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))) atTop
      (𝓝 (zetaZeroConfig.W (fun x => (factorialTailCombination S d x : ℂ))
        (fun x => (factorialTailCombination S d x : ℂ)))) := by
  set g : ℝ → ℂ := fun x => (factorialTailCombination S d x : ℂ) with hg
  have hZ := factorialTailCombination_zeroSquare_summable S d
  have hsumm := summable_norm_Wsummand g g hZ hZ
  have hfac : ∀ (k : ℕ) (ρ : zetaZeroConfig.carrier),
      zetaZeroConfig.Wsummand (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
        (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) ρ =
      factorialMuntzKernelReadout k ρ * conj (factorialMuntzKernelReadout k (reflect ρ)) *
        zetaZeroConfig.Wsummand g g ρ := by
    intro k ρ
    have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
    have hre : -1 < (reflect (ρ : ℂ)).re := by
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith only [hρ.2]
    unfold ZeroConfig.Wsummand
    rw [← Tail.gammaOf_reflect, paperFT_factorialTailCombinationSmoothed S d k
      (by linarith only [hρ.1]), paperFT_factorialTailCombinationSmoothed S d k hre, map_mul]
    ring
  have hbound : ∀ (k : ℕ) (ρ : zetaZeroConfig.carrier),
      ‖zetaZeroConfig.Wsummand (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
        (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) ρ‖ ≤
      Real.exp 1 ^ 2 * ‖zetaZeroConfig.Wsummand g g ρ‖ := by
    intro k ρ
    have hρ := zetaZeroConfig.strip (ρ : ℂ) ρ.2
    have h1 := factorialMuntzKernelReadout_bound k hρ.1 hρ.2
    have h2 : ‖factorialMuntzKernelReadout k (reflect (ρ : ℂ))‖ ≤ Real.exp 1 := by
      refine factorialMuntzKernelReadout_bound k ?_ ?_ <;>
        simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] <;> linarith
    rw [hfac, norm_mul, norm_mul, Complex.norm_conj, sq]
    gcongr
  refine tendsto_tsum_of_dominated_convergence (hsumm.mul_left _) (fun ρ => ?_)
    (Eventually.of_forall hbound)
  simp_rw [hfac]
  have h := ((factorialMuntzKernelReadout_tendsto (ρ : ℂ)).mul
    ((Complex.continuous_conj.tendsto _).comp
      (factorialMuntzKernelReadout_tendsto (reflect (ρ : ℂ))))).mul_const
    (zetaZeroConfig.Wsummand g g ρ)
  simpa only [Function.comp_def, map_one, one_mul] using h

theorem gammaOf_zero_eq : gammaOf 0 = Complex.I / 2 := by
  simp only [gammaOf, Complex.div_I]
  ring

theorem gammaOf_one_eq : gammaOf 1 = -Complex.I / 2 := by
  simp only [gammaOf, Complex.div_I]
  ring

theorem gammaOf_half_add_I_mul (r : ℝ) : gammaOf (1 / 2 + Complex.I * r) = r := by
  simp only [gammaOf]
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ Complex.I_ne_zero]

/-- **Pole-channel smoothing limit** at every point of the readout half-plane. -/
theorem tendsto_paperFT_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) {s : ℂ}
    (hs : -1 < s.re) :
    Tendsto (fun k : ℕ => paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
      (gammaOf s)) atTop (𝓝 (paperFT (fun x => (factorialTailCombination S d x : ℂ))
        (gammaOf s))) := by
  simp_rw [paperFT_factorialTailCombinationSmoothed S d _ hs]
  simpa only [one_mul] using (factorialMuntzKernelReadout_tendsto s).mul_const
    (paperFT (fun x => (factorialTailCombination S d x : ℂ)) (gammaOf s))

theorem measurable_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) :
    Measurable (factorialTailCombination S d) := by
  unfold factorialTailCombination
  exact Finset.measurable_sum _ fun n _ =>
    measurable_const.mul (factorialMuntzCorrectedTail_measurable n)

theorem integrable_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) :
    Integrable (fun x => (factorialTailCombination S d x : ℂ)) ∧
      MemLp (fun x => (factorialTailCombination S d x : ℂ)) 2 := by
  set C := factorialTailCombinationDecayConstant S d
  have hC : 0 ≤ C := factorialTailCombinationDecayConstant_nonneg S d
  have hm : AEStronglyMeasurable (fun x => (factorialTailCombination S d x : ℂ)) volume :=
    (Complex.measurable_ofReal.comp (measurable_factorialTailCombination S d)).aestronglyMeasurable
  have hb (x : ℝ) : ‖(factorialTailCombination S d x : ℂ)‖ ≤
      C * Real.exp (-((3 / 2 : ℝ) * |x|)) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_factorialTailCombination_le S d x
  have hi : Integrable (fun x : ℝ => C * Real.exp (-((3 / 2 : ℝ) * |x|))) :=
    (RHTower.EvenSector.integrable_exp_neg_rate_abs (by norm_num)).const_mul C
  have h1 : Integrable (fun x => (factorialTailCombination S d x : ℂ)) :=
    hi.mono' hm (Eventually.of_forall hb)
  refine ⟨h1, (memLp_two_iff_integrable_sq_norm hm).mpr ?_⟩
  refine (hi.const_mul C).mono' ((hm.norm.pow 2)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (norm_nonneg _) (hb x) 2
  have he : Real.exp (-((3 / 2 : ℝ) * |x|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := abs_nonneg x; nlinarith)
  calc ‖(factorialTailCombination S d x : ℂ)‖ ^ 2 ≤ (C * Real.exp (-((3 / 2 : ℝ) * |x|))) ^ 2 := h
    _ = C * Real.exp (-((3 / 2 : ℝ) * |x|)) * (C * Real.exp (-((3 / 2 : ℝ) * |x|))) := sq _
    _ ≤ C * Real.exp (-((3 / 2 : ℝ) * |x|)) * C := by
        exact mul_le_mul_of_nonneg_left (by nlinarith [Real.exp_pos (-((3 / 2 : ℝ) * |x|))])
          (by positivity)
    _ = C * (C * Real.exp (-((3 / 2 : ℝ) * |x|))) := by ring

/-- **Plancherel** for a tail combination: `(1/2π) ∫ ‖F_g‖² = ∫ g²`. -/
theorem integral_norm_sq_paperFT_factorialTailCombination (S : Finset ℕ) (d : ℕ → ℝ) :
    Integrable (fun r : ℝ => ‖paperFT (fun x => (factorialTailCombination S d x : ℂ)) r‖ ^ 2) ∧
    (∫ r : ℝ, ‖paperFT (fun x => (factorialTailCombination S d x : ℂ)) r‖ ^ 2) =
      2 * Real.pi * ∫ x : ℝ, ‖(factorialTailCombination S d x : ℂ)‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := integrable_factorialTailCombination S d
  exact ⟨RHTower.KernelStrip.integrable_norm_sq_paperFT h1 h2,
    RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp h1 h2⟩

/-- **Band-energy smoothing limit.** On every measurable set of frequencies, the spectral mass
of the smoothed combinations converges to that of the raw combination. -/
theorem tendsto_setIntegral_norm_sq_paperFT_smoothed (S : Finset ℕ) (d : ℕ → ℝ) (A : Set ℝ) :
    Tendsto (fun k : ℕ => ∫ r in A,
      ‖paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) r‖ ^ 2) atTop
      (𝓝 (∫ r in A, ‖paperFT (fun x => (factorialTailCombination S d x : ℂ)) r‖ ^ 2)) := by
  set g : ℝ → ℂ := fun x => (factorialTailCombination S d x : ℂ) with hg
  obtain ⟨hgi, -⟩ := integral_norm_sq_paperFT_factorialTailCombination S d
  have hre (r : ℝ) : -1 < (1 / 2 + Complex.I * r : ℂ).re := by simp; norm_num
  have hfac (k : ℕ) (r : ℝ) :
      paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) r =
        factorialMuntzKernelReadout k (1 / 2 + Complex.I * r) * paperFT g r := by
    have h := paperFT_factorialTailCombinationSmoothed S d k (hre r)
    rwa [gammaOf_half_add_I_mul] at h
  have hκ (k : ℕ) (r : ℝ) : ‖factorialMuntzKernelReadout k (1 / 2 + Complex.I * r)‖ ≤
      Real.exp 1 := factorialMuntzKernelReadout_bound k (by simp) (by simp; norm_num)
  have hgc : Continuous fun r : ℝ => paperFT g r :=
    RHTower.KernelStrip.continuous_paperFT_of_integrable
      (integrable_factorialTailCombination S d).1
  refine tendsto_integral_of_dominated_convergence (fun r => Real.exp 1 ^ 2 * ‖paperFT g r‖ ^ 2)
    (fun k => ?_) (hgi.const_mul _).integrableOn (fun k => ?_) ?_
  · have hc : Continuous fun r : ℝ =>
        paperFT (fun x => (factorialTailCombinationSmoothed S d k x : ℂ)) r :=
      RHTower.KernelStrip.continuous_paperFT_of_integrable
        ((factorialTailCombinationSmoothed_readout S d k
          (s := 1 / 2) (by norm_num)).2.1.congr (Eventually.of_forall fun x => by simp))
    exact (hc.norm.pow 2).aestronglyMeasurable
  · refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _), hfac, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hκ k r) 2)
      (sq_nonneg _)
  · refine Eventually.of_forall fun r => ?_
    simp_rw [hfac]
    have h := ((factorialMuntzKernelReadout_tendsto (1 / 2 + Complex.I * r)).mul_const
      (paperFT g r)).norm.pow 2
    simpa only [one_mul] using h

theorem factorialTailCombinationSmoothed_tendsto_ae (S : Finset ℕ) (d : ℕ → ℝ) :
    ∀ᵐ x : ℝ, Tendsto (fun k : ℕ => factorialTailCombinationSmoothed S d k x) atTop
      (𝓝 (factorialTailCombination S d x)) := by
  have h : ∀ᵐ x : ℝ, ∀ n ∈ S, Tendsto (fun k : ℕ => factorialMuntzSmoothedTail n k x) atTop
      (𝓝 (factorialMuntzCorrectedTail n x)) :=
    (Filter.eventually_all_finset S).mpr fun n _ => factorialMuntzSmoothedTail_tendsto_ae n
  filter_upwards [h] with x hx
  exact tendsto_finsetSum _ fun n hn => (hx n hn).const_mul (d n)

/-- **Correlation smoothing limit** at every lag. -/
theorem tendsto_crossCorr_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) (y : ℝ) :
    Tendsto (fun k : ℕ => crossCorr (factorialTailCombinationSmoothed S d k)
      (factorialTailCombinationSmoothed S d k) y) atTop
      (𝓝 (crossCorr (factorialTailCombination S d) (factorialTailCombination S d) y)) := by
  set C := factorialTailCombinationDecayConstant S d
  have hC : 0 ≤ C := factorialTailCombinationDecayConstant_nonneg S d
  have hae := factorialTailCombinationSmoothed_tendsto_ae S d
  have hae' : ∀ᵐ t : ℝ, Tendsto (fun k : ℕ => factorialTailCombinationSmoothed S d k (t - y))
      atTop (𝓝 (factorialTailCombination S d (t - y))) :=
    (measurePreserving_sub_right volume y).quasiMeasurePreserving.ae hae
  unfold crossCorr
  refine tendsto_integral_of_dominated_convergence
    (fun t => C * Real.exp (-((3 / 2 : ℝ) * |t|)) * C)
    (fun k => ?_) ((RHTower.EvenSector.integrable_exp_neg_rate_abs (by norm_num)).const_mul C
      |>.mul_const C) (fun k => Eventually.of_forall fun t => ?_) ?_
  · have hc := (factorialTailCombinationSmoothed_expDecayTest S d k).1.continuous
    exact (hc.mul (hc.comp (continuous_sub_right y))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_factorialTailCombinationSmoothed_le S d k t
    have h2 := abs_factorialTailCombinationSmoothed_le S d k (t - y)
    have he : Real.exp (-((3 / 2 : ℝ) * |t - y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have := abs_nonneg (t - y); nlinarith)
    exact mul_le_mul h1 (h2.trans (by nlinarith)) (abs_nonneg _) (by positivity)
  · filter_upwards [hae, hae'] with t h1 h2
    exact h1.mul h2

/-- The atom constant `K = C² ∫ e^{-|t|/4}` of the correlation decay, uniform in `k`. -/
def factorialTailCombinationCorrConstant (S : Finset ℕ) (d : ℕ → ℝ) : ℝ :=
  factorialTailCombinationDecayConstant S d ^ 2 *
    ∫ t : ℝ, Real.exp (-((3 / 2 - 5 / 4 : ℝ) * |t|))

theorem abs_crossCorr_factorialTailCombinationSmoothed_le (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ)
    (y : ℝ) :
    |crossCorr (factorialTailCombinationSmoothed S d k) (factorialTailCombinationSmoothed S d k) y|
      ≤ factorialTailCombinationCorrConstant S d * Real.exp (-((5 / 4 : ℝ) * |y|)) :=
  RHTower.EvenSector.abs_crossCorr_le_of_decay (by norm_num) (by norm_num)
    (factorialTailCombinationDecayConstant_nonneg S d)
    (abs_factorialTailCombinationSmoothed_le S d k)
    (abs_factorialTailCombinationSmoothed_le S d k) y

theorem abs_crossCorr_factorialTailCombination_le (S : Finset ℕ) (d : ℕ → ℝ) (y : ℝ) :
    |crossCorr (factorialTailCombination S d) (factorialTailCombination S d) y|
      ≤ factorialTailCombinationCorrConstant S d * Real.exp (-((5 / 4 : ℝ) * |y|)) :=
  RHTower.EvenSector.abs_crossCorr_le_of_decay (by norm_num) (by norm_num)
    (factorialTailCombinationDecayConstant_nonneg S d)
    (abs_factorialTailCombination_le S d) (abs_factorialTailCombination_le S d) y

/-- The atom weight times the correlation decay at `± log n` is the prime majorant of order
`7/4`. -/
theorem atom_weight_mul_decay_eq (n : ℕ) (hn : 2 ≤ n) :
    (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
        Real.exp (-((5 / 4 : ℝ) * |Real.log n|)) = envelopePrimeMajorant (5 / 4) n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  unfold envelopePrimeMajorant
  rw [if_pos hn, abs_of_nonneg hlog, Real.sqrt_eq_rpow,
    show -((5 / 4 : ℝ) * Real.log n) = Real.log n * (-(5 / 4)) by ring,
    ← Real.rpow_def_of_pos hn0, div_mul_eq_mul_div, mul_div_assoc,
    ← Real.rpow_sub hn0, div_eq_mul_inv (ArithmeticFunction.vonMangoldt n : ℝ),
    ← Real.rpow_neg hn0.le]
  congr 2
  norm_num

/-- **Prime-channel smoothing limit** for the literal von Mangoldt atom pairing. -/
theorem tendsto_atomPairing_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) :
    Tendsto (fun k : ℕ => atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (crossCorr (factorialTailCombinationSmoothed S d k) (factorialTailCombinationSmoothed S d k)))
      atTop (𝓝 (atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (factorialTailCombination S d) (factorialTailCombination S d)))) := by
  set K := factorialTailCombinationCorrConstant S d
  unfold atomPairing
  refine tendsto_tsum_of_dominated_convergence
    ((summable_envelopePrimeMajorant_of_half_lt (by norm_num : (1 / 2 : ℝ) < 5 / 4)).mul_left
      (2 * K))
    (fun n => ?_) (Eventually.of_forall fun k n => ?_)
  · exact ((tendsto_crossCorr_factorialTailCombinationSmoothed S d _).add
      (tendsto_crossCorr_factorialTailCombinationSmoothed S d _)).const_mul _
  · split_ifs with hn
    · have h1 := abs_crossCorr_factorialTailCombinationSmoothed_le S d k (Real.log n)
      have h2 := abs_crossCorr_factorialTailCombinationSmoothed_le S d k (-Real.log n)
      rw [abs_neg] at h2
      have hw : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n :=
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, ← atom_weight_mul_decay_eq n hn]
      calc (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
            |crossCorr (factorialTailCombinationSmoothed S d k)
              (factorialTailCombinationSmoothed S d k) (Real.log n) +
              crossCorr (factorialTailCombinationSmoothed S d k)
              (factorialTailCombinationSmoothed S d k) (-Real.log n)| ≤
            (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
              (2 * (K * Real.exp (-((5 / 4 : ℝ) * |Real.log n|)))) :=
            mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (by linarith)) hw
        _ = 2 * K * ((ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n *
            Real.exp (-((5 / 4 : ℝ) * |Real.log n|))) := by ring
    · simp only [zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg zero_le_two (mul_nonneg (sq_nonneg _)
        (integral_nonneg fun _ => (Real.exp_pos _).le))) (envelopePrimeMajorant_nonneg _ _)

/-- **Explicit formula for the smoothed combinations.** -/
theorem archPoleEnergy_factorialTailCombinationSmoothed (S : Finset ℕ) (d : ℕ → ℝ) (k : ℕ) :
    archPoleEnergy (factorialTailCombinationSmoothed S d k) =
      (zetaZeroConfig.W (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))
        (fun x => (factorialTailCombinationSmoothed S d k x : ℂ))).re +
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (factorialTailCombinationSmoothed S d k)
          (factorialTailCombinationSmoothed S d k)) := by
  have hE := factorialTailCombinationSmoothed_expDecayTest S d k
  rw [archPoleEnergy_eq_re_W_add_abelPrimePairing hE,
    RHTower.NullRayDilation.atomPairing_eq_abelPrimePairing_of_decay hE
      (by norm_num : (1 : ℝ) < 3 / 2) (factorialTailCombinationDecayConstant_nonneg S d)
      (abs_factorialTailCombinationSmoothed_le S d k)]

end

end GaloisForLFunctions.ArithmeticPositivityTheory
