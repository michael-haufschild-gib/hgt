import GaloisForLFunctions.HTGeometry.ExponentialCharacter
import GaloisForLFunctions.HTGeometry.TrigonometricSumWindowMean

/-!
# Uniform nonvanishing of finite oscillatory jets

The first `k` derivatives of a nonzero sum of `k` distinct real frequencies cannot all be small:
an inverse Vandermonde row recovers a coefficient of fixed modulus. Uniform Lipschitz bounds
then keep one real component of one derivative away from zero on a fixed-radius interval.
-/

open Complex Finset Set

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The explicit derivative chain of a finite oscillatory exponential sum. -/
def oscillatoryJet {k : ℕ} (γ : Fin k → ℝ) (c : Fin k → ℂ) (m : ℕ) (t : ℝ) : ℂ :=
  TrigSum.trigSum univ (fun j => c j * (I * γ j) ^ m) γ t

theorem hasDerivAt_oscillatoryJet {k : ℕ} (γ : Fin k → ℝ) (c : Fin k → ℂ)
    (m : ℕ) (t : ℝ) :
    HasDerivAt (oscillatoryJet γ c m) (oscillatoryJet γ c (m + 1) t) t := by
  have hterm (j : Fin k) :
      HasDerivAt (fun y : ℝ => c j * (I * γ j) ^ m * exp (I * (γ j * y)))
        (c j * (I * γ j) ^ (m + 1) * exp (I * (γ j * t))) t := by
    have h := (HTGeometry.hasDerivAt_cexp_const_mul (I * γ j) t).const_mul
      (c j * (I * γ j) ^ m)
    convert h using 1 <;> first
    | rfl
    | exact funext (fun y => by simp only [mul_assoc])
    | simp only [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  convert HasDerivAt.fun_sum (fun j (_ : j ∈ (univ : Finset (Fin k))) => hterm j)
    using 1 <;> rfl

/-- A common Lipschitz bound for the first `k` members of the derivative chain. -/
theorem exists_uniform_oscillatoryJet_lipschitz {k : ℕ} (γ : Fin k → ℝ)
    (c : Fin k → ℂ) :
    ∃ B : ℝ, 0 < B ∧ ∀ m < k, ∀ x y : ℝ,
      ‖oscillatoryJet γ c m x - oscillatoryJet γ c m y‖ ≤ B * |x - y| := by
  let L : ℕ → ℝ := fun m => ∑ j, ‖c j * (I * γ j) ^ m‖ * |γ j|
  have hL : ∀ m, 0 ≤ L m := fun m => sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  refine ⟨(∑ m ∈ range k, L m) + 1, by positivity, ?_⟩
  intro m hm x y
  exact (TrigSum.norm_trigSum_sub_le univ (fun j => c j * (I * γ j) ^ m) γ x y).trans
    (mul_le_mul_of_nonneg_right
      ((single_le_sum (fun i _ => hL i) (mem_range.mpr hm)).trans (by linarith)) (abs_nonneg _))

/-- A fixed inverse Vandermonde matrix forces a uniformly nonzero jet at every real point. -/
theorem exists_pos_forall_large_oscillatoryJet {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, ∃ m : Fin k, η ≤ ‖oscillatoryJet γ c m t‖ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  let p : Fin k → ℂ := fun j => I * γ j
  have hp : Function.Injective p := by
    intro i j hij
    apply hγ
    exact_mod_cast mul_left_cancel₀ I_ne_zero hij
  let V : Matrix (Fin k) (Fin k) ℂ := Matrix.transpose (Matrix.vandermonde p)
  have hdet : IsUnit V.det := by
    dsimp only [V]
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hp)
  let K : ℝ := ∑ m, ‖V⁻¹ j m‖
  have hK : 0 ≤ K := sum_nonneg fun _ _ => norm_nonneg _
  have hcpos : 0 < ‖c j‖ := norm_pos_iff.mpr hj
  refine ⟨‖c j‖ / (K + 1), by positivity, fun t => ?_⟩
  by_contra h
  push Not at h
  let x : Fin k → ℂ := fun i => c i * exp (I * (γ i * t))
  have hVx (m : Fin k) : V.mulVec x m = oscillatoryJet γ c m t := by
    simp only [Matrix.mulVec, dotProduct, V, Matrix.transpose_apply, Matrix.vandermonde_apply,
      x, p, oscillatoryJet, TrigSum.trigSum]
    exact sum_congr rfl fun i _ => by ring
  have hx : ‖x j‖ = ‖c j‖ := by
    dsimp [x]
    rw [norm_mul, show I * ((γ j : ℂ) * t) = I * ((γ j * t : ℝ) : ℂ) by push_cast; rfl,
      norm_exp_I_mul_ofReal, mul_one]
  have hrecover : x j = (V⁻¹.mulVec (V.mulVec x)) j := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V hdet, Matrix.one_mulVec]
  have hbound : ‖x j‖ ≤ K * (‖c j‖ / (K + 1)) := by
    rw [hrecover]
    simp only [Matrix.mulVec, dotProduct]
    calc ‖∑ m, V⁻¹ j m * V.mulVec x m‖ ≤ ∑ m, ‖V⁻¹ j m * V.mulVec x m‖ := norm_sum_le _ _
      _ ≤ ∑ m, ‖V⁻¹ j m‖ * (‖c j‖ / (K + 1)) := by
          refine sum_le_sum fun m _ => ?_
          rw [norm_mul, hVx]
          exact mul_le_mul_of_nonneg_left (h m).le (norm_nonneg _)
      _ = K * (‖c j‖ / (K + 1)) := (sum_mul _ _ _).symm
  have hstrict : K * (‖c j‖ / (K + 1)) < ‖c j‖ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith only [hcpos]
  rw [hx] at hbound
  exact (not_lt_of_ge hbound) hstrict

/-- The two real components, viewed as continuous real linear maps. -/
def traceComponent (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.reCLM else Complex.imCLM

theorem abs_traceComponent_le (b : Bool) (z : ℂ) : |traceComponent b z| ≤ ‖z‖ := by
  cases b
  · exact Complex.abs_im_le_norm z
  · exact Complex.abs_re_le_norm z

theorem hasDerivAt_traceComponent_jet {k : ℕ} (γ : Fin k → ℝ) (c : Fin k → ℂ)
    (b : Bool) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun x => traceComponent b (oscillatoryJet γ c m x))
      (traceComponent b (oscillatoryJet γ c (m + 1) t)) t :=
  (traceComponent b).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_oscillatoryJet γ c m t)

/-- One real component of a derivative stays uniformly away from zero on a fixed-radius
interval about every center. Both the order and component may depend on the center. -/
theorem exists_uniform_oscillatoryJet_window {k : ℕ} (γ : Fin k → ℝ)
    (hγ : Function.Injective γ) (c : Fin k → ℂ) (hc : c ≠ 0) :
    ∃ r A : ℝ, 0 < r ∧ 0 < A ∧ ∀ x : ℝ, ∃ m : Fin k, ∃ b : Bool,
      ∀ y ∈ Ioo (x - r) (x + r), A ≤ |traceComponent b (oscillatoryJet γ c m y)| := by
  obtain ⟨η, hη, hlarge⟩ := exists_pos_forall_large_oscillatoryJet γ hγ c hc
  obtain ⟨B, hB, hLip⟩ := exists_uniform_oscillatoryJet_lipschitz γ c
  refine ⟨η / (8 * B), η / 4, by positivity, by positivity, fun x => ?_⟩
  obtain ⟨m, hm⟩ := hlarge x
  obtain ⟨b, hb⟩ : ∃ b : Bool, η / 2 ≤ |traceComponent b (oscillatoryJet γ c m x)| := by
    have hn := Complex.norm_le_abs_re_add_abs_im (oscillatoryJet γ c m x)
    by_cases h : η / 2 ≤ |(oscillatoryJet γ c m x).re|
    · exact ⟨true, h⟩
    · exact ⟨false, by change η / 2 ≤ |(oscillatoryJet γ c m x).im|; linarith⟩
  refine ⟨m, b, fun y hy => ?_⟩
  have hdist : |y - x| < η / (8 * B) := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hdiff : |traceComponent b (oscillatoryJet γ c m y) -
      traceComponent b (oscillatoryJet γ c m x)| ≤ B * |y - x| := by
    rw [← map_sub]
    exact (abs_traceComponent_le b _).trans (hLip m m.isLt y x)
  have hsmall : B * |y - x| < η / 8 := by
    have := mul_lt_mul_of_pos_left hdist hB
    have heq : B * (η / (8 * B)) = η / 8 := by field_simp
    rwa [heq] at this
  have htri := abs_sub_abs_le_abs_sub (traceComponent b (oscillatoryJet γ c m x))
    (traceComponent b (oscillatoryJet γ c m y))
  rw [abs_sub_comm] at htri
  linarith only [hb, hdiff, hsmall, htri, hη]

#print axioms exists_uniform_oscillatoryJet_window

end GaloisForLFunctions.InfiniteRankWeilTheory
