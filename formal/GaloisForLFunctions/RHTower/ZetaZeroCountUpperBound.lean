import Zeta23.RvM.MainTerm
import Zeta23.GammaFacts.Complete
import Zeta23.Assembly
import Zeta23.Defs.Counting

/-!
# An upper bound for the number of zeros of `ζ` up to height `T`

`N(0,T) ≤ (T/2π)(log(T/2π) - 1) + C log²T` for `T ≥ T₁` (`zeroCount_upper`), by dyadic summation
of the Riemann–von Mangoldt window law `N(t,2t) = (t/2π)ℓ₁(t) + O(log t)` (`Zeta23.RvM.rvM_main`):
the main terms telescope exactly, since `F(2t) - F(t) = (t/2π)ℓ₁(t)` for
`F(t) = (t/2π)(log(t/2π) - 1)`.

The set of distinct nontrivial zeros with `|Im ρ| ≤ T` is finite with at most `2N(0,T) + c₀`
elements (`ncard_lowZeros_le`), by conjugation symmetry.
-/

open Complex Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- `F(t) = (t/2π)(log(t/2π) - 1)`. -/
def zeroCountMain (t : ℝ) : ℝ := t / (2 * π) * (Real.log (t / (2 * π)) - 1)

theorem zeroCountMain_two_mul_sub {t : ℝ} (ht : 0 < t) :
    zeroCountMain (2 * t) - zeroCountMain t = t / (2 * π) * ell1 t := by
  unfold zeroCountMain ell1 l
  have hpi := Real.pi_pos
  have e : Real.log (2 * t / (2 * π)) = Real.log 2 + Real.log (t / (2 * π)) := by
    rw [show 2 * t / (2 * π) = 2 * (t / (2 * π)) by ring, Real.log_mul (by norm_num)
      (by positivity)]
  rw [e]
  have e2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  field_simp
  ring

theorem neg_one_le_zeroCountMain {t : ℝ} (ht : 0 < t) : -1 ≤ zeroCountMain t := by
  unfold zeroCountMain
  have hx : 0 < t / (2 * π) := by positivity
  have h := Real.one_sub_inv_le_log_of_pos hx
  have : t / (2 * π) * (1 - (t / (2 * π))⁻¹) = t / (2 * π) - 1 := by
    field_simp
  nlinarith

theorem N_zero_le_of_le {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) :
    zetaZeroConfig.N 0 a ≤ zetaZeroConfig.N 0 b := by
  rw [Assembly.N_add zetaZeroConfig h0 hab]; omega

/-- The dyadic induction: `N(0,T) ≤ F(T) + k C log T + K` for `T₀ ≤ T ≤ 2^{k+1}T₀`. -/
theorem zeroCount_dyadic {C T₀ : ℝ} (hC : 0 ≤ C) (hT₀ : 3 ≤ T₀)
    (hrvm : ∀ T : ℝ, T₀ ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * π) * ell1 T| ≤ C * Real.log T) :
    ∀ k : ℕ, ∀ T : ℝ, T₀ ≤ T → T ≤ 2 ^ (k + 1) * T₀ →
      (zetaZeroConfig.N 0 T : ℝ) ≤ zeroCountMain T + k * C * Real.log T +
        (zetaZeroConfig.N 0 (2 * T₀) + 1) := by
  intro k
  induction k with
  | zero =>
    intro T hT hT2
    have hmono : zetaZeroConfig.N 0 T ≤ zetaZeroConfig.N 0 (2 * T₀) :=
      N_zero_le_of_le (by linarith) (by simpa using hT2)
    have hF := neg_one_le_zeroCountMain (t := T) (by linarith)
    have : (zetaZeroConfig.N 0 T : ℝ) ≤ zetaZeroConfig.N 0 (2 * T₀) := by exact_mod_cast hmono
    push_cast
    linarith
  | succ k ih =>
    intro T hT hT2
    have hlog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    by_cases hsmall : T ≤ 2 ^ (k + 1) * T₀
    · have := ih T hT hsmall
      have hk : (k : ℝ) * C * Real.log T ≤ ((k + 1 : ℕ) : ℝ) * C * Real.log T := by
        push_cast; nlinarith
      linarith
    · push Not at hsmall
      set T' := T / 2 with hT'
      have hpow : 2 * T₀ ≤ (2 : ℝ) ^ (k + 1) * T₀ := by
        have : (2 : ℝ) ≤ 2 ^ (k + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
      have hT'lo : T₀ ≤ T' := by rw [hT']; linarith
      have hT'hi : T' ≤ 2 ^ (k + 1) * T₀ := by
        have e : (2 : ℝ) ^ (k + 1 + 1) * T₀ = 2 * (2 ^ (k + 1) * T₀) := by ring
        rw [e] at hT2
        rw [hT']; linarith
      have hih := ih T' hT'lo hT'hi
      have h2T : 2 * T' = T := by rw [hT']; ring
      have hsplit : zetaZeroConfig.N 0 T = zetaZeroConfig.N 0 T' + zetaZeroConfig.N T' T :=
        Assembly.N_add zetaZeroConfig (by linarith) (by linarith)
      have hw := hrvm T' hT'lo
      rw [h2T] at hw
      have hw' := (abs_le.mp hw).2
      have htel := zeroCountMain_two_mul_sub (t := T') (by linarith)
      rw [h2T] at htel
      have hlogT' : Real.log T' ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
      have hlogT'0 : 0 ≤ Real.log T' := Real.log_nonneg (by linarith)
      have hk1 : (k : ℝ) * C * Real.log T' ≤ (k : ℝ) * C * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT' (by positivity)
      have hk2 : C * Real.log T' ≤ C * Real.log T := mul_le_mul_of_nonneg_left hlogT' hC
      have hcast : (zetaZeroConfig.N 0 T : ℝ) =
          (zetaZeroConfig.N 0 T' : ℝ) + (zetaZeroConfig.N T' T : ℝ) := by
        rw [hsplit]; push_cast; ring
      rw [hcast]
      push_cast
      linarith

/-- **Upper bound for the zero count.** `N(0,T) ≤ F(T) + C log²T` for `T ≥ T₁`. -/
theorem zeroCount_upper : ∃ C T₁ : ℝ, 0 ≤ C ∧ 3 ≤ T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
    (zetaZeroConfig.N 0 T : ℝ) ≤ zeroCountMain T + C * Real.log T ^ 2 := by
  obtain ⟨C₀, T₀, hrvm⟩ := RvM.rvM_main gammaFacts
  set C := max C₀ 0 with hCdef
  set T₁ := max T₀ 3 with hT₁def
  have hC : 0 ≤ C := le_max_right _ _
  have hT₁3 : 3 ≤ T₁ := le_max_right _ _
  have hrvm' : ∀ T : ℝ, T₁ ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * π) * ell1 T| ≤ C * Real.log T := by
    intro T hT
    refine (hrvm T (le_trans (le_max_left _ _) hT)).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.log_nonneg (by linarith))
  set K : ℝ := (zetaZeroConfig.N 0 (2 * T₁) : ℝ) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * C + K, T₁, by positivity, hT₁3, fun T hT => ?_⟩
  have hTpos : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    have : Real.exp 1 ≤ T := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) this
  set x := T / T₁ with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by linarith)]; linarith
  set k := ⌊Real.logb 2 x⌋₊ with hk
  have hkx : Real.logb 2 x < k + 1 := Nat.lt_floor_add_one _
  have hxlt : x < 2 ^ (k + 1) := by
    have h1 : x = (2 : ℝ) ^ (Real.logb 2 x) := (Real.rpow_logb (by norm_num) (by norm_num)
      (by linarith)).symm
    have h2 : (2 : ℝ) ^ (Real.logb 2 x) < (2 : ℝ) ^ ((k + 1 : ℕ) : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
      push_cast; exact hkx
    rw [Real.rpow_natCast] at h2
    linarith
  have hTle : T ≤ 2 ^ (k + 1) * T₁ := by
    have := hxlt.le
    rw [hx, div_le_iff₀ (by linarith)] at this
    linarith
  have hmain := zeroCount_dyadic hC (by linarith) hrvm' k T hT hTle
  have hkle : (k : ℝ) ≤ 2 * Real.log T := by
    have h1 : (k : ℝ) ≤ Real.logb 2 x := Nat.floor_le (Real.logb_nonneg (by norm_num) hx1)
    have h2 : Real.logb 2 x ≤ Real.logb 2 T := by
      apply Real.logb_le_logb_of_le (by norm_num) (by linarith)
      rw [hx, div_le_iff₀ (by linarith)]; nlinarith
    have h3 : Real.logb 2 T ≤ 2 * Real.log T := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have : 1 / 2 ≤ Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      nlinarith
    linarith
  have hKlog : K ≤ K * Real.log T ^ 2 := by
    have : 1 ≤ Real.log T ^ 2 := by nlinarith
    nlinarith
  have hkC : (k : ℝ) * C * Real.log T ≤ 2 * C * Real.log T ^ 2 := by
    have := mul_le_mul_of_nonneg_right hkle (mul_nonneg hC (by linarith : (0 : ℝ) ≤ Real.log T))
    nlinarith
  have hKeq : (zetaZeroConfig.N 0 (2 * T₁) : ℝ) + 1 = K := rfl
  rw [hKeq] at hmain
  nlinarith

/-! ## Distinct zeros of bounded height -/

/-- The distinct nontrivial zeros with `|Im ρ| ≤ T`. -/
def lowZeros (T : ℝ) : Set ℂ := {ρ | ρ ∈ zetaZeroConfig.carrier ∧ |ρ.im| ≤ T}

theorem lowZeros_finite (T : ℝ) : (lowZeros T).Finite :=
  (zetaZeroConfig.window_finite (-T - 1) T).subset fun ρ hρ =>
    ⟨hρ.1, by linarith [(abs_le.mp hρ.2).1], (abs_le.mp hρ.2).2⟩

theorem conj_mem_zetaCarrier {ρ : ℂ} (hρ : ρ ∈ zetaZeroConfig.carrier) :
    (starRingEnd ℂ) ρ ∈ zetaZeroConfig.carrier := by
  have h : IsNontrivialZero ρ := hρ
  refine ⟨?_, by simpa using h.2.1, by simpa using h.2.2⟩
  rw [_root_.riemannZeta_conj, h.1, map_zero]

/-- **Distinct zeros up to height `T`.** `#{ρ : |Im ρ| ≤ T} ≤ 2N(0,T) + c₀`. -/
theorem ncard_lowZeros_le : ∃ c₀ : ℕ, ∀ T : ℝ, 0 ≤ T →
    (lowZeros T).ncard ≤ 2 * zetaZeroConfig.N 0 T + c₀ := by
  set Z₀ : Set ℂ := zetaZeroConfig.carrier ∩ {ρ | ρ.im = 0} with hZ₀
  have hZ₀fin : Z₀.Finite := (zetaZeroConfig.window_finite (-1) 0).subset fun ρ hρ =>
    ⟨hρ.1, by rw [hρ.2]; norm_num, by rw [hρ.2]⟩
  refine ⟨Z₀.ncard, fun T hT => ?_⟩
  set A := zetaZeroConfig.window 0 T with hA
  have hAfin : A.Finite := zetaZeroConfig.window_finite 0 T
  have hsub : lowZeros T ⊆ (A ∪ (starRingEnd ℂ) '' A) ∪ Z₀ := by
    intro ρ hρ
    rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
    · left; right
      refine ⟨(starRingEnd ℂ) ρ, ⟨conj_mem_zetaCarrier hρ.1, ?_, ?_⟩, by simp⟩
      · simp only [Complex.conj_im]; linarith
      · simp only [Complex.conj_im]; linarith [(abs_le.mp hρ.2).1]
    · right; exact ⟨hρ.1, hzero⟩
    · left; left; exact ⟨hρ.1, hpos, (abs_le.mp hρ.2).2⟩
  have hfin : ((A ∪ (starRingEnd ℂ) '' A) ∪ Z₀).Finite :=
    (hAfin.union (hAfin.image _)).union hZ₀fin
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_union_le (A ∪ (starRingEnd ℂ) '' A) Z₀
  have h3 := Set.ncard_union_le A ((starRingEnd ℂ) '' A)
  have h4 : ((starRingEnd ℂ) '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  have h5 : A.ncard ≤ zetaZeroConfig.N 0 T := zetaZeroConfig.Nd_le_N 0 T
  omega

end

end RHTower
