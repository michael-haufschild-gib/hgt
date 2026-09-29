import GaloisForLFunctions.RHTower.Matveev.FeldmanAuxiliaryFunction
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Analytic bounds for Fel'dman's auxiliary function

* **Derivatives along the diagonal.**  From `F′_{σ,τ} = (σ+1) F_{σ+1,τ} + Σ_j log p_j F_{σ,τ+e_j}`,
  if every `|F_{σ′,τ′}(z)|` with `σ′ + |τ′| ≤ n` is at most `β`, then
  `|F^{(t)}_{σ,τ}(z)| ≤ (n + W)^t β` whenever `σ + |τ| + t ≤ n`, where `W = Σ_{j<m} log p_j`.
* **Growth.**  `|γ_j/B| ≤ 2q` and `|ω′| ≤ 2qW`, so
  `|F_{σ,τ}(w)| ≤ U·C·2^N (|w| + N + 1)^N (2q)^{|τ|} e^{2qW|w|}` with `U` the number of unknowns
  and `C` a bound for the coefficients.
* **Distance to the true function.**  `ω′ − ω = −l_m Λ/B`, so for `|z| q |Λ| ≤ 1`,
  `|F_{σ,τ}(z) − Φ_{σ,τ}(z)| ≤ U·C·2^N (|z| + N + 1)^N (2q)^{|τ|} e^{qW₊|z|} · 2|z| q |Λ|`
  with `W₊ = Σ_j log p_j`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset Complex

variable {m : ℕ} (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)

/-- `W = Σ_{j<m} log p_j`. -/
def baseLogSum : ℝ := ∑ j : Fin m, Real.log (p j.castSucc)

/-- `W₊ = Σ_j log p_j`. -/
def totalLogSum : ℝ := ∑ j, Real.log (p j)

theorem baseLogSum_nonneg (hp : ∀ j, 1 ≤ p j) : 0 ≤ baseLogSum p :=
  sum_nonneg fun j _ => Real.log_nonneg (by exact_mod_cast hp _)

theorem totalLogSum_nonneg (hp : ∀ j, 1 ≤ p j) : 0 ≤ totalLogSum p :=
  sum_nonneg fun j _ => Real.log_nonneg (by exact_mod_cast hp _)

theorem sum_add_piSingle (τ : Fin m → ℕ) (j : Fin m) :
    ∑ i, (τ + Pi.single j 1 : Fin m → ℕ) i = ∑ i, τ i + 1 := by
  classical
  simp only [Pi.add_apply, sum_add_distrib]
  congr 1
  rw [sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne hij _) (fun h => absurd (mem_univ j) h)]
  simp

/-- **Derivatives along the diagonal.** -/
theorem norm_iteratedDeriv_feldmanAux_le (hp : ∀ j, 1 ≤ p j) {N q : ℕ}
    (C : FeldmanIndex N q m → ℤ) {z : ℂ} {n : ℕ} {β : ℝ}
    (hβ : ∀ σ (τ : Fin m → ℕ), σ + ∑ j, τ j ≤ n → ‖feldmanAux p b N q C σ τ z‖ ≤ β) :
    ∀ t σ (τ : Fin m → ℕ), σ + ∑ j, τ j + t ≤ n →
      ‖iteratedDeriv t (feldmanAux p b N q C σ τ) z‖ ≤ ((n : ℝ) + baseLogSum p) ^ t * β := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) (hβ 0 0 (by simp))
  have hW := baseLogSum_nonneg p hp
  intro t
  induction t with
  | zero =>
      intro σ τ h
      simpa using hβ σ τ (by omega)
  | succ t ih =>
      intro σ τ h
      have hd := differentiable_feldmanAux p b C
      have hcd : ∀ σ' τ' (c : ℂ), ContDiffAt ℂ t (fun w => c * feldmanAux p b N q C σ' τ' w) z :=
        fun σ' τ' c => (Differentiable.contDiff ((hd σ' τ').const_mul c)).contDiffAt
      rw [iteratedDeriv_succ', deriv_feldmanAux, iteratedDeriv_fun_add (hcd _ _ _)
        (ContDiff.sum fun j _ => Differentiable.contDiff ((hd _ _).const_mul _)).contDiffAt,
        iteratedDeriv_fun_sum fun j _ => hcd _ _ _, iteratedDeriv_const_mul_field]
      simp only [iteratedDeriv_const_mul_field]
      have h1 := ih (σ + 1) τ (by omega)
      have h2 : ∀ j : Fin m, ‖iteratedDeriv t (feldmanAux p b N q C σ (τ + Pi.single j 1)) z‖ ≤
          ((n : ℝ) + baseLogSum p) ^ t * β := fun j =>
        ih σ (τ + Pi.single j 1) (by rw [sum_add_piSingle]; omega)
      have hσn : ((σ : ℝ) + 1) ≤ n := by exact_mod_cast (show σ + 1 ≤ n by omega)
      have hpow : 0 ≤ ((n : ℝ) + baseLogSum p) ^ t * β := by positivity
      calc ‖((σ : ℂ) + 1) * iteratedDeriv t (feldmanAux p b N q C (σ + 1) τ) z +
            ∑ j : Fin m, (Real.log (p j.castSucc) : ℂ) *
              iteratedDeriv t (feldmanAux p b N q C σ (τ + Pi.single j 1)) z‖
          ≤ ((σ : ℝ) + 1) * (((n : ℝ) + baseLogSum p) ^ t * β) +
              ∑ j : Fin m, Real.log (p j.castSucc) * (((n : ℝ) + baseLogSum p) ^ t * β) := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]
              refine mul_le_mul ?_ h1 (norm_nonneg _) (by positivity)
              rw [show ((σ : ℂ) + 1) = ((σ + 1 : ℕ) : ℂ) by push_cast; ring,
                Complex.norm_natCast]
              push_cast
              exact le_rfl
            · refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp _))]
              exact mul_le_mul_of_nonneg_left (h2 j) (Real.log_nonneg (by exact_mod_cast hp _))
        _ = ((σ : ℝ) + 1 + baseLogSum p) * (((n : ℝ) + baseLogSum p) ^ t * β) := by
            rw [← sum_mul, baseLogSum]
            ring
        _ ≤ ((n : ℝ) + baseLogSum p) * (((n : ℝ) + baseLogSum p) ^ t * β) :=
            mul_le_mul_of_nonneg_right (by linarith) hpow
        _ = ((n : ℝ) + baseLogSum p) ^ (t + 1) * β := by ring

/-! ## Coefficient-level bounds -/

variable {p b}

theorem abs_feldmanGamma_le (hB : 0 < b (Fin.last m)) (hb : ∀ j, |b j| ≤ b (Fin.last m))
    {q : ℕ} (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) (j : Fin m) :
    |(feldmanGamma b l j : ℝ)| ≤ 2 * q * (b (Fin.last m) : ℝ) := by
  rw [feldmanGamma]
  push_cast
  have hBr : (0 : ℝ) < b (Fin.last m) := by exact_mod_cast hB
  have hbj : |(b j.castSucc : ℝ)| ≤ b (Fin.last m) := by exact_mod_cast hb j.castSucc
  have hl1 : (l j.castSucc : ℝ) ≤ q := by exact_mod_cast (hl _).le
  have hl2 : (l (Fin.last m) : ℝ) ≤ q := by exact_mod_cast (hl _).le
  have hl1' : (0 : ℝ) ≤ l j.castSucc := Nat.cast_nonneg _
  have hl2' : (0 : ℝ) ≤ l (Fin.last m) := Nat.cast_nonneg _
  calc |(b (Fin.last m) : ℝ) * l j.castSucc - b j.castSucc * l (Fin.last m)|
      ≤ |(b (Fin.last m) : ℝ) * l j.castSucc| + |(b j.castSucc : ℝ) * l (Fin.last m)| :=
        abs_sub _ _
    _ = (b (Fin.last m) : ℝ) * l j.castSucc + |(b j.castSucc : ℝ)| * l (Fin.last m) := by
        rw [abs_mul, abs_mul, abs_of_pos hBr, abs_of_nonneg hl1', abs_of_nonneg hl2']
    _ ≤ (b (Fin.last m) : ℝ) * q + (b (Fin.last m) : ℝ) * q := by
        gcongr
    _ = 2 * q * (b (Fin.last m) : ℝ) := by ring

theorem norm_gammaWeight_le (hB : 0 < b (Fin.last m)) (hb : ∀ j, |b j| ≤ b (Fin.last m))
    {q : ℕ} (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) (τ : Fin m → ℕ) :
    ‖gammaWeight b l τ‖ ≤ (2 * q : ℝ) ^ (∑ j, τ j) := by
  rw [gammaWeight, norm_prod, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
  have hBr : (0 : ℝ) < b (Fin.last m) := by exact_mod_cast hB
  rw [norm_div, Complex.norm_intCast, Complex.norm_intCast, abs_of_pos hBr, div_le_iff₀ hBr]
  exact abs_feldmanGamma_le hB hb l hl j

theorem abs_feldmanFreq_le (hB : 0 < b (Fin.last m)) (hb : ∀ j, |b j| ≤ b (Fin.last m))
    (hp : ∀ j, 1 ≤ p j) {q : ℕ} (l : Fin (m + 1) → ℕ) (hl : ∀ i, l i < q) :
    |feldmanFreq p b l| ≤ 2 * q * baseLogSum p := by
  have hBr : (0 : ℝ) < b (Fin.last m) := by exact_mod_cast hB
  rw [feldmanFreq, baseLogSum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
  have hlog : 0 ≤ Real.log (p j.castSucc) := Real.log_nonneg (by exact_mod_cast hp _)
  rw [abs_mul, abs_div, abs_of_pos hBr, abs_of_nonneg hlog]
  refine mul_le_mul_of_nonneg_right ?_ hlog
  rw [div_le_iff₀ hBr]
  exact abs_feldmanGamma_le hB hb l hl j

theorem expo_lt {N q : ℕ} (kl : FeldmanIndex N q m) (i : Fin (m + 1)) : kl.expo i < q :=
  (kl.2 i).isLt

/-- **Growth of the auxiliary function.** -/
theorem norm_feldmanAux_le (hB : 0 < b (Fin.last m)) (hb : ∀ j, |b j| ≤ b (Fin.last m))
    (hp : ∀ j, 1 ≤ p j) {N q : ℕ} (C : FeldmanIndex N q m → ℤ) {Cmax : ℝ}
    (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (σ : ℕ) (τ : Fin m → ℕ) (w : ℂ) :
    ‖feldmanAux p b N q C σ τ w‖ ≤
      ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (‖w‖ + N + 1) ^ N) *
        (2 * q : ℝ) ^ (∑ j, τ j) * Real.exp (‖w‖ * (2 * q * baseLogSum p)) := by
  have hcard : Fintype.card (FeldmanIndex N q m) = (N + 1) * q ^ (m + 1) := by
    simp [FeldmanIndex, Fintype.card_prod, Fintype.card_pi]
  rw [feldmanAux]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ kl : FeldmanIndex N q m,
      ‖(C kl : ℂ) * feldmanJet N kl.1 σ w * gammaWeight b kl.expo τ *
          Complex.exp (w * (feldmanFreq p b kl.expo : ℂ))‖ ≤
        Cmax * (2 ^ N * (‖w‖ + N + 1) ^ N) * (2 * q : ℝ) ^ (∑ j, τ j) *
          Real.exp (‖w‖ * (2 * q * baseLogSum p)) := by
    intro kl
    rw [norm_mul, norm_mul, norm_mul]
    have hCm : 0 ≤ Cmax := (abs_nonneg _).trans (hC kl)
    have h1 : ‖((C kl : ℤ) : ℂ)‖ ≤ Cmax := by
      rw [Complex.norm_intCast]
      exact hC kl
    have h2 := norm_feldmanJet_le (Nat.lt_succ_iff.mp kl.1.isLt) σ w
    have h3 := norm_gammaWeight_le hB hb kl.expo (expo_lt kl) τ
    have h4 : ‖Complex.exp (w * (feldmanFreq p b kl.expo : ℂ))‖ ≤
        Real.exp (‖w‖ * (2 * q * baseLogSum p)) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_feldmanFreq_le hB hb hp kl.expo (expo_lt kl))
        (norm_nonneg _)
    gcongr
  refine (sum_le_sum fun kl _ => hterm kl).trans (le_of_eq ?_)
  rw [sum_const, card_univ, hcard, nsmul_eq_mul]
  ring

/-- **Distance to the true function.**  For `|z| q |Λ| ≤ 1` the difference `F − Φ` is a multiple
of `|Λ|`. -/
theorem norm_feldmanAux_sub_feldmanTrueAux_le (hB : 0 < b (Fin.last m))
    (hb : ∀ j, |b j| ≤ b (Fin.last m)) (hp : ∀ j, 1 ≤ p j) {N q : ℕ}
    (C : FeldmanIndex N q m → ℤ) {Cmax : ℝ} (hC : ∀ kl, |(C kl : ℝ)| ≤ Cmax) (σ : ℕ)
    (τ : Fin m → ℕ) {z : ℂ} (hz : ‖z‖ * q * |primeLogForm p b| ≤ 1) :
    ‖feldmanAux p b N q C σ τ z - feldmanTrueAux p b N q C σ τ z‖ ≤
      ((N + 1) * q ^ (m + 1) : ℕ) * Cmax * (2 ^ N * (‖z‖ + N + 1) ^ N) *
        (2 * q : ℝ) ^ (∑ j, τ j) * Real.exp (‖z‖ * (q * totalLogSum p)) *
          (2 * (‖z‖ * q * |primeLogForm p b|)) := by
  have hBr : (0 : ℝ) < b (Fin.last m) := by exact_mod_cast hB
  have hcard : Fintype.card (FeldmanIndex N q m) = (N + 1) * q ^ (m + 1) := by
    simp [FeldmanIndex, Fintype.card_prod, Fintype.card_pi]
  rw [feldmanAux, feldmanTrueAux, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ kl : FeldmanIndex N q m,
      ‖(C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
            Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) -
          (C kl : ℂ) * feldmanJet N kl.1 σ z * gammaWeight b kl.expo τ *
            Complex.exp (z * (trueFreq p kl.expo : ℂ))‖ ≤
        Cmax * (2 ^ N * (‖z‖ + N + 1) ^ N) * (2 * q : ℝ) ^ (∑ j, τ j) *
          Real.exp (‖z‖ * (q * totalLogSum p)) * (2 * (‖z‖ * q * |primeLogForm p b|)) := by
    intro kl
    rw [← mul_sub, norm_mul, norm_mul, norm_mul]
    have hCm : 0 ≤ Cmax := (abs_nonneg _).trans (hC kl)
    have h1 : ‖((C kl : ℤ) : ℂ)‖ ≤ Cmax := by
      rw [Complex.norm_intCast]
      exact hC kl
    have h2 := norm_feldmanJet_le (Nat.lt_succ_iff.mp kl.1.isLt) σ z
    have h3 := norm_gammaWeight_le hB hb kl.expo (expo_lt kl) τ
    have hfreq := feldmanFreq_eq p b hB.ne' kl.expo
    have hsplit : Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) -
        Complex.exp (z * (trueFreq p kl.expo : ℂ)) =
          Complex.exp (z * (trueFreq p kl.expo : ℂ)) *
            (Complex.exp (z * (-(((kl.expo (Fin.last m) : ℝ) * primeLogForm p b /
              (b (Fin.last m) : ℝ) : ℝ) : ℂ))) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add, hfreq]
      push_cast
      ring_nf
    have hlast : (kl.expo (Fin.last m) : ℝ) ≤ q := by exact_mod_cast (expo_lt kl _).le
    have hsmall : ‖z * (-(((kl.expo (Fin.last m) : ℝ) * primeLogForm p b /
        (b (Fin.last m) : ℝ) : ℝ) : ℂ))‖ ≤ ‖z‖ * q * |primeLogForm p b| := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_pos hBr, abs_of_nonneg (Nat.cast_nonneg _)]
      have hB1 : (1 : ℝ) ≤ b (Fin.last m) := by exact_mod_cast hB
      calc ‖z‖ * ((kl.expo (Fin.last m) : ℝ) * |primeLogForm p b| / (b (Fin.last m) : ℝ))
          ≤ ‖z‖ * ((q : ℝ) * |primeLogForm p b| / 1) := by
            gcongr
        _ = ‖z‖ * q * |primeLogForm p b| := by ring
    have h4 : ‖Complex.exp (z * (feldmanFreq p b kl.expo : ℂ)) -
        Complex.exp (z * (trueFreq p kl.expo : ℂ))‖ ≤
          Real.exp (‖z‖ * (q * totalLogSum p)) * (2 * (‖z‖ * q * |primeLogForm p b|)) := by
      rw [hsplit, norm_mul]
      refine mul_le_mul ?_ ((Complex.norm_exp_sub_one_le (hsmall.trans hz)).trans
        (by linarith)) (norm_nonneg _) (by positivity)
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [trueFreq, totalLogSum, mul_sum]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      have hlog : 0 ≤ Real.log (p j) := Real.log_nonneg (by exact_mod_cast hp _)
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hlog]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (expo_lt kl j).le) hlog
    rw [mul_assoc _ (Real.exp _) _]
    gcongr
  refine (sum_le_sum fun kl _ => hterm kl).trans (le_of_eq ?_)
  rw [sum_const, card_univ, hcard, nsmul_eq_mul]
  ring

end GaloisForLFunctions.RHTower.Matveev
