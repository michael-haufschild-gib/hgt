import GaloisForLFunctions.ArithmeticDefectRigidity.RankOneEscapeRowsAreTranslatedZeros
import Mathlib.LinearAlgebra.Lagrange

/-!
# Finite-rank escape rows are sums of translated-zero powers

Let `0 < ε < 1/2` and `F` a finite set of exponents on one line `Re s = σ ∈ (1/2, 1 − ε)`, with the
values `2^{−s}` distinct and the values `3^{−s}` distinct. A complex row `w` with `w(0) = 0` obeys the
*finite-rank dilation laws* if `∏_{s∈F}(I − 2^s D₂) w` and `∏_{s∈F}(I − 3^s D₃) w` have finite pronic
energy. If moreover it satisfies the renormalized inversion law, then
(`exists_finiteRank_zeroPower_decomposition`)

`w = Σ_{(s,t)∈F×F} c_{st} n^{z_{st}} + (finite energy)`, `Re z_{st} = σ`,

and every `z_{st}` with `c_{st} ≠ 0` is tied (`2^{z} = 2^s`, `3^{z} = 3^t`) and is a translated zero,
`ζ(z_{st} + ε) = 0`. In particular, if `ζ` has no zero on `Re = σ + ε`, every such row has finite
energy (`cPronicEnergy_ne_top_of_finiteRank_of_zeroFree`). Real rows are the case `F = {s, s̄}`.

The proof is algebraic over the rank-one theorems. The Lagrange basis `ℓ_s` of the nodes `2^{−s}`
gives `Σ_s ℓ_s(D₂) = I` and `(D₂ − 2^{−s}) ℓ_s(D₂) ∈ ℂ · ∏(D₂ − 2^{−u})`; with the same at `3` the
components `w_{st} = m_t(D₃) ℓ_s(D₂) w` sum to `w`, are joint approximate eigenrows of `D₂` and `D₃`
(exponents `s`, `t`), and inherit the inversion law because `S_ε` commutes with floor dilations.
-/

open Finset Polynomial Complex
open GaloisForLFunctions.BezoutValuationIncidence (pronicNorm pronicNorm_nonneg pronicNorm_sq
  pronicNorm_add_le)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Floor dilations as operators -/

/-- The floor dilation `D_p v(n) = v(⌊n/p⌋)` as a linear endomorphism of complex rows. -/
def dilOp (p : ℕ) : Module.End ℂ (ℕ → ℂ) where
  toFun v n := v (n / p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem dilOp_apply (p : ℕ) (v : ℕ → ℂ) (n : ℕ) : dilOp p v n = v (n / p) := rfl

theorem dilOp_pow_apply (p i : ℕ) (v : ℕ → ℂ) (n : ℕ) : ((dilOp p) ^ i) v n = v (n / p ^ i) := by
  induction i generalizing v with
  | zero => simp
  | succ i ih => rw [pow_succ, Module.End.mul_apply, ih, dilOp_apply, Nat.div_div_eq_div_mul,
      pow_succ]

/-- `Q(D_p) v(n) = Σ_i q_i v(⌊n/p^i⌋)`. -/
theorem aeval_dilOp_apply (p : ℕ) (Q : ℂ[X]) (v : ℕ → ℂ) (n : ℕ) :
    aeval (dilOp p) Q v n = ∑ i ∈ range (Q.natDegree + 1), Q.coeff i * v (n / p ^ i) := by
  rw [aeval_eq_sum_range, LinearMap.coe_sum, Finset.sum_apply, Finset.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, dilOp_pow_apply, smul_eq_mul]

/-- Polynomials in `D_p` and in `D_q` commute. -/
theorem aeval_dilOp_comm (p q : ℕ) (P Q : ℂ[X]) (v : ℕ → ℂ) :
    aeval (dilOp p) P (aeval (dilOp q) Q v) = aeval (dilOp q) Q (aeval (dilOp p) P v) := by
  funext n
  simp only [aeval_dilOp_apply, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm (p ^ i)]
  ring

theorem aeval_dilOp_mul_apply (p : ℕ) (P Q : ℂ[X]) (v : ℕ → ℂ) :
    aeval (dilOp p) (P * Q) v = aeval (dilOp p) P (aeval (dilOp p) Q v) := by
  rw [map_mul, Module.End.mul_apply]

theorem aeval_dilOp_euler (p : ℕ) (a : ℂ) (v : ℕ → ℂ) (n : ℕ) :
    aeval (dilOp p) (1 - C a * X) v n = v n - a * v (n / p) := by
  simp [dilOp_apply]

/-! ### Admitted rows -/

/-- Rows vanishing at `0` with finite pronic energy. -/
def Adm (v : ℕ → ℂ) : Prop := v 0 = 0 ∧ cPronicEnergy v ≠ ⊤

theorem Adm.add {u v : ℕ → ℂ} (hu : Adm u) (hv : Adm v) : Adm (u + v) := by
  refine ⟨by simp [hu.1, hv.1], ?_⟩
  obtain ⟨Bu, hBu⟩ := (pronicEnergy_ne_top_iff _).mp hu.2
  obtain ⟨Bv, hBv⟩ := (pronicEnergy_ne_top_iff _).mp hv.2
  rw [cPronicEnergy, pronicEnergy_ne_top_iff]
  refine ⟨Bu + Bv, fun T => ?_⟩
  calc pronicNorm T (fun n => ‖(u + v) n‖) ≤ pronicNorm T (fun n => ‖u n‖ + ‖v n‖) :=
        pronicNorm_le_of_abs_le_abs fun n => by
          rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)]
          exact norm_add_le _ _
    _ ≤ Bu + Bv := (pronicNorm_add_le T _ _).trans (add_le_add (hBu T) (hBv T))

theorem Adm.smul {v : ℕ → ℂ} (a : ℂ) (hv : Adm v) : Adm (a • v) := by
  refine ⟨by simp [hv.1], ?_⟩
  obtain ⟨B, hB⟩ := (pronicEnergy_ne_top_iff _).mp hv.2
  rw [cPronicEnergy, pronicEnergy_ne_top_iff]
  refine ⟨‖a‖ * B, fun T => ?_⟩
  have h : (fun n => ‖(a • v) n‖) = fun n => ‖a‖ * ‖v n‖ := funext fun n => by
    simp
  rw [h, pronicNorm_const_mul (norm_nonneg a)]
  exact mul_le_mul_of_nonneg_left (hB T) (norm_nonneg a)

theorem Adm.zero : Adm 0 := ⟨rfl, by simp [cPronicEnergy, pronicEnergy]⟩

theorem Adm.sum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℂ) (h : ∀ i ∈ s, Adm (f i)) :
    Adm (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Adm.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Adm.dil {v : ℕ → ℂ} {p : ℕ} (hp : 1 ≤ p) (hv : Adm v) : Adm (dilOp p v) := by
  refine ⟨by simp [dilOp_apply, hv.1], ?_⟩
  obtain ⟨B, hB⟩ := (pronicEnergy_ne_top_iff _).mp hv.2
  rw [cPronicEnergy, pronicEnergy_ne_top_iff]
  refine ⟨Real.sqrt (2 / (p : ℝ)) * B, fun T => ?_⟩
  have h := pronicNorm_rowDilate_le hp T (fun n => ‖v n‖) (by simp [hv.1])
  exact h.trans (mul_le_mul_of_nonneg_left (hB T) (Real.sqrt_nonneg _))

theorem Adm.polyDil {v : ℕ → ℂ} {p : ℕ} (hp : 1 ≤ p) (Q : ℂ[X]) (hv : Adm v) :
    Adm (Polynomial.aeval (dilOp p) Q v) := by
  have h : Polynomial.aeval (dilOp p) Q v = ∑ i ∈ range (Q.natDegree + 1), Q.coeff i • dilOp (p ^ i) v := by
    funext n
    rw [aeval_dilOp_apply, Finset.sum_apply]
    rfl
  rw [h]
  exact Adm.sum _ _ fun i _ => (hv.dil (Nat.one_le_pow _ _ hp)).smul _

theorem Adm.of_bounded {v : ℕ → ℂ} (hv0 : v 0 = 0) {K : ℝ} (hK : 0 ≤ K) (hv : ∀ n, ‖v n‖ ≤ K) :
    Adm v :=
  ⟨hv0, pronicEnergy_ne_top_of_abs_le hK fun n => by rw [abs_of_nonneg (norm_nonneg _)]; exact hv n⟩

end GaloisForLFunctions.ArithmeticDefectRigidity
