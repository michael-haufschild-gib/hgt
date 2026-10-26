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

/-! ### Power rows and the cofactor sum under dilation polynomials -/

/-- `‖⌊n/q⌋^a − q^{-a} n^a‖ ≤ ‖a‖ + 1` for `0 < Re a ≤ 1`. -/
theorem norm_floor_cpow_sub_le {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re ≤ 1) {q : ℕ} (hq : 1 ≤ q)
    (n : ℕ) : ‖((n / q : ℕ) : ℂ) ^ a - (q : ℂ) ^ (-a) * (n : ℂ) ^ a‖ ≤ ‖a‖ + 1 := by
  have ha : a ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha0; exact lt_irrefl 0 ha0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Complex.zero_cpow ha]
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set y : ℝ := (n : ℝ) / q
  have hy : ((y : ℝ) : ℂ) ^ a = (q : ℂ) ^ (-a) * (n : ℂ) ^ a := by
    rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hn0 hq0, Complex.ofReal_natCast,
      Complex.ofReal_natCast, mul_comm]
  rw [← hy]
  set m := n / q with hm
  have hmy : (m : ℝ) ≤ y := Nat.cast_div_le
  have hym : y < (m : ℝ) + 1 := by
    have hlt : n < q * (n / q + 1) := Nat.lt_mul_div_succ n (by omega)
    have hlt' : (n : ℝ) < (q : ℝ) * ((m : ℝ) + 1) := by rw [hm]; exact_mod_cast hlt
    rw [div_lt_iff₀ hq0]; linarith
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hm0, Nat.cast_zero, Complex.zero_cpow ha, zero_sub, norm_neg,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hn0 hq0)]
    have hy1 : y ≤ 1 := by rw [hm0, Nat.cast_zero, zero_add] at hym; exact hym.le
    have := Real.rpow_le_one (div_pos hn0 hq0).le hy1 ha0.le
    have := norm_nonneg a
    linarith
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hmv := norm_ofReal_cpow_sub_le' (z := a) ha1 (by linarith : (0 : ℝ) < m) le_rfl hmy
    rw [Complex.ofReal_natCast] at hmv
    rw [norm_sub_rev]
    have hp : (m : ℝ) ^ (a.re - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 (by linarith)
    calc ‖((y : ℝ) : ℂ) ^ a - (m : ℂ) ^ a‖ ≤ ‖a‖ * (m : ℝ) ^ (a.re - 1) * (y - m) := hmv
      _ ≤ ‖a‖ * 1 * 1 := by
          have h0 : 0 ≤ y - m := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hp (norm_nonneg _)) (by linarith) h0
            (by positivity)
      _ ≤ ‖a‖ + 1 := by linarith

/-- On `n^a` a dilation polynomial acts by its value at `p^{-a}`, up to a bounded row. -/
theorem exists_bound_aeval_cpow {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re ≤ 1) {p : ℕ} (hp : 1 ≤ p)
    (Q : ℂ[X]) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ,
      ‖Polynomial.aeval (dilOp p) Q (fun m : ℕ => (m : ℂ) ^ a) n -
        Q.eval ((p : ℂ) ^ (-a)) * (n : ℂ) ^ a‖ ≤ K := by
  refine ⟨∑ i ∈ range (Q.natDegree + 1), ‖Q.coeff i‖ * (‖a‖ + 1), by positivity, fun n => ?_⟩
  have hpow : ∀ i : ℕ, ((p : ℂ) ^ (-a)) ^ i = ((p ^ i : ℕ) : ℂ) ^ (-a) := fun i => by
    rw [← Complex.cpow_nat_mul, Nat.cast_pow, Complex.natCast_cpow_natCast_mul]
  rw [aeval_dilOp_apply, eval_eq_sum_range, sum_mul, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
  rw [hpow, mul_assoc, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_floor_cpow_sub_le ha0 ha1 (Nat.one_le_pow _ _ hp) n) (norm_nonneg _)

theorem cTotalCofactorSum_zero (ε : ℝ) (v : ℕ → ℂ) : cTotalCofactorSum ε v 0 = 0 := by
  simp [cTotalCofactorSum]

/-- `S_ε` commutes with floor dilations on rows vanishing at `0`. -/
theorem cTotalCofactorSum_dilOp (ε : ℝ) {v : ℕ → ℂ} (hv0 : v 0 = 0) (p : ℕ) (n : ℕ) :
    cTotalCofactorSum ε (dilOp p v) n = dilOp p (cTotalCofactorSum ε v) n := by
  rw [dilOp_apply, cTotalCofactorSum, cTotalCofactorSum]
  have hsub : Icc 1 (n / p) ⊆ Icc 1 n := fun j hj => by
    simp only [Finset.mem_Icc] at hj ⊢
    exact ⟨hj.1, hj.2.trans (Nat.div_le_self n p)⟩
  have hR : ∑ j ∈ Icc 1 (n / p), (((j : ℝ) ^ (-ε) : ℝ) : ℂ) * v (n / p / j) =
      ∑ j ∈ Icc 1 n, (((j : ℝ) ^ (-ε) : ℝ) : ℂ) * v (n / p / j) :=
    Finset.sum_subset hsub fun j hj hnot => by
      simp only [Finset.mem_Icc, not_and, not_le] at hj hnot
      rw [Nat.div_eq_of_lt (hnot hj.1), hv0, mul_zero]
  rw [hR]
  refine sum_congr rfl fun j _ => ?_
  rw [dilOp_apply, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm j p]

/-- `S_ε` commutes with dilation polynomials on rows vanishing at `0`. -/
theorem cTotalCofactorSum_aeval (ε : ℝ) {v : ℕ → ℂ} (hv0 : v 0 = 0) (p : ℕ) (Q : ℂ[X]) (n : ℕ) :
    cTotalCofactorSum ε (Polynomial.aeval (dilOp p) Q v) n =
      Polynomial.aeval (dilOp p) Q (cTotalCofactorSum ε v) n := by
  rw [aeval_dilOp_apply]
  have h : ∀ i : ℕ, Q.coeff i * cTotalCofactorSum ε v (n / p ^ i) =
      Q.coeff i * cTotalCofactorSum ε (dilOp (p ^ i) v) n := fun i => by
    rw [cTotalCofactorSum_dilOp ε hv0, dilOp_apply]
  simp_rw [h]
  simp only [cTotalCofactorSum, aeval_dilOp_apply, mul_sum, dilOp_apply]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  ring

/-- **The inversion law passes to dilation-polynomial images.** -/
theorem adm_cofactor_aeval {ε : ℝ} {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re ≤ 1) {v : ℕ → ℂ}
    (hv0 : v 0 = 0) {c' : ℂ} (hlaw : Adm fun n => cTotalCofactorSum ε v n - c' * (n : ℂ) ^ a)
    {p : ℕ} (hp : 1 ≤ p) (Q : ℂ[X]) :
    Adm fun n => cTotalCofactorSum ε (Polynomial.aeval (dilOp p) Q v) n -
      (c' * Q.eval ((p : ℂ) ^ (-a))) * (n : ℂ) ^ a := by
  have ha : a ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha0; exact lt_irrefl 0 ha0
  obtain ⟨K, hK0, hK⟩ := exists_bound_aeval_cpow ha0 ha1 hp Q
  set r' : ℕ → ℂ := fun n => cTotalCofactorSum ε v n - c' * (n : ℂ) ^ a with hr'
  set b : ℕ → ℂ := fun n => Polynomial.aeval (dilOp p) Q (fun m : ℕ => (m : ℂ) ^ a) n -
    Q.eval ((p : ℂ) ^ (-a)) * (n : ℂ) ^ a with hb
  have hb0 : b 0 = 0 := by
    simp only [hb, aeval_dilOp_apply, Nat.zero_div, Nat.cast_zero, Complex.zero_cpow ha, mul_zero,
      Finset.sum_const_zero, sub_zero]
  have hbA : Adm b := Adm.of_bounded hb0 hK0 hK
  have hS : cTotalCofactorSum ε v = fun n : ℕ => c' * (n : ℂ) ^ a + r' n := by
    funext n; simp only [hr']; ring
  have hlin : Polynomial.aeval (dilOp p) Q (cTotalCofactorSum ε v) =
      c' • Polynomial.aeval (dilOp p) Q (fun m : ℕ => (m : ℂ) ^ a) +
        Polynomial.aeval (dilOp p) Q r' := by
    rw [hS, show (fun n : ℕ => c' * (n : ℂ) ^ a + r' n) =
      c' • (fun m : ℕ => (m : ℂ) ^ a) + r' from funext fun n => by simp, map_add, map_smul]
  have hrow : (fun n => cTotalCofactorSum ε (Polynomial.aeval (dilOp p) Q v) n -
      (c' * Q.eval ((p : ℂ) ^ (-a))) * (n : ℂ) ^ a) = c' • b + Polynomial.aeval (dilOp p) Q r' := by
    funext n
    rw [cTotalCofactorSum_aeval ε hv0, hlin]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb]
    ring
  rw [hrow]
  exact (hbA.smul c').add (hlaw.polyDil hp Q)

/-! ### Lagrange projectors -/

theorem aeval_dilOp_apply_zero {p : ℕ} (Q : ℂ[X]) {v : ℕ → ℂ} (hv0 : v 0 = 0) :
    Polynomial.aeval (dilOp p) Q v 0 = 0 := by
  simp [aeval_dilOp_apply, hv0]

theorem natCast_cpow_ne_zero {p : ℕ} (hp : p ≠ 0) (s : ℂ) : (p : ℂ) ^ s ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp)]
  exact Complex.exp_ne_zero _

/-- `1 − aX = (−a)(X − a⁻¹)`. -/
theorem one_sub_C_mul_X_eq {a : ℂ} (ha : a ≠ 0) :
    (1 - C a * X : ℂ[X]) = C (-a) * (X - C a⁻¹) := by
  rw [mul_sub, ← C_mul, show -a * a⁻¹ = -1 by field_simp, C_neg, C_neg, C_1]
  ring

/-- The Euler-factor product is a nonzero multiple of the nodal polynomial at `p^{−s}`. -/
theorem prod_euler_eq_C_mul_nodal {p : ℕ} (hp : p ≠ 0) (F : Finset ℂ) :
    (∏ s ∈ F, (1 - C ((p : ℂ) ^ s) * X)) =
      C (∏ s ∈ F, -((p : ℂ) ^ s)) * Lagrange.nodal F (fun s => (p : ℂ) ^ (-s)) := by
  rw [Lagrange.nodal, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [one_sub_C_mul_X_eq (natCast_cpow_ne_zero hp s), Complex.cpow_neg]

/-- `(X − v_s) ℓ_s = w_s · nodal`. -/
theorem X_sub_C_mul_basis {F : Finset ℂ} {v : ℂ → ℂ} {s : ℂ} (hs : s ∈ F) :
    (X - C (v s)) * Lagrange.basis F v s = C (Lagrange.nodalWeight F v s) * Lagrange.nodal F v := by
  classical
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hs, ← Lagrange.nodal_erase_eq_nodal_div hs,
    Lagrange.nodal_eq_mul_nodal_erase hs]
  ring

/-- The `s`-component satisfies the single Euler law at `s`: `(1 − p^s X) ℓ_s ∈ ℂ · nodal`. -/
theorem euler_mul_basis {p : ℕ} (hp : p ≠ 0) {F : Finset ℂ} {s : ℂ} (hs : s ∈ F) :
    (1 - C ((p : ℂ) ^ s) * X) * Lagrange.basis F (fun u => (p : ℂ) ^ (-u)) s =
      C (-((p : ℂ) ^ s) * Lagrange.nodalWeight F (fun u => (p : ℂ) ^ (-u)) s) *
        Lagrange.nodal F (fun u => (p : ℂ) ^ (-u)) := by
  rw [one_sub_C_mul_X_eq (natCast_cpow_ne_zero hp s), mul_assoc, ← Complex.cpow_neg,
    X_sub_C_mul_basis (v := fun u => (p : ℂ) ^ (-u)) hs, ← mul_assoc, ← C_mul]

theorem cEulerLaw_eq_aeval (p : ℕ) (s : ℂ) (v : ℕ → ℂ) :
    cEulerLaw p s v = Polynomial.aeval (dilOp p) (1 - C ((p : ℂ) ^ s) * X) v := by
  funext n
  rw [aeval_dilOp_euler, cEulerLaw]

/-- The law at `p` for the component of `w` along `s` is a multiple of the nodal law of `w`. -/
theorem adm_euler_component {p : ℕ} (hp : 1 ≤ p) {F : Finset ℂ} {s : ℂ} (hs : s ∈ F)
    {w : ℕ → ℂ} (hN : Adm (Polynomial.aeval (dilOp p) (Lagrange.nodal F fun u => (p : ℂ) ^ (-u)) w)) :
    Adm (cEulerLaw p s (Polynomial.aeval (dilOp p)
      (Lagrange.basis F (fun u => (p : ℂ) ^ (-u)) s) w)) := by
  rw [cEulerLaw_eq_aeval, ← aeval_dilOp_mul_apply, euler_mul_basis (by omega) hs,
    aeval_dilOp_mul_apply, aeval_C]
  exact hN.smul _

/-! ### The decomposition -/

/-- **Finite-rank escape rows are sums of translated-zero powers.** -/
theorem exists_finiteRank_zeroPower_decomposition {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1 - ε) (F : Finset ℂ) (hFre : ∀ s ∈ F, s.re = σ)
    (h2inj : Set.InjOn (fun s : ℂ => (2 : ℂ) ^ (-s)) F)
    (h3inj : Set.InjOn (fun s : ℂ => (3 : ℂ) ^ (-s)) F) {w : ℕ → ℂ} (hw0 : w 0 = 0)
    (h2 : cPronicEnergy (Polynomial.aeval (dilOp 2) (∏ s ∈ F, (1 - C ((2 : ℂ) ^ s) * X)) w) ≠ ⊤)
    (h3 : cPronicEnergy (Polynomial.aeval (dilOp 3) (∏ s ∈ F, (1 - C ((3 : ℂ) ^ s) * X)) w) ≠ ⊤)
    {c' : ℂ}
    (hlaw : cPronicEnergy (fun n => cTotalCofactorSum ε w n - c' * (n : ℂ) ^ ((1 - ε : ℝ) : ℂ)) ≠ ⊤) :
    ∃ c z : ℂ × ℂ → ℂ, (∀ st ∈ F ×ˢ F, (z st).re = σ ∧ (c st ≠ 0 →
        (2 : ℂ) ^ z st = 2 ^ st.1 ∧ (3 : ℂ) ^ z st = 3 ^ st.2 ∧ riemannZeta (z st + ε) = 0)) ∧
      cPronicEnergy (fun n => w n - ∑ st ∈ F ×ˢ F, c st * (n : ℂ) ^ z st) ≠ ⊤ := by
  classical
  rcases F.eq_empty_or_nonempty with hF | hF
  · subst hF
    refine ⟨fun _ => 0, fun _ => 0, by simp, ?_⟩
    simp only [Finset.prod_empty, map_one, Module.End.one_apply] at h2
    simpa using h2
  set a : ℂ := ((1 - ε : ℝ) : ℂ) with hadef
  have ha0 : 0 < a.re := by simp [hadef]; linarith
  have ha1 : a.re ≤ 1 := by simp [hadef]; linarith
  set v₂ : ℂ → ℂ := fun u => (2 : ℂ) ^ (-u)
  set v₃ : ℂ → ℂ := fun u => (3 : ℂ) ^ (-u)
  -- the nodal laws of `w`
  have hN : ∀ {p : ℕ}, 1 ≤ p →
      cPronicEnergy (Polynomial.aeval (dilOp p) (∏ s ∈ F, (1 - C ((p : ℂ) ^ s) * X)) w) ≠ ⊤ →
        Adm (Polynomial.aeval (dilOp p) (Lagrange.nodal F fun u => (p : ℂ) ^ (-u)) w) := by
    intro p hp h
    have hk : (∏ s ∈ F, -((p : ℂ) ^ s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun s _ => neg_ne_zero.mpr (natCast_cpow_ne_zero (by omega) s)
    have hA : Adm (Polynomial.aeval (dilOp p) (∏ s ∈ F, (1 - C ((p : ℂ) ^ s) * X)) w) :=
      ⟨aeval_dilOp_apply_zero _ hw0, h⟩
    rw [prod_euler_eq_C_mul_nodal (by omega), aeval_dilOp_mul_apply, aeval_C] at hA
    have := hA.smul (∏ s ∈ F, -((p : ℂ) ^ s))⁻¹
    rwa [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, smul_smul,
      inv_mul_cancel₀ hk, one_smul] at this
  have hN2 := hN (p := 2) (by norm_num) (by exact_mod_cast h2)
  have hN3 := hN (p := 3) (by norm_num) (by exact_mod_cast h3)
  -- the components
  set W : ℂ × ℂ → ℕ → ℂ := fun st => Polynomial.aeval (dilOp 3) (Lagrange.basis F v₃ st.2)
    (Polynomial.aeval (dilOp 2) (Lagrange.basis F v₂ st.1) w) with hWdef
  have hsum : (∑ st ∈ F ×ˢ F, W st) = w := by
    rw [Finset.sum_product]
    have hinner : ∀ s, ∑ t ∈ F, W (s, t) = Polynomial.aeval (dilOp 2) (Lagrange.basis F v₂ s) w := by
      intro s
      simp only [hWdef]
      rw [← LinearMap.sum_apply, ← map_sum, Lagrange.sum_basis h3inj hF, map_one,
        Module.End.one_apply]
    simp_rw [hinner]
    rw [← LinearMap.sum_apply, ← map_sum, Lagrange.sum_basis h2inj hF, map_one,
      Module.End.one_apply]
  have hW0 : ∀ st, W st 0 = 0 := fun st =>
    aeval_dilOp_apply_zero _ (aeval_dilOp_apply_zero _ hw0)
  have hlawA : Adm fun n => cTotalCofactorSum ε w n - c' * (n : ℂ) ^ a :=
    ⟨by
      have ha : a ≠ 0 := fun h => by rw [h, Complex.zero_re] at ha0; exact lt_irrefl 0 ha0
      simp [cTotalCofactorSum, Complex.zero_cpow ha], hlaw⟩
  have hcomp : ∀ st : ℂ × ℂ, ∃ c z : ℂ, st ∈ F ×ˢ F →
      ((z.re = σ ∧ (c ≠ 0 → (2 : ℂ) ^ z = 2 ^ st.1 ∧ (3 : ℂ) ^ z = 3 ^ st.2 ∧
        riemannZeta (z + ε) = 0)) ∧ cPronicEnergy (fun n => W st n - c * (n : ℂ) ^ z) ≠ ⊤) := by
    intro st
    by_cases hst : st ∈ F ×ˢ F
    swap
    · exact ⟨0, 0, fun h => absurd h hst⟩
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
    -- the two single laws of the component
    have hL2 : Adm (cEulerLaw 2 st.1 (W st)) := by
      have h := (adm_euler_component (p := 2) (by norm_num) hs hN2).polyDil (p := 3) (by norm_num)
        (Lagrange.basis F v₃ st.2)
      rw [cEulerLaw_eq_aeval] at h ⊢
      simp only [hWdef]
      rw [aeval_dilOp_comm 2 3]
      exact h
    have hL3 : Adm (cEulerLaw 3 st.2 (W st)) := by
      have h := (adm_euler_component (p := 3) (by norm_num) ht hN3).polyDil (p := 2) (by norm_num)
        (Lagrange.basis F v₂ st.1)
      have hWc : W st = Polynomial.aeval (dilOp 2) (Lagrange.basis F v₂ st.1)
          (Polynomial.aeval (dilOp 3) (Lagrange.basis F v₃ st.2) w) := by
        simp only [hWdef]; rw [aeval_dilOp_comm 3 2]
      rw [cEulerLaw_eq_aeval] at h ⊢
      rw [hWc, aeval_dilOp_comm 3 2]
      exact h
    have hre : st.1.re = st.2.re := by rw [hFre _ hs, hFre _ ht]
    have h12 : 1 / 2 < st.1.re := by rw [hFre _ hs]; exact hσ
    have h1 : st.1.re ≤ 1 := by rw [hFre _ hs]; linarith
    obtain ⟨c, z, hzre, htied, hfin⟩ :=
      exists_cPronicEnergy_sub_cpow_ne_top hre h12 h1 (hW0 st) hL2.2 hL3.2
    refine ⟨c, z, fun _ => ⟨⟨by rw [hzre, hFre _ hs], fun hc => ?_⟩, hfin⟩⟩
    obtain ⟨t2, t3⟩ := htied hc
    refine ⟨t2, t3, ?_⟩
    -- the inversion law of the component
    have hI := adm_cofactor_aeval ha0 ha1 (aeval_dilOp_apply_zero _ hw0)
      (adm_cofactor_aeval ha0 ha1 hw0 hlawA (p := 2) (by norm_num) (Lagrange.basis F v₂ st.1))
      (p := 3) (by norm_num) (Lagrange.basis F v₃ st.2)
    have hzre' : z.re = σ := by rw [hzre, hFre _ hs]
    have hz0 : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzre'; linarith
    have hzα : z ≠ ((1 - ε : ℝ) : ℂ) := fun h => by
      have := congrArg Complex.re h; rw [hzre'] at this; simp at this; linarith
    set r : ℕ → ℂ := fun n => W st n - c * (n : ℂ) ^ z with hrdef
    set c'' := c' * (Lagrange.basis F v₂ st.1).eval ((2 : ℂ) ^ (-a)) *
      (Lagrange.basis F v₃ st.2).eval ((3 : ℂ) ^ (-a))
    set r' : ℕ → ℂ := fun n => cTotalCofactorSum ε (W st) n - c'' * (n : ℂ) ^ a with hr'def
    have hr0 : r 0 = 0 := by simp [hrdef, hW0 st, Complex.zero_cpow hz0]
    have hr'A : Adm r' := by
      simp only [hr'def, hWdef]
      exact hI
    refine riemannZeta_add_eq_zero_of_powerLike_solution hε0 hε {z}
      (fun u hu => by
        rw [Finset.mem_singleton] at hu; subst hu
        exact ⟨by rw [hzre']; exact hσ, by rw [hzre']; linarith, hzα⟩)
      (fun _ => c) hr0 (energyBounded_of_cPronicEnergy_ne_top hfin) hr'A.1
      (energyBounded_of_cPronicEnergy_ne_top hr'A.2) c'' ?_ z (Finset.mem_singleton_self z) hc
    intro n
    have hfun : (fun m : ℕ => ∑ u ∈ ({z} : Finset ℂ), (fun _ => c) u * ((m : ℝ) : ℂ) ^ u + r m) =
        W st := by
      funext m
      simp only [Finset.sum_singleton, hrdef, Complex.ofReal_natCast]
      ring
    rw [hfun]
    simp only [hr'def, hadef, Complex.ofReal_natCast]
    ring
  choose c z hcz using hcomp
  refine ⟨c, z, fun st hst => (hcz st hst).1, ?_⟩
  have hdiff : (fun n => w n - ∑ st ∈ F ×ˢ F, c st * (n : ℂ) ^ z st) =
      ∑ st ∈ F ×ˢ F, fun n => W st n - c st * (n : ℂ) ^ z st := by
    funext n
    rw [Finset.sum_apply, Finset.sum_sub_distrib]
    congr 1
    conv_lhs => rw [← hsum]
    rw [Finset.sum_apply]
  rw [hdiff]
  refine (Adm.sum _ _ fun st hst => ⟨?_, (hcz st hst).2⟩).2
  have hzre' : (z st).re = σ := (hcz st hst).1.1
  have hz0 : z st ≠ 0 := fun h => by rw [h, Complex.zero_re] at hzre'; linarith
  simp [hW0 st, Complex.zero_cpow hz0]

/-- **A zero-free line admits no finite-rank escape row.** If `ζ` does not vanish on
`Re = σ + ε`, every row obeying the finite-rank dilation laws on that line and the inversion law has
finite pronic energy. -/
theorem cPronicEnergy_ne_top_of_finiteRank_of_zeroFree {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1 - ε) (F : Finset ℂ) (hFre : ∀ s ∈ F, s.re = σ)
    (h2inj : Set.InjOn (fun s : ℂ => (2 : ℂ) ^ (-s)) F)
    (h3inj : Set.InjOn (fun s : ℂ => (3 : ℂ) ^ (-s)) F) {w : ℕ → ℂ} (hw0 : w 0 = 0)
    (h2 : cPronicEnergy (Polynomial.aeval (dilOp 2) (∏ s ∈ F, (1 - C ((2 : ℂ) ^ s) * X)) w) ≠ ⊤)
    (h3 : cPronicEnergy (Polynomial.aeval (dilOp 3) (∏ s ∈ F, (1 - C ((3 : ℂ) ^ s) * X)) w) ≠ ⊤)
    {c' : ℂ}
    (hlaw : cPronicEnergy (fun n => cTotalCofactorSum ε w n - c' * (n : ℂ) ^ ((1 - ε : ℝ) : ℂ)) ≠ ⊤)
    (hzf : ∀ z : ℂ, z.re = σ → riemannZeta (z + ε) ≠ 0) : cPronicEnergy w ≠ ⊤ := by
  obtain ⟨c, z, hcz, hfin⟩ := exists_finiteRank_zeroPower_decomposition hε0 hε hσ hσ1 F hFre
    h2inj h3inj hw0 h2 h3 hlaw
  have hc : ∀ st ∈ F ×ˢ F, c st = 0 := fun st hst => by
    by_contra hne
    exact hzf (z st) (hcz st hst).1 ((hcz st hst).2 hne).2.2
  have hzero : (fun n => w n - ∑ st ∈ F ×ˢ F, c st * (n : ℂ) ^ z st) = w := by
    funext n
    rw [Finset.sum_eq_zero fun st hst => by rw [hc st hst, zero_mul], sub_zero]
  rwa [hzero] at hfin

end GaloisForLFunctions.ArithmeticDefectRigidity
