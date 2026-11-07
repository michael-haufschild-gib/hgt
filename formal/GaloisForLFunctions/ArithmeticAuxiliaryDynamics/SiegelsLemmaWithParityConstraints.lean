import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheParityBalanceOfAProducer
import Mathlib.NumberTheory.SiegelsLemma

/-!
# Siegel's lemma with parity constraints

Siegel's lemma produces, on the letters `(B, K]`, a nonzero integer stencil of controlled height
satisfying any fewer than `K − B` integer linear constraints. With balance and parity balance as the two
constraints, cleared by `K!`, the height is at most `((K − B) K!)^{2/(K − B − 2)}`: polynomial in `K` when
`B ≤ K/2`.

This is everything Siegel can give, and it does not make a producer:

* **Rigidity.** Two stencils with the same multiplicity on `[1, B]` have the same letters in `[1, B]`, so
  the multiplicity on a window has no free parameter below the window. Only letters above it are free.
* **Siegel stencils are not producers.** A stencil with no letter `1` has multiplicity `0` at `r = 1`.
* Siegel imposes equalities. The producer condition `g ≥ 0` is an inequality on a whole period, and integrality
  is free by the exact clearing of rational weights. So the existence problem for producers is a real
  linear program, with parity neutrality settled by an explicit Hecke construction, not by counting.
-/

open Finset Matrix
open GaloisForLFunctions.ArithmeticKreinLangerTheory

attribute [local instance] Matrix.seminormedAddCommGroup

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

local notation "lam" => ArithmeticFunction.liouville

/-- **Siegel's lemma for stencils.** Fewer than `K − B` integer constraints of height at most `H` have a
nonzero solution on the letters `(B, K]` of height at most `((K − B) H)^{m/(K − B − m)}`. -/
theorem exists_stencil_of_constraints {B K : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → ℕ → ℤ)
    {H : ℝ} (hH : 1 ≤ H) (hA : ∀ i, ∀ k ∈ Ioc B K, |(A i k : ℝ)| ≤ H)
    (hlt : Fintype.card ι < K - B) :
    ∃ c : ℕ →₀ ℤ, c ≠ 0 ∧ c.support ⊆ Ioc B K ∧ (∀ i, ∑ k ∈ Ioc B K, c k * A i k = 0) ∧
      ∀ k, |(c k : ℝ)| ≤ (((K - B : ℕ) : ℝ) * H) ^
        ((Fintype.card ι : ℝ) / (((K - B : ℕ) : ℝ) - Fintype.card ι)) := by
  classical
  set M : Matrix ι (Ioc B K) ℤ := Matrix.of fun i k => A i k with hM
  have hcard : Fintype.card (Ioc B K) = K - B := by
    rw [Fintype.card_coe, Nat.card_Ioc]
  have hm : 0 < Fintype.card ι := Fintype.card_pos
  obtain ⟨t, ht0, htM, htn⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le M
    (by rw [hcard]; exact hlt) hm
  rw [hcard] at htn
  have hMnorm : ‖M‖ ≤ H := by
    refine (Matrix.norm_le_iff (by linarith)).mpr fun i k => ?_
    simp only [hM, Matrix.of_apply, Int.norm_eq_abs]
    exact hA i k k.2
  have hmax : max 1 ‖M‖ ≤ H := max_le hH hMnorm
  have hnm : ((Fintype.card ι : ℕ) : ℝ) < ((K - B : ℕ) : ℝ) := by exact_mod_cast hlt
  have hexp : 0 ≤ (Fintype.card ι : ℝ) / (((K - B : ℕ) : ℝ) - Fintype.card ι) :=
    div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hbase : ((K - B : ℕ) : ℝ) * max 1 ‖M‖ ≤ ((K - B : ℕ) : ℝ) * H :=
    mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg _)
  have hpow := Real.rpow_le_rpow (by positivity) hbase hexp
  set c : ℕ →₀ ℤ := Finsupp.onFinset (Ioc B K)
    (fun k => if h : k ∈ Ioc B K then t ⟨k, h⟩ else 0) (fun k hk => by
      by_contra hnot
      simp [hnot] at hk) with hc
  have hval : ∀ k : Ioc B K, c k = t k := by
    intro k
    simp [hc]
  have hout : ∀ k, k ∉ Ioc B K → c k = 0 := by
    intro k hk
    simp [hc, hk]
  refine ⟨c, ?_, ?_, fun i => ?_, fun k => ?_⟩
  · intro h0
    apply ht0
    funext k
    rw [← hval k, h0]
    rfl
  · exact Finsupp.support_onFinset_subset
  · have hrow := congrFun htM i
    rw [Matrix.mulVec, dotProduct] at hrow
    rw [← Finset.sum_coe_sort (Ioc B K) (fun k => c k * A i k)]
    rw [Pi.zero_apply] at hrow
    rw [← hrow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hval k]
    simp only [hM, Matrix.of_apply]
    ring
  · by_cases hk : k ∈ Ioc B K
    · have h1 : |(c k : ℝ)| ≤ ‖t‖ := by
        rw [hval ⟨k, hk⟩]
        have := norm_le_pi_norm t ⟨k, hk⟩
        rwa [Int.norm_eq_abs] at this
      exact h1.trans (htn.trans hpow)
    · rw [hout k hk]
      simp only [Int.cast_zero, abs_zero]
      exact Real.rpow_nonneg (by positivity) _

/-- **Siegel's lemma with parity constraints.** On `(B, K]`, with at least three letters, there is a
nonzero integer stencil with balance and parity balance `0`, of height at most
`((K − B) K!)^{2/(K − B − 2)}`, and multiplicity `0` on `[0, B]`. -/
theorem exists_parity_stencil {B K : ℕ} (hBK : B + 2 < K) :
    ∃ c : ℕ →₀ ℤ, c ≠ 0 ∧ c.support ⊆ Ioc B K ∧ IsBalanced c ∧ parityBalance c = 0 ∧
      (∀ k, |(c k : ℝ)| ≤ (((K - B : ℕ) : ℝ) * (K.factorial : ℝ)) ^
        ((2 : ℝ) / (((K - B : ℕ) : ℝ) - 2))) ∧ ∀ r, r ≤ B → stepWeight c r = 0 := by
  classical
  set A : Fin 2 → ℕ → ℤ := fun i k =>
    (if i = 0 then 1 else lam k) * ((K.factorial / k : ℕ) : ℤ) with hA
  have hF : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.factorial_pos K
  have hdiv : ∀ k ∈ Ioc B K, (((K.factorial / k : ℕ) : ℝ)) = (K.factorial : ℝ) / k := by
    intro k hk
    have hk' := mem_Ioc.mp hk
    have hk0 : 0 < k := by omega
    exact Nat.cast_div (Nat.dvd_factorial hk0 hk'.2) (Nat.cast_ne_zero.mpr hk0.ne')
  have hlam : ∀ k, k ≠ 0 → |((lam k : ℤ) : ℝ)| = 1 := by
    intro k hk
    rw [ArithmeticFunction.liouville_apply hk]
    rcases neg_one_pow_eq_or ℤ (ArithmeticFunction.cardFactors k) with h | h <;> rw [h] <;> simp
  have hbound : ∀ i, ∀ k ∈ Ioc B K, |(A i k : ℝ)| ≤ (K.factorial : ℝ) := by
    intro i k hk
    have hk' := mem_Ioc.mp hk
    have hk0 : k ≠ 0 := by omega
    have hle : (((K.factorial / k : ℕ) : ℝ)) ≤ K.factorial := by
      exact_mod_cast Nat.div_le_self _ _
    simp only [hA]
    push_cast
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (K.factorial / k))]
    by_cases hi : i = 0
    · simp only [hi, if_true, Int.cast_one, abs_one, one_mul]
      exact hle
    · simp only [hi, if_false]
      rw [hlam k hk0, one_mul]
      exact hle
  have hlt : Fintype.card (Fin 2) < K - B := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨c, hc0, hsupp, hcons, hheight⟩ := exists_stencil_of_constraints A hF hbound hlt
  rw [Fintype.card_fin] at hheight
  have hFne : (K.factorial : ℝ) ≠ 0 := by linarith
  -- Dividing a cleared constraint by `K!`.
  have hclear : ∀ (w : ℕ → ℝ), ∑ k ∈ Ioc B K, (c k : ℝ) * w k * ((K.factorial / k : ℕ) : ℝ) = 0 →
      ∑ k ∈ c.support, (c k : ℝ) * w k / k = 0 := by
    intro w h
    have h1 : ∑ k ∈ c.support, (c k : ℝ) * w k / k = ∑ k ∈ Ioc B K, (c k : ℝ) * w k / k :=
      sum_subset hsupp fun k _ hk => by
        rw [Finsupp.notMem_support_iff.mp hk]
        simp
    rw [h1]
    have h2 : (K.factorial : ℝ) * ∑ k ∈ Ioc B K, (c k : ℝ) * w k / k = 0 := by
      rw [mul_sum, ← h]
      refine sum_congr rfl fun k hk => ?_
      rw [hdiv k hk]
      ring
    exact (mul_eq_zero.mp h2).resolve_left hFne
  refine ⟨c, hc0, hsupp, ?_, ?_, ?_, fun r hr => ?_⟩
  · have h := hclear (fun _ => 1) (by
      have h0 := hcons 0
      have hR : ((∑ k ∈ Ioc B K, c k * A 0 k : ℤ) : ℝ) = 0 := by rw [h0]; simp
      rw [← hR]
      push_cast
      refine sum_congr rfl fun k _ => ?_
      simp [hA])
    simpa [IsBalanced] using h
  · have h := hclear (fun k => (lam k : ℝ)) (by
      have h0 := hcons 1
      have hR : ((∑ k ∈ Ioc B K, c k * A 1 k : ℤ) : ℝ) = 0 := by rw [h0]; simp
      rw [← hR]
      push_cast
      refine sum_congr rfl fun k _ => ?_
      simp [hA])
    exact h
  · intro k
    have h := hheight k
    have hcast : (((2 : ℕ) : ℝ)) = 2 := by norm_num
    rwa [hcast] at h
  · rw [stepWeight]
    refine sum_eq_zero fun k hk => ?_
    have hk' := mem_Ioc.mp (hsupp hk)
    rw [Nat.div_eq_of_lt (by omega)]
    simp

/-- **Rigidity on a window.** Stencils with the same multiplicity on `[1, B]` have the same letters in
`[1, B]`. The multiplicity on a window leaves no free parameter below the window. -/
theorem coeff_eq_of_stepWeight_eq {c d : ℕ →₀ ℤ} {B : ℕ} (hc0 : c 0 = 0) (hd0 : d 0 = 0)
    (h : ∀ r, r ≤ B → stepWeight c r = stepWeight d r) {k : ℕ} (hk : k ≤ B) : c k = d k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hc0, hd0]
  rw [coeff_eq_moebius_increment c hk0, coeff_eq_moebius_increment d hk0]
  refine sum_congr rfl fun x hx => ?_
  have hx' := Nat.mem_divisorsAntidiagonal.mp hx
  have hx2 : 0 < x.2 := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hx'
    exact hx'.2 hx'.1.symm
  have hx2le : x.2 ≤ k := Nat.le_of_dvd hk0 ⟨x.1, by rw [mul_comm]; exact hx'.1.symm⟩
  obtain ⟨y, hy⟩ : ∃ y, x.2 = y + 1 := ⟨x.2 - 1, by omega⟩
  have h1 := stepWeight_succ c y
  have h2 := stepWeight_succ d y
  have h3 := h (y + 1) (by omega)
  have h4 := h y (by omega)
  have hinc : increment c x.2 = increment d x.2 := by
    rw [hy]
    linarith
  rw [hinc]

/-- **A Siegel stencil is never a producer.** A stencil with no letter `1` has multiplicity `0` at
`r = 1`. -/
theorem not_isProducer_of_support {c : ℕ →₀ ℤ} {B K : ℕ} (hB : 1 ≤ B) (hsupp : c.support ⊆ Ioc B K)
    (m B' : ℕ) : ¬ IsProducer c m B' := by
  intro hP
  have h1 : c 1 = 0 := by
    by_contra h
    have := mem_Ioc.mp (hsupp (Finsupp.mem_support_iff.mpr h))
    omega
  have h2 := hP.le_coeff_one
  rw [h1] at h2
  have h3 : (1 : ℤ) ≤ m := by exact_mod_cast hP.one_le_m
  omega

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
