import Mathlib

/-!
# Coefficient mass of complex polynomials: products, Lagrange nodes, heat comparison

`coeffMass P = Σ_k |p_k|` is submultiplicative (`coeffMass_mul_le`).  A polynomial of degree `≤ d`
is controlled by its values at `d + 1` nodes of modulus `≤ R` and mutual distance `≥ h`
(`coeffMass_le_of_nodes`):
`coeffMass Q ≤ ((1 + R)/h)^d Σ_k |Q(t_k)|`.

For the heat weight, `Re(e^{-s} Q(s) \overline{Q(\bar s)})` differs from
`e^{-σ}|Q(σ)|²` (`σ = Re s`) by at most `(1 + 2d) |Im s| e^{-σ} coeffMass(Q)² (1 + 2|s|)^{2d}`
(`re_exp_mul_eval_mul_conj_ge`).
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The coefficient mass `Σ_k |p_k|`. -/
def coeffMass (P : ℂ[X]) : ℝ := P.sum fun _ c => ‖c‖

theorem coeffMass_eq_sum_range (P : ℂ[X]) {N : ℕ} (hN : P.natDegree < N) :
    coeffMass P = ∑ k ∈ Finset.range N, ‖P.coeff k‖ :=
  Polynomial.sum_over_range' _ (fun _ => norm_zero) N hN

theorem coeffMass_nonneg (P : ℂ[X]) : 0 ≤ coeffMass P := by
  rw [coeffMass, Polynomial.sum_def]
  exact Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem coeffMass_add_le (P R : ℂ[X]) : coeffMass (P + R) ≤ coeffMass P + coeffMass R := by
  set N := max P.natDegree R.natDegree + 1
  have hP : P.natDegree < N := by omega
  have hR : R.natDegree < N := by omega
  have hPR : (P + R).natDegree < N := lt_of_le_of_lt (natDegree_add_le _ _) (by omega)
  rw [coeffMass_eq_sum_range _ hP, coeffMass_eq_sum_range _ hR, coeffMass_eq_sum_range _ hPR,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => by rw [coeff_add]; exact norm_add_le _ _

theorem coeffMass_zero : coeffMass 0 = 0 := by simp [coeffMass]

theorem coeffMass_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    coeffMass (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffMass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffMass_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (coeffMass_add_le _ _).trans (by linarith)

theorem coeffMass_C_mul (c : ℂ) (P : ℂ[X]) : coeffMass (C c * P) = ‖c‖ * coeffMass P := by
  have hN : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self _
  have hN' : (C c * P).natDegree < P.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_C_mul_le c P) hN
  rw [coeffMass_eq_sum_range _ hN, coeffMass_eq_sum_range _ hN', Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [coeff_C_mul, norm_mul]

theorem coeffMass_monomial_mul (i : ℕ) (c : ℂ) (R : ℂ[X]) :
    coeffMass (monomial i c * R) = ‖c‖ * coeffMass R := by
  set M := R.natDegree + 1 with hM
  have hR : R.natDegree < M := Nat.lt_succ_self _
  have hdeg : (monomial i c * R).natDegree < i + M :=
    lt_of_le_of_lt (natDegree_mul_le.trans (add_le_add (natDegree_monomial_le c) le_rfl))
      (by omega)
  rw [coeffMass_eq_sum_range _ hdeg, coeffMass_eq_sum_range _ hR, Finset.sum_range_add,
    Finset.mul_sum]
  have h1 : ∑ x ∈ Finset.range i, ‖(monomial i c * R).coeff x‖ = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxi : ¬ i ≤ x := by simp at hx; omega
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg hxi, mul_zero,
      norm_zero]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show i + x = x + i by ring, coeff_monomial_mul, norm_mul]

/-- **Submultiplicativity.** -/
theorem coeffMass_mul_le (P R : ℂ[X]) : coeffMass (P * R) ≤ coeffMass P * coeffMass R := by
  have hN : P.natDegree < P.natDegree + 1 := Nat.lt_succ_self _
  conv_lhs => rw [as_sum_range' P _ hN, Finset.sum_mul]
  refine (coeffMass_sum_le _ _).trans (le_of_eq ?_)
  rw [coeffMass_eq_sum_range P hN, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => coeffMass_monomial_mul _ _ _

theorem coeffMass_one : coeffMass 1 = 1 := by
  rw [coeffMass_eq_sum_range 1 (by simp : (1 : ℂ[X]).natDegree < 1)]
  simp

theorem coeffMass_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    coeffMass (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coeffMass (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffMass_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (coeffMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (coeffMass_nonneg _))

theorem coeffMass_X_sub_C (y : ℂ) : coeffMass (X - C y) = 1 + ‖y‖ := by
  have hdeg : (X - C y).natDegree < 2 := by rw [natDegree_X_sub_C]; norm_num
  rw [coeffMass_eq_sum_range _ hdeg]
  simp [Finset.sum_range_succ, coeff_X, coeff_C]
  ring

theorem norm_eval_le_coeffMass (P : ℂ[X]) (z : ℂ) :
    ‖P.eval z‖ ≤ coeffMass P * (1 + ‖z‖) ^ P.natDegree := by
  rw [eval_eq_sum, coeffMass, Polynomial.sum_def, Polynomial.sum_def, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖z‖ ^ e ≤ (1 + ‖z‖) ^ e := pow_le_pow_left₀ (norm_nonneg _) (by linarith) e
    _ ≤ (1 + ‖z‖) ^ P.natDegree :=
        pow_le_pow_right₀ (by linarith [norm_nonneg z]) (le_natDegree_of_mem_supp e he)

/-- **Lipschitz bound.** `|Q(z) − Q(y)| ≤ |z − y| · deg Q · coeffMass Q · (1 + |z| + |y|)^{deg Q}`. -/
theorem norm_eval_sub_eval_le (P : ℂ[X]) (z y : ℂ) :
    ‖P.eval z - P.eval y‖ ≤
      ‖z - y‖ * P.natDegree * coeffMass P * (1 + ‖z‖ + ‖y‖) ^ P.natDegree := by
  set d := P.natDegree
  have hN : d < d + 1 := Nat.lt_succ_self _
  have hdiff : P.eval z - P.eval y = ∑ k ∈ Finset.range (d + 1), P.coeff k * (z ^ k - y ^ k) := by
    rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hM : ∀ k ∈ Finset.range (d + 1), ‖z ^ k - y ^ k‖ ≤ ‖z - y‖ * d * (1 + ‖z‖ + ‖y‖) ^ d := by
    intro k hk
    have hkd : k ≤ d := by simp at hk; omega
    rw [← (Commute.all z y).geom_sum₂_mul, norm_mul, mul_comm, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (z - y))
    calc ‖∑ i ∈ Finset.range k, z ^ i * y ^ (k - 1 - i)‖
        ≤ ∑ i ∈ Finset.range k, (1 + ‖z‖ + ‖y‖) ^ d := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          rw [norm_mul, norm_pow, norm_pow]
          have hz : ‖z‖ ≤ 1 + ‖z‖ + ‖y‖ := by linarith [norm_nonneg y]
          have hy : ‖y‖ ≤ 1 + ‖z‖ + ‖y‖ := by linarith [norm_nonneg z]
          have h1 : (1 : ℝ) ≤ 1 + ‖z‖ + ‖y‖ := by linarith [norm_nonneg z, norm_nonneg y]
          simp at hi
          calc ‖z‖ ^ i * ‖y‖ ^ (k - 1 - i)
              ≤ (1 + ‖z‖ + ‖y‖) ^ i * (1 + ‖z‖ + ‖y‖) ^ (k - 1 - i) :=
                mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _)
                  (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)
            _ = (1 + ‖z‖ + ‖y‖) ^ (k - 1) := by rw [← pow_add]; congr 1; omega
            _ ≤ (1 + ‖z‖ + ‖y‖) ^ d := pow_le_pow_right₀ h1 (by omega)
      _ = k * (1 + ‖z‖ + ‖y‖) ^ d := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ d * (1 + ‖z‖ + ‖y‖) ^ d := by
          gcongr
  rw [hdiff, coeffMass_eq_sum_range P hN]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.range (d + 1), ‖P.coeff k * (z ^ k - y ^ k)‖
      ≤ ∑ k ∈ Finset.range (d + 1), ‖P.coeff k‖ * (‖z - y‖ * d * (1 + ‖z‖ + ‖y‖) ^ d) :=
        Finset.sum_le_sum fun k hk => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hM k hk) (norm_nonneg _)
    _ = ‖z - y‖ * d * (∑ k ∈ Finset.range (d + 1), ‖P.coeff k‖) * (1 + ‖z‖ + ‖y‖) ^ d := by
        rw [← Finset.sum_mul]; ring

/-- **Lagrange control.**  A polynomial of degree `≤ d` is controlled by its values at `d + 1`
nodes of modulus `≤ R` and mutual distance `≥ h`. -/
theorem coeffMass_le_of_nodes {d : ℕ} (t : Fin (d + 1) → ℂ) {R h : ℝ} (hh : 0 < h)
    (hR : ∀ i, ‖t i‖ ≤ R) (hsep : ∀ i j, i ≠ j → h ≤ ‖t i - t j‖) (Q : ℂ[X])
    (hQ : Q.natDegree ≤ d) :
    coeffMass Q ≤ ((1 + R) / h) ^ d * ∑ i, ‖Q.eval (t i)‖ := by
  classical
  have hinj : Set.InjOn t ↑(Finset.univ : Finset (Fin (d + 1))) := fun i _ j _ hij => by
    by_contra hne
    have := hsep i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  have hdeg : Q.degree < ↑(Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le hQ)
  have hQeq := Lagrange.eq_interpolate (s := Finset.univ) hinj hdeg
  rw [Lagrange.interpolate_apply] at hQeq
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0)
  have hbasis : ∀ i, coeffMass (Lagrange.basis Finset.univ t i) ≤ ((1 + R) / h) ^ d := by
    intro i
    rw [Lagrange.basis]
    refine (coeffMass_prod_le _ _).trans ?_
    have hcard : (Finset.univ.erase i).card = d := by simp
    calc ∏ j ∈ Finset.univ.erase i, coeffMass (Lagrange.basisDivisor (t i) (t j))
        ≤ ∏ _j ∈ Finset.univ.erase i, (1 + R) / h := by
          refine Finset.prod_le_prod (fun j _ => coeffMass_nonneg _) fun j hj => ?_
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          rw [Lagrange.basisDivisor, coeffMass_C_mul, coeffMass_X_sub_C, norm_inv]
          have hs := hsep i j (Ne.symm hji)
          have hpos : 0 < ‖t i - t j‖ := lt_of_lt_of_le hh hs
          rw [inv_mul_eq_div, div_le_div_iff₀ hpos hh]
          nlinarith [hR j, norm_nonneg (t j)]
      _ = ((1 + R) / h) ^ d := by rw [Finset.prod_const, hcard]
  conv_lhs => rw [hQeq]
  refine (coeffMass_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [coeffMass_C_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hbasis i) (norm_nonneg _)

/-- **Heat comparison.**  For `s = σ + iε` and `Q` of degree `≤ d`,
`Re(e^{-s} Q(s) \overline{Q(\bar s)}) ≥ e^{-σ}|Q(σ)|² − (1 + 2d)|ε| e^{-σ} coeffMass(Q)² (1 + 2|s|)^{2d}`. -/
theorem re_exp_mul_eval_mul_conj_ge {d : ℕ} (Q : ℂ[X]) (hQ : Q.natDegree ≤ d) (s : ℂ) :
    Real.exp (-s.re) * ‖Q.eval (s.re : ℂ)‖ ^ 2 -
        (1 + 2 * d) * |s.im| * Real.exp (-s.re) * coeffMass Q ^ 2 * (1 + 2 * ‖s‖) ^ (2 * d) ≤
      (Complex.exp (-s) * Q.eval s * (starRingEnd ℂ) (Q.eval ((starRingEnd ℂ) s))).re := by
  set σ := s.re with hσ
  set ε := s.im with hε
  set M := coeffMass Q with hM
  have hM0 : 0 ≤ M := coeffMass_nonneg Q
  have hσs : ‖(σ : ℂ)‖ ≤ ‖s‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm s
  have hcs : ‖(starRingEnd ℂ) s‖ = ‖s‖ := Complex.norm_conj s
  have hsσ : ‖s - σ‖ = |ε| := by
    have : s - σ = ε * Complex.I := by apply Complex.ext <;> simp [hσ, hε]
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hcsσ : ‖(starRingEnd ℂ) s - σ‖ = |ε| := by
    have : (starRingEnd ℂ) s - σ = -(ε * Complex.I) := by apply Complex.ext <;> simp [hσ, hε]
    rw [this, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  set W := (1 + 2 * ‖s‖) ^ d with hW
  have hW1 : 1 ≤ W := one_le_pow₀ (by linarith [norm_nonneg s])
  have hpow : ∀ z : ℂ, ‖z‖ ≤ ‖s‖ → ‖Q.eval z‖ ≤ M * W := by
    intro z hz
    refine (norm_eval_le_coeffMass Q z).trans (mul_le_mul_of_nonneg_left ?_ hM0)
    calc (1 + ‖z‖) ^ Q.natDegree ≤ (1 + 2 * ‖s‖) ^ Q.natDegree :=
          pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg s]) _
      _ ≤ W := pow_le_pow_right₀ (by linarith [norm_nonneg s]) hQ
  have hlip : ∀ z : ℂ, ‖z‖ ≤ ‖s‖ → ‖Q.eval z - Q.eval (σ : ℂ)‖ ≤ ‖z - σ‖ * d * M * W := by
    intro z hz
    refine (norm_eval_sub_eval_le Q z σ).trans ?_
    have h1 : (1 + ‖z‖ + ‖(σ : ℂ)‖) ^ Q.natDegree ≤ W :=
      (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg s]) hQ)
    have h2 : (Q.natDegree : ℝ) ≤ d := by exact_mod_cast hQ
    have h3 : 0 ≤ ‖z - σ‖ := norm_nonneg _
    have h4 : 0 ≤ (1 + ‖z‖ + ‖(σ : ℂ)‖) ^ Q.natDegree := by positivity
    have h5 : ‖z - σ‖ * Q.natDegree * M ≤ ‖z - σ‖ * d * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h3) hM0
    nlinarith [mul_le_mul h5 h1 h4 (by positivity : (0 : ℝ) ≤ ‖z - σ‖ * d * M)]
  set A : ℂ := Q.eval s with hAdef
  set B : ℂ := (starRingEnd ℂ) (Q.eval ((starRingEnd ℂ) s)) with hBdef
  set A₀ : ℂ := Q.eval (σ : ℂ) with hA₀def
  have hA : ‖A‖ ≤ M * W := hpow s le_rfl
  have hB : ‖B‖ ≤ M * W := by rw [Complex.norm_conj]; exact hpow _ hcs.le
  have hA₀ : ‖A₀‖ ≤ M * W := hpow _ hσs
  have hAA : ‖A - A₀‖ ≤ |ε| * d * M * W := by rw [← hsσ]; exact hlip s le_rfl
  have hBB : ‖B - (starRingEnd ℂ) A₀‖ ≤ |ε| * d * M * W := by
    rw [← map_sub, Complex.norm_conj, ← hcsσ]; exact hlip _ hcs.le
  have hexp : ‖Complex.exp (-s) - Real.exp (-σ)‖ ≤ Real.exp (-σ) * |ε| := by
    have : Complex.exp (-s) = Real.exp (-σ) * Complex.exp (Complex.I * ((-ε : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1
      apply Complex.ext <;> simp [hσ, hε]
    rw [this, show (Real.exp (-σ) : ℂ) * Complex.exp (Complex.I * ((-ε : ℝ) : ℂ)) - Real.exp (-σ) =
      Real.exp (-σ) * (Complex.exp (Complex.I * ((-ε : ℝ) : ℂ)) - 1) by ring, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -ε)
    rwa [Real.norm_eq_abs, abs_neg] at this
  -- the exact main term
  have hmain : ((Real.exp (-σ) : ℂ) * A₀ * (starRingEnd ℂ) A₀).re = Real.exp (-σ) * ‖A₀‖ ^ 2 := by
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hdiff : ‖Complex.exp (-s) * A * B - (Real.exp (-σ) : ℂ) * A₀ * (starRingEnd ℂ) A₀‖ ≤
      (1 + 2 * d) * |ε| * Real.exp (-σ) * M ^ 2 * W ^ 2 := by
    have hsplit : Complex.exp (-s) * A * B - (Real.exp (-σ) : ℂ) * A₀ * (starRingEnd ℂ) A₀ =
        (Complex.exp (-s) - Real.exp (-σ)) * (A * B) +
          (Real.exp (-σ) : ℂ) * ((A - A₀) * B + A₀ * (B - (starRingEnd ℂ) A₀)) := by ring
    rw [hsplit]
    have he := (Real.exp_pos (-σ)).le
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hε0 := abs_nonneg ε
    have hMW : 0 ≤ M * W := mul_nonneg hM0 (by linarith)
    calc ‖(Complex.exp (-s) - Real.exp (-σ)) * (A * B) +
          (Real.exp (-σ) : ℂ) * ((A - A₀) * B + A₀ * (B - (starRingEnd ℂ) A₀))‖
        ≤ ‖Complex.exp (-s) - Real.exp (-σ)‖ * (‖A‖ * ‖B‖) +
            Real.exp (-σ) * (‖A - A₀‖ * ‖B‖ + ‖A₀‖ * ‖B - (starRingEnd ℂ) A₀‖) := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, norm_mul]
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg he]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) he
            rw [norm_mul, norm_mul]
      _ ≤ Real.exp (-σ) * |ε| * (M * W * (M * W)) +
            Real.exp (-σ) * (|ε| * d * M * W * (M * W) + M * W * (|ε| * d * M * W)) := by
          gcongr
      _ = (1 + 2 * d) * |ε| * Real.exp (-σ) * M ^ 2 * W ^ 2 := by ring
  have hW2 : W ^ 2 = (1 + 2 * ‖s‖) ^ (2 * d) := by rw [hW, ← pow_mul, mul_comm d 2]
  set D := Complex.exp (-s) * A * B - (Real.exp (-σ) : ℂ) * A₀ * (starRingEnd ℂ) A₀ with hD
  have hre : (-D).re ≤ ‖-D‖ := Complex.re_le_norm _
  rw [norm_neg, Complex.neg_re, hD, Complex.sub_re, hmain] at hre
  rw [← hW2]
  linarith

end

end GaloisForLFunctions.HTGeometry
