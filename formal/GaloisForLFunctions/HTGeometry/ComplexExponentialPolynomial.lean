import Mathlib
import GaloisForLFunctions.HTGeometry.ExponentialTypeZeroDensity

/-!
# Complex exponential polynomials

An exponential polynomial `∑ⱼ Pⱼ(z) e^{cⱼ z}` with pairwise distinct complex frequencies and
nonzero polynomial blocks is entire, of finite exponential type, and not identically zero.

Nonvanishing is proved algebraically: multiplying by `e^{-c_last z}` and differentiating
`deg P_last + 1` times kills the last block, while every other block keeps its degree because its
leading coefficient is multiplied by a nonzero power of `c_j - c_last`.  Induction on the number
of blocks reduces to a single block, where an identically vanishing polynomial multiple of a
nonvanishing exponential forces the polynomial to be zero.

Combining the resulting exponential-type envelope with the Jensen zero-count of
`ExponentialTypeZeroDensity` bounds the number of distinct zeros in a disc of radius `r`
by `K(1 + r)`.
-/

namespace GaloisForLFunctions.HTGeometry.CExpPoly

open Finset Polynomial

/-- The first-order operator `P ↦ c·P + P'` computing derivatives of `P(z)e^{cz}`. -/
noncomputable def cshiftD (c : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.C c * P + Polynomial.derivative P

/-- A complex exponential polynomial. -/
noncomputable def cexpFn {m : ℕ} (c : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (z : ℂ) : ℂ :=
  ∑ j, (P j).eval z * Complex.exp (c j * z)

theorem hasDerivAt_cpolyExp (c : ℂ) (P : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => P.eval w * Complex.exp (c * w))
      ((cshiftD c P).eval z * Complex.exp (c * z)) z := by
  have hP : HasDerivAt (fun w : ℂ => P.eval w) ((Polynomial.derivative P).eval z) z :=
    P.hasDerivAt z
  have hE : HasDerivAt (fun w : ℂ => Complex.exp (c * w)) (Complex.exp (c * z) * c) z := by
    simpa using ((hasDerivAt_id z).const_mul c).cexp
  have hmul := hP.mul hE
  have hval : (Polynomial.derivative P).eval z * Complex.exp (c * z)
      + P.eval z * (Complex.exp (c * z) * c)
      = (cshiftD c P).eval z * Complex.exp (c * z) := by
    simp [cshiftD]
    ring
  rwa [hval] at hmul

theorem differentiable_cpolyExp (c : ℂ) (P : Polynomial ℂ) :
    Differentiable ℂ (fun z : ℂ => P.eval z * Complex.exp (c * z)) :=
  fun z => (hasDerivAt_cpolyExp c P z).differentiableAt

theorem differentiable_cexpFn {m : ℕ} (c : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    Differentiable ℂ (cexpFn c P) := by
  intro z
  unfold cexpFn
  exact DifferentiableAt.fun_sum (fun j _ => (differentiable_cpolyExp (c j) (P j)) z)

theorem deriv_cexpFn {m : ℕ} (c : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    deriv (cexpFn c P) = cexpFn c (fun j => cshiftD (c j) (P j)) := by
  funext z
  unfold cexpFn
  rw [deriv_fun_sum (fun j _ => (differentiable_cpolyExp (c j) (P j)) z)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (hasDerivAt_cpolyExp (c j) (P j) z).deriv

theorem coeff_cderivative_natDegree (P : Polynomial ℂ) :
    (Polynomial.derivative P).coeff P.natDegree = 0 := by
  rcases Nat.eq_zero_or_pos P.natDegree with h | h
  · rw [Polynomial.eq_C_of_natDegree_eq_zero h]
    simp
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (Polynomial.natDegree_derivative_lt (by omega))

theorem coeff_cshiftD_natDegree (c : ℂ) (P : Polynomial ℂ) :
    (cshiftD c P).coeff P.natDegree = c * P.leadingCoeff := by
  rw [cshiftD, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_cderivative_natDegree, add_zero]
  rfl

theorem cshiftD_ne_zero (c : ℂ) (hc : c ≠ 0) {P : Polynomial ℂ} (hP : P ≠ 0) :
    cshiftD c P ≠ 0 := by
  intro hzero
  have hlead := coeff_cshiftD_natDegree c P
  rw [hzero] at hlead
  simp only [Polynomial.coeff_zero] at hlead
  exact (mul_ne_zero hc (Polynomial.leadingCoeff_ne_zero.mpr hP)) hlead.symm

theorem cshiftD_iterate_ne_zero (c : ℂ) (hc : c ≠ 0) :
    ∀ (k : ℕ) {P : Polynomial ℂ}, P ≠ 0 → (cshiftD c)^[k] P ≠ 0 := by
  intro k
  induction k with
  | zero => intro P hP; simpa using hP
  | succ k ih =>
      intro P hP
      rw [Function.iterate_succ_apply]
      exact ih (cshiftD_ne_zero c hc hP)

theorem cshiftD_zero (P : Polynomial ℂ) : cshiftD 0 P = Polynomial.derivative P := by
  simp [cshiftD]

theorem cexpFn_shift {m : ℕ} (c : Fin m → ℂ) (P : Fin m → Polynomial ℂ) (t z : ℂ) :
    cexpFn c P z = Complex.exp (t * z) * cexpFn (fun j => c j - t) P z := by
  unfold cexpFn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← mul_assoc, mul_comm (Complex.exp (t * z)) ((P j).eval z), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem cexpFn_last_zero {m : ℕ} (c : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ)
    (hlast : P (Fin.last m) = 0) (z : ℂ) :
    cexpFn c P z = cexpFn (fun j : Fin m => c j.castSucc) (fun j : Fin m => P j.castSucc) z := by
  unfold cexpFn
  rw [Fin.sum_univ_castSucc, hlast]
  simp only [Polynomial.eval_zero, zero_mul, add_zero]

/-- Iterating the polynomial shift operator preserves identical vanishing. -/
theorem cexpFn_eq_zero_iterate {m : ℕ} (c : Fin m → ℂ) :
    ∀ (k : ℕ) (P : Fin m → Polynomial ℂ), (∀ z, cexpFn c P z = 0) →
      ∀ z, cexpFn c (fun j => (cshiftD (c j))^[k] (P j)) z = 0 := by
  intro k
  induction k with
  | zero => intro P hP z; simpa using hP z
  | succ k ih =>
      intro P hP z
      have hstep : ∀ w, cexpFn c (fun j => cshiftD (c j) (P j)) w = 0 := by
        intro w
        have hzero : cexpFn c P = fun _ : ℂ => (0 : ℂ) := funext hP
        have := congrFun (deriv_cexpFn c P) w
        rw [hzero] at this
        simpa using this.symm
      have := ih (fun j => cshiftD (c j) (P j)) hstep z
      simpa only [Function.iterate_succ_apply] using this

/-- A complex exponential polynomial vanishing identically has all polynomial blocks zero. -/
theorem eq_zero_of_cexpFn_eq_zero :
    ∀ (m : ℕ) (c : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ), Function.Injective c →
      (∀ z, cexpFn c P z = 0) → ∀ j, P j = 0 := by
  intro m
  induction m with
  | zero =>
      intro c P _ hzero j
      have hroot : ∀ z : ℂ, (P 0).eval z = 0 := by
        intro z
        have h := hzero z
        unfold cexpFn at h
        rw [Fin.sum_univ_one] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact h1
        · exact absurd h2 (Complex.exp_ne_zero _)
      have : P 0 = 0 := by
        apply Polynomial.funext
        intro z
        simpa using hroot z
      have hj : j = 0 := Fin.fin_one_eq_zero j
      rw [hj]
      exact this
  | succ m ih =>
      intro c P hc hzero
      set L : Fin (m + 2) := Fin.last (m + 1) with hL
      set b : Fin (m + 2) → ℂ := fun j => c j - c L with hb
      have hbinj : Function.Injective b := by
        intro i j hij
        exact hc (by simpa [hb, sub_left_inj] using hij)
      have hbL : b L = 0 := by simp [hb]
      have hbzero : ∀ z, cexpFn b P z = 0 := by
        intro z
        have h := hzero z
        rw [cexpFn_shift c P (c L) z] at h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 (Complex.exp_ne_zero _)
        · exact h2
      set d : ℕ := (P L).natDegree with hd
      set Q : Fin (m + 2) → Polynomial ℂ := fun j => (cshiftD (b j))^[d + 1] (P j) with hQ
      have hQzero : ∀ z, cexpFn b Q z = 0 := cexpFn_eq_zero_iterate b (d + 1) P hbzero
      have hQL : Q L = 0 := by
        have hfun : cshiftD (b L) = (⇑(Polynomial.derivative (R := ℂ))) := by
          funext R
          rw [hbL]
          exact cshiftD_zero R
        show (cshiftD (b L))^[d + 1] (P L) = 0
        rw [hfun]
        exact Polynomial.iterate_derivative_eq_zero (by omega)
      have hQcast : ∀ z, cexpFn (fun j : Fin (m + 1) => b j.castSucc)
          (fun j : Fin (m + 1) => Q j.castSucc) z = 0 := by
        intro z
        rw [← cexpFn_last_zero b Q hQL z]
        exact hQzero z
      have hIH := ih (fun j : Fin (m + 1) => b j.castSucc) (fun j : Fin (m + 1) => Q j.castSucc)
        (fun i j hij => Fin.castSucc_injective _ (hbinj hij)) hQcast
      have hPcast : ∀ j : Fin (m + 1), P j.castSucc = 0 := by
        intro j
        by_contra hne
        have hbne : b j.castSucc ≠ 0 := by
          intro h0
          have : j.castSucc = L := hbinj (by rw [h0, hbL])
          exact absurd this (Fin.castSucc_lt_last j).ne
        exact cshiftD_iterate_ne_zero (b j.castSucc) hbne (d + 1) hne (hIH j)
      have hPL : P L = 0 := by
        have hlast : ∀ z : ℂ, (P L).eval z * Complex.exp (c L * z) = 0 := by
          intro z
          have h := hzero z
          unfold cexpFn at h
          rw [Fin.sum_univ_castSucc] at h
          have hsum : ∑ j : Fin (m + 1),
              (P j.castSucc).eval z * Complex.exp (c j.castSucc * z) = 0 := by
            refine Finset.sum_eq_zero (fun j _ => ?_)
            rw [hPcast j]
            simp
          rw [hsum, zero_add] at h
          exact h
        apply Polynomial.funext
        intro z
        have h := hlast z
        rcases mul_eq_zero.mp h with h1 | h2
        · simpa using h1
        · exact absurd h2 (Complex.exp_ne_zero _)
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact hPcast j'
      · exact hPL

/-- A complex exponential polynomial with distinct frequencies and nonzero polynomial blocks is
not identically zero. -/
theorem exists_cexpFn_ne_zero {m : ℕ} (c : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ)
    (hc : Function.Injective c) (hP : ∀ j, P j ≠ 0) : ∃ z : ℂ, cexpFn c P z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hP 0 (eq_zero_of_cexpFn_eq_zero m c P hc hcon 0)

theorem norm_eval_le (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ≤ (∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖) * (1 + ‖z‖) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun k hk => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg z) (by linarith [norm_nonneg z]) k
  have h2 : (1 + ‖z‖) ^ k ≤ (1 + ‖z‖) ^ P.natDegree :=
    pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  linarith

theorem one_add_norm_pow_le_exp (d : ℕ) (z : ℂ) :
    (1 + ‖z‖) ^ d ≤ Real.exp ((d : ℝ) * ‖z‖) := by
  have h1 : (1 : ℝ) + ‖z‖ ≤ Real.exp ‖z‖ := by
    have := Real.add_one_le_exp ‖z‖
    linarith
  calc (1 + ‖z‖) ^ d ≤ (Real.exp ‖z‖) ^ d :=
        pow_le_pow_left₀ (by linarith [norm_nonneg z]) h1 d
    _ = Real.exp ((d : ℝ) * ‖z‖) := by
        rw [← Real.exp_nat_mul]

/-- A complex exponential polynomial has finite exponential type. -/
theorem exists_exponentialType_bound {m : ℕ} (c : Fin m → ℂ) (P : Fin m → Polynomial ℂ) :
    ∃ C A : ℝ, 1 ≤ C ∧ 0 ≤ A ∧ ∀ z : ℂ, ‖cexpFn c P z‖ ≤ C * Real.exp (A * ‖z‖) := by
  classical
  set A : ℝ := ∑ j, (((P j).natDegree : ℝ) + ‖c j‖) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg (fun j _ => by positivity)
  set C : ℝ := 1 + ∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖ with hC
  have hCsum : (0 : ℝ) ≤ ∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖ :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => norm_nonneg _))
  refine ⟨C, A, by rw [hC]; linarith, hA0, ?_⟩
  intro z
  have hterm : ∀ j : Fin m, ‖(P j).eval z * Complex.exp (c j * z)‖
      ≤ (∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) * Real.exp (A * ‖z‖) := by
    intro j
    have hexp : ‖Complex.exp (c j * z)‖ ≤ Real.exp (‖c j‖ * ‖z‖) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      calc (c j * z).re ≤ ‖c j * z‖ := Complex.re_le_norm _
        _ = ‖c j‖ * ‖z‖ := by rw [norm_mul]
    have hpoly := norm_eval_le (P j) z
    have hpow := one_add_norm_pow_le_exp (P j).natDegree z
    have hSj : (0 : ℝ) ≤ ∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖ :=
      Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hAj : ((P j).natDegree : ℝ) * ‖z‖ + ‖c j‖ * ‖z‖ ≤ A * ‖z‖ := by
      have hle : ((P j).natDegree : ℝ) + ‖c j‖ ≤ A := by
        rw [hA]
        refine Finset.single_le_sum (f := fun i : Fin m => ((P i).natDegree : ℝ) + ‖c i‖)
          (fun i _ => by positivity) (Finset.mem_univ j)
      nlinarith [norm_nonneg z]
    calc ‖(P j).eval z * Complex.exp (c j * z)‖
        = ‖(P j).eval z‖ * ‖Complex.exp (c j * z)‖ := norm_mul _ _
      _ ≤ ((∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) *
            (1 + ‖z‖) ^ (P j).natDegree) * Real.exp (‖c j‖ * ‖z‖) := by
          exact mul_le_mul hpoly hexp (norm_nonneg _) (by positivity)
      _ ≤ ((∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) *
            Real.exp (((P j).natDegree : ℝ) * ‖z‖)) * Real.exp (‖c j‖ * ‖z‖) := by
          have := mul_le_mul_of_nonneg_left hpow hSj
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = (∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) *
            Real.exp (((P j).natDegree : ℝ) * ‖z‖ + ‖c j‖ * ‖z‖) := by
          rw [Real.exp_add]; ring
      _ ≤ (∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) * Real.exp (A * ‖z‖) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hAj) hSj
  calc ‖cexpFn c P z‖ ≤ ∑ j, ‖(P j).eval z * Complex.exp (c j * z)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) * Real.exp (A * ‖z‖) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = (∑ j, ∑ k ∈ Finset.range ((P j).natDegree + 1), ‖(P j).coeff k‖) * Real.exp (A * ‖z‖) := by
        rw [← Finset.sum_mul]
    _ ≤ C * Real.exp (A * ‖z‖) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [hC]; linarith

end GaloisForLFunctions.HTGeometry.CExpPoly

namespace GaloisForLFunctions.HTGeometry.CExpPoly

open Finset Polynomial

/-- Reflection of the polynomial variable. -/
noncomputable def negComp (P : Polynomial ℂ) : Polynomial ℂ := P.comp (-Polynomial.X)

@[simp]
theorem eval_negComp (P : Polynomial ℂ) (z : ℂ) : (negComp P).eval z = P.eval (-z) := by
  simp [negComp, Polynomial.eval_comp]

theorem negComp_negComp (P : Polynomial ℂ) : negComp (negComp P) = P := by
  unfold negComp
  rw [Polynomial.comp_assoc]
  simp

theorem negComp_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) : negComp P ≠ 0 := by
  intro hzero
  apply hP
  rw [← negComp_negComp P, hzero]
  simp [negComp]

theorem natDegree_negComp (P : Polynomial ℂ) : (negComp P).natDegree = P.natDegree := by
  unfold negComp
  rw [Polynomial.natDegree_comp]
  simp

end GaloisForLFunctions.HTGeometry.CExpPoly

namespace GaloisForLFunctions.HTGeometry.CExpPoly

open Finset Polynomial Metric

/-- **Linear zero count for complex exponential polynomials.**  Jensen's formula applied at a
nonvanishing anchor bounds the number of distinct zeros in a disc of radius `r` by `K(1 + r)`. -/
theorem exists_zeroCount_linear {m : ℕ} (c : Fin (m + 1) → ℂ) (P : Fin (m + 1) → Polynomial ℂ)
    (hc : Function.Injective c) (hP : ∀ j, P j ≠ 0) :
    ∃ (z₀ : ℂ) (K : ℝ), 0 < K ∧ ∀ r : ℝ, 1 ≤ r → ∀ S : Finset ℂ,
      (∀ w ∈ S, cexpFn c P w = 0) → (∀ w ∈ S, w ∈ closedBall z₀ r) →
      (S.card : ℝ) ≤ K * (1 + r) := by
  classical
  obtain ⟨z₀, hz₀⟩ := exists_cexpFn_ne_zero c P hc hP
  obtain ⟨C, A, hC, hA, hgrow⟩ := exists_exponentialType_bound c P
  obtain ⟨K, hK, hbound⟩ :=
    RHTower.exponentialType_zeroCount_linear (differentiable_cexpFn c P) hz₀ hA hC hgrow
  refine ⟨z₀, K, hK, ?_⟩
  intro r hr S hSzero hSball
  have hcard : (S.card : ℤ) ≤
      ∑ᶠ u, (MeromorphicOn.divisor (cexpFn c P) (closedBall z₀ r)) u :=
    RHTower.card_le_sum_divisor_of_finite_zeros (differentiable_cexpFn c P) hz₀
      S (fun w => w) (fun _ _ _ _ h => h) hSball hSzero
  have hcast : (S.card : ℝ) ≤
      (↑(∑ᶠ u, (MeromorphicOn.divisor (cexpFn c P) (closedBall z₀ r)) u) : ℝ) := by
    exact_mod_cast hcard
  exact le_trans hcast (hbound r hr)

end GaloisForLFunctions.HTGeometry.CExpPoly
