import GaloisForLFunctions.HTGeometry.ReciprocalGammaHypertranscendental
import GaloisForLFunctions.HTGeometry.LocalPolynomialGauge
import GaloisForLFunctions.HTGeometry.ExpPolynomialDA
import GaloisForLFunctions.HTGeometry.RationalPowerNormDichotomy
import GaloisForLFunctions.RHTower.FiniteHermiteCRT

/-!
# Complete asymptotic invisibility of hypertranscendence

A nonzero differentially algebraic multiplier divided by `Γ` is hypertranscendental, flat to all
orders in the inverse-power scale, and can be made to vanish to any prescribed finite order at any
finite set of points.  Adding it therefore changes neither a finite jet table nor a complete
inverse-power Poincaré expansion.

The file carries the growth of `Γ` past every power on the positive ray, numeric Hermite
interpolation, the two flatness statements, and the resulting realization theorem: every finite jet
table and every complete asymptotic expansion carried by a differentially algebraic function is
carried simultaneously by a differentially algebraic function and by a punctured affine line of
hypertranscendental ones.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

theorem one_le_gamma_of_two_le {x : ℝ} (hx : 2 ≤ x) : 1 ≤ Real.Gamma x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, Real.Gamma_two]
  · rw [← Real.Gamma_two]
    exact (Real.Gamma_strictMonoOn_Ici (Set.self_mem_Ici) (Set.mem_Ici.2 hx) h).le

theorem gamma_ge_descProd : ∀ (k : ℕ) {x : ℝ}, (k : ℝ) + 3 ≤ x →
    ∏ j ∈ Finset.range (k + 1), (x - (j + 1)) ≤ Real.Gamma x := by
  intro k
  induction k with
  | zero =>
      intro x hx
      have hx1 : (2 : ℝ) ≤ x - 1 := by push_cast at hx; linarith
      have hne : x - 1 ≠ 0 := by linarith
      have hstep : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have := Real.Gamma_add_one hne
        rw [sub_add_cancel] at this
        exact this
      have h1 : 1 ≤ Real.Gamma (x - 1) := one_le_gamma_of_two_le hx1
      have hpos : (0 : ℝ) < x - 1 := by linarith
      have hone : ∏ j ∈ Finset.range 1, (x - ((j : ℝ) + 1)) = x - 1 := by simp
      rw [hone, hstep]
      nlinarith
  | succ k ih =>
      intro x hx
      have hxk : (k : ℝ) + 3 ≤ x - 1 := by push_cast at hx; linarith
      have hne : x - 1 ≠ 0 := by push_cast at hx; linarith
      have hstep : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have := Real.Gamma_add_one hne
        rw [sub_add_cancel] at this
        exact this
      have hIH := ih hxk
      have hpos : (0 : ℝ) < x - 1 := by push_cast at hx; linarith
      have hprod : ∏ j ∈ Finset.range (k + 2), (x - ((j : ℝ) + 1))
          = (x - 1) * ∏ j ∈ Finset.range (k + 1), ((x - 1) - ((j : ℝ) + 1)) := by
        rw [Finset.prod_range_succ']
        simp only [Nat.cast_zero, zero_add]
        rw [mul_comm]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        push_cast
        ring
      rw [hprod, hstep]
      exact mul_le_mul_of_nonneg_left hIH hpos.le

theorem gamma_ge_pow {k : ℕ} {x : ℝ} (hx : (k : ℝ) + 3 ≤ x) :
    (x - (k + 1)) ^ (k + 1) ≤ Real.Gamma x := by
  refine le_trans ?_ (gamma_ge_descProd k hx)
  have hle : ∀ j ∈ Finset.range (k + 1), x - ((k : ℝ) + 1) ≤ x - ((j : ℝ) + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.lt_succ_iff.1 hj
    linarith
  have hnn : (0 : ℝ) ≤ x - ((k : ℝ) + 1) := by linarith
  calc (x - ((k : ℝ) + 1)) ^ (k + 1)
      = ∏ _j ∈ Finset.range (k + 1), (x - ((k : ℝ) + 1)) := by
        rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ j ∈ Finset.range (k + 1), (x - ((j : ℝ) + 1)) :=
        Finset.prod_le_prod (fun j _ => hnn) hle

/-- `Γ` grows faster than every power along the positive real axis. -/
theorem tendsto_pow_div_gamma (M : ℕ) :
    Tendsto (fun x : ℝ => x ^ M / Real.Gamma x) atTop (nhds 0) := by
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlow : ∀ᶠ x : ℝ in atTop, (0 : ℝ) ≤ x ^ M / Real.Gamma x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (by positivity) (Real.Gamma_pos_of_pos hx).le
  have hup : ∀ᶠ x : ℝ in atTop,
      x ^ M / Real.Gamma x ≤ (2 : ℝ) ^ M / (x - ((M : ℝ) + 2)) ^ 2 := by
    filter_upwards [eventually_ge_atTop ((M : ℝ) + 4),
      eventually_ge_atTop (2 * ((M : ℝ) + 2))] with x hx hx2
    have hbase : (0 : ℝ) < x - ((M : ℝ) + 2) := by linarith
    have hxpos : (0 : ℝ) < x := by linarith
    have hgamma : (x - ((M : ℝ) + 2)) ^ (M + 2) ≤ Real.Gamma x := by
      have h := gamma_ge_pow (k := M + 1) (x := x) (by push_cast; linarith)
      have hcast : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
      rwa [hcast] at h
    have hstep1 : x ^ M / Real.Gamma x ≤ x ^ M / (x - ((M : ℝ) + 2)) ^ (M + 2) :=
      div_le_div_of_nonneg_left (pow_nonneg hxpos.le M) (pow_pos hbase _) hgamma
    refine hstep1.trans ?_
    have hxle : x ≤ 2 * (x - ((M : ℝ) + 2)) := by linarith
    have hpow : x ^ M ≤ (2 : ℝ) ^ M * (x - ((M : ℝ) + 2)) ^ M := by
      calc x ^ M ≤ (2 * (x - ((M : ℝ) + 2))) ^ M :=
            pow_le_pow_left₀ (by linarith) hxle M
        _ = (2 : ℝ) ^ M * (x - ((M : ℝ) + 2)) ^ M := by rw [mul_pow]
    have hden : (x - ((M : ℝ) + 2)) ^ (M + 2)
        = (x - ((M : ℝ) + 2)) ^ M * (x - ((M : ℝ) + 2)) ^ 2 := by
      rw [← pow_add]
    rw [hden]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc x ^ M * (x - ((M : ℝ) + 2)) ^ 2
        ≤ ((2 : ℝ) ^ M * (x - ((M : ℝ) + 2)) ^ M) * (x - ((M : ℝ) + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (2 : ℝ) ^ M * ((x - ((M : ℝ) + 2)) ^ M * (x - ((M : ℝ) + 2)) ^ 2) := by ring
  have hzero : Tendsto (fun x : ℝ => (2 : ℝ) ^ M / (x - ((M : ℝ) + 2)) ^ 2) atTop (nhds 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ _
    exact tendsto_pow_atTop (by norm_num) |>.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
  exact squeeze_zero' hlow hup hzero

/-! ### Numeric Hermite interpolation -/

open Polynomial in
/-- The Taylor polynomial with prescribed iterated derivative values at one point. -/
def jetTaylorPolynomial (a : ℂ) (m : ℕ) (v : ℕ → ℂ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (m + 1), Polynomial.C (v j / ((Nat.factorial j : ℕ) : ℂ)) * (Polynomial.X - Polynomial.C a) ^ j

open Polynomial in
theorem eval_iterate_derivative_jetTaylorPolynomial (a : ℂ) (m : ℕ) (v : ℕ → ℂ) {n : ℕ}
    (hn : n ≤ m) :
    (Polynomial.derivative^[n] (jetTaylorPolynomial a m v)).eval a = v n := by
  classical
  rw [jetTaylorPolynomial, iterate_derivative_sum, eval_finsetSum]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      (Polynomial.derivative^[n] (Polynomial.C (v j / ((Nat.factorial j : ℕ) : ℂ)) *
        (Polynomial.X - Polynomial.C a) ^ j)).eval a = if j = n then v n else 0 := by
    intro j _
    rw [iterate_derivative_C_mul, iterate_derivative_X_sub_pow, eval_mul, eval_C, eval_smul,
      eval_pow, eval_sub, eval_X, eval_C, sub_self]
    by_cases hj : j = n
    · subst hj
      rw [if_pos rfl, Nat.sub_self, pow_zero, Nat.descFactorial_self]
      have hfac : ((Nat.factorial j : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
      rw [nsmul_eq_mul, mul_one]
      field_simp
    · rw [if_neg hj]
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hzero : j.descFactorial n = 0 := Nat.descFactorial_eq_zero_iff_lt.2 hlt
        rw [hzero]
        simp
      · have hpos : 0 < j - n := Nat.sub_pos_of_lt hgt
        rw [zero_pow (by omega)]
        simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (m + 1)) n (fun _ => v n),
    if_pos (Finset.mem_range.2 (by omega))]

open Polynomial in
/-- **Numeric Hermite interpolation.**  One polynomial realizes arbitrary prescribed iterated
derivative values at finitely many distinct points. -/
theorem exists_polynomial_iteratedDeriv_eval_eq {ι : Type*} [Finite ι] (a : ι → ℂ)
    (ha : Function.Injective a) (m : ι → ℕ) (v : ι → ℕ → ℂ) :
    ∃ B : Polynomial ℂ, ∀ (i : ι) (n : ℕ), n ≤ m i →
      iteratedDeriv n (fun z => B.eval z) (a i) = v i n := by
  obtain ⟨B, hB⟩ := RHTower.exists_polynomial_iterateDerivative_eval_eq a ha (fun i => m i + 1)
    (fun i => jetTaylorPolynomial (a i) (m i) (v i))
  refine ⟨B, fun i n hn => ?_⟩
  rw [iteratedDeriv_polynomial_eval, hB i n (by omega),
    eval_iterate_derivative_jetTaylorPolynomial (a i) (m i) (v i) hn]

/-! ### Jet agreement is preserved by multiplication -/

theorem iteratedDeriv_mul_jet_congr {f g h : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : ContDiffAt ℂ (⊤ : ℕ∞) f a) (hg : ContDiffAt ℂ (⊤ : ℕ∞) g a)
    (hh : ContDiffAt ℂ (⊤ : ℕ∞) h a)
    (hjet : ∀ l, l ≤ m → iteratedDeriv l f a = iteratedDeriv l g a) {j : ℕ} (hj : j ≤ m) :
    iteratedDeriv j (fun z => h z * f z) a = iteratedDeriv j (fun z => h z * g z) a := by
  have hfj : ContDiffAt ℂ ((j : ℕ) : ℕ∞) f a := hf.of_le (by exact_mod_cast le_top)
  have hgj : ContDiffAt ℂ ((j : ℕ) : ℕ∞) g a := hg.of_le (by exact_mod_cast le_top)
  have hhj : ContDiffAt ℂ ((j : ℕ) : ℕ∞) h a := hh.of_le (by exact_mod_cast le_top)
  have hlf : (fun z => h z * f z) = h * f := rfl
  have hlg : (fun z => h z * g z) = h * g := rfl
  rw [hlf, hlg, iteratedDeriv_mul hhj hfj, iteratedDeriv_mul hhj hgj]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hjet (j - i) (le_trans (Nat.sub_le j i) hj)]

/-! ### Polynomial growth on the positive ray -/

theorem exists_bound_eval_polynomial (B : Polynomial ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖B.eval (x : ℂ)‖ ≤ C * x ^ B.natDegree := by
  classical
  refine ⟨∑ i ∈ Finset.range (B.natDegree + 1), ‖B.coeff i‖, by positivity, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [norm_mul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact pow_le_pow_right₀ hx (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-! ### Flatness in the inverse-power scale -/

/-- A function is flat in the inverse-power Poincaré scale along the positive real ray. -/
def FlatInversePowers (E : ℂ → ℂ) : Prop :=
  ∀ M : ℕ, Tendsto (fun x : ℝ => ‖E (x : ℂ)‖ * x ^ M) atTop (nhds 0)

theorem flat_exp_neg_mul_polynomial (Q : Polynomial ℂ) :
    FlatInversePowers (fun z => Complex.exp (-z) * Q.eval z) := by
  intro M
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial Q
  refine squeeze_zero' (g := fun x : ℝ => C * (x ^ (Q.natDegree + M) * Real.exp (-x))) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    show ‖Complex.exp (-(x : ℂ)) * Q.eval (x : ℂ)‖ * x ^ M
      ≤ C * (x ^ (Q.natDegree + M) * Real.exp (-x))
    have hexp : ‖Complex.exp (-(x : ℂ))‖ = Real.exp (-x) := by
      rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal]
    rw [norm_mul, hexp]
    have hx0 : (0 : ℝ) ≤ x := by linarith
    calc Real.exp (-x) * ‖Q.eval (x : ℂ)‖ * x ^ M
        ≤ Real.exp (-x) * (C * x ^ Q.natDegree) * x ^ M := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hC x hx) (Real.exp_nonneg _)
      _ = C * (x ^ (Q.natDegree + M) * Real.exp (-x)) := by rw [pow_add]; ring
  · have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (Q.natDegree + M)).const_mul C
    simpa using this

theorem flat_polynomial_mul_invGamma (lam : ℂ) (A : Polynomial ℂ) :
    FlatInversePowers (fun z => lam * A.eval z * (Complex.Gamma z)⁻¹) := by
  intro M
  obtain ⟨C, hC0, hC⟩ := exists_bound_eval_polynomial A
  refine squeeze_zero'
    (g := fun x : ℝ => (‖lam‖ * C) * (x ^ (A.natDegree + M) / Real.Gamma x)) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    show ‖lam * A.eval (x : ℂ) * (Complex.Gamma (x : ℂ))⁻¹‖ * x ^ M
      ≤ (‖lam‖ * C) * (x ^ (A.natDegree + M) / Real.Gamma x)
    have hx0 : (0 : ℝ) < x := by linarith
    have hgam : ‖(Complex.Gamma (x : ℂ))⁻¹‖ = (Real.Gamma x)⁻¹ := by
      rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.Gamma x)⁻¹)]
    rw [norm_mul, norm_mul, hgam]
    have hginv : (0 : ℝ) < (Real.Gamma x)⁻¹ := by positivity
    calc ‖lam‖ * ‖A.eval (x : ℂ)‖ * (Real.Gamma x)⁻¹ * x ^ M
        ≤ ‖lam‖ * (C * x ^ A.natDegree) * (Real.Gamma x)⁻¹ * x ^ M := by
          gcongr
          exact hC x hx
      _ = (‖lam‖ * C) * (x ^ (A.natDegree + M) / Real.Gamma x) := by
          rw [pow_add, div_eq_mul_inv]
          ring
  · have := (tendsto_pow_div_gamma (A.natDegree + M)).const_mul (‖lam‖ * C)
    simpa using this

/-! ### Poincaré expansions in inverse powers -/

/-- `G` carries the complete inverse-power Poincaré expansion `∑ b n x^{-n}` along `+∞`. -/
def PoincareInversePowers (G : ℂ → ℂ) (b : ℕ → ℂ) : Prop :=
  ∀ M : ℕ, Tendsto
    (fun x : ℝ => ‖G (x : ℂ) - ∑ n ∈ Finset.range M, b n * ((x : ℂ) ^ n)⁻¹‖ * x ^ M)
    atTop (nhds 0)

theorem PoincareInversePowers.add_flat {G E : ℂ → ℂ} {b : ℕ → ℂ}
    (h : PoincareInversePowers G b) (hE : FlatInversePowers E) :
    PoincareInversePowers (fun z => G z + E z) b := by
  intro M
  have hsum := (h M).add (hE M)
  rw [add_zero] at hsum
  refine squeeze_zero'
    (g := fun x : ℝ => ‖G (x : ℂ) - ∑ n ∈ Finset.range M, b n * ((x : ℂ) ^ n)⁻¹‖ * x ^ M
      + ‖E (x : ℂ)‖ * x ^ M) ?_ ?_ hsum
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    positivity
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hrw : (G (x : ℂ) + E (x : ℂ)) - ∑ n ∈ Finset.range M, b n * ((x : ℂ) ^ n)⁻¹
        = (G (x : ℂ) - ∑ n ∈ Finset.range M, b n * ((x : ℂ) ^ n)⁻¹) + E (x : ℂ) := by ring
    show ‖(G (x : ℂ) + E (x : ℂ)) - ∑ n ∈ Finset.range M, b n * ((x : ℂ) ^ n)⁻¹‖ * x ^ M ≤ _
    rw [hrw, ← add_mul]
    gcongr
    exact norm_add_le _ _

/-! ### The interpolation modulus and its vanishing jets -/

open Polynomial in
/-- The modulus with a zero of order `m i + 1` at every node. -/
def jetModulus {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ) : Polynomial ℂ :=
  ∏ i : ι, (Polynomial.X - Polynomial.C (a i)) ^ (m i + 1)

open Polynomial in
theorem jetModulus_ne_zero {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ) :
    jetModulus a m ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ ?_
  exact Polynomial.X_sub_C_ne_zero (a i)

open Polynomial in
theorem iteratedDeriv_jetModulus_eq_zero {ι : Type*} [Fintype ι] (a : ι → ℂ) (m : ι → ℕ)
    (i : ι) {n : ℕ} (hn : n ≤ m i) :
    iteratedDeriv n (fun z => (jetModulus a m).eval z) (a i) = 0 := by
  classical
  have hdvd : (Polynomial.X - Polynomial.C (a i)) ^ (m i + 1) ∣ jetModulus a m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hsub : (Polynomial.X - Polynomial.C (a i)) ^ (m i + 1) ∣ (jetModulus a m - 0) := by
    simpa using hdvd
  have h := RHTower.eval_iterate_derivative_eq_of_power_linear_dvd_sub hsub
    (Nat.lt_succ_of_le hn)
  rw [iteratedDeriv_polynomial_eval, h]
  simp

/-! ### The invisibility theorem -/

open Polynomial in
/-- **Complete asymptotic invisibility via flat hypertranscendental perturbations.**  Every finite
jet table and every complete inverse-power Poincaré expansion carried by a differentially algebraic
function on a domain is carried simultaneously by a differentially algebraic function and by a
punctured affine line of hypertranscendental ones. -/
theorem exists_differentiallyAlgebraic_and_hypertranscendental_realization
    {ι : Type*} [Fintype ι] {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    {G : ℂ → ℂ} (hGan : AnalyticOnNhd ℂ G U) (hGDA : DifferentiallyAlgebraicOn G U)
    {b : ℕ → ℂ} (hGpo : PoincareInversePowers G b)
    (a : ι → ℂ) (ha : Function.Injective a) (haU : ∀ i, a i ∈ U)
    (m : ι → ℕ) (c : ι → ℕ → ℂ) :
    ∃ (D : ℂ → ℂ) (A : Polynomial ℂ), A ≠ 0 ∧ AnalyticOnNhd ℂ D U ∧
      DifferentiallyAlgebraicOn D U ∧
      (∀ i n, n ≤ m i → iteratedDeriv n D (a i) = c i n) ∧
      PoincareInversePowers D b ∧
      ∀ lam : ℂ, lam ≠ 0 →
        (∀ i n, n ≤ m i →
            iteratedDeriv n (fun z => D z + lam * A.eval z * (Complex.Gamma z)⁻¹) (a i) = c i n) ∧
          ¬ DifferentiallyAlgebraicOn
              (fun z => D z + lam * A.eval z * (Complex.Gamma z)⁻¹) U ∧
          PoincareInversePowers (fun z => D z + lam * A.eval z * (Complex.Gamma z)⁻¹) b := by
  classical
  obtain ⟨T, hT⟩ := exists_polynomial_iteratedDeriv_eval_eq a ha m
    (fun i n => c i n - iteratedDeriv n G (a i))
  obtain ⟨Q, hQ⟩ := exists_polynomial_iteratedDeriv_eval_eq a ha m
    (fun i n => iteratedDeriv n (fun z => Complex.exp z * T.eval z) (a i))
  -- smoothness of the building blocks
  have hexpNeg : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp (-z) :=
    (Complex.differentiable_exp.comp differentiable_neg).contDiff
  have hQpoly : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Q.eval z :=
    (Polynomial.differentiable Q).contDiff
  have hTpoly : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => T.eval z :=
    (Polynomial.differentiable T).contDiff
  have hexpT : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => Complex.exp z * T.eval z :=
    (Complex.differentiable_exp.contDiff).mul hTpoly
  have hinvG : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => (Complex.Gamma z)⁻¹ :=
    Complex.differentiable_one_div_Gamma.contDiff
  set E : ℂ → ℂ := fun z => Complex.exp (-z) * Q.eval z with hEdef
  have hEcd : ContDiff ℂ (⊤ : ℕ∞) E := hexpNeg.mul hQpoly
  have hEan : AnalyticOnNhd ℂ E U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.2 (hEcd.differentiable (by simp))) z
      (Set.mem_univ z)
  have hEDA : DifferentiallyAlgebraicOn E U := by
    obtain ⟨n, P, hP0, hPv⟩ := differentiallyAlgebraic_cexp_mul_polynomial (-1) Q
    refine ⟨n, P, hP0, fun z _ => ?_⟩
    have hfun : (fun s : ℂ => Complex.exp (-1 * s) * Q.eval s) = E := by
      funext s
      rw [hEdef]
      congr 2
      ring
    rw [← hfun]
    exact hPv z
  -- the jets of the correction
  have hEjet : ∀ (i : ι) (n : ℕ), n ≤ m i →
      iteratedDeriv n E (a i) = c i n - iteratedDeriv n G (a i) := by
    intro i n hn
    have hcongr := iteratedDeriv_mul_jet_congr (f := fun z : ℂ => Q.eval z)
      (g := fun z : ℂ => Complex.exp z * T.eval z) (h := fun z : ℂ => Complex.exp (-z))
      (a := a i) (m := m i) hQpoly.contDiffAt hexpT.contDiffAt hexpNeg.contDiffAt
      (fun l hl => hQ i l hl) hn
    have hcollapse : (fun z : ℂ => Complex.exp (-z) * (Complex.exp z * T.eval z))
        = fun z : ℂ => T.eval z := by
      funext z
      rw [← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
    rw [hEdef, hcongr, hcollapse, hT i n hn]
  refine ⟨fun z => G z + E z, jetModulus a m, jetModulus_ne_zero a m,
    hGan.add hEan,
    differentiallyAlgebraicOn_add hUo hUc hUne hUinf hGan hEan hGDA hEDA, ?_, ?_, ?_⟩
  · intro i n hn
    have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
      ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
    have hEcdn : ContDiffAt ℂ ((n : ℕ) : ℕ∞) E (a i) := hEcd.contDiffAt.of_le
      (by exact_mod_cast le_top)
    have hadd : (fun z => G z + E z) = G + E := rfl
    rw [hadd, iteratedDeriv_add hGcd hEcdn, hEjet i n hn]
    ring
  · exact hGpo.add_flat (by simpa [hEdef] using flat_exp_neg_mul_polynomial Q)
  · intro lam hlam
    have hAjet : ∀ (i : ι) (n : ℕ), n ≤ m i →
        iteratedDeriv n (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) (a i)
          = 0 := by
      intro i n hn
      have hAcd : ContDiff ℂ (⊤ : ℕ∞) fun z : ℂ => lam * (jetModulus a m).eval z :=
        contDiff_const.mul ((Polynomial.differentiable (jetModulus a m)).contDiff)
      have hjets : ∀ l, l ≤ m i →
          iteratedDeriv l (fun z : ℂ => lam * (jetModulus a m).eval z) (a i)
            = iteratedDeriv l (fun _ : ℂ => (0 : ℂ)) (a i) := by
        intro l hl
        have hpoly : ContDiffAt ℂ ((l : ℕ) : ℕ∞) (fun z : ℂ => (jetModulus a m).eval z) (a i) :=
          ((Polynomial.differentiable (jetModulus a m)).contDiff (n := ((l : ℕ) : ℕ∞))).contDiffAt
        rw [iteratedDeriv_const_mul (f := fun z : ℂ => (jetModulus a m).eval z) lam hpoly,
          iteratedDeriv_jetModulus_eq_zero a m i hl, mul_zero, iteratedDeriv_const]
        simp
      have hcongr := iteratedDeriv_mul_jet_congr
        (f := fun z : ℂ => lam * (jetModulus a m).eval z) (g := fun _ : ℂ => (0 : ℂ))
        (h := fun z : ℂ => (Complex.Gamma z)⁻¹) (a := a i) (m := m i)
        hAcd.contDiffAt contDiff_const.contDiffAt hinvG.contDiffAt hjets hn
      have hswap : (fun z : ℂ => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹)
          = fun z : ℂ => (Complex.Gamma z)⁻¹ * (lam * (jetModulus a m).eval z) := by
        funext z
        ring
      rw [hswap, hcongr]
      simp
    refine ⟨?_, ?_, ?_⟩
    · intro i n hn
      have hDcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) (fun z => G z + E z) (a i) := by
        refine ContDiffAt.add ?_ (hEcd.contDiffAt.of_le (by exact_mod_cast le_top))
        exact ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
      have hRcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞)
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) (a i) := by
        refine ContDiffAt.mul ?_ (hinvG.contDiffAt.of_le (by exact_mod_cast le_top))
        exact (contDiff_const.mul ((Polynomial.differentiable
          (jetModulus a m)).contDiff)).contDiffAt.of_le (by exact_mod_cast le_top)
      have hsum : (fun z => (fun z => G z + E z) z +
          lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹)
          = (fun z => G z + E z) + fun z => lam * (jetModulus a m).eval z *
            (Complex.Gamma z)⁻¹ := rfl
      rw [hsum, iteratedDeriv_add hDcd hRcd, hAjet i n hn, add_zero]
      have hGcd : ContDiffAt ℂ ((n : ℕ) : ℕ∞) G (a i) :=
        ((hGan (a i) (haU i)).contDiffAt).of_le (by exact_mod_cast le_top)
      have hEcdn : ContDiffAt ℂ ((n : ℕ) : ℕ∞) E (a i) := hEcd.contDiffAt.of_le
        (by exact_mod_cast le_top)
      have hadd : (fun z => G z + E z) = G + E := rfl
      rw [hadd, iteratedDeriv_add hGcd hEcdn, hEjet i n hn]
      ring
    · intro hDA
      have hRan : AnalyticOnNhd ℂ
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) U := by
        intro z _
        exact (Complex.analyticOnNhd_univ_iff_differentiable.2
          (((contDiff_const.mul ((Polynomial.differentiable (jetModulus a m)).contDiff)).mul
            hinvG).differentiable (by simp))) z (Set.mem_univ z)
      have hDan : AnalyticOnNhd ℂ (fun z => G z + E z) U := hGan.add hEan
      have hFan : AnalyticOnNhd ℂ (fun z => (fun z => G z + E z) z +
          lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) U := hDan.add hRan
      have hDdA : DifferentiallyAlgebraicOn (fun z => G z + E z) U :=
        differentiallyAlgebraicOn_add hUo hUc hUne hUinf hGan hEan hGDA hEDA
      have hRDA : DifferentiallyAlgebraicOn
          (fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) U := by
        have hsub := differentiallyAlgebraicOn_sub hUo hUc hUne hUinf hFan hDan hDA hDdA
        have hfun : (fun z => ((fun z => G z + E z) z +
            lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹) - (fun z => G z + E z) z)
            = fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹ := by
          funext z
          ring
        rwa [hfun] at hsub
      have hinvDA : DifferentiallyAlgebraicOn (fun z => (Complex.Gamma z)⁻¹) U := by
        refine differentiallyAlgebraicOn_of_mul_polynomial
          (fun z _ => hinvG.contDiffAt) (a := Polynomial.C lam * jetModulus a m) ?_ ?_
        · exact mul_ne_zero (by simpa using hlam) (jetModulus_ne_zero a m)
        · have hfun : (fun z => (Polynomial.C lam * jetModulus a m).eval z *
              (Complex.Gamma z)⁻¹)
              = fun z => lam * (jetModulus a m).eval z * (Complex.Gamma z)⁻¹ := by
            funext z
            rw [Polynomial.eval_mul, Polynomial.eval_C]
          rw [hfun]
          exact hRDA
      exact not_differentiallyAlgebraicOn_invGamma hUo hUne hinvDA
    · exact (hGpo.add_flat (by simpa [hEdef] using flat_exp_neg_mul_polynomial Q)).add_flat
        (flat_polynomial_mul_invGamma lam (jetModulus a m))

/-- **The multiplier lemma.**  A nonvanishing analytic differentially algebraic multiplier divided
by `Γ` satisfies no algebraic differential equation: otherwise dividing back by the multiplier would
make `1/Γ` differentially algebraic. -/
theorem not_differentiallyAlgebraicOn_mul_invGamma {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite) {B : ℂ → ℂ}
    (hBan : AnalyticOnNhd ℂ B U) (hBne : ∀ z ∈ U, B z ≠ 0)
    (hBDA : DifferentiallyAlgebraicOn B U) :
    ¬ DifferentiallyAlgebraicOn (fun z => B z * (Complex.Gamma z)⁻¹) U := by
  intro h
  refine not_differentiallyAlgebraicOn_invGamma hUo hUne ?_
  have hinvGan : AnalyticOnNhd ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.2 Complex.differentiable_one_div_Gamma) z
      (Set.mem_univ z)
  have hprodan : AnalyticOnNhd ℂ (fun z : ℂ => B z * (Complex.Gamma z)⁻¹) U := hBan.mul hinvGan
  obtain ⟨n, P, hP0, hPv⟩ :=
    differentiallyAlgebraicOn_div hUo hUc hUne hUinf hprodan hBan hBne h hBDA
  refine ⟨n, P, hP0, fun z hz => ?_⟩
  have hev : (fun w : ℂ => B w * (Complex.Gamma w)⁻¹ / B w)
      =ᶠ[nhds z] fun w : ℂ => (Complex.Gamma w)⁻¹ := by
    filter_upwards [hUo.mem_nhds hz] with w hw
    have hbw : B w ≠ 0 := hBne w hw
    field_simp
  have hjets : ∀ j : ℕ,
      iteratedDeriv j (fun w : ℂ => B w * (Complex.Gamma w)⁻¹ / B w) z
        = iteratedDeriv j (fun w : ℂ => (Complex.Gamma w)⁻¹) z :=
    fun j => Filter.EventuallyEq.iteratedDeriv_eq j hev
  have hvec : (Fin.cons z (fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun w : ℂ => (Complex.Gamma w)⁻¹) z) : Fin (n + 2) → ℂ)
      = Fin.cons z (fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun w : ℂ => B w * (Complex.Gamma w)⁻¹ / B w) z) := by
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
        simp only [Fin.cons_succ]
        exact (hjets (j : ℕ)).symm
  rw [hvec]
  exact hPv z hz

/-! ### The rung witnesses `1/Γ(c z^q)` -/

/-- **Monomial rung witnesses.**  For every nonzero `c` and every positive exponent `q`, the
reciprocal Gamma function composed with the monomial `c z^q` satisfies no algebraic differential
equation: the monomial substitution is invertible on differential algebraicity, and `1/Γ` is
hypertranscendental. -/
theorem hypertranscendental_invGamma_comp_const_mul_pow {c : ℂ} (hc : c ≠ 0) {q : ℕ} (hq : 0 < q) :
    Hypertranscendental (fun z : ℂ => (Complex.Gamma (c * z ^ q))⁻¹) := by
  intro hDA
  refine hypertranscendental_invGamma ?_
  have hinvan : AnalyticOnNhd ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.2 Complex.differentiable_one_div_Gamma
  exact (HTGeometry.differentiallyAlgebraic_comp_const_mul_pow_iff hinvan hc hq).1 hDA

end

end GaloisForLFunctions.HTGeometry
