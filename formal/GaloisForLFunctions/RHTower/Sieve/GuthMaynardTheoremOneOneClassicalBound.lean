import GaloisForLFunctions.RHTower.WellSpacedSubset
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMajorant
import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues

/-!
# The classical large-values counts for a dyadic Dirichlet polynomial

Let `D(t) = Σ_{N<n≤2N} b_n n^{it}` with `|b_n| ≤ 1`, and let `W` be a `1`-separated set in an
interval of length `T` on which `|D| ≥ V`.  Then

* (mean value theorem, no logarithm) `|W| V² ≤ 627 (T + N) N` (`card_mul_sq_le_meanValue`);
* (Montgomery–Huxley) if `V² ≥ 18438 N √N`,
  `|W| V² ≤ 320 (1 + log(T + 1)) (6594624 T N⁴/V⁴ + N²)` (`card_mul_sq_le_huxley`).

Together they are the classical bound (1.2) of Guth–Maynard,
`R ⪅ N²V⁻² + T min(NV⁻², N⁴V⁻⁶)`.

The mean value count carries no `log N`: Gallagher's inequality (corpus `large_values_separated`)
is applied to the twisted polynomial `N^{-it} D(t) = Σ b_n (n/N)^{it}`, whose derivative has
coefficients `i log(n/N) b_n` of modulus at most `|b_n|`, and both second moments are bounded by the
log-free integral mean value theorem `∫_A^{A+U} |Σ_{n≤L} a_n n^{it}|² ≤ (U + 104 L) Σ|a_n|²`
(corpus `dirichlet_meanValue_sharp`, shifted to `[A, A + U]`).
-/

set_option autoImplicit false

open Finset Complex

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-! ### The dyadic polynomial -/

/-- The dyadic Dirichlet polynomial `D(t) = Σ_{N<n≤2N} b_n n^{it}` of Theorem 1.1. -/
def dyadicPoly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)

theorem dyadicPoly_eq_hbPoly (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    dyadicPoly N b t = hbPoly (Ioc N (2 * N)) b t := by
  unfold dyadicPoly hbPoly hbPhase
  refine sum_congr rfl fun n _ => ?_
  congr 2
  push_cast
  ring

theorem card_Ioc_two_mul (N : ℕ) : ((Ioc N (2 * N)).card : ℝ) = N := by
  rw [Nat.card_Ioc]
  norm_num [show 2 * N - N = N by omega]

/-- `Σ_{N<n≤2N} |b_n|² ≤ N` for `|b_n| ≤ 1`. -/
theorem sum_normSq_le_of_norm_le_one {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n ∈ Ioc N (2 * N), ‖b n‖ ≤ 1) :
    ∑ n ∈ Ioc N (2 * N), ‖b n‖ ^ 2 ≤ N := by
  calc ∑ n ∈ Ioc N (2 * N), ‖b n‖ ^ 2 ≤ ∑ _n ∈ Ioc N (2 * N), (1 : ℝ) :=
        sum_le_sum fun n hn => by nlinarith [hb n hn, norm_nonneg (b n)]
    _ = N := by rw [sum_const, nsmul_eq_mul, mul_one, card_Ioc_two_mul]

/-- The trivial bound `|D(t)| ≤ N`. -/
theorem norm_dyadicPoly_le {N : ℕ} {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) (t : ℝ) :
    ‖dyadicPoly N b t‖ ≤ N := by
  unfold dyadicPoly
  refine (norm_sum_le _ _).trans ?_
  calc ∑ n ∈ Ioc N (2 * N), ‖b n * Complex.exp (Complex.I * t * Real.log n)‖
      ≤ ∑ _n ∈ Ioc N (2 * N), (1 : ℝ) := sum_le_sum fun n _ => by
        rw [norm_mul, norm_exp_mul_log, mul_one]
        exact hb n
    _ = N := by rw [sum_const, nsmul_eq_mul, mul_one, card_Ioc_two_mul]

/-! ### The integral mean value theorem on any interval -/

/-- Shifting the variable twists the coefficients: `P_{S,a}(A + s) = P_{S, a n^{iA}}(s)`. -/
theorem hbPoly_add (S : Finset ℕ) (a : ℕ → ℂ) (A s : ℝ) :
    hbPoly S a (A + s) = hbPoly S (fun n => a n * hbPhase n A) s := by
  unfold hbPoly hbPhase
  refine sum_congr rfl fun n _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Integral mean value theorem without logarithm.**  For `S ⊆ [1, L]` and `U ≥ 0`:
`∫_A^{A+U} |Σ_{n∈S} a_n n^{it}|² dt ≤ (U + 104 L) Σ_{n∈S} |a_n|²`. -/
theorem integral_normSq_hbPoly_le {S : Finset ℕ} {L : ℕ} (hS : S ⊆ Icc 1 L) (a : ℕ → ℂ)
    (A U : ℝ) :
    ∫ t in A..A + U, ‖hbPoly S a t‖ ^ 2 ≤ (U + 104 * L) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin L → ℂ, c = fun i : Fin L =>
      if (i : ℕ) + 1 ∈ S then a ((i : ℕ) + 1) * hbPhase ((i : ℕ) + 1) A else 0 := ⟨_, rfl⟩
  -- the shifted polynomial is a `dirPoly` of length `L`
  have hpoly : ∀ s, ‖hbPoly S a (A + s)‖ ^ 2 = ‖dirPoly L c s‖ ^ 2 := fun s => by
    rw [hbPoly_add, hbPoly_eq_dirPoly hS, hc]
  have hshift : ∫ t in A..A + U, ‖hbPoly S a t‖ ^ 2 = ∫ s in (0 : ℝ)..U, ‖dirPoly L c s‖ ^ 2 := by
    have h := intervalIntegral.integral_comp_add_left (fun t => ‖hbPoly S a t‖ ^ 2) A
      (a := 0) (b := U)
    simp only [add_zero, hpoly] at h
    exact h.symm
  -- the coefficient energy is unchanged by the unimodular twist
  have hcoef : ∑ i : Fin L, ‖c i‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    have hfun : ∀ n, ‖(if n ∈ S then a n * hbPhase n A else 0)‖ ^ 2 =
        if n ∈ S then ‖a n‖ ^ 2 else 0 := fun n => by
      split_ifs <;> simp [norm_hbPhase]
    have h := RHTower.sum_fin_succ_eq_sum_Icc L
      (fun n => ‖(if n ∈ S then a n * hbPhase n A else 0)‖ ^ 2)
    simp only [hfun] at h
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS] at h
    rw [hc]
    simpa only [hfun] using h
  have hweight : ∑ m : Fin L, (((m : ℕ) : ℝ) + 1) * ‖c m‖ ^ 2 ≤ L * ∑ m : Fin L, ‖c m‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt m.isLt) (sq_nonneg _)
  have hmv := (abs_le.mp (dirichlet_meanValue_sharp L c U)).2
  rw [hshift, ← hcoef]
  nlinarith

/-! ### The twisted polynomial `N^{-it} D(t)` and its derivative -/

/-- `Σ_{n∈S} a_n (n/N)^{it}`, the polynomial `N^{-it} Σ_{n∈S} a_n n^{it}`. -/
def twistedPoly (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * Complex.exp (((t * (Real.log n - Real.log N) : ℝ) : ℂ) * Complex.I)

theorem norm_twistedPoly (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖twistedPoly N S a t‖ = ‖hbPoly S a t‖ := by
  have h : twistedPoly N S a t =
      Complex.exp (((-(t * Real.log N)) : ℝ) * Complex.I) * hbPoly S a t := by
    unfold twistedPoly hbPoly hbPhase
    rw [Finset.mul_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `d/dt Σ a_n (n/N)^{it} = Σ a_n i log(n/N) (n/N)^{it}`. -/
theorem hasDerivAt_twistedPoly (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (twistedPoly N S a)
      (twistedPoly N S (fun n => a n * (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I)) t) t := by
  have h := HasDerivAt.fun_sum (u := S)
    (A := fun n s => a n * Complex.exp (((s * (Real.log n - Real.log N) : ℝ) : ℂ) * Complex.I))
    (fun n _ => (hasDerivAt_exp_phase (Real.log n - Real.log N) t).const_mul (a n))
  refine h.congr_deriv ?_
  unfold twistedPoly
  exact sum_congr rfl fun n _ => by ring

theorem continuous_twistedPoly (N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    Continuous (twistedPoly N S a) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_twistedPoly N S a t).continuousAt

/-- On `(N, 2N]` the derivative weight `log(n/N)` lies in `[0, 1]`. -/
theorem abs_log_sub_log_le_one {N n : ℕ} (hn : n ∈ Ioc N (2 * N)) :
    |Real.log n - Real.log N| ≤ 1 := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by omega)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast h1.le
  have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast h2
  have hlo : Real.log N ≤ Real.log n := Real.log_le_log hN hNn
  have hhi : Real.log n ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hN.ne']
    exact Real.log_le_log (by linarith) hn2
  have h2 := Real.log_two_lt_d9
  rw [abs_of_nonneg (by linarith)]
  norm_num at h2
  linarith

/-! ### The mean value count -/

/-- **Mean value count without logarithm.**  If `|b_n| ≤ 1`, `W ⊂ [T₀, T₀ + T]` is
`1`-separated and `|D(t)| ≥ V` on `W`, then `|W| V² ≤ 627 (T + N) N`. -/
theorem card_mul_sq_le_meanValue {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖) :
    (W.card : ℝ) * V ^ 2 ≤ 627 * (T + N) * N := by
  set S := Ioc N (2 * N) with hSdef
  obtain ⟨b', hb'⟩ : ∃ b' : ℕ → ℂ,
      b' = fun n => b n * (((Real.log n - Real.log N : ℝ) : ℂ) * Complex.I) := ⟨_, rfl⟩
  have hS : S ⊆ Icc 1 (2 * N) := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
  have hf := continuous_twistedPoly N S b
  have hf' := continuous_twistedPoly N S b'
  have hderiv : ∀ y ∈ Set.Icc T₀ (T₀ + T + 1), HasDerivAt (twistedPoly N S b)
      (twistedPoly N S b' y) y := fun y _ => by
    rw [hb']
    exact hasDerivAt_twistedPoly N S b y
  have hgal := large_values_separated (P := W) (A := T₀) (B := T₀ + T) (η := 1) one_pos one_pos hV
    (by linarith) hW hsep hderiv
    ((continuous_const.mul (hf.inner hf')).intervalIntegrable _ _)
    ((hf.norm.pow 2).intervalIntegrable _ _) ((hf'.norm.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hf.norm.mul hf'.norm)).intervalIntegrable _ _)
    (fun x hx => by rw [norm_twistedPoly, ← dyadicPoly_eq_hbPoly]; exact hbig x hx)
  -- both second moments through the integral mean value theorem
  have hmass : ∑ n ∈ S, ‖b n‖ ^ 2 ≤ N := sum_normSq_le_of_norm_le_one fun n _ => hb n
  have hmass' : ∑ n ∈ S, ‖b' n‖ ^ 2 ≤ N := by
    refine le_trans (sum_le_sum fun n hn => ?_) hmass
    rw [hb', norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := abs_log_sub_log_le_one hn
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_of_le_one_right (norm_nonneg _) this) 2
  have hI : ∀ a : ℕ → ℂ, ∑ n ∈ S, ‖a n‖ ^ 2 ≤ N →
      ∫ u in T₀..T₀ + T + 1, ‖twistedPoly N S a u‖ ^ 2 ≤ (T + 1 + 208 * N) * N := by
    intro a ha
    have h := integral_normSq_hbPoly_le hS a T₀ (T + 1)
    simp only [norm_twistedPoly]
    rw [show T₀ + T + 1 = T₀ + (T + 1) by ring]
    push_cast at h
    calc _ ≤ (T + 1 + 104 * (2 * (N : ℝ))) * ∑ n ∈ S, ‖a n‖ ^ 2 := h
      _ ≤ (T + 1 + 208 * N) * N := by
        have : (0 : ℝ) ≤ T + 1 + 104 * (2 * (N : ℝ)) := by positivity
        nlinarith
  have h1 := hI b hmass
  have h2 := hI b' hmass'
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn : (0 : ℝ) ≤ N := by linarith
  have hbound : (T + 1 + 208 * N) * N ≤ 209 * (T + N) * N :=
    mul_le_mul_of_nonneg_right (by nlinarith) hNn
  norm_num at hgal
  linarith

/-! ### The Huxley count -/

/-- The conjugate of `D(t)` is the corpus block polynomial `Σ_{N+1≤n<2N+2} c_n n^{-it}` with
`c_n = conj b_n` on `(N, 2N]` and `c_{2N+1} = 0`. -/
theorem blockPoly_conj_eq (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    blockPoly (N + 1) (fun n => if n ≤ 2 * N then (starRingEnd ℂ) (b n) else 0) 0 t =
      (starRingEnd ℂ) (dyadicPoly N b t) := by
  classical
  unfold blockPoly dyadicPoly
  rw [map_sum]
  have hfilter : (Ico (N + 1) (2 * (N + 1))).filter (fun n => n ≤ 2 * N) = Ioc N (2 * N) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [← hfilter, Finset.sum_filter]
  refine sum_congr rfl fun n _ => ?_
  dsimp only
  by_cases h : n ≤ 2 * N
  · rw [if_pos h, if_pos h, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one, map_mul,
      ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  · rw [if_neg h, if_neg h, zero_mul, zero_mul]

/-- **Huxley count.**  If `|b_n| ≤ 1`, `W ⊂ [T₀, T₀ + T]` is `1`-separated, `|D(t)| ≥ V` on `W`
and `V² ≥ 18438 N √N`, then `|W| V² ≤ 320 (1 + log(T + 1)) (6594624 T N⁴/V⁴ + N²)`. -/
theorem card_mul_sq_le_huxley {N : ℕ} (hN : 1 ≤ N) {T T₀ V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    {b : ℕ → ℂ} (hb : ∀ n, ‖b n‖ ≤ 1) {W : Finset ℝ} (hW : ∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T)
    (hsep : IsSeparated 1 W) (hbig : ∀ t ∈ W, V ≤ ‖dyadicPoly N b t‖)
    (hthr : 18438 * (N : ℝ) * Real.sqrt N ≤ V ^ 2) :
    (W.card : ℝ) * V ^ 2 ≤
      320 * (1 + Real.log (T + 1)) * (6594624 * T * (N : ℝ) ^ 4 / V ^ 4 + (N : ℝ) ^ 2) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, c = fun n => if n ≤ 2 * N then (starRingEnd ℂ) (b n) else 0 :=
    ⟨_, rfl⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  -- the coefficient vector has energy at most `N + 1 ≤ 2N`
  have hmass : ‖blockCoeff (N + 1) c 0‖ ^ 2 ≤ 2 * N := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    calc ∑ j : Fin (N + 1), ‖(blockCoeff (N + 1) c 0).ofLp j‖ ^ 2 ≤ ∑ _j : Fin (N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => by
            have hcj : ‖c (N + 1 + j)‖ ≤ 1 := by
              rw [hc]; dsimp only; split_ifs
              · rw [Complex.norm_conj]; exact hb _
              · simp
            have : ‖(blockCoeff (N + 1) c 0).ofLp j‖ ≤ 1 := by
              simp only [blockCoeff, neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
              exact hcj
            nlinarith [norm_nonneg ((blockCoeff (N + 1) c 0).ofLp j)]
      _ = N + 1 := by simp
      _ ≤ 2 * N := by linarith
  have hbig' : ∀ x ∈ W, V ≤ ‖inner ℂ (dyadicDirRow (N + 1) x) (blockCoeff (N + 1) c 0)‖ :=
    fun x hx => by
      rw [inner_dyadicDirRow_blockCoeff, hc, blockPoly_conj_eq, Complex.norm_conj]
      exact hbig x hx
  have hspread : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ T := fun x hx y hy => by
    have := hW x hx; have := hW y hy
    rw [abs_le]; constructor <;> linarith
  -- the Huxley threshold
  have hsq : Real.sqrt (3 * ((N + 1 : ℕ) : ℝ) / (4 * Real.pi)) ≤ 2 * Real.sqrt N := by
    have hpi := Real.pi_gt_three
    have h4 : Real.sqrt (4 * N) = 2 * Real.sqrt N := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    rw [← h4]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hsqrt1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hthresh : 2 * (N : ℝ) * (1 + 1536 * Real.sqrt (3 * ((N + 1 : ℕ) : ℝ) / (4 * Real.pi))) ≤
      V ^ 2 / 3 := by
    have : 1 + 1536 * Real.sqrt (3 * ((N + 1 : ℕ) : ℝ) / (4 * Real.pi)) ≤ 3073 * Real.sqrt N := by
      linarith
    have hNn : (0 : ℝ) ≤ 2 * N := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hNn]
  have hH := huxley_large_values_finset_explicit_energy (by omega : 1 ≤ N + 1)
    (blockCoeff (N + 1) c 0) one_pos hV hT hmass W hsep hspread hbig' hthresh
  refine hH.trans ?_
  -- simplify the explicit right-hand side
  have hlog : 0 ≤ Real.log (T + 1) := Real.log_nonneg (by linarith)
  have hpi := Real.pi_lt_d2
  have hlogfac : 1 + 12 * Real.pi * (1 + Real.log (T + 1)) ≤ 40 * (1 + Real.log (T + 1)) := by
    norm_num at hpi
    nlinarith
  have hV4 : 0 < V ^ 4 := by positivity
  have hsecond : 2 * (2 * (N : ℝ)) * (((N + 1 : ℕ) : ℝ) + 12 * Real.pi * ((N + 1 : ℕ) : ℝ) / 1 *
      (1 + Real.log (T / 1 + 1))) ≤ 320 * (1 + Real.log (T + 1)) * (N : ℝ) ^ 2 := by
    rw [div_one, div_one]
    push_cast
    have hN2 : (N : ℝ) + 1 ≤ 2 * N := by linarith
    have e : (N : ℝ) + 1 + 12 * Real.pi * ((N : ℝ) + 1) * (1 + Real.log (T + 1)) =
        ((N : ℝ) + 1) * (1 + 12 * Real.pi * (1 + Real.log (T + 1))) := by ring
    rw [e]
    have := mul_le_mul hN2 hlogfac (by positivity) (by positivity)
    nlinarith
  have hfirst : T * (1284 * (2 * (N : ℝ))) ^ 2 / V ^ 4 + 1 =
      6594624 * T * (N : ℝ) ^ 2 / V ^ 4 + 1 := by ring
  rw [hfirst]
  calc (6594624 * T * (N : ℝ) ^ 2 / V ^ 4 + 1) *
        (2 * (2 * (N : ℝ)) * (((N + 1 : ℕ) : ℝ) + 12 * Real.pi * ((N + 1 : ℕ) : ℝ) / 1 *
          (1 + Real.log (T / 1 + 1))))
      ≤ (6594624 * T * (N : ℝ) ^ 2 / V ^ 4 + 1) * (320 * (1 + Real.log (T + 1)) * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsecond (by positivity)
    _ = 320 * (1 + Real.log (T + 1)) * (6594624 * T * (N : ℝ) ^ 4 / V ^ 4 + (N : ℝ) ^ 2) := by
        ring

end

end RHTower.GuthMaynard
