import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import GaloisForLFunctions.HTGeometry.DirichletConvolutionExponential
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Forward coefficients of a full-positive arithmetic source

For every full-positive source, the forward Dirichlet-exponential coefficients
have critical square energy `sum (norm a(n))^2 / n = O(log N)`. The proof
retains the signed logarithmic convolution when inserting these coefficients
into the Weil--Toeplitz form, then uses a finite logarithmic-moment induction.

No multiplicativity or coefficient-order premise is required. This energy
bound does not assert uniform boundedness of the zeta quotient.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Coefficients of the forward exponential, with the source truncated below two. -/
def forwardCoeff (lam : ℕ → ℝ) : ℕ → ℂ :=
  dirichletExp (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0))

@[simp] theorem forwardCoeff_zero (lam : ℕ → ℝ) : forwardCoeff lam 0 = 0 :=
  dirichletExp_zero

@[simp] theorem forwardCoeff_one (lam : ℕ → ℝ) : forwardCoeff lam 1 = 1 := by
  apply dirichletExp_one <;> simp [logZetaCoeff]

/-- Full positivity supplies the literal forward Dirichlet series on its
absolute half-plane, without coefficient ordering or multiplicativity. -/
theorem forwardCoeff_LSeries {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (forwardCoeff lam) s ∧
      LSeries (forwardCoeff lam) s =
        cexp (LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s) := by
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  apply LSeries_dirichletExp (by simp [logZetaCoeff]) (by simp [logZetaCoeff])
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  exact (abscissaOfAbsConv_logZetaCoeff_le hH.summable).trans_lt (by exact_mod_cast hs)

private theorem forwardCoeff_abscissa_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    LSeries.abscissaOfAbsConv (forwardCoeff lam) ≤ 1 := by
  have h := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
    (fun y hy => (forwardCoeff_LSeries hW (s := y) (by simpa using hy)).1)
  exact_mod_cast h

/-- The exact logarithmic convolution of the forward coefficients. -/
theorem forwardCoeff_log_convolution {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (n : ℕ) :
    LSeries.convolution (WeilHerglotz.lamC lam) (forwardCoeff lam) n =
      (Real.log n : ℂ) * forwardCoeff lam n := by
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have ha := forwardCoeff_abscissa_le hW
  have hlog : LSeries.abscissaOfAbsConv (LSeries.logMul (forwardCoeff lam)) < ⊤ := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact ha.trans_lt (EReal.coe_lt_top 1)
  have hconv : LSeries.abscissaOfAbsConv
      (LSeries.convolution (WeilHerglotz.lamC lam) (forwardCoeff lam)) < ⊤ := by
    have hLam : LSeriesSummable (WeilHerglotz.lamC lam) 2 :=
      WeilHerglotz.summable_term_lamC hW (by norm_num)
    have h := hLam.convolution
      (forwardCoeff_LSeries hW (s := 2) (by norm_num)).1
    exact h.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hid : (fun x : ℝ => LSeries
      (LSeries.convolution (WeilHerglotz.lamC lam) (forwardCoeff lam)) x) =ᶠ[atTop]
      fun x => LSeries (LSeries.logMul (forwardCoeff lam)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx' : 1 < (x : ℂ).re := by simpa using hx
    have hd := (hasDerivAt_LSeries_logZetaCoeff hH.summable (by simp) hx').cexp
    have heq : LSeries (forwardCoeff lam) =ᶠ[nhds (x : ℂ)]
        fun s => cexp (LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s) := by
      filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds hx'] with s hs
      exact (forwardCoeff_LSeries hW hs).2
    have hd' := hd.congr_of_eventuallyEq heq
    have hd'' := LSeries_hasDerivAt (s := (x : ℂ))
      (ha.trans_lt (by exact_mod_cast hx'))
    have hv := hd'.unique hd''
    rw [LSeries_convolution' (WeilHerglotz.summable_term_lamC hW hx')
      (forwardCoeff_LSeries hW hx').1, (forwardCoeff_LSeries hW hx').2]
    change LSeries (fun n => ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) x *
      cexp (LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) x) = _
    rw [mul_comm]
    exact neg_injective (by simpa only [mul_neg] using hv)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h := LSeries.eq_of_LSeries_eventually_eq hconv hlog hid hn.ne'
    simpa only [LSeries.logMul, ← Complex.ofReal_natCast,
      Complex.ofReal_log (Nat.cast_nonneg n)] using h

theorem forwardCoeff_ofReal_re (lam : ℕ → ℝ) (n : ℕ) :
    ((forwardCoeff lam n).re : ℂ) = forwardCoeff lam n := by
  let u : ℕ → ℝ := fun m => (if 2 ≤ m then lam m else 0) / Real.log m
  have hcast : ((∑ k ∈ Finset.range (n + 1),
      dirichletConvPow u k n / (k.factorial : ℝ) : ℝ) : ℂ) = forwardCoeff lam n := by
    change ((∑ k ∈ Finset.range (n + 1),
        dirichletConvPow u k n / (k.factorial : ℝ) : ℝ) : ℂ) =
      ∑ k ∈ Finset.range (n + 1),
        dirichletConvPow (fun m => (u m : ℂ)) k n / (k.factorial : ℂ)
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    rw [dirichletConvPow_ofReal]
  rw [← hcast]
  simp

private theorem forwardCoeff_log_convolution_re {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal,
      (if 2 ≤ p.1 then lam p.1 else 0) * (forwardCoeff lam p.2).re) =
        Real.log n * (forwardCoeff lam n).re := by
  have h := congrArg Complex.re (forwardCoeff_log_convolution hW n)
  simpa only [LSeries.convolution_def, Complex.re_sum, WeilHerglotz.lamC,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

private theorem sum_le_log_of_log_moment {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ N : ℕ, 1 ≤ N →
      2 * ∑ n ∈ Finset.Icc 1 N, Real.log n * w n ≤
        (Real.log N + C) * ∑ n ∈ Finset.Icc 1 N, w n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.Icc 1 N, w n ≤ K * (1 + Real.log N) := by
  let E (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, w n
  let S (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, Real.log n * w n
  let H (N : ℕ) : ℝ := Real.log N * E N - S N
  have hE0 (N : ℕ) : 0 ≤ E N := Finset.sum_nonneg fun n _ => hw n
  have hEmono {M N : ℕ} (h : M ≤ N) : E M ≤ E N := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans h⟩
    · intro n _ _
      exact hw n
  have hH0 (N : ℕ) (hN : 1 ≤ N) : 0 ≤ H N := by
    dsimp [H, E, S]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_nonneg
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    have hl : Real.log n ≤ Real.log N := Real.log_le_log
      (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hn'.2)
    nlinarith [hw n]
  have hmoment (N : ℕ) (hN : 1 ≤ N) :
      (Real.log N - C) * E N ≤ 2 * H N := by
    have h := hbound N hN
    change 2 * S N ≤ (Real.log N + C) * E N at h
    dsimp [H]
    linarith
  have hrec (N : ℕ) (hN : 1 ≤ N) :
      H (N + 1) = H N + (Real.log (N + 1) - Real.log N) * E N := by
    have he : E (N + 1) = E N + w (N + 1) :=
      Finset.sum_Icc_succ_top (by omega) w
    have hs : S (N + 1) = S N + Real.log (N + 1) * w (N + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1) (fun n => Real.log n * w n)
    simp only [H, he, hs, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (Real.exp (C + 1))
  have hN₀pos : 0 < N₀ := by
    exact_mod_cast (Real.exp_pos (C + 1)).trans hN₀
  have hN₀one : 1 ≤ N₀ := hN₀pos
  have hd₀ : 0 < Real.log N₀ - C := by
    have h := Real.log_lt_log (Real.exp_pos (C + 1)) hN₀
    rw [Real.log_exp] at h
    linarith
  let K₀ := H N₀ / (Real.log N₀ - C) ^ 2
  have hK₀ : 0 ≤ K₀ := div_nonneg (hH0 N₀ hN₀one) (sq_nonneg _)
  have hlarge : ∀ N : ℕ, N₀ ≤ N → H N ≤ K₀ * (Real.log N - C) ^ 2 := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      dsimp [K₀]
      rw [div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hd₀))]
    | succ N hN ih =>
      have hN1 : 1 ≤ N := hN₀one.trans hN
      have hd : 0 < Real.log N - C := by
        have h := Real.log_le_log (x := (N₀ : ℝ)) (y := (N : ℝ))
          (by exact_mod_cast hN₀pos) (by exact_mod_cast hN)
        linarith
      have hEn : E N ≤ 2 * K₀ * (Real.log N - C) := by
        apply le_of_mul_le_mul_left (a := Real.log N - C) _ hd
        calc
          (Real.log N - C) * E N ≤ 2 * H N := hmoment N hN1
          _ ≤ 2 * (K₀ * (Real.log N - C) ^ 2) := by linarith
          _ = (Real.log N - C) * (2 * K₀ * (Real.log N - C)) := by ring
      have hdelta : 0 ≤ Real.log (N + 1) - Real.log N := sub_nonneg.mpr
        (Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (by linarith))
      rw [hrec N hN1]
      have he := mul_le_mul_of_nonneg_left hEn hdelta
      have hsq := mul_nonneg hK₀ (sq_nonneg (Real.log (N + 1) - Real.log N))
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith
  have hEl (N : ℕ) (hN : N₀ ≤ N) : E N ≤ 2 * K₀ * (Real.log N - C) := by
    have hd : 0 < Real.log N - C := by
      have h := Real.log_le_log (x := (N₀ : ℝ)) (y := (N : ℝ))
        (by exact_mod_cast hN₀pos) (by exact_mod_cast hN)
      linarith
    apply le_of_mul_le_mul_left (a := Real.log N - C) _ hd
    have h := hmoment N (hN₀one.trans hN)
    have hh := hlarge N hN
    nlinarith
  refine ⟨E N₀ + 2 * K₀, add_nonneg (hE0 N₀) (mul_nonneg (by norm_num) hK₀),
    fun N hN => ?_⟩
  change E N ≤ (E N₀ + 2 * K₀) * (1 + Real.log N)
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  rcases le_total N₀ N with h | h
  · have hb := hEl N h
    have he := mul_nonneg (hE0 N₀) (show 0 ≤ 1 + Real.log N by linarith)
    have hc := mul_nonneg hK₀ hC
    nlinarith
  · have hb := hEmono h
    have he := mul_nonneg (hE0 N₀) hlog
    have hk := mul_nonneg hK₀ (show 0 ≤ 1 + Real.log N by linarith)
    nlinarith

/-- The exact forward-coefficient test of the Weil--Toeplitz ceiling. -/
theorem exists_forwardCoeff_log_moment_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      2 * ∑ n ∈ Finset.Icc 1 N, Real.log n * ‖forwardCoeff lam n‖ ^ 2 / n ≤
        (Real.log N + C) * ∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n‖ ^ 2 / n := by
  classical
  obtain ⟨C, hC⟩ := weil_multiplicativeToeplitz_bound (weilPositive_of_weilPositiveFull hW)
  refine ⟨max C 0, le_max_right _ _, fun N hN => ?_⟩
  let b : ℕ → ℝ := fun n => (forwardCoeff lam n).re
  have hb (n : ℕ) : ‖forwardCoeff lam n‖ ^ 2 = b n ^ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, b] using
      (congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (forwardCoeff_ofReal_re lam n)).symm
  let c : ℕ → ℂ := fun m => ((if m ≤ N then b m / Real.sqrt m else 0 : ℝ) : ℂ)
  let F : ℕ → ℕ → ℝ := fun n m =>
    (if 2 ≤ n then lam n else 0) * b (n * m) * b m / (n * m : ℕ)
  have hcN : ∀ m, N < m → c m = 0 := by
    intro m hm
    simp [c, not_le.mpr hm]
  have hcnorm (m : ℕ) (hm : m ∈ Finset.Icc 1 N) : ‖c m‖ ^ 2 = b m ^ 2 / m := by
    simp only [c, if_pos (Finset.mem_Icc.mp hm).2, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hpair (n m : ℕ) (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 N) :
      lam n / Real.sqrt n * (c (n * m) * conj (c m)).re =
        if n * m ≤ N then F n m else 0 := by
    by_cases hnm : n * m ≤ N
    · simp only [c, if_pos hnm, if_pos (Finset.mem_Icc.mp hm).2,
        Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, F, if_pos hn]
      have hden : Real.sqrt n * (Real.sqrt (n * m : ℕ) * Real.sqrt m) = (n * m : ℕ) := by
        rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg n)]
        calc
          _ = (Real.sqrt n) ^ 2 * (Real.sqrt m) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (Nat.cast_nonneg m)]
      simp only [div_mul_div_comm]
      rw [hden]
      ring
    · simp [c, hnm]
  have hrow (n : ℕ) (hn : n ∈ Finset.Icc 2 N) :
      lam n / Real.sqrt n * (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re =
        ∑ m ∈ Finset.Icc 1 (N / n), F n m := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hn0 : 0 < n := by omega
    have hsub : Finset.Icc 1 (N / n) ⊆ Finset.Icc 1 N := by
      intro m hm
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
        (Finset.mem_Icc.mp hm).2.trans (Nat.div_le_self N n)⟩
    rw [Complex.re_sum, Finset.mul_sum]
    calc
      _ = ∑ m ∈ Finset.Icc 1 N, if n * m ≤ N then F n m else 0 :=
        Finset.sum_congr rfl fun m hm => hpair n m hn2 hm
      _ = ∑ m ∈ Finset.Icc 1 (N / n), if n * m ≤ N then F n m else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro m hm hmn
        have hnm : ¬ n * m ≤ N := by
          intro h
          apply hmn
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
            (Nat.le_div_iff_mul_le hn0).mpr (by simpa only [Nat.mul_comm] using h)⟩
        simp [hnm]
      _ = _ := Finset.sum_congr rfl fun m hm => if_pos (by
        have h := (Nat.le_div_iff_mul_le hn0).mp (Finset.mem_Icc.mp hm).2
        simpa only [Nat.mul_comm] using h)
  have hdiag (k : ℕ) :
      (∑ p ∈ k.divisorsAntidiagonal, F p.1 p.2) = Real.log k * b k ^ 2 / k := by
    calc
      _ = b k / k * ∑ p ∈ k.divisorsAntidiagonal,
          (if 2 ≤ p.1 then lam p.1 else 0) * b p.2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
        dsimp [F]
        rw [hp']
        ring
      _ = _ := by rw [forwardCoeff_log_convolution_re hW]; dsimp [b]; ring
  have hleft :
      (∑ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
        (∑ m ∈ Finset.Icc 1 N, c (n * m) * conj (c m)).re) =
        ∑ k ∈ Finset.Icc 1 N, Real.log k * b k ^ 2 / k := by
    calc
      _ = ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 (N / n), F n m :=
        Finset.sum_congr rfl fun n hn => hrow n hn
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / n), F n m := by
        apply Finset.sum_subset
        · intro n hn
          have h := Finset.mem_Icc.mp hn
          exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
        · intro n hn hn'
          have hn1 : n = 1 := by
            simp only [Finset.mem_Icc, not_and, not_le] at hn hn'
            omega
          subst n
          simp [F]
      _ = ∑ k ∈ Finset.Icc 1 N, ∑ p ∈ k.divisorsAntidiagonal, F p.1 p.2 :=
        (Sieve.sum_Icc_divisorsAntidiagonal_swap F N).symm
      _ = _ := Finset.sum_congr rfl fun k _ => hdiag k
  have ht := hC N hN c hcN
  rw [hleft, Finset.sum_congr rfl hcnorm] at ht
  simp only [hb]
  exact ht.trans (mul_le_mul_of_nonneg_right
    (add_le_add_right (le_max_left C 0) _) (Finset.sum_nonneg fun m _ =>
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg m)))

/-- Full positivity bounds the critical weighted square energy of the
literal forward coefficients by a single logarithm. -/
theorem exists_forwardCoeff_critical_energy_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n‖ ^ 2 / n ≤ K * (1 + Real.log N) := by
  obtain ⟨C, hC, hbound⟩ := exists_forwardCoeff_log_moment_le hW
  apply sum_le_log_of_log_moment (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)) hC
  intro N hN
  simpa only [mul_div_assoc] using hbound N hN

end RHTower.WeilSingularArithmetic
