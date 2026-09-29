import GaloisForLFunctions.RHTower.MobiusHilbertFormCriterion

/-!
# A logarithmic Hilbert bound forces the weak Mertens bound pointwise

Let `F_N(x) = Σ_{n ≤ N} μ(n) e^{-nx}` and `E_N = ∫_0^∞ F_N² = Σ_{m,n ≤ N} μ(m)μ(n)/(m+n)`.
With `q = e^{-x}`, Abel summation gives the exact identity

`F_N(x) = M(N) q^N + (1 - q) Σ_{k<N} M(k) q^k`.

On `(0, 1/(4N)]` the first term is at least `(3/4)|M(N)|`.  If every earlier `|M(k)|` is at
most `|M(N)|`, the second term is at most `|M(N)|/4`.  So `F_N² ≥ M(N)²/4` on an interval of
length `1/(4N)`, and `E_N ≥ M(N)²/(16N)`.  Strong induction on `N` then gives:

if `E_N ≤ C(1 + log N)` for every `N`, then `M(N)² ≤ (16C + 1) N (1 + log N)` for every `N`.

Hilbert sub-orthogonality (nonpositive off-diagonal part for every `N`) gives `E_N ≤ (1+log N)/2`.
It therefore forces `|M(N)| ≤ 3 √(N(1 + log N))`, a pointwise weak Mertens bound that is not
known to follow from the Riemann hypothesis.  The subpolynomial Hilbert target is equivalent to
RH; the logarithmic one lies strictly beyond it.

The same floor works for the Γ--Hankel energies `E_N(r) = ∫_0^∞ x^{r-1} F_N²`: on `(0, 1/(4N)]`
it gives `E_N(r) ≥ M(N)²/(4r(4N)^r)`.  Sub-orthogonality on a band `(1, 2σ₀)` bounds `E_N(r)` by
the diagonal `≤ (1 + log N)/2` at `r = 1 + 1/(1+log N)`, where `(4N)^r ≤ 16N`.  So the band form of
sub-orthogonality also forces `M(N)² ≪ N log N`.

Below the Hilbert exponent the diagonal is only `O(N^{1-r})`, and sub-orthogonality at one fixed
`r ∈ (0, 1)` forces `M(N) = O(√N)`.  That is the strength of the Mertens conjecture; by Ingham it
is incompatible with linear independence of the zeta ordinates.  So `r = 1` is the critical
exponent for Möbius sign laws.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- The Mertens sum `M(N) = Σ_{n ≤ N} μ(n)` in shifted indexing. -/
def shiftedMertensReal (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n

/-- The shifted Mertens sum is the Mertens function. -/
theorem shiftedMertensReal_eq (N : ℕ) :
    shiftedMertensReal N = ∑ n ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_right, shiftedMertensReal, shiftedMobiusRealCoefficient]
  exact Finset.sum_congr rfl fun n _ => by rw [add_comm]

/-- Abel summation for the shifted Möbius coefficients against the powers `q^{n+1}`. -/
theorem sum_range_shiftedMobius_mul_pow_eq_abel (N : ℕ) (q : ℝ) :
    ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n * q ^ (n + 1) =
      shiftedMertensReal N * q ^ N +
        (1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k := by
  induction N with
  | zero => simp [shiftedMertensReal]
  | succ N ih =>
    have hM : shiftedMertensReal (N + 1) =
        shiftedMertensReal N + shiftedMobiusRealCoefficient N := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, ih, hM, Finset.sum_range_succ]
    ring

/-- **Abel form of the pencil.**  `F_N(x) = M(N)q^N + (1-q)Σ_{k<N} M(k)q^k`, `q = e^{-x}`. -/
theorem finiteMobiusLaplacePencil_eq_abel (N : ℕ) (x : ℝ) :
    finiteMobiusLaplacePencil N x =
      shiftedMertensReal N * Real.exp (-x) ^ N +
        (1 - Real.exp (-x)) *
          ∑ k ∈ Finset.range N, shiftedMertensReal k * Real.exp (-x) ^ k := by
  rw [finiteMobiusLaplacePencil_eq, sum_range_shiftedMobius_mul_pow_eq_abel]

/-- A pointwise floor `F_N² ≥ m²` on `(0, b]` gives the energy floor `E_N ≥ b m²`. -/
theorem finiteMobiusGammaHankelEnergy_one_ge_of_sq_le {N : ℕ} {b m : ℝ} (hb : 0 ≤ b)
    (hm : ∀ x ∈ Ioc (0 : ℝ) b, m ^ 2 ≤ finiteMobiusLaplacePencil N x ^ 2) :
    b * m ^ 2 ≤ finiteMobiusGammaHankelEnergy N 1 := by
  have hInt := integrableOn_sq_finiteMobiusLaplacePencil N
  rw [← integral_sq_finiteMobiusLaplacePencil]
  calc b * m ^ 2 = ∫ _ in Ioc (0 : ℝ) b, m ^ 2 := by
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hb, sub_zero, smul_eq_mul]
    _ ≤ ∫ x in Ioc (0 : ℝ) b, finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_on (integrableOn_const (by simp)) (hInt.mono_set Ioc_subset_Ioi_self)
          measurableSet_Ioc hm
    _ ≤ ∫ x in Ioi (0 : ℝ), finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_set hInt (ae_of_all _ fun x => sq_nonneg _)
          Ioc_subset_Ioi_self.eventuallyLE

/-- If `|M(N)| = a` dominates every earlier `|M(k)|`, then `|F_N(x)| ≥ a/2` whenever
`0 < x` and `Nx ≤ 1/4`. -/
theorem half_le_abs_finiteMobiusLaplacePencil {N : ℕ} {a x : ℝ}
    (hMN : |shiftedMertensReal N| = a) (hMk : ∀ k < N, |shiftedMertensReal k| ≤ a)
    (hx : 0 < x) (hNx : (N : ℝ) * x ≤ 1 / 4) :
    a / 2 ≤ |finiteMobiusLaplacePencil N x| := by
  set q := Real.exp (-x) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha0 : 0 ≤ a := hMN ▸ abs_nonneg _
  have hqN : 3 / 4 ≤ q ^ N := by
    rw [hq, ← Real.exp_nat_mul]
    have h1 := Real.add_one_le_exp (-(1 / 4 : ℝ))
    have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (N * -x) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h1q : 1 - q ≤ x := by
    have := Real.add_one_le_exp (-x)
    rw [hq]
    linarith
  have h1q0 : 0 ≤ 1 - q := by linarith
  have hS : |∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ N * a := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Finset.range N, |shiftedMertensReal k * q ^ k|
        ≤ ∑ _k ∈ Finset.range N, a := Finset.sum_le_sum fun k hk => by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 k)]
          exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq0 hq1)).trans
            (hMk k (Finset.mem_range.mp hk))
      _ = N * a := by simp
  have hmain : 3 / 4 * a ≤ |shiftedMertensReal N * q ^ N| := by
    rw [abs_mul, hMN, abs_of_nonneg (pow_nonneg hq0 N)]
    nlinarith
  have htail : |(1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ a / 4 := by
    rw [abs_mul, abs_of_nonneg h1q0]
    calc (1 - q) * |∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k| ≤ x * (N * a) :=
          mul_le_mul h1q hS (abs_nonneg _) hx.le
      _ = (N * x) * a := by ring
      _ ≤ 1 / 4 * a := mul_le_mul_of_nonneg_right hNx ha0
      _ = a / 4 := by ring
  rw [finiteMobiusLaplacePencil_eq_abel]
  have htri := abs_add_le (shiftedMertensReal N * q ^ N +
      (1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k)
    (-((1 - q) * ∑ k ∈ Finset.range N, shiftedMertensReal k * q ^ k))
  rw [add_neg_cancel_right, abs_neg] at htri
  linarith

/-- **Logarithmic Hilbert energy forces the weak Mertens bound.**  If
`Σ_{m,n ≤ N} μ(m)μ(n)/(m+n) ≤ C(1 + log N)` for every `N`, then
`M(N)² ≤ (16C + 1) N (1 + log N)` for every `N`. -/
theorem shiftedMertensReal_sq_le_of_hilbert_log_le {C : ℝ}
    (h : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ C * (1 + Real.log N)) (N : ℕ) :
    shiftedMertensReal N ^ 2 ≤ (16 * C + 1) * N * (1 + Real.log N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [shiftedMertensReal]
  by_contra hlt
  rw [not_le] at hlt
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set a := |shiftedMertensReal N| with ha
  have ha2 : a ^ 2 = shiftedMertensReal N ^ 2 := sq_abs _
  have hmono : ∀ k < N, (k : ℝ) * (1 + Real.log k) ≤ N * (1 + Real.log N) := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [CharP.cast_eq_zero, zero_mul]
      positivity
    have hk1 : (0 : ℝ) < k := by exact_mod_cast hk0
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    exact mul_le_mul hkN (by linarith [Real.log_le_log hk1 hkN]) (by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk0)]) hNpos.le
  have hC : 0 ≤ C := by
    have h0 := h 0
    simp [finiteMobiusGammaHankelEnergy_zero] at h0
    exact h0
  have hK0 : 0 ≤ 16 * C + 1 := by linarith
  have hMk : ∀ k < N, |shiftedMertensReal k| ≤ a := by
    intro k hk
    have h1 := ih k hk
    have h2 : (16 * C + 1) * k * (1 + Real.log k) ≤ (16 * C + 1) * N * (1 + Real.log N) := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmono k hk) hK0
    have h3 : shiftedMertensReal k ^ 2 ≤ a ^ 2 := by linarith
    have := sq_le_sq.mp h3
    rwa [abs_of_nonneg (abs_nonneg _)] at this
  have hfloor : ∀ x ∈ Ioc (0 : ℝ) (1 / (4 * N)), (a / 2) ^ 2 ≤ finiteMobiusLaplacePencil N x ^ 2 := by
    intro x hx
    have hNx : (N : ℝ) * x ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hx.2 hNpos.le
      calc (N : ℝ) * x ≤ N * (1 / (4 * N)) := this
        _ = 1 / 4 := by field_simp
    have hhalf := half_le_abs_finiteMobiusLaplacePencil ha.symm hMk hx.1 hNx
    have ha0 : 0 ≤ a / 2 := by positivity
    rw [← sq_abs (finiteMobiusLaplacePencil N x)]
    exact pow_le_pow_left₀ ha0 hhalf 2
  have hE := finiteMobiusGammaHankelEnergy_one_ge_of_sq_le (by positivity) hfloor
  have hEN := h N
  have key : 1 / (4 * N) * (a / 2) ^ 2 = a ^ 2 / (16 * N) := by
    field_simp
    ring
  rw [key] at hE
  have hbig : (16 * C + 1) * N * (1 + Real.log N) / (16 * N) < a ^ 2 / (16 * N) :=
    div_lt_div_of_pos_right (by rw [ha2]; exact hlt) (by positivity)
  have hsimp : (16 * C + 1) * N * (1 + Real.log N) / (16 * N) =
      (16 * C + 1) * (1 + Real.log N) / 16 := by
    field_simp
  rw [hsimp] at hbig
  nlinarith

/-- **Hilbert sub-orthogonality lies beyond RH.**  A nonpositive off-diagonal Möbius Hilbert
form for every `N` forces `M(N)² ≤ 9N(1 + log N)`. -/
theorem shiftedMertensReal_sq_le_of_mobiusHilbertSubOrthogonal
    (h : ∀ N : ℕ, finiteMobiusGammaHankelOffDiagonalCovariance N 1 ≤ 0) (N : ℕ) :
    shiftedMertensReal N ^ 2 ≤ 9 * N * (1 + Real.log N) := by
  have hlog : ∀ N : ℕ, finiteMobiusGammaHankelEnergy N 1 ≤ 1 / 2 * (1 + Real.log N) := by
    intro N
    rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
    have h1 := finiteMobiusGammaHankelDiagonalEnergy_one_le N
    linarith [h N]
  have := shiftedMertensReal_sq_le_of_hilbert_log_le hlog N
  norm_num at this ⊢
  linarith

/-- `Γ ≤ 1` on `[1, 2]`, by convexity and `Γ(1) = Γ(2) = 1`. -/
theorem gamma_le_one_of_mem_Icc {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2) : Real.Gamma r ≤ 1 := by
  have hc := Real.convexOn_Gamma.2 (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Ioi 0 by norm_num) (show 0 ≤ 2 - r by linarith) (show 0 ≤ r - 1 by linarith)
    (by ring)
  simp only [smul_eq_mul, Real.Gamma_one, Real.Gamma_two] at hc
  have : (2 - r) * 1 + (r - 1) * 2 = r := by ring
  rw [this] at hc
  linarith

/-- For `1 ≤ r ≤ 2` the Γ--Hankel diagonal `Γ(r)Σ_{n≤N} μ(n)²/(2n)^r` is at most `(1+log N)/2`. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_le_of_one_le {r : ℝ} (h1 : 1 ≤ r) (h2 : r ≤ 2)
    (N : ℕ) : finiteMobiusGammaHankelDiagonalEnergy N r ≤ (1 + Real.log N) / 2 := by
  have hD1 := finiteMobiusGammaHankelDiagonalEnergy_one_le N
  unfold finiteMobiusGammaHankelDiagonalEnergy at hD1 ⊢
  rw [Real.Gamma_one, one_mul] at hD1
  have hsum : ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n ^ 2 /
      (((2 * (n + 1) : ℕ) : ℝ) ^ r) ≤ ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n ^ 2 /
      (((2 * (n + 1) : ℕ) : ℝ) ^ (1 : ℝ)) := by
    refine Finset.sum_le_sum fun n _ => ?_
    have hb : (1 : ℝ) ≤ ((2 * (n + 1) : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * (n + 1) := by omega
      exact_mod_cast this
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (Real.rpow_le_rpow_of_exponent_le hb h1)
  have hG := gamma_le_one_of_mem_Icc h1 h2
  have hG0 : 0 ≤ Real.Gamma r := (Real.Gamma_pos_of_pos (by linarith)).le
  have hs0 : 0 ≤ ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n ^ 2 /
      (((2 * (n + 1) : ℕ) : ℝ) ^ r) :=
    Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
  calc Real.Gamma r * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hG hs0
    _ ≤ _ := by rw [one_mul]; exact hsum.trans hD1

/-- A pointwise floor `F_N² ≥ m²` on `(0, b]` gives `E_N(r) ≥ (b^r/r) m²`. -/
theorem finiteMobiusGammaHankelEnergy_ge_of_sq_le {N : ℕ} {r b m : ℝ} (hr : 0 < r)
    (hb : 0 ≤ b) (hm : ∀ x ∈ Ioc (0 : ℝ) b, m ^ 2 ≤ finiteMobiusLaplacePencil N x ^ 2) :
    b ^ r / r * m ^ 2 ≤ finiteMobiusGammaHankelEnergy N r := by
  have hInt := integrableOn_rpow_mul_sq_finiteMobiusLaplacePencil N hr
  rw [← integral_finiteMobiusLaplacePencil_sq N hr]
  have hpow : IntegrableOn (fun x : ℝ => x ^ (r - 1)) (Ioc 0 b) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hconst : ∫ x in Ioc (0 : ℝ) b, x ^ (r - 1) * m ^ 2 = b ^ r / r * m ^ 2 := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hb,
      integral_rpow (Or.inl (by linarith))]
    simp [Real.zero_rpow hr.ne']
  calc b ^ r / r * m ^ 2 = ∫ x in Ioc (0 : ℝ) b, x ^ (r - 1) * m ^ 2 := hconst.symm
    _ ≤ ∫ x in Ioc (0 : ℝ) b, x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_on (hpow.mul_const _) (hInt.mono_set Ioc_subset_Ioi_self)
          measurableSet_Ioc fun x hx =>
            mul_le_mul_of_nonneg_left (hm x hx) (Real.rpow_nonneg hx.1.le _)
    _ ≤ ∫ x in Ioi (0 : ℝ), x ^ (r - 1) * finiteMobiusLaplacePencil N x ^ 2 :=
        setIntegral_mono_set hInt
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
              exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (sq_nonneg _))
          Ioc_subset_Ioi_self.eventuallyLE

/-- At the exponent `r = 1 + 1/(1 + log N)` the scale factor is harmless: `(4N)^r ≤ 16N`. -/
theorem four_mul_rpow_one_add_inv_le {N : ℕ} (hN : 1 ≤ N) :
    ((4 * N : ℝ)) ^ (1 + 1 / (1 + Real.log N)) ≤ 16 * N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h4N : (0 : ℝ) < 4 * N := by positivity
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlog4 : 1 ≤ Real.log 4 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_gt_d9]
  rw [Real.rpow_add h4N, Real.rpow_one, Real.rpow_def_of_pos h4N,
    Real.log_mul (by norm_num) (by positivity)]
  have hexp : (Real.log 4 + Real.log N) * (1 / (1 + Real.log N)) ≤ Real.log 4 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  have := Real.exp_le_exp.mpr hexp
  rw [Real.exp_log (by norm_num)] at this
  nlinarith

/-- The trivial bound `|M(N)| ≤ N`. -/
theorem abs_shiftedMertensReal_le (N : ℕ) : |shiftedMertensReal N| ≤ N := by
  unfold shiftedMertensReal
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ Finset.range N, |shiftedMobiusRealCoefficient n| ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => by
          unfold shiftedMobiusRealCoefficient
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = N := by simp

/-- **Γ--Hankel sub-orthogonality lies beyond RH.**  If the off-diagonal Γ--Hankel covariance is
nonpositive for every cutoff and every exponent in a band `(1, 2σ₀)`, then
`M(N)² ≤ K N (1 + log N)` for every `N`.  At cutoff `N` the proof uses the exponent
`r = 1 + 1/(1 + log N)`, where the diagonal is at most `(1+log N)/2` and `(4N)^r ≤ 16N`. -/
theorem exists_shiftedMertensReal_sq_le_of_mobiusGammaHankelSubOrthogonal
    (h : MobiusGammaHankelSubOrthogonal) :
    ∃ K : ℝ, ∀ N : ℕ, shiftedMertensReal N ^ 2 ≤ K * N * (1 + Real.log N) := by
  obtain ⟨σ₀, hσ₀, hSO⟩ := h
  set δ := min (σ₀ - 1 / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδσ : δ ≤ σ₀ - 1 / 2 := min_le_left _ _
  set N₀ : ℕ := ⌈Real.exp (1 / (2 * δ))⌉₊ with hN₀
  have hthr : ∀ N : ℕ, N₀ < N → 1 / (1 + Real.log N) < 2 * δ := by
    intro N hN
    have hNreal : Real.exp (1 / (2 * δ)) < N :=
      lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hN)
    have hlog : 1 / (2 * δ) < Real.log N :=
      (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos _) hNreal)).mpr hNreal
    have hpos : 0 < 1 / (2 * δ) := by positivity
    calc 1 / (1 + Real.log N) < 1 / (1 / (2 * δ)) :=
          one_div_lt_one_div_of_lt hpos (by linarith)
      _ = 2 * δ := by field_simp
  refine ⟨max 64 N₀, fun N => ?_⟩
  set K : ℝ := max 64 N₀ with hK
  have hK64 : (64 : ℝ) ≤ K := le_max_left _ _
  have hKN₀ : (N₀ : ℝ) ≤ K := le_max_right _ _
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [shiftedMertensReal]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  set L := 1 + Real.log N with hL
  have hL1 : 1 ≤ L := by linarith
  rcases le_or_gt N N₀ with hsmall | hbig
  · have hM := abs_shiftedMertensReal_le N
    have hsq : shiftedMertensReal N ^ 2 ≤ (N : ℝ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hM 2
    have hNN₀ : (N : ℝ) ≤ N₀ := by exact_mod_cast hsmall
    calc shiftedMertensReal N ^ 2 ≤ (N : ℝ) ^ 2 := hsq
      _ = (N : ℝ) * N := by ring
      _ ≤ K * N := mul_le_mul_of_nonneg_right (hNN₀.trans hKN₀) hNpos.le |>.trans_eq' (by ring)
      _ ≤ K * N * L := by
          have : 0 ≤ K * N := by positivity
          nlinarith
  by_contra hlt
  rw [not_le] at hlt
  set a := |shiftedMertensReal N| with ha
  have ha2 : a ^ 2 = shiftedMertensReal N ^ 2 := sq_abs _
  have hMk : ∀ k < N, |shiftedMertensReal k| ≤ a := by
    intro k hk
    have h1 := ih k hk
    have hmono : (k : ℝ) * (1 + Real.log k) ≤ N * L := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · simp only [CharP.cast_eq_zero, zero_mul]
        positivity
      have hk1 : (0 : ℝ) < k := by exact_mod_cast hk0
      have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
      exact mul_le_mul hkN (by linarith [Real.log_le_log hk1 hkN]) (by
        linarith [Real.log_nonneg (show (1 : ℝ) ≤ k by exact_mod_cast hk0)]) hNpos.le
    have hK0 : 0 ≤ K := by linarith
    have h2 : K * k * (1 + Real.log k) ≤ K * N * L := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left hmono hK0
    have h3 : shiftedMertensReal k ^ 2 ≤ a ^ 2 := by linarith
    have := sq_le_sq.mp h3
    rwa [abs_of_nonneg (abs_nonneg _)] at this
  set r : ℝ := 1 + 1 / L with hr
  have hLinv : 0 < 1 / L := by positivity
  have hLinv1 : 1 / L ≤ 1 := by rw [div_le_one (by linarith)]; exact hL1
  have hr1 : 1 ≤ r := by linarith
  have hr2 : r ≤ 2 := by linarith
  have hrpos : 0 < r := by linarith
  have hσ1 : 1 / 2 < r / 2 := by linarith
  have hσ2 : r / 2 < σ₀ := by
    have := hthr N hbig
    rw [← hL] at this
    linarith
  have hO := hSO (r / 2) hσ1 hσ2 N
  rw [show 2 * (r / 2) = r by ring] at hO
  have hE : finiteMobiusGammaHankelEnergy N r ≤ L / 2 := by
    rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
    have := finiteMobiusGammaHankelDiagonalEnergy_le_of_one_le hr1 hr2 N
    rw [← hL] at this
    linarith
  have hfloor : ∀ x ∈ Ioc (0 : ℝ) (1 / (4 * N)),
      (a / 2) ^ 2 ≤ finiteMobiusLaplacePencil N x ^ 2 := by
    intro x hx
    have hNx : (N : ℝ) * x ≤ 1 / 4 := by
      calc (N : ℝ) * x ≤ N * (1 / (4 * N)) := mul_le_mul_of_nonneg_left hx.2 hNpos.le
        _ = 1 / 4 := by field_simp
    have hhalf := half_le_abs_finiteMobiusLaplacePencil ha.symm hMk hx.1 hNx
    rw [← sq_abs (finiteMobiusLaplacePencil N x)]
    exact pow_le_pow_left₀ (by positivity) hhalf 2
  have hEge := finiteMobiusGammaHankelEnergy_ge_of_sq_le hrpos (by positivity) hfloor
  have hpow : ((4 * N : ℝ)) ^ r ≤ 16 * N := by
    rw [hr, hL]; exact four_mul_rpow_one_add_inv_le hN
  have hbr : (1 / (4 * N : ℝ)) ^ r = 1 / ((4 * N : ℝ)) ^ r := by
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow]
  rw [hbr] at hEge
  have hpowpos : (0 : ℝ) < ((4 * N : ℝ)) ^ r := by positivity
  have hlow : a ^ 2 / (128 * N) ≤ 1 / ((4 * N : ℝ)) ^ r / r * (a / 2) ^ 2 := by
    rw [div_div, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    have : ((4 * N : ℝ)) ^ r * r ≤ 16 * N * 2 :=
      mul_le_mul hpow hr2 hrpos.le (by positivity)
    nlinarith [sq_nonneg a]
  have hfin : a ^ 2 / (128 * N) ≤ L / 2 := hlow.trans (hEge.trans hE)
  rw [div_le_iff₀ (by positivity)] at hfin
  have : K * N * L < a ^ 2 := by rw [ha2]; exact hlt
  nlinarith


private theorem rpow_neg_mul_le_sub (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    ((N : ℝ) + 1) ^ (-r) * (1 - r) ≤ ((N : ℝ) + 1) ^ (1 - r) - (N : ℝ) ^ (1 - r) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - r) (w₂ := r)
    (p₁ := (N : ℝ)) (p₂ := (N : ℝ) + 1) (by linarith) hr0.le hN0 ha.le (by ring)
  have hmul : ((N : ℝ) + 1) ^ (-r) * ((N : ℝ) + 1) ^ r = 1 := by
    rw [← Real.rpow_add ha]; simp
  have hsplit : ((N : ℝ) + 1) ^ (1 - r) = ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (-r) := by
    rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
  have hpos : 0 ≤ ((N : ℝ) + 1) ^ (-r) := Real.rpow_nonneg ha.le _
  have h2 : (N : ℝ) ^ (1 - r) = (N : ℝ) ^ (1 - r) * ((N : ℝ) + 1) ^ r * ((N : ℝ) + 1) ^ (-r) := by
    rw [mul_assoc, mul_comm (((N : ℝ) + 1) ^ r), hmul, mul_one]
  rw [hsplit, h2]
  have : (N : ℝ) ^ (1 - r) * ((N : ℝ) + 1) ^ r ≤ N + r := by nlinarith
  nlinarith

/-- `Σ_{n ≤ N} n^{-r} ≤ N^{1-r}/(1-r)` for `0 < r < 1`, via weighted AM--GM on each step. -/
theorem sum_range_rpow_neg_le (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-r) ≤ ((N : ℝ)) ^ (1 - r) / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  induction N with
  | zero => simp [Real.zero_rpow (by linarith : (1 - r) ≠ 0)]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have key := rpow_neg_mul_le_sub r hr0 hr1 N
    push_cast
    rw [le_div_iff₀ h1r] at ih ⊢
    rw [add_mul]
    linarith

/-- Below the Hilbert exponent the diagonal is `O(N^{1-r})`. -/
theorem finiteMobiusGammaHankelDiagonalEnergy_le_of_lt_one {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (N : ℕ) : finiteMobiusGammaHankelDiagonalEnergy N r ≤
      Real.Gamma r * (2 : ℝ) ^ (-r) * ((N : ℝ) ^ (1 - r) / (1 - r)) := by
  unfold finiteMobiusGammaHankelDiagonalEnergy
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.Gamma_pos_of_pos hr0).le
  calc ∑ n ∈ Finset.range N, shiftedMobiusRealCoefficient n ^ 2 / (((2 * (n + 1) : ℕ) : ℝ) ^ r)
      ≤ ∑ n ∈ Finset.range N, (2 : ℝ) ^ (-r) * ((n : ℝ) + 1) ^ (-r) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hsq : shiftedMobiusRealCoefficient n ^ 2 ≤ 1 := by
          have h1 : |shiftedMobiusRealCoefficient n| ≤ 1 := by
            unfold shiftedMobiusRealCoefficient
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          nlinarith [abs_nonneg (shiftedMobiusRealCoefficient n),
            sq_abs (shiftedMobiusRealCoefficient n)]
        have hpos : (0 : ℝ) < ((2 * (n + 1) : ℕ) : ℝ) ^ r := by positivity
        have heq : (2 : ℝ) ^ (-r) * ((n : ℝ) + 1) ^ (-r) = 1 / (((2 * (n + 1) : ℕ) : ℝ) ^ r) := by
          push_cast
          rw [← Real.mul_rpow (by norm_num) (by positivity), Real.rpow_neg (by positivity),
            one_div]
        rw [heq]
        exact div_le_div_of_nonneg_right hsq hpos.le
    _ = (2 : ℝ) ^ (-r) * ∑ n ∈ Finset.range N, ((n : ℝ) + 1) ^ (-r) := by rw [Finset.mul_sum]
    _ ≤ (2 : ℝ) ^ (-r) * ((N : ℝ) ^ (1 - r) / (1 - r)) :=
        mul_le_mul_of_nonneg_left (sum_range_rpow_neg_le r hr0 hr1 N) (by positivity)

/-- **Sub-orthogonality below the Hilbert exponent has Mertens-conjecture strength.**  If for one
`r ∈ (0, 1)` the off-diagonal Γ--Hankel covariance is nonpositive for every cutoff, then
`M(N)² ≤ K N` for every `N`, i.e. `M(N) = O(√N)`.  At a record, `E_N(r) ≥ M(N)²/(4r(4N)^r)`, while
the diagonal is `≤ Γ(r)2^{-r}N^{1-r}/(1-r)`. -/
theorem exists_shiftedMertensReal_sq_le_mul_of_offDiagonal_nonpos {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (h : ∀ N : ℕ, finiteMobiusGammaHankelOffDiagonalCovariance N r ≤ 0) :
    ∃ K : ℝ, ∀ N : ℕ, shiftedMertensReal N ^ 2 ≤ K * N := by
  have h1r : 0 < 1 - r := by linarith
  have hG : 0 < Real.Gamma r := Real.Gamma_pos_of_pos hr0
  set K : ℝ := 4 * r * Real.Gamma r * (2 : ℝ) ^ r / (1 - r) + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K, fun N => ?_⟩
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [shiftedMertensReal]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hlt
  rw [not_le] at hlt
  set a := |shiftedMertensReal N| with ha
  have ha2 : a ^ 2 = shiftedMertensReal N ^ 2 := sq_abs _
  have hMk : ∀ k < N, |shiftedMertensReal k| ≤ a := by
    intro k hk
    have h1 := ih k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.le
    have h3 : shiftedMertensReal k ^ 2 ≤ a ^ 2 := by nlinarith
    have := sq_le_sq.mp h3
    rwa [abs_of_nonneg (abs_nonneg _)] at this
  have hfloor : ∀ x ∈ Ioc (0 : ℝ) (1 / (4 * N)),
      (a / 2) ^ 2 ≤ finiteMobiusLaplacePencil N x ^ 2 := by
    intro x hx
    have hNx : (N : ℝ) * x ≤ 1 / 4 := by
      calc (N : ℝ) * x ≤ N * (1 / (4 * N)) := mul_le_mul_of_nonneg_left hx.2 hNpos.le
        _ = 1 / 4 := by field_simp
    have hhalf := half_le_abs_finiteMobiusLaplacePencil ha.symm hMk hx.1 hNx
    rw [← sq_abs (finiteMobiusLaplacePencil N x)]
    exact pow_le_pow_left₀ (by positivity) hhalf 2
  have hEge := finiteMobiusGammaHankelEnergy_ge_of_sq_le hr0 (by positivity) hfloor
  have hE : finiteMobiusGammaHankelEnergy N r ≤
      Real.Gamma r * (2 : ℝ) ^ (-r) * ((N : ℝ) ^ (1 - r) / (1 - r)) := by
    rw [finiteMobiusGammaHankelEnergy_eq_diagonal_add_offDiagonal]
    linarith [h N, finiteMobiusGammaHankelDiagonalEnergy_le_of_lt_one hr0 hr1 N]
  have hbr : (1 / (4 * N : ℝ)) ^ r = 1 / ((4 : ℝ) ^ r * (N : ℝ) ^ r) := by
    rw [Real.div_rpow (by norm_num) (by positivity), Real.one_rpow,
      Real.mul_rpow (by norm_num) hNpos.le]
  rw [hbr] at hEge
  have h4 : (4 : ℝ) ^ r = (2 : ℝ) ^ r * (2 : ℝ) ^ r := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hNr : (N : ℝ) ^ r * (N : ℝ) ^ (1 - r) = N := by
    rw [← Real.rpow_add hNpos]; simp
  have h2r : (2 : ℝ) ^ r * (2 : ℝ) ^ (-r) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have hp2 : 0 < (2 : ℝ) ^ r := by positivity
  have hpN : 0 < (N : ℝ) ^ r := by positivity
  -- a² ≤ 4 r 2^r Γ(r) N / (1 - r)
  have hbound : a ^ 2 ≤ (4 * r * Real.Gamma r * (2 : ℝ) ^ r / (1 - r)) * N := by
    have hchain := hEge.trans hE
    have hden : 0 < (4 : ℝ) ^ r * (N : ℝ) ^ r := by positivity
    rw [div_div, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at hchain
    have e : Real.Gamma r * (2 : ℝ) ^ (-r) * ((N : ℝ) ^ (1 - r) / (1 - r)) *
        ((4 : ℝ) ^ r * (N : ℝ) ^ r * r) =
        r * Real.Gamma r * (2 : ℝ) ^ r * N / (1 - r) := by
      rw [h4]
      calc Real.Gamma r * (2 : ℝ) ^ (-r) * ((N : ℝ) ^ (1 - r) / (1 - r)) *
            ((2 : ℝ) ^ r * (2 : ℝ) ^ r * (N : ℝ) ^ r * r)
          = r * Real.Gamma r * (2 : ℝ) ^ r *
              (((2 : ℝ) ^ r * (2 : ℝ) ^ (-r)) * ((N : ℝ) ^ r * (N : ℝ) ^ (1 - r))) / (1 - r) := by
            ring
        _ = r * Real.Gamma r * (2 : ℝ) ^ r * N / (1 - r) := by rw [h2r, hNr]; ring
    rw [e] at hchain
    have : a ^ 2 = 4 * (a / 2) ^ 2 := by ring
    rw [this]
    have e2 : (4 * r * Real.Gamma r * (2 : ℝ) ^ r / (1 - r)) * N =
        4 * (r * Real.Gamma r * (2 : ℝ) ^ r * N / (1 - r)) := by ring
    rw [e2]
    linarith
  have : K * N < a ^ 2 := by rw [ha2]; exact hlt
  nlinarith

end RHTower
