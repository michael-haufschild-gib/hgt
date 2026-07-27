import GaloisForLFunctions.RHTower.ReflectionCocycleCurvature
import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound

/-!
# Landau's summability transfer for nonnegative Dirichlet series

For a Dirichlet series `Σ aₙ n^{−s}` with **nonnegative real** coefficients, analytic
continuation through a disk around a real interior point transfers summability leftward:
if the series converges at the real point `σ₁` and some `G` analytic on the closed ball of
radius `R` centred at `σ₁ + 1` agrees with the series on the half-plane `Re s > σ₁`, then
the series converges absolutely at every real `σ > σ₁ + 1 − R` (`landau_summability_transfer`).
With `G` entire this gives convergence at every real point (`landau_entire_summable`): a
nonnegative Dirichlet series with an entire continuation converges everywhere.  This is the
quantitative content of Landau's theorem — a nonnegative Dirichlet series has a genuine
singularity at its real abscissa of convergence.

**Mechanism.**  At the centre `σ₂ = σ₁ + 1` the iterated derivatives of the series are
`(−1)^k Σ aₙ (log n)^k n^{−σ₂}` — a sign `(−1)^k` times a *nonnegative* number.  The Taylor
coefficients of `G` at `σ₂` therefore have norms `Σ aₙ (log n)^k n^{−σ₂} / k!`, and analyticity
on the ball makes `Σ_k ‖c_k‖ ρ^k` finite for `ρ < R`.  Every term of the double array
`aₙ (log n)^k n^{−σ₂} ρ^k / k!` is nonnegative, so Tonelli regroups the sum by `n`, where the
inner series reassembles the exponential: `Σ_k (ρ log n)^k / k! = n^ρ`.  The total is exactly
`Σ aₙ n^{−(σ₂−ρ)} < ∞`.  Positivity enters twice — no cancellation inside the derivative
values, and free regrouping of the double sum — and it is the only obstruction: signed series
(alternating partial thetas) do continue entire beyond their abscissa.
-/

noncomputable section

namespace RHTower

open Complex LSeries

/-- The iterate of the logarithmic twist: `logMul^[k] f n = (log n)^k · f n`. -/
private theorem logMul_iterate (f : ℕ → ℂ) (k n : ℕ) :
    (LSeries.logMul)^[k] f n = (Complex.log n) ^ k * f n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, ih (LSeries.logMul f), LSeries.logMul, pow_succ]
      ring

/-- The nonnegative real term array of the twisted series at real abscissa `τ`:
`aₙ (log n)^k / n^τ`, with the `n = 0` term zeroed out. -/
private def landauTerm (a : ℕ → ℝ) (τ : ℝ) (k n : ℕ) : ℝ :=
  if n = 0 then 0 else a n * (Real.log n) ^ k / (n : ℝ) ^ τ

private theorem landauTerm_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (τ : ℝ) (k n : ℕ) :
    0 ≤ landauTerm a τ k n := by
  rw [landauTerm]
  split_ifs with hn
  · exact le_refl 0
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have han := ha n
    positivity

/-- The `LSeries` term of the `k`-fold logarithmic twist at a real point is the complexified
`landauTerm`. -/
private theorem term_logMul_iterate_eq (a : ℕ → ℝ) (τ : ℝ) (k n : ℕ) :
    LSeries.term ((LSeries.logMul)^[k] fun m => (a m : ℂ)) (τ : ℂ) n
      = ((landauTerm a τ k n : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [landauTerm]
  · rw [LSeries.term_of_ne_zero hn, logMul_iterate, landauTerm, if_neg hn,
      log_natCast_eq (by omega : 1 ≤ n),
      show ((n : ℂ)) ^ (τ : ℂ) = (((n : ℝ) ^ τ : ℝ) : ℂ) by
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]]
    push_cast
    ring

/-- Summability of the twisted term array one unit right of a convergence point:
`(log n)^k ≤ k!·n` absorbs the logarithm into the extra `n^{−1}`. -/
private theorem summable_landauTerm {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₁ : ℝ}
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) (σ₁ : ℂ)) (k : ℕ) :
    Summable (landauTerm a (σ₁ + 1) k) := by
  have hbase : Summable (landauTerm a σ₁ 0) := by
    have h1 : Summable (fun n => ((landauTerm a σ₁ 0 n : ℝ) : ℂ)) :=
      hsum.congr fun n => by simpa using term_logMul_iterate_eq a σ₁ 0 n
    have h2 := h1.map (AddMonoidHom.mk' (fun z : ℂ => z.re) fun x y => Complex.add_re x y)
      Complex.continuous_re
    exact h2.congr fun n => Complex.ofReal_re _
  refine Summable.of_nonneg_of_le (landauTerm_nonneg ha _ k)
    (fun n => ?_) (hbase.mul_left (k.factorial : ℝ))
  rcases eq_or_ne n 0 with rfl | hn
  · simp [landauTerm]
  · have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hkey : (Real.log n) ^ k ≤ (k.factorial : ℝ) * (n : ℝ) := by
      have h := pow_le_factorial_mul_exp hlog k
      rwa [Real.exp_log hn0] at h
    simp only [landauTerm, if_neg hn, pow_zero, mul_one]
    rw [Real.rpow_add hn0, Real.rpow_one, div_le_iff₀ (by positivity)]
    have hclear : (k.factorial : ℝ) * (a n / (n : ℝ) ^ σ₁) * ((n : ℝ) ^ σ₁ * n)
        = (k.factorial : ℝ) * a n * n := by
      field_simp
    rw [hclear]
    calc a n * Real.log n ^ k ≤ a n * ((k.factorial : ℝ) * n) :=
          mul_le_mul_of_nonneg_left hkey (ha n)
      _ = (k.factorial : ℝ) * a n * n := by ring

/-- The value of the twisted `LSeries` at a real point is the complexified nonnegative sum. -/
private theorem LSeries_logMul_iterate_eq {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₁ : ℝ}
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) (σ₁ : ℂ)) (k : ℕ) :
    LSeries ((LSeries.logMul)^[k] fun m => (a m : ℂ)) ((σ₁ + 1 : ℝ) : ℂ)
      = ((∑' n, landauTerm a (σ₁ + 1) k n : ℝ) : ℂ) :=
  calc LSeries ((LSeries.logMul)^[k] fun m => (a m : ℂ)) ((σ₁ + 1 : ℝ) : ℂ)
      = ∑' n, LSeries.term ((LSeries.logMul)^[k] fun m => (a m : ℂ)) ((σ₁ + 1 : ℝ) : ℂ) n := rfl
    _ = ∑' n, ((landauTerm a (σ₁ + 1) k n : ℝ) : ℂ) :=
        tsum_congr (term_logMul_iterate_eq a (σ₁ + 1) k)
    _ = ((∑' n, landauTerm a (σ₁ + 1) k n : ℝ) : ℂ) :=
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).map_tsum (summable_landauTerm ha hsum k)).symm

/-- The real exponential as its Taylor series. -/
private theorem real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' k : ℕ, x ^ k / (k.factorial : ℝ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Summability of every logarithmic twist at an arbitrary real point strictly
right of the abscissa of absolute convergence. -/
private theorem summable_landauTerm_of_abscissa_lt
    {a : ℕ → ℝ} {τ : ℝ}
    (habs : abscissaOfAbsConv (fun n => (a n : ℂ)) < (τ : EReal))
    (k : ℕ) : Summable (landauTerm a τ k) := by
  have htwist : LSeriesSummable
      ((LSeries.logMul)^[k] fun n => (a n : ℂ)) (τ : ℂ) := by
    apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
    simpa using habs
  have hre := htwist.map
    (AddMonoidHom.mk' (fun z : ℂ => z.re) fun x y => Complex.add_re x y)
    Complex.continuous_re
  refine hre.congr (fun n => ?_)
  change (LSeries.term
    ((LSeries.logMul)^[k] fun n => (a n : ℂ)) (τ : ℂ) n).re = _
  rw [term_logMul_iterate_eq]
  simp

/-- The arbitrary-centre version of the logarithmic-twist value identity. -/
private theorem LSeries_logMul_iterate_eq_of_abscissa_lt
    {a : ℕ → ℝ} {τ : ℝ}
    (habs : abscissaOfAbsConv (fun n => (a n : ℂ)) < (τ : EReal))
    (k : ℕ) :
    LSeries ((LSeries.logMul)^[k] fun m => (a m : ℂ)) (τ : ℂ) =
      ((∑' n, landauTerm a τ k n : ℝ) : ℂ) :=
  calc
    LSeries ((LSeries.logMul)^[k] fun m => (a m : ℂ)) (τ : ℂ) =
        ∑' n, LSeries.term
          ((LSeries.logMul)^[k] fun m => (a m : ℂ)) (τ : ℂ) n := rfl
    _ = ∑' n, ((landauTerm a τ k n : ℝ) : ℂ) :=
      tsum_congr (term_logMul_iterate_eq a τ k)
    _ = ((∑' n, landauTerm a τ k n : ℝ) : ℂ) :=
      ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).map_tsum
        (summable_landauTerm_of_abscissa_lt habs k)).symm

/-- **Scale-local Landau transfer.**  The Taylor centre may be any positive
distance `h` to the right of a convergence point.  Thus a nonnegative
Dirichlet series analytically continued across a real boundary point is forced
to converge to the left of that boundary, with no hard-coded unit aperture. -/
theorem landau_local_summability_transfer
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₁ h : ℝ}
    (hh : 0 < h)
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) (σ₁ : ℂ))
    {R : NNReal} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G
      (Metric.closedBall ((σ₁ + h : ℝ) : ℂ) (R : ℝ)))
    (hagree : ∀ s : ℂ, σ₁ < s.re →
      G s = LSeries (fun n => (a n : ℂ)) s)
    {σ : ℝ} (hσ : σ₁ + h - (R : ℝ) < σ) :
    LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ) := by
  by_cases hσbig : σ₁ ≤ σ
  · exact hsum.of_re_le_re (by simpa using hσbig)
  push Not at hσbig
  have habs : abscissaOfAbsConv (fun n => (a n : ℂ)) ≤ (σ₁ : EReal) :=
    abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsum.of_re_le_re (by simpa using hy.le)
  have habs₂ : abscissaOfAbsConv (fun n => (a n : ℂ)) <
      (((σ₁ + h : ℝ) : ℂ).re : EReal) := by
    refine lt_of_le_of_lt habs ?_
    rw [Complex.ofReal_re]
    exact_mod_cast (by linarith : σ₁ < σ₁ + h)
  have habs₂' : abscissaOfAbsConv (fun n => (a n : ℂ)) <
      ((σ₁ + h : ℝ) : EReal) := by
    simpa using habs₂
  have hEvEq : G =ᶠ[nhds ((σ₁ + h : ℝ) : ℂ)]
      LSeries (fun n => (a n : ℂ)) := by
    have hopen : IsOpen {s : ℂ | σ₁ < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds ?_) fun s hs => hagree s hs
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    linarith
  have hiter : ∀ k, iteratedDeriv k G ((σ₁ + h : ℝ) : ℂ) =
      (-1) ^ k * ((∑' n, landauTerm a (σ₁ + h) k n : ℝ) : ℂ) := fun k => by
    rw [hEvEq.iteratedDeriv_eq k, LSeries_iteratedDeriv k habs₂,
      LSeries_logMul_iterate_eq_of_abscissa_lt habs₂' k]
  have hR0 : (0 : NNReal) < R := by
    have hRreal : (0 : ℝ) < (R : ℝ) := by linarith
    exact_mod_cast hRreal
  obtain ⟨p, hball⟩ : ∃ p,
      HasFPowerSeriesOnBall G p ((σ₁ + h : ℝ) : ℂ) R :=
    ⟨_, hGd.hasFPowerSeriesOnBall hR0⟩
  have hcoeff : ∀ k, (k.factorial : ℂ) * p.coeff k =
      iteratedDeriv k G ((σ₁ + h : ℝ) : ℂ) := by
    intro k
    have h1 := hball.factorial_smul (1 : ℂ) k
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h1, nsmul_eq_mul]
    rfl
  have htsum_nonneg : ∀ k, 0 ≤ ∑' n, landauTerm a (σ₁ + h) k n := fun k =>
    tsum_nonneg fun n => landauTerm_nonneg ha (σ₁ + h) k n
  have hcoeff_norm : ∀ k, ‖p.coeff k‖ =
      (∑' n, landauTerm a (σ₁ + h) k n) / (k.factorial : ℝ) := by
    intro k
    have h2 : (k.factorial : ℂ) * p.coeff k =
        (-1) ^ k * ((∑' n, landauTerm a (σ₁ + h) k n : ℝ) : ℂ) := by
      rw [hcoeff k, hiter k]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (htsum_nonneg k)] at h3
    have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by
      exact_mod_cast k.factorial_pos
    rw [eq_div_iff (ne_of_gt hkpos), mul_comm]
    exact h3
  set ρ : ℝ := σ₁ + h - σ with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hρR : ρ < (R : ℝ) := by rw [hρdef]; linarith
  set ρ' : NNReal := ⟨ρ, hρpos.le⟩ with hρ'
  have hsum_coeff : Summable fun k => ‖p k‖ * (ρ' : ℝ) ^ k := by
    refine p.summable_norm_mul_pow ?_
    calc
      (ρ' : ENNReal) < (R : ENNReal) := by exact_mod_cast hρR
      _ ≤ p.radius := hball.r_le
  have hsum_coeff' : Summable fun k =>
      (∑' n, landauTerm a (σ₁ + h) k n) *
        (ρ ^ k / (k.factorial : ℝ)) := by
    refine hsum_coeff.congr fun k => ?_
    rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, hcoeff_norm k,
      show (ρ' : ℝ) = ρ from rfl]
    ring
  set F2 : ℕ × ℕ → ℝ := fun kn =>
    landauTerm a (σ₁ + h) kn.1 kn.2 *
      (ρ ^ kn.1 / (kn.1.factorial : ℝ)) with hF2
  have hF2nonneg : ∀ kn, 0 ≤ F2 kn := by
    intro kn
    have hnonneg := landauTerm_nonneg ha (σ₁ + h) kn.1 kn.2
    simp only [hF2]
    positivity
  have hprod : Summable F2 := by
    refine (summable_prod_of_nonneg hF2nonneg).mpr ⟨fun k => ?_, ?_⟩
    · refine ((summable_landauTerm_of_abscissa_lt habs₂' k).mul_right
        (ρ ^ k / (k.factorial : ℝ))).congr fun n => ?_
      simp only [hF2]
    · refine hsum_coeff'.congr fun k => ?_
      simp only [hF2]
      exact tsum_mul_right.symm
  have hswap : Summable fun nk : ℕ × ℕ => F2 (nk.2, nk.1) :=
    ((Equiv.prodComm ℕ ℕ).summable_iff.mpr hprod).congr fun nk => rfl
  have hcols : Summable fun n => ∑' k, F2 (k, n) :=
    ((summable_prod_of_nonneg fun nk => hF2nonneg (nk.2, nk.1)).mp hswap).2
  have hcol_val : ∀ n : ℕ, n ≠ 0 →
      a n / (n : ℝ) ^ σ ≤ ∑' k, F2 (k, n) := by
    intro n hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ n)
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hexp : ∑' k : ℕ,
        (ρ * Real.log n) ^ k / (k.factorial : ℝ) = (n : ℝ) ^ ρ := by
      rw [← real_exp_eq_tsum, Real.rpow_def_of_pos hn0,
        mul_comm ρ (Real.log n)]
    have hval : ∑' k, F2 (k, n) =
        (a n / (n : ℝ) ^ (σ₁ + h)) *
          ∑' k : ℕ, (ρ * Real.log n) ^ k / (k.factorial : ℝ) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      simp only [hF2, landauTerm, if_neg hn]
      rw [mul_pow]
      ring
    have hsplit : (n : ℝ) ^ (σ₁ + h) =
        (n : ℝ) ^ σ * (n : ℝ) ^ ρ := by
      rw [← Real.rpow_add hn0]
      congr 1
      rw [hρdef]
      ring
    have hfin : a n / (n : ℝ) ^ (σ₁ + h) * (n : ℝ) ^ ρ =
        a n / (n : ℝ) ^ σ := by
      have h1 : (n : ℝ) ^ σ ≠ 0 := by positivity
      have h2 : (n : ℝ) ^ ρ ≠ 0 := by positivity
      rw [hsplit]
      field_simp
    rw [hval, hexp, hfin]
  have htarget : Summable (landauTerm a σ 0) := by
    refine Summable.of_nonneg_of_le (landauTerm_nonneg ha σ 0)
      (fun n => ?_) hcols
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [landauTerm] using tsum_nonneg fun k => hF2nonneg (k, 0)
    · calc
        landauTerm a σ 0 n = a n / (n : ℝ) ^ σ := by
          simp [landauTerm, if_neg hn]
        _ ≤ ∑' k, F2 (k, n) := hcol_val n hn
  have hfinal : Summable (fun n => ((landauTerm a σ 0 n : ℝ) : ℂ)) := by
    refine Summable.of_norm (htarget.congr fun n => ?_)
    rw [Complex.norm_real,
      Real.norm_of_nonneg (landauTerm_nonneg ha σ 0 n)]
  show Summable fun n =>
    LSeries.term (fun m => (a m : ℂ)) (σ : ℂ) n
  refine hfinal.congr fun n => ?_
  exact (by simpa using term_logMul_iterate_eq a σ 0 n :
    LSeries.term _ (σ : ℂ) n =
      ((landauTerm a σ 0 n : ℝ) : ℂ)).symm

/-- **Landau's summability transfer.**  A Dirichlet series with nonnegative real coefficients,
convergent at the real point `σ₁` and continued by a function analytic on the closed ball of
radius `R` around `σ₂ = σ₁ + 1` (agreeing with the series on `Re s > σ₁`), converges at
every real `σ > σ₂ − R`.  The Taylor coefficients of the continuation at `σ₂` are signs times
nonnegative values with no interior cancellation, so Tonelli regroups `Σ_k |c_k| ρ^k` by `n`
and reassembles `Σ aₙ n^{−(σ₂−ρ)}`. -/
theorem landau_summability_transfer {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₁ : ℝ}
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) (σ₁ : ℂ))
    {R : NNReal} {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (Metric.closedBall ((σ₁ + 1 : ℝ) : ℂ) (R : ℝ)))
    (hagree : ∀ s : ℂ, σ₁ < s.re → G s = LSeries (fun n => (a n : ℂ)) s)
    {σ : ℝ} (hσ : σ₁ + 1 - (R : ℝ) < σ) :
    LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ) :=
  landau_local_summability_transfer ha zero_lt_one hsum hGd hagree hσ

/-- **Landau for entire continuations.**  A Dirichlet series with nonnegative real coefficients
and an entire continuation converges at every real point: no real abscissa survives.
Contrapositive: a nonnegative series that diverges somewhere (any infinite 0/1 series at
`σ = 0`) admits no entire continuation. -/
theorem landau_entire_summable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {σ₁ : ℝ}
    (hsum : LSeriesSummable (fun n => (a n : ℂ)) (σ₁ : ℂ))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hagree : ∀ s : ℂ, σ₁ < s.re → G s = LSeries (fun n => (a n : ℂ)) s)
    (σ : ℝ) : LSeriesSummable (fun n => (a n : ℂ)) (σ : ℂ) := by
  set R : NNReal := (max 2 (σ₁ + 2 - σ)).toNNReal with hR
  have hRval : (R : ℝ) = max 2 (σ₁ + 2 - σ) := by
    rw [hR, Real.coe_toNNReal _ (le_trans (by norm_num) (le_max_left _ _))]
  refine landau_summability_transfer (R := R) ha hsum hG.differentiableOn hagree ?_
  rw [hRval]
  have h := le_max_right 2 (σ₁ + 2 - σ)
  linarith

end RHTower
