import GaloisForLFunctions.RHTower.CausalMobiusThetaMovingCusp
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import GaloisForLFunctions.RHTower.HedenmalmThetaKernelEnergy
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Moving-cusp reflection: the signed-totient dual source

For a finite prime set `S` with `P = ∏_{p∈S} p` the moving-frame source

```text
R_S(u) = μ(P)√P k_S(−log P − u) = Σ_{e|P} μ(e)√e k(u + log e) = ∏_{p∈S}(1 − √p T_{log p}) k(u)
```

has Mellin transform `F(w)∏(1 − p^{1/2−w})`, `F(w) = ∫e^{wu}k = XiC(iw)`.  Along every prime
exhaustion `R_S` converges, with all derivatives and locally uniformly, to
`R_∞(u) = Σ_n μ(n)√n k(u + log n)`, whose Mellin transform is `F(w)/ζ(w − 1/2)` for `Re w > 3/2`.

The analytic engine is the class of log-shift series `Σ_n a_n f(u + log n)` with polynomially
bounded weights and a source `f` that is bounded and has a right Gaussian tail
`|f(x)| ≤ C e^{Dx} e^{−π e^{2x}}`: such series converge locally uniformly, may be differentiated
termwise, and are stable under pointwise convergence of the weights (Tannery).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## Log-shift series -/

/-- A source with a global bound and a right Gaussian tail. -/
structure GaussianLogTail (f : ℝ → ℝ) : Prop where
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |f x| ≤ B
  tail : ∃ C : ℝ, ∃ D : ℕ, 0 ≤ C ∧ ∀ x, 0 ≤ x →
    |f x| ≤ C * Real.exp (D * x) * Real.exp (-Real.pi * Real.exp (2 * x))

/-- The log-shift series `Σ_n a_n f(u + log n)`. -/
def logShiftSeries (a : ℕ → ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ := ∑' n : ℕ, a n * f (u + Real.log n)

/-- Weights bounded by `n^K`. -/
def PolyBoundedWeight (K : ℕ) (a : ℕ → ℝ) : Prop := ∀ n, |a n| ≤ (n : ℝ) ^ K

theorem exp_mul_exp_neg_le (D x : ℝ) (hx : 0 ≤ x) :
    Real.exp (D * x) * Real.exp (-Real.pi * Real.exp (2 * x)) ≤
      Real.exp (D ^ 2 / (8 * Real.pi)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x by linarith)
  have hpi := Real.pi_pos
  have h1 : -Real.pi * Real.exp (2 * x) ≤ -Real.pi * (1 + 2 * x + (2 * x) ^ 2 / 2) := by
    nlinarith
  have h2 : D * x - Real.pi * (1 + 2 * x + (2 * x) ^ 2 / 2) ≤ D ^ 2 / (8 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (4 * Real.pi * x - D), mul_pos hpi hpi, mul_nonneg (mul_pos hpi hpi).le hx]
  linarith

/-- Every derivative of the completed theta source is bounded with a right Gaussian tail. -/
theorem gaussianLogTail_iteratedDeriv_thetaCuspFullSource (m : ℕ) :
    GaussianLogTail (iteratedDeriv m thetaCuspFullSource) := by
  obtain ⟨C, D, hC, hD, h⟩ := exists_abs_iteratedDeriv_thetaCuspFullSource_le_gaussian m
  refine ⟨⟨C * Real.exp (D ^ 2 / (8 * Real.pi)), by positivity, fun x => ?_⟩,
    ⟨C, ⌈D⌉₊, hC, fun x hx => ?_⟩⟩
  · have hpos : ∀ y, 0 ≤ y → |iteratedDeriv m thetaCuspFullSource y| ≤
        C * Real.exp (D ^ 2 / (8 * Real.pi)) := fun y hy => by
      refine (h y hy).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (exp_mul_exp_neg_le D y hy) hC
    rcases le_total 0 x with hx | hx
    · exact hpos x hx
    · rw [← neg_neg x, abs_iteratedDeriv_thetaCuspFullSource_neg]
      exact hpos (-x) (by linarith)
  · refine (h x hx).trans ?_
    gcongr
    exact Nat.le_ceil D

theorem gaussianLogTail_thetaCuspFullSource : GaussianLogTail thetaCuspFullSource := by
  simpa using gaussianLogTail_iteratedDeriv_thetaCuspFullSource 0

/-- **Uniform majorant on a compact window.**  For weights `|a n| ≤ n^K` and a Gaussian-tailed
source there is a summable `G` with `|a n f(u + log n)| ≤ G n` for every `u ∈ [lo, hi]`. -/
theorem GaussianLogTail.exists_majorant {f : ℝ → ℝ} (hf : GaussianLogTail f) (K : ℕ)
    (lo hi : ℝ) :
    ∃ G : ℕ → ℝ, Summable G ∧ ∀ a : ℕ → ℝ, PolyBoundedWeight K a →
      ∀ n, ∀ u ∈ Icc lo hi, |a n * f (u + Real.log n)| ≤ G n := by
  obtain ⟨B, hB, hfB⟩ := hf.bound
  obtain ⟨C, D, hC, hfC⟩ := hf.tail
  set N₀ : ℕ := ⌈Real.exp (-lo)⌉₊ + 1
  set σ : ℝ := Real.pi * Real.exp (2 * lo)
  have hσ : 0 < σ := by positivity
  set G : ℕ → ℝ := fun n => (if n < N₀ then (n : ℝ) ^ K * B else 0) +
    C * Real.exp (D * hi) * ((n : ℝ) ^ (K + D) * Real.exp (-σ * (n : ℝ) ^ 2))
  refine ⟨G, ?_, fun a ha n u hu => ?_⟩
  · refine Summable.add ?_ ((summable_pow_mul_exp_neg_nat_sq (K + D) hσ).mul_left _)
    exact summable_of_ne_finset_zero (s := Finset.range N₀) fun n hn => by
      rw [Finset.mem_range] at hn; simp [hn]
  have hG2 : 0 ≤ C * Real.exp (D * hi) * ((n : ℝ) ^ (K + D) * Real.exp (-σ * (n : ℝ) ^ 2)) := by
    positivity
  rw [abs_mul]
  by_cases hn : n < N₀
  · simp only [G, if_pos hn]
    have := mul_le_mul (ha n) (hfB (u + Real.log n)) (abs_nonneg _) (by positivity)
    linarith
  · simp only [G, if_neg hn, zero_add]
    have hnN : (N₀ : ℝ) ≤ n := by exact_mod_cast not_lt.1 hn
    have hceil : Real.exp (-lo) ≤ (⌈Real.exp (-lo)⌉₊ : ℝ) := Nat.le_ceil _
    have hn1 : Real.exp (-lo) + 1 ≤ (n : ℝ) := by
      have : (N₀ : ℝ) = (⌈Real.exp (-lo)⌉₊ : ℝ) + 1 := by simp [N₀]
      linarith
    have hnpos : (0 : ℝ) < n := by linarith [Real.exp_pos (-lo)]
    have hlog : -lo ≤ Real.log n := by
      rw [← Real.log_exp (-lo)]
      exact Real.log_le_log (Real.exp_pos _) (by linarith)
    have hx : 0 ≤ u + Real.log n := by linarith [hu.1]
    have hfx := hfC _ hx
    have hexpD : Real.exp (D * (u + Real.log n)) ≤ Real.exp (D * hi) * (n : ℝ) ^ D := by
      rw [mul_add, Real.exp_add, ← Real.rpow_natCast, Real.rpow_def_of_pos hnpos, mul_comm (Real.log n)]
      gcongr
      exact hu.2
    have hexp2 : Real.exp (-Real.pi * Real.exp (2 * (u + Real.log n))) ≤
        Real.exp (-σ * (n : ℝ) ^ 2) := by
      refine Real.exp_le_exp.2 ?_
      have h2 : Real.exp (2 * (u + Real.log n)) = Real.exp (2 * u) * (n : ℝ) ^ 2 := by
        have hl : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
          rw [← Real.exp_log (pow_pos hnpos 2), Real.log_pow]; norm_num
        rw [mul_add, Real.exp_add, hl]
      rw [h2]
      have : Real.exp (2 * lo) ≤ Real.exp (2 * u) := Real.exp_le_exp.2 (by linarith [hu.1])
      have hn2 : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      simp only [σ]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right this hn2]
    calc |a n| * |f (u + Real.log n)|
        ≤ (n : ℝ) ^ K * (C * (Real.exp (D * hi) * (n : ℝ) ^ D) * Real.exp (-σ * (n : ℝ) ^ 2)) := by
          refine mul_le_mul (ha n) (hfx.trans ?_) (abs_nonneg _) (by positivity)
          gcongr
      _ = C * Real.exp (D * hi) * ((n : ℝ) ^ (K + D) * Real.exp (-σ * (n : ℝ) ^ 2)) := by
          rw [pow_add]; ring

theorem GaussianLogTail.summable {f : ℝ → ℝ} (hf : GaussianLogTail f) {K : ℕ} {a : ℕ → ℝ}
    (ha : PolyBoundedWeight K a) (u : ℝ) : Summable fun n => a n * f (u + Real.log n) := by
  obtain ⟨G, hG, hb⟩ := hf.exists_majorant K u u
  exact Summable.of_norm_bounded hG fun n => by
    rw [Real.norm_eq_abs]; exact hb a ha n u ⟨le_rfl, le_rfl⟩

theorem GaussianLogTail.continuous_logShiftSeries {f : ℝ → ℝ} (hf : GaussianLogTail f)
    (hfc : Continuous f) {K : ℕ} {a : ℕ → ℝ} (ha : PolyBoundedWeight K a) :
    Continuous (logShiftSeries a f) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  obtain ⟨G, hG, hb⟩ := hf.exists_majorant K (u - 1) (u + 1)
  have hcont : ContinuousOn (logShiftSeries a f) (Icc (u - 1) (u + 1)) :=
    continuousOn_tsum (fun n => (continuous_const.mul (hfc.comp
      (continuous_id.add continuous_const))).continuousOn) hG
      fun n x hx => by rw [Real.norm_eq_abs]; exact hb a ha n x hx
  exact hcont.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- **Termwise differentiation.** -/
theorem GaussianLogTail.hasDerivAt_logShiftSeries {f f' : ℝ → ℝ} (hf : GaussianLogTail f)
    (hf' : GaussianLogTail f') (hderiv : ∀ x, HasDerivAt f (f' x) x) {K : ℕ} {a : ℕ → ℝ}
    (ha : PolyBoundedWeight K a) (u : ℝ) :
    HasDerivAt (logShiftSeries a f) (logShiftSeries a f' u) u := by
  obtain ⟨G, hG, hb⟩ := hf'.exists_majorant K (u - 1) (u + 1)
  have h := hasDerivAt_tsum_of_isPreconnected (g := fun n y => a n * f (y + Real.log n))
    (g' := fun n y => a n * f' (y + Real.log n)) (t := Ioo (u - 1) (u + 1)) (y₀ := u) hG isOpen_Ioo
    isPreconnected_Ioo (fun n y _ => ((hderiv _).comp y ((hasDerivAt_id y).add_const _)).const_mul _
      |>.congr_deriv (by simp))
    (fun n y hy => by rw [Real.norm_eq_abs]; exact hb a ha n y (Ioo_subset_Icc_self hy))
    ⟨by linarith, by linarith⟩ (hf.summable ha u) ⟨by linarith, by linarith⟩
  exact h

/-- **Tannery's theorem for log-shift series.**  If the weights converge pointwise under a common
polynomial bound, the series converge uniformly on every compact window. -/
theorem GaussianLogTail.tendstoUniformlyOn_logShiftSeries {f : ℝ → ℝ} (hf : GaussianLogTail f)
    {K : ℕ} {ι : Type*} {l : Filter ι} {a : ι → ℕ → ℝ} {b : ℕ → ℝ}
    (ha : ∀ i, PolyBoundedWeight K (a i)) (hb : PolyBoundedWeight K b)
    (hlim : ∀ n, Tendsto (fun i => a i n) l (𝓝 (b n))) (lo hi : ℝ) :
    TendstoUniformlyOn (fun i => logShiftSeries (a i) f) (logShiftSeries b f) l (Icc lo hi) := by
  obtain ⟨G, hG, hGb⟩ := hf.exists_majorant K lo hi
  obtain ⟨B, hB, hfB⟩ := hf.bound
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' k, G (k + N) < ε / 3 :=
    ((tendsto_sum_nat_add G).eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε / 3))).exists
  have hfin : ∀ n ∈ Finset.range N, ∀ᶠ i in l, |b n - a i n| < ε / (3 * (N * (B + 1) + 1)) := by
    intro n _
    have := (hlim n).eventually (Metric.ball_mem_nhds (b n) (show 0 < ε / (3 * (N * (B + 1) + 1))
      by positivity))
    filter_upwards [this] with i hi
    rw [dist_comm, Real.dist_eq] at hi
    exact hi
  filter_upwards [(Finset.range N).eventually_all.2 hfin] with i hi u hu
  have hsa := hf.summable (ha i) u
  have hsb := hf.summable hb u
  set d : ℕ → ℝ := fun n => b n * f (u + Real.log n) - a i n * f (u + Real.log n) with hd
  have hsd : Summable d := hsb.sub hsa
  rw [Real.dist_eq, logShiftSeries, logShiftSeries, ← hsb.tsum_sub hsa,
    ← hsd.sum_add_tsum_nat_add N]
  have hhead : |∑ n ∈ Finset.range N, d n| ≤ ε / 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range N, |d n|
        ≤ ∑ n ∈ Finset.range N, ε / (3 * (N * (B + 1) + 1)) * (B + 1) := by
          refine Finset.sum_le_sum fun n hn => ?_
          simp only [hd]
          rw [← sub_mul, abs_mul]
          exact mul_le_mul (hi n hn).le ((hfB _).trans (by linarith)) (abs_nonneg _)
            (by positivity)
      _ = N * (B + 1) * (ε / (3 * (N * (B + 1) + 1))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ ε / 3 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hε.le, mul_nonneg (Nat.cast_nonneg N) (by linarith : (0:ℝ) ≤ B + 1)]
  have hmaj : ∀ k, |d (k + N)| ≤ 2 * G (k + N) := fun k => by
    simp only [hd]
    refine (abs_sub _ _).trans ?_
    linarith [hGb b hb (k + N) u hu, hGb (a i) (ha i) (k + N) u hu]
  have hGs : Summable fun k => G (k + N) := (summable_nat_add_iff N).2 hG
  have hdn : Summable fun k => ‖d (k + N)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hmaj k) (hGs.mul_left 2)
  have htail : |∑' k, d (k + N)| < 2 * (ε / 3) := by
    calc |∑' k, d (k + N)| ≤ ∑' k, ‖d (k + N)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hdn
      _ ≤ ∑' k, 2 * G (k + N) :=
          Summable.tsum_le_tsum (fun k => by rw [Real.norm_eq_abs]; exact hmaj k) hdn
            (hGs.mul_left 2)
      _ = 2 * ∑' k, G (k + N) := tsum_mul_left
      _ < 2 * (ε / 3) := by linarith
  calc |∑ n ∈ Finset.range N, d n + ∑' k, d (k + N)|
      < ε / 3 + 2 * (ε / 3) := (abs_add_le _ _).trans_lt (add_lt_add_of_le_of_lt hhead htail)
    _ = ε := by ring

/-- Termwise iterated differentiation of a log-shift series of the theta source. -/
theorem iteratedDeriv_logShiftSeries_thetaCuspFullSource {K : ℕ} {a : ℕ → ℝ}
    (ha : PolyBoundedWeight K a) (m : ℕ) :
    iteratedDeriv m (logShiftSeries a thetaCuspFullSource) =
      logShiftSeries a (iteratedDeriv m thetaCuspFullSource) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    refine (GaussianLogTail.hasDerivAt_logShiftSeries
      (gaussianLogTail_iteratedDeriv_thetaCuspFullSource m)
      (gaussianLogTail_iteratedDeriv_thetaCuspFullSource (m + 1)) (fun x => ?_) ha u).deriv
    rw [iteratedDeriv_succ]
    exact ((contDiff_thetaCuspFullSource.differentiable_iteratedDeriv m
      (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt

theorem contDiff_logShiftSeries_thetaCuspFullSource {K : ℕ} {a : ℕ → ℝ}
    (ha : PolyBoundedWeight K a) :
    ContDiff ℝ ∞ (logShiftSeries a thetaCuspFullSource) := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _hm
  rw [iteratedDeriv_logShiftSeries_thetaCuspFullSource ha]
  intro u
  refine (GaussianLogTail.hasDerivAt_logShiftSeries
    (gaussianLogTail_iteratedDeriv_thetaCuspFullSource m)
    (gaussianLogTail_iteratedDeriv_thetaCuspFullSource (m + 1)) (fun x => ?_) ha u).differentiableAt
  rw [iteratedDeriv_succ]
  exact ((contDiff_thetaCuspFullSource.differentiable_iteratedDeriv m
    (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt

/-! ## The finite moving-cusp source -/

/-- The moving-frame source `R_S f(u) = Σ_{T ⊆ S} (−1)^{|T|} (∏T)^{1/2} f(u + log ∏T)`, the
expansion of `∏_{p∈S}(1 − √p T_{log p}) f`. -/
def movingCuspSource (S : Finset ℕ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
    ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (1 / 2 : ℝ) * f (u + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))

theorem movingCuspSource_empty (f : ℝ → ℝ) : movingCuspSource ∅ f = f := by
  funext u; simp [movingCuspSource]

/-- **Product form.**  One more factor `1 − √p T_{log p}`. -/
theorem movingCuspSource_insert {p : ℕ} {S : Finset ℕ} (hp : 0 < p) (hS : ∀ q ∈ S, 0 < q)
    (hpS : p ∉ S) (f : ℝ → ℝ) (u : ℝ) :
    movingCuspSource (insert p S) f u =
      movingCuspSource S f u - (p : ℝ) ^ (1 / 2 : ℝ) * movingCuspSource S f (u + Real.log p) := by
  classical
  unfold movingCuspSource
  rw [Finset.sum_powerset_insert hpS, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hpT : p ∉ T := fun h => hpS (Finset.mem_powerset.mp hT h)
  have hTpos : 0 < ∏ q ∈ T, q := Finset.prod_pos fun q hq => hS q (Finset.mem_powerset.mp hT hq)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hTR : (0 : ℝ) < ((∏ q ∈ T, q : ℕ) : ℝ) := by exact_mod_cast hTpos
  rw [Finset.prod_insert hpT, Finset.card_insert_of_notMem hpT, Nat.cast_mul,
    Real.mul_rpow hpR.le hTR.le, Real.log_mul hpR.ne' hTR.ne', pow_succ]
  rw [show u + (Real.log p + Real.log ((∏ q ∈ T, q : ℕ) : ℝ)) =
      u + Real.log p + Real.log ((∏ q ∈ T, q : ℕ) : ℝ) by ring]
  ring

/-- **(1) Moving-cusp reflection.**  For an even source,
`R_S(u) = (−1)^{|S|} √P · k_S(−log P − u)`. -/
theorem movingCuspSource_eq_neg_one_pow_mul_deletion {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p)
    {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (u : ℝ) :
    movingCuspSource S f u = (-1 : ℝ) ^ S.card * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
      thetaPrimeDeletion S f (-Real.log ((∏ p ∈ S, p : ℕ) : ℝ) - u) := by
  classical
  induction S using Finset.induction_on generalizing u with
  | empty =>
    rw [movingCuspSource_empty, thetaPrimeDeletion_empty]
    simp [hf]
  | @insert p S hpS ih =>
    have hp : 0 < p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, 0 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hPR : (0 : ℝ) < ((∏ q ∈ S, q : ℕ) : ℝ) := by exact_mod_cast Finset.prod_pos hS'
    rw [movingCuspSource_insert hp hS' hpS, ih hS' u, ih hS' (u + Real.log p),
      thetaPrimeDeletion_insert hp hS' hpS, Finset.prod_insert hpS, Finset.card_insert_of_notMem hpS,
      Nat.cast_mul, Real.mul_rpow hpR.le hPR.le, Real.log_mul hpR.ne' hPR.ne']
    have hpp : (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hpR]; norm_num
    rw [show -(Real.log p + Real.log ((∏ q ∈ S, q : ℕ) : ℝ)) - u + Real.log p =
        -Real.log ((∏ q ∈ S, q : ℕ) : ℝ) - u by ring,
      show -(Real.log p + Real.log ((∏ q ∈ S, q : ℕ) : ℝ)) - u =
        -Real.log ((∏ q ∈ S, q : ℕ) : ℝ) - (u + Real.log p) by ring, pow_succ]
    linear_combination (-((-1 : ℝ) ^ S.card * ((∏ q ∈ S, q : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
      thetaPrimeDeletion S f (-Real.log ((∏ q ∈ S, q : ℕ) : ℝ) - u))) * hpp

/-- **(1)** `R_S(u) = μ(P)√P k_S(−log P − u)`. -/
theorem movingCuspSource_eq_moebius_mul_deletion {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (u : ℝ) :
    movingCuspSource S f u =
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℝ) * ((∏ p ∈ S, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
        thetaPrimeDeletion S f (-Real.log ((∏ p ∈ S, p : ℕ) : ℝ) - u) := by
  rw [movingCuspSource_eq_neg_one_pow_mul_deletion (fun p hp => (hS p hp).pos) hf,
    moebius_prod_of_primes hS]
  push_cast
  ring

/-- **(1) Divisor form** `R_S(u) = Σ_{e|P} μ(e)√e f(u + log e)`. -/
theorem movingCuspSource_eq_sum_divisors {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (f : ℝ → ℝ) (u : ℝ) :
    movingCuspSource S f u = ∑ e ∈ (∏ p ∈ S, p).divisors,
      ((ArithmeticFunction.moebius e : ℤ) : ℝ) * (e : ℝ) ^ (1 / 2 : ℝ) * f (u + Real.log e) := by
  rw [Sieve.sum_divisors_prod_primes_eq hS, movingCuspSource]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hTS : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
  rw [moebius_prod_of_primes hTS]
  push_cast
  ring

/-- The finite moving-cusp weights `1_{n|P} μ(n)√n`. -/
def movingCuspWeight (S : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∣ ∏ p ∈ S, p then ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) else 0

/-- The cofinal moving-cusp weights `μ(n)√n`. -/
def movingCuspLimitWeight (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)

theorem abs_moebius_mul_sqrt_le (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ)| ≤ (n : ℝ) ^ 1 := by
  rw [abs_mul, pow_one]
  have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
    have := ArithmeticFunction.abs_moebius_le_one (n := n)
    exact_mod_cast this
  have hs : |(n : ℝ) ^ (1 / 2 : ℝ)| ≤ n := by
    rw [abs_of_nonneg (by positivity)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Real.rpow_le_self_of_one_le (by exact_mod_cast hn) (by norm_num)
  calc _ ≤ 1 * (n : ℝ) := mul_le_mul hμ hs (abs_nonneg _) zero_le_one
    _ = n := one_mul _

theorem polyBoundedWeight_movingCuspLimitWeight : PolyBoundedWeight 1 movingCuspLimitWeight :=
  fun n => abs_moebius_mul_sqrt_le n

theorem polyBoundedWeight_movingCuspWeight (S : Finset ℕ) : PolyBoundedWeight 1 (movingCuspWeight S) :=
  fun n => by
    unfold movingCuspWeight
    split_ifs
    · exact abs_moebius_mul_sqrt_le n
    · simp

theorem movingCuspSource_eq_logShiftSeries {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (f : ℝ → ℝ) :
    movingCuspSource S f = logShiftSeries (movingCuspWeight S) f := by
  funext u
  have hP0 : (∏ p ∈ S, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hS p hp).ne_zero
  rw [movingCuspSource_eq_sum_divisors hS, logShiftSeries,
    tsum_eq_sum (s := (∏ p ∈ S, p).divisors)]
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [movingCuspWeight, if_pos (Nat.dvd_of_mem_divisors he)]
  · intro n hn
    rw [movingCuspWeight, if_neg, zero_mul]
    exact fun h => hn (Nat.mem_divisors.2 ⟨h, hP0⟩)

/-! ## The cofinal dual source -/

/-- The cofinal moving-cusp dual source `R_∞(u) = Σ_n μ(n)√n k(u + log n)`. -/
def movingCuspDualLimit (u : ℝ) : ℝ := logShiftSeries movingCuspLimitWeight thetaCuspFullSource u

theorem summable_movingCuspDualLimit (u : ℝ) :
    Summable fun n => movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n) :=
  gaussianLogTail_thetaCuspFullSource.summable polyBoundedWeight_movingCuspLimitWeight u

theorem contDiff_movingCuspDualLimit : ContDiff ℝ ∞ movingCuspDualLimit :=
  contDiff_logShiftSeries_thetaCuspFullSource polyBoundedWeight_movingCuspLimitWeight

theorem iteratedDeriv_movingCuspDualLimit (m : ℕ) :
    iteratedDeriv m movingCuspDualLimit =
      logShiftSeries movingCuspLimitWeight (iteratedDeriv m thetaCuspFullSource) :=
  iteratedDeriv_logShiftSeries_thetaCuspFullSource polyBoundedWeight_movingCuspLimitWeight m

theorem PrimeExhaustion.tendsto_movingCuspWeight {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S)
    (n : ℕ) : Tendsto (fun N => movingCuspWeight (S N) n) atTop (𝓝 (movingCuspLimitWeight n)) := by
  by_cases hsq : Squarefree n
  · have hev : ∀ᶠ N in atTop, n ∣ ∏ p ∈ S N, p := by
      have hall : ∀ᶠ N in atTop, ∀ p ∈ n.primeFactors, p ∈ S N :=
        n.primeFactors.eventually_all.2 fun p hp => hS.eventually_mem p (Nat.prime_of_mem_primeFactors hp)
      filter_upwards [hall] with N hN
      rw [← Nat.prod_primeFactors_of_squarefree hsq]
      exact Finset.prod_dvd_prod_of_subset _ _ _ hN
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    rw [movingCuspWeight, if_pos hN, movingCuspLimitWeight]
  · have h0 : ArithmeticFunction.moebius n = 0 := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    refine tendsto_const_nhds.congr fun N => ?_
    unfold movingCuspWeight movingCuspLimitWeight
    split_ifs <;> simp [h0]

/-- **(3) Cofinal limit with every derivative.**  Along every prime exhaustion,
`R_{S_N}^{(m)} → R_∞^{(m)}` uniformly on compact windows. -/
theorem PrimeExhaustion.tendstoUniformlyOn_iteratedDeriv_movingCuspSource {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (m : ℕ) (lo hi : ℝ) :
    TendstoUniformlyOn (fun N => iteratedDeriv m (movingCuspSource (S N) thetaCuspFullSource))
      (iteratedDeriv m movingCuspDualLimit) atTop (Icc lo hi) := by
  have hfun : (fun N => iteratedDeriv m (movingCuspSource (S N) thetaCuspFullSource)) =
      fun N => logShiftSeries (movingCuspWeight (S N)) (iteratedDeriv m thetaCuspFullSource) := by
    funext N
    rw [movingCuspSource_eq_logShiftSeries (hS.prime N),
      iteratedDeriv_logShiftSeries_thetaCuspFullSource (polyBoundedWeight_movingCuspWeight _)]
  rw [hfun, iteratedDeriv_movingCuspDualLimit]
  exact (gaussianLogTail_iteratedDeriv_thetaCuspFullSource m).tendstoUniformlyOn_logShiftSeries
    (fun N => polyBoundedWeight_movingCuspWeight _) polyBoundedWeight_movingCuspLimitWeight
    hS.tendsto_movingCuspWeight lo hi

theorem PrimeExhaustion.tendstoUniformlyOn_movingCuspSource {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (lo hi : ℝ) :
    TendstoUniformlyOn (fun N => movingCuspSource (S N) thetaCuspFullSource)
      movingCuspDualLimit atTop (Icc lo hi) := by
  simpa using hS.tendstoUniformlyOn_iteratedDeriv_movingCuspSource 0 lo hi

/-- **(3)** `√P k_S(−log P − u) − μ(P) R_∞(u) → 0` locally uniformly along every exhaustion. -/
theorem PrimeExhaustion.tendstoUniformlyOn_sqrt_mul_deletion_sub {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (lo hi : ℝ) :
    TendstoUniformlyOn (fun N u => ((∏ p ∈ S N, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
        thetaPrimeDeletion (S N) thetaCuspFullSource (-Real.log ((∏ p ∈ S N, p : ℕ) : ℝ) - u) -
        ((ArithmeticFunction.moebius (∏ p ∈ S N, p) : ℤ) : ℝ) * movingCuspDualLimit u)
      (fun _ => 0) atTop (Icc lo hi) := by
  have h := hS.tendstoUniformlyOn_movingCuspSource lo hi
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with N hN u hu
  have hμ : ((ArithmeticFunction.moebius (∏ p ∈ S N, p) : ℤ) : ℝ) = (-1) ^ (S N).card := by
    rw [moebius_prod_of_primes (hS.prime N)]; push_cast; ring
  have hsq : ((-1 : ℝ) ^ (S N).card) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hR := movingCuspSource_eq_moebius_mul_deletion (hS.prime N) thetaCuspFullSource_neg u
  rw [hμ] at hR ⊢
  have hkey : ((∏ p ∈ S N, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
      thetaPrimeDeletion (S N) thetaCuspFullSource (-Real.log ((∏ p ∈ S N, p : ℕ) : ℝ) - u) -
      (-1) ^ (S N).card * movingCuspDualLimit u =
      (-1) ^ (S N).card * (movingCuspSource (S N) thetaCuspFullSource u - movingCuspDualLimit u) := by
    rw [hR]; linear_combination (-(((∏ p ∈ S N, p : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
      thetaPrimeDeletion (S N) thetaCuspFullSource (-Real.log ((∏ p ∈ S N, p : ℕ) : ℝ) - u))) * hsq
  rw [dist_eq_norm, zero_sub, norm_neg, hkey, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, ← dist_eq_norm, dist_comm]
  exact hN u hu

/-! ## Mellin transforms -/

theorem natCast_prod_cpow_eq_prod_cpow (T : Finset ℕ) (s : ℂ) :
    (((∏ p ∈ T, p : ℕ) : ℂ)) ^ s = ∏ p ∈ T, (p : ℂ) ^ s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert q T hqT ih =>
    rw [Finset.prod_insert hqT, Finset.prod_insert hqT, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/-- **(2) Mellin law of the moving-frame source.**  Wherever the source is exponentially
integrable, `∫ e^{wu} R_S f = ∏_{p∈S}(1 − p^{1/2−w}) ∫ e^{wx} f`. -/
theorem integral_cexp_mul_movingCuspSource (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    (f : ℝ → ℝ) (w : ℂ) (hf : Integrable (fun x : ℝ => Complex.exp (w * x) * (f x : ℂ))) :
    Integrable (fun u : ℝ => Complex.exp (w * u) * (movingCuspSource S f u : ℂ)) ∧
      (∫ u : ℝ, Complex.exp (w * u) * (movingCuspSource S f u : ℂ)) =
        (∏ p ∈ S, (1 - (p : ℂ) ^ ((1 / 2 : ℂ) - w))) *
          ∫ x : ℝ, Complex.exp (w * x) * (f x : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [movingCuspSource_empty, hf]
  | @insert p S hpS ih =>
    have hp : 0 < p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, 0 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨hint, heq⟩ := ih hS'
    have hfun : (fun u : ℝ => Complex.exp (w * u) * (movingCuspSource (insert p S) f u : ℂ)) =
        fun u : ℝ => Complex.exp (w * u) * (movingCuspSource S f u : ℂ) -
          (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (Complex.exp (w * u) * (movingCuspSource S f (u + Real.log p) : ℂ)) := by
      funext u
      rw [movingCuspSource_insert hp hS' hpS]
      push_cast
      ring
    have hshift := integrable_cexp_mul_comp_add (Real.log p)
      (G := fun y => (movingCuspSource S f y : ℂ)) hint
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hint.sub (hshift.const_mul _)
    · rw [hfun, integral_sub hint (hshift.const_mul _), integral_const_mul,
        integral_cexp_mul_comp_add w (Real.log p) (fun y => (movingCuspSource S f y : ℂ)),
        heq, Finset.prod_insert hpS]
      have hpow : (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (-(w * (Real.log p : ℂ))) =
          (p : ℂ) ^ ((1 / 2 : ℂ) - w) := by
        rw [natCast_cpow_eq_cexp_mul_log hp, Complex.ofReal_cpow (by positivity),
          show ((p : ℝ) : ℂ) = (p : ℂ) by norm_cast, natCast_cpow_eq_cexp_mul_log hp,
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← hpow]
      ring

/-- `F(w) = ∫ e^{wu} k(u) du = XiC(iw)`. -/
theorem integral_cexp_mul_movingCuspSource_theta {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (w : ℂ) :
    (∫ u : ℝ, Complex.exp (w * u) * (movingCuspSource S thetaCuspFullSource u : ℂ)) =
      XiC (Complex.I * w) * ∏ p ∈ S, (1 - (p : ℂ) ^ ((1 / 2 : ℂ) - w)) := by
  rw [(integral_cexp_mul_movingCuspSource S hS _ w (integrable_cexp_mul_thetaCuspFullSource w)).2,
    integral_cexp_mul_thetaCuspFullSource, mul_comm]

theorem integrable_cexp_mul_movingCuspSource_theta {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (w : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (w * u) * (movingCuspSource S thetaCuspFullSource u : ℂ)) :=
  (integral_cexp_mul_movingCuspSource S hS _ w (integrable_cexp_mul_thetaCuspFullSource w)).1

/-- **(2), reflected form.**  `F(w)∏(1 − p^{1/2−w}) = μ(P) P^{1/2−w} F(−w) ∏(1 − p^{−1/2+w})`. -/
theorem XiC_mul_prod_one_sub_eq_reflected {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (w : ℂ) :
    XiC (Complex.I * w) * ∏ p ∈ S, (1 - (p : ℂ) ^ ((1 / 2 : ℂ) - w)) =
      ((ArithmeticFunction.moebius (∏ p ∈ S, p) : ℤ) : ℂ) *
        ((∏ p ∈ S, p : ℕ) : ℂ) ^ ((1 / 2 : ℂ) - w) * XiC (Complex.I * -w) *
          ∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) + w)) := by
  have hfac : ∀ p ∈ S, (1 - (p : ℂ) ^ ((1 / 2 : ℂ) - w)) =
      -1 * (p : ℂ) ^ ((1 / 2 : ℂ) - w) * (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) + w)) := by
    intro p hp
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    have h1 : (p : ℂ) ^ ((1 / 2 : ℂ) - w) * (p : ℂ) ^ (-(1 / 2 : ℂ) + w) = 1 := by
      rw [← Complex.cpow_add _ _ hp0, show (1 / 2 : ℂ) - w + (-(1 / 2 : ℂ) + w) = 0 by ring,
        Complex.cpow_zero]
    linear_combination (-1 : ℂ) * h1
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    moebius_prod_of_primes hS, natCast_prod_cpow_eq_prod_cpow, show Complex.I * -w = -(Complex.I * w) by ring, XiC_even]
  simp only [Finset.prod_const]
  push_cast
  ring

theorem norm_cexp_mul_real_weight (w : ℂ) (u : ℝ) (r : ℝ) :
    ‖Complex.exp (w * u) * (r : ℂ)‖ = Real.exp (w.re * u) * |r| := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  congr 2
  simp

/-- **(5) Mellin law of the cofinal dual source.**  For `Re w > 3/2`, with absolute convergence,
`∫ e^{wu} R_∞(u) du = F(w)/ζ(w − 1/2)`. -/
theorem integral_cexp_mul_movingCuspDualLimit {w : ℂ} (hw : 3 / 2 < w.re) :
    Integrable (fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) ∧
      (∫ u : ℝ, Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) =
        XiC (Complex.I * w) * (riemannZeta (w - 1 / 2))⁻¹ := by
  set F : ℕ → ℝ → ℂ := fun n u =>
    Complex.exp (w * u) * ((movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n) : ℝ) : ℂ)
  have hk := integrable_cexp_mul_thetaCuspFullSource w
  have hFint : ∀ n, Integrable (F n) := fun n => by
    have := (integrable_cexp_mul_comp_add (Real.log n)
      (G := fun y => (thetaCuspFullSource y : ℂ)) hk).const_mul (movingCuspLimitWeight n : ℂ)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [F]; push_cast; ring
  set I : ℝ := ∫ x : ℝ, ‖Complex.exp (w * x) * (thetaCuspFullSource x : ℂ)‖
  have hFnorm : ∀ n, 0 < n → (∫ u : ℝ, ‖F n u‖) = |movingCuspLimitWeight n| * (n : ℝ) ^ (-w.re) * I := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hshift := integral_add_right_eq_self (μ := volume)
      (fun y : ℝ => ‖Complex.exp (w * y) * (thetaCuspFullSource y : ℂ)‖) (Real.log n)
    have hpt : ∀ u : ℝ, ‖F n u‖ = |movingCuspLimitWeight n| * (n : ℝ) ^ (-w.re) *
        ‖Complex.exp (w * (((u + Real.log n : ℝ)) : ℂ)) *
          (thetaCuspFullSource (u + Real.log n) : ℂ)‖ := by
      intro u
      simp only [F]
      rw [norm_cexp_mul_real_weight, norm_cexp_mul_real_weight, abs_mul, Real.rpow_def_of_pos hnR]
      have : Real.exp (w.re * u) = Real.exp (Real.log n * -w.re) * Real.exp (w.re * (u + Real.log n)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    simp_rw [hpt]
    rw [integral_const_mul, hshift]
  have hsum : Summable fun n => ∫ u : ℝ, ‖F n u‖ := by
    have hs : Summable fun n : ℕ => (n : ℝ) ^ (1 / 2 - w.re) * I :=
      (Real.summable_nat_rpow.2 (by linarith)).mul_right I
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) (fun n => ?_) hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [F, movingCuspLimitWeight, ArithmeticFunction.map_zero, Int.cast_zero, zero_mul,
        Complex.ofReal_zero, mul_zero, norm_zero, integral_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg 0) _) (integral_nonneg fun x => norm_nonneg _)
    · rw [hFnorm n hn]
      have hI : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hw' : |movingCuspLimitWeight n| ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
        rw [movingCuspLimitWeight, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) ^ (1/2:ℝ))]
        have hμ : |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        nlinarith [Real.rpow_pos_of_pos hnR (1/2 : ℝ)]
      calc |movingCuspLimitWeight n| * (n : ℝ) ^ (-w.re) * I
          ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-w.re) * I := by gcongr
        _ = (n : ℝ) ^ (1 / 2 - w.re) * I := by
          rw [← Real.rpow_add hnR]; ring_nf
  have hfun : (fun u : ℝ => Complex.exp (w * u) * (movingCuspDualLimit u : ℂ)) =
      fun u => ∑' n, F n u := by
    funext u
    simp only [F, movingCuspDualLimit, logShiftSeries]
    rw [Complex.ofReal_tsum, tsum_mul_left]
  have hInt : ∀ n, 0 < n → (∫ u, F n u) =
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-(w - 1 / 2)) * XiC (Complex.I * w) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (fun u => F n u) = fun u : ℝ => (movingCuspLimitWeight n : ℂ) *
        (Complex.exp (w * u) * (thetaCuspFullSource (u + Real.log n) : ℂ)) := by
      funext u; simp only [F]; push_cast; ring
    rw [h1, integral_const_mul, integral_cexp_mul_comp_add w (Real.log n)
      (fun y => (thetaCuspFullSource y : ℂ)), integral_cexp_mul_thetaCuspFullSource,
      movingCuspLimitWeight]
    push_cast
    rw [Complex.ofReal_cpow hnR.le, show ((n : ℝ) : ℂ) = (n : ℂ) by norm_cast,
      natCast_cpow_eq_cexp_mul_log hn, natCast_cpow_eq_cexp_mul_log hn,
      mul_assoc, mul_assoc, ← mul_assoc (Complex.exp _), ← Complex.exp_add]
    have hl : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [Complex.ofReal_log hnR.le, Complex.ofReal_natCast]
    rw [hl]
    push_cast
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hFint hsum
  · rw [hfun, ← (hasSum_integral_of_summable_integral_norm hFint hsum).tsum_eq]
    have hz : 1 < (w - 1 / 2).re := by simp; linarith
    rw [← tsum_moebius_mul_natCast_cpow hz, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, movingCuspLimitWeight]
    · rw [hInt n hn]; ring

/-! ## The positive cusp and the one-sign obstruction -/

section PositiveCusp

open HedenmalmThetaSource

theorem thetaEnvelope_add_log_div {u : ℝ} {n : ℕ} (hn : 0 < n) :
    thetaEnvelope (u + Real.log n) / thetaEnvelope u =
      (n : ℝ) ^ (9 / 2 : ℝ) * Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : Real.exp (2 * (u + Real.log n)) = Real.exp (2 * u) * (n : ℝ) ^ 2 := by
    have hl : Real.exp (2 * Real.log n) = (n : ℝ) ^ 2 := by
      rw [← Real.exp_log (pow_pos hnR 2), Real.log_pow]; norm_num
    rw [mul_add, Real.exp_add, hl]
  rw [div_eq_iff (thetaEnvelope_pos u).ne', thetaEnvelope, thetaEnvelope, h2,
    Real.rpow_def_of_pos hnR]
  rw [show 9 * (u + Real.log n) / 2 = 9 * u / 2 + Real.log n * (9 / 2) by ring, Real.exp_add]
  have : Real.exp (-Real.pi * (Real.exp (2 * u) * (n : ℝ) ^ 2)) =
      Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) * Real.exp (-Real.pi * Real.exp (2 * u)) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]; ring

/-- For `u ≥ 1` and `n ≥ 2`: `|μ(n)√n k(u + log n)| / k(u) ≤ (U/L) e^π n⁶ e^{−πn²}`, and each
ratio tends to zero. -/
theorem abs_movingCuspTerm_div_le {u : ℝ} (hu : 1 ≤ u) {n : ℕ} (hn : 2 ≤ n) :
    |movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n)| / thetaCuspFullSource u ≤
      thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6 *
        Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) := by
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hu0 : 0 < u := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hk := thetaCuspFullSource_pos u
  have hlow := thetaCuspFullSource_ge_envelope hu0
  have hup := thetaCuspFullSource_le_envelope (show 0 ≤ u + Real.log n by linarith)
  have hkn := thetaCuspFullSource_pos (u + Real.log n)
  have hL := thetaEnvelopeLower_pos
  have hU := thetaEnvelopeUpper_pos
  have henv := thetaEnvelope_add_log_div (u := u) hn0
  have hE := thetaEnvelope_pos u
  rw [div_le_iff₀ hk, abs_mul, abs_of_pos hkn]
  have hw : |movingCuspLimitWeight n| ≤ (n : ℝ) ^ 1 := polyBoundedWeight_movingCuspLimitWeight n
  have h92 : (n : ℝ) ^ (9 / 2 : ℝ) ≤ (n : ℝ) ^ 5 := by
    have h := Real.rpow_le_rpow_of_exponent_le hnR (show (9 / 2 : ℝ) ≤ ((5 : ℕ) : ℝ) by norm_num)
    rwa [Real.rpow_natCast] at h
  have hexp : 0 < Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) := Real.exp_pos _
  have henv' : thetaEnvelope (u + Real.log n) =
      (n : ℝ) ^ (9 / 2 : ℝ) * Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) *
        thetaEnvelope u := by
    rw [← henv, div_mul_cancel₀ _ hE.ne']
  calc |movingCuspLimitWeight n| * thetaCuspFullSource (u + Real.log n)
      ≤ (n : ℝ) ^ 1 * (thetaEnvelopeUpper * thetaEnvelope (u + Real.log n)) :=
        mul_le_mul hw hup hkn.le (by positivity)
    _ = thetaEnvelopeUpper * (n : ℝ) * (n : ℝ) ^ (9 / 2 : ℝ) *
          Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) * thetaEnvelope u := by
        rw [henv']; ring
    _ ≤ thetaEnvelopeUpper * (n : ℝ) * (n : ℝ) ^ 5 *
          Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) * thetaEnvelope u := by
        gcongr
    _ = thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6 *
          Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) *
            (thetaEnvelopeLower * thetaEnvelope u) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **The first theta atom dominates at the positive cusp:** `R_∞(u)/k(u) → 1`. -/
theorem tendsto_movingCuspDualLimit_div_thetaCuspFullSource :
    Tendsto (fun u => movingCuspDualLimit u / thetaCuspFullSource u) atTop (𝓝 1) := by
  set c : ℝ → ℕ → ℝ := fun u n => if n = 1 then 0 else
    movingCuspLimitWeight n * thetaCuspFullSource (u + Real.log n) / thetaCuspFullSource u
  have hsplit : ∀ u, movingCuspDualLimit u / thetaCuspFullSource u = 1 + ∑' n, c u n := by
    intro u
    have hs := summable_movingCuspDualLimit u
    rw [movingCuspDualLimit, logShiftSeries, hs.tsum_eq_add_tsum_ite 1, add_div]
    have h1 : movingCuspLimitWeight 1 * thetaCuspFullSource (u + Real.log (1 : ℕ)) /
        thetaCuspFullSource u = 1 := by
      simp [movingCuspLimitWeight, (thetaCuspFullSource_pos u).ne']
    rw [h1, ← tsum_div_const]
    congr 1
    refine tsum_congr fun n => ?_
    simp only [c]
    split_ifs <;> simp
  simp_rw [hsplit]
  set b : ℕ → ℝ := fun n => if n < 2 then 0 else
    thetaEnvelopeUpper / thetaEnvelopeLower * Real.exp Real.pi * ((n : ℝ) ^ 6 *
      Real.exp (-Real.pi * (n : ℝ) ^ 2))
  have hb : Summable b := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_pow_mul_exp_neg_nat_sq 6 Real.pi_pos).mul_left
        (thetaEnvelopeUpper / thetaEnvelopeLower * Real.exp Real.pi))
    · simp only [b]; split_ifs
      · exact le_rfl
      · have := thetaEnvelopeLower_pos; have := thetaEnvelopeUpper_pos; positivity
    · simp only [b]; split_ifs
      · have := thetaEnvelopeLower_pos; have := thetaEnvelopeUpper_pos; positivity
      · exact le_of_eq (by ring)
  have hlim : ∀ n, Tendsto (fun u => c u n) atTop (𝓝 0) := by
    intro n
    by_cases h1 : n = 1
    · simp [c, h1]
    by_cases h0 : n = 0
    · simp [c, h0, movingCuspLimitWeight]
    have hn : 2 ≤ n := by omega
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
    have hmaj : Tendsto (fun u => thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6 *
        Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1))) atTop (𝓝 0) := by
      have h := Real.tendsto_exp_atBot.comp ((Real.tendsto_exp_atTop.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))).const_mul_atTop_of_neg
          (show -Real.pi * ((n : ℝ) ^ 2 - 1) < 0 by nlinarith [Real.pi_pos]))
      have := h.const_mul (thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6)
      rw [mul_zero] at this
      refine this.congr fun u => ?_
      simp only [Function.comp, id]; ring_nf
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun u => abs_nonneg _) ?_ hmaj
    filter_upwards [eventually_ge_atTop 1] with u hu
    simp only [c, if_neg h1, Function.comp_apply]
    rw [abs_div, abs_of_pos (thetaCuspFullSource_pos u)]
    exact abs_movingCuspTerm_div_le hu hn
  have hbound : ∀ᶠ u in atTop, ∀ n, ‖c u n‖ ≤ b n := by
    filter_upwards [eventually_ge_atTop 1] with u hu n
    rw [Real.norm_eq_abs]
    by_cases h1 : n = 1
    · simp only [c, if_pos h1, abs_zero, b]; split_ifs <;> [exact le_rfl; omega]
    by_cases h0 : n = 0
    · simp [c, h0, movingCuspLimitWeight, b]
    have hn : 2 ≤ n := by omega
    simp only [c, if_neg h1, b, if_neg (show ¬ n < 2 by omega)]
    rw [abs_div, abs_of_pos (thetaCuspFullSource_pos u)]
    refine (abs_movingCuspTerm_div_le hu hn).trans ?_
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have he : Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1)) ≤
        Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have h1' : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
      have hpos : 0 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_right h1' hpos]
    have := thetaEnvelopeLower_pos; have := thetaEnvelopeUpper_pos
    calc thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6 *
          Real.exp (-Real.pi * Real.exp (2 * u) * ((n : ℝ) ^ 2 - 1))
        ≤ thetaEnvelopeUpper / thetaEnvelopeLower * (n : ℝ) ^ 6 *
          (Real.exp Real.pi * Real.exp (-Real.pi * (n : ℝ) ^ 2)) := by gcongr
      _ = _ := by ring
  have h := tendsto_tsum_of_dominated_convergence hb hlim hbound
  rw [tsum_zero] at h
  simpa using h.const_add 1

/-- `R_∞ > 0` on a far positive ray. -/
theorem eventually_movingCuspDualLimit_pos : ∀ᶠ u in atTop, 0 < movingCuspDualLimit u := by
  filter_upwards [tendsto_movingCuspDualLimit_div_thetaCuspFullSource.eventually
    (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
  exact (div_pos_iff_of_pos_right (thetaCuspFullSource_pos u)).1 hu

theorem tendsto_XiC_mul_inv_riemannZeta :
    Tendsto (fun σ : ℝ => XiC (Complex.I * σ) * (riemannZeta ((σ : ℂ) - 1 / 2))⁻¹)
      (𝓝[>] (3 / 2)) (𝓝 0) := by
  have hX : Tendsto (fun σ : ℝ => XiC (Complex.I * σ)) (𝓝[>] (3 / 2)) (𝓝 (XiC (Complex.I * (3 / 2 : ℝ)))) :=
    ((XiC_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal)).tendsto _).mono_left
      nhdsWithin_le_nhds
  have hs : Tendsto (fun σ : ℝ => (σ : ℂ) - 1 / 2) (𝓝[>] (3 / 2)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun σ : ℝ => (σ : ℂ) - 1 / 2) (𝓝 (3 / 2)) (𝓝 (((3 / 2 : ℝ) : ℂ) - 1 / 2)) :=
        (Complex.continuous_ofReal.sub continuous_const).tendsto _
      rw [show ((3 / 2 : ℝ) : ℂ) - 1 / 2 = 1 by push_cast; norm_num] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [hσ.out]
  have hres := riemannZeta_residue_one.comp hs
  have hzero : Tendsto (fun σ : ℝ => (σ : ℂ) - 1 / 2 - 1) (𝓝[>] (3 / 2)) (𝓝 0) := by
    have := (tendsto_nhdsWithin_iff.1 hs).1
    simpa using this.sub_const 1
  have hinv : Tendsto (fun σ : ℝ => (riemannZeta ((σ : ℂ) - 1 / 2))⁻¹) (𝓝[>] (3 / 2)) (𝓝 0) := by
    have h := hzero.div hres one_ne_zero
    rw [zero_div] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hne : (σ : ℂ) - 1 / 2 - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith [hσ.out]
    simp only [Pi.div_apply, Function.comp_apply]
    rw [div_mul_eq_div_div, div_self hne, one_div]
  simpa using hX.mul hinv

end PositiveCusp

theorem continuous_movingCuspDualLimit : Continuous movingCuspDualLimit :=
  contDiff_movingCuspDualLimit.continuous

/-- **Sign-change theorem.**  `R_∞` is positive on a far positive ray but not nonnegative
everywhere: otherwise `∫ e^{σu}R_∞ = F(σ)/ζ(σ − 1/2)` would stay above a fixed positive mass while
tending to zero as `σ ↓ 3/2`. -/
theorem not_forall_movingCuspDualLimit_nonneg : ¬ ∀ u, 0 ≤ movingCuspDualLimit u := by
  intro hnn
  obtain ⟨U, hU⟩ := eventually_atTop.1 eventually_movingCuspDualLimit_pos
  set U₀ : ℝ := max U 0
  have hpos : ∀ u ∈ Ioo U₀ (U₀ + 1), 0 < Real.exp (3 / 2 * u) * movingCuspDualLimit u :=
    fun u hu => mul_pos (Real.exp_pos _) (hU u (le_trans (le_max_left _ _) hu.1.le))
  have hcont : ∀ σ : ℝ, Continuous fun u => Real.exp (σ * u) * movingCuspDualLimit u := fun σ =>
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_movingCuspDualLimit
  set c : ℝ := ∫ u in U₀..U₀ + 1, Real.exp (3 / 2 * u) * movingCuspDualLimit u
  have hc : 0 < c := intervalIntegral.intervalIntegral_pos_of_pos_on
    ((hcont _).intervalIntegrable _ _) hpos (by linarith)
  have hle : ∀ σ : ℝ, 3 / 2 < σ →
      c ≤ ‖XiC (Complex.I * σ) * (riemannZeta ((σ : ℂ) - 1 / 2))⁻¹‖ := by
    intro σ hσ
    obtain ⟨hint, heq⟩ := integral_cexp_mul_movingCuspDualLimit (w := (σ : ℂ)) (by simpa using hσ)
    have hreal : (fun u : ℝ => Complex.exp ((σ : ℂ) * u) * (movingCuspDualLimit u : ℂ)) =
        fun u => ((Real.exp (σ * u) * movingCuspDualLimit u : ℝ) : ℂ) := by
      funext u; push_cast; rfl
    rw [hreal] at hint heq
    have hintR : Integrable fun u : ℝ => Real.exp (σ * u) * movingCuspDualLimit u :=
      hint.norm.congr (Eventually.of_forall fun u => by
        simp only
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hnn u))])
    rw [integral_complex_ofReal] at heq
    rw [← heq, Complex.norm_real, Real.norm_eq_abs]
    refine le_trans ?_ (le_abs_self _)
    calc c ≤ ∫ u in U₀..U₀ + 1, Real.exp (σ * u) * movingCuspDualLimit u := by
          refine intervalIntegral.integral_mono_on (by linarith) ((hcont _).intervalIntegrable _ _)
            ((hcont _).intervalIntegrable _ _) fun u hu => ?_
          have hu0 : 0 ≤ u := le_trans (le_max_right _ _) hu.1
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by nlinarith)) (hnn u)
      _ = ∫ u in Ioc U₀ (U₀ + 1), Real.exp (σ * u) * movingCuspDualLimit u :=
          intervalIntegral.integral_of_le (by linarith)
      _ ≤ ∫ u, Real.exp (σ * u) * movingCuspDualLimit u :=
          setIntegral_le_integral hintR (Eventually.of_forall fun u =>
            mul_nonneg (Real.exp_pos _).le (hnn u))
  have hlim := tendsto_XiC_mul_inv_riemannZeta.norm
  rw [norm_zero] at hlim
  have : c ≤ 0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun σ hσ => hle σ hσ)
  linarith

end

end RHTower
