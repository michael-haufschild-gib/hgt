import GaloisForLFunctions.FiniteFreeProbability.FiniteFreeDeBruijnNewman
import GaloisForLFunctions.FiniteFreeProbability.SymmetrizedEulerHorizon
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer

/-!
# A Möbius-mollified finite free criterion for the Riemann hypothesis

For a nonempty finite set of primes `S`, `σ > 0` and a phase `c ≥ θ_S/2` (`θ_S = Σ_{p∈S} log p`),
multiply `Ξ(w)` by the translated Möbius product `M(w) = e^{icw}Π_{p∈S}(1 − p^{−σ−iw})`.

**Theorem.** RH holds iff the reversed Jensen polynomials of `Ξ·M` have all roots in the open lower
half-plane for infinitely many degrees; under RH this holds at every degree.

* Under RH, `R_d(Ξ)` is real-rooted (`Ξ` is Laguerre–Pólya) and `R_d(M)` has all roots in `Im < 0`
  (Hermite–Biehler stability of the normalized Euler factors), so strict Walsh puts the roots of
  `R_d(ΞM) = R_d(M) ⊞_d R_d(Ξ)` in `Im < 0`.
* Conversely, `R_d(F)(d/u) = (d/u)^d Φ_d(u)` with `Φ_d(u) = Σ_{k≤d} f_k d!/((d−k)! d^k) u^k`, and
  `Φ_d → F` locally uniformly (Tannery). Stability puts every zero of `Φ_d` in `Im > 0`, so by
  Hurwitz `F = ΞM` has no zero in `Im < 0`. The zeros of `Ξ` are closed under conjugation, hence
  real.

The pole side cannot be attached in this way: pole pieces, `ζ(σ + iw)` and `Γ(1/4 + iw/2)` are
unstable for every phase.
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## The scaled Jensen approximants -/

/-- `Φ_d(u) = Σ_{k≤d} f_k d!/((d−k)! d^k) u^k`. -/
def scaledJensen (f : ℕ → ℂ) (d : ℕ) (u : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1), f k * ((d.descFactorial k : ℂ) / (d : ℂ) ^ k) * u ^ k

theorem eval_jensenRev_div (f : ℕ → ℂ) {d : ℕ} (hd : 0 < d) {u : ℂ} (hu : u ≠ 0) :
    (jensenRev d (PowerSeries.mk f)).eval ((d : ℂ) / u) =
      ((d : ℂ) / u) ^ d * scaledJensen f d u := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [jensenRev_eq_sum, eval_finsetSum, scaledJensen, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [eval_mul, eval_C, eval_pow, eval_X, PowerSeries.coeff_mk]
  have hsplit : ((d : ℂ) / u) ^ d = ((d : ℂ) / u) ^ (d - k) * ((d : ℂ) / u) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hsplit, div_pow, div_pow]
  field_simp

theorem scaledJensen_zero (f : ℕ → ℂ) (d : ℕ) : scaledJensen f d 0 = f 0 := by
  rw [scaledJensen, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; rw [zero_pow hk, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

/-- Stability of `R_d(F)` puts every zero of `Φ_d` in the open upper half-plane. -/
theorem im_pos_of_scaledJensen_eq_zero {f : ℕ → ℂ} {d : ℕ} (hd : 0 < d) (hf0 : f 0 ≠ 0)
    (hst : ∀ x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im < 0) {u : ℂ}
    (hu : scaledJensen f d u = 0) : 0 < u.im := by
  have hu0 : u ≠ 0 := by rintro rfl; rw [scaledJensen_zero] at hu; exact hf0 hu
  have hroot := hst _ (by rw [IsRoot, eval_jensenRev_div f hd hu0, hu, mul_zero])
  rw [Complex.div_im] at hroot
  simp only [natCast_im, zero_mul, natCast_re, zero_div] at hroot
  have hns : 0 < Complex.normSq u := Complex.normSq_pos.2 hu0
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  by_contra hle
  push Not at hle
  have : (d : ℝ) * u.im / Complex.normSq u ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hdpos.le hle) hns.le
  linarith

theorem norm_descFactorial_div_pow_le (d k : ℕ) :
    ‖(d.descFactorial k : ℂ) / (d : ℂ) ^ k‖ ≤ 1 := by
  rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp [zero_pow hk.ne']
  · rw [div_le_one (by positivity)]
    exact_mod_cast Nat.descFactorial_le_pow d k

/-- **Tannery.** Along any sequence of degrees tending to infinity, `Φ_d → Σ_k f_k u^k` locally
uniformly, provided `Σ_k ‖f_k‖ R^k < ∞` for every `R`. -/
theorem tendstoLocallyUniformly_scaledJensen {f : ℕ → ℂ}
    (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k) {ψ : ℕ → ℕ} (hψ : Tendsto ψ atTop atTop) :
    TendstoLocallyUniformly (fun n => scaledJensen f (ψ n)) (fun u => ∑' k, f k * u ^ k) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R := max R₀ 0
  have hKR : ∀ u ∈ K, ‖u‖ ≤ R := fun u hu => by
    have := hR₀ hu; rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set c : ℕ → ℕ → ℂ := fun d k => (d.descFactorial k : ℂ) / (d : ℂ) ^ k
  set e : ℕ → ℝ := fun d => ∑' k, ‖f k‖ * ‖1 - c d k‖ * R ^ k
  have hbound : ∀ d k, ‖f k‖ * ‖1 - c d k‖ * R ^ k ≤ 2 * (‖f k‖ * R ^ k) := fun d k => by
    have h1 : ‖1 - c d k‖ ≤ 2 := (norm_sub_le _ _).trans (by
      rw [norm_one]; linarith [norm_descFactorial_div_pow_le d k])
    have hR : 0 ≤ R ^ k := pow_nonneg (le_max_right _ _) k
    nlinarith [norm_nonneg (f k), mul_nonneg (norm_nonneg (f k)) hR]
  have he : Tendsto e atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (bound := fun k => 2 * (‖f k‖ * R ^ k))
      (f := fun d k => ‖f k‖ * ‖1 - c d k‖ * R ^ k) (g := fun _ => (0 : ℝ))
      ((hf R).mul_left 2) (fun k => by
        have hc := tendsto_descFactorial_div_pow k
        have : Tendsto (fun d => ‖1 - c d k‖) atTop (𝓝 ‖(1 : ℂ) - 1‖) :=
          (tendsto_const_nhds.sub hc).norm
        rw [sub_self, norm_zero] at this
        simpa using (this.const_mul ‖f k‖).mul_const (R ^ k))
      (Eventually.of_forall fun d k => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hbound d k)
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hψ.eventually (he.eventually (gt_mem_nhds hε))] with n hn u hu
  have hsumu : Summable fun k => ‖f k‖ * ‖u‖ ^ k := hf ‖u‖
  have hfin : scaledJensen f (ψ n) u = ∑' k, f k * c (ψ n) k * u ^ k := by
    rw [scaledJensen, tsum_eq_sum (s := Finset.range (ψ n + 1)) fun k hk => by
      simp only [c, Nat.descFactorial_eq_zero_iff_lt.2 (by simpa using hk), Nat.cast_zero,
        zero_div, mul_zero, zero_mul]]
  have hs1 : Summable fun k => f k * u ^ k :=
    Summable.of_norm (hsumu.congr fun k => by rw [norm_mul, norm_pow])
  have hs2 : Summable fun k => f k * c (ψ n) k * u ^ k :=
    Summable.of_norm_bounded hsumu fun k => by
      rw [norm_mul, norm_mul, norm_pow]
      have hc1 : ‖c (ψ n) k‖ ≤ 1 := norm_descFactorial_div_pow_le (ψ n) k
      nlinarith [mul_le_mul_of_nonneg_left hc1
        (mul_nonneg (norm_nonneg (f k)) (pow_nonneg (norm_nonneg u) k))]
  rw [dist_eq_norm, hfin, ← hs1.tsum_sub hs2]
  refine lt_of_le_of_lt ?_ hn
  have hs3 : Summable fun k => ‖f k‖ * ‖1 - c (ψ n) k‖ * R ^ k :=
    Summable.of_nonneg_of_le (fun k => by positivity) (hbound (ψ n)) ((hf R).mul_left 2)
  refine (norm_tsum_le_tsum_norm ((hs1.sub hs2).norm)).trans
    (Summable.tsum_le_tsum (fun k => ?_) (hs1.sub hs2).norm hs3)
  rw [show f k * u ^ k - f k * c (ψ n) k * u ^ k = f k * (1 - c (ψ n) k) * u ^ k by ring,
    norm_mul, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg u) (hKR u hu) k)
    (by positivity)

/-- **Hurwitz.** If `R_d(F)` is stable for infinitely many `d`, the entire function
`F(u) = Σ_k f_k u^k` has no zeros in the open lower half-plane. -/
theorem im_nonneg_of_frequently_stable {f : ℕ → ℂ} (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k)
    (hf0 : f 0 ≠ 0)
    (h : ∃ᶠ d : ℕ in atTop, ∀ x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im < 0)
    {z : ℂ} (hz : ∑' k, f k * z ^ k = 0) : 0 ≤ z.im := by
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop h
  set ψ : ℕ → ℕ := fun n => φ (n + 1)
  have hψ : Tendsto ψ atTop atTop :=
    hφ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hψpos : ∀ n, 0 < ψ n := fun n => lt_of_le_of_lt (Nat.zero_le _) (hφ (Nat.succ_pos n))
  have hconv := tendstoLocallyUniformly_scaledJensen hf hψ
  have hdiff : ∀ n, Differentiable ℂ (scaledJensen f (ψ n)) := fun n => by
    unfold scaledJensen; fun_prop
  have hF : Differentiable ℂ fun u => ∑' k, f k * u ^ k := by
    have := (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
      (Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ
    exact differentiableOn_univ.1 this
  refine RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv
    (fun w _ => hF.analyticAt w) (Eventually.of_forall hdiff)
    (isClosed_le continuous_const Complex.continuous_im)
    (Eventually.of_forall fun n w hw => (im_pos_of_scaledJensen_eq_zero (hψpos n) hf0
      (hP (n + 1)) hw).le) (a := 0) ?_ hz
  rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
  simpa using hf0

/-! ## Entire power series and their products -/

theorem summable_norm_mul_pow_of_summable {f : ℕ → ℂ}
    (hf : ∀ z : ℂ, Summable fun k => f k * z ^ k) (R : ℝ) :
    Summable fun k => ‖f k‖ * R ^ k := by
  set r := |R| + 1
  have hr : 0 < r := by positivity
  have hb := (hf ((2 * r : ℝ) : ℂ)).tendsto_atTop_zero.norm
  rw [norm_zero] at hb
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hb) 1 one_pos
  have hgeo : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (summable_nat_add_iff N).1 (Summable.of_norm_bounded hgeo fun k => ?_)
  have hk := hN (k + N) (by omega)
  rw [dist_zero_right, norm_norm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * r)] at hk
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (norm_nonneg _)]
  have hRr : |R| ≤ r := by simp only [r]; linarith
  have hfk : ‖f (k + N)‖ ≤ 1 / (2 * r) ^ (k + N) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc ‖f (k + N)‖ * |R| ^ (k + N) ≤ 1 / (2 * r) ^ (k + N) * r ^ (k + N) :=
        mul_le_mul hfk (pow_le_pow_left₀ (abs_nonneg R) hRr _) (by positivity) (by positivity)
    _ = (1 / 2) ^ (k + N) := by field_simp; rw [← mul_pow]; congr 1; ring
    _ ≤ (1 / 2) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- The Cauchy product of two entire power series is the power series of the product. -/
theorem hasSum_coeff_mul {F G : ℂ → ℂ} {f g : ℕ → ℂ}
    (hF : ∀ z, HasSum (fun k => f k * z ^ k) (F z)) (hG : ∀ z, HasSum (fun k => g k * z ^ k) (G z))
    (z : ℂ) :
    HasSum (fun k => PowerSeries.coeff k (PowerSeries.mk f * PowerSeries.mk g) * z ^ k)
      (F z * G z) := by
  have hFn := summable_norm_mul_pow_of_summable (fun w => (hF w).summable) ‖z‖
  have hGn := summable_norm_mul_pow_of_summable (fun w => (hG w).summable) ‖z‖
  have h1 : Summable fun k => ‖f k * z ^ k‖ := hFn.congr fun k => by rw [norm_mul, norm_pow]
  have h2 : Summable fun k => ‖g k * z ^ k‖ := hGn.congr fun k => by rw [norm_mul, norm_pow]
  have hcp := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h1 h2
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm h1 h2
  rw [(hF z).tsum_eq, (hG z).tsum_eq] at hcp
  rw [hcp]
  have hcoeff : ∀ k, PowerSeries.coeff k (PowerSeries.mk f * PowerSeries.mk g) * z ^ k =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, f p.1 * z ^ p.1 * (g p.2 * z ^ p.2) :=
      fun k => by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [PowerSeries.coeff_mk]
    rw [← hp, pow_add]; ring
  simp_rw [hcoeff]
  exact (Summable.of_norm hsum).hasSum

/-! ## The Möbius mollifier -/

/-- The coefficients of `M(w) = e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` define an entire function. -/
theorem hasSum_translatedMobiusProduct (S : Finset Nat.Primes) (σ c : ℝ) (z : ℂ) :
    HasSum (fun k => PowerSeries.coeff k (translatedMobiusProduct S σ c) * z ^ k)
      (∑ T ∈ S.powerset, (mobiusWeight σ T : ℂ) *
        Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z)) := by
  rw [translatedMobiusProduct_eq]
  simp only [map_sum, Finset.sum_mul]
  refine hasSum_sum fun T _ => ?_
  have h := NormedSpace.expSeries_div_hasSum_exp (I * ((c - logFrequency T : ℝ) : ℂ) * z)
  rw [← Complex.exp_eq_exp_ℂ] at h
  refine (h.mul_left (mobiusWeight σ T : ℂ)).congr_fun fun k => ?_
  rw [PowerSeries.coeff_C_mul, expSeries, PowerSeries.coeff_mk, mul_pow]
  push_cast; ring

/-! ## The criterion -/

/-- The Taylor series of `Ξ` at `0`. -/
def xiSeries : PowerSeries ℂ := PowerSeries.mk fun k => ((realTaylorCoeff XiC k : ℝ) : ℂ)

theorem jensenRev_xiSeries (d : ℕ) :
    jensenRev d xiSeries = (jensenReverse (realTaylorCoeff XiC) d).map (algebraMap ℝ ℂ) := by
  rw [← jensenRev_mk_eq_jensenReverse, jensenRev_eq_sum, jensenRev_eq_sum, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [xiSeries]

theorem constantCoeff_xiSeries : PowerSeries.constantCoeff xiSeries = XiC 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, xiSeries, PowerSeries.coeff_mk,
    ofReal_realTaylorCoeff (fun z => XiC_conj z)]
  simp

theorem hasSum_xiSeries (z : ℂ) :
    HasSum (fun k => PowerSeries.coeff k xiSeries * z ^ k) (XiC z) := by
  simpa [xiSeries] using hasSum_realTaylorCoeff XiC_differentiable (fun w => XiC_conj w) z

/-- Under RH the reversed Jensen polynomials of `Ξ` have only real roots. -/
theorem im_eq_zero_of_isRoot_jensenRev_xiSeries (hRH : RiemannHypothesis) (d : ℕ) {x : ℂ}
    (hx : (jensenRev d xiSeries).IsRoot x) : x.im = 0 := by
  have hJ := splits_jensenPoly_realTaylorCoeff (riemannHypothesis_iff_laguerrePolya_XiC.mp hRH)
    (fun z => XiC_conj z) d
  have hR : (jensenReverse (realTaylorCoeff XiC) d).Splits := by
    rw [show jensenReverse (realTaylorCoeff XiC) d =
      (jensenPoly (realTaylorCoeff XiC) d).reflect d by
        rw [← reflect_jensenReverse, Polynomial.reflect_reflect]]
    exact Splits.reflect hJ (natDegree_jensenPoly_le _ _)
  have hne : jensenReverse (realTaylorCoeff XiC) d ≠ 0 := fun h0 => by
    have := jensenRev_ne_zero (d := d) (f := xiSeries) (by rw [constantCoeff_xiSeries]; exact XiC_zero_ne)
    rw [jensenRev_xiSeries, h0, Polynomial.map_zero] at this
    exact this rfl
  rw [jensenRev_xiSeries, IsRoot, eval_map_algebraMap] at hx
  exact im_eq_zero_of_splits hR hne hx

/-- The Möbius-mollified series `Ξ · e^{icw}Π_{p∈S}(1 − p^{−σ−iw})`. -/
def mollifiedXiSeries (S : Finset Nat.Primes) (σ c : ℝ) : PowerSeries ℂ :=
  xiSeries * translatedMobiusProduct S σ c

/-- **Under RH, the mollified Jensen polynomials are stable at every degree.** -/
theorem im_neg_of_isRoot_jensenRev_mollifiedXiSeries (hRH : RiemannHypothesis)
    {S : Finset Nat.Primes} (hS : S.Nonempty) {σ : ℝ} (hσ : 0 < σ) {c : ℝ}
    (hc : logFrequency S / 2 ≤ c) {d : ℕ} {x : ℂ}
    (hx : (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x) : x.im < 0 := by
  have hcM : PowerSeries.constantCoeff (translatedMobiusProduct S σ c) ≠ 0 := by
    rw [constantCoeff_translatedMobiusProduct]
    refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
    rw [sub_ne_zero]; intro h
    have := congrArg Complex.re h
    simp only [one_re, ofReal_re] at this
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := ((p : ℕ) : ℝ)) (z := -σ)
      (by exact_mod_cast p.prop.one_lt) (by linarith)
    linarith
  have hcX : PowerSeries.constantCoeff xiSeries ≠ 0 := by
    rw [constantCoeff_xiSeries]; exact XiC_zero_ne
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exfalso
    have hc0 : PowerSeries.constantCoeff (mollifiedXiSeries S σ c) ≠ 0 := by
      rw [mollifiedXiSeries, map_mul]; exact mul_ne_zero hcX hcM
    have h0 : jensenRev 0 (mollifiedXiSeries S σ c) =
        C (PowerSeries.constantCoeff (mollifiedXiSeries S σ c)) := by
      rw [jensenRev_eq_sum]; simp
    rw [h0, IsRoot, eval_C] at hx
    exact hc0 hx
  rw [mollifiedXiSeries, jensenRev_mul, ffConv_comm (natDegree_jensenRev_le _ _)
    (natDegree_jensenRev_le _ _)] at hx
  have := ffConv_root_im_lt (jensenRev_ne_zero hcM) (natDegree_jensenRev hcM)
    (jensenRev_ne_zero hcX) (natDegree_jensenRev_le _ _) (a := 0) (b := 0)
    (fun r hr => im_neg_of_isRoot_jensenRev_translatedMobiusProduct hS hσ hc hd hr)
    (fun μ hμ => (im_eq_zero_of_isRoot_jensenRev_xiSeries hRH d hμ).le) hx
  linarith

/-- **The Möbius-mollified finite free criterion.** For a nonempty finite set of primes, `σ > 0`
and `c ≥ θ_S/2`: RH holds iff the reversed Jensen polynomials of
`Ξ(w)·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` have all roots in the open lower half-plane for infinitely
many degrees. -/
theorem riemannHypothesis_iff_frequently_stable_mollified {S : Finset Nat.Primes}
    (hS : S.Nonempty) {σ : ℝ} (hσ : 0 < σ) {c : ℝ} (hc : logFrequency S / 2 ≤ c) :
    RiemannHypothesis ↔ ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x → x.im < 0 := by
  constructor
  · intro hRH
    exact Frequently.of_forall fun d x hx =>
      im_neg_of_isRoot_jensenRev_mollifiedXiSeries hRH hS hσ hc hx
  · intro h
    set f : ℕ → ℂ := fun k => PowerSeries.coeff k (mollifiedXiSeries S σ c)
    have hmk : PowerSeries.mk f = mollifiedXiSeries S σ c := by ext k; simp [f]
    set g : ℂ → ℂ := fun z => ∑ T ∈ S.powerset, (mobiusWeight σ T : ℂ) *
      Complex.exp (I * ((c - logFrequency T : ℝ) : ℂ) * z)
    have hsum : ∀ z, HasSum (fun k => f k * z ^ k) (XiC z * g z) := fun z => by
      have := hasSum_coeff_mul (f := fun k => PowerSeries.coeff k xiSeries)
        (g := fun k => PowerSeries.coeff k (translatedMobiusProduct S σ c))
        hasSum_xiSeries (hasSum_translatedMobiusProduct S σ c) z
      have e1 : PowerSeries.mk (fun k => PowerSeries.coeff k xiSeries) = xiSeries := by
        ext k; simp
      have e2 : PowerSeries.mk (fun k => PowerSeries.coeff k (translatedMobiusProduct S σ c)) =
          translatedMobiusProduct S σ c := by ext k; simp
      rw [e1, e2] at this
      exact this
    have hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k :=
      summable_norm_mul_pow_of_summable fun z => (hsum z).summable
    have hf0 : f 0 ≠ 0 := by
      have := (hsum 0).tsum_eq
      rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero]), pow_zero, mul_one] at this
      rw [this]
      refine mul_ne_zero XiC_zero_ne ?_
      have hg0 := (hasSum_translatedMobiusProduct S σ c 0).tsum_eq
      rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero]), pow_zero, mul_one] at hg0
      simp only [g]
      rw [← hg0, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_translatedMobiusProduct]
      refine Finset.prod_ne_zero_iff.2 fun p _ => ?_
      rw [sub_ne_zero]; intro h
      have := congrArg Complex.re h
      simp only [one_re, ofReal_re] at this
      have := Real.rpow_lt_one_of_one_lt_of_neg (x := ((p : ℕ) : ℝ)) (z := -σ)
        (by exact_mod_cast p.prop.one_lt) (by linarith)
      linarith
    have hst : ∃ᶠ d : ℕ in atTop, ∀ x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im < 0 := by
      simpa only [hmk] using h
    refine riemannHypothesis_iff_XiC_zeros_real.2 fun z hz => ?_
    have hlow : ∀ w, XiC w = 0 → 0 ≤ w.im := fun w hw =>
      im_nonneg_of_frequently_stable hf hf0 hst (by rw [(hsum w).tsum_eq, hw, zero_mul])
    have h1 := hlow z hz
    have h2 := hlow (conj z) (by rw [XiC_conj, hz, map_zero])
    rw [conj_im] at h2
    linarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.riemannHypothesis_iff_frequently_stable_mollified
