import GaloisForLFunctions.FiniteFreeProbability.MollifiedJensenCriterion

/-!
# Bounded imaginary parts decide the Riemann hypothesis

Real-rootedness in the finite free criteria can be relaxed to a uniform bound on imaginary parts,
and the mollifier needs no normalization.

**Theorem.** For every finite set of primes `S` (possibly empty), `σ > 0` and every phase `c`:
RH holds iff there is `K` such that, for infinitely many `d`, every root of the reversed Jensen
polynomial of `Ξ(w)·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` has imaginary part `≤ K`. Under RH one may take
`K = θ_S/2 − c` for every `d` (Walsh).

The converse is Hurwitz at the scale `X = d/u`: a root bound `Im(d/u) ≤ K` puts the zeros of the
scaled approximants `Φ_d` in `Im u ≥ −K|u|²/d`, a region exhausting the closed upper half-plane on
compact sets, so the limit `F = Ξ·M` has no zero in `Im < 0`; the zeros of `Ξ` are among them and
are closed under conjugation.
-/

open Polynomial Filter Topology Complex Metric
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-- **Hurwitz with a degree-dependent margin.** If, for infinitely many `d`, the roots of `R_d(F)`
have imaginary parts `≤ K`, the entire function `F(u) = Σ f_k u^k` has no zeros in `Im < 0`. -/
theorem im_nonneg_of_frequently_im_le {f : ℕ → ℂ}
    (hf : ∀ R : ℝ, Summable fun k => ‖f k‖ * R ^ k) (hf0 : f 0 ≠ 0) {K : ℝ}
    (h : ∃ᶠ d : ℕ in atTop, ∀ x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im ≤ K)
    {z : ℂ} (hz : ∑' k, f k * z ^ k = 0) : 0 ≤ z.im := by
  by_contra hneg
  push Not at hneg
  set ε := -z.im / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  set R := ‖z‖ + 1
  have hR : 0 < R := by positivity
  set K' := max K 0
  obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop
    (h.and_eventually (eventually_gt_atTop ⌈K' * R ^ 2 / ε⌉₊))
  have hψ : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hconv := tendstoLocallyUniformly_scaledJensen hf hψ
  have hdiff : ∀ n, Differentiable ℂ (scaledJensen f (φ n)) := fun n => by
    unfold scaledJensen; fun_prop
  have hF : Differentiable ℂ fun u => ∑' k, f k * u ^ k := by
    have := (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
      (Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ
    exact differentiableOn_univ.1 this
  set S : Set ℂ := {w | -ε ≤ w.im} ∪ {w | R ≤ ‖w‖}
  have hS : IsClosed S :=
    (isClosed_le continuous_const Complex.continuous_im).union
      (isClosed_le continuous_const continuous_norm)
  have hzeroS : ∀ n, ∀ w, scaledJensen f (φ n) w = 0 → w ∈ S := fun n w hw => by
    obtain ⟨hst, hbig⟩ := hP n
    have hd : 0 < φ n := lt_of_le_of_lt (Nat.zero_le _) hbig
    by_cases hwR : R ≤ ‖w‖
    · exact Or.inr hwR
    left
    push Not at hwR
    have hw0 : w ≠ 0 := by rintro rfl; rw [scaledJensen_zero] at hw; exact hf0 hw
    have hroot := hst _ (by rw [IsRoot, eval_jensenRev_div f hd hw0, hw, mul_zero])
    rw [Complex.div_im] at hroot
    simp only [natCast_im, zero_mul, natCast_re, zero_div, zero_sub] at hroot
    have hns : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
    have hnsR : Complex.normSq w ≤ R ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg w) hwR.le 2
    have hdpos : (0 : ℝ) < φ n := by exact_mod_cast hd
    have hbig' : K' * R ^ 2 / ε < φ n := lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hbig)
    rw [div_lt_iff₀ hε] at hbig'
    -- `−d Im w / |w|² ≤ K` gives `Im w ≥ −K' |w|²/d ≥ −ε`
    have h0 : -((φ n : ℝ) * w.im) / Complex.normSq w ≤ K' := by
      rw [neg_div]; exact hroot.trans (le_max_left K 0)
    have h1 : -((φ n : ℝ) * w.im) ≤ K' * Complex.normSq w := (div_le_iff₀ hns).1 h0
    have hK' : 0 ≤ K' := le_max_right _ _
    have h2 : K' * Complex.normSq w ≤ K' * R ^ 2 := mul_le_mul_of_nonneg_left hnsR hK'
    show -ε ≤ w.im
    nlinarith
  have hmem := RHTower.zero_mem_closed_of_tendstoLocallyUniformly hconv
    (fun w _ => hF.analyticAt w) (Eventually.of_forall hdiff) hS
    (Eventually.of_forall hzeroS) (a := 0) (by
      rw [tsum_eq_single 0 (fun k hk => by rw [zero_pow hk, mul_zero])]
      simpa using hf0) hz
  rcases hmem with hmem | hmem
  · simp only [Set.mem_setOf_eq, ε] at hmem; linarith
  · simp only [Set.mem_setOf_eq, R] at hmem; linarith

/-- Under RH the roots of `R_d(Ξ·e^{icw}Π_{p∈S}(1 − p^{−σ−iw}))` satisfy `Im ≤ θ_S/2 − c`. -/
theorem im_le_of_isRoot_jensenRev_mollifiedXiSeries (hRH : RiemannHypothesis)
    (S : Finset Nat.Primes) {σ : ℝ} (hσ : 0 < σ) (c : ℝ) {d : ℕ} {x : ℂ}
    (hx : (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x) :
    x.im ≤ logFrequency S / 2 - c := by
  classical
  have hqlt : ∀ p ∈ S, ‖((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ < 1 := fun p _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast p.prop.pos) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  have hcE := constantCoeff_eulerProduct_ne_zero S _ (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ))
    hqlt
  have hcX : PowerSeries.constantCoeff xiSeries ≠ 0 := by
    rw [constantCoeff_xiSeries]; exact XiC_zero_ne
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : jensenRev 0 (mollifiedXiSeries S σ c) =
        C (PowerSeries.constantCoeff (mollifiedXiSeries S σ c)) := by
      rw [jensenRev_eq_sum]; simp
    have hc0 : PowerSeries.constantCoeff (mollifiedXiSeries S σ c) ≠ 0 := by
      rw [mollifiedXiSeries, map_mul, translatedMobiusProduct_eq_expSeries_mul, map_mul]
      refine mul_ne_zero hcX (mul_ne_zero ?_ hcE)
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, expSeries, PowerSeries.coeff_mk]
      simp
    rw [h0, IsRoot, eval_C] at hx
    exact absurd hx hc0
  set E := eulerProduct S (fun p => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ))
    fun p => Real.log ((p : ℕ) : ℝ)
  have hM : ∀ r, (jensenRev d (translatedMobiusProduct S σ c)).IsRoot r →
      r.im ≤ logFrequency S / 2 - c := fun r hr => by
    rw [translatedMobiusProduct_eq_expSeries_mul, jensenRev_expSeries_mul] at hr
    have hroot : (jensenRev d E).IsRoot (r + I * (c - logFrequency S / 2)) := by
      simpa [IsRoot, eval_comp] using hr
    have := (roots_jensenRev_eulerProduct (fun p : Nat.Primes => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ))
      (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ)) hd S hqlt
      (fun p _ => Real.log_pos (by exact_mod_cast p.prop.one_lt))).1 _ hroot
    simp only [add_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add] at this
    have hre : ((c : ℂ) - (logFrequency S : ℂ) / 2).re = c - logFrequency S / 2 := by simp
    rw [hre] at this
    linarith
  have hcM : PowerSeries.constantCoeff (translatedMobiusProduct S σ c) ≠ 0 := by
    rw [translatedMobiusProduct_eq_expSeries_mul, map_mul]
    refine mul_ne_zero ?_ hcE
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, expSeries, PowerSeries.coeff_mk]
    simp
  rw [mollifiedXiSeries, jensenRev_mul] at hx
  have := ffConv_root_im_le (jensenRev_ne_zero hcX) (natDegree_jensenRev hcX)
    (jensenRev_ne_zero hcM) (natDegree_jensenRev_le _ _) (a := 0)
    (fun r hr => (im_eq_zero_of_isRoot_jensenRev_xiSeries hRH d hr).le) hM hx
  linarith

/-- **Bounded imaginary parts decide RH.** For every finite set of primes, `σ > 0` and every
phase `c`: RH holds iff, for some `K` and infinitely many `d`, every root of the reversed Jensen
polynomial of `Ξ(w)·e^{icw}Π_{p∈S}(1 − p^{−σ−iw})` has imaginary part at most `K`. -/
theorem riemannHypothesis_iff_frequently_im_le_mollified (S : Finset Nat.Primes) {σ : ℝ}
    (hσ : 0 < σ) (c : ℝ) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d (mollifiedXiSeries S σ c)).IsRoot x → x.im ≤ K := by
  constructor
  · intro hRH
    exact ⟨logFrequency S / 2 - c, Frequently.of_forall fun d x hx =>
      im_le_of_isRoot_jensenRev_mollifiedXiSeries hRH S hσ c hx⟩
  · rintro ⟨K, h⟩
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
    have hst : ∃ᶠ d : ℕ in atTop, ∀ x, (jensenRev d (PowerSeries.mk f)).IsRoot x → x.im ≤ K := by
      simpa only [hmk] using h
    refine riemannHypothesis_iff_XiC_zeros_real.2 fun z hz => ?_
    have hlow : ∀ w, XiC w = 0 → 0 ≤ w.im := fun w hw =>
      im_nonneg_of_frequently_im_le hf hf0 hst (by rw [(hsum w).tsum_eq, hw, zero_mul])
    have h1 := hlow z hz
    have h2 := hlow (conj z) (by rw [XiC_conj, hz, map_zero])
    rw [conj_im] at h2
    linarith

/-- **The plain case.** RH holds iff, for some `K` and infinitely many `d`, the roots of the
reversed Jensen polynomial of `Ξ` have imaginary parts at most `K`. -/
theorem riemannHypothesis_iff_frequently_im_le :
    RiemannHypothesis ↔ ∃ K : ℝ, ∃ᶠ d : ℕ in atTop,
      ∀ x, (jensenRev d xiSeries).IsRoot x → x.im ≤ K := by
  have hexp : expSeries (0 : ℂ) = 1 := by
    ext k
    rw [expSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rcases k with _ | k <;> simp
  have hone : mollifiedXiSeries ∅ 1 0 = xiSeries := by
    rw [mollifiedXiSeries, translatedMobiusProduct, Finset.prod_empty, mul_one,
      Complex.ofReal_zero, mul_zero, hexp, mul_one]
  simpa [hone] using riemannHypothesis_iff_frequently_im_le_mollified ∅ one_pos 0

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.riemannHypothesis_iff_frequently_im_le_mollified
#print axioms FiniteFreeProbability.riemannHypothesis_iff_frequently_im_le
