import GaloisForLFunctions.ArithmeticResonanceTheory.TheTwoRealizationsOfThePrimes
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation

/-!
# Oscillation fails on additive and free realizations

Oscillatory cancellation (Dolgopyat) pushes resonances of a dynamical zeta function off a strip by
contracting the twisted periodic sums `Z_n(σ + it)` uniformly in `|t| ≥ T`, exponentially in `n`
relative to the untwisted sums `Z_n(σ)` (`RelativeDolgopyat`). This needs the phases
`e^{−it ℓ(γ)}` of the periodic orbits never to align for large `t`.

**Returns.** For finitely many lengths, Dirichlet's simultaneous approximation brings all phases
`e^{−itℓ_i}` within any `δ` of `1` at arbitrarily large times (`exists_ge_forall_norm_phase_sub_one_lt`).
With a summable tail the same holds for any absolutely convergent exponential sum
(`exists_ge_norm_tsum_twist_lt`).

* **Finite additive realizations** (locally constant roofs on finitely many edges): a closed walk
  of `n` edges has phase within `nδ` of `1` once every edge phase is within `δ`
  (`norm_sum_words_twist_le`), so no relative Dolgopyat bound holds
  (`not_relativeDolgopyat_of_finite_edges`).
* **The free realization**: the twisted eigenvalue `P(σ + it)` returns to `P(σ)`
  (`exists_ge_primeZetaR_sub_lt_norm_twist`), so its periodic sums `P(σ + it)ⁿ` admit no relative
  Dolgopyat bound (`not_relativeDolgopyat_free`).
* **The commutative realization**: twisting multiplies each eigenvalue by a phase and changes no
  modulus (`norm_commEigen_twist`); there is nothing to contract.

Oscillation therefore needs a non-additive roof — which is what the conformal threshold
constrains.
-/

open Filter Topology Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticResonanceTheory

/-- The phase `e^{−i t ℓ}` of a periodic orbit of length `ℓ` at twist `t`. -/
noncomputable def phase (t ℓ : ℝ) : ℂ := Complex.exp (((-(t * ℓ) : ℝ) : ℂ) * Complex.I)

theorem norm_phase (t ℓ : ℝ) : ‖phase t ℓ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

theorem phase_zero (ℓ : ℝ) : phase 0 ℓ = 1 := by simp [phase]

theorem phase_add (t ℓ ℓ' : ℝ) : phase t (ℓ + ℓ') = phase t ℓ * phase t ℓ' := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## Simultaneous returns of finitely many phases -/

/-- **Phases return.** For a finite set of lengths and any `T`, `δ > 0`, some `t ≥ T` puts every
phase `e^{−itℓ_i}` within `δ` of `1`. -/
theorem exists_ge_forall_norm_phase_sub_one_lt {ι : Type*} (S : Finset ι) (ℓ : ι → ℝ) (T : ℝ)
    {δ : ℝ} (hδ : 0 < δ) : ∃ t, T ≤ t ∧ ∀ i ∈ S, ‖phase t (ℓ i) - 1‖ < δ := by
  classical
  have hπ := Real.pi_pos
  obtain ⟨Q, hQ⟩ := exists_nat_gt ((2 * Real.pi ^ 2 + 2 * Real.pi) / δ)
  have hQpos : (0 : ℝ) < Q := lt_of_le_of_lt (by positivity) hQ
  have hQ1 : 1 ≤ Q := by exact_mod_cast hQpos
  set U : ℝ := max T 1 with hU
  obtain ⟨k, hk1, -, hk⟩ := exists_dirichlet_phase (fun i : S => ℓ i) U Q hQ1
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  refine ⟨k * U, ?_, fun i hi => ?_⟩
  · calc T ≤ U := le_max_left _ _
      _ = 1 * U := (one_mul U).symm
      _ ≤ k * U := mul_le_mul_of_nonneg_right hk1' (le_trans zero_le_one (le_max_right _ _))
  · obtain ⟨hcos, hsin⟩ := hk ⟨i, hi⟩
    set θ : ℝ := ℓ i * (k * U) with hθ
    have hre : (phase (k * U) (ℓ i) - 1).re = Real.cos θ - 1 := by
      rw [Complex.sub_re, phase, Complex.exp_ofReal_mul_I_re, Complex.one_re, Real.cos_neg,
        hθ, mul_comm]
    have him : (phase (k * U) (ℓ i) - 1).im = -Real.sin θ := by
      rw [Complex.sub_im, phase, Complex.exp_ofReal_mul_I_im, Complex.one_im, Real.sin_neg,
        hθ, mul_comm, sub_zero]
    have hcos1 := Real.cos_le_one θ
    have hQ1r : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
    have hQsq : 2 * Real.pi ^ 2 / (Q : ℝ) ^ 2 ≤ 2 * Real.pi ^ 2 / Q := by
      apply div_le_div_of_nonneg_left (by positivity) hQpos
      nlinarith
    calc ‖phase (k * U) (ℓ i) - 1‖ ≤ |Real.cos θ - 1| + |-Real.sin θ| := by
          rw [← hre, ← him]; exact Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 2 * Real.pi ^ 2 / Q + 2 * Real.pi / Q := by
          rw [abs_neg, abs_of_nonpos (by linarith)]
          linarith
      _ = (2 * Real.pi ^ 2 + 2 * Real.pi) / Q := by ring
      _ < δ := by
          rw [div_lt_iff₀ hQpos]
          rw [div_lt_iff₀ hδ] at hQ
          linarith

/-- **Absolutely convergent exponential sums return.** For nonnegative summable weights `a` and any
lengths, `Σ a_i (e^{−itℓ_i} − 1)` is smaller than any `ε > 0` at arbitrarily large `t`. -/
theorem exists_ge_norm_tsum_twist_lt {ι : Type*} {a : ι → ℝ} (ha0 : ∀ i, 0 ≤ a i)
    (ha : Summable a) (ℓ : ι → ℝ) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ t, T ≤ t ∧ ‖∑' i, (a i : ℂ) * (phase t (ℓ i) - 1)‖ < ε := by
  classical
  -- a finite set carrying all but `ε/4` of the mass
  obtain ⟨S, hS⟩ := (ha.hasSum.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))).exists
  have hSle : ∑ i ∈ S, a i ≤ ∑' i, a i :=
    Summable.sum_le_tsum S (fun i _ => ha0 i) ha
  have htail : ∑' i, a i - ∑ i ∈ S, a i < ε / 4 := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)] at hS
    exact hS
  set A : ℝ := ∑' i, a i with hA
  have hA0 : 0 ≤ A := tsum_nonneg ha0
  obtain ⟨t, hT, ht⟩ :=
    exists_ge_forall_norm_phase_sub_one_lt S ℓ T (by positivity : 0 < ε / (4 * (A + 1)))
  refine ⟨t, hT, ?_⟩
  set g : ι → ℂ := fun i => (a i : ℂ) * (phase t (ℓ i) - 1) with hg
  have hgn : ∀ i, ‖g i‖ ≤ 2 * a i := fun i => by
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 i)]
    have : ‖phase t (ℓ i) - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_phase, norm_one]; norm_num)
    nlinarith [ha0 i]
  have hgs : Summable g := Summable.of_norm_bounded (ha.mul_left 2) hgn
  rw [← hgs.sum_add_tsum_compl (s := S)]
  -- the finite part
  have hfin : ‖∑ i ∈ S, g i‖ ≤ ε / 4 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ S, ‖g i‖ ≤ ∑ i ∈ S, a i * (ε / (4 * (A + 1))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha0 i)]
          exact mul_le_mul_of_nonneg_left (ht i hi).le (ha0 i)
      _ = (∑ i ∈ S, a i) * (ε / (4 * (A + 1))) := by rw [Finset.sum_mul]
      _ ≤ A * (ε / (4 * (A + 1))) := by gcongr
      _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- the tail
  have hcompl : ∑' i : ↥((S : Set ι)ᶜ), a i = A - ∑ i ∈ S, a i := by
    rw [hA, ← ha.sum_add_tsum_compl (s := S)]; ring
  have htl : ‖∑' i : ↥((S : Set ι)ᶜ), g i‖ ≤ 2 * (A - ∑ i ∈ S, a i) := by
    have hsub : Summable fun i : ↥((S : Set ι)ᶜ) => a i := ha.subtype _
    refine (norm_tsum_le_tsum_norm (hgs.subtype _).norm).trans ?_
    rw [← hcompl, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun i => hgn i) (hgs.subtype _).norm (hsub.mul_left 2)
  calc ‖∑ i ∈ S, g i + ∑' i : ↥((S : Set ι)ᶜ), g i‖
      ≤ ‖∑ i ∈ S, g i‖ + ‖∑' i : ↥((S : Set ι)ᶜ), g i‖ := norm_add_le _ _
    _ ≤ ε / 4 + 2 * (A - ∑ i ∈ S, a i) := add_le_add hfin htl
    _ < ε := by linarith

/-! ## The relative Dolgopyat bound -/

/-- A **relative Dolgopyat bound** for periodic sums `Z n t` (twist `t`) with untwisted sizes `z n`:
the twisted sums are uniformly in `t ≥ T` exponentially smaller than the untwisted ones. -/
def RelativeDolgopyat (Z : ℕ → ℝ → ℂ) (z : ℕ → ℝ) : Prop :=
  ∃ C ρ T : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ n t, T ≤ t → ‖Z n t‖ ≤ C * ρ ^ n * z n

/-- `‖Π zᵢ − 1‖ ≤ Σ ‖zᵢ − 1‖` for unimodular factors. -/
theorem norm_prod_phase_sub_one_le {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ‖∏ i, z i - 1‖ ≤ ∑ i, ‖z i - 1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hrest := ih (fun i => z i.succ) fun i => hz _
    have hprod : ‖∏ i : Fin n, z i.succ‖ = 1 := by rw [norm_prod]; simp [hz]
    calc ‖z 0 * ∏ i : Fin n, z i.succ - 1‖
        = ‖(z 0 - 1) * ∏ i : Fin n, z i.succ + (∏ i : Fin n, z i.succ - 1)‖ := by ring_nf
      _ ≤ ‖z 0 - 1‖ * 1 + ‖∏ i : Fin n, z i.succ - 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hprod]
      _ ≤ ‖z 0 - 1‖ + ∑ i : Fin n, ‖z i.succ - 1‖ := by rw [mul_one]; linarith

/-- The twisted sum over a set `W` of words of `n` edges with edge lengths `r`:
`Σ_{w ∈ W} a_w e^{−it Σ_i r(wᵢ)}`. -/
noncomputable def wordSum {E : Type*} {n : ℕ} (W : Finset (Fin n → E)) (a : (Fin n → E) → ℝ)
    (r : E → ℝ) (t : ℝ) : ℂ :=
  ∑ w ∈ W, (a w : ℂ) * phase t (∑ i, r (w i))

/-- The phase of a word is the product of its edge phases. -/
theorem phase_sum {E : Type*} (t : ℝ) (r : E → ℝ) :
    ∀ {n : ℕ} (w : Fin n → E), phase t (∑ i, r (w i)) = ∏ i, phase t (r (w i))
  | 0, _ => by simp [phase]
  | n + 1, w => by
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, phase_add, phase_sum t r (fun i : Fin n => w i.succ)]

/-- If every edge phase is within `δ` of `1`, a word sum is within `nδ Σ a` of its untwisted value. -/
theorem norm_sum_words_twist_le {E : Type*} {n : ℕ} (W : Finset (Fin n → E))
    {a : (Fin n → E) → ℝ} (ha : ∀ w, 0 ≤ a w) (r : E → ℝ) {t δ : ℝ}
    (hδ : ∀ e, ‖phase t (r e) - 1‖ ≤ δ) :
    ‖wordSum W a r t - wordSum W a r 0‖ ≤ n * δ * ∑ w ∈ W, a w := by
  have hphase : ∀ w : Fin n → E, phase t (∑ i, r (w i)) = ∏ i, phase t (r (w i)) :=
    fun w => phase_sum t r w
  rw [wordSum, wordSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [phase_zero, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha w),
    hphase]
  have h := norm_prod_phase_sub_one_le (fun i => phase t (r (w i))) fun i => norm_phase _ _
  have hsum : ∑ i, ‖phase t (r (w i)) - 1‖ ≤ n * δ := by
    calc ∑ i, ‖phase t (r (w i)) - 1‖ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hδ _
      _ = n * δ := by simp
  calc a w * ‖∏ i, phase t (r (w i)) - 1‖ ≤ a w * (n * δ) :=
        mul_le_mul_of_nonneg_left (h.trans hsum) (ha w)
    _ = n * δ * a w := by ring

/-- **No oscillation on finite additive realizations.** For finitely many edges with lengths `r`,
word sets `W n` (e.g. the closed walks of length `n`) with nonnegative weights and positive
untwisted mass, the twisted sums `wordSum (W n) (a n) r t` admit no relative Dolgopyat bound. -/
theorem not_relativeDolgopyat_of_finite_edges {E : Type*} [Fintype E]
    (W : ∀ n, Finset (Fin n → E)) (a : ∀ n, (Fin n → E) → ℝ) (ha : ∀ n w, 0 ≤ a n w)
    (r : E → ℝ) (hpos : ∀ n, 0 < ∑ w ∈ W n, a n w) :
    ¬ RelativeDolgopyat (fun n t => wordSum (W n) (a n) r t) (fun n => ∑ w ∈ W n, a n w) := by
  rintro ⟨C, ρ, T, hρ0, hρ, hbound⟩
  -- a length `n` at which the bound is below one half
  have ht0 : Tendsto (fun n : ℕ => C * ρ ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ).const_mul C
  have hev : ∀ᶠ n : ℕ in atTop, C * ρ ^ n < 1 / 2 := ht0.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n, hn⟩ := hev.exists
  set M := ∑ w ∈ W n, a n w with hM
  have hM0 : 0 < M := hpos n
  -- all edge phases within `1/(2n+2)` of `1` at some `t ≥ T`
  obtain ⟨t, hT, ht⟩ := exists_ge_forall_norm_phase_sub_one_lt (Finset.univ : Finset E) r T
    (by positivity : (0 : ℝ) < 1 / (2 * n + 2))
  have hclose := norm_sum_words_twist_le (W n) (ha n) r (fun e => (ht e (Finset.mem_univ e)).le)
  have hzero : wordSum (W n) (a n) r 0 = (M : ℂ) := by
    simp [wordSum, phase_zero, hM]
  rw [hzero] at hclose
  have hnδ : (n : ℝ) * (1 / (2 * n + 2)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hlow : M / 2 ≤ ‖wordSum (W n) (a n) r t‖ := by
    have h1 : ‖(M : ℂ)‖ ≤ ‖wordSum (W n) (a n) r t‖ + ‖wordSum (W n) (a n) r t - M‖ := by
      have := norm_sub_le (wordSum (W n) (a n) r t) (wordSum (W n) (a n) r t - M)
      rw [sub_sub_cancel] at this
      exact this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0] at h1
    nlinarith
  have hup := hbound n t hT
  have hlt : C * ρ ^ n * M < M / 2 := by nlinarith
  linarith

/-! ## The free and the commutative realization -/

/-- The twisted eigenvalue of the free realization, `P(σ + it) = Σ_p p^{−σ} e^{−it log p}`. -/
noncomputable def twistedPrimeZeta (σ t : ℝ) : ℂ :=
  ∑' p : Nat.Primes, ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * phase t (Real.log (p : ℕ))

theorem norm_twistedPrimeZeta_le {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    ‖twistedPrimeZeta σ t‖ ≤ primeZetaR σ := by
  have hs := summable_prime_rpow_neg hσ
  refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hs
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  · refine tsum_congr fun p => ?_
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- **The free eigenvalue returns**: `sup_{t ≥ T} |P(σ + it)| = P(σ)` for every `T`. -/
theorem exists_ge_primeZetaR_sub_lt_norm_twist {σ : ℝ} (hσ : 1 < σ) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∃ t, T ≤ t ∧ primeZetaR σ - ε < ‖twistedPrimeZeta σ t‖ := by
  have hs := summable_prime_rpow_neg hσ
  obtain ⟨t, hT, ht⟩ := exists_ge_norm_tsum_twist_lt
    (fun p : Nat.Primes => Real.rpow_nonneg (by positivity) (-σ)) hs
    (fun p => Real.log (p : ℕ)) T hε
  refine ⟨t, hT, ?_⟩
  have hsc : Summable fun p : Nat.Primes => ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) :=
    (Complex.ofRealCLM.summable hs)
  have hst : Summable fun p : Nat.Primes =>
      ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) * phase t (Real.log (p : ℕ)) := by
    refine Summable.of_norm_bounded hs fun p => ?_
    rw [norm_mul, norm_phase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hdiff : ∑' p : Nat.Primes, ((((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
      (phase t (Real.log (p : ℕ)) - 1) = twistedPrimeZeta σ t - (primeZetaR σ : ℂ) := by
    rw [twistedPrimeZeta, primeZetaR, Complex.ofReal_tsum, ← hst.tsum_sub hsc]
    exact tsum_congr fun p => by ring
  rw [hdiff] at ht
  have h := norm_sub_norm_le (primeZetaR σ : ℂ) (twistedPrimeZeta σ t)
  have hP0 : 0 ≤ primeZetaR σ := tsum_nonneg fun p => Real.rpow_nonneg (by positivity) _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hP0, norm_sub_rev] at h
  linarith

/-- **No oscillation on the free realization.** Its periodic sums `P(σ + it)ⁿ` admit no relative
Dolgopyat bound. -/
theorem not_relativeDolgopyat_free {σ : ℝ} (hσ : 1 < σ) :
    ¬ RelativeDolgopyat (fun n t => twistedPrimeZeta σ t ^ n) (fun n => primeZetaR σ ^ n) := by
  rintro ⟨C, ρ, T, hρ0, hρ, hbound⟩
  have hP : 0 < primeZetaR σ := by
    have := primeZetaR_strictAntiOn (show σ ∈ Set.Ioi 1 from hσ)
      (show σ + 1 ∈ Set.Ioi 1 by simp only [Set.mem_Ioi]; linarith) (by linarith)
    exact lt_of_le_of_lt (tsum_nonneg fun p => Real.rpow_nonneg (by positivity) _) this
  -- an intermediate rate `ρ < ρ' < 1` and a length `n` with `C (ρ/ρ')ⁿ < 1`
  set ρ' : ℝ := (1 + ρ) / 2 with hρ'
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := by rw [hρ']; linarith
  have hq : ρ / ρ' < 1 := (div_lt_one hρ'0).mpr (by rw [hρ']; linarith)
  have ht0 : Tendsto (fun n : ℕ => C * (ρ / ρ') ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hρ0 hρ'0.le) hq).const_mul C
  obtain ⟨n, hn⟩ := (ht0.eventually (gt_mem_nhds one_pos)).exists
  obtain ⟨t, hT, ht⟩ := exists_ge_primeZetaR_sub_lt_norm_twist hσ T
    (by nlinarith : 0 < (1 - ρ') * primeZetaR σ)
  have hlow : ρ' * primeZetaR σ < ‖twistedPrimeZeta σ t‖ := by linarith
  have hup := hbound n t hT
  rw [norm_pow] at hup
  -- `(ρ' P)ⁿ ≤ ‖P(σ+it)‖ⁿ ≤ C ρⁿ Pⁿ = C (ρ/ρ')ⁿ (ρ' P)ⁿ < (ρ' P)ⁿ`
  have h1 : (ρ' * primeZetaR σ) ^ n ≤ ‖twistedPrimeZeta σ t‖ ^ n :=
    pow_le_pow_left₀ (by positivity) hlow.le n
  have hkey : C * ρ ^ n * primeZetaR σ ^ n = C * (ρ / ρ') ^ n * (ρ' * primeZetaR σ) ^ n := by
    rw [div_pow, mul_pow]; field_simp
  have h2 : C * (ρ / ρ') ^ n * (ρ' * primeZetaR σ) ^ n < (ρ' * primeZetaR σ) ^ n :=
    mul_lt_of_lt_one_left (by positivity) hn
  linarith

/-- **Twisting the commutative realization is unitary on each eigenvalue.** -/
theorem norm_commEigen_twist (σ t : ℝ) (p : Nat.Primes) :
    ‖commEigen (σ + t * Complex.I) p‖ = ‖commEigen σ p‖ := by
  rw [norm_commEigen, norm_commEigen]
  simp

end GaloisForLFunctions.ArithmeticResonanceTheory
