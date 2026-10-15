import Mathlib.Analysis.Complex.Asymptotics
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.Asymptotics.Lemmas
import GaloisForLFunctions.RHTower.PrimeCurveTaylorControl
import GaloisForLFunctions.RHTower.PrimeCurveFiniteSmoothJets

/-!
# Actual-prime-curve vacuum rigidity

A C^k germ on real ell²(primes) agreeing with the genuine Euler logarithm
along the actual curve (p^(-sigma)) has derivative value 1 on every prime
unit vector with p <= 2^k. Its derivative norm is at least sqrt(pi(2^k)).
The explicit finite-smoothness models attain this lower bound. No single
C-infinity germ has the required actual-curve agreement.

The proof truncates the actual curve, uses radial Taylor control, expands
finite multilinear terms, and separates the resulting Dirichlet coefficients.
Unique prime factorization isolates degree one. The C^1 endpoint uses the
Frechet little-o remainder. No arbitrary finite-packet agreement is assumed.

This excludes smooth vacuum regularization as a Kummer-root producer.
It does not exclude singular source coordinates or prove a zero-free strip.
-/

open Filter Topology

namespace RHTower.PrimeCurveCoefficient


theorem coefficients_zero_of_scaled_limits
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hlim : ∀ n : ℕ, 1 ≤ n → n ≤ M →
      Tendsto (fun x : ℝ => (n : ℂ) ^ (x : ℂ) * LSeries a x)
        atTop (𝓝 0)) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => exact ha0
    | succ n =>
      have hprev : ∀ m ≤ n, a m = 0 := by
        intro m hm
        exact ih m (Nat.lt_succ_of_le hm) (le_trans hm (Nat.le_of_succ_le hn))
      have hvalue := LSeries.tendsto_cpow_mul_atTop hprev ha
      have hzero := hlim (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) hn
      simp only [Nat.cast_add, Nat.cast_one] at hzero
      exact tendsto_nhds_unique hvalue hzero

theorem coefficients_zero_of_scaled_limit
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hlim : Tendsto (fun x : ℝ => (M : ℂ) ^ (x : ℂ) * LSeries a x)
      atTop (𝓝 0)) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  apply coefficients_zero_of_scaled_limits ha0 ha
  intro n _ hn
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖(n : ℂ) ^ (x : ℂ) * LSeries a x‖ ≤
        ‖(M : ℂ) ^ (x : ℂ) * LSeries a x‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [norm_mul, Complex.norm_cpow_real, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hx) (norm_nonneg _)
  exact squeeze_zero_norm' hbound (by simpa using hlim.norm)

theorem coefficients_zero_of_littleO
    {a : ℕ → ℂ} {M : ℕ}
    (ha0 : a 0 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤)
    (hsmall : (fun x : ℝ => LSeries a x) =o[atTop]
      (fun x : ℝ => (M : ℂ) ^ (-(x : ℂ)))) :
    ∀ n : ℕ, n ≤ M → a n = 0 := by
  apply coefficients_zero_of_scaled_limit ha0 ha
  have h := hsmall.tendsto_div_nhds_zero
  simpa only [Complex.cpow_neg, div_inv_eq_mul, mul_comm] using h


end RHTower.PrimeCurveCoefficient

namespace RHTower.PrimeCurveCoefficient


variable {I : Type*} [Fintype I]

noncomputable def finiteDirichletCoeff (q : I → ℕ) (c : I → ℝ) (n : ℕ) : ℂ :=
  ∑ i, if n = q i then (c i : ℂ) else 0

theorem finiteDirichletCoeff_hasSum (q : I → ℕ) (c : I → ℝ)
    (hq : ∀ i, q i ≠ 0) (x : ℝ) :
    LSeriesHasSum (finiteDirichletCoeff q c) x
      ((∑ i, c i * (q i : ℝ) ^ (-x) : ℝ) : ℂ) := by
  classical
  have hi (i : I) : LSeriesHasSum (fun n : ℕ => if n = q i then (c i : ℂ) else 0)
      x ((c i : ℂ) / (q i : ℂ) ^ (x : ℂ)) := by
    have heq : LSeries.term (fun n : ℕ => if n = q i then (c i : ℂ) else 0) x =
        fun n => if n = q i then (c i : ℂ) / (q i : ℂ) ^ (x : ℂ) else 0 := by
      funext n
      by_cases hn : n = q i
      · subst n
        simp [LSeries.term_of_ne_zero (hq i)]
      · simp [LSeries.term_def, hn]
    change HasSum (LSeries.term _ _) _
    rw [heq]
    exact hasSum_ite_eq _ _
  have hs := LSeriesHasSum.sum (S := Finset.univ) (fun i _ => hi i)
  convert hs using 1
  · ext n
    simp only [finiteDirichletCoeff, Finset.sum_apply]
  · simp only [Complex.ofReal_sum, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.cpow_neg, div_eq_mul_inv]

theorem finiteDirichletCoeff_zero (q : I → ℕ) (c : I → ℝ)
    (hq : ∀ i, q i ≠ 0) : finiteDirichletCoeff q c 0 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (Ne.symm (hq i))

theorem finiteDirichletCoeff_zero_of_littleO (q : I → ℕ) (c : I → ℝ)
    (hq : ∀ i, q i ≠ 0) (M : ℕ)
    (hsmall : (fun x : ℝ => ∑ i, c i * (q i : ℝ) ^ (-x)) =o[atTop]
      (fun x : ℝ => (M : ℝ) ^ (-x))) :
    ∀ n ≤ M, ∑ i, (if q i = n then c i else 0) = 0 := by
  classical
  have ha : LSeries.abscissaOfAbsConv (finiteDirichletCoeff q c) < ⊤ := by
    exact lt_of_le_of_lt
      (finiteDirichletCoeff_hasSum q c hq 0).LSeriesSummable.abscissaOfAbsConv_le (by simp)
  have hcomplex := Complex.isLittleO_ofReal_right.mpr
    (Complex.isLittleO_ofReal_left.mpr hsmall)
  have hseries : (fun x : ℝ => LSeries (finiteDirichletCoeff q c) x) =o[atTop]
      (fun x : ℝ => (M : ℂ) ^ (-(x : ℂ))) := by
    simpa only [← (finiteDirichletCoeff_hasSum q c hq _).LSeries_eq,
      Complex.ofReal_cpow (Nat.cast_nonneg M), Complex.ofReal_neg, Complex.ofReal_natCast]
      using hcomplex
  intro n hn
  have h := coefficients_zero_of_littleO (finiteDirichletCoeff_zero q c hq) ha hseries n hn
  apply Complex.ofReal_injective
  simpa only [finiteDirichletCoeff, Complex.ofReal_sum, Complex.ofReal_zero,
    apply_ite Complex.ofReal, eq_comm] using h

end RHTower.PrimeCurveCoefficient


open Filter Set Topology

namespace RHTower.PrimeCurveModel

abbrev TruncatedPrime (N : ℕ) := ↥(finitePrimeSet N)


theorem primeTruncation_eq_sum (N : ℕ) (σ : ℝ) :
    primeTruncation N σ = ∑ p : TruncatedPrime N,
      (p.val.val : ℝ) ^ (-σ) • lp.single 2 p.val (1 : ℝ) := by
  classical
  have hs := Finset.sum_coe_sort (finitePrimeSet N)
    (fun p : Nat.Primes => (p.val : ℝ) ^ (-σ) • lp.single 2 p (1 : ℝ))
  calc
    primeTruncation N σ = ∑ p ∈ finitePrimeSet N,
        (p.val : ℝ) ^ (-σ) • lp.single 2 p (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [← lp.single_smul, smul_eq_mul, mul_one]
    _ = _ := hs.symm

noncomputable def primeWord (N j : ℕ) (a : Fin j → TruncatedPrime N) : ℕ :=
  ∏ i, (a i).val.val

theorem primeWord_pos (N j : ℕ) (a : Fin j → TruncatedPrime N) :
    0 < primeWord N j a := by
  apply Finset.prod_pos
  intro i _
  exact (a i).val.property.pos

theorem primeWord_ge_two_pow (N j : ℕ) (a : Fin j → TruncatedPrime N) :
    2 ^ j ≤ primeWord N j a := by
  have h := Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin j => 2)
    (g := fun i => (a i).val.val) (fun _ _ => Nat.zero_le _) (fun i _ => (a i).val.property.two_le)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, primeWord] using h

theorem primeWord_prime_degree {N j : ℕ} (a : Fin j → TruncatedPrime N)
    (h : Nat.Prime (primeWord N j a)) : j = 1 := by
  cases j with
  | zero => simp [primeWord, Nat.not_prime_one] at h
  | succ j =>
    cases j with
    | zero => rfl
    | succ j =>
      have hfac : primeWord N (j + 2) a =
          (a 0).val.val * primeWord N (j + 1) (fun i => a i.succ) := by
        exact Fin.prod_univ_succ (fun i => (a i).val.val)
      rw [hfac, Nat.prime_mul_iff] at h
      rcases h with h | h
      · have hb := primeWord_ge_two_pow N (j + 1) (fun i => a i.succ)
        have hp : 0 < 2 ^ j := by positivity
        rw [h.2, pow_succ] at hb
        omega
      · exact False.elim ((a 0).val.property.ne_one h.2)

theorem multilinear_primeTruncation_expansion (N j : ℕ) (σ : ℝ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => PrimeHilbert) ℝ) :
    A (fun _ => primeTruncation N σ) =
      ∑ a : Fin j → TruncatedPrime N,
        A (fun i => lp.single 2 (a i).val (1 : ℝ)) *
          (primeWord N j a : ℝ) ^ (-σ) := by
  classical
  simp only [primeTruncation_eq_sum, A.map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [A.map_smul_univ, smul_eq_mul]
  have hp := Real.finsetProd_rpow Finset.univ (fun i => ((a i).val.val : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (-σ)
  rw [hp, ← Nat.cast_prod]
  exact mul_comm _ _

theorem primeWord_coefficient_zero_of_degree_ne_one {N j p : ℕ}
    (hp : Nat.Prime p) (hj : j ≠ 1)
    (c : (Fin j → TruncatedPrime N) → ℝ) :
    (∑ a : Fin j → TruncatedPrime N, if primeWord N j a = p then c a else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  apply if_neg
  intro heq
  exact hj (primeWord_prime_degree a (heq.symm ▸ hp))

theorem primeWord_coefficient_degree_one {N : ℕ} (r : TruncatedPrime N)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => PrimeHilbert) ℝ) :
    (∑ a : Fin 1 → TruncatedPrime N, if primeWord N 1 a = r.val.val then
      A (fun i => lp.single 2 (a i).val (1 : ℝ)) else 0) =
        A (fun _ => lp.single 2 r.val (1 : ℝ)) := by
  classical
  have hd (a : Fin 1 → TruncatedPrime N) : a = fun _ => a 0 := by
    ext i
    rw [Fin.eq_zero i]
  calc
    _ = ∑ p : TruncatedPrime N, if p.val.val = r.val.val then
        A (fun _ => lp.single 2 p.val (1 : ℝ)) else 0 := by
      have he := (Equiv.funUnique (Fin 1) (TruncatedPrime N)).sum_comp
        (fun p => if p.val.val = r.val.val then A (fun _ => lp.single 2 p.val (1 : ℝ)) else 0)
      convert he using 1
      apply Finset.sum_congr rfl
      intro a _
      rw [hd a]
      simp [primeWord, Equiv.funUnique, Equiv.piUnique]
    _ = _ := by
      rw [Finset.sum_eq_single r]
      · simp
      · intro p _ hpr
        apply if_neg
        intro heq
        exact hpr (Subtype.ext (Subtype.ext heq))
      · simp

abbrev TaylorWord (N K : ℕ) := Σ j : Fin K, (Fin j.val → TruncatedPrime N)

noncomputable def taylorWordFrequency (N K : ℕ) (w : TaylorWord N K) : ℕ :=
  primeWord N w.1.val w.2

noncomputable def taylorWordCoeff (f : PrimeHilbert → ℝ) (N K : ℕ) (w : TaylorWord N K) : ℝ :=
  (w.1.val.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ w.1.val f 0)
    (fun i => lp.single 2 (w.2 i).val (1 : ℝ))


theorem taylorWord_expansion (f : PrimeHilbert → ℝ) (N K : ℕ) (σ : ℝ) :
    (∑ w : TaylorWord N K,
      taylorWordCoeff f N K w * (taylorWordFrequency N K w : ℝ) ^ (-σ)) =
        ∑ j ∈ Finset.range K, (j.factorial : ℝ)⁻¹ *
          (iteratedFDeriv ℝ j f 0) (fun _ => primeTruncation N σ) := by
  classical
  rw [Fintype.sum_sigma]
  simp only [taylorWordCoeff, taylorWordFrequency, mul_assoc, ← Finset.mul_sum,
    ← multilinear_primeTruncation_expansion]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ => (j.factorial : ℝ)⁻¹ *
    (iteratedFDeriv ℝ j f 0) (fun _ => primeTruncation N σ)) K

theorem taylorWord_prime_coefficient (f : PrimeHilbert → ℝ) {N K : ℕ}
    (hK : 1 < K) (p : Nat.Primes) (hpN : p.val ≤ N) :
    (∑ w : TaylorWord N K, if taylorWordFrequency N K w = p.val then
      taylorWordCoeff f N K w else 0) = fderiv ℝ f 0 (lp.single 2 p (1 : ℝ)) := by
  classical
  let r : TruncatedPrime N := ⟨p, (mem_finitePrimeSet N p).mpr hpN⟩
  have hcoeff (j : ℕ) :
      (∑ a : Fin j → TruncatedPrime N, if primeWord N j a = p.val then
        (j.factorial : ℝ)⁻¹ * (iteratedFDeriv ℝ j f 0)
          (fun i => lp.single 2 (a i).val (1 : ℝ)) else 0) =
        if j = 1 then fderiv ℝ f 0 (lp.single 2 p (1 : ℝ)) else 0 := by
    by_cases hj : j = 1
    · subst j
      simpa only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, if_true,
        iteratedFDeriv_one_apply] using
        (primeWord_coefficient_degree_one r (iteratedFDeriv ℝ 1 f 0))
    · rw [if_neg hj]
      exact primeWord_coefficient_zero_of_degree_ne_one p.property hj _
  rw [Fintype.sum_sigma]
  simp only [taylorWordFrequency, taylorWordCoeff, hcoeff]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j = 1 then fderiv ℝ f 0 (lp.single 2 p (1 : ℝ)) else 0) K]
  simp [Finset.sum_ite_eq', hK]

end RHTower.PrimeCurveModel

namespace RHTower.PrimeCurveModel

theorem prime_fderiv_zero_of_vanishing_curve {f : PrimeHilbert → ℝ}
    {U : Set PrimeHilbert} {k N : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hf : ContDiffOn ℝ (k + 1) f U) (hk : 1 ≤ k) (hN : 1 ≤ N)
    (hNk : N < 2 ^ (k + 1)) (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0)
    (p : Nat.Primes) (hpN : p.val ≤ N) :
    fderiv ℝ f 0 (lp.single 2 p (1 : ℝ)) = 0 := by
  have hs := truncated_radial_taylor_isLittleO hU h0 hf hN hNk hv
  have hw := hs.congr_left (fun σ => (taylorWord_expansion f N (k + 1) σ).symm)
  have hc := RHTower.PrimeCurveCoefficient.finiteDirichletCoeff_zero_of_littleO
    (taylorWordFrequency N (k + 1)) (taylorWordCoeff f N (k + 1))
    (fun w => (primeWord_pos N w.1.val w.2).ne') N hw p.val hpN
  rwa [taylorWord_prime_coefficient f (by omega) p hpN] at hc

theorem first_taylor_isLittleO_of_vanishing_curve {f : PrimeHilbert → ℝ}
    (hf : ContDiffAt ℝ 1 f 0)
    (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0) :
    (fun σ : ℝ => ∑ j ∈ Finset.range 2, (j.factorial : ℝ)⁻¹ *
      (iteratedFDeriv ℝ j f 0) (fun _ => primeTruncation 2 σ)) =o[atTop]
        (fun σ : ℝ => (2 : ℝ) ^ (-σ)) := by
  have he : (fun σ : ℝ => f (primeTruncation 2 σ) - f 0 -
      fderiv ℝ f 0 (primeTruncation 2 σ)) =o[atTop] primeTruncation 2 := by
    simpa only [Function.comp_def, sub_zero] using
      (hf.differentiableAt (by norm_num)).hasFDerivAt.isLittleO.comp_tendsto
        (primeTruncation_tendsto_zero 2)
  have hv' := vanishing_curve_truncation_isLittleO (N := 2) (by norm_num) hf hv
  have ht := hv'.sub (he.trans_isBigO (primeTruncation_isBigO 2))
  apply ht.congr_left
  intro σ
  simp [Finset.sum_range_succ]
  ring

theorem two_fderiv_zero_of_vanishing_curve {f : PrimeHilbert → ℝ}
    (hf : ContDiffAt ℝ 1 f 0)
    (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0) :
    fderiv ℝ f 0 (lp.single 2 ⟨2, Nat.prime_two⟩ (1 : ℝ)) = 0 := by
  have hs := first_taylor_isLittleO_of_vanishing_curve hf hv
  have hw := hs.congr_left (fun σ => (taylorWord_expansion f 2 2 σ).symm)
  have hc := RHTower.PrimeCurveCoefficient.finiteDirichletCoeff_zero_of_littleO
    (taylorWordFrequency 2 2) (taylorWordCoeff f 2 2)
    (fun w => (primeWord_pos 2 w.1.val w.2).ne') 2 hw 2 le_rfl
  rwa [taylorWord_prime_coefficient f (by norm_num) ⟨2, Nat.prime_two⟩ le_rfl] at hc

end RHTower.PrimeCurveModel

namespace RHTower.PrimeCurveModel

theorem prime_fderiv_zero_of_vanishing_curve_sharp {f : PrimeHilbert → ℝ}
    {U : Set PrimeHilbert} {k : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hf : ContDiffOn ℝ k f U) (hk : 1 ≤ k)
    (hv : ∀ᶠ σ : ℝ in atTop, f (farPrimeCurve σ) = 0)
    (p : Nat.Primes) (hp : p.val ≤ 2 ^ k) :
    fderiv ℝ f 0 (lp.single 2 p (1 : ℝ)) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      have hp2 : p = ⟨2, Nat.prime_two⟩ := by
        apply Subtype.ext
        change p.val = 2
        exact Nat.le_antisymm (by simpa using hp) p.property.two_le
      subst p
      exact two_fderiv_zero_of_vanishing_curve (hf.contDiffAt (hU.mem_nhds h0)) hv
    | succ k =>
      have hnot : ¬ Nat.Prime (2 ^ (k + 2)) := by
        rw [pow_succ]
        apply Nat.not_prime_mul
        · have hb : 0 < 2 ^ k := by positivity
          rw [pow_succ]
          omega
        · norm_num
      have hlt : p.val < 2 ^ (k + 2) := by
        have hneq : p.val ≠ 2 ^ (k + 2) := fun h => hnot (h ▸ p.property)
        exact lt_of_le_of_ne hp hneq
      exact prime_fderiv_zero_of_vanishing_curve (k := k + 1) (N := p.val)
        hU h0 hf (by omega) p.property.pos hlt hv p le_rfl

theorem prime_fderiv_eq_one_of_euler_curve {G : PrimeHilbert → ℝ}
    {U : Set PrimeHilbert} {k : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hG : ContDiffOn ℝ k G U) (hk : 1 ≤ k)
    (hcurve : ∀ᶠ σ : ℝ in atTop, G (farPrimeCurve σ) = Real.log ‖riemannZeta (σ : ℂ)‖)
    (p : Nat.Primes) (hp : p.val ≤ 2 ^ k) :
    fderiv ℝ G 0 (lp.single 2 p (1 : ℝ)) = 1 := by
  let V : Set PrimeHilbert := U ∩ Metric.ball 0 modelRadius
  have hV : IsOpen V := hU.inter Metric.isOpen_ball
  have hV0 : (0 : PrimeHilbert) ∈ V := ⟨h0, Metric.mem_ball_self modelRadius_pos⟩
  have hF : ContDiffOn ℝ k (fun x => G x - finiteSmoothModel k x) V :=
    (hG.mono inter_subset_left).sub ((contDiffOn_finiteSmoothModel k).mono inter_subset_right)
  have hv : ∀ᶠ σ : ℝ in atTop, G (farPrimeCurve σ) - finiteSmoothModel k (farPrimeCurve σ) = 0 := by
    filter_upwards [hcurve, eventually_gt_atTop (1 : ℝ)] with σ hc hσ
    rw [hc, farPrimeCurve_eq (by linarith : 1 / 2 < σ),
      finiteSmoothModel_eq_log_norm_zeta k hσ, sub_self]
  have hz := prime_fderiv_zero_of_vanishing_curve_sharp hV hV0 hF hk hv p hp
  have hd : DifferentiableAt ℝ G 0 := (hG.contDiffAt (hU.mem_nhds h0)).differentiableAt
    (by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hk)))
  have hdsub := hd.hasFDerivAt.sub (hasFDerivAt_finiteSmoothModel hk)
  change (fderiv ℝ (G - finiteSmoothModel k) 0) (lp.single 2 p (1 : ℝ)) = 0 at hz
  rw [hdsub.fderiv, sub_apply, cutoffReader_single, if_pos hp] at hz
  linarith

theorem norm_fderiv_lowerBound_of_euler_curve {G : PrimeHilbert → ℝ}
    {U : Set PrimeHilbert} {k : ℕ} (hU : IsOpen U) (h0 : (0 : PrimeHilbert) ∈ U)
    (hG : ContDiffOn ℝ k G U) (hk : 1 ≤ k)
    (hcurve : ∀ᶠ σ : ℝ in atTop, G (farPrimeCurve σ) = Real.log ‖riemannZeta (σ : ℂ)‖) :
    Real.sqrt (((Finset.range (2 ^ k + 1)).filter Nat.Prime).card : ℝ) ≤ ‖fderiv ℝ G 0‖ :=
  norm_lowerBound_of_prime_coordinates (2 ^ k) (fderiv ℝ G 0)
    (prime_fderiv_eq_one_of_euler_curve hU h0 hG hk hcurve)

open scoped ContDiff in
theorem no_smooth_euler_curve_germ :
    ¬ ∃ G : PrimeHilbert → ℝ, ∃ U : Set PrimeHilbert,
      IsOpen U ∧ (0 : PrimeHilbert) ∈ U ∧ ContDiffOn ℝ ∞ G U ∧
        (∀ᶠ σ : ℝ in atTop, G (farPrimeCurve σ) = Real.log ‖riemannZeta (σ : ℂ)‖) := by
  rintro ⟨G, U, hU, h0, hG, hcurve⟩
  apply no_bounded_all_prime_reader
  refine ⟨fderiv ℝ G 0, fun p => ?_⟩
  have hGk : ContDiffOn ℝ (p.val + 1 : ℕ) G U :=
    hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (p.val + 1))
  apply prime_fderiv_eq_one_of_euler_curve hU h0 hGk (by omega) hcurve p
  have h : p.val + 1 < 2 ^ (p.val + 1) := Nat.lt_two_pow_self
  omega

end RHTower.PrimeCurveModel
