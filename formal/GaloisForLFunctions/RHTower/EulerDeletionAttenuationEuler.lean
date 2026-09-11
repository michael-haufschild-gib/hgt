import GaloisForLFunctions.RHTower.EulerDeletionPrimeAttenuation
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleZeroLanding
import Mathlib.Tactic

/-!
# The Euler quotient of one attenuated prime, and the fate of the pole at one

For a prime `p` and `0 <= c <= 1` the attenuated coefficients are `b(n) = c^(v_p(n))`.  In the
absolute half-plane their ordinary Dirichlet series is exactly

```text
F(s) = zeta(s) * (1 - p^(-s)) / (1 - c * p^(-s)),
```

proved here from the literal finite dilation identity rather than from an Euler product.  For
`0 <= c <= 1` and `Re s > 0` the quotient is continuous and nowhere zero, so multiplying by it
preserves the zeta zero divisor exactly.

The literal deletion coefficients `(1 - ell [p divides n]) b(n)` have far-right value
`(1 - ell * c * p^(-s)) * F(s)`.  At `s = 1` the residue is `(1 - c)` times the local factor: the
pole of zeta survives for every `c < 1` when the original multiplier `ell = p` is retained, and it
is cancelled exactly under the repaired normalization `ell * c = p`, where the far-right value has
the finite limit `log p` times the local factor.

This is the analytic-continuation explanation attached to `EulerDeletionPrimeAttenuation`.  It
establishes no relation forced by a zeta zero and no RH implication.
-/

open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionAttenuationEuler
open RHTower.DeletionPrimeAttenuation
noncomputable section

/-- Literal one-indexed Dirichlet prefix of the attenuated coefficients. -/
def attenuatedPrefix (p : ℕ) (c : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, (weight p c n : ℂ) * ((n : ℝ) : ℂ) ^ (-s)

/-- The Euler quotient of one attenuated prime. -/
def localFactor (p : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  (1 - (((p : ℝ) : ℂ) ^ (-s))) / (1 - (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)))

theorem prime_cast_ne_zero {p : ℕ} (hp : 2 ≤ p) : ((p : ℝ) : ℂ) ≠ 0 := by
  have hpos : (0:ℝ) < (p:ℝ) := by
    have : (0:ℕ) < p := by omega
    exact_mod_cast this
  simpa using Complex.ofReal_ne_zero.mpr hpos.ne'

theorem norm_cpow_prime (p : ℕ) (hp : 2 ≤ p) (s : ℂ) :
    ‖(((p : ℝ) : ℂ) ^ (-s))‖ = (p : ℝ) ^ (-s.re) := by
  have hpos : (0:ℝ) < (p:ℝ) := by
    have : (0:ℕ) < p := by omega
    exact_mod_cast this
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp

theorem norm_cpow_prime_lt_one {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖(((p : ℝ) : ℂ) ^ (-s))‖ < 1 := by
  rw [norm_cpow_prime p hp]
  have h1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem one_sub_mul_ne_zero {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) ≠ 0 := by
  intro h
  have h1 : (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_one] at h2
  nlinarith [norm_cpow_prime_lt_one hp hs, norm_nonneg ((((p : ℝ) : ℂ) ^ (-s)))]

theorem one_sub_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (((p : ℝ) : ℂ) ^ (-s)) ≠ 0 := by
  intro h
  have h1 : (((p : ℝ) : ℂ) ^ (-s)) = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_one] at h2
  have h3 := norm_cpow_prime_lt_one hp hs
  linarith

theorem localFactor_ne_zero {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : localFactor p c s ≠ 0 :=
  div_ne_zero (one_sub_ne_zero hp hs) (one_sub_mul_ne_zero hp hc hc1 hs)

theorem cpow_prime_mul (p m : ℕ) (s : ℂ) :
    (((p * m : ℕ) : ℝ) : ℂ) ^ (-s) =
      (((p : ℕ) : ℝ) : ℂ) ^ (-s) * (((m : ℕ) : ℝ) : ℂ) ^ (-s) := by
  have h1 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  simpa only [Nat.cast_mul, Complex.ofReal_mul] using
    (Complex.mul_cpow_ofReal_nonneg h1 h2 (-s))

theorem cpow_neg_one {p : ℕ} (_hp : 2 ≤ p) : (((p : ℝ) : ℂ) ^ (-(1:ℂ))) = ((p : ℂ))⁻¹ := by
  rw [Complex.cpow_neg, Complex.cpow_one]
  simp

theorem cpow_neg_eq_exp {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    (((p : ℝ) : ℂ)) ^ (-s) = Complex.exp (Complex.log ((p : ℝ) : ℂ) * (-s)) :=
  Complex.cpow_def_of_ne_zero (prime_cast_ne_zero hp) (-s)

theorem hasDerivAt_cpow_neg {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    HasDerivAt (fun z : ℂ => (((p : ℝ) : ℂ)) ^ (-z))
      (-(Complex.log ((p : ℝ) : ℂ) * ((((p : ℝ) : ℂ)) ^ (-s)))) s := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log ((p : ℝ) : ℂ) * (-z))
      (Complex.log ((p : ℝ) : ℂ) * (-1)) s := ((hasDerivAt_id s).neg).const_mul _
  have h2 := h1.cexp
  have heq : (fun z : ℂ => Complex.exp (Complex.log ((p : ℝ) : ℂ) * (-z)))
      = fun z : ℂ => (((p : ℝ) : ℂ)) ^ (-z) := by
    funext z
    exact (cpow_neg_eq_exp hp z).symm
  have hval : Complex.exp (Complex.log ((p : ℝ) : ℂ) * (-s)) *
        (Complex.log ((p : ℝ) : ℂ) * (-1))
      = -(Complex.log ((p : ℝ) : ℂ) * ((((p : ℝ) : ℂ)) ^ (-s))) := by
    rw [← cpow_neg_eq_exp hp s]
    ring
  rw [heq, hval] at h2
  exact h2

theorem continuousAt_cpow_neg {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    ContinuousAt (fun z : ℂ => (((p : ℝ) : ℂ) ^ (-z))) s :=
  (hasDerivAt_cpow_neg hp s).continuousAt

theorem differentiableAt_cpow_neg {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => (((p : ℝ) : ℂ) ^ (-z))) s :=
  (hasDerivAt_cpow_neg hp s).differentiableAt

theorem continuousAt_localFactor {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : ContinuousAt (localFactor p c) s := by
  unfold localFactor
  exact ((continuousAt_const.sub (continuousAt_cpow_neg hp s)).div
    (continuousAt_const.sub (continuousAt_const.mul (continuousAt_cpow_neg hp s)))
    (one_sub_mul_ne_zero hp hc hc1 hs))

/-- The Euler quotient is holomorphic on the positive half-plane. -/
theorem differentiableAt_localFactor {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (localFactor p c) s := by
  unfold localFactor
  exact ((differentiableAt_const 1).sub (differentiableAt_cpow_neg hp s)).div
    ((differentiableAt_const 1).sub ((differentiableAt_const _).mul
      (differentiableAt_cpow_neg hp s)))
    (one_sub_mul_ne_zero hp hc hc1 hs)

/-- The attenuated mass carried by the multiples of the attenuated prime. -/
theorem sum_dvd_attenuated {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) (s : ℂ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n),
        (weight p c n : ℂ) * ((n : ℝ) : ℂ) ^ (-s)
      = (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) * attenuatedPrefix p c (N / p) s := by
  classical
  rw [sum_Icc_filter_dvd_reindex p N hp.pos, attenuatedPrefix, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [weight_prime_mul hp, cpow_prime_mul]
  push_cast
  ring

/-- Exact finite dilation identity for the attenuated prefix. -/
theorem attenuatedPrefix_dilation {p : ℕ} (hp : p.Prime) (c : ℝ) (N : ℕ) (s : ℂ) :
    attenuatedPrefix p c N s =
      zetaDirichletPrefix N s - (((p : ℝ) : ℂ) ^ (-s)) * zetaDirichletPrefix (N / p) s +
        (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) * attenuatedPrefix p c (N / p) s := by
  classical
  have hp0 : 0 < p := hp.pos
  have hdvd := sum_dvd_attenuated hp c N s
  have hdvdz : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), ((n : ℝ) : ℂ) ^ (-s)
      = (((p : ℝ) : ℂ) ^ (-s)) * zetaDirichletPrefix (N / p) s := by
    rw [sum_Icc_filter_dvd_reindex p N hp0, zetaDirichletPrefix, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => cpow_prime_mul p m s)
  have hnot : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n),
        (weight p c n : ℂ) * ((n : ℝ) : ℂ) ^ (-s)
      = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n), ((n : ℝ) : ℂ) ^ (-s) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [weight_of_not_dvd (Finset.mem_filter.mp hn).2]
    push_cast
    ring
  have hz := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)
    (fun n => ((n : ℝ) : ℂ) ^ (-s))
  have hw := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => p ∣ n)
    (fun n => (weight p c n : ℂ) * ((n : ℝ) : ℂ) ^ (-s))
  have hkey : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ p ∣ n), ((n : ℝ) : ℂ) ^ (-s)
      = zetaDirichletPrefix N s - (((p : ℝ) : ℂ) ^ (-s)) * zetaDirichletPrefix (N / p) s := by
    rw [← hdvdz, zetaDirichletPrefix]
    linear_combination hz
  rw [attenuatedPrefix, ← hw, hdvd, hnot, hkey]
  ring

theorem attenuated_summable {p : ℕ} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (weight p c (n+1) : ℂ) * ((((n+1 : ℕ)) : ℝ) : ℂ) ^ (-s)) := by
  have hcomp : Summable (fun n : ℕ => (((n+1 : ℕ)) : ℝ) ^ (-s.re)) := by
    have h := (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith)).comp_injective
      Nat.succ_injective
    exact h.congr (fun n => by simp [Function.comp_def])
  refine Summable.of_norm_bounded hcomp (fun n => ?_)
  have hpos : (0:ℝ) < (((n+1 : ℕ)) : ℝ) := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hw : |weight p c (n+1)| ≤ 1 := by
    rw [abs_of_nonneg (weight_nonneg p hc _)]
    exact weight_le_one p hc hc1 _
  have hr : (0:ℝ) ≤ (((n+1 : ℕ)) : ℝ) ^ (-s).re := by positivity
  calc |weight p c (n+1)| * (((n+1 : ℕ)) : ℝ) ^ (-s).re
      ≤ 1 * (((n+1 : ℕ)) : ℝ) ^ (-s).re := mul_le_mul_of_nonneg_right hw hr
    _ = (((n+1 : ℕ)) : ℝ) ^ (-s.re) := by simp

/-- The attenuated Dirichlet series in the absolute half-plane. -/
def attenuatedSum (p : ℕ) (c : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (weight p c (n+1) : ℂ) * ((((n+1 : ℕ)) : ℝ) : ℂ) ^ (-s)

theorem attenuatedPrefix_tendsto {p : ℕ} {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => attenuatedPrefix p c N s) atTop (𝓝 (attenuatedSum p c s)) := by
  have h := (attenuated_summable (p := p) (c := c) hc hc1 hs).hasSum.tendsto_sum_nat
  refine h.congr (fun N => ?_)
  rw [attenuatedPrefix, sum_Icc_eq_sum_range_succ]

/-- The exact Euler-quotient identity for the attenuated Dirichlet series. -/
theorem attenuatedSum_mul_denom {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    attenuatedSum p c s * (1 - (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s))) =
      riemannZeta s * (1 - (((p : ℝ) : ℂ) ^ (-s))) := by
  have hp0 : 0 < p := hp.pos
  have hA := attenuatedPrefix_tendsto (p := p) (c := c) hc hc1 hs
  have hAdiv : Tendsto (fun N => attenuatedPrefix p c (N / p) s) atTop
      (𝓝 (attenuatedSum p c s)) := hA.comp (Nat.tendsto_div_const_atTop hp0.ne')
  have hZ := tendsto_zetaDirichletPrefix hs
  have hZdiv : Tendsto (fun N => zetaDirichletPrefix (N / p) s) atTop (𝓝 (riemannZeta s)) :=
    hZ.comp (Nat.tendsto_div_const_atTop hp0.ne')
  have hlim : Tendsto (fun N => attenuatedPrefix p c N s) atTop
      (𝓝 (riemannZeta s - (((p:ℝ):ℂ)^(-s)) * riemannZeta s
        + (c:ℂ) * (((p:ℝ):ℂ)^(-s)) * attenuatedSum p c s)) := by
    have hcomb := ((hZ.sub ((tendsto_const_nhds
        (x := (((p:ℝ):ℂ)^(-s)))).mul hZdiv)).add
      ((tendsto_const_nhds (x := (c:ℂ) * (((p:ℝ):ℂ)^(-s)))).mul hAdiv))
    refine hcomb.congr (fun N => ?_)
    exact (attenuatedPrefix_dilation hp c N s).symm
  have huniq := tendsto_nhds_unique hA hlim
  linear_combination huniq

/-- The attenuated series is zeta times an explicit Euler quotient. -/
theorem attenuatedSum_eq {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    attenuatedSum p c s = riemannZeta s * localFactor p c s := by
  have hne := one_sub_mul_ne_zero hp.two_le hc hc1 (by linarith : 0 < s.re)
  rw [localFactor, ← mul_div_assoc, eq_div_iff hne]
  exact attenuatedSum_mul_denom hp hc hc1 hs

/-- Literal one-indexed deletion prefix at an attenuated prime. -/
def deletionPrefixC (p : ℕ) (c ell : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((((1 : ℝ) - ell * (if p ∣ n then (1:ℝ) else 0)) * weight p c n : ℝ) : ℂ) *
      ((n : ℝ) : ℂ) ^ (-s)

theorem deletionPrefixC_eq {p : ℕ} (hp : p.Prime) (c ell : ℝ) (N : ℕ) (s : ℂ) :
    deletionPrefixC p c ell N s =
      attenuatedPrefix p c N s -
        (ell : ℂ) * ((c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) * attenuatedPrefix p c (N / p) s) := by
  classical
  rw [← sum_dvd_attenuated hp c N s, deletionPrefixC, attenuatedPrefix, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hd : p ∣ n
  · simp only [hd, if_true]
    push_cast
    ring
  · simp only [hd, if_false]
    push_cast
    ring

/-- Far-right value of the literal deletion series at an attenuated prime. -/
def deletionFarRight (p : ℕ) (c ell : ℝ) (s : ℂ) : ℂ :=
  (1 - (ell : ℂ) * (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s))) * (riemannZeta s * localFactor p c s)

/-- The literal deletion series of an attenuated prime has the stated far-right value. -/
theorem deletionPrefixC_tendsto {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (ell : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun N => deletionPrefixC p c ell N s) atTop (𝓝 (deletionFarRight p c ell s)) := by
  have hp0 : 0 < p := hp.pos
  have hA := attenuatedPrefix_tendsto (p := p) (c := c) hc hc1 hs
  have hAdiv : Tendsto (fun N => attenuatedPrefix p c (N / p) s) atTop
      (𝓝 (attenuatedSum p c s)) := hA.comp (Nat.tendsto_div_const_atTop hp0.ne')
  have hlim := hA.sub ((tendsto_const_nhds (x := (ell : ℂ))).mul
    ((tendsto_const_nhds (x := (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)))).mul hAdiv))
  have heq : deletionFarRight p c ell s
      = attenuatedSum p c s -
        (ell : ℂ) * ((c : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) * attenuatedSum p c s) := by
    rw [deletionFarRight, attenuatedSum_eq hp hc hc1 hs]
    ring
  rw [heq]
  exact hlim.congr (fun N => (deletionPrefixC_eq hp c ell N s).symm)

/-- A zero-free holomorphic Euler quotient preserves the zeta zero divisor. -/
theorem zeta_mul_localFactor_eq_zero_iff {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 0 ≤ c)
    (hc1 : c ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    riemannZeta s * localFactor p c s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' (localFactor_ne_zero hp hc hc1 hs)
  · intro h
    rw [h, zero_mul]

/-- The literal deletion factor vanishes at one exactly under the repaired normalization. -/
theorem repaired_factor_at_one {p : ℕ} (hp : 2 ≤ p) :
    (1 : ℂ) - (p : ℂ) * (((p : ℝ) : ℂ) ^ (-(1:ℂ))) = 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by simpa using prime_cast_ne_zero hp
  rw [cpow_neg_one hp, mul_inv_cancel₀ hp0, sub_self]

theorem hasDerivAt_repaired_factor {p : ℕ} (hp : 2 ≤ p) :
    HasDerivAt (fun s : ℂ => 1 - (p : ℂ) * (((p : ℝ) : ℂ) ^ (-s))) ((Real.log p : ℂ)) 1 := by
  have h := ((hasDerivAt_cpow_neg hp 1).const_mul ((p : ℂ))).const_sub (1:ℂ)
  have hp0 : (p : ℂ) ≠ 0 := by simpa using prime_cast_ne_zero hp
  have hlog : Complex.log ((p : ℝ) : ℂ) = (Real.log p : ℂ) := by
    rw [← Complex.ofReal_log (by positivity)]
  have hval : -((p : ℂ) * -(Complex.log ((p : ℝ) : ℂ) * ((((p : ℝ) : ℂ)) ^ (-(1:ℂ)))))
      = (Real.log p : ℂ) := by
    rw [cpow_neg_one hp, hlog]
    field_simp
  rw [hval] at h
  exact h

/-- The pole at one survives the literal deletion of a strictly attenuated prime. -/
theorem deletionFarRight_residue {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun s => (s - 1) * deletionFarRight p c (p : ℝ) s) (𝓝[≠] (1:ℂ))
      (𝓝 ((1 - (c : ℂ)) * localFactor p c 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hcont : ContinuousAt
      (fun s : ℂ => (1 - (((p:ℝ)) : ℂ) * (c : ℂ) * (((p : ℝ) : ℂ) ^ (-s))) * localFactor p c s)
      1 :=
    ((continuousAt_const.sub (continuousAt_const.mul (continuousAt_cpow_neg hp2 1))).mul
      (continuousAt_localFactor hp2 hc hc1.le (by norm_num)))
  have hp0 : (p : ℂ) ≠ 0 := by simpa using prime_cast_ne_zero hp2
  have hval : (1 - (((p:ℝ)) : ℂ) * (c : ℂ) * (((p : ℝ) : ℂ) ^ (-(1:ℂ)))) * localFactor p c 1
      = (1 - (c : ℂ)) * localFactor p c 1 := by
    rw [cpow_neg_one hp2]
    congr 2
    push_cast
    field_simp
  have hlim := (hcont.continuousWithinAt.tendsto).mul riemannZeta_residue_one
  rw [hval, mul_one] at hlim
  refine hlim.congr (fun s => ?_)
  rw [deletionFarRight]
  push_cast
  ring

theorem deletionFarRight_residue_ne_zero {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 ≤ c)
    (hc1 : c < 1) : (1 - (c : ℂ)) * localFactor p c 1 ≠ 0 := by
  refine mul_ne_zero ?_ (localFactor_ne_zero hp.two_le hc hc1.le (by norm_num))
  intro h
  have h1 : (c : ℂ) = 1 := by linear_combination -h
  have h2 : c = 1 := by exact_mod_cast h1
  linarith

/-- The repaired normalization cancels the pole at one. -/
theorem repairedFarRight_tendsto {p : ℕ} (hp : p.Prime) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    {ell : ℝ} (hcancel : ell * c = p) :
    Tendsto (fun s => deletionFarRight p c ell s) (𝓝[≠] (1:ℂ))
      (𝓝 ((Real.log p : ℂ) * localFactor p c 1)) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hell : (ell : ℂ) * (c : ℂ) = (p : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hcancel
    push_cast at h
    exact h
  have hquot : Tendsto (fun s : ℂ => (1 - (p:ℂ) * (((p : ℝ) : ℂ) ^ (-s))) / (s - 1))
      (𝓝[≠] (1:ℂ)) (𝓝 ((Real.log p : ℂ))) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_repaired_factor hp2)
    refine h.congr (fun z => ?_)
    simp only [slope_def_field]
    rw [repaired_factor_at_one hp2, sub_zero]
  have hlim := (hquot.mul riemannZeta_residue_one).mul
    ((continuousAt_localFactor hp2 hc.le hc1 (by norm_num)).continuousWithinAt.tendsto)
  rw [mul_one] at hlim
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [deletionFarRight, hell]
  field_simp

end
end RHTower.DeletionAttenuationEuler
