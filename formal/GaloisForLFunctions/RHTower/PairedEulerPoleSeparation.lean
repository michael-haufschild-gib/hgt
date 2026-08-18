import GaloisForLFunctions.RHTower.EulerUnitTangent
import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope

/-!
# The private boundary pole of a paired Euler tangent

The FE-paired Euler unit tangent `w_p = T_p(s) − T_p(1−s)` has a **private** double pole at the
boundary point `b_p = 2πi / log p`: no other prime's tangent, and no reflected tangent, is singular
there.  Reading the leading coefficient at `b_p` therefore separates the primes, and the transverse
coordinate `2s − 1` — which is regular at every `b_p` — cannot be a finite combination of the
tangents.

Main results:

* `primeExp_tangentPole_self` — `p^{-b_p} = 1`;
* `primeExp_tangentPole_ne_one` — `q^{-b_p} ≠ 1` for a distinct prime `q` (unique factorization:
  `log q / log p ∈ ℤ` would force `q = p^m`);
* `one_sub_primeExp_reflect_ne_zero` — the reflected side never degenerates, since `Re b_p = 0`
  puts `1 − b_p` on the line `Re = 1`;
* `tendsto_sq_mul_tangentE` — the boundary residue `(s − b_p)² T_p(s) → 1/log p`;
* `not_finite_combination_eq_transverse` — **the theorem**: no finite `ℂ`-combination of the paired
  tangents equals `2s − 1` on the open critical strip.

The closure half of the card (the same coordinate *is* in the closed span after deleting any finite
prime set) is the separate stage-3 card `fe-odd-reduced-quotient-blindness`; together they give the
nonzero class `[2s − 1]` in `closure(span)/span`.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower.PairedEulerPole

open RHTower RHTower.Sieve

/-- The prime exponential `p^{-s}` written through `exp`. -/
def primeExp (p : ℕ) (s : ℂ) : ℂ := Complex.exp (-s * (Real.log p : ℂ))

theorem complexLog_natCast (p : ℕ) :
    Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.ofReal_log (by positivity)]

theorem cpow_neg_eq_primeExp {p : ℕ} (hp : 0 < p) (s : ℂ) :
    (p : ℂ) ^ (-s) = primeExp p s := by
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [Complex.cpow_def_of_ne_zero hpne, primeExp, complexLog_natCast p]
  ring_nf

theorem norm_primeExp {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖primeExp p s‖ = Real.exp (-s.re * Real.log p) := by
  rw [primeExp, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- The boundary pole of the `p`-tangent. -/
def tangentPole (p : ℕ) : ℂ := 2 * Real.pi * I / (Real.log p : ℂ)

theorem tangentPole_eq {p : ℕ} (hp : 2 ≤ p) :
    tangentPole p = ((2 * Real.pi / Real.log p : ℝ) : ℂ) * I := by
  have hL : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (log_pos_of_two_le hp).ne'
  rw [tangentPole]
  push_cast
  field_simp

theorem tangentPole_re {p : ℕ} (hp : 2 ≤ p) : (tangentPole p).re = 0 := by
  rw [tangentPole_eq hp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, sub_self]

theorem tangentPole_mul_log {p : ℕ} (hp : 2 ≤ p) :
    tangentPole p * (Real.log p : ℂ) = 2 * Real.pi * I := by
  have hL : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (log_pos_of_two_le hp).ne'
  rw [tangentPole, div_mul_cancel₀ _ hL]

/-- At its own boundary pole the prime exponential is one. -/
theorem primeExp_tangentPole_self {p : ℕ} (hp : 2 ≤ p) : primeExp p (tangentPole p) = 1 := by
  rw [primeExp, neg_mul, tangentPole_mul_log hp]
  rw [show -(2 * (Real.pi : ℂ) * I) = (-1 : ℤ) * (2 * (Real.pi : ℂ) * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-1)

/-- Distinct primes do not share a boundary pole. -/
theorem primeExp_tangentPole_ne_one {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : q ≠ p) :
    primeExp q (tangentPole p) ≠ 1 := by
  intro hcon
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  have hLp : (0 : ℝ) < Real.log p := log_pos_of_two_le hp2
  have hLq : (0 : ℝ) < Real.log q := log_pos_of_two_le hq2
  rw [primeExp] at hcon
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hcon
  have hLpC : ((Real.log p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hLp.ne'
  have hshape : -tangentPole p * (Real.log q : ℂ)
      = (((-(2 * Real.pi)) * (Real.log q / Real.log p) : ℝ) : ℂ) * I := by
    rw [tangentPole_eq hp2]
    push_cast
    field_simp
  have hrhs : (n : ℂ) * (2 * (Real.pi : ℂ) * I)
      = ((((n : ℝ)) * (2 * Real.pi) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hshape, hrhs] at hn
  have hcast : (((-(2 * Real.pi)) * (Real.log q / Real.log p) : ℝ) : ℂ)
      = ((((n : ℝ)) * (2 * Real.pi) : ℝ) : ℂ) := mul_right_cancel₀ Complex.I_ne_zero hn
  have him : (-(2 * Real.pi)) * (Real.log q / Real.log p) = ((n : ℝ)) * (2 * Real.pi) :=
    Complex.ofReal_inj.mp hcast
  have h2pi : (-(2 * Real.pi)) ≠ 0 := by
    have hpi := Real.pi_pos
    intro hc
    nlinarith
  have h2 : (-(2 * Real.pi)) * (Real.log q / Real.log p)
      = (-(2 * Real.pi)) * (-((n : ℝ))) := by
    rw [him]
    ring
  have hratio : Real.log q / Real.log p = -((n : ℝ)) := mul_left_cancel₀ h2pi h2
  set k : ℤ := -n with hk
  have hkR : ((k : ℤ) : ℝ) = Real.log q / Real.log p := by
    rw [hk, hratio]
    push_cast
    ring
  have hkpos : 0 < k := by
    have hposR : (0 : ℝ) < ((k : ℤ) : ℝ) := by
      rw [hkR]
      positivity
    exact_mod_cast hposR
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, (Int.toNat_of_nonneg hkpos.le).symm⟩
  have hlog : Real.log q = (m : ℝ) * Real.log p := by
    have hkm : ((m : ℕ) : ℝ) = Real.log q / Real.log p := by
      rw [← hkR, hm]
      push_cast
      ring
    field_simp at hkm
    linarith
  have hqp : (q : ℝ) = (p : ℝ) ^ m := by
    have h1 : Real.log q = Real.log ((p : ℝ) ^ m) := by
      rw [Real.log_pow, hlog]
    have hqpos : (0 : ℝ) < q := by positivity
    have hppos : (0 : ℝ) < (p : ℝ) ^ m := by positivity
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hqpos) (Set.mem_Ioi.mpr hppos) h1
  have hqpNat : q = p ^ m := by exact_mod_cast hqp
  have hdvd : p ∣ q := by
    rw [hqpNat]
    refine dvd_pow_self p ?_
    intro hm0
    rw [hm0, pow_zero] at hqpNat
    omega
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd).symm

/-! ## The tangent in exponential form -/

/-- The Euler unit tangent written through `exp`. -/
def tangentE (p : ℕ) (s : ℂ) : ℂ :=
  (Real.log p : ℂ) * primeExp p s / (1 - primeExp p s) ^ 2

theorem primeEulerUnitTangent_eq_tangentE {p : ℕ} (hp : 0 < p) (s : ℂ) :
    primeEulerUnitTangent p s = tangentE p s := by
  rw [primeEulerUnitTangent, tangentE, cpow_neg_eq_primeExp hp]

theorem primeEulerUnitFETangent_eq {p : ℕ} (hp : 0 < p) (s : ℂ) :
    primeEulerUnitFETangent p s = tangentE p s - tangentE p (1 - s) := by
  rw [primeEulerUnitFETangent, primeEulerUnitTangent_eq_tangentE hp,
    primeEulerUnitTangent_eq_tangentE hp]

theorem continuous_primeExp (p : ℕ) : Continuous (primeExp p) := by
  unfold primeExp
  fun_prop

/-- On the reflected side of the boundary pole the denominator never vanishes. -/
theorem one_sub_primeExp_reflect_ne_zero {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    1 - primeExp q (1 - tangentPole p) ≠ 0 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hLq : (0 : ℝ) < Real.log q := log_pos_of_two_le hq
  have hre : (1 - tangentPole p).re = 1 := by
    rw [Complex.sub_re, Complex.one_re, tangentPole_re hp, sub_zero]
  have hnorm : ‖primeExp q (1 - tangentPole p)‖ = Real.exp (-Real.log q) := by
    rw [norm_primeExp hq0, hre]
    norm_num
  intro hcon
  have h1 : primeExp q (1 - tangentPole p) = 1 := by
    have := sub_eq_zero.mp hcon
    exact this.symm
  rw [h1, norm_one] at hnorm
  have hlt : Real.exp (-Real.log q) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  rw [← hnorm] at hlt
  exact lt_irrefl 1 hlt

/-- Away from its own boundary pole the tangent is continuous. -/
theorem continuousAt_tangentE {q : ℕ} {s₀ : ℂ} (h : 1 - primeExp q s₀ ≠ 0) :
    ContinuousAt (tangentE q) s₀ := by
  unfold tangentE
  refine ContinuousAt.div ?_ ?_ (pow_ne_zero 2 h)
  · exact continuousAt_const.mul (continuous_primeExp q).continuousAt
  · exact (continuousAt_const.sub (continuous_primeExp q).continuousAt).pow 2

theorem hasDerivAt_one_sub_primeExp {p : ℕ} (hp : 2 ≤ p) :
    HasDerivAt (fun s => 1 - primeExp p s) (Real.log p : ℂ) (tangentPole p) := by
  have hlin : HasDerivAt (fun s : ℂ => -s * (Real.log p : ℂ)) (-(Real.log p : ℂ))
      (tangentPole p) := by
    have h := ((hasDerivAt_id (tangentPole p)).neg).mul_const ((Real.log p : ℝ) : ℂ)
    simpa using h
  have hexp : HasDerivAt (fun s : ℂ => Complex.exp (-s * (Real.log p : ℂ)))
      (Complex.exp (-(tangentPole p) * (Real.log p : ℂ)) * (-(Real.log p : ℂ)))
      (tangentPole p) := hlin.cexp
  have hval : Complex.exp (-(tangentPole p) * (Real.log p : ℂ)) = 1 := by
    have := primeExp_tangentPole_self hp
    rw [primeExp] at this
    exact this
  rw [hval, one_mul] at hexp
  have := hexp.const_sub 1
  simpa [primeExp] using this

/-- **The boundary residue.**  At its own boundary point the `p`-tangent has a double pole with
leading coefficient `1/log p`. -/
theorem tendsto_sq_mul_tangentE {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun s => (s - tangentPole p) ^ 2 * tangentE p s) (𝓝[≠] (tangentPole p))
      (𝓝 ((Real.log p : ℂ)⁻¹)) := by
  have hL : ((Real.log p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (log_pos_of_two_le hp).ne'
  set b := tangentPole p with hb
  set f : ℂ → ℂ := fun s => 1 - primeExp p s with hf
  have hfb : f b = 0 := by
    rw [hf]
    simp only
    rw [primeExp_tangentPole_self hp, sub_self]
  have hslope : Tendsto (slope f b) (𝓝[≠] b) (𝓝 ((Real.log p : ℝ) : ℂ)) :=
    hasDerivAt_iff_tendsto_slope.mp (hasDerivAt_one_sub_primeExp hp)
  have hsl : ∀ s : ℂ, s ≠ b → slope f b s = f s / (s - b) := by
    intro s hs
    rw [slope_def_field, hfb, sub_zero]
  have hkey : ∀ s : ℂ, s ≠ b →
      (s - b) ^ 2 * tangentE p s
        = (Real.log p : ℂ) * primeExp p s / (slope f b s) ^ 2 := by
    intro s hs
    have hsb : s - b ≠ 0 := sub_ne_zero.mpr hs
    have hfs : f s = slope f b s * (s - b) := by
      rw [hsl s hs, div_mul_cancel₀ _ hsb]
    have hden : (1 - primeExp p s) = slope f b s * (s - b) := hfs
    by_cases hz : slope f b s = 0
    · rw [hz] at hden
      rw [tangentE, hden]
      simp [hz]
    · rw [tangentE, hden]
      field_simp
  have hE : Tendsto (fun s : ℂ => primeExp p s) (𝓝[≠] b) (𝓝 1) := by
    have hc := ((continuous_primeExp p).tendsto b).mono_left
      (nhdsWithin_le_nhds (s := {b}ᶜ) (a := b))
    rw [primeExp_tangentPole_self hp] at hc
    exact hc
  have hlim : Tendsto (fun s => (Real.log p : ℂ) * primeExp p s / (slope f b s) ^ 2)
      (𝓝[≠] b) (𝓝 ((Real.log p : ℂ)⁻¹)) := by
    have hnum : Tendsto (fun s => (Real.log p : ℂ) * primeExp p s) (𝓝[≠] b)
        (𝓝 ((Real.log p : ℂ) * 1)) := tendsto_const_nhds.mul hE
    have hden : Tendsto (fun s => (slope f b s) ^ 2) (𝓝[≠] b) (𝓝 (((Real.log p : ℝ) : ℂ) ^ 2)) :=
      hslope.pow 2
    have hval : ((Real.log p : ℂ) * 1) / (((Real.log p : ℝ) : ℂ) ^ 2)
        = ((Real.log p : ℂ))⁻¹ := by
      field_simp
    rw [← hval]
    exact hnum.div hden (pow_ne_zero 2 hL)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hkey s hs).symm

/-! ## Finite exact nonrepresentability -/

/-- The interior approach sequence to a boundary pole. -/
def approach (p : ℕ) (n : ℕ) : ℂ := tangentPole p + ((1 / ((n : ℝ) + 2) : ℝ) : ℂ)

theorem approach_re {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : (approach p n).re = 1 / ((n : ℝ) + 2) := by
  rw [approach, Complex.add_re, tangentPole_re hp, Complex.ofReal_re, zero_add]

theorem approach_mem_strip {p : ℕ} (hp : 2 ≤ p) (n : ℕ) :
    0 < (approach p n).re ∧ (approach p n).re < 1 := by
  rw [approach_re hp]
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

theorem approach_ne {p : ℕ} (hp : 2 ≤ p) (n : ℕ) : approach p n ≠ tangentPole p := by
  intro hcon
  have hre := congrArg Complex.re hcon
  rw [approach_re hp, tangentPole_re hp] at hre
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  rw [hre] at hpos
  exact lt_irrefl 0 hpos

theorem tendsto_approach (p : ℕ) : Tendsto (approach p) atTop (𝓝 (tangentPole p)) := by
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simp only [one_div]
    exact hden.inv_tendsto_atTop
  have h3 : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 2) : ℝ)) : ℂ)) atTop (𝓝 0) := by
    have hc := (Complex.continuous_ofReal.tendsto 0).comp h2
    rw [Complex.ofReal_zero] at hc
    exact hc
  have hconst : Tendsto (fun _ : ℕ => tangentPole p) atTop (𝓝 (tangentPole p)) :=
    tendsto_const_nhds
  have h4 := hconst.add h3
  rw [add_zero] at h4
  exact h4

theorem tendsto_approach_punctured {p : ℕ} (hp : 2 ≤ p) :
    Tendsto (approach p) atTop (𝓝[≠] (tangentPole p)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_approach p)
    (Filter.Eventually.of_forall (fun n => approach_ne hp n))

set_option maxHeartbeats 1000000 in
/-- **Finite exact nonrepresentability.**  The transverse coordinate `2s − 1` is not a finite
`ℂ`-linear combination of the functional-equation-paired Euler tangents on the open critical
strip. -/
theorem not_finite_combination_eq_transverse
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (c : ℕ → ℂ)
    (h : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      ∑ p ∈ P, c p * primeEulerUnitFETangent p s = 2 * s - 1) :
    False := by
  classical
  have hzero : ∀ p ∈ P, c p = 0 := by
    intro p hpP
    have hp : Nat.Prime p := hP p hpP
    have hp2 : 2 ≤ p := hp.two_le
    have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp2
    set b := tangentPole p with hb
    set S := approach p with hS
    have hSpunct : Tendsto S atTop (𝓝[≠] b) := tendsto_approach_punctured hp2
    have hsq : Tendsto (fun n => (S n - b) ^ 2) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ => b) atTop (𝓝 b) := tendsto_const_nhds
      have h1 : Tendsto (fun n => S n - b) atTop (𝓝 (b - b)) :=
        (tendsto_approach p).sub hconst
      rw [sub_self] at h1
      have h2 := h1.pow 2
      rw [zero_pow (by norm_num : (2:ℕ) ≠ 0)] at h2
      exact h2
    -- the term of the distinguished prime
    have hmain : Tendsto (fun n => (S n - b) ^ 2 * tangentE p (S n)) atTop
        (𝓝 ((Real.log p : ℂ)⁻¹)) := (tendsto_sq_mul_tangentE hp2).comp hSpunct
    -- every other term vanishes in the limit
    have hother : ∀ q ∈ P, q ≠ p →
        Tendsto (fun n => (S n - b) ^ 2 * tangentE q (S n)) atTop (𝓝 0) := by
      intro q hqP hqp
      have hq : Nat.Prime q := hP q hqP
      have hcont : ContinuousAt (tangentE q) b :=
        continuousAt_tangentE (by
          intro hcon
          exact primeExp_tangentPole_ne_one hp hq hqp (sub_eq_zero.mp hcon).symm)
      have hTq : Tendsto (fun n => tangentE q (S n)) atTop (𝓝 (tangentE q b)) :=
        hcont.tendsto.comp (tendsto_approach p)
      have := hsq.mul hTq
      simpa using this
    have hrefl : ∀ q ∈ P,
        Tendsto (fun n => (S n - b) ^ 2 * tangentE q (1 - S n)) atTop (𝓝 0) := by
      intro q hqP
      have hq : Nat.Prime q := hP q hqP
      have hcont : ContinuousAt (fun s => tangentE q (1 - s)) b := by
        have h1 : ContinuousAt (fun s : ℂ => 1 - s) b :=
          continuousAt_const.sub continuousAt_id
        have h2 : ContinuousAt (tangentE q) (1 - b) :=
          continuousAt_tangentE (one_sub_primeExp_reflect_ne_zero hp2 hq.two_le)
        exact ContinuousAt.comp (x := b) h2 h1
      have hTq : Tendsto (fun n => tangentE q (1 - S n)) atTop (𝓝 (tangentE q (1 - b))) :=
        hcont.tendsto.comp (tendsto_approach p)
      have := hsq.mul hTq
      simpa using this
    -- the whole combination
    have hterm : ∀ q ∈ P,
        Tendsto (fun n => c q * ((S n - b) ^ 2 * primeEulerUnitFETangent q (S n))) atTop
          (𝓝 (if q = p then c p * (Real.log p : ℂ)⁻¹ else 0)) := by
      intro q hqP
      have hq : Nat.Prime q := hP q hqP
      have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq.two_le
      have hrw : ∀ n, (S n - b) ^ 2 * primeEulerUnitFETangent q (S n)
          = (S n - b) ^ 2 * tangentE q (S n) - (S n - b) ^ 2 * tangentE q (1 - S n) := by
        intro n
        rw [primeEulerUnitFETangent_eq hq0]
        ring
      by_cases hqp : q = p
      · subst hqp
        rw [if_pos rfl]
        have hlim := (hmain.sub (hrefl q hqP))
        rw [sub_zero] at hlim
        have hcq : Tendsto (fun _ : ℕ => c q) atTop (𝓝 (c q)) := tendsto_const_nhds
        have hmul := hcq.mul hlim
        refine hmul.congr (fun n => ?_)
        rw [hrw n]
      · rw [if_neg hqp]
        have hlim := ((hother q hqP hqp).sub (hrefl q hqP))
        rw [sub_zero] at hlim
        have hcq : Tendsto (fun _ : ℕ => c q) atTop (𝓝 (c q)) := tendsto_const_nhds
        have hmul := hcq.mul hlim
        rw [mul_zero] at hmul
        refine hmul.congr (fun n => ?_)
        rw [hrw n]
    have hsum : Tendsto (fun n => ∑ q ∈ P, c q * ((S n - b) ^ 2
        * primeEulerUnitFETangent q (S n))) atTop
        (𝓝 (∑ q ∈ P, if q = p then c p * (Real.log p : ℂ)⁻¹ else 0)) :=
      tendsto_finsetSum _ hterm
    have hval : (∑ q ∈ P, if q = p then c p * (Real.log p : ℂ)⁻¹ else 0)
        = c p * (Real.log p : ℂ)⁻¹ := by
      rw [Finset.sum_eq_single p]
      · rw [if_pos rfl]
      · intro q _ hqp
        rw [if_neg hqp]
      · intro hcon
        exact absurd hpP hcon
    rw [hval] at hsum
    -- but the same sequence is the transverse coordinate
    have hrhs : Tendsto (fun n => ∑ q ∈ P, c q * ((S n - b) ^ 2
        * primeEulerUnitFETangent q (S n))) atTop (𝓝 0) := by
      have hid : ∀ n, (∑ q ∈ P, c q * ((S n - b) ^ 2 * primeEulerUnitFETangent q (S n)))
          = (S n - b) ^ 2 * (2 * S n - 1) := by
        intro n
        obtain ⟨h1, h2⟩ := approach_mem_strip hp2 n
        rw [← h (S n) h1 h2, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
      have hlim : Tendsto (fun n => (S n - b) ^ 2 * (2 * S n - 1)) atTop
          (𝓝 (0 * (2 * b - 1))) := by
        refine hsq.mul ?_
        have hc1 : Tendsto (fun _ : ℕ => (2 : ℂ)) atTop (𝓝 2) := tendsto_const_nhds
        have hc2 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
        exact (hc1.mul (tendsto_approach p)).sub hc2
      rw [zero_mul] at hlim
      exact hlim.congr (fun n => (hid n).symm)
    have huniq := tendsto_nhds_unique hsum hrhs
    have hLne : ((Real.log p : ℝ) : ℂ)⁻¹ ≠ 0 := by
      simp only [ne_eq, inv_eq_zero]
      exact_mod_cast (log_pos_of_two_le hp2).ne'
    exact (mul_eq_zero.mp huniq).resolve_right hLne
  have hquarter := h (1 / 4 : ℂ) (by norm_num) (by norm_num)
  rw [Finset.sum_congr rfl (fun q hq => by rw [hzero q hq, zero_mul])] at hquarter
  rw [Finset.sum_const_zero] at hquarter
  norm_num at hquarter

end RHTower.PairedEulerPole
