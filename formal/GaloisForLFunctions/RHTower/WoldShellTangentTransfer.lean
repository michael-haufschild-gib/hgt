import GaloisForLFunctions.RHTower.WoldEulerActivationSquare

/-!
# The shell tangent and its two-prime transfer spectrum

The first normal derivative of a depth shell is the prime-power current `D_m(s) = ∑_p (log p)
p^{-ms}`.  Normalizing by the prime-two atom makes the whole family converge to one, and the same
normalization after removing that atom isolates the prime three.  Consequently the adjacent shell
ratio recovers `2^{-s}` and, after the half-density normalization, `2^{1/2 - s}`.
-/

open Complex Filter Topology ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The shell tangent -/

/-- The depth-`m` shell tangent `D_m(s) = ∑_p (log p) p^{-ms}` of `(14)`. -/
def shellTangent (m : ℕ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))

theorem summable_shellTangentTerm {w : ℂ} (hw : 1 < w.re) :
    Summable fun p : Nat.Primes => (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-w) := by
  have hΛ : Summable (LSeries.term (fun n => (Λ n : ℂ)) w) := LSeriesSummable_vonMangoldt hw
  refine (hΛ.subtype Nat.Prime).congr fun p => ?_
  show LSeries.term (fun n => (Λ n : ℂ)) w (p : ℕ) = _
  rw [LSeries.term_of_ne_zero p.prop.ne_zero, vonMangoldt_apply_prime p.prop, Complex.cpow_neg,
    div_eq_mul_inv]

theorem summable_logPrime_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : Nat.Primes => Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ) := by
  have hw : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hcast : ∀ p : Nat.Primes,
      (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-(σ : ℂ))
        = ((Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro p
    have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hp0]
    congr 2
    push_cast
    ring
  exact Complex.summable_ofReal.mp ((summable_shellTangentTerm hw).congr hcast)

/-- The normalized transfer weight `(b/p)^{z}` in complex form, for natural bases.  The general
real-base statement lives in the Sonin divided-shift layer; this natural-cast form avoids importing
it. -/
theorem natCast_div_cpow {b p : ℕ} (hp : 0 < p) (z : ℂ) :
    (((b : ℝ) / (p : ℝ) : ℝ) : ℂ) ^ z = ((b : ℂ) ^ z) * ((p : ℂ) ^ (-z)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdiv : (0 : ℝ) ≤ (b : ℝ) / (p : ℝ) := by positivity
  have hmul := Complex.mul_cpow_ofReal_nonneg hdiv hp0.le z
  have hbp : (((b : ℝ) / (p : ℝ) : ℝ) : ℂ) * ((p : ℝ) : ℂ) = ((b : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [hbp] at hmul
  have hpz : ((p : ℝ) : ℂ) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp0.ne'))
  have hcastp : ((p : ℝ) : ℂ) = (p : ℂ) := by push_cast; ring
  have hcastb : ((b : ℝ) : ℂ) = (b : ℂ) := by push_cast; ring
  rw [hcastp, hcastb] at hmul
  rw [hcastp] at hpz
  rw [Complex.cpow_neg, ← div_eq_mul_inv, eq_div_iff hpz]
  exact hmul.symm

theorem tendsto_rpow_atTop_of_lt_one {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (fun x : ℝ => c ^ x) atTop (𝓝 0) := by
  have hlog : Real.log c < 0 := Real.log_neg hc hc1
  have hrw : ∀ x : ℝ, c ^ x = Real.exp (Real.log c * x) := fun x => Real.rpow_def_of_pos hc x
  rw [tendsto_congr hrw]
  refine Real.tendsto_exp_atBot.comp ?_
  have hpos : 0 < -Real.log c := by linarith
  have h1 : Tendsto (fun x : ℝ => (-Real.log c) * x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hpos tendsto_id
  have h2 := tendsto_neg_atTop_atBot.comp h1
  simpa [Function.comp_def] using h2

/-- The `b`-normalized transfer weight of a prime at depth `m`. -/
def normalizedTransfer (b m : ℕ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  ((Real.log (p : ℕ) / Real.log b : ℝ) : ℂ) *
    ((((b : ℝ) / (((p : ℕ) : ℝ))) : ℝ) : ℂ) ^ ((m : ℂ) * s)

/-! ## The normalized tail -/

/-- **Normalized prime tails vanish at infinite depth.**  Above the normalizing prime every
normalized transfer weight tends to zero, uniformly enough for termwise summation. -/
theorem tendsto_normalizedPrimeTail {b : ℕ} (hb : 1 < b) (F : Finset Nat.Primes)
    (hF : ∀ p : Nat.Primes, p ∉ F → b < (p : ℕ)) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => ∑' p : ↥((F : Set Nat.Primes)ᶜ),
        normalizedTransfer b m s (p : Nat.Primes)) atTop (𝓝 0) := by
  classical
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hb.le
  have hmem : ∀ p : ↥((F : Set Nat.Primes)ᶜ), b < ((p : Nat.Primes) : ℕ) := by
    intro p
    have hp : (p : Nat.Primes) ∉ F := by
      have hpp := p.prop
      rw [Set.mem_compl_iff, Finset.mem_coe] at hpp
      exact hpp
    exact hF _ hp
  set bound : ↥((F : Set Nat.Primes)ᶜ) → ℝ := fun p =>
    (Real.log ((p : Nat.Primes) : ℕ) / Real.log b) *
      ((b : ℝ) / ((((p : Nat.Primes) : ℕ) : ℝ))) ^ (2 : ℝ) with hboundDef
  have hbound_summable : Summable bound := by
    have hreal := summable_logPrime_rpow (σ := 2) (by norm_num)
    have hrw : ∀ p : Nat.Primes,
        (Real.log (p : ℕ) / Real.log b) * ((b : ℝ) / (((p : ℕ) : ℝ))) ^ (2 : ℝ)
          = ((b : ℝ) ^ (2 : ℝ) / Real.log b) * (Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
      intro p
      have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [Real.div_rpow hb0.le hp0, Real.rpow_neg hp0]
      field_simp
    have := (hreal.mul_left ((b : ℝ) ^ (2 : ℝ) / Real.log b)).congr fun p => (hrw p).symm
    exact this.subtype _
  have hlim : ∀ p : ↥((F : Set Nat.Primes)ᶜ),
      Tendsto (fun m : ℕ => normalizedTransfer b m s (p : Nat.Primes)) atTop (𝓝 0) := by
    intro p
    have hpb : b < ((p : Nat.Primes) : ℕ) := hmem p
    have hp0 : (0 : ℝ) < ((((p : Nat.Primes) : ℕ)) : ℝ) := by
      exact_mod_cast (p : Nat.Primes).prop.pos
    have hratio0 : 0 < (b : ℝ) / ((((p : Nat.Primes) : ℕ)) : ℝ) := by positivity
    have hratio1 : (b : ℝ) / ((((p : Nat.Primes) : ℕ)) : ℝ) < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast hpb
    have hexp : Tendsto (fun m : ℕ => ((m : ℂ) * s).re) atTop atTop := by
      have hfun : ∀ m : ℕ, ((m : ℂ) * s).re = (m : ℝ) * s.re := by
        intro m
        simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
      simp only [hfun]
      exact Filter.Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
    have hnorm : Tendsto (fun m : ℕ =>
        ‖((((b : ℝ) / ((((p : Nat.Primes) : ℕ) : ℝ))) : ℝ) : ℂ) ^ ((m : ℂ) * s)‖) atTop (𝓝 0) := by
      have hrw : ∀ m : ℕ,
          ‖((((b : ℝ) / ((((p : Nat.Primes) : ℕ) : ℝ))) : ℝ) : ℂ) ^ ((m : ℂ) * s)‖
            = ((b : ℝ) / ((((p : Nat.Primes) : ℕ) : ℝ))) ^ (((m : ℂ) * s).re) := fun m =>
        Complex.norm_cpow_eq_rpow_re_of_pos hratio0 _
      simp only [hrw]
      exact (tendsto_rpow_atTop_of_lt_one hratio0 hratio1).comp hexp
    have hzero : Tendsto (fun m : ℕ =>
        ((((b : ℝ) / ((((p : Nat.Primes) : ℕ) : ℝ))) : ℝ) : ℂ) ^ ((m : ℂ) * s)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
    simpa [normalizedTransfer] using hzero.const_mul
      (((Real.log ((p : Nat.Primes) : ℕ) / Real.log b : ℝ) : ℂ))
  have hdom : ∀ᶠ m : ℕ in atTop, ∀ p : ↥((F : Set Nat.Primes)ᶜ),
      ‖normalizedTransfer b m s (p : Nat.Primes)‖ ≤ bound p := by
    have hexp : Tendsto (fun m : ℕ => (m : ℝ) * s.re) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
    filter_upwards [hexp.eventually_ge_atTop 2] with m hm p
    have hpb : b < ((p : Nat.Primes) : ℕ) := hmem p
    have hp0 : (0 : ℝ) < ((((p : Nat.Primes) : ℕ)) : ℝ) := by
      exact_mod_cast (p : Nat.Primes).prop.pos
    have hratio0 : 0 < (b : ℝ) / ((((p : Nat.Primes) : ℕ)) : ℝ) := by positivity
    have hratio1 : (b : ℝ) / ((((p : Nat.Primes) : ℕ)) : ℝ) ≤ 1 := by
      rw [div_le_one hp0]
      exact_mod_cast hpb.le
    have hre : ((m : ℂ) * s).re = (m : ℝ) * s.re := by
      simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    have hlogp : 0 ≤ Real.log ((p : Nat.Primes) : ℕ) :=
      Real.log_nonneg (by exact_mod_cast (p : Nat.Primes).prop.one_lt.le)
    rw [normalizedTransfer, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hratio0,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hre]
    simp only [hboundDef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_ge hratio0 hratio1 hm
  have hmain := tendsto_tsum_of_dominated_convergence hbound_summable hlim hdom
  simpa using hmain


/-! ## Stripping finitely many atoms -/

theorem summable_normalizedTransfer (b : ℕ) {m : ℕ} {s : ℂ} (hms : 1 < ((m : ℂ) * s).re) :
    Summable fun p : Nat.Primes => normalizedTransfer b m s p := by
  have hsum := summable_shellTangentTerm hms
  have hrw : ∀ p : Nat.Primes, normalizedTransfer b m s p
      = (((b : ℂ) ^ ((m : ℂ) * s)) / (Real.log b : ℂ)) *
          ((Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))) := by
    intro p
    rw [normalizedTransfer, natCast_div_cpow p.prop.pos]
    push_cast
    ring
  exact (hsum.mul_left _).congr fun p => (hrw p).symm

/-- **Atom stripping.**  Removing finitely many prime atoms from the shell tangent and normalizing
by a base prime leaves exactly the normalized tail. -/
theorem normalizedShellTangent_sub_atoms (b : ℕ) (F : Finset Nat.Primes) {m : ℕ} {s : ℂ}
    (hms : 1 < ((m : ℂ) * s).re) :
    (((b : ℂ) ^ ((m : ℂ) * s)) / (Real.log b : ℂ)) *
        (shellTangent m s - ∑ p ∈ F, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)))
      = ∑' p : ↥((F : Set Nat.Primes)ᶜ), normalizedTransfer b m s (p : Nat.Primes) := by
  have hsum := summable_shellTangentTerm hms
  have hst : shellTangent m s
      = (∑ p ∈ F, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s)))
        + ∑' p : ↥((F : Set Nat.Primes)ᶜ),
            (Real.log (((p : Nat.Primes) : ℕ)) : ℂ) *
              ((((p : Nat.Primes) : ℕ)) : ℂ) ^ (-((m : ℂ) * s)) :=
    (hsum.sum_add_tsum_compl).symm
  rw [hst, add_sub_cancel_left, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [normalizedTransfer, natCast_div_cpow (p : Nat.Primes).prop.pos]
  push_cast
  ring

theorem eventually_one_lt_re_natMul {s : ℂ} (hs : 0 < s.re) :
    ∀ᶠ m : ℕ in atTop, 1 < ((m : ℂ) * s).re := by
  have hexp : Tendsto (fun m : ℕ => ((m : ℂ) * s).re) atTop atTop := by
    have hfun : ∀ m : ℕ, ((m : ℂ) * s).re = (m : ℝ) * s.re := by
      intro m
      simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    simp only [hfun]
    exact Filter.Tendsto.atTop_mul_const hs tendsto_natCast_atTop_atTop
  exact hexp.eventually_gt_atTop 1

/-! ## The two-prime transfer spectrum -/

/-- **The prime-two normalization `(15)`.**  The shell tangent normalized by its prime-two atom
tends to one. -/
theorem tendsto_normalized_shellTangent_two {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => ((2 : ℂ) ^ ((m : ℂ) * s) / (Real.log 2 : ℂ)) * shellTangent m s)
      atTop (𝓝 1) := by
  classical
  set F : Finset Nat.Primes := {⟨2, Nat.prime_two⟩} with hF
  have hlog2R : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact hlog2R
  have htail := tendsto_normalizedPrimeTail (b := 2) (by norm_num) F ?_ hs
  · have hsum : Tendsto (fun m : ℕ =>
        (1 : ℂ) + ∑' p : ↥((F : Set Nat.Primes)ᶜ), normalizedTransfer 2 m s (p : Nat.Primes))
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add htail
    refine hsum.congr' ?_
    filter_upwards [eventually_one_lt_re_natMul hs] with m hm
    have hatoms := normalizedShellTangent_sub_atoms 2 F hm
    rw [show (((2 : ℕ) : ℂ)) = (2 : ℂ) from by norm_num,
      show Real.log ((2 : ℕ) : ℝ) = Real.log 2 from by norm_num] at hatoms
    have hpow : (2 : ℂ) ^ ((m : ℂ) * s) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    have hsingle : ∑ p ∈ F, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))
        = (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s)) := by
      rw [hF, Finset.sum_singleton]
      norm_num
    rw [← hatoms, hsingle, mul_sub]
    have hone : (2 : ℂ) ^ ((m : ℂ) * s) / (Real.log 2 : ℂ) *
        ((Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s))) = 1 := by
      rw [Complex.cpow_neg]
      field_simp
    rw [hone]
    ring
  · intro p hp
    have hne : (p : Nat.Primes) ≠ ⟨2, Nat.prime_two⟩ := by
      intro hcon
      exact hp (by simp [hF, hcon])
    have hval : ((p : Nat.Primes) : ℕ) ≠ 2 := by
      intro hcon
      exact hne (Subtype.ext hcon)
    have h2le : 2 ≤ ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).prop.two_le
    omega


/-- **The prime-three normalization `(16)`.**  After removing the prime-two atom the same
normalization by prime three tends to one. -/
theorem tendsto_normalized_shellTangent_three {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => ((3 : ℂ) ^ ((m : ℂ) * s) / (Real.log 3 : ℂ)) *
        (shellTangent m s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s)))) atTop (𝓝 1) := by
  classical
  set F : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} with hF
  have hlog3R : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlog3 : ((Real.log 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact hlog3R
  have htail := tendsto_normalizedPrimeTail (b := 3) (by norm_num) F ?_ hs
  · have hsum : Tendsto (fun m : ℕ =>
        (1 : ℂ) + ∑' p : ↥((F : Set Nat.Primes)ᶜ), normalizedTransfer 3 m s (p : Nat.Primes))
        atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add htail
    refine hsum.congr' ?_
    filter_upwards [eventually_one_lt_re_natMul hs] with m hm
    have hatoms := normalizedShellTangent_sub_atoms 3 F hm
    rw [show (((3 : ℕ) : ℂ)) = (3 : ℂ) from by norm_num,
      show Real.log ((3 : ℕ) : ℝ) = Real.log 3 from by norm_num] at hatoms
    have hpair : ∑ p ∈ F, (Real.log (p : ℕ) : ℂ) * ((p : ℕ) : ℂ) ^ (-((m : ℂ) * s))
        = (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s))
          + (Real.log 3 : ℂ) * (3 : ℂ) ^ (-((m : ℂ) * s)) := by
      rw [hF, Finset.sum_insert (by decide), Finset.sum_singleton]
      norm_num
    rw [← hatoms, hpair]
    have hone : (3 : ℂ) ^ ((m : ℂ) * s) / (Real.log 3 : ℂ) *
        ((Real.log 3 : ℂ) * (3 : ℂ) ^ (-((m : ℂ) * s))) = 1 := by
      rw [Complex.cpow_neg]
      field_simp
    rw [show shellTangent m s - ((Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s))
        + (Real.log 3 : ℂ) * (3 : ℂ) ^ (-((m : ℂ) * s)))
        = (shellTangent m s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s)))
          - (Real.log 3 : ℂ) * (3 : ℂ) ^ (-((m : ℂ) * s)) from by ring, mul_sub, hone]
    ring
  · intro p hp
    have h2 : (p : Nat.Primes) ≠ ⟨2, Nat.prime_two⟩ := by
      intro hcon
      exact hp (by simp [hF, hcon])
    have h3 : (p : Nat.Primes) ≠ ⟨3, Nat.prime_three⟩ := by
      intro hcon
      exact hp (by simp [hF, hcon])
    have hv2 : ((p : Nat.Primes) : ℕ) ≠ 2 := fun hcon => h2 (Subtype.ext hcon)
    have hv3 : ((p : Nat.Primes) : ℕ) ≠ 3 := fun hcon => h3 (Subtype.ext hcon)
    have hle : 2 ≤ ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).prop.two_le
    have hne4 : ((p : Nat.Primes) : ℕ) ≠ 4 := by
      intro hcon
      have := (p : Nat.Primes).prop
      rw [hcon] at this
      norm_num at this
    omega

/-- **Adjacent ratios from a normalization.**  If a complex family is normalized to one by the
weights `b^{ms}/log b`, its adjacent ratio recovers `b^{-s}`. -/
theorem tendsto_ratio_of_normalized {b : ℝ} (hb : 1 < b) {f : ℕ → ℂ} {s : ℂ}
    (hf : Tendsto (fun m : ℕ => (((b : ℝ) : ℂ) ^ ((m : ℂ) * s) / (Real.log b : ℂ)) * f m)
      atTop (𝓝 1)) :
    Tendsto (fun m : ℕ => f (m + 1) / f m) atTop (𝓝 (((b : ℝ) : ℂ) ^ (-s))) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt hb0
  have hlogR : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  have hlog : ((Real.log b : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact hlogR
  set A : ℕ → ℂ := fun m => (((b : ℝ) : ℂ) ^ ((m : ℂ) * s) / (Real.log b : ℂ)) * f m with hA
  have hAlim : Tendsto A atTop (𝓝 1) := hf
  have hAshift : Tendsto (fun m : ℕ => A (m + 1)) atTop (𝓝 1) :=
    hAlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hAne : ∀ᶠ m : ℕ in atTop, A m ≠ 0 := hAlim.eventually_ne one_ne_zero
  have hratio : ∀ᶠ m : ℕ in atTop,
      f (m + 1) / f m = (A (m + 1) / A m) * ((b : ℝ) : ℂ) ^ (-s) := by
    filter_upwards [hAne] with m hm
    have hpow : ∀ k : ℕ, ((b : ℝ) : ℂ) ^ ((k : ℂ) * s) ≠ 0 := fun k =>
      Complex.cpow_ne_zero_iff.mpr (Or.inl hbne)
    have hshell : ∀ k : ℕ, f k
        = A k * (Real.log b : ℂ) * (((b : ℝ) : ℂ) ^ ((k : ℂ) * s))⁻¹ := by
      intro k
      have hk := hpow k
      rw [hA]
      field_simp
    have hcpow : ((b : ℝ) : ℂ) ^ (((m + 1 : ℕ) : ℂ) * s)
        = ((b : ℝ) : ℂ) ^ ((m : ℂ) * s) * ((b : ℝ) : ℂ) ^ s := by
      rw [← Complex.cpow_add _ _ hbne]
      congr 1
      push_cast
      ring
    have hk := hpow m
    have hbs : ((b : ℝ) : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hbne)
    rw [hshell (m + 1), hshell m, hcpow, Complex.cpow_neg]
    field_simp
  refine Tendsto.congr' (hratio.mono fun m hm => hm.symm) ?_
  have hdiv : Tendsto (fun m : ℕ => A (m + 1) / A m) atTop (𝓝 1) := by
    have hd := hAshift.div hAlim one_ne_zero
    simpa [Pi.div_def] using hd
  simpa using hdiv.mul_const (((b : ℝ) : ℂ) ^ (-s))

/-- **The adjacent transfer ratio `(17)`.**  Successive shell tangents recover the prime-two
character. -/
theorem tendsto_shellTangent_ratio {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ => shellTangent (m + 1) s / shellTangent m s) atTop
      (𝓝 ((2 : ℂ) ^ (-s))) := by
  have h := tendsto_ratio_of_normalized (b := (2 : ℝ)) (by norm_num) (s := s)
    (f := fun m => shellTangent m s) ?_
  · simpa using h
  · simpa using tendsto_normalized_shellTangent_two hs

/-- **The residual adjacent transfer ratio.**  After removing the prime-two atom the adjacent
ratio recovers the prime-three character. -/
theorem tendsto_shellTangent_three_ratio {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ =>
        (shellTangent (m + 1) s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-(((m : ℕ) + 1 : ℂ) * s))) /
          (shellTangent m s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s)))) atTop
      (𝓝 ((3 : ℂ) ^ (-s))) := by
  have h := tendsto_ratio_of_normalized (b := (3 : ℝ)) (by norm_num) (s := s)
    (f := fun m => shellTangent m s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s))) ?_
  · simpa using h
  · simpa using tendsto_normalized_shellTangent_three hs

/-! ## The half-density normalization -/

/-- The real shell-tangent mass `δ_m = D_m(1)`. -/
def shellTangentMass (m : ℕ) : ℝ :=
  ∑' p : Nat.Primes, Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(m : ℝ))

theorem ofReal_shellTangentMass (m : ℕ) :
    ((shellTangentMass m : ℝ) : ℂ) = shellTangent m 1 := by
  rw [shellTangentMass, Complex.ofReal_tsum, shellTangent]
  refine tsum_congr fun p => ?_
  have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hp0]
  congr 2
  push_cast
  ring

theorem tendsto_normalized_shellTangentMass :
    Tendsto (fun m : ℕ => ((2 : ℝ) ^ m / Real.log 2) * shellTangentMass m) atTop (𝓝 1) := by
  have hcomplex := tendsto_normalized_shellTangent_two (s := 1) (by norm_num)
  have hcast : ∀ m : ℕ, (2 : ℂ) ^ ((m : ℂ) * 1) / (Real.log 2 : ℂ) * shellTangent m 1
      = ((((2 : ℝ) ^ m / Real.log 2) * shellTangentMass m : ℝ) : ℂ) := by
    intro m
    rw [← ofReal_shellTangentMass]
    push_cast
    rw [mul_one, Complex.cpow_natCast]
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simp only [Function.comp_def, Complex.one_re] at hre
  refine hre.congr fun m => ?_
  rw [hcast m, Complex.ofReal_re]

/-- **Adjacent ratios from a real normalization.** -/
theorem tendsto_ratio_of_normalized_real {b : ℝ} (hb : 1 < b) {g : ℕ → ℝ}
    (hg : Tendsto (fun m : ℕ => (b ^ m / Real.log b) * g m) atTop (𝓝 1)) :
    Tendsto (fun m : ℕ => g m / g (m + 1)) atTop (𝓝 b) := by
  have hb0 : (0 : ℝ) < b := lt_trans zero_lt_one hb
  have hlogR : Real.log b ≠ 0 := ne_of_gt (Real.log_pos hb)
  set a : ℕ → ℝ := fun m => (b ^ m / Real.log b) * g m with ha
  have halim : Tendsto a atTop (𝓝 1) := hg
  have hashift : Tendsto (fun m : ℕ => a (m + 1)) atTop (𝓝 1) :=
    halim.comp (Filter.tendsto_add_atTop_nat 1)
  have hane : ∀ᶠ m : ℕ in atTop, a (m + 1) ≠ 0 := hashift.eventually_ne one_ne_zero
  have hratio : ∀ᶠ m : ℕ in atTop, g m / g (m + 1) = (a m / a (m + 1)) * b := by
    filter_upwards [hane] with m hm
    have hmass : ∀ k : ℕ, g k = a k * Real.log b / b ^ k := by
      intro k
      rw [ha]
      field_simp
    have hbk : (b : ℝ) ^ m ≠ 0 := ne_of_gt (pow_pos hb0 m)
    rw [hmass m, hmass (m + 1), pow_succ]
    field_simp
  refine Tendsto.congr' (hratio.mono fun m hm => hm.symm) ?_
  have hdiv : Tendsto (fun m : ℕ => a m / a (m + 1)) atTop (𝓝 1) := by
    have hd := halim.div hashift one_ne_zero
    simpa [Pi.div_def] using hd
  simpa using hdiv.mul_const b

/-- **The half-density mass ratio.**  Adjacent shell masses have ratio two. -/
theorem tendsto_shellTangentMass_ratio :
    Tendsto (fun m : ℕ => shellTangentMass m / shellTangentMass (m + 1)) atTop (𝓝 2) :=
  tendsto_ratio_of_normalized_real (b := (2 : ℝ)) (by norm_num)
    tendsto_normalized_shellTangentMass

/-- The prime-two-stripped shell mass. -/
def shellTangentMassThree (m : ℕ) : ℝ := shellTangentMass m - Real.log 2 / (2 : ℝ) ^ m

theorem ofReal_shellTangentMassThree (m : ℕ) :
    ((shellTangentMassThree m : ℝ) : ℂ)
      = shellTangent m 1 - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * 1)) := by
  rw [shellTangentMassThree, Complex.ofReal_sub, ofReal_shellTangentMass, mul_one,
    Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  ring

theorem tendsto_normalized_shellTangentMassThree :
    Tendsto (fun m : ℕ => ((3 : ℝ) ^ m / Real.log 3) * shellTangentMassThree m) atTop (𝓝 1) := by
  have hcomplex := tendsto_normalized_shellTangent_three (s := 1) (by norm_num)
  have hcast : ∀ m : ℕ, (3 : ℂ) ^ ((m : ℂ) * 1) / (Real.log 3 : ℂ) *
      (shellTangent m 1 - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * 1)))
      = ((((3 : ℝ) ^ m / Real.log 3) * shellTangentMassThree m : ℝ) : ℂ) := by
    intro m
    rw [← ofReal_shellTangentMassThree]
    push_cast
    rw [mul_one, Complex.cpow_natCast]
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simp only [Function.comp_def, Complex.one_re] at hre
  refine hre.congr fun m => ?_
  rw [hcast m, Complex.ofReal_re]

/-- **The prime-three half-density mass ratio.** -/
theorem tendsto_shellTangentMassThree_ratio :
    Tendsto (fun m : ℕ => shellTangentMassThree m / shellTangentMassThree (m + 1)) atTop (𝓝 3) :=
  tendsto_ratio_of_normalized_real (b := (3 : ℝ)) (by norm_num)
    tendsto_normalized_shellTangentMassThree

/-- **The half-density transfer limit `(18)`.**  The source-normalized adjacent transfer ratio
recovers the critical character `2^{1/2 - s}`. -/
theorem tendsto_halfDensity_shellTangent_ratio {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ =>
        ((Real.sqrt (shellTangentMass m / shellTangentMass (m + 1)) : ℝ) : ℂ) *
          (shellTangent (m + 1) s / shellTangent m s))
      atTop (𝓝 ((2 : ℂ) ^ ((1 : ℂ) / 2 - s))) := by
  have hsqrt : Tendsto (fun m : ℕ =>
      ((Real.sqrt (shellTangentMass m / shellTangentMass (m + 1)) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.sqrt 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_shellTangentMass_ratio.sqrt
  have hmul := hsqrt.mul (tendsto_shellTangent_ratio hs)
  have hval : ((Real.sqrt 2 : ℝ) : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) ^ ((1 : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h2, ← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
  rwa [hval] at hmul


/-- **The prime-three half-density transfer limit `(18)`.**  After removing the prime-two atom the
source-normalized adjacent transfer ratio recovers `3^{1/2 - s}`. -/
theorem tendsto_halfDensity_shellTangent_three_ratio {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun m : ℕ =>
        ((Real.sqrt (shellTangentMassThree m / shellTangentMassThree (m + 1)) : ℝ) : ℂ) *
          ((shellTangent (m + 1) s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-(((m : ℕ) + 1 : ℂ) * s))) /
            (shellTangent m s - (Real.log 2 : ℂ) * (2 : ℂ) ^ (-((m : ℂ) * s)))))
      atTop (𝓝 ((3 : ℂ) ^ ((1 : ℂ) / 2 - s))) := by
  have hsqrt : Tendsto (fun m : ℕ =>
      ((Real.sqrt (shellTangentMassThree m / shellTangentMassThree (m + 1)) : ℝ) : ℂ)) atTop
      (𝓝 ((Real.sqrt 3 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp tendsto_shellTangentMassThree_ratio.sqrt
  have hmul := hsqrt.mul (tendsto_shellTangent_three_ratio hs)
  have hval : ((Real.sqrt 3 : ℝ) : ℂ) * (3 : ℂ) ^ (-s) = (3 : ℂ) ^ ((1 : ℂ) / 2 - s) := by
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) = (3 : ℂ) ^ ((1 : ℂ) / 2) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    rw [h3, ← Complex.cpow_add _ _ (by norm_num : (3 : ℂ) ≠ 0)]
    congr 1
  rwa [hval] at hmul

end

end RHTower
