import GaloisForLFunctions.RHTower.JointAncestryChainFreeHalfPlane
import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectOrderTwentyThreeThresholdAdvance

/-!
# JAS existence holds unconditionally at dressing `2`

At `σ = 2` (`c = 3/2`) both radii of every Xi zero are at most `p^{−3/2}`, so each local phase width
is at most `(8/7) p^{−3/2}`.  Over any finite set of primes these widths add up to at most
`(8/7)(2^{−3/2} + Σ_{odd n ≥ 3} n^{−3/2}) ≤ (8/7) · 3/(2√2)`, using
`n^{−3/2} ≤ (n−1)^{−1/2} − (n+1)^{−1/2}`.  The argument of the weight `1/(ρ(1 − ρ))` is at most
`1/|γ| ≤ 1/14` for an off-line zero (`γ² ≥ 431/2`) and `0` on the line.  The total stays below
`π/2`, so the per-zero phase budgets give positivity:

`JasDressedPSD 2` (`jasDressedPSD_two`), hence `σ* ≤ 2` (`jasAbscissa_le_two`).

With the chain-free bound `Re ρ ≤ ½ + σ*` and, off a chain, `1 + |Re ρ₀ − ½| ≤ σ*`, the JAS
abscissa lies in `[Θ − ½, 2]` always and in `[Θ + ½, 2]` off a chain, and RH is `σ* = 0`.
-/

open Complex

namespace RHTower

noncomputable section

theorem arctan_le_self_of_nonneg' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h0 : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx
  have h1 := Real.le_tan h0 (Real.arctan_lt_pi_div_two x)
  rwa [Real.tan_arctan] at h1

theorem abs_arctan_le_abs' (x : ℝ) : |Real.arctan x| ≤ |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hx), abs_of_nonneg hx]
    exact arctan_le_self_of_nonneg' hx
  · have h := arctan_le_self_of_nonneg' (neg_nonneg.mpr hx)
    rw [Real.arctan_neg] at h
    rw [abs_of_nonpos (Real.arctan_le_zero.mpr hx), abs_of_nonpos hx]
    linarith

/-- For `Re z > 0`, `|arg z| ≤ |Im z| / Re z`. -/
theorem abs_arg_le_abs_im_div_re {z : ℂ} (hz : 0 < z.re) : |z.arg| ≤ |z.im| / z.re := by
  have hlt : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  rw [abs_lt] at hlt
  have harg : z.arg = Real.arctan (z.im / z.re) := by
    rw [← Complex.tan_arg, Real.arctan_tan hlt.1 hlt.2]
  rw [harg]
  refine (abs_arctan_le_abs' _).trans (le_of_eq ?_)
  rw [abs_div, abs_of_pos hz]

/-- The weight argument of every Xi zero is at most `1/14`. -/
theorem abs_arg_jasWeight_le (q : XiZeroCopy) :
    |(1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).arg| ≤ 1 / 14 := by
  set z : ℂ := (q.1 : ℂ) * (1 - (q.1 : ℂ)) with hz
  obtain ⟨hβ0, hβ1⟩ := xiZeroCopy_re_mem_open_unit q
  set β := ((q.1 : ℂ)).re
  set γ := ((q.1 : ℂ)).im
  have hre : z.re = β * (1 - β) + γ ^ 2 := by
    rw [hz]; simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have him : z.im = γ * (1 - 2 * β) := by
    rw [hz]; simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have hre_pos : 0 < z.re := by rw [hre]; nlinarith [sq_nonneg γ]
  have hargz : z.arg ≠ Real.pi := by
    intro h
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  rw [one_div, Complex.arg_inv, if_neg hargz, abs_neg]
  refine (abs_arg_le_abs_im_div_re hre_pos).trans ?_
  rw [div_le_iff₀ hre_pos, him, hre, abs_mul]
  have h12 : |1 - 2 * β| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  by_cases hoff : β = 1 / 2
  · rw [hoff]; norm_num; nlinarith [sq_nonneg γ]
  · have hγ : 431 / 2 ≤ γ ^ 2 := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hoff
    have hγabs : 14 ≤ |γ| := by
      by_contra hlt
      push Not at hlt
      have := mul_self_lt_mul_self (abs_nonneg γ) hlt
      nlinarith [sq_abs γ]
    have hsq : |γ| ^ 2 = γ ^ 2 := sq_abs γ
    have h1 : |γ| * |1 - 2 * β| ≤ |γ| := by
      calc |γ| * |1 - 2 * β| ≤ |γ| * 1 := mul_le_mul_of_nonneg_left h12 (abs_nonneg γ)
        _ = |γ| := mul_one _
    have h2 : |γ| ≤ 1 / 14 * γ ^ 2 := by rw [← hsq]; nlinarith
    nlinarith [mul_pos hβ0 (sub_pos.mpr hβ1)]

/-- A phase width with both radii in `[0, t]`, `t² ≤ 1/8`, is at most `(8/7) t`. -/
theorem jasPhaseWidth_le_of_le {r₁ r₂ t : ℝ} (h₁0 : 0 ≤ r₁) (h₁ : r₁ ≤ t) (h₂0 : 0 ≤ r₂)
    (h₂ : r₂ ≤ t) (ht : t ^ 2 ≤ 1 / 8) : jasPhaseWidth r₁ r₂ ≤ 8 / 7 * t := by
  unfold jasPhaseWidth
  have hd : |r₁ - r₂| ≤ t := by rw [abs_le]; constructor <;> linarith
  have hr₁ : r₁ ^ 2 ≤ 1 / 8 := le_trans (pow_le_pow_left₀ h₁0 h₁ 2) ht
  have hr₂ : r₂ ^ 2 ≤ 1 / 8 := le_trans (pow_le_pow_left₀ h₂0 h₂ 2) ht
  have hprod : (7 / 8 : ℝ) ^ 2 ≤ (1 - r₁ ^ 2) * (1 - r₂ ^ 2) := by
    have a : (7 / 8 : ℝ) ≤ 1 - r₁ ^ 2 := by linarith
    have b : (7 / 8 : ℝ) ≤ 1 - r₂ ^ 2 := by linarith
    nlinarith
  have hsqrt : (7 / 8 : ℝ) ≤ Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) :=
    Real.le_sqrt_of_sq_le hprod
  have hpos : (0 : ℝ) < Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by linarith
  have hratio : |r₁ - r₂| / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ≤ 8 / 7 * t := by
    rw [div_le_iff₀ hpos]
    have ht0 : 0 ≤ t := le_trans h₁0 h₁
    nlinarith
  exact (arctan_le_self_of_nonneg' (div_nonneg (abs_nonneg _) hpos.le)).trans hratio

/-- `p^{−3/2}` as an exponential. -/
def jasThreeHalves (p : Nat.Primes) : ℝ := Real.exp (-(3 / 2) * Real.log p)

theorem jasThreeHalves_nonneg (p : Nat.Primes) : 0 ≤ jasThreeHalves p := (Real.exp_pos _).le

theorem jasThreeHalves_sq_le (p : Nat.Primes) : jasThreeHalves p ^ 2 ≤ 1 / 8 := by
  unfold jasThreeHalves
  rw [← Real.exp_nat_mul]
  have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
  have hlog : Real.log 2 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log (by norm_num) hp
  have h8 : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
    rw [Real.exp_neg, show 3 * Real.log 2 = Real.log 8 by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring,
      Real.exp_log (by norm_num)]; norm_num
  rw [← h8]
  exact Real.exp_le_exp.mpr (by push_cast; nlinarith)

theorem jasR1_le_jasThreeHalves (q : XiZeroCopy) (p : Nat.Primes) :
    jasR1 ((q.1 : ℂ) + ((3 / 2 : ℝ) : ℂ)) p ≤ jasThreeHalves p := by
  rw [jasR1_dressed, jasThreeHalves]
  refine Real.exp_le_exp.mpr ?_
  have hβ := (xiZeroCopy_re_mem_open_unit q).1
  have hl := log_prime_pos p
  nlinarith

theorem jasR2_le_jasThreeHalves (q : XiZeroCopy) (p : Nat.Primes) :
    jasR2 ((q.1 : ℂ) - ((3 / 2 : ℝ) : ℂ)) p ≤ jasThreeHalves p := by
  rw [jasR2_dressed, jasThreeHalves]
  refine Real.exp_le_exp.mpr ?_
  have hβ := (xiZeroCopy_re_mem_open_unit q).2
  have hl := log_prime_pos p
  nlinarith

/-! ## The prime sum `Σ p^{−3/2}` -/

/-- `x^{−3/2} = 1/(x √x)` for `x > 0`. -/
theorem exp_neg_three_halves_log {x : ℝ} (hx : 0 < x) :
    Real.exp (-(3 / 2) * Real.log x) = (x * Real.sqrt x)⁻¹ := by
  have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]; ring_nf
  rw [hs, ← Real.exp_log hx, Real.log_exp, ← Real.exp_add, ← Real.exp_neg]
  ring_nf

/-- **Telescoping majorant:** `1/(n√n) ≤ 1/√(n−1) − 1/√(n+1)` for `n ≥ 2`. -/
theorem inv_mul_sqrt_le_sub {n : ℝ} (hn : 2 ≤ n) :
    (n * Real.sqrt n)⁻¹ ≤ (Real.sqrt (n - 1))⁻¹ - (Real.sqrt (n + 1))⁻¹ := by
  set a := Real.sqrt (n - 1)
  set b := Real.sqrt (n + 1)
  set s := Real.sqrt n
  have ha : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = n - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hab : a * b ≤ s ^ 2 := by
    have h1 : (a * b) ^ 2 ≤ (s ^ 2) ^ 2 := by
      rw [mul_pow, ha2, hb2, hs2]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hsum : a + b ≤ 2 * s := by
    have h1 : (a + b) ^ 2 ≤ (2 * s) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hdiff : a⁻¹ - b⁻¹ = 2 / (a * b * (a + b)) := by
    field_simp
    nlinarith
  rw [hdiff, show n * s = s ^ 2 * s by rw [hs2]]
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hab hsum (by positivity) (by positivity)]

/-- The telescoped sum over odd `n = 2k + 3`, `k < K`. -/
theorem sum_range_odd_inv_le (K : ℕ) :
    ∑ k ∈ Finset.range K, ((2 * (k : ℝ) + 3) * Real.sqrt (2 * (k : ℝ) + 3))⁻¹ ≤
      (Real.sqrt 2)⁻¹ := by
  have hstep : ∀ k : ℕ, ((2 * (k : ℝ) + 3) * Real.sqrt (2 * (k : ℝ) + 3))⁻¹ ≤
      (Real.sqrt (2 * (k : ℝ) + 2))⁻¹ - (Real.sqrt (2 * ((k + 1 : ℕ) : ℝ) + 2))⁻¹ := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have h := inv_mul_sqrt_le_sub (n := 2 * (k : ℝ) + 3) (by linarith)
    have e1 : 2 * (k : ℝ) + 3 - 1 = 2 * (k : ℝ) + 2 := by ring
    have e2 : 2 * (k : ℝ) + 3 + 1 = 2 * ((k + 1 : ℕ) : ℝ) + 2 := by push_cast; ring
    rwa [e1, e2] at h
  refine (Finset.sum_le_sum fun k _ => hstep k).trans ?_
  rw [Finset.sum_range_sub' (fun k : ℕ => (Real.sqrt (2 * (k : ℝ) + 2))⁻¹)]
  have hK : 0 ≤ (Real.sqrt (2 * (K : ℝ) + 2))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  norm_num at hK ⊢

/-- **`Σ_{p ∈ P} p^{−3/2} ≤ 3/(2√2)` for every finite set of primes.** -/
theorem sum_jasThreeHalves_le (P : Finset Nat.Primes) :
    ∑ p ∈ P, jasThreeHalves p ≤ 3 / 2 * (Real.sqrt 2)⁻¹ := by
  classical
  have hval : ∀ p : Nat.Primes, jasThreeHalves p =
      ((((p : ℕ) : ℝ)) * Real.sqrt (((p : ℕ) : ℝ)))⁻¹ := fun p =>
    exp_neg_three_halves_log (by exact_mod_cast p.2.pos)
  rw [← Finset.sum_filter_add_sum_filter_not P (fun p : Nat.Primes => (p : ℕ) = 2)]
  have h2 : ∑ p ∈ P.filter (fun p : Nat.Primes => (p : ℕ) = 2), jasThreeHalves p ≤
      (2 * Real.sqrt 2)⁻¹ := by
    have hsub : P.filter (fun p : Nat.Primes => (p : ℕ) = 2) ⊆ {⟨2, Nat.prime_two⟩} := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      simp only [Finset.mem_singleton]
      exact Subtype.ext hp.2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => jasThreeHalves_nonneg p).trans ?_
    rw [Finset.sum_singleton, hval]
    norm_num
  have hodd : ∑ p ∈ P.filter (fun p : Nat.Primes => ¬ (p : ℕ) = 2), jasThreeHalves p ≤
      (Real.sqrt 2)⁻¹ := by
    set S := P.filter (fun p : Nat.Primes => ¬ (p : ℕ) = 2)
    set φ : Nat.Primes → ℕ := fun p => ((p : ℕ) - 3) / 2
    have hform : ∀ p ∈ S, (p : ℕ) = 2 * φ p + 3 := by
      intro p hp
      simp only [S, Finset.mem_filter] at hp
      have hodd := p.2.eq_two_or_odd'.resolve_left hp.2
      have h3 : 3 ≤ (p : ℕ) := by
        have := p.2.two_le
        rcases hodd with ⟨m, hm⟩
        omega
      rcases hodd with ⟨m, hm⟩
      simp only [φ]
      omega
    have hinj : Set.InjOn φ S := by
      intro p hp p' hp' h
      exact Subtype.ext (by rw [hform p hp, hform p' hp', h])
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ p ∈ S, φ p < K :=
      ⟨(S.sup φ) + 1, fun p hp => Nat.lt_succ_of_le (Finset.le_sup (f := φ) hp)⟩
    have hrewrite : ∑ p ∈ S, jasThreeHalves p =
        ∑ k ∈ S.image φ, ((2 * (k : ℝ) + 3) * Real.sqrt (2 * (k : ℝ) + 3))⁻¹ := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hval, hform p hp]
      push_cast
      ring_nf
    rw [hrewrite]
    have hsub : S.image φ ⊆ Finset.range K := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_range.mpr (hK p hp)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => ?_).trans
      (sum_range_odd_inv_le K)
    positivity
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have e : (2 * Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ = 3 / 2 * (Real.sqrt 2)⁻¹ := by
    field_simp; ring
  linarith

/-- **JAS existence at dressing `2`.** -/
theorem jasDressedPSD_two : JasDressedPSD 2 := by
  have h := jasDressedPSD_of_phaseBudget (c := 3 / 2) (by norm_num) fun q P => by
    have harg := abs_arg_jasWeight_le q
    have hw : ∑ p ∈ P, jasPhaseWidth (jasR1 ((q.1 : ℂ) + ((3 / 2 : ℝ) : ℂ)) p)
        (jasR2 ((q.1 : ℂ) - ((3 / 2 : ℝ) : ℂ)) p) ≤ ∑ p ∈ P, 8 / 7 * jasThreeHalves p :=
      Finset.sum_le_sum fun p _ => jasPhaseWidth_le_of_le
        (Real.exp_pos _).le (jasR1_le_jasThreeHalves q p) (Real.exp_pos _).le
        (jasR2_le_jasThreeHalves q p) (jasThreeHalves_sq_le p)
    rw [← Finset.mul_sum] at hw
    have hsum := sum_jasThreeHalves_le P
    have hs2 : (1.41 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ ≤ 1 / 1.41 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs2
    have hpi := Real.pi_gt_d2
    nlinarith
  norm_num at h
  exact h

/-- **`σ* ≤ 2` unconditionally.** -/
theorem jasAbscissa_le_two : jasAbscissa ≤ 2 :=
  jasDressedPSD_iff_jasAbscissa_le.mp jasDressedPSD_two

end

end RHTower
