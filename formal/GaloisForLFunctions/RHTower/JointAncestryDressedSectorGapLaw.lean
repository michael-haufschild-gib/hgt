import GaloisForLFunctions.RHTower.JointAncestryLagAggregatePositivityAbscissa

/-!
# The single-sector gap law for dressed explicit-formula sectors

Dressing a zero's explicit-formula sector by the prime-Poisson sector `μ_σ`, `σ = 1/2 + c`,
multiplies its coefficient at `p^{±k}` by `p^{-ck}`.  The local parameters become

`a_p = p^{-(ρ + c)}`,   `b_p = p^{-(1 - ρ + c)}`,

with radii `r₁ = p^{-(β + c)}`, `r₂ = p^{-(1 - β + c)}` and common height `γ`.

* **Critical line.**  For `β = 1/2` one has `b_p = ā_p` for every dressing, so the dressed sector is
  a positive prime-Poisson density at every depth.
* **Gap law.**  For `β ≠ 1/2` and every dressing with `c < 1/2 + |β - 1/2|`, the smaller radius
  exponent `1/2 - |β - 1/2| + c` is at most `1`, so `Σ_p |r₁ - r₂| = ∞`.  The quarter-point phases
  then accumulate past `π/2` over a finite prime set and the dressed density has negative real part
  at some point of that finite torus.

Thus an off-line zero at distance `δ` from the critical line destroys positivity of its own dressed
sector for every dressing `σ < 1 + δ`, the single-sector form of the predicted positivity gap of
the dressed lag aggregate.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## Generic quarter-point estimates -/

theorem jasQuarterRe_pos {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁' : r₁ < 1) (h₂ : 0 < r₂) (h₂' : r₂ < 1) :
    0 < jasQuarterRe r₁ r₂ := by
  unfold jasQuarterRe
  have e1 : 1 / 2 < 1 / (1 + r₁ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have e2 : 1 / 2 < 1 / (1 + r₂ ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  linarith

theorem jasQuarterRe_le_one {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) : jasQuarterRe r₁ r₂ ≤ 1 := by
  unfold jasQuarterRe
  have e1 : 1 / (1 + r₁ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have e2 : 1 / (1 + r₂ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  linarith

theorem abs_jasQuarterIm_le_one {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    |jasQuarterIm r₁ r₂| ≤ 1 := by
  unfold jasQuarterIm
  rw [abs_le]
  have e1 : r₁ / (1 + r₁ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have e2 : r₂ / (1 + r₂ ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have f1 : 0 ≤ r₁ / (1 + r₁ ^ 2) := by positivity
  have f2 : 0 ≤ r₂ / (1 + r₂ ^ 2) := by positivity
  constructor <;> linarith

theorem abs_sub_div_eight_le_abs_jasQuarterIm' {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁' : r₁ < 1)
    (h₂ : 0 < r₂) (h₂' : r₂ < 1) (hprod : r₁ * r₂ ≤ 1 / 2) :
    |r₁ - r₂| / 8 ≤ |jasQuarterIm r₁ r₂| := by
  rw [jasQuarterIm_eq, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) <
      (1 + r₁ ^ 2) * (1 + r₂ ^ 2)), abs_of_pos (by linarith : (0 : ℝ) < 1 - r₁ * r₂)]
  rw [le_div_iff₀ (by positivity)]
  have a1 : 1 + r₁ ^ 2 ≤ 2 := by nlinarith
  have a2 : 1 + r₂ ^ 2 ≤ 2 := by nlinarith
  have hd : (1 + r₁ ^ 2) * (1 + r₂ ^ 2) ≤ 4 := by
    calc (1 + r₁ ^ 2) * (1 + r₂ ^ 2) ≤ 2 * 2 := mul_le_mul a1 a2 (by positivity) (by norm_num)
      _ = 4 := by norm_num
  nlinarith [abs_nonneg (r₁ - r₂)]

/-- The quarter-point value with nonnegative imaginary part. -/
def jasQuarterComplex (r₁ r₂ : ℝ) : ℂ :=
  ((jasQuarterRe r₁ r₂ : ℝ) : ℂ) + I * ((|jasQuarterIm r₁ r₂| : ℝ) : ℂ)

theorem arg_jasQuarterComplex_ge {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁' : r₁ < 1) (h₂ : 0 < r₂)
    (h₂' : r₂ < 1) (hprod : r₁ * r₂ ≤ 1 / 2) :
    |r₁ - r₂| / 16 ≤ (jasQuarterComplex r₁ r₂).arg := by
  set z := jasQuarterComplex r₁ r₂ with hz
  have hre : z.re = jasQuarterRe r₁ r₂ := by rw [hz, jasQuarterComplex]; simp
  have him : z.im = |jasQuarterIm r₁ r₂| := by rw [hz, jasQuarterComplex]; simp
  have hrepos : 0 < z.re := by rw [hre]; exact jasQuarterRe_pos h₁ h₁' h₂ h₂'
  have hne : z ≠ 0 := fun h => by rw [h, Complex.zero_re] at hrepos; exact lt_irrefl 0 hrepos
  have hnpos : 0 < ‖z‖ := norm_pos_iff.mpr hne
  have hnorm : ‖z‖ ≤ 2 := by
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + 1 := by
          rw [hre, him, abs_abs, abs_of_pos (jasQuarterRe_pos h₁ h₁' h₂ h₂')]
          exact add_le_add (jasQuarterRe_le_one h₁ h₂) (abs_jasQuarterIm_le_one h₁ h₂)
      _ = 2 := by norm_num
  have hargnn : 0 ≤ z.arg := by rw [Complex.arg_nonneg_iff, him]; exact abs_nonneg _
  have hsin := Complex.sin_arg z
  have hle := Real.sin_le hargnn
  have himb := abs_sub_div_eight_le_abs_jasQuarterIm' h₁ h₁' h₂ h₂' hprod
  rw [him] at hsin
  have : |jasQuarterIm r₁ r₂| / 2 ≤ |jasQuarterIm r₁ r₂| / ‖z‖ :=
    div_le_div_of_nonneg_left (abs_nonneg _) hnpos hnorm
  linarith

theorem arg_jasQuarterComplex_lt {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₁' : r₁ < 1) (h₂ : 0 < r₂)
    (h₂' : r₂ < 1) : (jasQuarterComplex r₁ r₂).arg < Real.pi / 2 := by
  apply Complex.arg_lt_pi_div_two_iff.mpr
  left
  rw [jasQuarterComplex]; simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
  simpa using jasQuarterRe_pos h₁ h₁' h₂ h₂'

/-! ## Two-point local densities -/

/-- Local density of a two-point sector: parameters `p^{-s₁}` and `p^{-(1-s₂)}`. -/
def jasTwoPointLocal (s₁ s₂ : ℂ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  jasHoloLocal (jasHoloA s₁ p) (jasHoloB s₂ p) w

theorem jasQuarterPoint_congr_im {s₁ s₂ : ℂ} (h : s₁.im = s₂.im) (p : Nat.Primes) (ε : ℝ) :
    jasQuarterPoint s₁ p ε = jasQuarterPoint s₂ p ε := by
  unfold jasQuarterPoint; rw [h]

/-- Two-point local density at the quarter point. -/
theorem jasTwoPointLocal_quarter {s₁ s₂ : ℂ} (h : s₁.im = s₂.im) (p : Nat.Primes) (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) :
    jasTwoPointLocal s₁ s₂ p (jasQuarterPoint s₁ p ε) =
      ((jasQuarterRe (jasR1 s₁ p) (jasR2 s₂ p) : ℝ) : ℂ) +
        I * ((ε * jasQuarterIm (jasR1 s₁ p) (jasR2 s₂ p) : ℝ) : ℂ) := by
  have hB := jasHoloB_mul_conj_quarter s₂ p ε
  rw [← jasQuarterPoint_congr_im h] at hB
  rw [jasTwoPointLocal, jasHoloLocal, jasHoloA_mul_quarter, hB, sub_neg_eq_add]
  rcases hε with rfl | rfl
  · rw [show (1 : ℂ) - ((1 : ℝ) : ℂ) * I * (jasR1 s₁ p : ℂ) = 1 - I * (jasR1 s₁ p : ℂ) by
        push_cast; ring,
      show (1 : ℂ) + ((1 : ℝ) : ℂ) * I * (jasR2 s₂ p : ℂ) = 1 - I * ((-jasR2 s₂ p : ℝ) : ℂ) by
        push_cast; ring,
      inv_one_sub_I_mul, inv_one_sub_I_mul]
    simp only [jasQuarterRe, jasQuarterIm]
    push_cast
    ring
  · rw [show (1 : ℂ) - ((-1 : ℝ) : ℂ) * I * (jasR1 s₁ p : ℂ) = 1 - I * ((-jasR1 s₁ p : ℝ) : ℂ) by
        push_cast; ring,
      show (1 : ℂ) + ((-1 : ℝ) : ℂ) * I * (jasR2 s₂ p : ℂ) = 1 - I * (jasR2 s₂ p : ℂ) by
        push_cast; ring,
      inv_one_sub_I_mul, inv_one_sub_I_mul]
    simp only [jasQuarterRe, jasQuarterIm]
    push_cast
    ring

/-- Sign choice making the quarter-point imaginary part nonnegative. -/
def jasTwoPointSign (r₁ r₂ : ℝ) : ℝ := if 0 ≤ jasQuarterIm r₁ r₂ then 1 else -1

theorem jasTwoPointSign_cases (r₁ r₂ : ℝ) : jasTwoPointSign r₁ r₂ = 1 ∨ jasTwoPointSign r₁ r₂ = -1 := by
  unfold jasTwoPointSign; split <;> simp

theorem jasTwoPointSign_mul (r₁ r₂ : ℝ) :
    jasTwoPointSign r₁ r₂ * jasQuarterIm r₁ r₂ = |jasQuarterIm r₁ r₂| := by
  unfold jasTwoPointSign
  split
  · rename_i h; rw [one_mul, abs_of_nonneg h]
  · rename_i h; rw [abs_of_neg (lt_of_not_ge h)]; ring

theorem jasTwoPointLocal_signedQuarter {s₁ s₂ : ℂ} (h : s₁.im = s₂.im) (p : Nat.Primes) :
    jasTwoPointLocal s₁ s₂ p
        (jasQuarterPoint s₁ p (jasTwoPointSign (jasR1 s₁ p) (jasR2 s₂ p))) =
      jasQuarterComplex (jasR1 s₁ p) (jasR2 s₂ p) := by
  rw [jasTwoPointLocal_quarter h p _ (jasTwoPointSign_cases _ _), jasTwoPointSign_mul,
    jasQuarterComplex]

/-- **Two-point detection.**  If the radius gap `Σ_p |r₁ - r₂|` diverges, some finite prime set and
some point of its torus make the two-point density have negative real part. -/
theorem exists_re_prod_jasTwoPointLocal_neg {s₁ s₂ : ℂ} (h : s₁.im = s₂.im)
    (hr₁ : ∀ p, jasR1 s₁ p < 1) (hr₂ : ∀ p, jasR2 s₂ p < 1)
    (hprod : ∀ p, jasR1 s₁ p * jasR2 s₂ p ≤ 1 / 2)
    (hdiv : ¬ Summable (fun n : ℕ => |jasR1 s₁ (nthPrimeSubtype n) - jasR2 s₂ (nthPrimeSubtype n)|)) :
    ∃ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) ∧
      (∏ p ∈ P, jasTwoPointLocal s₁ s₂ p (w p)).re < 0 := by
  classical
  set φ : ℕ → ℝ := fun n =>
    (jasQuarterComplex (jasR1 s₁ (nthPrimeSubtype n)) (jasR2 s₂ (nthPrimeSubtype n))).arg with hφ
  have hpos1 : ∀ p, 0 < jasR1 s₁ p := jasR1_pos s₁
  have hpos2 : ∀ p, 0 < jasR2 s₂ p := jasR2_pos s₂
  have hφnn : ∀ n, 0 ≤ φ n := fun n => by
    simp only [hφ]
    rw [Complex.arg_nonneg_iff, jasQuarterComplex]
    simp
  have hφlt : ∀ n, φ n < Real.pi / 2 := fun n =>
    arg_jasQuarterComplex_lt (hpos1 _) (hr₁ _) (hpos2 _) (hr₂ _)
  have hφge : ∀ n, |jasR1 s₁ (nthPrimeSubtype n) - jasR2 s₂ (nthPrimeSubtype n)| / 16 ≤ φ n :=
    fun n => arg_jasQuarterComplex_ge (hpos1 _) (hr₁ _) (hpos2 _) (hr₂ _) (hprod _)
  have hnot : ¬ Summable φ := by
    intro hs
    apply hdiv
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) (hs.mul_left 16)
    have := hφge n
    linarith
  have htend : Tendsto (fun N => ∑ n ∈ Finset.range N, φ n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hφnn).mp hnot
  have hex : ∃ N, Real.pi / 2 < ∑ n ∈ Finset.range N, φ n :=
    (htend.eventually_gt_atTop (Real.pi / 2)).exists
  set N := Nat.find hex with hN
  have hNspec : Real.pi / 2 < ∑ n ∈ Finset.range N, φ n := Nat.find_spec hex
  have hNpos : N ≠ 0 := by
    intro h0
    rw [h0, Finset.sum_range_zero] at hNspec
    linarith [Real.pi_pos]
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hNpos
  have hprev : ∑ n ∈ Finset.range M, φ n ≤ Real.pi / 2 :=
    le_of_not_gt (Nat.find_min hex (show M < N by omega))
  have hupper : ∑ n ∈ Finset.range N, φ n < Real.pi := by
    rw [hM, Finset.sum_range_succ]
    linarith [hφlt M]
  refine ⟨(Finset.range N).image nthPrimeSubtype,
    fun p => jasQuarterPoint s₁ p (jasTwoPointSign (jasR1 s₁ p) (jasR2 s₂ p)),
    fun p => norm_jasQuarterPoint s₁ p (by
      rcases jasTwoPointSign_cases (jasR1 s₁ p) (jasR2 s₂ p) with h' | h' <;> rw [h'] <;> simp), ?_⟩
  have hinj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N,
      nthPrimeSubtype x = nthPrimeSubtype y → x = y :=
    fun x _ y _ hxy => nthPrimeEquiv.injective hxy
  rw [Finset.prod_image hinj]
  simp_rw [jasTwoPointLocal_signedQuarter h]
  rw [prod_eq_prod_norm_mul_exp_sum_arg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  apply mul_neg_of_pos_of_neg
  · refine Finset.prod_pos fun n _ => norm_pos_iff.mpr ?_
    intro h0
    have := jasQuarterRe_pos (hpos1 (nthPrimeSubtype n)) (hr₁ _) (hpos2 (nthPrimeSubtype n)) (hr₂ _)
    have hre := congrArg Complex.re h0
    rw [jasQuarterComplex] at hre
    simp at hre
    linarith
  · exact Real.cos_neg_of_pi_div_two_lt_of_lt hNspec (by linarith [Real.pi_pos])

/-! ## Dressed sectors of strip points -/

/-- The `c`-dressed explicit-formula local density of `ρ`: parameters `p^{-(ρ + c)}` and
`p^{-(1 - ρ + c)}`. -/
def jasDressedLocal (ρ : ℂ) (c : ℝ) (p : Nat.Primes) (w : ℂ) : ℂ :=
  jasTwoPointLocal (ρ + c) (ρ - c) p w

theorem jasR1_dressed (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasR1 (ρ + c) p = Real.exp (-(ρ.re + c) * Real.log p) := by
  rw [jasR1]; congr 2

theorem jasR2_dressed (ρ : ℂ) (c : ℝ) (p : Nat.Primes) :
    jasR2 (ρ - c) p = Real.exp (-(1 - ρ.re + c) * Real.log p) := by
  rw [jasR2, Complex.sub_re, Complex.ofReal_re]; congr 1; ring

/-- **Critical line**: every dressing of an on-line sector is a positive density at every depth. -/
theorem prod_jasDressedLocal_pos_of_critical {ρ : ℂ} (hρ : ρ.re = 1 / 2) {c : ℝ} (hc : 0 ≤ c)
    (P : Finset Nat.Primes) (w : Nat.Primes → ℂ) (hw : ∀ p, ‖w p‖ = 1) :
    0 < (∏ p ∈ P, jasDressedLocal ρ c p (w p)).re := by
  have hconj : ∀ p, jasHoloB (ρ - c) p = conj (jasHoloA (ρ + c) p) := by
    intro p
    rw [jasHoloB, jasHoloA, ← Complex.exp_conj]
    congr 1
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
        Complex.conj_ofReal, hρ]
      ring
    · simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.sub_re, Complex.sub_im,
        Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_mul, map_neg, map_add,
        Complex.conj_ofReal, hρ]
      ring
  have hloc : ∀ p, jasDressedLocal ρ c p (w p) =
      (((jasDressedLocal ρ c p (w p)).re : ℝ) : ℂ) := by
    intro p
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, jasDressedLocal, jasTwoPointLocal, hconj]
      exact im_jasHoloLocal_conj _ _
  have hA : ∀ p, ‖jasHoloA (ρ + c) p‖ < 1 := fun p =>
    norm_jasHoloA_lt_one (by simp [hρ]; linarith) p
  have hB : ∀ p, ‖jasHoloB (ρ - c) p‖ < 1 := fun p => by
    rw [hconj, Complex.norm_conj]; exact hA p
  rw [Finset.prod_congr rfl fun p _ => hloc p, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_pos fun p _ => re_jasHoloLocal_pos (hA p) (hB p) (hw p)

/-- **Single-sector gap law.**  An off-line strip point loses positivity of its dressed
explicit-formula sector at finite depth for every dressing `c < 1/2 + |β - 1/2|`. -/
theorem exists_re_prod_jasDressedLocal_neg {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hoff : ρ.re ≠ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2 + |ρ.re - 1 / 2|) :
    ∃ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) ∧
      (∏ p ∈ P, jasDressedLocal ρ c p (w p)).re < 0 := by
  have him : (ρ + c).im = (ρ - c).im := by simp
  have hp2 : ∀ p : Nat.Primes, Real.log 2 ≤ Real.log (p : ℝ) := fun p =>
    Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr₁ : ∀ p, jasR1 (ρ + c) p < 1 := fun p => by
    rw [jasR1_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hr₂ : ∀ p, jasR2 (ρ - c) p < 1 := fun p => by
    rw [jasR2_dressed, Real.exp_lt_one_iff]; nlinarith [log_prime_pos p]
  have hprod : ∀ p, jasR1 (ρ + c) p * jasR2 (ρ - c) p ≤ 1 / 2 := fun p => by
    rw [jasR1_dressed, jasR2_dressed, ← Real.exp_add]
    have hle : Real.exp (-(ρ.re + c) * Real.log p + -(1 - ρ.re + c) * Real.log p) ≤
        Real.exp (-Real.log 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hp2 p, log_prime_pos p])
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at hle
    linarith
  refine exists_re_prod_jasTwoPointLocal_neg him hr₁ hr₂ hprod ?_
  -- divergence of the radius gap
  intro hsum
  have hprime : Summable (fun p : Nat.Primes => |jasR1 (ρ + c) p - jasR2 (ρ - c) p|) :=
    nthPrimeEquiv.summable_iff.mp hsum
  apply Nat.Primes.not_summable_one_div
  -- smaller exponent `x = min(β + c, 1 - β + c) ≤ 1`, gap ratio bounded below
  set x := min (ρ.re + c) (1 - ρ.re + c) with hx
  set y := max (ρ.re + c) (1 - ρ.re + c) with hy
  have hxy : x < y := by
    rw [hx, hy]
    rcases lt_or_gt_of_ne hoff with hl | hg
    · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [min_eq_right (by linarith), max_eq_left (by linarith)]; linarith
  have hx1 : x ≤ 1 := by
    rw [hx]
    rcases le_total (ρ.re) (1 / 2) with hl | hg
    · rw [abs_of_nonpos (by linarith)] at hc
      exact (min_le_left _ _).trans (by linarith)
    · rw [abs_of_nonneg (by linarith)] at hc
      exact (min_le_right _ _).trans (by linarith)
  set κ := 1 - Real.exp (-(y - x) * Real.log 2) with hκ
  have hκ0 : 0 < κ := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))
  have hbound : ∀ p : Nat.Primes, κ * (1 / (p : ℝ)) ≤ |jasR1 (ρ + c) p - jasR2 (ρ - c) p| := by
    intro p
    have hlp := log_prime_pos p
    have hgapexp : |jasR1 (ρ + c) p - jasR2 (ρ - c) p| =
        Real.exp (-x * Real.log p) - Real.exp (-y * Real.log p) := by
      rw [jasR1_dressed, jasR2_dressed, hx, hy]
      rcases le_total (ρ.re + c) (1 - ρ.re + c) with hl | hg
      · rw [min_eq_left hl, max_eq_right hl, abs_of_nonneg]
        exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))
      · rw [min_eq_right hg, max_eq_left hg, abs_sub_comm, abs_of_nonneg]
        exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))
    rw [hgapexp]
    have hsplit : Real.exp (-y * Real.log p) =
        Real.exp (-x * Real.log p) * Real.exp (-(y - x) * Real.log p) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmono : Real.exp (-(y - x) * Real.log p) ≤ Real.exp (-(y - x) * Real.log 2) :=
      Real.exp_le_exp.mpr (by nlinarith [hp2 p])
    have hpx : 1 / (p : ℝ) ≤ Real.exp (-x * Real.log p) := by
      rw [show 1 / ((p : ℕ) : ℝ) = Real.exp (-Real.log p) by
        rw [Real.exp_neg, Real.exp_log (by exact_mod_cast p.2.pos), one_div]]
      exact Real.exp_le_exp.mpr (by nlinarith)
    rw [hsplit]
    have hE : 0 < Real.exp (-x * Real.log p) := Real.exp_pos _
    calc κ * (1 / (p : ℝ)) ≤ κ * Real.exp (-x * Real.log p) := by gcongr
      _ ≤ Real.exp (-x * Real.log p) * (1 - Real.exp (-(y - x) * Real.log p)) := by
          rw [hκ, mul_comm]; gcongr
      _ = _ := by ring
  have hmaj : Summable (fun p : Nat.Primes => (1 / κ) * |jasR1 (ρ + c) p - jasR2 (ρ - c) p|) :=
    hprime.mul_left _
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) hmaj
  have := hbound p
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hκ0]
  linarith

/-- Every off-line Xi zero destroys positivity of its own dressed sector for every dressing
`σ = 1/2 + c < 1 + |β - 1/2|`, at finite prime depth. -/
theorem xi_offLine_dressedSector_nonpositive (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2 + |(rho : ℂ).re - 1 / 2|) :
    ∃ (P : Finset Nat.Primes) (w : Nat.Primes → ℂ), (∀ p, ‖w p‖ = 1) ∧
      (∏ p ∈ P, jasDressedLocal (rho : ℂ) c p (w p)).re < 0 :=
  exists_re_prod_jasDressedLocal_neg (xi_divisor_support_re_mem_open_unit rho).1
    (xi_divisor_support_re_mem_open_unit rho).2 hoff hc0 hc

end

end RHTower
