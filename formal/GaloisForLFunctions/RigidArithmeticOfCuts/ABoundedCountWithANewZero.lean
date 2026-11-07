import GaloisForLFunctions.RigidArithmeticOfCuts.StencilSystemsHaveInfiniteDefect
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.ReturnsAreReturnsOfThePrimes

/-!
# A bounded count with a new zero

How close can a count come to `⌊x⌋` and still have a new zero right of the critical line? As close as a bounded error, and the count
can be nonnegative, integral and multiplicative.

**The system.** Count every odd integer once, and every multiple of `8` four times: `a(n) = 1 − 1_{2∣n} + 4·1_{8∣n}`. Then

* `a(n) ∈ {0, 1, 4}` and `a` is multiplicative (`cubicMass_nonneg`, `cubicMass_mul`);
* `N(x) = ⌊x⌋ − ⌊x/2⌋ + 4⌊x/8⌋`, and `−3 ≤ N(x) − x ≤ 0` (`cubicCount_sub_mem`);
* `Σ a(n) n^{-s} = ζ(s) P(2^{-s})` with `P(X) = 1 − X + 4X³` (`hasSum_cubicMass`);
* `P` has a pair of roots of modulus in `(½, 2^{-½})`, so the system has zeros with `½ < Re s < 1`, along a full vertical
  progression (`exists_cubicFactor_eq_zero`, `cubicFactor_shift`);
* its FE defect is not sublinear (`not_tendsto_cubic_defect`).

So a bounded count error does not bring the zeros to the line: only an exact count does (`nonempty_label_equiv_primes`). This does not contradict the Hamming law, since the
Euler factor at `2` has generators of negative multiplicity, of size growing like `2^{β k}/k` on the powers `2^k`. A Beurling system with nonnegative generators carrying a
new zero is a different and open question.
-/

open Complex Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The mass `a(n) = 1 − 1_{2∣n} + 4·1_{8∣n}`. -/
def cubicMass (n : ℕ) : ℤ := 1 - (if 2 ∣ n then 1 else 0) + (if 8 ∣ n then 4 else 0)

theorem cubicMass_nonneg (n : ℕ) : 0 ≤ cubicMass n := by
  unfold cubicMass
  split_ifs <;> norm_num

theorem cubicMass_one : cubicMass 1 = 1 := by decide

private lemma cubicMass_of_odd {m : ℕ} (hm : ¬ 2 ∣ m) : cubicMass m = 1 := by
  have h8 : ¬ 8 ∣ m := fun h => hm (Dvd.dvd.trans (by norm_num) h)
  simp [cubicMass, hm, h8]

/-- **The mass is multiplicative.** -/
theorem cubicMass_mul {m n : ℕ} (h : Nat.Coprime m n) : cubicMass (m * n) = cubicMass m * cubicMass n := by
  have hodd : ¬ 2 ∣ m ∨ ¬ 2 ∣ n := by
    by_contra hc
    push Not at hc
    have := Nat.dvd_gcd hc.1 hc.2
    rw [h] at this
    omega
  rcases hodd with hm | hn
  · have h2 : (2 ∣ m * n) ↔ 2 ∣ n := by
      constructor
      · intro hd
        exact (Nat.Prime.dvd_mul Nat.prime_two).mp hd |>.resolve_left hm
      · exact fun hd => Dvd.dvd.mul_left hd m
    have h8 : (8 ∣ m * n) ↔ 8 ∣ n := by
      have hc : Nat.Coprime 8 m := by
        have : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
        exact Nat.Coprime.pow_left 3 this
      exact ⟨fun hd => hc.dvd_of_dvd_mul_left hd, fun hd => Dvd.dvd.mul_left hd m⟩
    rw [cubicMass_of_odd hm, one_mul, cubicMass, cubicMass]
    simp only [h2, h8]
  · have h2 : (2 ∣ m * n) ↔ 2 ∣ m := by
      constructor
      · intro hd
        exact (Nat.Prime.dvd_mul Nat.prime_two).mp hd |>.resolve_right hn
      · exact fun hd => Dvd.dvd.mul_right hd n
    have h8 : (8 ∣ m * n) ↔ 8 ∣ m := by
      have hc : Nat.Coprime 8 n := by
        have : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn
        exact Nat.Coprime.pow_left 3 this
      exact ⟨fun hd => hc.dvd_of_dvd_mul_right hd, fun hd => Dvd.dvd.mul_right hd n⟩
    rw [cubicMass_of_odd hn, mul_one, cubicMass, cubicMass]
    simp only [h2, h8]

/-- The count of the system. -/
def cubicCount (x : ℕ) : ℤ := ∑ n ∈ Ioc 0 x, cubicMass n

private lemma sum_ite_dvd (d : ℕ) (x : ℕ) :
    ∑ n ∈ Ioc 0 x, (if d ∣ n then (1 : ℤ) else 0) = ((x / d : ℕ) : ℤ) := by
  rw [sum_boole, Nat.Ioc_filter_dvd_card_eq_div]

theorem cubicCount_eq (x : ℕ) : cubicCount x = (x : ℤ) - ((x / 2 : ℕ) : ℤ) + 4 * ((x / 8 : ℕ) : ℤ) := by
  have h4 : ∀ n, (if 8 ∣ n then (4 : ℤ) else 0) = 4 * (if 8 ∣ n then (1 : ℤ) else 0) := by
    intro n
    split_ifs <;> norm_num
  simp only [cubicCount, cubicMass, h4]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_ite_dvd, sum_ite_dvd]
  simp

/-- **The count has bounded error.** `−3 ≤ N(x) − x ≤ 0`. -/
theorem cubicCount_sub_mem (x : ℕ) : -3 ≤ cubicCount x - x ∧ cubicCount x - x ≤ 0 := by
  rw [cubicCount_eq]
  omega

/-! ### The generating function -/

/-- `P(2^{-s})` with `P(X) = 1 − X + 4X³`. -/
def cubicFactor (s : ℂ) : ℂ := 1 - ((2 : ℝ) : ℂ) ^ (-s) + 4 * (((2 : ℝ) : ℂ) ^ (-s)) ^ 3

/-- The multiples of `d` carry `d^{-s} ζ(s)`. -/
private lemma hasSum_dvd {d : ℕ} (hd : 1 ≤ d) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => if d ∣ m + 1 then (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0)
      (((d : ℝ) : ℂ) ^ (-s) * riemannZeta s) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hbase := (ArithmeticAuxiliaryDynamics.hasSum_zetaTerm hs).mul_left (((d : ℝ) : ℂ) ^ (-s))
  set g : ℕ → ℕ := fun k => d * (k + 1) - 1 with hg
  have hg1 : ∀ k, g k + 1 = d * (k + 1) := fun k => by
    have : 1 ≤ d * (k + 1) := Nat.mul_pos hd (Nat.succ_pos k)
    simp only [hg]
    omega
  have hinj : Function.Injective g := by
    intro a b hab
    have h1 : d * (a + 1) = d * (b + 1) := by
      rw [← hg1, ← hg1, hab]
    have h2 := Nat.eq_of_mul_eq_mul_left hd h1
    omega
  have hzero : ∀ m ∉ Set.range g, (if d ∣ m + 1 then (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) = 0 := by
    intro m hm
    rw [if_neg]
    rintro ⟨q, hq⟩
    have hq0 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · simp at hq
      · exact h
    refine hm ⟨q - 1, ?_⟩
    simp only [hg]
    rw [Nat.sub_add_cancel hq0, ← hq]
    simp
  refine (hinj.hasSum_iff hzero).mp ?_
  have hfun : (fun m : ℕ => if d ∣ m + 1 then (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) ∘ g =
      fun k => ((d : ℝ) : ℂ) ^ (-s) * ArithmeticAuxiliaryDynamics.zetaTerm s k := by
    funext k
    simp only [Function.comp]
    have hdvd : d ∣ g k + 1 := by
      rw [hg1]
      exact dvd_mul_right _ _
    rw [if_pos hdvd, ArithmeticAuxiliaryDynamics.zetaTerm]
    have hcast : (((g k : ℕ) : ℝ) + 1) = (d : ℝ) * ((k : ℝ) + 1) := by
      have h2 : (((g k + 1 : ℕ)) : ℝ) = ((d * (k + 1) : ℕ) : ℝ) := by rw [hg1 k]
      push_cast at h2
      exact h2
    rw [hcast]
    have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg hd0.le hk (-s)
  rw [hfun]
  exact hbase

private lemma cpow_eight (s : ℂ) : (((8 : ℕ) : ℝ) : ℂ) ^ (-s) = (((2 : ℝ) : ℂ) ^ (-s)) ^ 3 := by
  have hl : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h8 : (((8 : ℕ) : ℝ) : ℂ) = ((8 : ℝ) : ℂ) := by norm_num
  have h0 : ((8 : ℝ) : ℂ) ≠ 0 := by norm_num
  have h1 : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
  rw [h8, Complex.cpow_def_of_ne_zero h0, Complex.cpow_def_of_ne_zero h1, ← Complex.exp_nat_mul,
    ← Complex.ofReal_log (by norm_num), ← Complex.ofReal_log (by norm_num), hl]
  congr 1
  push_cast
  ring

/-- **The generating function.** `Σ a(n) n^{-s} = ζ(s) P(2^{-s})` on `Re s > 1`. -/
theorem hasSum_cubicMass {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun m : ℕ => ((cubicMass (m + 1) : ℤ) : ℂ) * (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      (riemannZeta s * cubicFactor s) := by
  have h0 := ArithmeticAuxiliaryDynamics.hasSum_zetaTerm hs
  have h2 := hasSum_dvd (d := 2) (by norm_num) hs
  have h8 := (hasSum_dvd (d := 8) (by norm_num) hs).mul_left 4
  have htot := (h0.sub h2).add h8
  rw [cpow_eight] at htot
  have hval : riemannZeta s - (((2 : ℕ) : ℝ) : ℂ) ^ (-s) * riemannZeta s +
      4 * ((((2 : ℝ) : ℂ) ^ (-s)) ^ 3 * riemannZeta s) = riemannZeta s * cubicFactor s := by
    have h2c : (((2 : ℕ) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    rw [h2c, cubicFactor]
    ring
  rw [hval] at htot
  have hfun : (fun m : ℕ => ((cubicMass (m + 1) : ℤ) : ℂ) * (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s)) =
      fun m : ℕ => ArithmeticAuxiliaryDynamics.zetaTerm s m -
        (if 2 ∣ m + 1 then (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) +
        4 * (if 8 ∣ m + 1 then (((m : ℝ) + 1 : ℝ) : ℂ) ^ (-s) else 0) := by
    funext m
    rw [ArithmeticAuxiliaryDynamics.zetaTerm, cubicMass]
    split_ifs <;> push_cast <;> ring
  rw [hfun]
  exact htot

/-! ### The new zero -/

private lemma exists_real_root : ∃ r : ℝ, -(4 / 5) ≤ r ∧ r ≤ -(3 / 4) ∧ 4 * r ^ 3 - r + 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => 4 * x ^ 3 - x + 1) (Set.Icc (-(4 / 5)) (-(3 / 4))) := by fun_prop
  have h := intermediate_value_Icc (by norm_num : (-(4 / 5) : ℝ) ≤ -(3 / 4)) hc
  have h0 : (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => 4 * x ^ 3 - x + 1) (-(4 / 5)))
      ((fun x : ℝ => 4 * x ^ 3 - x + 1) (-(3 / 4))) := by
    constructor <;> norm_num
  obtain ⟨r, hr, hval⟩ := h h0
  exact ⟨r, hr.1, hr.2, hval⟩

/-- **The new zero.** `P(2^{-s})` vanishes at a point with `½ < Re s < 1`. -/
theorem exists_cubicFactor_eq_zero : ∃ ρ : ℂ, 1 / 2 < ρ.re ∧ ρ.re < 1 ∧ cubicFactor ρ = 0 := by
  obtain ⟨r, hr1, hr2, hroot⟩ := exists_real_root
  have hrsq1 : 9 / 16 ≤ r ^ 2 := by nlinarith
  have hrsq2 : r ^ 2 ≤ 16 / 25 := by nlinarith
  set w : ℝ := Real.sqrt (3 / 4 * r ^ 2 - 1 / 4) with hw
  have hw2 : w ^ 2 = 3 / 4 * r ^ 2 - 1 / 4 := Real.sq_sqrt (by linarith)
  set X : ℂ := ((-r / 2 : ℝ) : ℂ) + (w : ℂ) * I with hX
  have hI : I ^ 2 = -1 := Complex.I_sq
  have hW : (w : ℂ) ^ 2 = 3 / 4 * (r : ℂ) ^ 2 - 1 / 4 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hw2
    push_cast at this
    exact this
  have hR : 4 * (r : ℂ) ^ 3 - (r : ℂ) + 1 = 0 := by exact_mod_cast hroot
  have hquad : 4 * X ^ 2 + 4 * (r : ℂ) * X + (4 * (r : ℂ) ^ 2 - 1) = 0 := by
    rw [hX]
    push_cast
    linear_combination (4 * I ^ 2) * hW + (3 * (r : ℂ) ^ 2 - 1) * hI
  have hP : 1 - X + 4 * X ^ 3 = 0 := by
    linear_combination (X - (r : ℂ)) * hquad + hR
  have hnormSq : Complex.normSq X = r ^ 2 - 1 / 4 := by
    rw [hX, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    nlinarith
  have hm1 : 1 / 4 < Complex.normSq X := by rw [hnormSq]; linarith
  have hm2 : Complex.normSq X < 1 / 2 := by rw [hnormSq]; linarith
  have hX0 : X ≠ 0 := by
    intro h
    rw [h, map_zero] at hm1
    norm_num at hm1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2C : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog2.ne'
  refine ⟨-Complex.log X / ((Real.log 2 : ℝ) : ℂ), ?_, ?_, ?_⟩
  all_goals
    have hre : (-Complex.log X / ((Real.log 2 : ℝ) : ℂ)).re = -Real.log ‖X‖ / Real.log 2 := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    have hnorm : Real.log (Complex.normSq X) = 2 * Real.log ‖X‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.log_pow]
      norm_num
    have hup : Real.log (Complex.normSq X) < -Real.log 2 := by
      have h3 := Real.log_lt_log (by linarith) hm2
      rw [one_div, Real.log_inv] at h3
      exact h3
    have hlo : -(2 * Real.log 2) < Real.log (Complex.normSq X) := by
      have h3 := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) hm1
      have h4 : Real.log (1 / 4) = -(2 * Real.log 2) := by
        rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rwa [h4] at h3
  · rw [hre, lt_div_iff₀ hlog2]
    linarith
  · rw [hre, div_lt_one hlog2]
    linarith
  · have hcpow : ((2 : ℝ) : ℂ) ^ (-(-Complex.log X / ((Real.log 2 : ℝ) : ℂ))) = X := by
      have h2 : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
      rw [Complex.cpow_def_of_ne_zero h2, ← Complex.ofReal_log (by norm_num)]
      have h3 : ((Real.log 2 : ℝ) : ℂ) * -(-Complex.log X / ((Real.log 2 : ℝ) : ℂ)) = Complex.log X := by
        field_simp
      rw [h3, Complex.exp_log hX0]
    rw [cubicFactor, hcpow]
    exact hP

/-- The vertical period of `P(2^{-s})`. -/
theorem cubicFactor_shift (s : ℂ) (k : ℤ) :
    cubicFactor (s + (k : ℂ) * ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I) = cubicFactor s := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog2.ne'
  have h2 : ((2 : ℝ) : ℂ) ≠ 0 := by norm_num
  have hshift : ((2 : ℝ) : ℂ) ^ (-(s + (k : ℂ) * ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I)) =
      ((2 : ℝ) : ℂ) ^ (-s) := by
    rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h2, ← Complex.ofReal_log (by norm_num)]
    have hsplit : ((Real.log 2 : ℝ) : ℂ) * -(s + (k : ℂ) * ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I) =
        ((Real.log 2 : ℝ) : ℂ) * -s + ((-k : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast
      field_simp
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [cubicFactor, cubicFactor, hshift]

/-! ### The defect -/

/-- The letters of the stencil. -/
def cubicLetters : Finset ℕ := {1, 2, 8}

/-- The coefficients of the stencil. -/
def cubicCoeff (n : ℕ) : ℂ := if n = 1 then 1 else if n = 2 then -1 else if n = 8 then 4 else 0

theorem dirichletPolyOf_cubic (s : ℂ) : dirichletPolyOf cubicLetters cubicCoeff s = cubicFactor s := by
  have h1 : (((1 : ℕ) : ℝ) : ℂ) ^ (-s) = 1 := by simp
  have h2 : (((2 : ℕ) : ℝ) : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [dirichletPolyOf, cubicLetters, sum_insert (by decide), sum_insert (by decide), sum_singleton, h1,
    cpow_eight, h2, cubicFactor]
  simp [cubicCoeff]
  ring

/-- **The FE defect is not sublinear.** -/
theorem not_tendsto_cubic_defect :
    ¬ Tendsto (fun T : ℝ => T⁻¹ * ∫ t in (0 : ℝ)..T, ‖stencilDefect cubicLetters cubicCoeff t‖) atTop (𝓝 0) := by
  intro h
  have hS : ∀ n ∈ cubicLetters, 1 ≤ n := by decide
  have h2 := eq_zero_of_defect_sublinear hS h 2 (by decide) (by norm_num)
  simp [cubicCoeff] at h2

end GaloisForLFunctions.RigidArithmeticOfCuts
