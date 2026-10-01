import GaloisForLFunctions.RHTower.WeilRoughFibreSignLaw
import GaloisForLFunctions.RHTower.ZetaNotchTwistPolynomialEnvelope
import GaloisForLFunctions.RHTower.Sieve.MertensSecond

/-!
# The fibre Bochner law of the Weil cone

**Theorem** (`twistFibreSum_nonpos_of_weilPositiveFull`). Let `lam` be full-cone Weil-positive with
notch-small deviation `d = lam − Λ`. Take a finite set `P` of primes, a finite set `A` of exponent
vectors and real coefficients `c`, and let `q(t) = |Σ_{a∈A} c_a e^{itλ(a)}|²`. Then the
`q`-fibre partial sums `Σ_{n≤k} d(n) n^{−½} W_q(n)`, with
`W_q(n) = Σ_{a,a'} c_a c_{a'} (h k)^{−½}` over the reduced twists `h/k = n Π_p p^{−(a−a')_p}`, cannot
stay above a positive level.

Equivalently, in the limit the fibre functionals `Φ(g) = Σ_n d(n) n^{−½} (h_g k_g)^{−½}`, `g ∈ ℤ^P`,
form a kernel `(a, a') ↦ Φ(a − a')` that cannot be eventually positive against any `c`. This is a
Bochner-type negativity law on the Euler fibres.

**Corollary** (`not_weilPositiveFull_evaporationProfile`). For `κ > 0`, HF's pinned
continuous-producer profile `Λ(n) − κ 1_ℙ(n) + κ/log n` (L201) is not Weil-positive. The test is
`q(t) = |1 + 2^{it}|²`, whose main weight is `(2 + √2) n^{−½}` on odd `n` and `(2 + 3/√2) n^{−½}` on
even `n`. The odd and even harmonic sums of the Cramér density `κ/(n log n)` are each
`≈ (κ/2) log log k`, while the prime deficit `−κ/p` is odd. So the fibre sum grows like
`(1/(2√2)) κ log log k`.

With MUST-601 this excludes the whole Cramér-restored family `Λ + κ(1_ℙ − 1/log n)`, `κ ≠ 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-! ## The fibre Bochner law -/

/-- **The fibre Bochner law, deviation form.** If `−ψ_v` is positive definite and `d(n) = √n v(n)`
is notch-small, then for every twist polynomial `q = |Σ_{a∈A} c_a e^{itλ(a)}|²` the partial sums of
`v(n) W_q(n)` cannot stay above a positive level. -/
theorem nonpos_of_twistFibreSum_ge (hP : ∀ p ∈ P, p.Prime) (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ)
    {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p) {v : ℕ → ℝ} (hv0 : v 0 = 0) {Av : ℝ}
    (hA : 0 ≤ Av) (ha : ∀ n, |v n| ≤ 2 * Real.log n + Av)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hd : NotchSmall (sqrtScaled v)) {Y : ℝ} {T : ℕ}
    (hc : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * twistMainWeight P A c n) k) : Y ≤ 0 := by
  by_contra hY
  push Not at hY
  obtain ⟨Dr, hDr0, hDr⟩ :=
    exists_sum_re_weightedMoment_ge_ramp_twist hP A c hβ (K := 7) (by norm_num)
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_abs_twistNotchWeight_le A c
  set a : ℕ → ℝ := fun n => v n * twistMainWeight P A c n with hadef
  set T' := max T 1 with hT'
  set B : ℝ := ∑ k ∈ Finset.range T', |rampPartial a k| with hB
  have hlow : ∀ k, -B ≤ rampPartial a k := by
    intro k
    rcases lt_or_ge k T' with hk | hk
    · have := Finset.single_le_sum (f := fun k => |rampPartial a k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr hk)
      linarith [neg_abs_le (rampPartial a k)]
    · have h1 := hc k ((le_max_left T 1).trans hk)
      have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => abs_nonneg _
      linarith
  obtain ⟨κ, Kc, hκ, hKc, h⟩ := exists_ramp_scale_bound_of (differentiable_twistNotchWeightC A c) hQb1
    (twistNotchWeightC_ofReal A c) (twistNotchWeight_nonneg A c) (continuous_twistNotchWeight A c) hqb one_pos
    (one_le_coordBound hP _) hDr0 (fun {v} hv0 N {u} hu => by rw [one_mul]; exact hDr hv0 N hu)
    hv0 hA ha hPD hd hY (le_max_right T 1) hlow fun k hk => hc k ((le_max_left T 1).trans hk)
  exact false_of_log_scale_bound hκ hKc h

/-- **The fibre Bochner law of the Weil cone.** If `lam` is full-cone Weil-positive and
`d = lam − Λ` is notch-small, then for every twist polynomial `q = |Σ_{a∈A} c_a e^{itλ(a)}|²` the
`q`-fibre partial sums `Σ_{n≤k} d(n) n^{−½} W_q(n)` cannot stay above a positive level. -/
theorem twistFibreSum_nonpos_of_weilPositiveFull {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hd : NotchSmall (WeilOneSided.coneDeviation lam)) (hP : ∀ p ∈ P, p.Prime)
    (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p)
    {Y : ℝ} {T : ℕ}
    (hc : ∀ k, T ≤ k → Y ≤ ∑ n ∈ Finset.range (k + 1),
      WeilOneSided.coneDeviation lam n * (Real.sqrt n)⁻¹ * twistMainWeight P A c n) : Y ≤ 0 := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc : ∀ n, sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    intro n
    simp only [sqrtScaled, hv, RHTower.WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with h2
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hdv : NotchSmall (sqrtScaled v) := by
    have e : sqrtScaled v = WeilOneSided.coneDeviation lam := funext hsc
    rw [e]; exact hd
  have hterm : ∀ n, v n = WeilOneSided.coneDeviation lam n * (Real.sqrt n)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv0, WeilOneSided.coneDeviation]
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [← hsc, sqrtScaled]
    field_simp
  refine nonpos_of_twistFibreSum_ge hP A c hβ hv0 hC0 hC hPD hdv (T := T) fun k hk => ?_
  refine (hc k hk).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  show _ = v n * twistMainWeight P A c n
  rw [hterm]

/-! ## The twist `|1 + 2^{it}|²` -/

/-- The singleton prime set `{2}`. -/
def twoSet : Finset ℕ := {2}

theorem prime_of_mem_twoSet : ∀ p ∈ twoSet, p.Prime := by
  intro p hp
  rw [twoSet, Finset.mem_singleton] at hp
  subst hp
  exact Nat.prime_two

theorem two_mem_twoSet : (2 : ℕ) ∈ twoSet := Finset.mem_singleton_self 2

/-- The point `2` of `twoSet`. -/
def twoPt : twoSet := ⟨2, two_mem_twoSet⟩

theorem eq_twoPt (p : twoSet) : p = twoPt := Subtype.ext (Finset.mem_singleton.mp p.2)

theorem prod_twoSet {M : Type*} [CommMonoid M] (f : twoSet → M) : ∏ p, f p = f twoPt :=
  Fintype.prod_eq_single twoPt fun x hx => absurd (eq_twoPt x) hx

/-- The unit exponent vector at `2`. -/
def unitVec : twoSet → ℤ := fun _ => 1

theorem unitVec_ne_zero : (0 : twoSet → ℤ) ≠ unitVec := by
  intro h
  have := congrFun h twoPt
  simp [unitVec] at this

theorem twistNorm_twoSet {n : ℕ} (g : twoSet → ℤ) :
    twistNorm twoSet n g = (2 : ℝ) ^ (((n.factorization 2 : ℕ) : ℤ) - g twoPt).natAbs *
      roughPart twoSet n := by
  unfold twistNorm vecNum vecDen vecOf
  rw [prod_twoSet, prod_twoSet]
  have h2 : ((twoPt : ℕ)) = 2 := rfl
  simp only [Pi.sub_apply, h2]
  push_cast
  rw [mul_comm ((2 : ℝ) ^ _ * _) _, ← mul_assoc, ← pow_add, add_comm,
    Int.toNat_add_toNat_neg_eq_natAbs, mul_comm]

theorem smoothPart_twoSet (n : ℕ) : smoothPart twoSet n = 2 ^ n.factorization 2 := by
  unfold smoothPart
  rw [prod_twoSet]
  rfl

/-- The main weight of `|1 + 2^{it}|²`: `(2 + √2) n^{−½}` on odd `n`, `(2 + √2 + 1/√2) n^{−½}` on
even `n`. -/
def evenOddWeight (n : ℕ) : ℝ := if 2 ∣ n then 2 + Real.sqrt 2 + (Real.sqrt 2)⁻¹ else 2 + Real.sqrt 2

theorem twistMainWeight_twoSet {n : ℕ} (hn : n ≠ 0) :
    twistMainWeight twoSet {0, unitVec} (fun _ => 1) n = evenOddWeight n * (Real.sqrt n)⁻¹ := by
  unfold twistMainWeight
  rw [Finset.sum_pair unitVec_ne_zero, Finset.sum_pair unitVec_ne_zero,
    Finset.sum_pair unitVec_ne_zero]
  simp only [mul_one, sub_self, zero_sub, sub_zero]
  have hnr' := smoothPart_mul_roughPart (P := twoSet) n hn
  rw [smoothPart_twoSet] at hnr'
  have hnr : (n : ℝ) = 2 ^ n.factorization 2 * (roughPart twoSet n : ℝ) := by
    exact_mod_cast hnr'.symm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs20 : 0 < Real.sqrt 2 := by positivity
  have t0 : twistNorm twoSet n 0 = n := by
    rw [twistNorm_twoSet, hnr]
    simp
  have tm : twistNorm twoSet n (-unitVec) = 2 * n := by
    rw [twistNorm_twoSet, hnr]
    simp only [Pi.neg_apply, unitVec, sub_neg_eq_add]
    rw [show (((n.factorization 2 : ℕ) : ℤ) + 1).natAbs = n.factorization 2 + 1 by omega,
      pow_succ]
    ring
  have e0 : (Real.sqrt (twistNorm twoSet n 0))⁻¹ = (Real.sqrt n)⁻¹ := by rw [t0]
  have em : (Real.sqrt (twistNorm twoSet n (-unitVec)))⁻¹ =
      (Real.sqrt 2)⁻¹ * (Real.sqrt n)⁻¹ := by
    rw [tm, Real.sqrt_mul (by norm_num), mul_inv]
  unfold evenOddWeight
  by_cases h2 : 2 ∣ n
  · have hv1 : 1 ≤ n.factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).mp h2
    have tp : twistNorm twoSet n unitVec = n / 2 := by
      rw [twistNorm_twoSet, hnr]
      simp only [unitVec]
      rw [show (((n.factorization 2 : ℕ) : ℤ) - 1).natAbs = n.factorization 2 - 1 by omega]
      have : (2 : ℝ) ^ n.factorization 2 = 2 ^ (n.factorization 2 - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hv1]
      rw [this]
      ring
    have ep : (Real.sqrt (twistNorm twoSet n unitVec))⁻¹ = Real.sqrt 2 * (Real.sqrt n)⁻¹ := by
      rw [tp, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2), inv_div, div_eq_mul_inv]
    rw [if_pos h2, e0, em, ep]
    ring
  · have hv0 : n.factorization 2 = 0 :=
      (Nat.factorization_eq_zero_iff n 2).mpr (Or.inr (Or.inl h2))
    have tp : twistNorm twoSet n unitVec = 2 * n := by
      rw [twistNorm_twoSet, hnr, hv0]
      simp [unitVec]
    have ep : (Real.sqrt (twistNorm twoSet n unitVec))⁻¹ =
        (Real.sqrt 2)⁻¹ * (Real.sqrt n)⁻¹ := by
      rw [tp, Real.sqrt_mul (by norm_num), mul_inv]
    rw [if_neg h2, e0, em, ep]
    have : (Real.sqrt 2)⁻¹ + (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
      have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      field_simp
      linarith
    linear_combination (Real.sqrt n)⁻¹ * this

/-! ## Parity sums of `1/(n log n)` -/

/-- `log log(n+1) − log log n ≤ 1/(n log n)` for `n ≥ 2`. -/
theorem logLog_succ_sub_le_invNLogN {n : ℕ} (hn : 2 ≤ n) :
    Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) ≤ invNLogN n := by
  unfold invNLogN
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : Real.log n < Real.log ((n + 1 : ℕ) : ℝ) := Real.log_lt_log hn0 (by push_cast; linarith)
  have hb0 : 0 < Real.log ((n + 1 : ℕ) : ℝ) := ha.trans hb
  have h1 : Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log n) ≤
      (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n := by
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha)
    rw [Real.log_div hb0.ne' ha.ne'] at this
    have e : Real.log ((n + 1 : ℕ) : ℝ) / Real.log n - 1 =
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n := by field_simp
    linarith
  have h2 : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ (n : ℝ)⁻¹ := by
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [← Real.log_div hn1.ne' hn0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hn1 hn0)
    have e : ((n + 1 : ℕ) : ℝ) / n - 1 = (n : ℝ)⁻¹ := by push_cast; field_simp; ring
    linarith
  calc _ ≤ (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) / Real.log n := h1
    _ ≤ (n : ℝ)⁻¹ / Real.log n := div_le_div_of_nonneg_right h2 ha.le
    _ = ((n : ℝ) * Real.log n)⁻¹ := by rw [mul_inv, div_eq_mul_inv]

/-- `Σ_{2≤n≤M} 1/(n log n) ≥ log log(M + 1) − log log 2`. -/
theorem sum_invNLogN_ge {M : ℕ} (hM : 2 ≤ M) :
    Real.log (Real.log ((M + 1 : ℕ) : ℝ)) - Real.log (Real.log 2) ≤
      ∑ n ∈ Finset.range (M + 1), (if 2 ≤ n then invNLogN n else 0) := by
  induction M, hM using Nat.le_induction with
  | base =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [show ¬ 2 ≤ 0 by omega, show ¬ 2 ≤ 1 by omega, le_refl, if_true, if_false,
      zero_add]
    have := logLog_succ_sub_le_invNLogN (n := 2) le_rfl
    push_cast at this ⊢
    linarith
  | succ M hM ih =>
    rw [Finset.sum_range_succ, if_pos (by omega)]
    have h := logLog_succ_sub_le_invNLogN (n := M + 1) (by omega)
    linarith

/-- The odd part `Σ_{3≤n≤M, n odd} 1/(n log n)`. -/
def oddInvNLogN (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), (if Odd n ∧ 3 ≤ n then invNLogN n else 0)

/-- The even part `Σ_{2≤n≤M, n even} 1/(n log n)`. -/
def evenInvNLogN (M : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), (if Even n ∧ 2 ≤ n then invNLogN n else 0)

theorem oddInvNLogN_succ_le (M : ℕ) : oddInvNLogN (M + 1) ≤ evenInvNLogN M := by
  induction M with
  | zero =>
    simp [oddInvNLogN, evenInvNLogN, Finset.sum_range_succ]
  | succ M ih =>
    unfold oddInvNLogN evenInvNLogN at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => if Even n ∧ 2 ≤ n then _ else _)]
    rcases Nat.even_or_odd (M + 2) with he | ho
    · have hno : ¬ (Odd (M + 1 + 1) ∧ 3 ≤ M + 1 + 1) := fun h =>
        (Nat.not_odd_iff_even.mpr he) h.1
      rw [if_neg hno]
      have : (0 : ℝ) ≤ (if Even (M + 1) ∧ 2 ≤ M + 1 then invNLogN (M + 1) else 0) := by
        split_ifs
        · exact invNLogN_nonneg _
        · exact le_rfl
      linarith
    · rcases Nat.lt_or_ge M 1 with hM | hM
      · have hM0 : M = 0 := by omega
        subst hM0
        exact absurd ho (by decide)
      · have he1 : Even (M + 1) := by
          rcases ho with ⟨j, hj⟩; exact ⟨j, by omega⟩
        rw [if_pos (show Odd (M + 1 + 1) ∧ 3 ≤ M + 1 + 1 from ⟨ho, by omega⟩),
          if_pos (show Even (M + 1) ∧ 2 ≤ M + 1 from ⟨he1, by omega⟩)]
        have := invNLogN_antitone (n := M + 1) (by omega)
        linarith

theorem evenInvNLogN_succ_le (M : ℕ) : evenInvNLogN (M + 1) ≤ oddInvNLogN M + invNLogN 2 := by
  induction M with
  | zero =>
    simp [oddInvNLogN, evenInvNLogN, Finset.sum_range_succ]
    exact invNLogN_nonneg 2
  | succ M ih =>
    unfold oddInvNLogN evenInvNLogN at ih ⊢
    rw [Finset.sum_range_succ, Finset.sum_range_succ (fun n => if Odd n ∧ 3 ≤ n then _ else _)]
    rcases Nat.even_or_odd (M + 2) with he | ho
    · rcases Nat.lt_or_ge M 1 with hM | hM
      · have hM0 : M = 0 := by omega
        subst hM0
        simp [Finset.sum_range_succ]
      · have hM2 : 2 ≤ M := by rcases he with ⟨j, hj⟩; omega
        have ho1 : Odd (M + 1) := by
          rcases he with ⟨j, hj⟩; exact ⟨j - 1, by omega⟩
        rw [if_pos (show Even (M + 1 + 1) ∧ 2 ≤ M + 1 + 1 from ⟨he, by omega⟩),
          if_pos (show Odd (M + 1) ∧ 3 ≤ M + 1 from ⟨ho1, by omega⟩)]
        have := invNLogN_antitone (n := M + 1) (by omega)
        linarith
    · have hne : ¬ (Even (M + 1 + 1) ∧ 2 ≤ M + 1 + 1) := fun h =>
        (Nat.not_even_iff_odd.mpr ho) h.1
      rw [if_neg hne]
      have : (0 : ℝ) ≤ (if Odd (M + 1) ∧ 3 ≤ M + 1 then invNLogN (M + 1) else 0) := by
        split_ifs
        · exact invNLogN_nonneg _
        · exact le_rfl
      linarith

theorem oddInvNLogN_add_evenInvNLogN (M : ℕ) :
    oddInvNLogN M + evenInvNLogN M =
      ∑ n ∈ Finset.range (M + 1), (if 2 ≤ n then invNLogN n else 0) := by
  unfold oddInvNLogN evenInvNLogN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.even_or_odd n with he | ho
  · have hno : ¬ Odd n := Nat.not_odd_iff_even.mpr he
    by_cases h2 : 2 ≤ n
    · simp [hno, he, h2]
    · simp [hno, h2]
  · have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
    by_cases h2 : 2 ≤ n
    · have h3 : 3 ≤ n := by rcases ho with ⟨j, hj⟩; omega
      simp [hne, ho, h2, h3]
    · have h3 : ¬ 3 ≤ n := by omega
      simp [hne, h2, h3]

theorem evenInvNLogN_le_succ (M : ℕ) : evenInvNLogN M ≤ evenInvNLogN (M + 1) := by
  unfold evenInvNLogN
  rw [Finset.sum_range_succ (fun n => if Even n ∧ 2 ≤ n then invNLogN n else 0) (M + 1)]
  have : (0 : ℝ) ≤ (if Even (M + 1) ∧ 2 ≤ M + 1 then invNLogN (M + 1) else 0) := by
    split_ifs
    · exact invNLogN_nonneg _
    · exact le_rfl
  linarith

theorem oddInvNLogN_le_succ (M : ℕ) : oddInvNLogN M ≤ oddInvNLogN (M + 1) := by
  unfold oddInvNLogN
  rw [Finset.sum_range_succ (fun n => if Odd n ∧ 3 ≤ n then invNLogN n else 0) (M + 1)]
  have : (0 : ℝ) ≤ (if Odd (M + 1) ∧ 3 ≤ M + 1 then invNLogN (M + 1) else 0) := by
    split_ifs
    · exact invNLogN_nonneg _
    · exact le_rfl
  linarith

/-! ## HF's pinned continuous-producer profile -/

theorem sum_odd_prime_inv_le_mertensS (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) ≤
      RHTower.Sieve.mertensS M := by
  unfold RHTower.Sieve.mertensS
  rw [show Nat.primesLE M = (Finset.range (M + 1)).filter Nat.Prime from rfl, Finset.sum_filter]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, one_div]
    split_ifs
    · exact le_rfl
    · positivity
  · rw [if_neg hp, if_neg (fun h => hp h.2)]

/-- The fibre term of `|1 + 2^{it}|²` for the profile `Λ − κ1_ℙ + κ/log n`. -/
theorem evaporation_term_eq (κ : ℝ) (n : ℕ) :
    WeilOneSided.coneDeviation (cramerProfile (-κ)) n * (Real.sqrt n)⁻¹ *
        twistMainWeight twoSet {0, unitVec} (fun _ => 1) n =
      κ * ((2 + Real.sqrt 2) * ((if Odd n ∧ 3 ≤ n then invNLogN n else 0) -
          (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0)) +
        (2 + Real.sqrt 2 + (Real.sqrt 2)⁻¹) * ((if Even n ∧ 2 ≤ n then invNLogN n else 0) -
          (if n = 2 then 1 / 2 else 0))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [WeilOneSided.coneDeviation]
  rw [twistMainWeight_twoSet hn.ne', coneDeviation_cramerProfile]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn0.le]
  have hcollect : ∀ X α : ℝ, X * (Real.sqrt n)⁻¹ * (α * (Real.sqrt n)⁻¹) = X * α * (n : ℝ)⁻¹ := by
    intro X α; rw [← hsq]; ring
  rw [hcollect]
  unfold invNLogN evenOddWeight
  rw [mul_inv]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have h1 : n = 1 := by omega
    subst h1
    simp [Nat.not_prime_one]
  · rcases Nat.even_or_odd n with he | ho
    · have h2d : 2 ∣ n := even_iff_two_dvd.mp he
      have hno : ¬ Odd n := Nat.not_odd_iff_even.mpr he
      rw [if_pos h2d, if_neg (show ¬ (Odd n ∧ 3 ≤ n) from fun h => hno h.1),
        if_neg (show ¬ (Odd n ∧ n.Prime) from fun h => hno h.1),
        if_pos (show Even n ∧ 2 ≤ n from ⟨he, h2⟩), if_pos (show 2 ≤ n from h2)]
      by_cases hp : n.Prime
      · have hn2 : n = 2 := (Nat.Prime.even_iff hp).mp he
        rw [if_pos (show 2 ≤ n ∧ n.Prime from ⟨h2, hp⟩), if_pos hn2]
        subst hn2
        push_cast
        ring
      · have hn2 : n ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
        rw [if_neg (show ¬ (2 ≤ n ∧ n.Prime) from fun h => hp h.2), if_neg hn2]
        ring
    · have hn2d : ¬ 2 ∣ n := fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr h)
      have hne : ¬ Even n := Nat.not_even_iff_odd.mpr ho
      have h3 : 3 ≤ n := by rcases ho with ⟨j, hj⟩; omega
      have hn2 : n ≠ 2 := by omega
      rw [if_neg hn2d, if_pos (show Odd n ∧ 3 ≤ n from ⟨ho, h3⟩),
        if_neg (show ¬ (Even n ∧ 2 ≤ n) from fun h => hne h.1), if_neg hn2,
        if_pos (show 2 ≤ n from h2)]
      by_cases hp : n.Prime
      · rw [if_pos (show 2 ≤ n ∧ n.Prime from ⟨h2, hp⟩), if_pos (show Odd n ∧ n.Prime from ⟨ho, hp⟩)]
        ring
      · rw [if_neg (show ¬ (2 ≤ n ∧ n.Prime) from fun h => hp h.2),
          if_neg (show ¬ (Odd n ∧ n.Prime) from fun h => hp h.2)]
        ring

/-- **HF's pinned continuous producer is not Weil-positive.** For `κ > 0` the profile
`Λ(n) − κ 1_ℙ(n) + κ/log n` is not full-cone Weil-positive. -/
theorem not_weilPositiveFull_evaporationProfile {κ : ℝ} (hκ : 0 < κ) :
    ¬ RHTower.WeilPositiveFull (cramerProfile (-κ)) := by
  intro hW
  set α₁ : ℝ := 2 + Real.sqrt 2 with hα₁
  set α₂ : ℝ := 2 + Real.sqrt 2 + (Real.sqrt 2)⁻¹ with hα₂
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hα₁0 : 0 < α₁ := by positivity
  have hα₂0 : 0 < α₂ := by positivity
  set C₁ : ℝ := 1 + 2 * (RHTower.Sieve.mertensFirstConst / Real.log 2) - RHTower.Sieve.logLog 2
    with hC₁
  set g2 : ℝ := invNLogN 2 with hg2
  set ll2 : ℝ := Real.log (Real.log 2) with hll2
  set Cst : ℝ := α₁ * (|ll2| + g2) / 2 + α₁ * |C₁| + α₂ * (|ll2| + 1) / 2 with hCst
  have hg20 : 0 ≤ g2 := invNLogN_nonneg 2
  have hCst0 : 0 ≤ Cst := by positivity
  set X : ℝ := 2 * Real.sqrt 2 * (Cst + 1) with hX
  set T : ℕ := ⌈Real.exp (Real.exp X)⌉₊ + 2 with hT
  have hβ : ∀ a ∈ ({0, unitVec} : Finset (twoSet → ℤ)), ∀ p,
      |a p| ≤ (((fun _ => 1 : twoSet → ℕ) p : ℕ) : ℤ) := by
    intro a ha p
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [unitVec]
  refine absurd (twistFibreSum_nonpos_of_weilPositiveFull hW (notchSmall_cramer (-κ))
    prime_of_mem_twoSet {0, unitVec} (fun _ => 1) hβ (Y := κ) (T := T) fun k hk => ?_)
    (not_le.mpr hκ)
  rw [Finset.sum_congr rfl fun n _ => evaporation_term_eq κ n, ← Finset.mul_sum]
  have hk2 : 2 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set O := oddInvNLogN k with hO
  set E := evenInvNLogN k with hE
  set Aa := ∑ n ∈ Finset.range (k + 1), (if 2 ≤ n then invNLogN n else 0) with hAa
  set Po := ∑ n ∈ Finset.range (k + 1), (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0) with hPo
  have hsplit : ∑ n ∈ Finset.range (k + 1),
      (α₁ * ((if Odd n ∧ 3 ≤ n then invNLogN n else 0) -
          (if Odd n ∧ n.Prime then (n : ℝ)⁻¹ else 0)) +
        α₂ * ((if Even n ∧ 2 ≤ n then invNLogN n else 0) - (if n = 2 then 1 / 2 else 0))) =
      α₁ * (O - Po) + α₂ * (E - 1 / 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range (k + 1)) 2 (fun _ => (1 : ℝ) / 2),
      if_pos (Finset.mem_range.mpr (by omega))]
    rfl
  rw [hsplit]
  -- the bounds
  have hPo : Po ≤ RHTower.Sieve.logLog k + C₁ :=
    (sum_odd_prime_inv_le_mertensS k).trans (RHTower.Sieve.mertensSecond_upper hk2)
  have hsum : O + E = Aa := oddInvNLogN_add_evenInvNLogN k
  have hOE : O + g2 ≥ E := by
    have h1 : evenInvNLogN (k + 1) ≤ O + g2 := evenInvNLogN_succ_le k
    have h2 : E ≤ evenInvNLogN (k + 1) := evenInvNLogN_le_succ k
    linarith
  have hEO : E ≥ O := by
    have h1 : oddInvNLogN (k + 1) ≤ E := oddInvNLogN_succ_le k
    have h2 : O ≤ oddInvNLogN (k + 1) := oddInvNLogN_le_succ k
    linarith
  have hA : Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - ll2 ≤ Aa := sum_invNLogN_ge hk2
  have hlogk : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hLLmono : Real.log (Real.log k) ≤ Real.log (Real.log ((k + 1 : ℕ) : ℝ)) :=
    Real.log_le_log hlogk (Real.log_le_log hk0 (by push_cast; linarith))
  have hLL : X ≤ Real.log (Real.log k) := by
    have hkT : Real.exp (Real.exp X) ≤ k := by
      have := Nat.le_ceil (Real.exp (Real.exp X))
      have h' : ((⌈Real.exp (Real.exp X)⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega)
      linarith
    rw [Real.le_log_iff_exp_le hlogk, Real.le_log_iff_exp_le hk0]
    exact hkT
  have hlogLog : RHTower.Sieve.logLog k = Real.log (Real.log k) := rfl
  rw [hlogLog] at hPo
  -- `O ≥ (A − g₂)/2` and `E ≥ A/2`, with `A ≥ log log k − log log 2`
  have hO2 : (Real.log (Real.log k) - ll2 - g2) / 2 ≤ O := by linarith
  have hE2 : (Real.log (Real.log k) - ll2) / 2 ≤ E := by linarith
  have hdiff : α₂ - α₁ = (Real.sqrt 2)⁻¹ := by rw [hα₁, hα₂]; ring
  have hmain : 1 ≤ α₁ * (O - Po) + α₂ * (E - 1 / 2) := by
    have h1 : α₁ * ((Real.log (Real.log k) - ll2 - g2) / 2 - (Real.log (Real.log k) + C₁)) ≤
        α₁ * (O - Po) := mul_le_mul_of_nonneg_left (by linarith) hα₁0.le
    have h2 : α₂ * ((Real.log (Real.log k) - ll2) / 2 - 1 / 2) ≤ α₂ * (E - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hα₂0.le
    have h3 : α₁ * ((Real.log (Real.log k) - ll2 - g2) / 2 - (Real.log (Real.log k) + C₁)) +
        α₂ * ((Real.log (Real.log k) - ll2) / 2 - 1 / 2) =
        (α₂ - α₁) / 2 * Real.log (Real.log k) -
          (α₁ * (ll2 + g2) / 2 + α₁ * C₁ + α₂ * (ll2 + 1) / 2) := by ring
    have h4 : α₁ * (ll2 + g2) / 2 + α₁ * C₁ + α₂ * (ll2 + 1) / 2 ≤ Cst := by
      have a1 : α₁ * (ll2 + g2) / 2 ≤ α₁ * (|ll2| + g2) / 2 := by
        have := le_abs_self ll2; gcongr
      have a2 : α₁ * C₁ ≤ α₁ * |C₁| := mul_le_mul_of_nonneg_left (le_abs_self _) hα₁0.le
      have a3 : α₂ * (ll2 + 1) / 2 ≤ α₂ * (|ll2| + 1) / 2 := by
        have := le_abs_self ll2; gcongr
      linarith
    have h5 : Cst + 1 ≤ (α₂ - α₁) / 2 * Real.log (Real.log k) := by
      rw [hdiff]
      have hX' : (Real.sqrt 2)⁻¹ / 2 * X = Cst + 1 := by
        rw [hX]; field_simp
      have := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ (Real.sqrt 2)⁻¹ / 2)
      linarith
    linarith
  nlinarith

/-- **No Cramér-restored profile is Weil-positive.** For every `κ ≠ 0`,
`Λ(n) + κ(1_ℙ(n) − 1/log n)` is not full-cone Weil-positive. Prime excess (`κ > 0`) fails the rough
sign law; prime deficit (`κ < 0`, HF's pinned producer) fails the `|1 + 2^{it}|²` fibre law. -/
theorem not_weilPositiveFull_cramerProfile_of_ne_zero {κ : ℝ} (hκ : κ ≠ 0) :
    ¬ RHTower.WeilPositiveFull (cramerProfile κ) := by
  rcases lt_or_gt_of_ne hκ with h | h
  · have := not_weilPositiveFull_evaporationProfile (κ := -κ) (by linarith)
    rwa [neg_neg] at this
  · exact not_weilPositiveFull_cramerProfile h

end RHTower.WeilAbscissa
