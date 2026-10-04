import GaloisForLFunctions.HTGeometry.TranslationFrameOperators
import GaloisForLFunctions.RHTower.MertensSecondRealVariable
import GaloisForLFunctions.RHTower.SelbergClass.DirichletCharacterC1

/-!
# The prime-harmonic logarithmic-end Haar frame

For `L ∈ ℝ` put `X_L = exp (exp L)`.  For an Euler coefficient `λ : ℕ → ℂ`, a grade `a ∈ ℝ` and a
phase `τ`, the end primes `p > X_L` carry the literal amplitudes
`λ(p) p^{-(1+a)/2} e^{-iτ log p}` at the clock coordinates `log log p - L ≥ 0`.  Their weight
measure is

`μ_{a,L} = ∑_{p > X_L} |λ(p)|² p^{-1-a} δ_{log log p - L}`.

With the prime-energy sum `A(x) = ∑_{p ≤ x} |λ(p)|²/p` the neutral window identity is exact:
`μ_{0,L}[0, y] = A(X_{L+y}) - A(X_L)`, so under an energy law `A(x) - κ log log x → C` the
cumulative discrepancy `|μ_{0,L}[0, y] - κ y|` is uniformly at most twice the tail supremum of the
remainder and tends to zero.

* `endClock`, `IsEndPrime`, `endPrimeClock`, `endPrimeCoeff`, `primeEndMeasure`;
* `primeEndMeasure_zero_Icc` — the window identity;
* `primeEndMeasure_zero_Icc_sub` — `μ_{0,L}[0, y] - κ y = r(X_{L+y}) - r(X_L)`;
* `abs_primeEndMeasure_zero_Icc_sub_le`, `tendsto_energyTailSup` — the uniform discrepancy law.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### The end clock and the end primes -/

/-- The end clock `X_L = exp (exp L)`. -/
def endClock (L : ℝ) : ℝ := Real.exp (Real.exp L)

theorem one_lt_endClock (L : ℝ) : 1 < endClock L := by
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ < endClock L := Real.exp_lt_exp.mpr (Real.exp_pos L)

theorem endClock_pos (L : ℝ) : 0 < endClock L := Real.exp_pos _

theorem logLog_endClock (L : ℝ) : Real.log (Real.log (endClock L)) = L := by
  rw [endClock, Real.log_exp, Real.log_exp]

theorem endClock_mono : Monotone endClock := fun _ _ h =>
  Real.exp_le_exp.mpr (Real.exp_le_exp.mpr h)

theorem tendsto_endClock : Tendsto endClock atTop atTop :=
  Real.tendsto_exp_atTop.comp Real.tendsto_exp_atTop

/-- `n` is a prime beyond the end clock. -/
def IsEndPrime (L : ℝ) (n : ℕ) : Prop := n.Prime ∧ endClock L < n

theorem IsEndPrime.one_lt_log {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) : 0 < Real.log n := by
  have : (1 : ℝ) < n := (one_lt_endClock L).trans hn.2
  exact Real.log_pos this

theorem IsEndPrime.pos {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) : (0 : ℝ) < n :=
  (endClock_pos L).trans hn.2

/-- For an end prime, `log log p - L ≤ y` exactly when `p ≤ X_{L+y}`. -/
theorem IsEndPrime.logLog_sub_le_iff {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) (y : ℝ) :
    Real.log (Real.log n) - L ≤ y ↔ (n : ℝ) ≤ endClock (L + y) := by
  rw [sub_le_iff_le_add', Real.log_le_iff_le_exp hn.one_lt_log,
    Real.log_le_iff_le_exp hn.pos, endClock]

theorem IsEndPrime.logLog_sub_pos {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) :
    0 < Real.log (Real.log n) - L := by
  have h := hn.logLog_sub_le_iff 0
  rw [add_zero] at h
  exact lt_of_not_ge fun hle => absurd (h.mp hle) (not_le.mpr hn.2)

open Classical in
/-- The clock coordinate `log log p - L` of an end prime (zero elsewhere). -/
def endPrimeClock (L : ℝ) (n : ℕ) : ℝ :=
  if IsEndPrime L n then Real.log (Real.log n) - L else 0

theorem endPrimeClock_nonneg (L : ℝ) (n : ℕ) : 0 ≤ endPrimeClock L n := by
  unfold endPrimeClock
  split_ifs with h
  · exact h.logLog_sub_pos.le
  · exact le_rfl

open Classical in
/-- The literal Euler amplitude `λ(p) p^{-(1+a)/2} e^{-iτ log p}` of an end prime (zero
elsewhere). -/
def endPrimeCoeff (coef : ℕ → ℂ) (a L τ : ℝ) (n : ℕ) : ℂ :=
  if IsEndPrime L n then
    coef n * (((n : ℝ) ^ (-(1 + a) / 2) : ℝ) : ℂ) *
      Complex.exp (-(((τ * Real.log n : ℝ)) : ℂ) * Complex.I)
  else 0

open Classical in
theorem norm_endPrimeCoeff_sq (coef : ℕ → ℂ) (a L τ : ℝ) (n : ℕ) :
    ‖endPrimeCoeff coef a L τ n‖ ^ 2 =
      if IsEndPrime L n then ‖coef n‖ ^ 2 * (n : ℝ) ^ (-1 - a) else 0 := by
  unfold endPrimeCoeff
  split_ifs with h
  · have hn : (0 : ℝ) ≤ n := h.pos.le
    have hexp : ‖Complex.exp (-(((τ * Real.log n : ℝ)) : ℂ) * Complex.I)‖ = 1 := by
      rw [show -(((τ * Real.log n : ℝ)) : ℂ) * Complex.I =
        ((-(τ * Real.log n) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn _), mul_pow, ← Real.rpow_mul_natCast hn]
    congr 2
    push_cast
    ring
  · simp

/-- The **end measure** `μ_{a,L} = ∑_{p > X_L} |λ(p)|² p^{-1-a} δ_{log log p - L}`. -/
def primeEndMeasure (coef : ℕ → ℂ) (a L : ℝ) : Measure ℝ :=
  translateSystemMeasure (endPrimeCoeff coef a L 0) (endPrimeClock L)

/-- The phase does not enter the weight measure. -/
theorem translateSystemMeasure_endPrimeCoeff (coef : ℕ → ℂ) (a L τ : ℝ) :
    translateSystemMeasure (endPrimeCoeff coef a L τ) (endPrimeClock L) =
      primeEndMeasure coef a L := by
  unfold primeEndMeasure translateSystemMeasure
  simp_rw [norm_endPrimeCoeff_sq]

open Classical in
theorem primeEndMeasure_apply (coef : ℕ → ℂ) (a L : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    primeEndMeasure coef a L S =
      ∑' n, if IsEndPrime L n ∧ Real.log (Real.log n) - L ∈ S then
        ENNReal.ofReal (‖coef n‖ ^ 2 * (n : ℝ) ^ (-1 - a)) else 0 := by
  rw [primeEndMeasure, translateSystemMeasure_apply _ _ hS]
  refine tsum_congr fun n => ?_
  rw [norm_endPrimeCoeff_sq]
  unfold endPrimeClock
  by_cases h : IsEndPrime L n
  · by_cases hs : Real.log (Real.log n) - L ∈ S
    · simp [h, hs]
    · simp [h, hs]
  · simp [h]

/-! ### The neutral window identity -/

/-- The prime-energy sum `A(x) = ∑_{p ≤ x} |λ(p)|² / p`. -/
def primeEnergySum (coef : ℕ → ℂ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, if n.Prime then ‖coef n‖ ^ 2 / n else 0

theorem primeEnergyTerm_nonneg (coef : ℕ → ℂ) (n : ℕ) :
    0 ≤ (if n.Prime then ‖coef n‖ ^ 2 / n else 0 : ℝ) := by
  split_ifs
  · positivity
  · exact le_rfl

theorem primeEnergySum_mono (coef : ℕ → ℂ) : Monotone (primeEnergySum coef) := by
  intro x y hxy
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => primeEnergyTerm_nonneg coef n
  exact Finset.Icc_subset_Icc_right (Nat.floor_mono hxy)

/-- The increment of the energy sum is the sum over the primes in `(X, B]`. -/
theorem primeEnergySum_sub {X B : ℝ} (coef : ℕ → ℂ) (hX : 0 ≤ X) (hXB : X ≤ B) :
    primeEnergySum coef B - primeEnergySum coef X =
      ∑ n ∈ (Finset.Icc 0 ⌊B⌋₊).filter (fun n : ℕ => X < n),
        if n.Prime then ‖coef n‖ ^ 2 / n else 0 := by
  rw [primeEnergySum, primeEnergySum, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 ⌊B⌋₊)
    (fun n : ℕ => X < n)]
  have hset : (Finset.Icc 0 ⌊B⌋₊).filter (fun n : ℕ => ¬ X < n) = Finset.Icc 0 ⌊X⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, not_lt, zero_le, true_and]
    constructor
    · rintro ⟨_, h⟩
      exact Nat.le_floor h
    · intro h
      refine ⟨h.trans (Nat.floor_mono hXB), ?_⟩
      exact (Nat.le_floor_iff hX).mp h
  rw [hset]
  ring

open Classical in
/-- **The neutral window identity**: `μ_{0,L}[0, y] = A(X_{L+y}) - A(X_L)` for `y ≥ 0`. -/
theorem primeEndMeasure_zero_Icc (coef : ℕ → ℂ) (L : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    primeEndMeasure coef 0 L (Icc 0 y) =
      ENNReal.ofReal (primeEnergySum coef (endClock (L + y)) -
        primeEnergySum coef (endClock L)) := by
  have hXB : endClock L ≤ endClock (L + y) := endClock_mono (by linarith)
  rw [primeEnergySum_sub coef (endClock_pos L).le hXB,
    primeEndMeasure_apply _ _ _ measurableSet_Icc,
    ENNReal.ofReal_sum_of_nonneg fun n _ => primeEnergyTerm_nonneg coef n]
  refine tsum_eq_sum (s := (Finset.Icc 0 ⌊endClock (L + y)⌋₊).filter
    (fun n : ℕ => endClock L < n)) (fun n hn => ?_) |>.trans (Finset.sum_congr rfl fun n hn => ?_)
  · rw [if_neg]
    rintro ⟨hp, hS⟩
    apply hn
    simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and]
    refine ⟨Nat.le_floor ((hp.logLog_sub_le_iff y).mp hS.2), hp.2⟩
  · simp only [Finset.mem_filter, Finset.mem_Icc, zero_le, true_and] at hn
    by_cases hprime : n.Prime
    · have hp : IsEndPrime L n := ⟨hprime, hn.2⟩
      have hS : Real.log (Real.log n) - L ∈ Icc 0 y := by
        refine ⟨hp.logLog_sub_pos.le, (hp.logLog_sub_le_iff y).mpr ?_⟩
        exact (Nat.le_floor_iff (endClock_pos _).le).mp hn.1
      rw [if_pos ⟨hp, hS⟩, if_pos hprime, sub_zero, Real.rpow_neg_one, ← div_eq_mul_inv]
    · have hnp : ¬ IsEndPrime L n := fun h => hprime h.1
      simp [hnp, hprime]

theorem primeEndMeasure_zero_Icc_real (coef : ℕ → ℂ) (L : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (primeEndMeasure coef 0 L).real (Icc 0 y) =
      primeEnergySum coef (endClock (L + y)) - primeEnergySum coef (endClock L) := by
  rw [measureReal_def, primeEndMeasure_zero_Icc coef L hy, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (primeEnergySum_mono coef (endClock_mono (by linarith)))

open Classical in
/-- Every end measure is finite on the windows `[0, R]`. -/
theorem primeEndMeasure_Icc_ne_top (coef : ℕ → ℂ) (a L R : ℝ) :
    primeEndMeasure coef a L (Icc 0 R) ≠ ⊤ := by
  rw [primeEndMeasure_apply _ _ _ measurableSet_Icc]
  rw [tsum_eq_sum (s := Finset.Icc 0 ⌊endClock (L + R)⌋₊) fun n hn => ?_]
  · exact ENNReal.sum_ne_top.mpr fun n _ => by
      split_ifs
      exacts [ENNReal.ofReal_ne_top, ENNReal.zero_ne_top]
  · rw [if_neg]
    rintro ⟨hp, hS⟩
    exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor ((hp.logLog_sub_le_iff R).mp hS.2)⟩)

/-! ### The energy law and the uniform discrepancy -/

/-- An **energy law** `∑_{p ≤ x} |λ(p)|²/p = κ log log x + C + o(1)`. -/
def HasPrimeEnergyLaw (coef : ℕ → ℂ) (κ C : ℝ) : Prop :=
  Tendsto (fun x => primeEnergySum coef x - κ * Real.log (Real.log x)) atTop (𝓝 C)

/-- The energy remainder `r(x) = A(x) - κ log log x - C`. -/
def energyRemainder (coef : ℕ → ℂ) (κ C x : ℝ) : ℝ :=
  primeEnergySum coef x - κ * Real.log (Real.log x) - C

theorem HasPrimeEnergyLaw.tendsto_remainder {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) : Tendsto (energyRemainder coef κ C) atTop (𝓝 0) := by
  have := h.sub_const C
  rw [sub_self] at this
  exact this

/-- **Exact discrepancy**: `μ_{0,L}[0, y] - κ y = r(X_{L+y}) - r(X_L)`. -/
theorem primeEndMeasure_zero_Icc_sub (coef : ℕ → ℂ) (κ C L : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    (primeEndMeasure coef 0 L).real (Icc 0 y) - κ * y =
      energyRemainder coef κ C (endClock (L + y)) - energyRemainder coef κ C (endClock L) := by
  rw [primeEndMeasure_zero_Icc_real coef L hy, energyRemainder, energyRemainder,
    logLog_endClock, logLog_endClock]
  ring

/-- The remainder is bounded on every tail `[X_L, ∞)`. -/
theorem HasPrimeEnergyLaw.bddAbove_remainder {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) (L : ℝ) :
    BddAbove (Set.range fun x : Ici (endClock L) => |energyRemainder coef κ C x|) := by
  obtain ⟨X₀, hX₀⟩ := (h.tendsto_remainder.eventually
    (Metric.ball_mem_nhds (0 : ℝ) one_pos)).exists_forall_of_atTop
  refine ⟨max 1 (primeEnergySum coef (max X₀ (endClock L)) +
    |κ| * max |L| |Real.log (Real.log (max X₀ (endClock L)))| + |C|), ?_⟩
  rintro _ ⟨⟨x, hx⟩, rfl⟩
  simp only [mem_Ici] at hx
  by_cases hxX : X₀ ≤ x
  · have := hX₀ x hxX
    rw [Real.dist_eq, sub_zero] at this
    exact this.le.trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    have hx1 : 1 < x := (one_lt_endClock L).trans_le hx
    have hlog : 0 < Real.log x := Real.log_pos hx1
    have hxM : x ≤ max X₀ (endClock L) := (lt_of_not_ge hxX).le.trans (le_max_left _ _)
    have hA0 : 0 ≤ primeEnergySum coef x :=
      Finset.sum_nonneg fun n _ => primeEnergyTerm_nonneg coef n
    have hA : primeEnergySum coef x ≤ primeEnergySum coef (max X₀ (endClock L)) :=
      primeEnergySum_mono coef hxM
    have hLL : |Real.log (Real.log x)| ≤ max |L| |Real.log (Real.log (max X₀ (endClock L)))| := by
      have hlow : L ≤ Real.log (Real.log x) := by
        rw [← logLog_endClock L]
        exact Real.log_le_log (Real.log_pos (one_lt_endClock L))
          (Real.log_le_log (endClock_pos L) hx)
      have hupp : Real.log (Real.log x) ≤ Real.log (Real.log (max X₀ (endClock L))) :=
        Real.log_le_log hlog (Real.log_le_log (by linarith) hxM)
      rw [abs_le]
      constructor
      · have := neg_abs_le L
        have := le_max_left |L| |Real.log (Real.log (max X₀ (endClock L)))|
        linarith
      · have := le_abs_self (Real.log (Real.log (max X₀ (endClock L))))
        have := le_max_right |L| |Real.log (Real.log (max X₀ (endClock L)))|
        linarith
    unfold energyRemainder
    calc |primeEnergySum coef x - κ * Real.log (Real.log x) - C|
        ≤ |primeEnergySum coef x| + |κ * Real.log (Real.log x)| + |C| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_sub _ _
      _ ≤ primeEnergySum coef (max X₀ (endClock L)) +
            |κ| * max |L| |Real.log (Real.log (max X₀ (endClock L)))| + |C| := by
          rw [abs_of_nonneg hA0, abs_mul]
          gcongr

/-- The **tail supremum** `sup_{x ≥ X_L} |r(x)|` of the energy remainder. -/
def energyTailSup (coef : ℕ → ℂ) (κ C L : ℝ) : ℝ :=
  ⨆ x : Ici (endClock L), |energyRemainder coef κ C x|

theorem abs_energyRemainder_le_tailSup {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) {L x : ℝ} (hx : endClock L ≤ x) :
    |energyRemainder coef κ C x| ≤ energyTailSup coef κ C L :=
  le_ciSup (h.bddAbove_remainder L) ⟨x, hx⟩

theorem energyTailSup_nonneg {coef : ℕ → ℂ} {κ C : ℝ} (h : HasPrimeEnergyLaw coef κ C)
    (L : ℝ) : 0 ≤ energyTailSup coef κ C L :=
  (abs_nonneg _).trans (abs_energyRemainder_le_tailSup h le_rfl)

/-- The tail supremum tends to zero. -/
theorem tendsto_energyTailSup {coef : ℕ → ℂ} {κ C : ℝ} (h : HasPrimeEnergyLaw coef κ C) :
    Tendsto (energyTailSup coef κ C) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨X₀, hX₀⟩ := (h.tendsto_remainder.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (half_pos hε))).exists_forall_of_atTop
  obtain ⟨L₀, hL₀⟩ := (tendsto_endClock.eventually_ge_atTop X₀).exists_forall_of_atTop
  refine ⟨L₀, fun L hL => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (energyTailSup_nonneg h L)]
  refine lt_of_le_of_lt (ciSup_le fun x => ?_) (half_lt_self hε)
  have := hX₀ x ((hL₀ L hL).trans x.2)
  rw [Real.dist_eq, sub_zero] at this
  exact this.le

/-- **The uniform discrepancy law**: `|μ_{0,L}[0, y] - κ y| ≤ 2 sup_{x ≥ X_L} |r(x)|`. -/
theorem abs_primeEndMeasure_zero_Icc_sub_le {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) (L : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |(primeEndMeasure coef 0 L).real (Icc 0 y) - κ * y| ≤ 2 * energyTailSup coef κ C L := by
  rw [primeEndMeasure_zero_Icc_sub coef κ C L hy]
  have h1 := abs_energyRemainder_le_tailSup h (endClock_mono (by linarith : L ≤ L + y))
  have h2 := abs_energyRemainder_le_tailSup h (le_refl (endClock L))
  calc |energyRemainder coef κ C (endClock (L + y)) - energyRemainder coef κ C (endClock L)|
      ≤ |energyRemainder coef κ C (endClock (L + y))| + |energyRemainder coef κ C (endClock L)| :=
        abs_sub _ _
    _ ≤ 2 * energyTailSup coef κ C L := by linarith

/-- The **neutral discrepancy** `ε_L = sup_{y ≥ 0} |μ_{0,L}[0, y] - κ y|`. -/
def neutralDiscrepancy (coef : ℕ → ℂ) (κ L : ℝ) : ℝ :=
  ⨆ y : Ici (0 : ℝ), |(primeEndMeasure coef 0 L).real (Icc 0 y) - κ * y|

theorem HasPrimeEnergyLaw.bddAbove_discrepancy {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) (L : ℝ) :
    BddAbove (Set.range fun y : Ici (0 : ℝ) =>
      |(primeEndMeasure coef 0 L).real (Icc 0 y) - κ * y|) :=
  ⟨2 * energyTailSup coef κ C L, by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    exact abs_primeEndMeasure_zero_Icc_sub_le h L hy⟩

theorem abs_primeEndMeasure_zero_Icc_sub_le_discrepancy {coef : ℕ → ℂ} {κ C : ℝ}
    (h : HasPrimeEnergyLaw coef κ C) (L : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |(primeEndMeasure coef 0 L).real (Icc 0 y) - κ * y| ≤ neutralDiscrepancy coef κ L :=
  le_ciSup (h.bddAbove_discrepancy L) ⟨y, hy⟩

/-- `ε_L ≤ 2 sup_{x ≥ X_L} |r(x)|`. -/
theorem neutralDiscrepancy_le {coef : ℕ → ℂ} {κ C : ℝ} (h : HasPrimeEnergyLaw coef κ C)
    (L : ℝ) : neutralDiscrepancy coef κ L ≤ 2 * energyTailSup coef κ C L :=
  ciSup_le fun y => abs_primeEndMeasure_zero_Icc_sub_le h L y.2

theorem neutralDiscrepancy_nonneg {coef : ℕ → ℂ} {κ C : ℝ} (h : HasPrimeEnergyLaw coef κ C)
    (L : ℝ) : 0 ≤ neutralDiscrepancy coef κ L :=
  (abs_nonneg _).trans (abs_primeEndMeasure_zero_Icc_sub_le_discrepancy h L le_rfl)

/-- **`ε_L → 0`**: the neutral end measures converge to `κ dy` on the whole future half-line with
uniform cumulative-discrepancy control. -/
theorem tendsto_neutralDiscrepancy {coef : ℕ → ℂ} {κ C : ℝ} (h : HasPrimeEnergyLaw coef κ C) :
    Tendsto (neutralDiscrepancy coef κ) atTop (𝓝 0) := by
  have hup : Tendsto (fun L => 2 * energyTailSup coef κ C L) atTop (𝓝 0) := by
    simpa using (tendsto_energyTailSup h).const_mul 2
  exact squeeze_zero (neutralDiscrepancy_nonneg h) (neutralDiscrepancy_le h) hup

/-! ### Grades: the tilt relation -/

/-- The **grade tilt** `exp (-a e^{L+t})`: the factor `p^{-a}` at the clock `t = log log p - L`. -/
def gradeTilt (a L t : ℝ) : ℝ := Real.exp (-(a * Real.exp (L + t)))

/-- Its derivative in the clock variable. -/
def gradeTiltDeriv (a L t : ℝ) : ℝ := -(a * Real.exp (L + t)) * gradeTilt a L t

theorem gradeTilt_pos (a L t : ℝ) : 0 < gradeTilt a L t := Real.exp_pos _

theorem continuous_gradeTilt (a L : ℝ) : Continuous (gradeTilt a L) := by
  unfold gradeTilt
  fun_prop

theorem continuous_gradeTiltDeriv (a L : ℝ) : Continuous (gradeTiltDeriv a L) := by
  unfold gradeTiltDeriv gradeTilt
  fun_prop

theorem hasDerivAt_gradeTilt (a L t : ℝ) :
    HasDerivAt (gradeTilt a L) (gradeTiltDeriv a L t) t := by
  have h1 : HasDerivAt (fun s => Real.exp (L + s)) (Real.exp (L + t)) t := by
    simpa using ((hasDerivAt_id t).const_add L).exp
  have h2 : HasDerivAt (fun s => -(a * Real.exp (L + s))) (-(a * Real.exp (L + t))) t := by
    exact (h1.const_mul a).neg
  show HasDerivAt (fun s => Real.exp (-(a * Real.exp (L + s)))) _ t
  convert h2.exp using 1
  unfold gradeTiltDeriv gradeTilt
  ring

theorem IsEndPrime.rpow_neg_eq_gradeTilt {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) (a : ℝ) :
    (n : ℝ) ^ (-a) = gradeTilt a L (Real.log (Real.log n) - L) := by
  rw [gradeTilt, add_sub_cancel, Real.exp_log hn.one_lt_log, Real.rpow_def_of_pos hn.pos]
  ring_nf

/-- **The tilt relation**: `μ_{a,L} = e^{-a e^{L+t}} μ_{0,L}` on the future half-line. -/
theorem setLIntegral_primeEndMeasure (coef : ℕ → ℂ) (a L : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ y in Ici 0, F y ∂primeEndMeasure coef a L =
      ∫⁻ y in Ici 0, ENNReal.ofReal (gradeTilt a L y) * F y ∂primeEndMeasure coef 0 L := by
  rw [primeEndMeasure, primeEndMeasure,
    setLIntegral_Ici_translateSystemMeasure _ (endPrimeClock_nonneg L),
    setLIntegral_Ici_translateSystemMeasure _ (endPrimeClock_nonneg L)]
  refine tsum_congr fun n => ?_
  rw [norm_endPrimeCoeff_sq, norm_endPrimeCoeff_sq]
  unfold endPrimeClock
  by_cases h : IsEndPrime L n
  · rw [if_pos h, if_pos h, if_pos h, ← h.rpow_neg_eq_gradeTilt a, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [sub_zero, mul_assoc, ← Real.rpow_add h.pos]
    ring_nf
  · simp [h]

/-- End measures live on the future half-line. -/
theorem primeEndMeasure_eq_setLIntegral (coef : ℕ → ℂ) (a L : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    primeEndMeasure coef a L S = ∫⁻ y in Ici 0, S.indicator 1 y ∂primeEndMeasure coef a L := by
  rw [primeEndMeasure, translateSystemMeasure_apply _ _ hS,
    setLIntegral_Ici_translateSystemMeasure _ (endPrimeClock_nonneg L)]

/-- **Positive-grade mass** as a tilted neutral integral. -/
theorem primeEndMeasure_univ_eq (coef : ℕ → ℂ) (a L : ℝ) :
    primeEndMeasure coef a L univ =
      ∫⁻ y in Ici 0, ENNReal.ofReal (gradeTilt a L y) ∂primeEndMeasure coef 0 L := by
  rw [primeEndMeasure_eq_setLIntegral _ _ _ MeasurableSet.univ, setLIntegral_primeEndMeasure]
  simp

/-- For `a > 0` the tilt is integrable on `[0, ∞)`. -/
theorem integrableOn_gradeTilt {a : ℝ} (ha : 0 < a) (L : ℝ) :
    IntegrableOn (gradeTilt a L) (Ici 0) := by
  have hb : 0 < a * Real.exp L := mul_pos ha (Real.exp_pos L)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  refine (exp_neg_integrableOn_Ioi 0 hb).mono' (continuous_gradeTilt a L).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun t ht => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (gradeTilt_pos a L t), gradeTilt]
  refine Real.exp_le_exp.mpr ?_
  have h1 : Real.exp L * t ≤ Real.exp (L + t) := by
    rw [Real.exp_add]
    have := Real.add_one_le_exp t
    nlinarith [Real.exp_pos L]
  nlinarith

theorem tendsto_gradeTilt_atTop {a : ℝ} (ha : 0 < a) (L : ℝ) :
    Tendsto (gradeTilt a L) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => a * Real.exp (L + t)) atTop atTop := by
    refine Tendsto.const_mul_atTop ha ?_
    exact Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_left _ L tendsto_id)
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1

theorem gradeTiltDeriv_nonpos {a : ℝ} (ha : 0 ≤ a) (L t : ℝ) : gradeTiltDeriv a L t ≤ 0 := by
  unfold gradeTiltDeriv
  have := gradeTilt_pos a L t
  have := Real.exp_pos (L + t)
  nlinarith [mul_nonneg ha this.le]

theorem integrableOn_gradeTiltDeriv {a : ℝ} (ha : 0 < a) (L : ℝ) :
    IntegrableOn (gradeTiltDeriv a L) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_deriv_of_nonpos (continuous_gradeTilt a L).continuousWithinAt
    (fun t _ => hasDerivAt_gradeTilt a L t) (fun t _ => gradeTiltDeriv_nonpos ha.le L t)
    (tendsto_gradeTilt_atTop ha L)

theorem integral_abs_gradeTiltDeriv_le {a : ℝ} (ha : 0 < a) (L : ℝ) :
    ∫ t in Ici 0, |gradeTiltDeriv a L t| ≤ 1 := by
  have hval := integral_Ioi_of_hasDerivAt_of_nonpos (a := 0) (l := 0)
    (continuous_gradeTilt a L).continuousWithinAt
    (fun t _ => hasDerivAt_gradeTilt a L t) (fun t _ => gradeTiltDeriv_nonpos ha.le L t)
    (tendsto_gradeTilt_atTop ha L)
  have habs : ∫ t in Ici 0, |gradeTiltDeriv a L t| = -∫ t in Ioi 0, gradeTiltDeriv a L t := by
    rw [integral_Ici_eq_integral_Ioi, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact abs_of_nonpos (gradeTiltDeriv_nonpos ha.le L t)
  rw [habs, hval, zero_sub, neg_neg, gradeTilt]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.exp_pos (L + 0)])

/-- `∫_0^∞ e^{-a e^{L+t}} dt → 0` as `L → ∞`. -/
theorem tendsto_integral_gradeTilt {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L => ∫ t in Ici 0, gradeTilt a L t) atTop (𝓝 0) := by
  have hlim : ∀ t : ℝ, Tendsto (fun L => gradeTilt a L t) atTop (𝓝 0) := by
    intro t
    have h1 : Tendsto (fun L => a * Real.exp (L + t)) atTop atTop := by
      refine Tendsto.const_mul_atTop ha ?_
      exact Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ t tendsto_id)
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ici (0 : ℝ)))
    (F := fun L t => gradeTilt a L t) (f := fun _ => 0) (gradeTilt a 0)
    (.of_forall fun L => (continuous_gradeTilt a L).aestronglyMeasurable)
    ((eventually_ge_atTop 0).mono fun L hL => .of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (gradeTilt_pos a L t), gradeTilt, gradeTilt]
      refine Real.exp_le_exp.mpr (neg_le_neg ?_)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) ha.le)
    (integrableOn_gradeTilt ha 0) (.of_forall hlim)
  simpa using this

/-- **Positive collapse, quantitative form**:
`μ_{a,L}[0, ∞) ≤ κ ∫_0^∞ e^{-a e^{L+t}} dt + ε_L`. -/
theorem primeEndMeasure_univ_le {coef : ℕ → ℂ} {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C)
    (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (L : ℝ) :
    primeEndMeasure coef a L univ ≤
      ENNReal.ofReal (κ * (∫ t in Ici 0, gradeTilt a L t) + neutralDiscrepancy coef κ L) := by
  set ν : Measure ℝ := ENNReal.ofReal κ • volume
  have hD : ∀ y, 0 ≤ y → |(primeEndMeasure coef 0 L).real (Icc 0 y) - ν.real (Icc 0 y)| ≤
      neutralDiscrepancy coef κ L := fun y hy => by
    rw [measureReal_smul_volume_Icc hκ hy]
    exact abs_primeEndMeasure_zero_Icc_sub_le_discrepancy hlaw L hy
  have hqν : IntegrableOn (gradeTilt a L) (Ici 0) ν := by
    rw [IntegrableOn, Measure.restrict_smul]
    exact (integrableOn_gradeTilt ha L).smul_measure ENNReal.ofReal_ne_top
  have hprim : ∀ s u, gradeTilt a L u - gradeTilt a L s = ∫ t in s..u, gradeTiltDeriv a L t :=
    fun s u => (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_gradeTilt a L t)
      ((continuous_gradeTiltDeriv a L).intervalIntegrable s u)).symm
  obtain ⟨hint, hcmp⟩ := abs_setIntegral_Ici_sub_le (primeEndMeasure coef 0 L) ν
    (primeEndMeasure_Icc_ne_top coef 0 L) (smul_volume_Icc_ne_top κ) hD
    (fun t => (gradeTilt_pos a L t).le) (continuous_gradeTilt a L) hqν
    (integrableOn_gradeTiltDeriv ha L) hprim (tendsto_gradeTilt_atTop ha L)
  have hνint : ∫ y in Ici 0, gradeTilt a L y ∂ν = κ * ∫ y in Ici 0, gradeTilt a L y := by
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal hκ, smul_eq_mul]
  rw [hνint] at hcmp
  have hε := neutralDiscrepancy_nonneg hlaw L
  rw [primeEndMeasure_univ_eq, ← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ici).mpr (.of_forall fun t _ => (gradeTilt_pos a L t).le))]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := (abs_le.mp hcmp).2
  have h2 := integral_abs_gradeTiltDeriv_le ha L
  nlinarith

/-- **Positive collapse**: for `a > 0`, `μ_{a,L}[0, ∞) → 0`. -/
theorem tendsto_primeEndMeasure_univ_of_pos {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun L => primeEndMeasure coef a L univ) atTop (𝓝 0) := by
  have hup : Tendsto (fun L => ENNReal.ofReal (κ * (∫ t in Ici 0, gradeTilt a L t) +
      neutralDiscrepancy coef κ L)) atTop (𝓝 0) := by
    have := ((tendsto_integral_gradeTilt ha).const_mul κ).add (tendsto_neutralDiscrepancy hlaw)
    rw [mul_zero, add_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => bot_le)
    fun L => primeEndMeasure_univ_le hlaw hκ ha L

theorem primeEndMeasure_univ_ne_top {coef : ℕ → ℂ} {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C)
    (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (L : ℝ) : primeEndMeasure coef a L univ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (primeEndMeasure_univ_le hlaw hκ ha L)

/-- **Negative grade, local lower bound**: `μ_{a,L}[0, δ] ≥ X_L^{-a} μ_{0,L}[0, δ]` for `a ≤ 0`. -/
theorem primeEndMeasure_Icc_ge (coef : ℕ → ℂ) {a : ℝ} (ha : a ≤ 0) (L δ : ℝ) :
    ENNReal.ofReal (endClock L ^ (-a)) * primeEndMeasure coef 0 L (Icc 0 δ) ≤
      primeEndMeasure coef a L (Icc 0 δ) := by
  rw [primeEndMeasure_eq_setLIntegral _ _ _ measurableSet_Icc,
    primeEndMeasure_eq_setLIntegral _ _ _ measurableSet_Icc, setLIntegral_primeEndMeasure coef a L,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ))) fun y hy => ?_
  gcongr
  rw [endClock, ← Real.exp_mul, gradeTilt]
  refine Real.exp_le_exp.mpr ?_
  have : Real.exp L ≤ Real.exp (L + y) := Real.exp_le_exp.mpr (by linarith [mem_Ici.mp hy])
  nlinarith

/-- **Negative local explosion**: for `a < 0`, `κ > 0` and `δ > 0`, `μ_{a,L}[0, δ] → ∞`. -/
theorem tendsto_primeEndMeasure_Icc_of_neg {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 < κ) {a : ℝ} (ha : a < 0) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun L => primeEndMeasure coef a L (Icc 0 δ)) atTop (𝓝 ⊤) := by
  have hev : ∀ᶠ L in atTop, κ * δ / 2 ≤ (primeEndMeasure coef 0 L).real (Icc 0 δ) := by
    filter_upwards [(tendsto_neutralDiscrepancy hlaw).eventually
      (Iio_mem_nhds (show (0 : ℝ) < κ * δ / 2 by positivity))] with L hL
    have hL' : neutralDiscrepancy coef κ L < κ * δ / 2 := hL
    have := abs_primeEndMeasure_zero_Icc_sub_le_discrepancy hlaw L hδ.le
    have := (abs_le.mp (this.trans hL'.le)).1
    linarith
  have hgrow : Tendsto (fun L => endClock L ^ (-a) * (κ * δ / 2)) atTop atTop := by
    refine Tendsto.atTop_mul_const (by positivity) ?_
    have : (fun L => endClock L ^ (-a)) = fun L => Real.exp (Real.exp L * (-a)) := by
      funext L
      rw [endClock, ← Real.exp_mul]
    rw [this]
    exact Real.tendsto_exp_atTop.comp
      (Real.tendsto_exp_atTop.atTop_mul_const (by linarith))
  refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp hgrow) ?_
  filter_upwards [hev] with L hL
  refine le_trans ?_ (primeEndMeasure_Icc_ge coef ha.le L δ)
  rw [Function.comp_apply, ENNReal.ofReal_mul (Real.rpow_nonneg (endClock_pos L).le _)]
  gcongr
  rw [← ENNReal.ofReal_toReal (primeEndMeasure_Icc_ne_top coef 0 L δ), ← measureReal_def]
  exact ENNReal.ofReal_le_ofReal hL

/-! ### The operator-valued lift -/

open Classical in
/-- The finite **end window** of primes with clocks in `[0, δ]`. -/
def endWindow (L δ : ℝ) : Finset ℕ :=
  (Finset.Icc 0 ⌊endClock (L + δ)⌋₊).filter (IsEndPrime L)

theorem mem_endWindow {L δ : ℝ} {n : ℕ} :
    n ∈ endWindow L δ ↔ IsEndPrime L n ∧ Real.log (Real.log n) - L ∈ Icc 0 δ := by
  classical
  unfold endWindow
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨hp, hp.logLog_sub_pos.le, (hp.logLog_sub_le_iff δ).mpr
      ((Nat.le_floor_iff (endClock_pos _).le).mp hle)⟩
  · rintro ⟨hp, _, hS⟩
    exact ⟨Nat.le_floor ((hp.logLog_sub_le_iff δ).mp hS), hp⟩

theorem endWindow_mono (L : ℝ) {δ δ' : ℝ} (h : δ' ≤ δ) : endWindow L δ' ⊆ endWindow L δ := by
  intro n hn
  rw [mem_endWindow] at hn ⊢
  exact ⟨hn.1, hn.2.1, hn.2.2.trans h⟩

open Classical in
/-- The window mass as a finite coefficient sum. -/
theorem primeEndMeasure_Icc_eq_sum (coef : ℕ → ℂ) (a L τ δ : ℝ) :
    (primeEndMeasure coef a L).real (Icc 0 δ) =
      ∑ n ∈ endWindow L δ, ‖endPrimeCoeff coef a L τ n‖ ^ 2 := by
  rw [measureReal_def, primeEndMeasure_apply _ _ _ measurableSet_Icc,
    tsum_eq_sum (s := endWindow L δ) (fun n hn => ?_)]
  swap
  · exact if_neg fun h => hn (mem_endWindow.mpr h)
  rw [ENNReal.toReal_sum fun n _ => by
    split_ifs
    exacts [ENNReal.ofReal_ne_top, ENNReal.zero_ne_top]]
  refine Finset.sum_congr rfl fun n hn => ?_
  have h := mem_endWindow.mp hn
  rw [if_pos h, norm_endPrimeCoeff_sq, if_pos h.1, ENNReal.toReal_ofReal
    (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg h.1.pos.le _))]

namespace SobolevTranslateWindow

variable {h h' : ℝ → ℂ}

/-- The **literal Euler frame** `u_{p,a,L,τ} = λ(p) p^{-(1+a)/2} e^{-iτ log p} T_{log log p - L}
h`. -/
def endFrame (W : SobolevTranslateWindow h h') (coef : ℕ → ℂ) (a L τ : ℝ) :
    ℕ → Lp ℂ 2 (volume : Measure ℝ) :=
  translateSystem W.toL2 (endPrimeCoeff coef a L τ) (endPrimeClock L)

theorem endFrame_of_isEndPrime (W : SobolevTranslateWindow h h') (coef : ℕ → ℂ) (a τ : ℝ)
    {L : ℝ} {n : ℕ} (hn : IsEndPrime L n) :
    W.endFrame coef a L τ n =
      (coef n * (((n : ℝ) ^ (-(1 + a) / 2) : ℝ) : ℂ) *
        Complex.exp (-(((τ * Real.log n : ℝ)) : ℂ) * Complex.I)) •
        translateRight (Real.log (Real.log n) - L) W.toL2 := by
  classical
  simp only [endFrame, translateSystem, endPrimeCoeff, endPrimeClock, if_pos hn]

/-- **The quadratic frame form**: `∑_p |⟨f, u_p⟩|² = ∫_0^∞ |⟨f, T_y h⟩|² dμ_{a,L}(y)`; the
phase cancels in the quadratic form. -/
theorem setLIntegral_corrSq_primeEndMeasure (W : SobolevTranslateWindow h h') (coef : ℕ → ℂ)
    (a L τ : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫⁻ y in Ici 0, ENNReal.ofReal (W.corrSq f y) ∂primeEndMeasure coef a L =
      ∑' n, ENNReal.ofReal (‖⟪W.endFrame coef a L τ n, f⟫_ℂ‖ ^ 2) := by
  rw [← translateSystemMeasure_endPrimeCoeff coef a L τ,
    setLIntegral_Ici_translateSystemMeasure _ (endPrimeClock_nonneg L)]
  refine tsum_congr fun n => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _), endFrame, norm_inner_translateSystem_sq]
  rfl

/-- The neutral end frame is a Bessel family. -/
theorem isBesselFamily_endFrame_zero (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ}
    {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) (L τ : ℝ) :
    IsBesselFamily (W.endFrame coef 0 L τ)
      (κ * (∫ x, ‖h x‖) ^ 2 + neutralDiscrepancy coef κ L * (2 * ((∫ x, ‖h x‖) * ∫ x, ‖h' x‖))) :=
  W.isBesselFamily_translateSystem _ (endPrimeClock_nonneg L)
    (fun R => by
      rw [translateSystemMeasure_endPrimeCoeff]
      exact primeEndMeasure_Icc_ne_top coef 0 L R) hκ
    (fun y hy => by
      rw [translateSystemMeasure_endPrimeCoeff]
      exact abs_primeEndMeasure_zero_Icc_sub_le_discrepancy hlaw L hy)

/-- The **neutral frame operator** `A_{0,L} = S_{0,L,τ} S_{0,L,τ}*`. -/
def neutralEndFrameOp (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) (L τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  besselFrameOp _ (W.isBesselFamily_endFrame_zero hlaw hκ L τ)

/-- **The neutral Haar tangent bound**: `‖A_{0,L} - κ A_H‖ ≤ 2 ε_L ‖h‖₁ ‖h'‖₁`. -/
theorem norm_neutralEndFrameOp_sub_le (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ}
    {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) (L τ : ℝ) :
    ‖W.neutralEndFrameOp hlaw hκ L τ - (κ : ℂ) • W.haarFrameOp‖ ≤
      neutralDiscrepancy coef κ L * (2 * ((∫ x, ‖h x‖) * ∫ x, ‖h' x‖)) :=
  W.norm_besselFrameOp_translateSystem_sub_le _ (endPrimeClock_nonneg L)
    (fun R => by
      rw [translateSystemMeasure_endPrimeCoeff]
      exact primeEndMeasure_Icc_ne_top coef 0 L R) hκ
    (fun y hy => by
      rw [translateSystemMeasure_endPrimeCoeff]
      exact abs_primeEndMeasure_zero_Icc_sub_le_discrepancy hlaw L hy) _

/-- **Operator-norm convergence to the Haar tangent**: `A_{0,L} → κ A_H`. -/
theorem tendsto_neutralEndFrameOp (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ}
    {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) (τ : ℝ) :
    Tendsto (fun L => ‖W.neutralEndFrameOp hlaw hκ L τ - (κ : ℂ) • W.haarFrameOp‖) atTop
      (𝓝 0) := by
  have hup := (tendsto_neutralDiscrepancy hlaw).mul_const (2 * ((∫ x, ‖h x‖) * ∫ x, ‖h' x‖))
  rw [zero_mul] at hup
  exact squeeze_zero (fun _ => norm_nonneg _) (fun L => W.norm_neutralEndFrameOp_sub_le hlaw hκ L τ)
    hup

theorem norm_endFrame_sq (W : SobolevTranslateWindow h h') (coef : ℕ → ℂ) (a L τ : ℝ) (n : ℕ) :
    ‖W.endFrame coef a L τ n‖ ^ 2 = ‖endPrimeCoeff coef a L τ n‖ ^ 2 * ‖W.toL2‖ ^ 2 := by
  rw [endFrame, translateSystem, norm_smul, norm_translateRight, mul_pow]

/-- At positive grade the end frame is square-summable, with `∑ ‖u_p‖² = ‖h‖₂² μ_{a,L}[0, ∞)`. -/
theorem hasSum_norm_endFrame_sq (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (L τ : ℝ) :
    HasSum (fun n => ‖W.endFrame coef a L τ n‖ ^ 2)
      (‖W.toL2‖ ^ 2 * (primeEndMeasure coef a L).real univ) := by
  have huniv : primeEndMeasure coef a L univ =
      ∑' n, ENNReal.ofReal (‖endPrimeCoeff coef a L τ n‖ ^ 2) := by
    rw [← translateSystemMeasure_endPrimeCoeff coef a L τ,
      translateSystemMeasure_apply _ _ MeasurableSet.univ]
    simp
  have hfin := primeEndMeasure_univ_ne_top hlaw hκ ha L
  have hsum : HasSum (fun n => ‖endPrimeCoeff coef a L τ n‖ ^ 2)
      ((primeEndMeasure coef a L).real univ) := by
    rw [huniv] at hfin
    have h1 := (ENNReal.summable_toReal hfin).hasSum
    rw [measureReal_def, huniv, ENNReal.tsum_toReal_eq fun n => ENNReal.ofReal_ne_top]
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using h1
  simp_rw [W.norm_endFrame_sq, mul_comm _ (‖W.toL2‖ ^ 2)]
  exact hsum.mul_left _

/-- The **positive-grade frame operator** `A_{a,L} = ∑_p |u_p⟩⟨u_p|`. -/
def positiveEndFrameOp (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (L τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  besselFrameOp _
    (isBesselFamily_of_summable_sq (W.hasSum_norm_endFrame_sq hlaw hκ ha L τ).summable)

/-- **Positive collapse in trace norm**: `A_{a,L}` is trace class with
`‖A_{a,L}‖₁ ≤ ‖h‖₂² μ_{a,L}[0, ∞) → 0`. -/
theorem positiveEndFrameOp_traceClass (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ}
    {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (L τ : ℝ) :
    _root_.RHTower.MemSchattenClass 1 (W.positiveEndFrameOp hlaw hκ ha L τ) ∧
      _root_.RHTower.traceNorm _ (W.positiveEndFrameOp hlaw hκ ha L τ) ≤
        ‖W.toL2‖ ^ 2 * (primeEndMeasure coef a L).real univ := by
  have hs := W.hasSum_norm_endFrame_sq hlaw hκ ha L τ
  obtain ⟨h1, h2⟩ := traceNorm_besselFrameOp_le
    (isBesselFamily_of_summable_sq hs.summable) hs.summable
  exact ⟨h1, h2.trans (le_of_eq hs.tsum_eq)⟩

theorem tendsto_traceNorm_positiveEndFrameOp (W : SobolevTranslateWindow h h') {coef : ℕ → ℂ}
    {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    Tendsto (fun L => _root_.RHTower.traceNorm _ (W.positiveEndFrameOp hlaw hκ ha L τ)) atTop
      (𝓝 0) := by
  have hμ : Tendsto (fun L => (primeEndMeasure coef a L).real univ) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_primeEndMeasure_univ_of_pos hlaw hκ ha)
    simp only [Function.comp_def, ENNReal.toReal_zero] at this
    simpa [measureReal_def] using this
  have hup := hμ.const_mul (‖W.toL2‖ ^ 2)
  rw [mul_zero] at hup
  exact squeeze_zero (fun L => _root_.RHTower.traceNorm_nonneg _)
    (fun L => (W.positiveEndFrameOp_traceClass hlaw hκ ha L τ).2) hup

/-- The **end-window frame operator** `∑_{log log p - L ∈ [0, δ]} |u_p⟩⟨u_p|`. -/
def endWindowFrameOp (W : SobolevTranslateWindow h h') (coef : ℕ → ℂ) (a L τ δ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ n ∈ endWindow L δ, InnerProductSpace.rankOne ℂ (W.endFrame coef a L τ n)
    (W.endFrame coef a L τ n)

/-- **Negative local explosion of the operator**: for `a < 0` the frame operator of the clocks in
any fixed end window `[0, δ]` has norm tending to infinity. -/
theorem tendsto_norm_endWindowFrameOp (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0)
    {coef : ℕ → ℂ} {κ C : ℝ} (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 < κ) {a : ℝ}
    (ha : a < 0) (τ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun L => ‖W.endWindowFrameOp coef a L τ δ‖) atTop atTop := by
  obtain ⟨δ₀, hδ₀, hwin⟩ := W.exists_window_norm_ge (ι := ℕ) hw
  set δ' := min δ δ₀
  have hδ' : 0 < δ' := lt_min hδ hδ₀
  have hlow : ∀ L, ‖W.toL2‖ ^ 2 / 2 * (primeEndMeasure coef a L).real (Icc 0 δ') ≤
      ‖W.endWindowFrameOp coef a L τ δ‖ := by
    intro L
    rw [primeEndMeasure_Icc_eq_sum coef a L τ δ']
    refine hwin (endWindow L δ) (endWindow L δ') (endWindow_mono L (min_le_left _ _)) _ _
      fun n hn => ?_
    have hm := mem_endWindow.mp hn
    classical
    simp only [endPrimeClock, if_pos hm.1]
    exact ⟨hm.2.1, hm.2.2.trans (min_le_right _ _)⟩
  have hreal : Tendsto (fun L => (primeEndMeasure coef a L).real (Icc 0 δ')) atTop atTop := by
    have htop := tendsto_primeEndMeasure_Icc_of_neg hlaw hκ ha hδ'
    rw [ENNReal.tendsto_nhds_top_iff_nnreal] at htop
    refine tendsto_atTop.mpr fun M => ?_
    filter_upwards [htop M.toNNReal] with L hL
    rw [measureReal_def]
    have hfin := primeEndMeasure_Icc_ne_top coef a L δ'
    have h1 := ENNReal.toReal_strict_mono hfin hL
    rw [ENNReal.coe_toReal] at h1
    exact (Real.le_coe_toNNReal M).trans h1.le
  have hpos : 0 < ‖W.toL2‖ ^ 2 / 2 := by positivity
  exact tendsto_atTop_mono hlow (hreal.const_mul_atTop hpos)

end SobolevTranslateWindow

end GaloisForLFunctions.HTGeometry
