import Mathlib
import GaloisForLFunctions.RHTower.Suzuki.SuzukiVolterraLogGradeRecurrence
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRootPortObservationGram

/-!
# Physical inverse-log grades are nuclear in the boundary-log measure

Suzuki's visible prime adjacency acts by oriented prime-power translation steps with weights
`w (p,j) = log p / p^{j/2}`.  A length-`k` word of steps carries the product of its step weights
times the universal Volterra factor `θ k ≤ 2^{-k}`, and its physical profile decays like
`L^{-(k+1/2)}` in the boundary-log coordinate.  This module proves the resulting carrier is
nuclear directly in `L²(dL)` on a tail `(L₀, ∞)`:

* the tail energy of the grade-`k` profile is exactly `L₀^{-2k} / (2k)`;
* the total word coefficient at grade `k` is exactly `θ k · M^k` for the alphabet mass `M`,
  hence at most `(M/2)^k`;
* for `L₀ > M/2` the grade-word series of `L²` norms is summable with the exact geometric bound
  `C/√2 · q/(1-q)`, `q = M/(2L₀)`, and the word profiles sum in `L²(dL)` itself;
* the trace-zero Volterra inverse of a power source `A L^{-α}` is
  `α/(2α+1) · A · L^{-α-1}` — one prime step raises the inverse-log exponent by exactly one,
  which is where the grade decay comes from.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Filter Set Fintype

/-! ## The oriented word alphabet and its coefficients -/

/-- The mass of an oriented visible alphabet: the sum of the prime-power step weights. -/
def suzukiWordMass (S : Finset ((Nat.Primes × ℕ) × Bool)) : ℝ :=
  ∑ s ∈ S, suzukiPrimePowerWeight s.1

/-- The absolute coefficient of a length-`k` word: the universal Volterra factor times the
product of the step weights. -/
def suzukiWordCoefficient (k : ℕ) (ν : Fin k → (Nat.Primes × ℕ) × Bool) : ℝ :=
  suzukiPrimeNormalGradeFactor k * ∏ i, suzukiPrimePowerWeight (ν i).1

theorem suzukiPrimePowerWeight_nonneg (pj : Nat.Primes × ℕ) :
    0 ≤ suzukiPrimePowerWeight pj := by
  rw [suzukiPrimePowerWeight]
  have hp : (1 : ℝ) ≤ ((pj.1 : ℕ) : ℝ) := by
    have h2 := pj.1.property.two_le
    exact_mod_cast le_trans (by norm_num) h2
  have hlog : 0 ≤ Real.log ((pj.1 : ℕ) : ℝ) := Real.log_nonneg hp
  have hpow : (0 : ℝ) < ((pj.1 : ℕ) : ℝ) ^ ((pj.2 : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by linarith) _
  positivity

theorem suzukiWordMass_nonneg (S : Finset ((Nat.Primes × ℕ) × Bool)) :
    0 ≤ suzukiWordMass S :=
  Finset.sum_nonneg fun s _ => suzukiPrimePowerWeight_nonneg s.1

/-- **The word sum at grade `k` is exactly the `k`-th power of the mass** — the raw sum over all
length-`k` words of the product of step weights is the multinomial expansion of `M^k`. -/
theorem sum_prod_suzukiWordWeights (S : Finset ((Nat.Primes × ℕ) × Bool)) (k : ℕ) :
    ∑ ν ∈ piFinset (fun _ : Fin k => S), ∏ i, suzukiPrimePowerWeight (ν i).1
      = suzukiWordMass S ^ k := by
  rw [suzukiWordMass, Finset.sum_pow']

/-- The total absolute word coefficient at grade `k` is exactly `θ k · M^k`. -/
theorem sum_suzukiWordCoefficient_eq (S : Finset ((Nat.Primes × ℕ) × Bool)) (k : ℕ) :
    ∑ ν ∈ piFinset (fun _ : Fin k => S), suzukiWordCoefficient k ν
      = suzukiPrimeNormalGradeFactor k * suzukiWordMass S ^ k := by
  rw [← sum_prod_suzukiWordWeights, Finset.mul_sum]
  rfl

/-- **The source-specialized grade majorant**: `θ k ≤ 2^{-k}` turns the raw mass into the
effective mass `M/2`. -/
theorem sum_suzukiWordCoefficient_le (S : Finset ((Nat.Primes × ℕ) × Bool)) (k : ℕ) :
    ∑ ν ∈ piFinset (fun _ : Fin k => S), suzukiWordCoefficient k ν
      ≤ (suzukiWordMass S / 2) ^ k := by
  rw [sum_suzukiWordCoefficient_eq, div_pow]
  have h1 := suzukiPrimeNormalGradeFactor_le_half_pow k
  have h2 : (0 : ℝ) ≤ suzukiWordMass S ^ k := pow_nonneg (suzukiWordMass_nonneg S) k
  calc suzukiPrimeNormalGradeFactor k * suzukiWordMass S ^ k
      ≤ (1 / 2) ^ k * suzukiWordMass S ^ k :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = suzukiWordMass S ^ k / 2 ^ k := by
        rw [div_pow]
        ring

theorem suzukiWordCoefficient_nonneg (k : ℕ) (ν : Fin k → (Nat.Primes × ℕ) × Bool) :
    0 ≤ suzukiWordCoefficient k ν :=
  mul_nonneg (le_of_lt (suzukiPrimeNormalGradeFactor_pos k))
    (Finset.prod_nonneg fun i _ => suzukiPrimePowerWeight_nonneg (ν i).1)

/-- **The closed central-binomial form of the Volterra factor**:
`θ k = binom(2k, k) / 8^k`.  The recursion factor `(2k+1)/(4k+4)` is exactly the central
binomial recurrence `(k+1) · binom(2k+2, k+1) = 2(2k+1) · binom(2k, k)` divided by `8`. -/
theorem suzukiPrimeNormalGradeFactor_eq_centralBinom (k : ℕ) :
    suzukiPrimeNormalGradeFactor k = (Nat.centralBinom k : ℝ) / 8 ^ k := by
  induction k with
  | zero => simp [Nat.centralBinom]
  | succ k ih =>
    rw [suzukiPrimeNormalGradeFactor_succ, ih]
    have h := Nat.succ_mul_centralBinom_succ k
    have hcast : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
        = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast h
    have h8 : (8 : ℝ) ^ k ≠ 0 := by positivity
    have hk4 : (4 : ℝ) * k + 4 ≠ 0 := by positivity
    field_simp
    push_cast
    linear_combination (-4 * (8 : ℝ) ^ k) * hcast

/-! ## The grade profile and its exact tail energy -/

/-- The grade-`k` physical profile with coefficient `c`: `c · L^{-(k+1/2)}`. -/
def suzukiGradeProfile (c : ℝ) (k : ℕ) (L : ℝ) : ℝ :=
  c * L ^ (-((k : ℝ) + 1 / 2))

theorem sq_suzukiGradeProfile_eqOn {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ) :
    ∀ L ∈ Ioi L0, suzukiGradeProfile c k L ^ 2
      = c ^ 2 * L ^ (-(2 * (k : ℝ)) - 1) := by
  intro L hL
  have hLpos : 0 < L := lt_trans hL0 hL
  rw [suzukiGradeProfile, mul_pow, ← Real.rpow_natCast (L ^ (-((k : ℝ) + 1 / 2))) 2,
    ← Real.rpow_mul hLpos.le]
  have he : (-((k : ℝ) + 1 / 2)) * ((2 : ℕ) : ℝ) = -(2 * (k : ℝ)) - 1 := by
    push_cast
    ring
  rw [he]

/-- **The exact tail energy of a grade profile** — the card's `(7)`–`(8)`:
`∫_{L₀}^∞ (c L^{-(k+1/2)})² dL = c² L₀^{-2k} / (2k)`. -/
theorem integral_sq_suzukiGradeProfile {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ)
    (hk : 1 ≤ k) :
    ∫ L in Ioi L0, suzukiGradeProfile c k L ^ 2
      = c ^ 2 * (L0 ^ (-(2 * (k : ℝ))) / (2 * k)) := by
  have hklow : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  rw [setIntegral_congr_fun measurableSet_Ioi (sq_suzukiGradeProfile_eqOn hL0 c k),
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hL0]
  have hne : -(2 * (k : ℝ)) - 1 + 1 = -(2 * (k : ℝ)) := by ring
  rw [hne]
  have hk2 : (2 * (k : ℝ)) ≠ 0 := by linarith
  field_simp

/-- The grade profile is square integrable on the tail. -/
theorem memLp_two_suzukiGradeProfile {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    MemLp (suzukiGradeProfile c k) 2 (volume.restrict (Ioi L0)) := by
  have hklow : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hmeas : AEStronglyMeasurable (suzukiGradeProfile c k)
      (volume.restrict (Ioi L0)) := by
    have hm : Measurable fun L : ℝ => c * L ^ (-((k : ℝ) + 1 / 2)) := by fun_prop
    exact hm.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hint : IntegrableOn (fun L : ℝ => c ^ 2 * L ^ (-(2 * (k : ℝ)) - 1)) (Ioi L0) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hL0).const_mul _
  exact (integrable_congr
    ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun L hL =>
        (sq_suzukiGradeProfile_eqOn hL0 c k L hL).symm))).mp hint

/-! ## The trace-zero Volterra inverse of a power source -/

/-- **The exact Volterra inverse** — the card's `(13)`: for the differentiated power source
`Φ' = -α A t^{-α-1}`, the trace-zero inverse `-1/(2√L) ∫_L^∞ Φ'(t)/√t dt` is exactly
`α/(2α+1) · A · L^{-α-1}`.  One prime step raises the inverse-log exponent by exactly one. -/
theorem suzukiVolterraInverse_integral {α A L : ℝ} (hα : 0 < α) (hL : 0 < L) :
    (-1 / (2 * Real.sqrt L))
        * ∫ t in Ioi L, (-α * A * t ^ (-α - 1)) / Real.sqrt t
      = α / (2 * α + 1) * A * L ^ (-α - 1) := by
  have hcongr : ∀ t ∈ Ioi L, (-α * A * t ^ (-α - 1)) / Real.sqrt t
      = (-α * A) * t ^ (-α - 1 - 1 / 2) := by
    intro t ht
    have htpos : 0 < t := lt_trans hL ht
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg htpos.le,
      mul_assoc, ← Real.rpow_add htpos]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hL]
  have he : -α - 1 - 1 / 2 + 1 = -α - 1 / 2 := by ring
  rw [he, Real.sqrt_eq_rpow]
  have hLhalf : (0 : ℝ) < L ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hL _
  have hsplit : L ^ (-α - 1 / 2) = L ^ (-α - 1) * L ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hL]
    ring_nf
  rw [hsplit]
  have hden : (2 : ℝ) * α + 1 ≠ 0 := by linarith
  have hhalf : -α - 1 / 2 ≠ 0 := by linarith
  have hne : (-1 - α * 2 : ℝ) ≠ 0 := by intro h; exact hden (by linarith)
  field_simp
  linear_combination A * mul_inv_cancel₀ hne

/-! ## The `L²` element of a grade profile and its exact norm -/

/-- The `L²(dL)` element of a grade profile on the tail. -/
def suzukiGradeProfileLp {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Lp ℝ 2 (volume.restrict (Ioi L0)) :=
  (memLp_two_suzukiGradeProfile hL0 c k hk).toLp _

/-- The squared norm of the grade profile element is its exact tail energy. -/
theorem norm_sq_suzukiGradeProfileLp {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ‖suzukiGradeProfileLp hL0 c k hk‖ ^ 2
      = c ^ 2 * (L0 ^ (-(2 * (k : ℝ))) / (2 * k)) := by
  have hip : inner ℝ (suzukiGradeProfileLp hL0 c k hk) (suzukiGradeProfileLp hL0 c k hk)
      = ∫ L in Ioi L0, suzukiGradeProfile c k L ^ 2 := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_two_suzukiGradeProfile hL0 c k hk).coeFn_toLp] with L hLfn
    rw [suzukiGradeProfileLp] at *
    rw [hLfn]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  rw [← real_inner_self_eq_norm_sq, hip, integral_sq_suzukiGradeProfile hL0 c k hk]

/-- **The exact `L²` norm of a grade profile** — `|c| · L₀^{-k} / √(2k)`. -/
theorem norm_suzukiGradeProfileLp {L0 : ℝ} (hL0 : 0 < L0) (c : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ‖suzukiGradeProfileLp hL0 c k hk‖
      = |c| * L0 ^ (-(k : ℝ)) / Real.sqrt (2 * k) := by
  have hsq := norm_sq_suzukiGradeProfileLp hL0 c k hk
  have hnn : 0 ≤ ‖suzukiGradeProfileLp hL0 c k hk‖ := norm_nonneg _
  have hrew : L0 ^ (-(2 * (k : ℝ))) = (L0 ^ (-(k : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast (L0 ^ (-(k : ℝ))) 2, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  calc ‖suzukiGradeProfileLp hL0 c k hk‖
      = Real.sqrt (‖suzukiGradeProfileLp hL0 c k hk‖ ^ 2) := by
        rw [Real.sqrt_sq hnn]
    _ = Real.sqrt (c ^ 2 * ((L0 ^ (-(k : ℝ))) ^ 2 / (2 * k))) := by
        rw [hsq, hrew]
    _ = |c| * L0 ^ (-(k : ℝ)) / Real.sqrt (2 * k) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
          Real.sqrt_div (sq_nonneg (L0 ^ (-(k : ℝ)))),
          Real.sqrt_sq (Real.rpow_nonneg hL0.le _), mul_div_assoc]

/-- The `L²` norm of a nonnegative-coefficient grade profile is at most
`c · L₀^{-k} / √2`. -/
theorem norm_suzukiGradeProfileLp_le {L0 : ℝ} (hL0 : 0 < L0) {c : ℝ} (hc : 0 ≤ c)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖suzukiGradeProfileLp hL0 c k hk‖
      ≤ c * L0 ^ (-(k : ℝ)) / Real.sqrt 2 := by
  rw [norm_suzukiGradeProfileLp hL0 c k hk, abs_of_nonneg hc]
  have hklow : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hnum : 0 ≤ c * L0 ^ (-(k : ℝ)) :=
    mul_nonneg hc (Real.rpow_nonneg hL0.le _)
  have hsqrt : Real.sqrt 2 ≤ Real.sqrt (2 * k) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hpos : 0 < Real.sqrt 2 := by positivity
  exact div_le_div_of_nonneg_left hnum hpos hsqrt

/-! ## The nuclear grade-word series -/

/-- The subtype form of the grade coefficient sum: summing over all words drawn from the
alphabet `S` gives exactly `θ k · M^k`. -/
theorem sum_suzukiWordCoefficient_subtype (S : Finset ((Nat.Primes × ℕ) × Bool)) (k : ℕ) :
    ∑ ν : Fin k → S,
        suzukiWordCoefficient k (fun i => ((ν i : (Nat.Primes × ℕ) × Bool)))
      = suzukiPrimeNormalGradeFactor k * suzukiWordMass S ^ k := by
  have hmass : ∑ s : S, suzukiPrimePowerWeight ((s : (Nat.Primes × ℕ) × Bool)).1
      = suzukiWordMass S := by
    rw [suzukiWordMass]
    exact Finset.sum_coe_sort S fun x => suzukiPrimePowerWeight x.1
  have h1 : ∑ ν : Fin k → S,
      ∏ i, suzukiPrimePowerWeight ((ν i : (Nat.Primes × ℕ) × Bool)).1
        = (∑ s : S, suzukiPrimePowerWeight ((s : (Nat.Primes × ℕ) × Bool)).1) ^ k := by
    rw [Finset.sum_pow' Finset.univ
      (fun s : S => suzukiPrimePowerWeight ((s : (Nat.Primes × ℕ) × Bool)).1) k,
      Fintype.piFinset_univ]
  simp only [suzukiWordCoefficient, ← Finset.mul_sum, h1, hmass]

theorem sum_suzukiWordCoefficient_subtype_le (S : Finset ((Nat.Primes × ℕ) × Bool)) (k : ℕ) :
    ∑ ν : Fin k → S,
        suzukiWordCoefficient k (fun i => ((ν i : (Nat.Primes × ℕ) × Bool)))
      ≤ (suzukiWordMass S / 2) ^ k := by
  rw [sum_suzukiWordCoefficient_subtype, div_pow]
  have h1 := suzukiPrimeNormalGradeFactor_le_half_pow k
  have h2 : (0 : ℝ) ≤ suzukiWordMass S ^ k := pow_nonneg (suzukiWordMass_nonneg S) k
  calc suzukiPrimeNormalGradeFactor k * suzukiWordMass S ^ k
      ≤ (1 / 2) ^ k * suzukiWordMass S ^ k := mul_le_mul_of_nonneg_right h1 h2
    _ = suzukiWordMass S ^ k / 2 ^ k := by
        rw [div_pow]
        ring

/-- The fiber norm sum at grade `k+1` is at most the geometric term `C/√2 · q^{k+1}`,
`q = M/(2L₀)`. -/
theorem sum_norm_suzukiWordProfileLp_le (S : Finset ((Nat.Primes × ℕ) × Bool))
    {L0 C : ℝ} (hL0 : 0 < L0) (hC : 0 ≤ C) (k : ℕ) :
    ∑ ν : Fin (k + 1) → S,
        ‖suzukiGradeProfileLp hL0
            (C * suzukiWordCoefficient (k + 1)
              (fun i => ((ν i : (Nat.Primes × ℕ) × Bool))))
            (k + 1) (Nat.le_add_left 1 k)‖
      ≤ C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1) := by
  have hstep : ∀ ν : Fin (k + 1) → S,
      ‖suzukiGradeProfileLp hL0
          (C * suzukiWordCoefficient (k + 1)
            (fun i => ((ν i : (Nat.Primes × ℕ) × Bool))))
          (k + 1) (Nat.le_add_left 1 k)‖
        ≤ C * suzukiWordCoefficient (k + 1)
            (fun i => ((ν i : (Nat.Primes × ℕ) × Bool)))
            * L0 ^ (-((k + 1 : ℕ) : ℝ)) / Real.sqrt 2 := fun ν =>
    norm_suzukiGradeProfileLp_le hL0
      (mul_nonneg hC (suzukiWordCoefficient_nonneg _ _)) (k + 1) (Nat.le_add_left 1 k)
  calc ∑ ν : Fin (k + 1) → S,
      ‖suzukiGradeProfileLp hL0
          (C * suzukiWordCoefficient (k + 1)
            (fun i => ((ν i : (Nat.Primes × ℕ) × Bool))))
          (k + 1) (Nat.le_add_left 1 k)‖
      ≤ ∑ ν : Fin (k + 1) → S,
          C * suzukiWordCoefficient (k + 1)
              (fun i => ((ν i : (Nat.Primes × ℕ) × Bool)))
            * L0 ^ (-((k + 1 : ℕ) : ℝ)) / Real.sqrt 2 :=
        Finset.sum_le_sum fun ν _ => hstep ν
    _ = (∑ ν : Fin (k + 1) → S,
          suzukiWordCoefficient (k + 1)
            (fun i => ((ν i : (Nat.Primes × ℕ) × Bool))))
          * (C * L0 ^ (-((k + 1 : ℕ) : ℝ)) / Real.sqrt 2) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring
    _ ≤ (suzukiWordMass S / 2) ^ (k + 1)
          * (C * L0 ^ (-((k + 1 : ℕ) : ℝ)) / Real.sqrt 2) :=
        mul_le_mul_of_nonneg_right (sum_suzukiWordCoefficient_subtype_le S (k + 1))
          (div_nonneg (mul_nonneg hC (Real.rpow_nonneg hL0.le _)) (Real.sqrt_nonneg 2))
    _ = C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1) := by
        rw [div_pow (suzukiWordMass S / 2) L0 (k + 1),
          Real.rpow_neg hL0.le, Real.rpow_natCast]
        have h1 : (L0 : ℝ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hL0)
        have h2 : Real.sqrt 2 ≠ 0 := by positivity
        field_simp

/-- **The physical grade-word carrier is nuclear in `L²(dL)`** — the summability half of the
card's `(4)`: for `L₀ > M/2` the norm series over all positive grades and all words is
summable. -/
theorem summable_norm_suzukiWordProfileLp (S : Finset ((Nat.Primes × ℕ) × Bool))
    {L0 C : ℝ} (hL0 : 0 < L0) (hC : 0 ≤ C) (hth : suzukiWordMass S / 2 < L0) :
    Summable (fun kν : Σ _k : ℕ, (Fin (_k + 1) → S) =>
      ‖suzukiGradeProfileLp hL0
          (C * suzukiWordCoefficient (kν.1 + 1)
            (fun i => ((kν.2 i : (Nat.Primes × ℕ) × Bool))))
          (kν.1 + 1) (Nat.le_add_left 1 kν.1)‖) := by
  have hq0 : 0 ≤ suzukiWordMass S / 2 / L0 :=
    div_nonneg (div_nonneg (suzukiWordMass_nonneg S) (by norm_num)) hL0.le
  have hq1 : suzukiWordMass S / 2 / L0 < 1 := (div_lt_one hL0).mpr hth
  rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  have hgeo : Summable
      (fun k : ℕ => C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1)) := by
    refine ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0))).congr fun k => ?_
    rw [pow_succ]
    ring
  refine Summable.of_nonneg_of_le (fun k => tsum_nonneg fun ν => norm_nonneg _)
    (fun k => ?_) hgeo
  rw [tsum_fintype]
  exact sum_norm_suzukiWordProfileLp_le S hL0 hC k

/-- **The exact geometric bound** — the card's `(4)`:
`∑_{k≥1} ∑_ν ‖F_{k,ν}‖ ≤ C/√2 · q/(1-q)` at `q = M/(2L₀) < 1`. -/
theorem tsum_norm_suzukiWordProfileLp_le (S : Finset ((Nat.Primes × ℕ) × Bool))
    {L0 C : ℝ} (hL0 : 0 < L0) (hC : 0 ≤ C) (hth : suzukiWordMass S / 2 < L0) :
    (∑' kν : Σ _k : ℕ, (Fin (_k + 1) → S),
      ‖suzukiGradeProfileLp hL0
          (C * suzukiWordCoefficient (kν.1 + 1)
            (fun i => ((kν.2 i : (Nat.Primes × ℕ) × Bool))))
          (kν.1 + 1) (Nat.le_add_left 1 kν.1)‖)
      ≤ C / Real.sqrt 2
          * (suzukiWordMass S / 2 / L0 / (1 - suzukiWordMass S / 2 / L0)) := by
  have hq0 : 0 ≤ suzukiWordMass S / 2 / L0 :=
    div_nonneg (div_nonneg (suzukiWordMass_nonneg S) (by norm_num)) hL0.le
  have hq1 : suzukiWordMass S / 2 / L0 < 1 := (div_lt_one hL0).mpr hth
  have hsum := summable_norm_suzukiWordProfileLp S hL0 hC hth
  have hpair := (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hsum
  have hgeo : Summable
      (fun k : ℕ => C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1)) := by
    refine ((summable_geometric_of_lt_one hq0 hq1).mul_left
      (C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0))).congr fun k => ?_
    rw [pow_succ]
    ring
  rw [Summable.tsum_sigma hsum]
  have hle := Summable.tsum_mono (f := fun k : ℕ =>
      ∑' ν : Fin (k + 1) → S,
        ‖suzukiGradeProfileLp hL0
            (C * suzukiWordCoefficient (k + 1)
              (fun i => ((ν i : (Nat.Primes × ℕ) × Bool))))
            (k + 1) (Nat.le_add_left 1 k)‖)
    hpair.2 hgeo (Pi.le_def.mpr fun k => by
      rw [tsum_fintype]
      exact sum_norm_suzukiWordProfileLp_le S hL0 hC k)
  refine le_trans hle ?_
  have hval : (∑' k : ℕ,
      C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1))
        = C / Real.sqrt 2
          * (suzukiWordMass S / 2 / L0 / (1 - suzukiWordMass S / 2 / L0)) := by
    have hrw : ∀ k : ℕ, C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0) ^ (k + 1)
        = C / Real.sqrt 2 * (suzukiWordMass S / 2 / L0)
            * (suzukiWordMass S / 2 / L0) ^ k := fun k => by
      rw [pow_succ]
      ring
    simp_rw [hrw]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv,
      div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact le_of_eq hval

/-- **The carrier sums in `L²(dL)` itself** — the card's `(5)`: absolute summability of the
grade-word profiles in the physical Hilbert space. -/
theorem summable_suzukiWordProfileLp (S : Finset ((Nat.Primes × ℕ) × Bool))
    {L0 C : ℝ} (hL0 : 0 < L0) (hC : 0 ≤ C) (hth : suzukiWordMass S / 2 < L0) :
    Summable (fun kν : Σ _k : ℕ, (Fin (_k + 1) → S) =>
      suzukiGradeProfileLp hL0
        (C * suzukiWordCoefficient (kν.1 + 1)
          (fun i => ((kν.2 i : (Nat.Primes × ℕ) × Bool))))
        (kν.1 + 1) (Nat.le_add_left 1 kν.1)) :=
  Summable.of_norm (summable_norm_suzukiWordProfileLp S hL0 hC hth)

end GaloisForLFunctions.RHTower
