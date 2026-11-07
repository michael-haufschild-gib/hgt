import GaloisForLFunctions.ArithmeticScatteringHolography.TheRegularSolution

/-!
# The exact ringdown of a pulse

The discrete wave equation on the black hole is `u(τ+1) + q u(τ-1) = A u(τ)`. On a ray it has the
d'Alembert solution `F(τ + k) + q^k G(τ - k)`: `F` runs in along the ray and `G` runs out.

Send one unit pulse down every cusp at time zero. The whole field is then explicit (`pulse_isWave`). With
`d_m` the complete homogeneous symmetric polynomial of `q², α, β`, where `α + β = t`, `αβ = q`, the
reflected signal is

  `G(2) = q`,  `G(2m) = q(q-1)h (d_{m-2} + q d_{m-3})`,

and it is zero at odd times and before time 2. So the echo train is the prompt bounce followed by the
response of the core, which carries the factor `h`. Three parts of the physics are exact here.

* **No remainder.** `d_m` is a finite sum of `a^{m+2}/Π(a - a')` over the three roots (`coreSeq_eq_modes`).
  The ground mode is removed by the causal probe `1 - q²w`, and what remains obeys the two-term recurrence
  `R_{n+2} = t R_{n+1} - q R_n` (`ringSignal_add_two`).
* **The minus branch rings.** At a resonance the eigenfunction with time factor `X^τ` is purely outgoing.
* **The plus branch is silent.** The same eigenfunction with time factor `Y^τ` is purely incoming: it is
  the time reversal of the ringdown, a wave absorbed with no reflection (`plusBranch_isIncoming`). This is
  `S(X) S(Y) = 1`, so the pole of `S` at `X` is a zero at `Y`, and it holds whatever the position of the
  resonance.

Each mode at `X² = a` decays by `|a|^{1/2} q^{-1/2}` per tick. Functional-equation partners `a`, `q/a` have
rates summing to `½` in units of `log q` (`dampingRate_add_partner`), and the two rates agree exactly when
`|a|² = q`.
-/

open Finset

noncomputable section

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.ArithmeticScatteringHolography

variable {G D : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] [Fintype D]

/-- The discrete wave equation on the black hole. -/
def IsWave (q : ℕ) (u : ℤ → Vertex G D → ℂ) : Prop :=
  ∀ τ v, u (τ + 1) v + (q : ℂ) * u (τ + (-1)) v = waveOp q (u τ) v

/-- The response of the core, in the double-tick index: `d_m`, the coefficient of `w^m` in
`1/((1 - q²w)(1 - tw + qw²))`. -/
def coreSeq (q t : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => q ^ 2 + t
  | 2 => (q ^ 2 + t) * (q ^ 2 + t) - (q + q ^ 2 * t)
  | n + 3 => (q ^ 2 + t) * coreSeq q t (n + 2) - (q + q ^ 2 * t) * coreSeq q t (n + 1) +
      q ^ 3 * coreSeq q t n

theorem coreSeq_add_three (q t : ℂ) (n : ℕ) :
    coreSeq q t (n + 3) = (q ^ 2 + t) * coreSeq q t (n + 2) - (q + q ^ 2 * t) * coreSeq q t (n + 1) +
      q ^ 3 * coreSeq q t n := by
  rw [coreSeq]

/-- `d_m` extended by zero to negative indices. -/
def coreZ (q t : ℂ) (m : ℤ) : ℂ := if m < 0 then 0 else coreSeq q t m.toNat

theorem coreZ_natCast (q t : ℂ) (n : ℕ) : coreZ q t n = coreSeq q t n := by
  simp [coreZ]

theorem coreZ_of_neg (q t : ℂ) {m : ℤ} (hm : m < 0) : coreZ q t m = 0 := by
  simp [coreZ, hm]

/-- The Kronecker delta in time. -/
def delta (τ : ℤ) : ℂ := if τ = 0 then 1 else 0

theorem coreZ_recurrence (q t : ℂ) (m : ℤ) :
    coreZ q t m - (q ^ 2 + t) * coreZ q t (m + (-1)) + (q + q ^ 2 * t) * coreZ q t (m + (-2)) -
      q ^ 3 * coreZ q t (m + (-3)) = delta m := by
  rcases lt_or_ge m 0 with hm | hm
  · have hne : m ≠ 0 := by omega
    rw [coreZ_of_neg q t hm, coreZ_of_neg q t (by omega), coreZ_of_neg q t (by omega),
      coreZ_of_neg q t (by omega)]
    simp [delta, hne]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have neg1 : coreZ q t (-1) = 0 := coreZ_of_neg q t (by norm_num)
    have neg2 : coreZ q t (-2) = 0 := coreZ_of_neg q t (by norm_num)
    have neg3 : coreZ q t (-3) = 0 := coreZ_of_neg q t (by norm_num)
    match n with
    | 0 =>
      rw [show ((0 : ℕ) : ℤ) + (-1) = -1 by norm_num, show ((0 : ℕ) : ℤ) + (-2) = -2 by norm_num,
        show ((0 : ℕ) : ℤ) + (-3) = -3 by norm_num, neg1, neg2, neg3, coreZ_natCast]
      simp [delta, coreSeq]
    | 1 =>
      rw [show ((1 : ℕ) : ℤ) + (-1) = ((0 : ℕ) : ℤ) by norm_num,
        show ((1 : ℕ) : ℤ) + (-2) = -1 by norm_num, show ((1 : ℕ) : ℤ) + (-3) = -2 by norm_num,
        neg1, neg2, coreZ_natCast, coreZ_natCast]
      simp [delta, coreSeq]
    | 2 =>
      rw [show ((2 : ℕ) : ℤ) + (-1) = ((1 : ℕ) : ℤ) by norm_num,
        show ((2 : ℕ) : ℤ) + (-2) = ((0 : ℕ) : ℤ) by norm_num,
        show ((2 : ℕ) : ℤ) + (-3) = -1 by norm_num, neg1, coreZ_natCast, coreZ_natCast,
        coreZ_natCast]
      simp [delta, coreSeq]
    | k + 3 =>
      rw [show ((k + 3 : ℕ) : ℤ) + (-1) = ((k + 2 : ℕ) : ℤ) by push_cast; ring,
        show ((k + 3 : ℕ) : ℤ) + (-2) = ((k + 1 : ℕ) : ℤ) by push_cast; ring,
        show ((k + 3 : ℕ) : ℤ) + (-3) = ((k : ℕ) : ℤ) by push_cast; ring, coreZ_natCast,
        coreZ_natCast, coreZ_natCast, coreZ_natCast, coreSeq_add_three]
      have hne : ((k + 3 : ℕ) : ℤ) ≠ 0 := by positivity
      simp only [delta, hne, if_false]
      ring

/-- The core response in time: supported on even times `τ ≥ 0`. -/
def coreTime (q t : ℂ) (τ : ℤ) : ℂ := if Even τ then coreZ q t (τ / 2) else 0

theorem coreTime_two_mul (q t : ℂ) (m : ℤ) : coreTime q t (2 * m) = coreZ q t m := by
  simp [coreTime]

theorem coreTime_of_not_even (q t : ℂ) {τ : ℤ} (h : ¬ Even τ) : coreTime q t τ = 0 := by
  simp [coreTime, h]

/-- **The recurrence of the core response in time.** -/
theorem coreTime_recurrence (q t : ℂ) (τ : ℤ) :
    coreTime q t τ - (q ^ 2 + t) * coreTime q t (τ + (-2)) +
        (q + q ^ 2 * t) * coreTime q t (τ + (-4)) - q ^ 3 * coreTime q t (τ + (-6)) = delta τ := by
  rcases Int.even_or_odd τ with ⟨r, rfl⟩ | hodd
  · have e0 : r + r = 2 * r := by ring
    have e2 : r + r + (-2) = 2 * (r + (-1)) := by ring
    have e4 : r + r + (-4) = 2 * (r + (-2)) := by ring
    have e6 : r + r + (-6) = 2 * (r + (-3)) := by ring
    rw [e2, e4, e6, e0, coreTime_two_mul, coreTime_two_mul, coreTime_two_mul, coreTime_two_mul,
      coreZ_recurrence]
    simp [delta]
  · have hne : τ ≠ 0 := by
      rintro rfl
      exact absurd hodd (by decide)
    have hn (k : ℤ) (hk : Even k) : ¬ Even (τ + k) := by
      rw [Int.even_add]
      simp [hk, Int.not_even_iff_odd.mpr hodd]
    rw [coreTime_of_not_even q t (Int.not_even_iff_odd.mpr hodd),
      coreTime_of_not_even q t (hn _ (by decide)), coreTime_of_not_even q t (hn _ (by decide)),
      coreTime_of_not_even q t (hn _ (by decide))]
    simp [delta, hne]

/-- The reflected signal of one pulse on each cusp: the prompt bounce plus the response of the core. -/
def reflected (q t h : ℂ) (τ : ℤ) : ℂ :=
  q * delta (τ + (-2)) +
    q * (q - 1) * h * (coreTime q t (τ + (-4)) + q * coreTime q t (τ + (-6)))

/-- The pulse field at time `τ` as radial data. -/
def pulseData (q t h : ℂ) (τ : ℤ) : RadialData where
  core := h * (coreTime q t (τ + (-2)) - q ^ 2 * coreTime q t (τ + (-6)))
  dead := (q + 1) * h * (coreTime q t (τ + (-3)) - q * coreTime q t (τ + (-5)))
  neck := 2 * delta (τ + (-1)) +
    (q - 1) * h * (coreTime q t (τ + (-3)) + q * coreTime q t (τ + (-5)))
  pin := delta (τ + (-1)) + q * h * (coreTime q t (τ + (-3)) - coreTime q t (τ + (-5)))
  cap := (q + 1) * (delta (τ + (-1)) + q * (q - 1) * h * coreTime q t (τ + (-5)))
  ray k := delta (τ + k) + q ^ k * reflected q t h (τ - k)

/-- The field of one unit pulse sent down every cusp at time zero. -/
def Channels.pulse (B : Channels G D) (τ : ℤ) : Vertex G D → ℂ :=
  (pulseData (B.q : ℂ) B.trace (cuspCount G) τ).toFun

/-- **The pulse is an exact solution of the wave equation** on the whole graph. -/
theorem Channels.pulse_isWave (B : Channels G D) : IsWave B.q B.pulse := by
  intro τ v
  have hh := B.cuspCount_eq
  have hcount := B.count_complex
  have hq1 := B.q_sub_one_ne_zero
  have e (a b : ℤ) : τ + a + b = τ + (a + b) := add_assoc _ _ _
  unfold Channels.pulse
  rcases v with _ | d | x | L | ⟨P, _ | k⟩
  · rw [waveOp_toFun_core]
    simp only [pulseData, RadialData.toFun_core, e, Int.reduceAdd, Int.reduceNeg]
    have hrec := coreTime_recurrence (B.q : ℂ) B.trace (τ + (-1))
    simp only [e, Int.reduceAdd, Int.reduceNeg] at hrec
    linear_combination cuspCount G * hrec +
      cuspCount G * (-(((B.q : ℂ) + 1) / 2) * coreTime (B.q : ℂ) B.trace (τ + (-3)) +
        ((B.q : ℂ) * ((B.q : ℂ) + 1) / 2) * coreTime (B.q : ℂ) B.trace (τ + (-5))) * hcount +
      cuspCount G * (coreTime (B.q : ℂ) B.trace (τ + (-3)) -
        (B.q : ℂ) ^ 2 * coreTime (B.q : ℂ) B.trace (τ + (-5))) * hh
  · simp only [waveOp_dead, pulseData, RadialData.toFun_core, RadialData.toFun_dead, e, Int.reduceAdd,
      Int.reduceNeg]
    ring
  · induction x using Quotient.inductionOn with
    | h P =>
      change RadialData.toFun _ (.neck (Branch.mk P)) + _ * RadialData.toFun _ (.neck (Branch.mk P)) =
        waveOp B.q _ (.neck (Branch.mk P))
      rw [waveOp_neck]
      unfold neckOp
      simp only [RadialData.toFun_core, RadialData.toFun_ray, RadialData.toFun_neck, pulseData, e,
        Int.reduceAdd, Int.reduceNeg]
      simp only [reflected, CharP.cast_eq_zero, add_zero, sub_zero, pow_zero, one_mul,
        Int.reduceNeg]
      split_ifs <;> ring
  · simp only [waveOp_cap, pulseData, RadialData.toFun_cap, RadialData.toFun_ray, e, Int.reduceAdd,
      Int.reduceNeg]
    simp only [reflected, CharP.cast_eq_zero, add_zero, sub_zero, pow_zero, one_mul, Int.reduceNeg]
    ring
  · rw [waveOp_ray_zero]
    unfold gapOp
    simp only [RadialData.toFun_neck, RadialData.toFun_ray, pulseData, e, Int.reduceAdd, Int.reduceNeg]
    have e1 : τ + ((1 : ℕ) : ℤ) = τ + 1 := by norm_num
    have e2 : τ - ((1 : ℕ) : ℤ) = τ + (-1) := by norm_num; ring
    simp only [e1, e2, reflected, CharP.cast_eq_zero, add_zero, sub_zero, pow_zero, pow_one, one_mul,
      e, Int.reduceAdd, Int.reduceNeg]
    split_ifs
    · simp only [RadialData.toFun_cap]
      ring
    · ring
  · rw [waveOp_ray_succ]
    simp only [RadialData.toFun_ray, pulseData]
    have a1 : τ + 1 + ((k + 1 : ℕ) : ℤ) = τ + ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    have a2 : τ + (-1) + ((k + 1 : ℕ) : ℤ) = τ + (k : ℤ) := by push_cast; ring
    have a3 : τ + 1 - ((k + 1 : ℕ) : ℤ) = τ - (k : ℤ) := by push_cast; ring
    have a4 : τ + (-1) - ((k + 1 : ℕ) : ℤ) = τ - ((k + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [a1, a2, a3, a4]
    ring

/-! ### The echo train -/

/-- The echo at double tick `m`: the reflected signal at time `2m`. -/
def echo (q t h : ℂ) (m : ℕ) : ℂ := reflected q t h (2 * m)

theorem delta_ne {τ : ℤ} (h : τ ≠ 0) : delta τ = 0 := by simp [delta, h]

theorem coreTime_of_neg (q t : ℂ) {τ : ℤ} (hτ : τ < 0) : coreTime q t τ = 0 := by
  unfold coreTime
  split_ifs
  · exact coreZ_of_neg q t (by omega)
  · rfl

/-- **Causality.** Nothing comes back before time 2. -/
theorem reflected_of_lt (q t h : ℂ) {τ : ℤ} (hτ : τ < 2) : reflected q t h τ = 0 := by
  unfold reflected
  rw [delta_ne (by omega), coreTime_of_neg q t (by omega), coreTime_of_neg q t (by omega)]
  ring

/-- The signal vanishes at odd times. -/
theorem reflected_of_not_even (q t h : ℂ) {τ : ℤ} (hτ : ¬ Even τ) : reflected q t h τ = 0 := by
  have hodd : Odd τ := Int.not_even_iff_odd.mp hτ
  have hn (k : ℤ) (hk : Even k) : ¬ Even (τ + k) := by
    rw [Int.even_add]
    simp [hk, hτ]
  unfold reflected
  have hne : τ + (-2) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := hodd
    omega
  rw [delta_ne hne, coreTime_of_not_even q t (hn _ (by decide)),
    coreTime_of_not_even q t (hn _ (by decide))]
  ring

/-- **The prompt bounce.** The first echo is `q`, independent of the core. -/
theorem echo_one (q t h : ℂ) : echo q t h 1 = q := by
  unfold echo reflected
  have a0 : (2 * ((1 : ℕ) : ℤ) + (-2)) = 0 := by norm_num
  have a4 : coreTime q t (2 * ((1 : ℕ) : ℤ) + (-4)) = 0 := coreTime_of_neg q t (by norm_num)
  have a6 : coreTime q t (2 * ((1 : ℕ) : ℤ) + (-6)) = 0 := coreTime_of_neg q t (by norm_num)
  rw [a0, a4, a6]
  simp [delta]

theorem coreTime_natCast_two_mul (q t : ℂ) (n : ℕ) : coreTime q t (2 * (n : ℤ)) = coreSeq q t n := by
  rw [coreTime_two_mul, coreZ_natCast]

/-- The echoes after the first bounce: the core response with the factor `q(q-1)h`. -/
theorem echo_add_two (q t h : ℂ) (n : ℕ) :
    echo q t h (n + 2) = q * (q - 1) * h *
      (coreSeq q t n + q * if n = 0 then 0 else coreSeq q t (n - 1)) := by
  unfold echo reflected
  have hne : (2 * ((n + 2 : ℕ) : ℤ) + (-2)) ≠ 0 := by push_cast; omega
  rw [delta_ne hne]
  have e4 : 2 * ((n + 2 : ℕ) : ℤ) + (-4) = 2 * (n : ℤ) := by push_cast; ring
  have e6 : 2 * ((n + 2 : ℕ) : ℤ) + (-6) = 2 * ((n : ℤ) + (-1)) := by push_cast; ring
  rw [e4, e6, coreTime_natCast_two_mul, coreTime_two_mul]
  rcases n with _ | n
  · rw [coreZ_of_neg q t (by norm_num)]
    simp
  · have e : ((n + 1 : ℕ) : ℤ) + (-1) = (n : ℤ) := by push_cast; ring
    rw [e, coreZ_natCast]
    simp

/-! ### The ringdown signal -/

/-- The Lucas sequence: the coefficient of `w^m` in `1/(1 - tw + qw²)`. -/
def lucas (q t : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => t
  | n + 2 => t * lucas q t (n + 1) - q * lucas q t n

theorem lucas_add_two (q t : ℂ) (n : ℕ) :
    lucas q t (n + 2) = t * lucas q t (n + 1) - q * lucas q t n := rfl

/-- **The ground mode is removed by a causal probe.** Multiplying by `1 - q²w` turns the core response
into the Lucas sequence. -/
theorem coreSeq_sub_ground (q t : ℂ) (n : ℕ) :
    coreSeq q t (n + 1) - q ^ 2 * coreSeq q t n = lucas q t (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [coreSeq, lucas]
  | one => simp only [coreSeq, lucas]; ring
  | more n h0 h1 =>
    have h1' : coreSeq q t (n + 2) - q ^ 2 * coreSeq q t (n + 1) = lucas q t (n + 2) := h1
    show coreSeq q t (n + 3) - q ^ 2 * coreSeq q t (n + 2) = lucas q t (n + 1 + 2)
    rw [coreSeq_add_three, lucas_add_two q t (n + 1)]
    linear_combination t * h1' - q * h0

/-- The ringdown signal `R_n`: the echo train seen through the probe `1 - q²w`, without the factor
`q(q-1)h`. -/
def ringSignal (q t : ℂ) (n : ℕ) : ℂ := lucas q t (n + 1) + q * lucas q t n

/-- **The ringdown is a second-order recurrence.** The ground mode is gone and what is left is one damped
oscillator: `R_{n+2} = t R_{n+1} - q R_n`. -/
theorem ringSignal_add_two (q t : ℂ) (n : ℕ) :
    ringSignal q t (n + 2) = t * ringSignal q t (n + 1) - q * ringSignal q t n := by
  unfold ringSignal
  rw [lucas_add_two q t (n + 1), lucas_add_two q t n]
  ring

/-- The echo train through the ground-mode probe is the ringdown signal, from the second echo on. -/
theorem echo_sub_ground (q t h : ℂ) (n : ℕ) :
    echo q t h (n + 3) - q ^ 2 * echo q t h (n + 2) = q * (q - 1) * h * ringSignal q t n := by
  have e (k : ℕ) : echo q t h (k + 3) =
      q * (q - 1) * h * (coreSeq q t (k + 1) + q * coreSeq q t k) := by
    rw [show k + 3 = (k + 1) + 2 from rfl, echo_add_two]
    simp
  unfold ringSignal
  rcases n with _ | k
  · rw [e, echo_add_two]
    simp only [if_true, coreSeq, lucas]
    ring
  · rw [show k + 1 + 3 = (k + 1) + 3 from rfl, e, show k + 1 + 2 = k + 3 from rfl, e]
    have h1 := coreSeq_sub_ground q t (k + 1)
    have h0 := coreSeq_sub_ground q t k
    linear_combination (q * (q - 1) * h) * (h1 + q * h0)

/-! ### Modes -/

/-- **Exact mode expansion of the core response.** For distinct roots, `d_m` is a finite sum of powers:
there is no remainder. -/
theorem coreSeq_eq_modes {q t a b c : ℂ} (hsum : a + b + c = q ^ 2 + t)
    (hpair : a * b + a * c + b * c = q + q ^ 2 * t) (hprod : a * b * c = q ^ 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (n : ℕ) :
    coreSeq q t n = a ^ (n + 2) / ((a - b) * (a - c)) + b ^ (n + 2) / ((b - a) * (b - c)) +
      c ^ (n + 2) / ((c - a) * (c - b)) := by
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hba' : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hac.symm
  have hcb' : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have root (x : ℂ) (hx : (x - a) * (x - b) * (x - c) = 0) :
      x ^ 3 = (q ^ 2 + t) * x ^ 2 - (q + q ^ 2 * t) * x + q ^ 3 := by
    rw [← hsum, ← hpair, ← hprod]
    linear_combination hx
  have ha := root a (by ring)
  have hb := root b (by ring)
  have hc := root c (by ring)
  have base0 : coreSeq q t 0 = a ^ (0 + 2) / ((a - b) * (a - c)) + b ^ (0 + 2) / ((b - a) * (b - c)) +
      c ^ (0 + 2) / ((c - a) * (c - b)) := by
    simp only [coreSeq]
    field_simp
    ring
  have base1 : coreSeq q t 1 = a ^ (1 + 2) / ((a - b) * (a - c)) + b ^ (1 + 2) / ((b - a) * (b - c)) +
      c ^ (1 + 2) / ((c - a) * (c - b)) := by
    simp only [coreSeq]
    rw [← hsum]
    field_simp
    ring
  have base2 : coreSeq q t 2 = a ^ (2 + 2) / ((a - b) * (a - c)) + b ^ (2 + 2) / ((b - a) * (b - c)) +
      c ^ (2 + 2) / ((c - a) * (c - b)) := by
    simp only [coreSeq]
    rw [← hsum, ← hpair]
    field_simp
    ring
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact base0
    | 1 => exact base1
    | 2 => exact base2
    | k + 3 =>
      rw [coreSeq_add_three, ih (k + 2) (by omega), ih (k + 1) (by omega), ih k (by omega)]
      have ea : a ^ (k + 3 + 2) = (q ^ 2 + t) * a ^ (k + 2 + 2) - (q + q ^ 2 * t) * a ^ (k + 1 + 2) +
          q ^ 3 * a ^ (k + 2) := by
        rw [show k + 3 + 2 = (k + 2) + 3 by ring, pow_add a (k + 2) 3, ha]
        ring
      have eb : b ^ (k + 3 + 2) = (q ^ 2 + t) * b ^ (k + 2 + 2) - (q + q ^ 2 * t) * b ^ (k + 1 + 2) +
          q ^ 3 * b ^ (k + 2) := by
        rw [show k + 3 + 2 = (k + 2) + 3 by ring, pow_add b (k + 2) 3, hb]
        ring
      have ec : c ^ (k + 3 + 2) = (q ^ 2 + t) * c ^ (k + 2 + 2) - (q + q ^ 2 * t) * c ^ (k + 1 + 2) +
          q ^ 3 * c ^ (k + 2) := by
        rw [show k + 3 + 2 = (k + 2) + 3 by ring, pow_add c (k + 2) 3, hc]
        ring
      rw [ea, eb, ec]
      ring

/-! ### The two branches -/

/-- A solution of the wave equation with a time factor: `ζ^τ f(v)`, where `A f = (ζ + q/ζ) f`. -/
def modeField (ζ : ℂ) (f : Vertex G D → ℂ) (τ : ℤ) (v : Vertex G D) : ℂ := ζ ^ τ * f v

/-- Both branches solve the wave equation. -/
theorem modeField_isWave {q : ℕ} {ζ ζ' : ℂ} (hζ : ζ ≠ 0) (hprod : ζ * ζ' = q) {f : Vertex G D → ℂ}
    (hf : ∀ v, waveOp q f v = (ζ + ζ') * f v) : IsWave q (modeField ζ f) := by
  intro τ v
  have hlin : waveOp q (modeField ζ f τ) v = ζ ^ τ * waveOp q f v := by
    have hs : modeField ζ f τ = fun w => ζ ^ τ * f w := rfl
    rw [hs]
    rcases v with _ | d | x | L | ⟨P, _ | k⟩
    · simp only [waveOp_core, mul_add, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun P _ => ?_
      ring
    · simp only [waveOp_dead]
      ring
    · induction x using Quotient.inductionOn with
      | h P =>
        change waveOp q _ (.neck (Branch.mk P)) = _ * waveOp q _ (.neck (Branch.mk P))
        rw [waveOp_neck, waveOp_neck]
        unfold neckOp
        split_ifs <;> ring
    · simp only [waveOp_cap]
      ring
    · simp only [waveOp_ray_zero]
      unfold gapOp
      split_ifs <;> ring
    · simp only [waveOp_ray_succ]
      ring
  rw [hlin, hf]
  simp only [modeField]
  rw [zpow_add₀ hζ, zpow_add₀ hζ, zpow_one, zpow_neg_one, ← hprod]
  field_simp

/-- **The minus branch is outgoing.** With time factor `X^τ` a resonant state is on every ray a function
of `τ - k`, up to the weight `q^k`. -/
theorem minusBranch_isOutgoing {q : ℕ} {X Y : ℂ} (hX : X ≠ 0) (hXY : X * Y = q) {f : Vertex G D → ℂ}
    {c : G → ℂ} (hf : IsOutgoing q X Y f c) (τ : ℤ) (P : G) (k : ℕ) :
    modeField X f τ (.ray P k) = (q : ℂ) ^ k * (c P * X ^ (τ - k)) := by
  unfold modeField
  rw [hf.ray, ← hXY, zpow_sub₀ hX, zpow_natCast, mul_pow]
  have hk : X ^ k ≠ 0 := pow_ne_zero k hX
  field_simp

/-- **The plus branch is incoming, so it is silent.** The same state with time factor `Y^τ` is on every
ray a function of `τ + k`: an incoming wave with no outgoing part, absorbed completely by the core. It is
the time reversal of the ringdown. -/
theorem plusBranch_isIncoming {q : ℕ} {X Y : ℂ} (hY : Y ≠ 0) {f : Vertex G D → ℂ} {c : G → ℂ}
    (hf : IsOutgoing q X Y f c) (τ : ℤ) (P : G) (k : ℕ) :
    modeField Y f τ (.ray P k) = c P * Y ^ (τ + k) := by
  unfold modeField
  rw [hf.ray, zpow_add₀ hY, zpow_natCast]
  ring

/-- **Reflection is reciprocal.** The zero of the scattering coefficient at the plus branch is the pole at
the minus branch: `S(X, Y) = -Y j(Y, X)/(X j(X, Y))` and `S(X, Y) S(Y, X) = 1`. -/
theorem scattering_mul_swap {t X Y : ℂ} (hX : X ≠ 0) (hY : Y ≠ 0) (h1 : jost t X Y ≠ 0)
    (h2 : jost t Y X ≠ 0) :
    (-(Y * jost t Y X) / (X * jost t X Y)) * (-(X * jost t X Y) / (Y * jost t Y X)) = 1 := by
  field_simp

/-! ### Rates -/

/-- The damping rate of the mode at `a = X²`, in units of `log q`: the ring-down factor per tick is
`q^{-rate}`. For `a = q^ρ` this is `(1 - Re ρ)/2`. -/
def dampingRate (q : ℝ) (a : ℂ) : ℝ := (1 - Real.log ‖a‖ / Real.log q) / 2

/-- **Functional-equation partners have rates summing to `½`.** -/
theorem dampingRate_add_partner {q : ℝ} (hq : 1 < q) {a : ℂ} (ha : a ≠ 0) :
    dampingRate q a + dampingRate q ((q : ℂ) / a) = 1 / 2 := by
  have hq0 : 0 < q := by linarith
  have hlog : Real.log q ≠ 0 := (Real.log_pos hq).ne'
  have hn : ‖(q : ℂ) / a‖ = q / ‖a‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  unfold dampingRate
  rw [hn, Real.log_div hq0.ne' hna.ne']
  field_simp
  ring

/-- The rate is `¼` exactly when `|a|² = q`: the modulus of the universal mode. -/
theorem dampingRate_eq_quarter_iff {q : ℝ} (hq : 1 < q) {a : ℂ} (ha : a ≠ 0) :
    dampingRate q a = 1 / 4 ↔ ‖a‖ ^ 2 = q := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  unfold dampingRate
  constructor
  · intro h
    have h1 : Real.log ‖a‖ / Real.log q = 1 / 2 := by linarith
    have h2 : 2 * Real.log ‖a‖ = Real.log q := by
      field_simp at h1
      linarith
    have h3 : Real.log (‖a‖ ^ 2) = Real.log q := by
      rw [Real.log_pow]
      push_cast
      exact h2
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr hq0) h3
  · intro h
    have h3 : Real.log (‖a‖ ^ 2) = Real.log q := by rw [h]
    rw [Real.log_pow] at h3
    push_cast at h3
    field_simp
    linarith

end GaloisForLFunctions.ArithmeticScatteringHolography

end
