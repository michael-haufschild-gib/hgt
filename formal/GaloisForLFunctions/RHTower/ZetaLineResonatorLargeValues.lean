import GaloisForLFunctions.RHTower.ZetaLineTwistedSeriesMoment

/-!
# Large values of `Re ζ(½ + it)` from a prime product resonator

For a finite set `P` of primes put
`W_P(t) = ∏_{p∈P} (2 + 2 cos(t log p)) = ∏_{p∈P} |1 + p^{it}|² ≥ 0`.

* **Twisted moments** (`norm_twistInt_zeta_sub_le`, `norm_twistInt_one_sub_le`). For `m, d ≥ 1`
  coprime to every `p ∈ P`, with `Q = ∏_{p∈P} p`:
  - `∫_T^{2T} ζ(½+it) W_P(t) (m/d)^{it} dt` equals `[d ∣ m] √(d/m) T ∏_{p∈P}(2 + p^{−½})` up to
    `4^{|P|} Q³ · 35 √(dm) m² √T`;
  - `∫_T^{2T} W_P(t) (m/d)^{it} dt` equals `[m = d] 2^{|P|} T` up to `4^{|P|} Q² · 2md`.

  The proof is induction on `P`. Since `W_{P∪{q}} = (2 + q^{it} + q^{−it}) W_P`, each moment
  splits into three moments of `W_P`, with twists `m/d`, `mq/d` and `m/(dq)`. The main terms satisfy
  the same recursion because `q ∤ m` and `q ∤ d`. At `P = ∅`, the first is the twisted first
  moment of `ζ` (`norm_integral_zeta_expChar_sub_le`); the second is the integral of `e^{iξt}`.
* **Resonance** (`resGain_le_of_re_le`). If `Re ζ(½+it) ≤ B` on `[T, 2T]` with `B ≥ 0`, then
  `T ∏(2 + p^{−½}) − err ≤ B (2^{|P|} T + err')`. Here `W_P ≥ 0`, and the gain per prime is
  `1 + 1/(2√p)`.
* **Large values** (`exists_log_add_lt_re_zeta`). For every `K` and `T₀` there is `t ≥ T₀` with
  `Re ζ(½+it) > log t + K`. Take `P` = the primes `≤ y`, `y = N⁸`, `T = e^{20y}`. Then
  `∏_{p≤y}(1 + 1/(2√p)) ≥ exp(¼ Σ_{p≤y} p^{−½}) ≥ exp(θ(y)/(4√y log y))`, and Chebyshev's lower
  bound for `θ` makes this exceed every linear function of `y = log T/20`. The errors are controlled
  by `∏_{p≤y} p ≤ 4^y`.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower.ZetaResonator

open RHTower.WeilBoundaryDilation RHTower.ZetaLineTwist

local notation "eχ" => _root_.GaloisForLFunctions.expChar

/-! ## The resonator -/

/-- `W_P(t) = ∏_{p∈P} (2 + 2 cos(t log p))`. -/
def resW (P : Finset ℕ) (t : ℝ) : ℝ := ∏ p ∈ P, (2 + 2 * Real.cos (t * Real.log p))

/-- The resonance gain `∏_{p∈P} (2 + p^{−½})`. -/
def resGain (P : Finset ℕ) : ℝ := ∏ p ∈ P, (2 + 1 / Real.sqrt p)

/-- The prime product `Q = ∏_{p∈P} p`. -/
def primeProd (P : Finset ℕ) : ℝ := ∏ p ∈ P, (p : ℝ)

theorem resW_nonneg (P : Finset ℕ) (t : ℝ) : 0 ≤ resW P t :=
  Finset.prod_nonneg fun p _ => by nlinarith [Real.neg_one_le_cos (t * Real.log p)]

theorem continuous_resW (P : Finset ℕ) : Continuous (resW P) := by
  unfold resW
  exact continuous_finsetProd _ fun p _ => by fun_prop

theorem one_le_primeProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) : 1 ≤ primeProd P := by
  have h := Finset.prod_le_prod (s := P) (f := fun _ : ℕ => (1 : ℝ)) (g := fun p : ℕ => (p : ℝ))
    (fun _ _ => zero_le_one) fun p hp => by exact_mod_cast (hP p hp).one_lt.le
  simpa [primeProd] using h

theorem continuous_expChar' (ξ : ℝ) : Continuous (eχ ξ) := by
  unfold _root_.GaloisForLFunctions.expChar; fun_prop

/-- `2 cos(t log q) · e^{iξt} = e^{i(ξ + log q)t} + e^{i(ξ − log q)t}`. -/
theorem two_cos_mul_expChar (q ξ t : ℝ) :
    ((2 * Real.cos (t * q) : ℝ) : ℂ) * eχ ξ t = eχ (ξ + q) t + eχ (ξ - q) t := by
  unfold _root_.GaloisForLFunctions.expChar
  rw [show ((2 * Real.cos (t * q) : ℝ) : ℂ) = Complex.exp (((q * t : ℝ) : ℂ) * I) +
      Complex.exp (-(((q * t : ℝ) : ℂ) * I)) by
    rw [show t * q = q * t by ring, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos,
      Complex.cos, ← mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, ← neg_mul]]
  rw [add_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-! ## The twisted integrals and their recursion -/

/-- `∫_T^{2T} f(t) W_P(t) (m/d)^{it} dt`. -/
def twistInt (f : ℝ → ℂ) (T : ℝ) (P : Finset ℕ) (m d : ℕ) : ℂ :=
  ∫ t in T..(2 * T), f t * (resW P t : ℂ) * eχ (Real.log m - Real.log d) t

theorem twistInt_insert {f : ℝ → ℂ} (hf : Continuous f) (T : ℝ) {P : Finset ℕ} {q : ℕ}
    (hq : q ∉ P) {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hq1 : 1 ≤ q) :
    twistInt f T (insert q P) m d =
      2 * twistInt f T P m d + twistInt f T P (m * q) d + twistInt f T P m (d * q) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have e1 : Real.log ((m * q : ℕ) : ℝ) - Real.log d = (Real.log m - Real.log d) + Real.log q := by
    rw [Nat.cast_mul, Real.log_mul hmR.ne' hqR.ne']; ring
  have e2 : Real.log m - Real.log ((d * q : ℕ) : ℝ) = (Real.log m - Real.log d) - Real.log q := by
    rw [Nat.cast_mul, Real.log_mul hdR.ne' hqR.ne']; ring
  have hpt : ∀ t, f t * (resW (insert q P) t : ℂ) * eχ (Real.log m - Real.log d) t =
      2 * (f t * (resW P t : ℂ) * eχ (Real.log m - Real.log d) t) +
      f t * (resW P t : ℂ) * eχ (Real.log ((m * q : ℕ) : ℝ) - Real.log d) t +
      f t * (resW P t : ℂ) * eχ (Real.log m - Real.log ((d * q : ℕ) : ℝ)) t := by
    intro t
    have h2 := two_cos_mul_expChar (Real.log q) (Real.log m - Real.log d) t
    have hW : (resW (insert q P) t : ℂ) =
        (2 + ((2 * Real.cos (t * Real.log q) : ℝ) : ℂ)) * (resW P t : ℂ) := by
      unfold resW
      rw [Finset.prod_insert hq, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_ofNat]
    rw [hW, e1, e2]
    linear_combination (f t * (resW P t : ℂ)) * h2
  have hc : ∀ ξ : ℝ, Continuous fun t => f t * (resW P t : ℂ) * eχ ξ t := fun ξ =>
    (hf.mul (Complex.continuous_ofReal.comp (continuous_resW P))).mul (continuous_expChar' ξ)
  have h0 : IntervalIntegrable (fun t => 2 * (f t * (resW P t : ℂ) *
      eχ (Real.log m - Real.log d) t)) volume T (2 * T) :=
    (continuous_const.mul (hc _)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun t => f t * (resW P t : ℂ) *
      eχ (Real.log ((m * q : ℕ) : ℝ) - Real.log d) t) volume T (2 * T) :=
    (hc _).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t => f t * (resW P t : ℂ) *
      eχ (Real.log m - Real.log ((d * q : ℕ) : ℝ)) t) volume T (2 * T) :=
    (hc _).intervalIntegrable _ _
  unfold twistInt
  rw [intervalIntegral.integral_congr fun t _ => hpt t,
    intervalIntegral.integral_add (h0.add h1) h3,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_const_mul]

/-! ## Induction over the primes of the resonator -/

theorem not_dvd_mul_of_ne {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {q : ℕ} (hq : q ∉ P)
    (hqP : q.Prime) {m : ℕ} (hm : ∀ p ∈ P, ¬ p ∣ m) : ∀ p ∈ P, ¬ p ∣ m * q := by
  intro p hp h
  rcases (hP p hp).dvd_mul.mp h with h | h
  · exact hm p hp h
  · have := (Nat.prime_dvd_prime_iff_eq (hP p hp) hqP).mp h
    exact hq (this ▸ hp)

/-- **The recursion bound.** If the integrals `I` and the main terms `M` satisfy the same
three-term recursion over the primes of the resonator, the error grows by at most `4 q^k` per
prime `q`. -/
theorem norm_sub_le_of_recursion {I M : Finset ℕ → ℕ → ℕ → ℂ} {φ : ℕ → ℕ → ℝ} {k : ℕ}
    (hφ0 : ∀ m d, 0 ≤ φ m d)
    (hφm : ∀ m d q : ℕ, 1 ≤ q → φ (m * q) d ≤ (q : ℝ) ^ k * φ m d)
    (hφd : ∀ m d q : ℕ, 1 ≤ q → φ m (d * q) ≤ (q : ℝ) ^ k * φ m d)
    (hI : ∀ (P : Finset ℕ) (q m d : ℕ), q ∉ P → 1 ≤ m → 1 ≤ d → 1 ≤ q →
      I (insert q P) m d = 2 * I P m d + I P (m * q) d + I P m (d * q))
    (hM : ∀ (P : Finset ℕ) (q m d : ℕ), q ∉ P → q.Prime → ¬ q ∣ m → ¬ q ∣ d →
      M (insert q P) m d = 2 * M P m d + M P (m * q) d + M P m (d * q))
    (h0 : ∀ m d, 1 ≤ m → 1 ≤ d → ‖I ∅ m d - M ∅ m d‖ ≤ φ m d) :
    ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → ∀ m d, 1 ≤ m → 1 ≤ d →
      (∀ p ∈ P, ¬ p ∣ m ∧ ¬ p ∣ d) →
      ‖I P m d - M P m d‖ ≤ 4 ^ P.card * primeProd P ^ k * φ m d := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty => intro _ m d hm hd _; simpa [primeProd] using h0 m d hm hd
  | insert q P hq ih =>
    intro hP m d hm hd hcop
    have hqP : q.Prime := hP q (Finset.mem_insert_self q P)
    have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcop' : ∀ p ∈ P, ¬ p ∣ m ∧ ¬ p ∣ d := fun p hp => hcop p (Finset.mem_insert_of_mem hp)
    obtain ⟨hqm, hqd⟩ := hcop q (Finset.mem_insert_self q P)
    have hq1 : 1 ≤ q := hqP.one_lt.le
    have hmq := not_dvd_mul_of_ne hP' hq hqP fun p hp => (hcop' p hp).1
    have hdq := not_dvd_mul_of_ne hP' hq hqP fun p hp => (hcop' p hp).2
    have e1 := ih hP' m d hm hd hcop'
    have e2 := ih hP' (m * q) d (Nat.one_le_iff_ne_zero.mpr (by positivity)) hd
      fun p hp => ⟨hmq p hp, (hcop' p hp).2⟩
    have e3 := ih hP' m (d * q) hm (Nat.one_le_iff_ne_zero.mpr (by positivity))
      fun p hp => ⟨(hcop' p hp).1, hdq p hp⟩
    rw [hI P q m d hq hm hd hq1, hM P q m d hq hqP hqm hqd]
    have key : (2 * I P m d + I P (m * q) d + I P m (d * q)) -
        (2 * M P m d + M P (m * q) d + M P m (d * q)) = 2 * (I P m d - M P m d) +
          (I P (m * q) d - M P (m * q) d) + (I P m (d * q) - M P m (d * q)) := by ring
    rw [key]
    set c := (4 : ℝ) ^ P.card * primeProd P ^ k with hc
    have hc0 : 0 ≤ c := by
      have := one_le_primeProd hP'
      positivity
    have hqk : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hq1)
    have hφ := hφ0 m d
    have hb2 : c * φ (m * q) d ≤ c * ((q : ℝ) ^ k * φ m d) :=
      mul_le_mul_of_nonneg_left (hφm m d q hq1) hc0
    have hb3 : c * φ m (d * q) ≤ c * ((q : ℝ) ^ k * φ m d) :=
      mul_le_mul_of_nonneg_left (hφd m d q hq1) hc0
    have hfin : 4 ^ (insert q P).card * primeProd (insert q P) ^ k * φ m d =
        4 * c * ((q : ℝ) ^ k * φ m d) := by
      rw [Finset.card_insert_of_notMem hq, primeProd, Finset.prod_insert hq, mul_pow, hc,
        primeProd, pow_succ]
      ring
    rw [hfin]
    calc ‖2 * (I P m d - M P m d) + (I P (m * q) d - M P (m * q) d) +
          (I P m (d * q) - M P m (d * q))‖
        ≤ ‖2 * (I P m d - M P m d)‖ + ‖I P (m * q) d - M P (m * q) d‖ +
          ‖I P m (d * q) - M P m (d * q)‖ := norm_add₃_le
      _ ≤ 2 * (c * φ m d) + c * φ (m * q) d + c * φ m (d * q) := by
          rw [norm_mul, Complex.norm_two]
          gcongr
      _ ≤ 4 * c * ((q : ℝ) ^ k * φ m d) := by nlinarith [mul_nonneg hc0 hφ]

/-! ## The first moment of `ζ` against the resonator -/

/-- The main term `[d ∣ m] √(d/m) T ∏_{p∈P}(2 + p^{−½})`. -/
def zetaMain (T : ℝ) (P : Finset ℕ) (m d : ℕ) : ℂ :=
  if d ∣ m then ((Real.sqrt d / Real.sqrt m * T * resGain P : ℝ) : ℂ) else 0

theorem resGain_insert {P : Finset ℕ} {q : ℕ} (hq : q ∉ P) :
    resGain (insert q P) = (2 + 1 / Real.sqrt q) * resGain P := by
  unfold resGain; rw [Finset.prod_insert hq]

theorem zetaMain_insert (T : ℝ) {P : Finset ℕ} {q m d : ℕ} (hq : q ∉ P) (hqP : q.Prime)
    (hqm : ¬ q ∣ m) (hqd : ¬ q ∣ d) :
    zetaMain T (insert q P) m d =
      2 * zetaMain T P m d + zetaMain T P (m * q) d + zetaMain T P m (d * q) := by
  have hcop : Nat.Coprime d q := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hqP).mpr hqd))
  have h1 : d ∣ m * q ↔ d ∣ m := ⟨fun h => hcop.dvd_of_dvd_mul_right h, fun h => h.mul_right q⟩
  have h2 : ¬ d * q ∣ m := fun h => hqm (dvd_trans (Dvd.intro_left d rfl) h)
  unfold zetaMain
  rw [if_congr h1 rfl rfl, if_neg h2, resGain_insert hq]
  split_ifs with h
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hqP.pos
    have hsq : Real.sqrt ((m * q : ℕ) : ℝ) = Real.sqrt m * Real.sqrt q := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _)]
    rw [hsq]
    push_cast
    have hsq0 : Real.sqrt (q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    by_cases hm0 : Real.sqrt (m : ℝ) = 0
    · simp [hm0]
    field_simp
    ring
  · simp

theorem resW_empty (t : ℝ) : resW ∅ t = 1 := by simp [resW]

theorem resGain_empty : resGain ∅ = 1 := by simp [resGain]

/-- **The first moment of `ζ` against the resonator.** -/
theorem norm_twistInt_zeta_sub_le {T : ℝ} (hT : 4 ≤ T) {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hcop : ∀ p ∈ P, ¬ p ∣ m ∧ ¬ p ∣ d) :
    ‖twistInt (fun t => riemannZeta (linePt t)) T P m d - zetaMain T P m d‖ ≤
      4 ^ P.card * primeProd P ^ 3 *
        (35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) := by
  have hsT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  refine norm_sub_le_of_recursion (φ := fun m d => 35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 *
    Real.sqrt T) (fun m d => by positivity) ?_ ?_
    (fun P q m d hq hm hd hq1 => twistInt_insert continuous_zeta_linePt T hq hm hd hq1)
    (fun P q m d hq hqP hqm hqd => zetaMain_insert T hq hqP hqm hqd) ?_ P hP m d hm hd hcop
  · intro m d q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hsq : Real.sqrt (q : ℝ) ≤ q := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have e : Real.sqrt ((d : ℝ) * ((m * q : ℕ) : ℝ)) = Real.sqrt ((d : ℝ) * m) * Real.sqrt q := by
      rw [Nat.cast_mul, ← mul_assoc, Real.sqrt_mul (by positivity)]
    rw [e]
    push_cast
    have h0 : 0 ≤ Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T := by positivity
    calc 35 * (Real.sqrt ((d : ℝ) * m) * Real.sqrt q) * ((m : ℝ) * q) ^ 2 * Real.sqrt T
        = 35 * (Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) * (Real.sqrt q * q ^ 2) := by
          ring
      _ ≤ 35 * (Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) * ((q : ℝ) * q ^ 2) := by
          gcongr
      _ = (q : ℝ) ^ 3 * (35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) := by ring
  · intro m d q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hsq : Real.sqrt (q : ℝ) ≤ q ^ 3 := by
      have : Real.sqrt (q : ℝ) ≤ q := by rw [Real.sqrt_le_left (by positivity)]; nlinarith
      exact this.trans (le_self_pow₀ hq1 (by norm_num))
    have e : Real.sqrt (((d * q : ℕ) : ℝ) * m) = Real.sqrt ((d : ℝ) * m) * Real.sqrt q := by
      rw [Nat.cast_mul, show (d : ℝ) * q * m = d * m * q by ring, Real.sqrt_mul (by positivity)]
    rw [e]
    have h0 : 0 ≤ 35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T := by positivity
    calc 35 * (Real.sqrt ((d : ℝ) * m) * Real.sqrt q) * (m : ℝ) ^ 2 * Real.sqrt T
        = (35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) * Real.sqrt q := by ring
      _ ≤ (35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T) * (q : ℝ) ^ 3 := by gcongr
      _ = _ := by ring
  · intro m d hm hd
    have h := norm_integral_zeta_expChar_sub_le hd hm hT
    have e : twistInt (fun t => riemannZeta (linePt t)) T ∅ m d =
        ∫ t in T..(2 * T), riemannZeta (linePt t) * eχ (Real.log m - Real.log d) t := by
      unfold twistInt
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [resW_empty, Complex.ofReal_one, mul_one]
    have e2 : zetaMain T ∅ m d =
        if d ∣ m then ((Real.sqrt d / Real.sqrt m * T : ℝ) : ℂ) else 0 := by
      simp [zetaMain, resGain_empty]
    rw [e, e2]
    refine h.trans ?_
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h0 : 0 ≤ Real.sqrt ((d : ℝ) * m) := Real.sqrt_nonneg _
    have hT0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
    have hm2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have a1 : 27 * Real.sqrt T * m ≤ 27 * Real.sqrt T * (m : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    have a2 : 8 * (m : ℝ) ^ 2 ≤ 8 * (m : ℝ) ^ 2 * Real.sqrt T :=
      le_mul_of_one_le_right (by positivity) hsT
    calc Real.sqrt ((d : ℝ) * m) * (27 * Real.sqrt T * m + 8 * (m : ℝ) ^ 2)
        ≤ Real.sqrt ((d : ℝ) * m) * (27 * Real.sqrt T * (m : ℝ) ^ 2 +
            8 * (m : ℝ) ^ 2 * Real.sqrt T) := mul_le_mul_of_nonneg_left (by linarith) h0
      _ = 35 * Real.sqrt ((d : ℝ) * m) * (m : ℝ) ^ 2 * Real.sqrt T := by ring

/-! ## The mass of the resonator -/

theorem norm_integral_expChar_le {ξ : ℝ} (hξ : ξ ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, eχ ξ t‖ ≤ 2 / |ξ| := by
  have hc : (ξ : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hξ) I_ne_zero
  have e : (fun t : ℝ => eχ ξ t) = fun t : ℝ => Complex.exp ((ξ : ℂ) * I * t) := by
    funext t; unfold _root_.GaloisForLFunctions.expChar; push_cast; ring_nf
  have hn : ∀ x : ℝ, ‖Complex.exp ((ξ : ℂ) * I * x)‖ = 1 := fun x => by
    rw [show (ξ : ℂ) * I * x = ((ξ * x : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  rw [e, integral_exp_mul_complex hc, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc ‖Complex.exp ((ξ : ℂ) * I * b) - Complex.exp ((ξ : ℂ) * I * a)‖
      ≤ ‖Complex.exp ((ξ : ℂ) * I * b)‖ + ‖Complex.exp ((ξ : ℂ) * I * a)‖ := norm_sub_le _ _
    _ = 2 := by rw [hn, hn]; norm_num

theorem inv_mul_le_abs_log_sub {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hmd : m ≠ d) :
    1 / ((m : ℝ) * d) ≤ |Real.log m - Real.log d| := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have key : ∀ {a b : ℕ}, 1 ≤ a → 1 ≤ b → a < b → 1 / ((a : ℝ) * b) ≤ Real.log b - Real.log a := by
    intro a b ha hb hab
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have habR : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
    have h := Real.one_sub_inv_le_log_of_pos (x := (b : ℝ) / a) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h
    have h2 : 1 / ((a : ℝ) * b) ≤ 1 - a / b := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 - (a : ℝ) / b) * (a * b) = a * (b - a) := by field_simp
      rw [this]; nlinarith
    linarith
  rcases lt_or_gt_of_ne hmd with h | h
  · have k := key hm hd h
    have hp : (0 : ℝ) ≤ 1 / ((m : ℝ) * d) := by positivity
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    exact k
  · have k := key hd hm h
    have hp : (0 : ℝ) ≤ 1 / ((d : ℝ) * m) := by positivity
    rw [abs_of_nonneg (by linarith), mul_comm]
    exact k

/-- The main term `[m = d] 2^{|P|} T` of the twisted mass. -/
def oneMain (T : ℝ) (P : Finset ℕ) (m d : ℕ) : ℂ :=
  if m = d then (((2 : ℝ) ^ P.card * T : ℝ) : ℂ) else 0

theorem oneMain_insert (T : ℝ) {P : Finset ℕ} {q m d : ℕ} (hq : q ∉ P) (_hqP : q.Prime)
    (hqm : ¬ q ∣ m) (hqd : ¬ q ∣ d) :
    oneMain T (insert q P) m d =
      2 * oneMain T P m d + oneMain T P (m * q) d + oneMain T P m (d * q) := by
  have h1 : m * q ≠ d := fun h => hqd (h ▸ Dvd.intro_left m rfl)
  have h2 : m ≠ d * q := fun h => hqm (h ▸ Dvd.intro_left d rfl)
  unfold oneMain
  rw [if_neg h1, if_neg h2, Finset.card_insert_of_notMem hq]
  split_ifs <;> push_cast <;> ring

/-- **The twisted mass of the resonator.** -/
theorem norm_twistInt_one_sub_le {T : ℝ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hcop : ∀ p ∈ P, ¬ p ∣ m ∧ ¬ p ∣ d) :
    ‖twistInt (fun _ => 1) T P m d - oneMain T P m d‖ ≤
      4 ^ P.card * primeProd P ^ 2 * (2 * (m : ℝ) * d) := by
  refine norm_sub_le_of_recursion (φ := fun m d => 2 * (m : ℝ) * d) (fun m d => by positivity)
    ?_ ?_ (fun P q m d hq hm hd hq1 => twistInt_insert continuous_const T hq hm hd hq1)
    (fun P q m d hq hqP hqm hqd => oneMain_insert T hq hqP hqm hqd) ?_ P hP m d hm hd hcop
  · intro m d q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    have : (q : ℝ) ≤ q ^ 2 := le_self_pow₀ hq1 (by norm_num)
    have h0 : 0 ≤ 2 * (m : ℝ) * d := by positivity
    nlinarith
  · intro m d q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    have : (q : ℝ) ≤ q ^ 2 := le_self_pow₀ hq1 (by norm_num)
    have h0 : 0 ≤ 2 * (m : ℝ) * d := by positivity
    nlinarith
  · intro m d hm hd
    have e : twistInt (fun _ => 1) T ∅ m d = ∫ t in T..(2 * T), eχ (Real.log m - Real.log d) t := by
      unfold twistInt
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [resW_empty, Complex.ofReal_one, one_mul]
    rw [e]
    unfold oneMain
    split_ifs with hmd
    · subst hmd
      have h1 : ∀ t, eχ (Real.log m - Real.log m) t = 1 := fun t => by
        unfold _root_.GaloisForLFunctions.expChar; simp
      simp only [h1, intervalIntegral.integral_const, Finset.card_empty, pow_zero, one_mul]
      rw [Complex.real_smul, mul_one, show (((2 * T - T : ℝ)) : ℂ) - (T : ℂ) = 0 by push_cast; ring,
        norm_zero]
      positivity
    · rw [sub_zero]
      have hξ : Real.log m - Real.log d ≠ 0 := by
        intro h
        have := inv_mul_le_abs_log_sub hm hd hmd
        rw [h, abs_zero] at this
        have : (0 : ℝ) < 1 / ((m : ℝ) * d) := by positivity
        linarith
      refine (norm_integral_expChar_le hξ _ _).trans ?_
      have hl := inv_mul_le_abs_log_sub hm hd hmd
      have hpos : (0 : ℝ) < (m : ℝ) * d := by positivity
      rw [div_le_iff₀ (abs_pos.mpr hξ)]
      rw [div_le_iff₀ hpos] at hl
      nlinarith

/-! ## Resonance -/

theorem coprime_one_of_prime {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P, ¬ p ∣ 1 ∧ ¬ p ∣ 1 := fun p hp =>
  ⟨(hP p hp).not_dvd_one, (hP p hp).not_dvd_one⟩

/-- **The resonance inequality.** If `Re ζ(½+it) ≤ B` on `[T, 2T]`, `B ≥ 0`, then
`T ∏(2 + p^{−½}) − 4^{|P|} Q³ 35 √T ≤ B (2^{|P|} T + 2 · 4^{|P|} Q²)`. -/
theorem resGain_le_of_re_le {T B : ℝ} (hT : 4 ≤ T) (hB : 0 ≤ B) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hre : ∀ t ∈ Icc T (2 * T), (riemannZeta (linePt t)).re ≤ B) :
    T * resGain P - 4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) ≤
      B * ((2 : ℝ) ^ P.card * T + 4 ^ P.card * primeProd P ^ 2 * 2) := by
  have hT0 : 0 ≤ T := by linarith
  have h1 := norm_twistInt_zeta_sub_le hT hP le_rfl le_rfl (coprime_one_of_prime hP)
  have h2 := norm_twistInt_one_sub_le (T := T) hP le_rfl le_rfl (coprime_one_of_prime hP)
  have he : ∀ t, eχ (Real.log ((1 : ℕ) : ℝ) - Real.log ((1 : ℕ) : ℝ)) t = 1 := fun t => by
    unfold _root_.GaloisForLFunctions.expChar; simp
  have cW := continuous_resW P
  have cZ : Continuous fun t => riemannZeta (linePt t) * (resW P t : ℂ) :=
    continuous_zeta_linePt.mul (Complex.continuous_ofReal.comp cW)
  have eA : twistInt (fun t => riemannZeta (linePt t)) T P 1 1 =
      ∫ t in T..(2 * T), riemannZeta (linePt t) * (resW P t : ℂ) := by
    unfold twistInt; exact intervalIntegral.integral_congr fun t _ => by simp only [he, mul_one]
  have eB : twistInt (fun _ => 1) T P 1 1 = ((∫ t in T..(2 * T), resW P t : ℝ) : ℂ) := by
    unfold twistInt
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr fun t _ => by simp only [he, mul_one, one_mul]
  have mA : zetaMain T P 1 1 = ((T * resGain P : ℝ) : ℂ) := by
    simp [zetaMain]
  have mB : oneMain T P 1 1 = (((2 : ℝ) ^ P.card * T : ℝ) : ℂ) := by simp [oneMain]
  rw [eA, mA] at h1
  rw [eB, mB, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
  simp only [Nat.cast_one, mul_one, Real.sqrt_one, one_pow] at h1 h2
  -- the real part of the first moment
  have hreI : (∫ t in T..(2 * T), riemannZeta (linePt t) * (resW P t : ℂ)).re =
      ∫ t in T..(2 * T), (riemannZeta (linePt t)).re * resW P t := by
    rw [← Complex.reCLM_apply, ← (Complex.reCLM).intervalIntegral_comp_comm
      (cZ.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp
  have hup : ∫ t in T..(2 * T), (riemannZeta (linePt t)).re * resW P t ≤
      ∫ t in T..(2 * T), B * resW P t := by
    refine intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_re.comp continuous_zeta_linePt).mul cW |>.intervalIntegrable _ _)
      ((continuous_const.mul cW).intervalIntegrable _ _) fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hre t ht) (resW_nonneg P t)
  rw [intervalIntegral.integral_const_mul] at hup
  have hlow : T * resGain P - 4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T) ≤
      (∫ t in T..(2 * T), riemannZeta (linePt t) * (resW P t : ℂ)).re := by
    have := (Complex.abs_re_le_norm _).trans h1
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [(abs_le.mp this).1]
  have hmass := (abs_le.mp h2).2
  calc T * resGain P - 4 ^ P.card * primeProd P ^ 3 * (35 * Real.sqrt T)
      ≤ B * ∫ t in T..(2 * T), resW P t := by linarith
    _ ≤ B * ((2 : ℝ) ^ P.card * T + 4 ^ P.card * primeProd P ^ 2 * 2) := by
        apply mul_le_mul_of_nonneg_left _ hB; linarith

/-! ## Large values -/

theorem resGain_eq (P : Finset ℕ) :
    resGain P = (2 : ℝ) ^ P.card * ∏ p ∈ P, (1 + 1 / (2 * Real.sqrt p)) := by
  unfold resGain
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rcases eq_or_ne (Real.sqrt p) 0 with h | h
  · simp [h]
  · field_simp

/-- `exp(Σ_{p∈P} 1/(4√p)) ≤ ∏_{p∈P} (1 + 1/(2√p))`, from `e^{x/2} ≤ 1/(1 − x/2) ≤ 1 + x` on
`[0, 1]`. -/
theorem exp_sum_le_prod {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, 1 / (4 * Real.sqrt p)) ≤ ∏ p ∈ P, (1 + 1 / (2 * Real.sqrt p)) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (hP p hp).one_lt.le)
  set x := 1 / (2 * Real.sqrt p) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have e : 1 / (4 * Real.sqrt p) = x / 2 := by rw [hx]; field_simp; ring
  rw [e]
  refine (Real.exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem mem_primesLE {y p : ℕ} : p ∈ Nat.primesLE y ↔ p ≤ y ∧ p.Prime := by
  unfold Nat.primesLE
  rw [Nat.mem_primesBelow, Nat.lt_succ_iff]

/-- `θ(y)/(√y log y) ≤ Σ_{p≤y} p^{−½}`. -/
theorem theta_div_le_sum {y : ℕ} (hy : 2 ≤ y) :
    Chebyshev.theta y / (Real.sqrt y * Real.log y) ≤ ∑ p ∈ Nat.primesLE y, 1 / Real.sqrt p := by
  have hy2 : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hl : 0 < Real.log y := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_div]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpy, hpp⟩ := mem_primesLE.mp hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have hpyR : (p : ℝ) ≤ y := by exact_mod_cast hpy
  have hlp : Real.log p ≤ Real.log y := Real.log_le_log (by linarith) hpyR
  have hsp : Real.sqrt p ≤ Real.sqrt y := Real.sqrt_le_sqrt hpyR
  have hsp0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hlp0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  rw [div_le_div_iff₀ (by positivity) hsp0, one_mul]
  calc Real.log p * Real.sqrt p ≤ Real.log y * Real.sqrt y :=
        mul_le_mul hlp hsp hsp0.le hl.le
    _ = Real.sqrt y * Real.log y := by ring

theorem primeProd_primesLE (y : ℕ) : primeProd (Nat.primesLE y) = (primorial y : ℝ) := by
  unfold primeProd primorial Nat.primesLE Nat.primesBelow
  push_cast
  rfl

theorem card_primesLE_le (y : ℕ) : (Nat.primesLE y).card ≤ y + 1 := by
  unfold Nat.primesLE Nat.primesBelow
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem primes_of_primesLE (y : ℕ) : ∀ p ∈ Nat.primesLE y, p.Prime :=
  fun _ hp => (mem_primesLE.mp hp).2

/-- `θ(N⁸) ≥ N⁸/2` for `N ≥ 5`. -/
theorem half_le_theta {N : ℕ} (hN : 5 ≤ N) :
    ((N : ℝ) ^ 8) / 2 ≤ Chebyshev.theta ((N ^ 8 : ℕ) : ℝ) := by
  have h := Chebyshev.theta_ge (N ^ 8)
  have hN5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  push_cast at h ⊢
  have hsq : Real.sqrt ((N : ℝ) ^ 8) = (N : ℝ) ^ 4 := by
    rw [show (N : ℝ) ^ 8 = ((N : ℝ) ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hlog8 : Real.log ((N : ℝ) ^ 8) = 8 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlog1 : Real.log ((N : ℝ) ^ 8 + 1) ≤ 1 + 8 * N := by
    have h2 : (N : ℝ) ^ 8 + 1 ≤ 2 * (N : ℝ) ^ 8 := by
      nlinarith [one_le_pow₀ (n := 8) (by linarith : (1:ℝ) ≤ N)]
    calc Real.log ((N : ℝ) ^ 8 + 1) ≤ Real.log (2 * (N : ℝ) ^ 8) :=
          Real.log_le_log (by positivity) h2
      _ = Real.log 2 + 8 * Real.log N := by
          rw [Real.log_mul (by norm_num) (by positivity), hlog8]
      _ ≤ 1 + 8 * N := by have := Real.log_two_lt_d9; nlinarith
  have hl2 : (69 / 100 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  rw [hsq, hlog8] at h
  have hN8 : 0 ≤ (N : ℝ) ^ 8 := by positivity
  have hkey : 16 * (N : ℝ) ^ 5 + 8 * N + 1 ≤ (19 / 100) * (N : ℝ) ^ 8 := by
    have h3 : (125 : ℝ) ≤ (N : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hN5 3
      norm_num at this; linarith
    have h5 : (0 : ℝ) ≤ (N : ℝ) ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 h5, pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hN5 4]
  nlinarith [mul_le_mul_of_nonneg_left hl2 hN8, mul_le_mul_of_nonneg_left hlogN
    (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ) ^ 4 * 8)]

theorem four_pow_eq_exp (n : ℕ) : (4 : ℝ) ^ n = Real.exp (n * Real.log 4) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]

theorem log_four_lt : Real.log 4 < 7 / 5 := by
  have := Real.log_two_lt_d9
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith

/-- The two error terms at `T = e^{20y}`, `P` = the primes `≤ y`. -/
theorem errors_le {y : ℕ} (hy : 1 ≤ y) :
    4 ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 3 *
        (35 * Real.sqrt (Real.exp (20 * y))) ≤ 35 * Real.exp (20 * y) ∧
      4 ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 2 * 2 ≤ Real.exp (20 * y) := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  have hQ : primeProd (Nat.primesLE y) ≤ (4 : ℝ) ^ y := by
    rw [primeProd_primesLE]; exact_mod_cast primorial_le_four_pow y
  have hQ1 := one_le_primeProd (primes_of_primesLE y)
  have hcard : (4 : ℝ) ^ (Nat.primesLE y).card ≤ 4 ^ (y + 1) :=
    pow_le_pow_right₀ (by norm_num) (card_primesLE_le y)
  have hsT : Real.sqrt (Real.exp (20 * y)) = Real.exp (10 * y) := by
    rw [show 20 * (y : ℝ) = (2 : ℕ) * (10 * y) by push_cast; ring, Real.exp_nat_mul,
      Real.sqrt_sq (Real.exp_pos _).le]
  have hl := log_four_lt
  have hl0 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  constructor
  · have h1 : (4 : ℝ) ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 3 ≤
        4 ^ (y + 1) * ((4 : ℝ) ^ y) ^ 3 :=
      mul_le_mul hcard (pow_le_pow_left₀ (by linarith) hQ 3) (by positivity) (by positivity)
    have h2 : (4 : ℝ) ^ (y + 1) * ((4 : ℝ) ^ y) ^ 3 * Real.exp (10 * y) ≤ Real.exp (20 * y) := by
      rw [← pow_mul, ← pow_add, four_pow_eq_exp, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    rw [hsT]
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (10 * (y : ℝ))).le
    nlinarith
  · have h1 : (4 : ℝ) ^ (Nat.primesLE y).card * primeProd (Nat.primesLE y) ^ 2 ≤
        4 ^ (y + 1) * ((4 : ℝ) ^ y) ^ 2 :=
      mul_le_mul hcard (pow_le_pow_left₀ (by linarith) hQ 2) (by positivity) (by positivity)
    have h2 : (4 : ℝ) ^ (y + 1) * ((4 : ℝ) ^ y) ^ 2 * 2 ≤ Real.exp (20 * y) := by
      rw [← pow_mul, ← pow_add, four_pow_eq_exp,
        show (2 : ℝ) = Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)], ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := Real.log_two_lt_d9
      push_cast
      nlinarith
    nlinarith

/-- **The resonance bound at `T = e^{20y}`.** If `Re ζ(½+it) ≤ B` on `[T, 2T]`, `B ≥ 0`, then
`∏_{p≤y} (1 + 1/(2√p)) ≤ 2B + 35`. -/
theorem prod_gain_le {y : ℕ} (hy : 1 ≤ y) {B : ℝ} (hB : 0 ≤ B)
    (hre : ∀ t ∈ Icc (Real.exp (20 * y)) (2 * Real.exp (20 * y)),
      (riemannZeta (linePt t)).re ≤ B) :
    ∏ p ∈ Nat.primesLE y, (1 + 1 / (2 * Real.sqrt p)) ≤ 2 * B + 35 := by
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast hy
  obtain ⟨T, hT⟩ : ∃ T, T = Real.exp (20 * y) := ⟨_, rfl⟩
  have hTy : 1 + 20 * (y : ℝ) ≤ T := by rw [hT]; linarith [Real.add_one_le_exp (20 * (y : ℝ))]
  have hT4 : 4 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  rw [← hT] at hre
  have hres := resGain_le_of_re_le hT4 hB (primes_of_primesLE y) hre
  obtain ⟨hEA, hEB⟩ := errors_le hy
  rw [← hT] at hEA hEB
  rw [resGain_eq] at hres
  obtain ⟨G, hG⟩ : ∃ G, G = ∏ p ∈ Nat.primesLE y, (1 + 1 / (2 * Real.sqrt p)) := ⟨_, rfl⟩
  rw [← hG] at hres ⊢
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 ^ (Nat.primesLE y).card := ⟨_, rfl⟩
  rw [← hc] at hres
  have hc1 : (1 : ℝ) ≤ c := by rw [hc]; exact one_le_pow₀ (by norm_num)
  have h1 : T * (c * G) - 35 * T ≤ B * (c * T + T) := by
    have := mul_le_mul_of_nonneg_left hEB hB
    nlinarith
  have h2 : c * G - 35 ≤ B * (c + 1) := by
    have h3 : T * (c * G - 35) ≤ T * (B * (c + 1)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hT0
  have h3 : c * G ≤ c * (2 * B + 35) := by nlinarith
  exact le_of_mul_le_mul_left h3 (by linarith)

/-- The gain is at least `exp(N³/64)` at `y = N⁸`, `N ≥ 5`. -/
theorem exp_le_prod_gain {N : ℕ} (hN : 5 ≤ N) :
    Real.exp ((N : ℝ) ^ 3 / 64) ≤ ∏ p ∈ Nat.primesLE (N ^ 8), (1 + 1 / (2 * Real.sqrt p)) := by
  have hN5 : (5 : ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hy2 : 2 ≤ N ^ 8 := by
    have : 2 ≤ 5 ^ 8 := by norm_num
    exact this.trans (Nat.pow_le_pow_left hN 8)
  have hyR : ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 := by push_cast; ring
  have hS : (N : ℝ) ^ 3 / 16 ≤ ∑ p ∈ Nat.primesLE (N ^ 8), 1 / Real.sqrt p := by
    refine le_trans ?_ (theta_div_le_sum hy2)
    have hth := half_le_theta hN
    have hsq : Real.sqrt (((N ^ 8 : ℕ) : ℝ)) = (N : ℝ) ^ 4 := by
      rw [hyR, show (N : ℝ) ^ 8 = ((N : ℝ) ^ 4) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    have hlog : Real.log (((N ^ 8 : ℕ) : ℝ)) ≤ 8 * N := by
      rw [hyR, Real.log_pow]
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < N)
      push_cast; linarith
    have hy2R : (2 : ℝ) ≤ ((N ^ 8 : ℕ) : ℝ) := by exact_mod_cast hy2
    have hlog0 : 0 < Real.log (((N ^ 8 : ℕ) : ℝ)) := Real.log_pos (by linarith)
    rw [hsq, le_div_iff₀ (by positivity)]
    have h4 : (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * Real.log (((N ^ 8 : ℕ) : ℝ))) ≤
        (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * (8 * N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
    have h5 : (N : ℝ) ^ 3 / 16 * ((N : ℝ) ^ 4 * (8 * N)) = (N : ℝ) ^ 8 / 2 := by ring
    linarith
  refine le_trans ?_ (exp_sum_le_prod (primes_of_primesLE _))
  apply Real.exp_le_exp.mpr
  rw [show ∑ p ∈ Nat.primesLE (N ^ 8), 1 / (4 * Real.sqrt p) =
      (∑ p ∈ Nat.primesLE (N ^ 8), 1 / Real.sqrt p) / 4 by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun p _ => by ring]
  linarith

/-- **Large values of `Re ζ` on the critical line.** For every `K` and `T₀` there is `t ≥ T₀` with
`Re ζ(½+it) > log t + K`. -/
theorem exists_log_add_lt_re_zeta (K T₀ : ℝ) :
    ∃ t : ℝ, T₀ ≤ t ∧ Real.log t + K < (riemannZeta (linePt t)).re := by
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (64 : ℝ) ^ 4 * 24 * (77 + 2 * |K|) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max 5 T₀) A)
  have hN5 : (5 : ℝ) ≤ N := le_of_lt (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hN)
  have hNT : T₀ ≤ N := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hN)
  have hNA : A < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN5' : 5 ≤ N := by exact_mod_cast hN5
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hy1 : 1 ≤ N ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hyR : ((N ^ 8 : ℕ) : ℝ) = (N : ℝ) ^ 8 := by push_cast; ring
  have hNy : (N : ℝ) ≤ (N : ℝ) ^ 8 := le_self_pow₀ hN1 (by norm_num)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 20 * (N : ℝ) ^ 8 + Real.log 2 + |K| := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hre : ∀ t ∈ Icc (Real.exp (20 * ((N ^ 8 : ℕ) : ℝ)))
      (2 * Real.exp (20 * ((N ^ 8 : ℕ) : ℝ))), (riemannZeta (linePt t)).re ≤ B := by
    intro t ht
    have hTlow : 1 + 20 * (N : ℝ) ^ 8 ≤ Real.exp (20 * ((N ^ 8 : ℕ) : ℝ)) := by
      rw [hyR]; linarith [Real.add_one_le_exp (20 * (N : ℝ) ^ 8)]
    have ht0 : T₀ ≤ t := by linarith [ht.1]
    have h := hcon t ht0
    have hlog : Real.log t ≤ Real.log (2 * Real.exp (20 * ((N ^ 8 : ℕ) : ℝ))) :=
      Real.log_le_log (by linarith [ht.1]) ht.2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp, hyR] at hlog
    rw [hB]; linarith [le_abs_self K]
  have hgain := prod_gain_le hy1 hB0 hre
  have hexp := (exp_le_prod_gain hN5').trans hgain
  have hpow := Real.pow_div_factorial_le_exp ((N : ℝ) ^ 3 / 64) (by positivity) 4
  have hfact : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfact] at hpow
  have hBle : 2 * B + 35 ≤ (77 + 2 * |K|) * (N : ℝ) ^ 8 := by
    have hN8 : (1 : ℝ) ≤ (N : ℝ) ^ 8 := one_le_pow₀ hN1
    have := Real.log_two_lt_d9
    have hK := abs_nonneg K
    rw [hB]; nlinarith
  have hfin : ((N : ℝ) ^ 3 / 64) ^ 4 / 24 ≤ (77 + 2 * |K|) * (N : ℝ) ^ 8 := by linarith
  have hN4 : (N : ℝ) ≤ (N : ℝ) ^ 4 := le_self_pow₀ hN1 (by norm_num)
  have hN8pos : 0 < (N : ℝ) ^ 8 := by positivity
  have e : ((N : ℝ) ^ 3 / 64) ^ 4 / 24 = (N : ℝ) ^ 4 * (N : ℝ) ^ 8 / ((64 : ℝ) ^ 4 * 24) := by ring
  rw [e, div_le_iff₀ (by positivity)] at hfin
  have hgt : A * (N : ℝ) ^ 8 < (N : ℝ) ^ 4 * (N : ℝ) ^ 8 :=
    mul_lt_mul_of_pos_right (lt_of_lt_of_le hNA hN4) hN8pos
  rw [hA] at hgt
  nlinarith

end RHTower.ZetaResonator
