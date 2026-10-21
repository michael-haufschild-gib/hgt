import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowFloorPolarAsymptotics
import GaloisForLFunctions.RHTower.PrimeBlindPoleCurvatureFloor
import GaloisForLFunctions.HTGeometry.KroneckerWeylDensity
import Zeta23.FromPNTPlus.Mertens

/-!
# The Liouville mirror of the window spectrum

For tests supported in intervals of length `L ≤ log N` the window deviations `(A − W)/‖c‖²` are
values of the prime-side form `Σ_{n<N} Λ(n) L_n`. Modulating a test by `e^{iξu}` keeps its mass and
its window and multiplies its correlation at `±log n` by `n^{±iξ}`. Since the `log p` are linearly
independent over `ℚ`, Kronecker's theorem gives one `ξ` with `p^{iξ}` as close to `−1` as wished for
every prime `p < N` at once; then `n^{iξ}` is close to the Liouville sign `(−1)^{Ω(n)}` on every
prime power `n < N`, and the modulated test has prime side

`−(Σ Λ(n) L_n) + 2 Σ_{Ω(n) even} Λ(n) L_n`:

every prime power changes sign except the squares `p^{2j}`, whose total atom is
`T(N) = Σ_{n<N, Ω(n) even} 2Λ(n)/√n = 2 Σ_{m²<N} Λ(m)/m ≤ 2 log N + O(1)`.

**Theorem** (`exists_mirror_mem_windowDeviations`). For every window deviation `x` and `δ > 0`
there is a window deviation `x'` of the same length with `|x + x'| ≤ 2T(N) + δ`.

**Consequences.**
* The window spectrum is symmetric to `O(log X)`: `|c(L) + floor(L)| ≤ 2T(N)`
  (`abs_windowCeiling_add_windowFloor_le`), `≤ 4L + C` for large `L`.
* The floor reads RH and the zero width as the ceiling does: `floor(L) ≥ −e^{L/2} − O(L)` forces
  RH (`riemannHypothesis_of_windowDeviations_ge`), and `floor(L) ≥ −e^{L/2} − O(Le^{θL})` forces
  every zero into `Re ρ ≤ ½ + θ` (`xiZeroHalfPlaneBound_of_windowDeviations_ge`).
* The extremes of the window spectrum see the prime atoms only through their sizes: the same
  modulation turns the prime measure into its Liouville twist `Λ(n)λ(n)/√n` up to the squares, so a
  statement about window extremes coarser than `O(log X)` cannot separate the two.
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate ArithmeticFunction.Omega

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Modulated tests -/

theorem contDiff_phase (ξ : ℝ) :
    ContDiff ℝ 2 (fun u : ℝ => Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I)) :=
  Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
    contDiff_const)

/-- The modulated test `e^{iξu} f(u)`. -/
def modulatedTest (ξ : ℝ) (f : WeilTestFn) : WeilTestFn :=
  ⟨fun u => Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I) * f.1 u, (contDiff_phase ξ).mul f.2.1,
    f.2.2.mul_left⟩

theorem modulatedTest_apply (ξ : ℝ) (f : WeilTestFn) (u : ℝ) :
    (modulatedTest ξ f).1 u = Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I) * f.1 u := rfl

/-- Modulation multiplies the autocorrelation at `y` by `e^{iξy}`. -/
theorem weilTest_modulatedTest (ξ : ℝ) (f : WeilTestFn) (y : ℝ) :
    EF.weilTest (modulatedTest ξ f).1 (modulatedTest ξ f).1 y =
      Complex.exp (((ξ * y : ℝ) : ℂ) * Complex.I) * EF.weilTest f.1 f.1 y := by
  rw [WeilSpectral.weilTest_apply, WeilSpectral.weilTest_apply, ← integral_const_mul]
  congr 1; funext u
  rw [modulatedTest_apply, modulatedTest_apply, map_mul, ← Complex.exp_conj]
  have hc : conj (((ξ * (u - y) : ℝ) : ℂ) * Complex.I) = -(((ξ * (u - y) : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  have e : Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-(((ξ * (u - y) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((ξ * y : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hc]
  calc Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I) * f.1 u *
        (Complex.exp (-(((ξ * (u - y) : ℝ) : ℂ) * Complex.I)) * conj (f.1 (u - y)))
      = (Complex.exp (((ξ * u : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(((ξ * (u - y) : ℝ) : ℂ) * Complex.I))) * (f.1 u * conj (f.1 (u - y))) := by
        ring
    _ = _ := by rw [e]

theorem norm_modulatedTest (ξ : ℝ) (f : WeilTestFn) (u : ℝ) :
    ‖(modulatedTest ξ f).1 u‖ = ‖f.1 u‖ := by
  rw [modulatedTest_apply, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem modulatedTest_injective (ξ : ℝ) : Function.Injective (modulatedTest ξ) := by
  intro f g h
  apply Subtype.ext
  funext u
  have := congrArg (fun F : WeilTestFn => F.1 u) h
  simp only [modulatedTest_apply] at this
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) this

/-! ### 2. Kronecker: one modulation turns every prime into `−1` -/

/-- **Kronecker for the primes below `N`.** For every `ε > 0` some `ξ` has `‖p^{iξ} + 1‖ < ε` for
every prime `p < N`. -/
theorem exists_phase_near_neg_one (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ℝ, ∀ p ∈ N.primesBelow,
      ‖Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) + 1‖ < ε := by
  classical
  have hind : LinearIndependent ℚ (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
    linearIndependent_log_primes.comp
      (fun x : (N.primesBelow : Finset ℕ) =>
        (⟨(x : ℕ), (Nat.mem_primesBelow.mp x.2).2⟩ : Nat.Primes))
      (fun _ _ hab => Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) hab))
  obtain ⟨t, ht⟩ := kronecker_approx hind (fun _ => Real.pi) hε
  refine ⟨t, fun p hp => ?_⟩
  have h := ht ⟨p, hp⟩
  simp only [expChar, Complex.exp_pi_mul_I, sub_neg_eq_add] at h
  rwa [mul_comm t]

/-- `‖z^k − w^k‖ ≤ k‖z − w‖` on the closed unit disc. -/
theorem norm_pow_sub_pow_le_of_norm_le_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ k * ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (k + 1) - w ^ (k + 1) = z * (z ^ k - w ^ k) + (z - w) * w ^ k := by ring
    have hwk : ‖w ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
    rw [e]
    calc ‖z * (z ^ k - w ^ k) + (z - w) * w ^ k‖
        ≤ ‖z‖ * ‖z ^ k - w ^ k‖ + ‖z - w‖ * ‖w ^ k‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_mul, norm_mul]
      _ ≤ 1 * (k * ‖z - w‖) + ‖z - w‖ * 1 := by
          have h1 := mul_le_mul hz ih (norm_nonneg _) zero_le_one
          have h2 := mul_le_mul_of_nonneg_left hwk (norm_nonneg (z - w))
          linarith
      _ = ((k + 1 : ℕ) : ℝ) * ‖z - w‖ := by push_cast; ring

/-- On a prime power `n = p^k < N`, `‖n^{iξ} − (−1)^k‖ ≤ kε` when `‖p^{iξ} + 1‖ ≤ ε`. -/
theorem norm_phase_prime_pow_sub_le {ξ ε : ℝ} {p k : ℕ}
    (hp : ‖Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) + 1‖ ≤ ε) :
    ‖Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) - (-1) ^ k‖ ≤ k * ε := by
  have e : Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) ^ k := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; rw [Real.log_pow]; push_cast; ring
  rw [e]
  refine (norm_pow_sub_pow_le_of_norm_le_one (by rw [Complex.norm_exp_ofReal_mul_I])
    (by simp) k).trans ?_
  rw [sub_neg_eq_add]
  exact mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg k)

/-! ### 3. The mirror of one test -/

/-- The total atom of the squares: `T(N) = Σ_{n<N, Ω(n) even} 2Λ(n)/√n`. -/
def mirrorDefect (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 2 N, if Even (Ω n) then 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n
    else 0

/-- The even-exponent part `Σ_{n<N, Ω(n) even} Λ(n) L_n` of the prime side of a test. -/
def evenPrimeSide (N : ℕ) (f : WeilTestFn) : ℝ :=
  ∑ n ∈ Finset.Ico 2 N, if Even (Ω n) then (ArithmeticFunction.vonMangoldt n : ℝ) * logValue f.1 n
    else 0

/-- The crude phase constant `K(N) = Σ_{n<N} 2nΛ(n)`. -/
def phaseConst (N : ℕ) : ℝ := ∑ n ∈ Finset.Ico 2 N, 2 * (n : ℝ) * ArithmeticFunction.vonMangoldt n

theorem phaseConst_nonneg (N : ℕ) : 0 ≤ phaseConst N :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg

theorem abs_logValue_le (f : WeilTestFn) {n : ℕ} (hn : 1 ≤ n) :
    |logValue f.1 n| ≤ 2 * testMass f / Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [logValue, abs_div, abs_of_pos hs]
  gcongr
  refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
  linarith [norm_weilTest_self_le_testMass f (Real.log n), norm_weilTest_self_le_testMass f (-Real.log n)]

theorem abs_evenPrimeSide_le (N : ℕ) (f : WeilTestFn) :
    |evenPrimeSide N f| ≤ mirrorDefect N * testMass f := by
  unfold evenPrimeSide mirrorDefect
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  split_ifs
  · rw [abs_mul, abs_of_nonneg hΛ]
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * |logValue f.1 n|
        ≤ ArithmeticFunction.vonMangoldt n * (2 * testMass f / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left (abs_logValue_le f hn1) hΛ
      _ = 2 * ArithmeticFunction.vonMangoldt n / Real.sqrt n * testMass f := by ring
  · simp

/-- **The mirror of one test.** If `‖p^{iξ} + 1‖ ≤ ε` for every prime `p < N` and the test lives in
a window of length `L ≤ log N`, the prime sides satisfy
`|P(e^{iξ·}f) + P(f) − 2 P_even(f)| ≤ ε K(N) ‖f‖²`. -/
theorem abs_primeSide_modulated_add_le {f : WeilTestFn} {a L : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) {N : ℕ} (hN : L ≤ Real.log N) {ξ ε : ℝ}
    (hε : 0 ≤ ε)
    (hξ : ∀ p ∈ N.primesBelow, ‖Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) + 1‖ ≤ ε) :
    |linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (logVector (modulatedTest ξ f)) +
        linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (logVector f) - 2 * evenPrimeSide N f| ≤ ε * phaseConst N * testMass f := by
  have hsupp' : ∀ u, (modulatedTest ξ f).1 u ≠ 0 → u ∈ Ioo a (a + L) := fun u hu =>
    hsupp u (right_ne_zero_of_mul hu)
  rw [primeSide_eq_sum_of_window hsupp' hN, primeSide_eq_sum_of_window hsupp hN, evenPrimeSide,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, phaseConst, Finset.mul_sum,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn2 := (Finset.mem_Ico.mp hn).1
  have hnN := (Finset.mem_Ico.mp hn).2
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hM : 0 ≤ testMass f := integral_nonneg fun _ => sq_nonneg _
  by_cases hpp : IsPrimePow n
  swap
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]; simp
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hpN : p ∈ N.primesBelow := Nat.mem_primesBelow.mpr ⟨lt_of_le_of_lt
    (Nat.le_self_pow hk.ne' p) hnN, hp⟩
  have hΩ : Ω (p ^ k) = k := ArithmeticFunction.cardFactors_apply_prime_pow hp
  -- the phase at `p^k` and its conjugate are within `kε` of the sign `(−1)^k`
  set z := Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) with hz
  have hzs : ‖z - (-1) ^ k‖ ≤ k * ε := norm_phase_prime_pow_sub_le (hξ p hpN)
  have hzc : Complex.exp (((ξ * -Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = conj z := by
    rw [hz, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; congr 1; push_cast; ring
  have hzs' : ‖conj z - (-1) ^ k‖ ≤ k * ε := by
    have : conj z - (-1) ^ k = conj (z - (-1) ^ k) := by simp [map_sub, map_pow, map_neg, map_one]
    rw [this, Complex.norm_conj]; exact hzs
  have hk1 : ((p ^ k : ℕ) : ℝ) ≥ 1 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hs1 : 1 ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := by rw [Real.one_le_sqrt]; exact hk1
  have hkn : (k : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le
  set kp := EF.weilTest f.1 f.1 (Real.log ((p ^ k : ℕ) : ℝ))
  set km := EF.weilTest f.1 f.1 (-Real.log ((p ^ k : ℕ) : ℝ))
  have hkp : ‖kp‖ ≤ testMass f := norm_weilTest_self_le_testMass f _
  have hkm : ‖km‖ ≤ testMass f := norm_weilTest_self_le_testMass f _
  -- the modulated node value
  have hmod : logValue (modulatedTest ξ f).1 (p ^ k) =
      (z * kp + conj z * km).re / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [logValue, weilTest_modulatedTest, weilTest_modulatedTest, ← hzc]
  have hD : logValue (modulatedTest ξ f).1 (p ^ k) + logValue f.1 (p ^ k) -
      2 * (if Even k then logValue f.1 (p ^ k) else 0) =
      ((z - (-1) ^ k) * kp + (conj z - (-1) ^ k) * km).re / Real.sqrt ((p ^ k : ℕ) : ℝ) := by
    rw [hmod, logValue]
    have hre : ((z - (-1) ^ k) * kp + (conj z - (-1) ^ k) * km).re =
        (z * kp + conj z * km).re - (-1 : ℝ) ^ k * (kp + km).re := by
      simp only [sub_mul, Complex.add_re, Complex.sub_re]
      have : ∀ w : ℂ, ((-1 : ℂ) ^ k * w).re = (-1 : ℝ) ^ k * w.re := fun w => by
        rw [show ((-1 : ℂ) ^ k) = (((-1 : ℝ) ^ k : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
      rw [this, this]; ring
    rw [hre]
    rcases Nat.even_or_odd k with he | ho
    · rw [if_pos he, he.neg_one_pow]; ring
    · rw [if_neg (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow]; ring
  have hterm : (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * logValue (modulatedTest ξ f).1 (p ^ k) +
      (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * logValue f.1 (p ^ k) -
      2 * (if Even (Ω (p ^ k)) then (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) *
        logValue f.1 (p ^ k) else 0) =
      (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) *
        (logValue (modulatedTest ξ f).1 (p ^ k) + logValue f.1 (p ^ k) -
          2 * (if Even k then logValue f.1 (p ^ k) else 0)) := by
    rw [hΩ]; split_ifs <;> ring
  rw [hterm, hD, abs_mul, abs_of_nonneg hΛ]
  have hnum : |((z - (-1) ^ k) * kp + (conj z - (-1) ^ k) * km).re| ≤ 2 * (k * ε) * testMass f := by
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul, norm_mul]
    have h1 := mul_le_mul hzs hkp (norm_nonneg _) (by positivity)
    have h2 := mul_le_mul hzs' hkm (norm_nonneg _) (by positivity)
    linarith
  have hfrac : |((z - (-1) ^ k) * kp + (conj z - (-1) ^ k) * km).re / Real.sqrt ((p ^ k : ℕ) : ℝ)| ≤
      2 * (k * ε) * testMass f := by
    have hsq : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := by linarith
    rw [abs_div, abs_of_pos hsq, div_le_iff₀ hsq]
    have : 0 ≤ 2 * (k * ε) * testMass f := by positivity
    nlinarith
  calc (ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) * |_| ≤
        ArithmeticFunction.vonMangoldt (p ^ k) * (2 * (k * ε) * testMass f) :=
        mul_le_mul_of_nonneg_left hfrac hΛ
    _ ≤ ArithmeticFunction.vonMangoldt (p ^ k) * (2 * (((p ^ k : ℕ) : ℝ) * ε) * testMass f) := by
        gcongr
    _ = ε * (2 * ((p ^ k : ℕ) : ℝ) * ArithmeticFunction.vonMangoldt (p ^ k)) * testMass f := by ring

/-! ### 4. The mirror of a combination -/

/-- The prime side of a combination is the weighted sum of the prime sides of its tests. -/
theorem nodeArchEnergy_sub_weilEnergy_eq_sum (c : WeilTestFn →₀ ℝ) :
    nodeArchEnergy c - weilEnergy c = c.sum fun f t => t *
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
  rw [nodeArchEnergy_eq_weilEnergy_add, add_sub_cancel_left, nodeVector_eq,
    linearCombination_apply ℝ (v := logVector), map_finsuppSum]
  refine Finsupp.sum_congr fun f _ => ?_
  rw [map_smul, smul_eq_mul]

theorem massOf_eq_sum (c : WeilTestFn →₀ ℝ) : massOf c = c.sum fun f t => t * testMass f := rfl

/-- **The Liouville mirror.** Every window deviation `x` has a mirror `x'` of the same length with
`|x + x'| ≤ 2T(N) + δ`, for `L ≤ log N` and any `δ > 0`. -/
theorem exists_mirror_mem_windowDeviations {L x : ℝ} (hx : x ∈ windowDeviations L) {N : ℕ}
    (hN : L ≤ Real.log N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x' ∈ windowDeviations L, |x + x'| ≤ 2 * mirrorDefect N + δ := by
  classical
  obtain ⟨c, hc, hs, hpos, rfl⟩ := hx
  set ε := δ / (phaseConst N + 1) with hεdef
  have hK := phaseConst_nonneg N
  have hε : 0 < ε := div_pos hδ (by linarith)
  obtain ⟨ξ, hξ⟩ := exists_phase_near_neg_one N hε
  set c' := Finsupp.mapDomain (modulatedTest ξ) c with hc'
  have hinj := modulatedTest_injective ξ
  -- sums over the mirrored combination
  have hsum : ∀ (h : WeilTestFn → ℝ), (c'.sum fun g t => t * h g) =
      c.sum fun f t => t * h (modulatedTest ξ f) := fun h =>
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  have hmass : massOf c' = massOf c := by
    rw [massOf_eq_sum, massOf_eq_sum, hsum]
    refine Finsupp.sum_congr fun f _ => ?_
    simp only [testMass, norm_modulatedTest]
  refine ⟨(nodeArchEnergy c' - weilEnergy c') / massOf c', ⟨c', fun g => ?_, fun g hg => ?_,
    hmass ▸ hpos, rfl⟩, ?_⟩
  · by_cases hg : g ∈ Set.range (modulatedTest ξ)
    · obtain ⟨f, rfl⟩ := hg
      rw [hc', Finsupp.mapDomain_apply hinj]; exact hc f
    · rw [hc', Finsupp.mapDomain_notin_range _ _ hg]
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    obtain ⟨a, ha⟩ := hs f hf
    exact ⟨a, fun u hu => ha u (right_ne_zero_of_mul hu)⟩
  · rw [hmass, ← add_div, abs_div, abs_of_pos hpos, div_le_iff₀ hpos,
      nodeArchEnergy_sub_weilEnergy_eq_sum, nodeArchEnergy_sub_weilEnergy_eq_sum, hsum,
      ← Finsupp.sum_add, massOf_eq_sum, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f hf => ?_)
    obtain ⟨a, ha⟩ := hs f hf
    have hcf := hc f
    have h1 := abs_primeSide_modulated_add_le ha hN hε.le (fun p hp => (hξ p hp).le) (ξ := ξ)
    have h2 := abs_evenPrimeSide_le N f
    have hM : 0 ≤ testMass f := integral_nonneg fun _ => sq_nonneg _
    have hεK : ε * phaseConst N ≤ δ := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    set P₁ := linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
      (logVector f)
    set P₂ := linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
      (logVector (modulatedTest ξ f))
    have hsplit : c f * P₁ + c f * P₂ =
        c f * (P₂ + P₁ - 2 * evenPrimeSide N f) + c f * (2 * evenPrimeSide N f) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hcf, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    have e1 : c f * |P₂ + P₁ - 2 * evenPrimeSide N f| ≤ c f * (δ * testMass f) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right hεK hM)) hcf
    have e2 : c f * (2 * |evenPrimeSide N f|) ≤ c f * (2 * (mirrorDefect N * testMass f)) :=
      mul_le_mul_of_nonneg_left (by linarith) hcf
    nlinarith

/-! ### 5. The size of the squares -/

/-- A prime power with an even number of prime factors is the square of a prime power `m`, with
`Λ(m²) = Λ(m)` and `√(m²) = m`. -/
theorem mirror_term_eq {n : ℕ} (hpp : IsPrimePow n) (he : Even (Ω n)) :
    n = Nat.sqrt n ^ 2 ∧ 2 * (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n =
      2 * (ArithmeticFunction.vonMangoldt (Nat.sqrt n) : ℝ) / (Nat.sqrt n : ℝ) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  rw [ArithmeticFunction.cardFactors_apply_prime_pow hp] at he
  obtain ⟨j, rfl⟩ := he
  have hj : 0 < j := by omega
  have hsq : p ^ (j + j) = (p ^ j) ^ 2 := by rw [← pow_mul]; ring_nf
  have hsqrt : Nat.sqrt (p ^ (j + j)) = p ^ j := by rw [hsq]; exact Nat.sqrt_eq' _
  refine ⟨by rw [hsqrt, hsq], ?_⟩
  rw [hsqrt, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_pow hj.ne', hsq]
  push_cast
  rw [Real.sqrt_sq (by positivity)]

/-- **The squares cost `O(log N)`**: `T(N) ≤ 2(log N + log 4 + 4)`. -/
theorem mirrorDefect_le {N : ℕ} (hN : 1 ≤ N) :
    mirrorDefect N ≤ 2 * (Real.log N + (Real.log 4 + 4)) := by
  classical
  set g : ℕ → ℝ := fun n => if Even (Ω n) then
    2 * (ArithmeticFunction.vonMangoldt n : ℝ) / Real.sqrt n else 0 with hg
  set S := (Finset.Ico 2 N).filter (fun n => g n ≠ 0) with hS
  have hmem : ∀ n ∈ S, IsPrimePow n ∧ Even (Ω n) := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    by_cases he : Even (Ω n)
    · refine ⟨?_, he⟩
      by_contra hpp
      apply h
      simp [hg, he, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
    · exact absurd (by simp [hg, he]) h
  have hinj : Set.InjOn Nat.sqrt S := fun n₁ h₁ n₂ h₂ h => by
    rw [(mirror_term_eq (hmem n₁ h₁).1 (hmem n₁ h₁).2).1,
      (mirror_term_eq (hmem n₂ h₂).1 (hmem n₂ h₂).2).1, h]
  have hsub : S.image Nat.sqrt ⊆ Finset.Ioc 0 N := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hnN := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).2
    have hn2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).1).1
    rw [Finset.mem_Ioc]
    exact ⟨Nat.sqrt_pos.mpr (by omega), (Nat.sqrt_le_self n).trans hnN.le⟩
  have hnn : ∀ m : ℕ, 0 ≤ 2 * (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) := fun m =>
    div_nonneg (mul_nonneg zero_le_two ArithmeticFunction.vonMangoldt_nonneg) (Nat.cast_nonneg m)
  have hmert := Mertens.sum_mangoldt_div_eq_log (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at hmert
  calc mirrorDefect N = ∑ n ∈ Finset.Ico 2 N, g n := rfl
    _ = ∑ n ∈ S, g n := (Finset.sum_filter_ne_zero _).symm
    _ = ∑ n ∈ S, 2 * (ArithmeticFunction.vonMangoldt (Nat.sqrt n) : ℝ) / (Nat.sqrt n : ℝ) :=
        Finset.sum_congr rfl fun n hn => by
          rw [hg]; simp only [if_pos (hmem n hn).2]
          exact (mirror_term_eq (hmem n hn).1 (hmem n hn).2).2
    _ = ∑ m ∈ S.image Nat.sqrt, 2 * (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) :=
        (Finset.sum_image (f := fun m : ℕ => 2 * (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ))
          hinj).symm
    _ ≤ ∑ m ∈ Finset.Ioc 0 N, 2 * (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => hnn m
    _ = 2 * ∑ m ∈ Finset.Ioc 0 N, (ArithmeticFunction.vonMangoldt m : ℝ) / (m : ℝ) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ 2 * (Real.log N + (Real.log 4 + 4)) := by
        have := (abs_le.mp hmert).2
        linarith

/-- With `N = ⌈e^L⌉`: `L ≤ log N` and `2T(N) ≤ 4L + 4(log 8 + 4)` for `L ≥ 0`. -/
theorem mirror_cutoff {L : ℝ} (hL : 0 ≤ L) :
    L ≤ Real.log ⌈Real.exp L⌉₊ ∧ 2 * mirrorDefect ⌈Real.exp L⌉₊ ≤ 4 * L + 4 * (Real.log 8 + 4) := by
  have he1 : 1 ≤ Real.exp L := Real.one_le_exp hL
  have hN1 : 1 ≤ ⌈Real.exp L⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; linarith)
  have hle : Real.exp L ≤ ⌈Real.exp L⌉₊ := Nat.le_ceil _
  have hlt : (⌈Real.exp L⌉₊ : ℝ) < Real.exp L + 1 := Nat.ceil_lt_add_one (by linarith)
  have hpos : (0 : ℝ) < ⌈Real.exp L⌉₊ := by linarith
  refine ⟨?_, ?_⟩
  · rw [Real.le_log_iff_exp_le hpos]; exact hle
  · have hlog : Real.log ⌈Real.exp L⌉₊ ≤ L + Real.log 2 := by
      calc Real.log ⌈Real.exp L⌉₊ ≤ Real.log (Real.exp L * 2) := Real.log_le_log hpos (by linarith)
        _ = L + Real.log 2 := by rw [Real.log_mul (Real.exp_pos L).ne' two_ne_zero, Real.log_exp]
    have h := mirrorDefect_le hN1
    have h8 : Real.log 8 = Real.log 2 + Real.log 4 := by
      rw [← Real.log_mul two_ne_zero (by norm_num)]; norm_num
    linarith

/-! ### 6. Consequences -/

theorem bddAbove_windowDeviations {L : ℝ} (hL : 0 ≤ L) : BddAbove (windowDeviations L) :=
  ⟨(Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2, fun y ⟨c, hc, hs, hm, hy⟩ => by
    rw [hy, div_le_iff₀ hm]
    exact (le_abs_self _).trans (abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL hs)⟩

theorem bddBelow_windowDeviations {L : ℝ} (hL : 0 ≤ L) : BddBelow (windowDeviations L) :=
  ⟨-((Real.log 4 + 4) * Real.exp (L / 2) + (1 + L) ^ 2), fun y ⟨c, hc, hs, hm, hy⟩ => by
    rw [hy, le_div_iff₀ hm]
    have := abs_nodeArchEnergy_sub_weilEnergy_le_chebyshev hc hL hs
    linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]⟩

/-- **The window spectrum is mirror-symmetric up to the squares**: `|c(L) + floor(L)| ≤ 2T(N)`. -/
theorem abs_windowCeiling_add_windowFloor_le {L : ℝ} (hL : 0 ≤ L)
    (hne : (windowDeviations L).Nonempty) {N : ℕ} (hN : L ≤ Real.log N) :
    |windowCeiling L + windowFloor L| ≤ 2 * mirrorDefect N := by
  have ha := bddAbove_windowDeviations hL
  have hb := bddBelow_windowDeviations hL
  rw [abs_le]
  constructor
  · -- `floor ≥ −c − 2T`: every deviation `x` has a mirror `x' ≤ c`
    have key : ∀ x ∈ windowDeviations L, -windowCeiling L - 2 * mirrorDefect N ≤ x := by
      intro x hx
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨x', hx', h⟩ := exists_mirror_mem_windowDeviations hx hN hδ
      have := le_csSup ha hx'
      unfold windowCeiling
      linarith [neg_abs_le (x + x')]
    have := le_csInf hne key
    unfold windowFloor
    linarith
  · -- `c ≤ −floor + 2T`: every deviation `x` has a mirror `x' ≥ floor`
    have key : ∀ x ∈ windowDeviations L, x ≤ -windowFloor L + 2 * mirrorDefect N := by
      intro x hx
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      obtain ⟨x', hx', h⟩ := exists_mirror_mem_windowDeviations hx hN hδ
      have := csInf_le hb hx'
      unfold windowFloor
      linarith [le_abs_self (x + x')]
    have := csSup_le hne key
    unfold windowCeiling
    linarith

/-- **The floor bounds the ceiling.** A lower bound `−F` on the deviations of length `L ≥ 0` gives
the upper bound `F + 4L + 4(log 8 + 4)`. -/
theorem windowDeviations_le_of_ge {L F : ℝ} (hL : 0 ≤ L)
    (h : ∀ x ∈ windowDeviations L, -F ≤ x) :
    ∀ x ∈ windowDeviations L, x ≤ F + (4 * L + 4 * (Real.log 8 + 4)) := by
  intro x hx
  obtain ⟨hN, hT⟩ := mirror_cutoff hL
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨x', hx', hmir⟩ := exists_mirror_mem_windowDeviations hx hN hδ
  have := h x' hx'
  linarith [le_abs_self (x + x')]

/-- **The floor criterion.** If the window floor stays above `−e^{L/2} − B(1+L)`, RH holds. -/
theorem riemannHypothesis_of_windowDeviations_ge {B : ℝ}
    (h : ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L, -(Real.exp (L / 2) + B * (1 + L)) ≤ x) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_windowDeviations_le (B := B + 4 * (Real.log 8 + 4)) ?_
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0 x hx
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have := windowDeviations_le_of_ge hL0 hL x hx
  nlinarith

/-- **The floor reads the zero width.** If `floor(L) ≥ −e^{L/2} − B(1+L)e^{θL}` eventually,
`0 ≤ θ < 1/2`, then every zero of `Ξ` has `Re ρ ≤ 1/2 + θ`. -/
theorem xiZeroHalfPlaneBound_of_windowDeviations_ge {θ B : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1 / 2)
    (h : ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L,
      -(Real.exp (L / 2) + B * (1 + L) * Real.exp (θ * L)) ≤ x) :
    XiZeroHalfPlaneBound θ := by
  refine xiZeroHalfPlaneBound_of_windowDeviations_le hθ hθ' (B := B + 4 * (Real.log 8 + 4)) ?_
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with L hL hL0 x hx
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (θ * L) := Real.one_le_exp (by positivity)
  have := windowDeviations_le_of_ge hL0 hL x hx
  have hc : 4 * L + 4 * (Real.log 8 + 4) ≤ 4 * (Real.log 8 + 4) * (1 + L) * Real.exp (θ * L) := by
    have : 4 * L + 4 * (Real.log 8 + 4) ≤ 4 * (Real.log 8 + 4) * (1 + L) := by nlinarith
    exact this.trans (le_mul_of_one_le_right (by positivity) he)
  nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty
