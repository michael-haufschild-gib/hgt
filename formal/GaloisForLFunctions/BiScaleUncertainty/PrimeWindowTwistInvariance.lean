import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowLiouvilleMirror

/-!
# Window spectra are twist invariant

Twist the prime atoms by a unimodular completely multiplicative function `χ`: the twisted prime side
of a test is `Σ_n Λ(n) Re(χ(n) k(log n) + χ̄(n) k(−log n))/√n`. Examples are the Liouville sign
(`χ(p) = −1`), the vertical shifts `χ(n) = n^{iτ}` (the prime measure of `ζ(s + iτ)`), and a Dirichlet
character mod `q` extended by `χ(p) = 1` at the primes dividing `q`.

**Theorem** (`exists_twisted_near_windowDeviation`, `exists_windowDeviation_near_twisted`). For
every twist `χ` and every window length `L`, every window deviation of the prime measure is a limit of
twisted window deviations of the same length, and conversely. Hence the twisted window ceiling and
floor equal `c(L)` and `floor(L)` (`twistedWindowCeiling_eq`, `twistedWindowFloor_eq`).

**Consequences.** The window extremes of the prime measure of every twisted `L`-function equal those
of `ζ`: the twisted ceiling is `e^{L/2}(1 + o(1))` although the twisted measure has no polar main
term, its excess reads the zero width of `ζ` (`PrimeWindowCeilingWidthLaw`) and never that of the
twisted `L`-function. Window extremes see the prime atoms only through their sizes.

**Mechanism.** Modulation `f ↦ e^{iξu} f` keeps mass and window and multiplies the correlation at
`±log n` by `n^{±iξ}` (`phasedPrimeSide_modulatedTest`). The `log p`, `p < X`, are `ℚ`-independent, so
Kronecker's theorem gives `ξ` with `p^{iξ}` within `ε` of any prescribed unimodular targets; on a prime
power `p^k` the phase error is at most `kε` (`norm_pow_sub_pow_le_of_norm_le_one`), and the prime
side moves by at most `ε K(X) ‖f‖²` (`abs_phasedPrimeSide_sub_le`).
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Unimodular twists and phased prime sides -/

/-- A unimodular completely multiplicative twist of the prime atoms. -/
structure UnimodularTwist where
  /-- The twist. -/
  toFun : ℕ → ℂ
  map_one : toFun 1 = 1
  map_mul : ∀ m n, toFun (m * n) = toFun m * toFun n
  norm_prime : ∀ p, p.Prime → ‖toFun p‖ = 1

namespace UnimodularTwist

theorem map_pow (χ : UnimodularTwist) (p k : ℕ) : χ.toFun (p ^ k) = χ.toFun p ^ k := by
  induction k with
  | zero => simp [χ.map_one]
  | succ k ih => rw [pow_succ, χ.map_mul, ih, pow_succ]

theorem norm_primePow (χ : UnimodularTwist) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ‖χ.toFun (p ^ k)‖ = 1 := by
  rw [χ.map_pow, norm_pow, χ.norm_prime p hp, one_pow]

end UnimodularTwist

/-- The phased prime side `Σ_{2≤n<N} Λ(n) Re(a(n) k(log n) + ā(n) k(−log n))/√n`. -/
def phasedPrimeSide (a : ℕ → ℂ) (N : ℕ) (f : WeilTestFn) : ℝ :=
  ∑ n ∈ Finset.Ico 2 N, (ArithmeticFunction.vonMangoldt n : ℝ) *
    ((a n * EF.weilTest f.1 f.1 (Real.log n) + conj (a n) * EF.weilTest f.1 f.1 (-Real.log n)).re /
      Real.sqrt n)

/-- With the trivial phase the phased prime side is the prime side. -/
theorem phasedPrimeSide_one {f : WeilTestFn} {a₀ L : ℝ}
    (hsupp : ∀ u, f.1 u ≠ 0 → u ∈ Ioo a₀ (a₀ + L)) {N : ℕ} (hN : L ≤ Real.log N) :
    phasedPrimeSide (fun _ => 1) N f =
      linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
        (logVector f) := by
  rw [primeSide_eq_sum_of_window hsupp hN, phasedPrimeSide]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [logValue]

/-- **Modulation shifts the phases**: the phased prime side of `e^{iξu} f` is the prime side of `f`
with phases `a(n) n^{iξ}`. -/
theorem phasedPrimeSide_modulatedTest (a : ℕ → ℂ) (N : ℕ) (ξ : ℝ) (f : WeilTestFn) :
    phasedPrimeSide a N (modulatedTest ξ f) =
      phasedPrimeSide (fun n => a n * Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) N f := by
  unfold phasedPrimeSide
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [weilTest_modulatedTest, weilTest_modulatedTest]
  have hc : Complex.exp (((ξ * -Real.log n : ℝ) : ℂ) * Complex.I) =
      conj (Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]; congr 1; push_cast; ring
  rw [hc, map_mul]
  congr 3; ring

/-- **Continuity in the phases**: `|P_a(f) − P_b(f)| ≤ Σ_n 2Λ(n)‖a(n) − b(n)‖ ‖f‖²`. -/
theorem abs_phasedPrimeSide_sub_le (a b : ℕ → ℂ) (N : ℕ) (f : WeilTestFn) :
    |phasedPrimeSide a N f - phasedPrimeSide b N f| ≤
      (∑ n ∈ Finset.Ico 2 N, 2 * (ArithmeticFunction.vonMangoldt n : ℝ) * ‖a n - b n‖) *
        testMass f := by
  unfold phasedPrimeSide
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := by have := (Finset.mem_Ico.mp hn).1; omega
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hs1 : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact_mod_cast hn1
  have hkp := norm_weilTest_self_le_testMass f (Real.log n)
  have hkm := norm_weilTest_self_le_testMass f (-Real.log n)
  have hM : 0 ≤ testMass f := integral_nonneg fun _ => sq_nonneg _
  rw [← mul_sub, ← sub_div, ← Complex.sub_re, abs_mul, abs_of_nonneg hΛ, abs_div,
    abs_of_pos (show 0 < Real.sqrt n by linarith)]
  have hdiff : (a n * EF.weilTest f.1 f.1 (Real.log n) + conj (a n) * EF.weilTest f.1 f.1 (-Real.log n) -
      (b n * EF.weilTest f.1 f.1 (Real.log n) + conj (b n) * EF.weilTest f.1 f.1 (-Real.log n))) =
      (a n - b n) * EF.weilTest f.1 f.1 (Real.log n) +
        conj (a n - b n) * EF.weilTest f.1 f.1 (-Real.log n) := by
    rw [map_sub]; ring
  rw [hdiff]
  have hnum : |((a n - b n) * EF.weilTest f.1 f.1 (Real.log n) +
      conj (a n - b n) * EF.weilTest f.1 f.1 (-Real.log n)).re| ≤ 2 * ‖a n - b n‖ * testMass f := by
    refine (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := mul_le_mul_of_nonneg_left hkp (norm_nonneg (a n - b n))
    have := mul_le_mul_of_nonneg_left hkm (norm_nonneg (a n - b n))
    linarith
  have hfrac : |((a n - b n) * EF.weilTest f.1 f.1 (Real.log n) +
      conj (a n - b n) * EF.weilTest f.1 f.1 (-Real.log n)).re| / Real.sqrt n ≤
      2 * ‖a n - b n‖ * testMass f := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ 2 * ‖a n - b n‖ * testMass f := by positivity
    nlinarith
  calc _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (2 * ‖a n - b n‖ * testMass f) :=
        mul_le_mul_of_nonneg_left hfrac hΛ
    _ = 2 * ArithmeticFunction.vonMangoldt n * ‖a n - b n‖ * testMass f := by ring

/-! ### 2. Kronecker with prescribed targets -/

/-- **Kronecker for the primes below `N`** with arbitrary target phases. -/
theorem exists_phase_near (N : ℕ) (α : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ℝ, ∀ p ∈ N.primesBelow,
      ‖Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) -
        Complex.exp (((α p : ℝ) : ℂ) * Complex.I)‖ < ε := by
  classical
  have hind : LinearIndependent ℚ (fun p : (N.primesBelow : Finset ℕ) => Real.log (p : ℕ)) :=
    linearIndependent_log_primes.comp
      (fun x : (N.primesBelow : Finset ℕ) =>
        (⟨(x : ℕ), (Nat.mem_primesBelow.mp x.2).2⟩ : Nat.Primes))
      (fun _ _ hab => Subtype.ext (congrArg (fun q : Nat.Primes => (q : ℕ)) hab))
  obtain ⟨t, ht⟩ := kronecker_approx hind (fun p => α p) hε
  refine ⟨t, fun p hp => ?_⟩
  have h := ht ⟨p, hp⟩
  simp only [expChar] at h
  rwa [mul_comm t]

/-- A unimodular number is `e^{i arg z}`. -/
theorem exp_arg_mul_I_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) = z := by
  have := Complex.norm_mul_exp_arg_mul_I z
  rwa [hz, Complex.ofReal_one, one_mul] at this

/-- **One modulation realizes a twist on every prime power below `N`.** For every twist `χ` and
`ε > 0` some `ξ` has `‖n^{iξ} − χ(n)‖ ≤ ε n` on every prime power `n < N`. -/
theorem exists_modulation_near_twist (χ : UnimodularTwist) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ξ : ℝ, ∀ n ∈ Finset.Ico 2 N, IsPrimePow n →
      ‖Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I) - χ.toFun n‖ ≤ ε * n := by
  obtain ⟨ξ, hξ⟩ := exists_phase_near N (fun p => Complex.arg (χ.toFun p)) hε
  refine ⟨ξ, fun n hn hpp => ?_⟩
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
  have hpN : p ∈ N.primesBelow := Nat.mem_primesBelow.mpr
    ⟨lt_of_le_of_lt (Nat.le_self_pow hk.ne' p) (Finset.mem_Ico.mp hn).2, hp⟩
  have hχp := exp_arg_mul_I_of_norm_one (χ.norm_prime p hp)
  have hp' := hξ p hpN
  rw [hχp] at hp'
  have e : Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((ξ * Real.log p : ℝ) : ℂ) * Complex.I) ^ k := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; rw [Real.log_pow]; push_cast; ring
  rw [e, χ.map_pow]
  refine (norm_pow_sub_pow_le_of_norm_le_one (by rw [Complex.norm_exp_ofReal_mul_I])
    (by rw [χ.norm_prime p hp]) k).trans ?_
  have hkn : (k : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_pow_self hp.one_lt).le
  calc (k : ℝ) * ‖_‖ ≤ k * ε := mul_le_mul_of_nonneg_left hp'.le (Nat.cast_nonneg k)
    _ ≤ ((p ^ k : ℕ) : ℝ) * ε := mul_le_mul_of_nonneg_right hkn hε.le
    _ = ε * ((p ^ k : ℕ) : ℝ) := mul_comm _ _

/-- The conjugate twist `χ̄`. -/
def UnimodularTwist.conj (χ : UnimodularTwist) : UnimodularTwist where
  toFun n := starRingEnd ℂ (χ.toFun n)
  map_one := by simp [χ.map_one]
  map_mul m n := by simp [χ.map_mul]
  norm_prime p hp := by rw [Complex.norm_conj, χ.norm_prime p hp]

/-! ### 3. Twisted window deviations -/

/-- The twisted window deviations `(Σ_f c_f P_χ(f))/‖c‖²`, tests in intervals of length `L`, with
the cutoff `N = ⌈e^L⌉`. -/
def twistedWindowDeviations (χ : UnimodularTwist) (L : ℝ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
    (∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) ∧ 0 < massOf c ∧
      x = (c.sum fun f t => t * phasedPrimeSide χ.toFun ⌈Real.exp L⌉₊ f) / massOf c}

theorem le_log_ceil_exp (L : ℝ) : L ≤ Real.log ⌈Real.exp L⌉₊ := by
  have hpos : (0 : ℝ) < ⌈Real.exp L⌉₊ := lt_of_lt_of_le (Real.exp_pos L) (Nat.le_ceil _)
  rw [Real.le_log_iff_exp_le hpos]; exact Nat.le_ceil _

/-- The phase error constant `Σ_{n<N} 2nΛ(n)`, as in `phaseConst`. -/
theorem sum_phase_error_le (N : ℕ) {ε : ℝ} (a b : ℕ → ℂ)
    (h : ∀ n ∈ Finset.Ico 2 N, IsPrimePow n → ‖a n - b n‖ ≤ ε * n) :
    ∑ n ∈ Finset.Ico 2 N, 2 * (ArithmeticFunction.vonMangoldt n : ℝ) * ‖a n - b n‖ ≤
      ε * phaseConst N := by
  rw [phaseConst, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  by_cases hpp : IsPrimePow n
  · have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have := mul_le_mul_of_nonneg_left (h n hn hpp) (by positivity : (0 : ℝ) ≤ 2 * (ArithmeticFunction.vonMangoldt n : ℝ))
    nlinarith
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]; simp

/-- Transport of a window combination by one modulation: the modulated combination has the same
mass and windows, and its phased prime sides are those of the original with phases `a(n) n^{iξ}`. -/
theorem modulated_combination (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) {L : ℝ}
    (hs : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) (ξ : ℝ) :
    let c' := Finsupp.mapDomain (modulatedTest ξ) c
    (∀ g, 0 ≤ c' g) ∧ (∀ g ∈ c'.support, ∃ a, ∀ u, g.1 u ≠ 0 → u ∈ Ioo a (a + L)) ∧
      massOf c' = massOf c ∧
      ∀ h : WeilTestFn → ℝ, (c'.sum fun g t => t * h g) = c.sum fun f t => t * h (modulatedTest ξ f) := by
  classical
  intro c'
  have hinj := modulatedTest_injective ξ
  have hsum : ∀ h : WeilTestFn → ℝ, (c'.sum fun g t => t * h g) =
      c.sum fun f t => t * h (modulatedTest ξ f) := fun h =>
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
  refine ⟨fun g => ?_, fun g hg => ?_, ?_, hsum⟩
  · by_cases hg : g ∈ Set.range (modulatedTest ξ)
    · obtain ⟨f, rfl⟩ := hg
      show 0 ≤ (Finsupp.mapDomain (modulatedTest ξ) c) (modulatedTest ξ f)
      rw [Finsupp.mapDomain_apply hinj]; exact hc f
    · show 0 ≤ (Finsupp.mapDomain (modulatedTest ξ) c) g
      rw [Finsupp.mapDomain_notin_range _ _ hg]
  · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
    obtain ⟨a, ha⟩ := hs f hf
    exact ⟨a, fun u hu => ha u (right_ne_zero_of_mul hu)⟩
  · rw [massOf_eq_sum, massOf_eq_sum, hsum]
    refine Finsupp.sum_congr fun f _ => ?_
    simp only [testMass, norm_modulatedTest]

/-- **Every window deviation is a limit of twisted window deviations.** -/
theorem exists_twisted_near_windowDeviation (χ : UnimodularTwist) {L x : ℝ}
    (hx : x ∈ windowDeviations L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x' ∈ twistedWindowDeviations χ L, |x' - x| ≤ δ := by
  classical
  obtain ⟨c, hc, hs, hpos, rfl⟩ := hx
  set N := ⌈Real.exp L⌉₊
  have hN := le_log_ceil_exp L
  have hK := phaseConst_nonneg N
  set ε := δ / (phaseConst N + 1) with hεdef
  have hε : 0 < ε := div_pos hδ (by linarith)
  -- `n^{iξ} ≈ χ̄(n)`, so the twisted side of the modulated test is the plain side
  obtain ⟨ξ, hξ⟩ := exists_modulation_near_twist χ.conj N hε
  obtain ⟨hc', hs', hmass, hsum⟩ := modulated_combination c hc hs ξ
  refine ⟨_, ⟨_, hc', hs', hmass ▸ hpos, rfl⟩, ?_⟩
  rw [hmass, hsum, nodeArchEnergy_sub_weilEnergy_eq_sum, div_sub_div_same, ← Finsupp.sum_sub,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos, massOf_eq_sum, Finsupp.sum, Finsupp.sum,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f hf => ?_)
  obtain ⟨a, ha⟩ := hs f hf
  rw [← mul_sub, abs_mul, abs_of_nonneg (hc f), phasedPrimeSide_modulatedTest,
    ← phasedPrimeSide_one ha hN]
  have herr := abs_phasedPrimeSide_sub_le (fun n => χ.toFun n *
    Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) (fun _ => 1) N f
  have hbound := sum_phase_error_le N (ε := ε) (fun n => χ.toFun n *
    Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) (fun _ => 1) (fun n hn hpp => by
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
      have h := hξ (p ^ k) hn hpp
      have hn1 : ‖χ.toFun (p ^ k)‖ = 1 := χ.norm_primePow hp k
      have hconj : χ.toFun (p ^ k) * starRingEnd ℂ (χ.toFun (p ^ k)) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn1]; simp
      calc ‖χ.toFun (p ^ k) * Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) - 1‖
          = ‖χ.toFun (p ^ k) * (Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) -
              starRingEnd ℂ (χ.toFun (p ^ k)))‖ := by rw [mul_sub, hconj]
        _ = ‖Complex.exp (((ξ * Real.log ((p ^ k : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) -
              (UnimodularTwist.conj χ).toFun (p ^ k)‖ := by
            rw [norm_mul, hn1, one_mul]; rfl
        _ ≤ ε * ((p ^ k : ℕ) : ℝ) := h)
  have hM : 0 ≤ testMass f := integral_nonneg fun _ => sq_nonneg _
  have hεK : ε * phaseConst N ≤ δ := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  calc c f * |phasedPrimeSide _ N f - phasedPrimeSide (fun _ => 1) N f|
      ≤ c f * ((ε * phaseConst N) * testMass f) :=
        mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_right hbound hM)) (hc f)
    _ ≤ c f * (δ * testMass f) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεK hM) (hc f)
    _ = δ * (c f * testMass f) := by ring

/-- **Every twisted window deviation is a limit of window deviations.** -/
theorem exists_windowDeviation_near_twisted (χ : UnimodularTwist) {L x : ℝ}
    (hx : x ∈ twistedWindowDeviations χ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x' ∈ windowDeviations L, |x' - x| ≤ δ := by
  classical
  obtain ⟨c, hc, hs, hpos, rfl⟩ := hx
  set N := ⌈Real.exp L⌉₊
  have hN := le_log_ceil_exp L
  have hK := phaseConst_nonneg N
  set ε := δ / (phaseConst N + 1) with hεdef
  have hε : 0 < ε := div_pos hδ (by linarith)
  -- `n^{iξ} ≈ χ(n)`, so the plain side of the modulated test is the twisted side
  obtain ⟨ξ, hξ⟩ := exists_modulation_near_twist χ N hε
  obtain ⟨hc', hs', hmass, hsum⟩ := modulated_combination c hc hs ξ
  refine ⟨_, ⟨_, hc', hs', hmass ▸ hpos, rfl⟩, ?_⟩
  rw [hmass, nodeArchEnergy_sub_weilEnergy_eq_sum, hsum, div_sub_div_same, ← Finsupp.sum_sub,
    abs_div, abs_of_pos hpos, div_le_iff₀ hpos, massOf_eq_sum, Finsupp.sum, Finsupp.sum,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun f hf => ?_)
  obtain ⟨a, ha⟩ := hs f hf
  have hsupp' : ∀ u, (modulatedTest ξ f).1 u ≠ 0 → u ∈ Ioo a (a + L) := fun u hu =>
    ha u (right_ne_zero_of_mul hu)
  rw [← mul_sub, abs_mul, abs_of_nonneg (hc f), ← phasedPrimeSide_one hsupp' hN,
    phasedPrimeSide_modulatedTest]
  have herr := abs_phasedPrimeSide_sub_le (fun n => 1 *
    Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) χ.toFun N f
  have hbound := sum_phase_error_le N (ε := ε) (fun n => 1 *
    Complex.exp (((ξ * Real.log n : ℝ) : ℂ) * Complex.I)) χ.toFun
    (fun n hn hpp => by rw [one_mul]; exact hξ n hn hpp)
  have hM : 0 ≤ testMass f := integral_nonneg fun _ => sq_nonneg _
  have hεK : ε * phaseConst N ≤ δ := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  calc c f * |phasedPrimeSide _ N f - phasedPrimeSide χ.toFun N f|
      ≤ c f * ((ε * phaseConst N) * testMass f) :=
        mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_right hbound hM)) (hc f)
    _ ≤ c f * (δ * testMass f) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεK hM) (hc f)
    _ = δ * (c f * testMass f) := by ring

/-! ### 4. Twisted ceilings and floors -/

/-- The twisted window ceiling. -/
def twistedWindowCeiling (χ : UnimodularTwist) (L : ℝ) : ℝ := sSup (twistedWindowDeviations χ L)

/-- The twisted window floor. -/
def twistedWindowFloor (χ : UnimodularTwist) (L : ℝ) : ℝ := sInf (twistedWindowDeviations χ L)

theorem bddAbove_twistedWindowDeviations (χ : UnimodularTwist) {L : ℝ} (hL : 0 ≤ L) :
    BddAbove (twistedWindowDeviations χ L) := by
  obtain ⟨B, hB⟩ := bddAbove_windowDeviations hL
  refine ⟨B + 1, fun x hx => ?_⟩
  obtain ⟨x', hx', h⟩ := exists_windowDeviation_near_twisted χ hx one_pos
  linarith [hB hx', neg_abs_le (x' - x)]

theorem bddBelow_twistedWindowDeviations (χ : UnimodularTwist) {L : ℝ} (hL : 0 ≤ L) :
    BddBelow (twistedWindowDeviations χ L) := by
  obtain ⟨B, hB⟩ := bddBelow_windowDeviations hL
  refine ⟨B - 1, fun x hx => ?_⟩
  obtain ⟨x', hx', h⟩ := exists_windowDeviation_near_twisted χ hx one_pos
  linarith [hB hx', le_abs_self (x' - x)]

/-- **The twisted window ceiling is the window ceiling.** -/
theorem twistedWindowCeiling_eq (χ : UnimodularTwist) {L : ℝ} (hL : 0 ≤ L)
    (hne : (windowDeviations L).Nonempty) : twistedWindowCeiling χ L = windowCeiling L := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀, -⟩ := exists_twisted_near_windowDeviation χ hx₀ one_pos
  have ha := bddAbove_windowDeviations hL
  have ha' := bddAbove_twistedWindowDeviations χ hL
  apply le_antisymm
  · refine csSup_le ⟨y₀, hy₀⟩ fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨x', hx', h⟩ := exists_windowDeviation_near_twisted χ hx hδ
    have := le_csSup ha hx'
    unfold windowCeiling
    linarith [le_abs_self (x' - x), neg_abs_le (x' - x)]
  · refine csSup_le ⟨x₀, hx₀⟩ fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨x', hx', h⟩ := exists_twisted_near_windowDeviation χ hx hδ
    have := le_csSup ha' hx'
    unfold twistedWindowCeiling
    linarith [le_abs_self (x' - x), neg_abs_le (x' - x)]

/-- **The twisted window floor is the window floor.** -/
theorem twistedWindowFloor_eq (χ : UnimodularTwist) {L : ℝ} (hL : 0 ≤ L)
    (hne : (windowDeviations L).Nonempty) : twistedWindowFloor χ L = windowFloor L := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨y₀, hy₀, -⟩ := exists_twisted_near_windowDeviation χ hx₀ one_pos
  have hb := bddBelow_windowDeviations hL
  have hb' := bddBelow_twistedWindowDeviations χ hL
  apply le_antisymm
  · refine le_csInf ⟨x₀, hx₀⟩ fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨x', hx', h⟩ := exists_twisted_near_windowDeviation χ hx hδ
    have := csInf_le hb' hx'
    unfold twistedWindowFloor
    linarith [le_abs_self (x' - x), neg_abs_le (x' - x)]
  · refine le_csInf ⟨y₀, hy₀⟩ fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨x', hx', h⟩ := exists_windowDeviation_near_twisted χ hx hδ
    have := csInf_le hb hx'
    unfold windowFloor
    linarith [le_abs_self (x' - x), neg_abs_le (x' - x)]

end

end GaloisForLFunctions.BiScaleUncertainty
