import GaloisForLFunctions.ArithmeticElectrostatics.TheWeilPrimeFormOnAtomsIsLogarithmic
import GaloisForLFunctions.BiarithmeticGaugeGeometry.PrimeGaugeTorusAndVacuumIntertwiners
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine

/-!
# The sign is a gauge-fixing

Lorentzian theory takes nonnegative coefficients as its hypothesis. On the atoms `log n`,
`1 ≤ n ≤ N`, the off-diagonal intersection numbers of a twin `χ` of the prime gauge torus (a
completely multiplicative function of modulus one) are the sum of two kernels,

    K_t(m, n) = A(m, n) + t · conj χ(m) χ(n) P(m, n),

the **archimedean kernel** `A(m, n) = ω(|log n − log m|)` (`ω` the Lévy density of the Gamma factor,
positive on every pair) and the **twisted prime kernel** (`P = Λ(n/m)(n/m)^{−1/2}` on prime-power
ratios), with `t > 0` their relative weight (at atomic resolution the prime kernel dominates by the
inverse width). A **gauge** is a choice of phases `g_n` on the atoms; it conjugates the kernel to
`conj g_m g_n K(m, n)` without changing any signature.

* **Each kernel alone carries no sign.** The twisted prime kernel becomes `P ≥ 0` in the gauge
  `g = conj χ` (`twinPrimeKernel_gauge_nonneg`); the archimedean kernel is nonnegative in the
  trivial gauge. The prime gauge torus acts on the prime kernel by gauge transformations.
* **The sum carries exactly the Euler sign** (`exists_nonneg_gauge_iff`). For `N ≥ 6` and `t ≥ 2`,
  the coupled kernel `K_t` is entrywise nonnegative in some gauge iff `χ(p) = 1` for every prime
  `p ≤ N`. The archimedean kernel fixes the gauge along the **successor**: consecutive orders
  `m, m + 1` (`m ≥ 2`) are never on a common prime ladder, so `K_t(m, m + 1) = A(m, m + 1) > 0`
  forces `g_m = g_{m+1}`; with the gauge fixed, `K_t(1, p) ≥ 0` forces `χ(p) = 1` because the
  prime weight `t log p/√p` exceeds `ω(log p) = p^{−1/2}/(1 − p^{−2})`.
* **The Liouville twin fails visibly** (`not_exists_nonneg_gauge_liouville`).
* **Archimedean characters** (`exists_nonneg_gauge_shifted_iff`, `exists_nonneg_gauge_kronecker`): with the archimedean kernel of
  the shifted function `ζ(s − iτ)`, `conj(m^{iτ}) n^{iτ} A(m, n)`, the nonnegative gauges exist iff
  `χ(p) = p^{iτ}` on the horizon. The Lorentzian locus of the torus is the set of archimedean
  characters `n^{iτ}`, each read with its own archimedean kernel; no other unimodular twin admits
  a nonnegative gauge on a horizon containing a prime where it differs from `p^{iτ}`. (Dirichlet
  characters vanish at the primes of their conductor and are not unimodular twins; with their own
  archimedean kernel they enter as isotypic components of Euler points of cyclotomic fields.)

The sign hypothesis of Lorentzian theory is therefore a gauge-fixing performed by the archimedean
place along the successor. It is invisible to every form built from the prime kernel alone.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticEffectivityTheory BiarithmeticGaugeGeometry ArithmeticElectrostatics

/-! ### Twins and kernels -/

/-- A **twin**: completely multiplicative, of modulus one on the positive integers. -/
structure IsTwin (χ : ℕ → ℂ) : Prop where
  map_mul : ∀ m n, χ (m * n) = χ m * χ n
  norm_eq : ∀ n, n ≠ 0 → ‖χ n‖ = 1

theorem IsTwin.map_one {χ : ℕ → ℂ} (hχ : IsTwin χ) : χ 1 = 1 := by
  have h := hχ.map_mul 1 1
  rw [Nat.mul_one] at h
  have h0 : χ 1 ≠ 0 := fun h0 => by
    have := hχ.norm_eq 1 one_ne_zero
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ h0 (h.symm.trans (mul_one _).symm)

theorem isTwin_gaugeChar (ω : PrimeGauge) : IsTwin ω.gaugeChar :=
  ⟨ω.gaugeChar_mul, fun _ hn => ω.norm_gaugeChar hn⟩

/-- The archimedean kernel between the atoms `log m` and `log n`: the Lévy density of the Gamma
factor at their distance. -/
def archAtomKernel (m n : ℕ) : ℝ :=
  if m = n then 0 else RHTower.archLevyDensity |Real.log n - Real.log m|

/-- The twisted prime kernel `conj χ(m) χ(n) P(m, n)` of the twin `χ`. -/
def twinPrimeKernel (χ : ℕ → ℂ) (m n : ℕ) : ℂ :=
  conj (χ m) * χ n * weilPrimeKernel m n

/-- The coupled kernel `A + t · (twisted prime kernel)`. -/
def coupledKernel (χ : ℕ → ℂ) (t : ℝ) (m n : ℕ) : ℂ :=
  (archAtomKernel m n : ℂ) + t * twinPrimeKernel χ m n

/-- A nonnegative gauge for a kernel on the atoms `[1, N]`. -/
def HasNonnegGauge (K : ℕ → ℕ → ℂ) (N : ℕ) : Prop :=
  ∃ g : ℕ → ℂ, (∀ n ∈ Icc 1 N, ‖g n‖ = 1) ∧
    ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n → 0 ≤ conj (g m) * g n * K m n

/-! ### Elementary facts -/

theorem archAtomKernel_pos {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    0 < archAtomKernel m n := by
  rw [archAtomKernel, if_neg hmn]
  refine RHTower.archLevyDensity_pos (abs_pos.mpr (sub_ne_zero.mpr fun h => hmn ?_))
  exact_mod_cast Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hm))
    (Set.mem_Ioi.mpr (by exact_mod_cast hn)) h.symm

theorem archAtomKernel_nonneg (m n : ℕ) : 0 ≤ archAtomKernel m n := by
  unfold archAtomKernel
  split_ifs
  · exact le_rfl
  · unfold RHTower.archLevyDensity
    rcases eq_or_lt_of_le (abs_nonneg (Real.log n - Real.log m)) with h | h
    · rw [← h]; simp
    · exact (RHTower.archLevyDensity_pos h).le

/-- **Successor pairs lie on no common prime ladder**: `P(m, m + 1) = 0` for `m ≥ 2`. -/
theorem weilPrimeKernel_succ {m : ℕ} (hm : 2 ≤ m) : weilPrimeKernel m (m + 1) = 0 := by
  unfold weilPrimeKernel
  have h1 : ¬ (m ∣ m + 1 ∧ m ≠ m + 1) := fun h =>
    absurd (Nat.le_of_dvd one_pos ((Nat.dvd_add_right (dvd_refl m)).mp h.1)) (by omega)
  have h2 : ¬ (m + 1 ∣ m ∧ m + 1 ≠ m) := fun h =>
    absurd (Nat.le_of_dvd (by omega) h.1) (by omega)
  rw [if_neg h1, if_neg h2]

/-- `P(1, 6) = 0`: six is not a prime power. -/
theorem weilPrimeKernel_one_six : weilPrimeKernel 1 6 = 0 := by
  unfold weilPrimeKernel
  rw [if_pos ⟨one_dvd 6, by norm_num⟩, ArithmeticFunction.vonMangoldt_apply,
    if_neg (by decide : ¬ IsPrimePow (6 / 1 : ℕ))]
  simp

theorem weilPrimeKernel_one_prime {p : ℕ} (hp : p.Prime) :
    weilPrimeKernel 1 p = Real.log p / Real.sqrt p := by
  unfold weilPrimeKernel
  rw [if_pos ⟨one_dvd p, (Nat.Prime.one_lt hp).ne⟩, Nat.div_one,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- **Unimodular rigidity**: if `conj a · b · r ≥ 0` with `|a| = |b| = 1` and `r > 0`, then `a = b`. -/
theorem eq_of_conj_mul_nonneg {a b : ℂ} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {r : ℝ} (hr : 0 < r)
    (h : 0 ≤ conj a * b * r) : a = b := by
  rw [Complex.nonneg_iff] at h
  set w := conj a * b with hw
  have hre : 0 ≤ w.re := by
    have : (w * r).re = w.re * r := by simp
    rw [this] at h; exact nonneg_of_mul_nonneg_left h.1 hr
  have him : w.im = 0 := by
    have : (w * r).im = w.im * r := by simp
    rw [this] at h; exact (mul_eq_zero.mp h.2.symm).resolve_right hr.ne'
  have hnorm : ‖w‖ = 1 := by rw [hw, norm_mul, Complex.norm_conj, ha, hb, mul_one]
  have hw1 : w = 1 := by
    have h1 : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre] at hnorm
    rw [h1, hnorm, Complex.ofReal_one]
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have haa : conj a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  have : conj a * b = conj a * a := by rw [← hw, hw1, haa]
  exact (mul_left_cancel₀ (map_ne_zero (starRingEnd ℂ) |>.mpr ha0) this).symm

/-! ### Each kernel alone carries no sign -/

/-- **The prime kernel alone is gauge-trivial**: in the gauge `g = conj χ` every twisted prime
kernel is the Euler kernel `P ≥ 0`. -/
theorem twinPrimeKernel_gauge_nonneg {χ : ℕ → ℂ} (hχ : IsTwin χ) {m n : ℕ} (hm : m ≠ 0)
    (hn : n ≠ 0) : 0 ≤ conj (conj (χ m)) * conj (χ n) * twinPrimeKernel χ m n := by
  have e : conj (conj (χ m)) * conj (χ n) * twinPrimeKernel χ m n =
      ((‖χ m‖ ^ 2 * ‖χ n‖ ^ 2 * weilPrimeKernel m n : ℝ) : ℂ) := by
    simp only [twinPrimeKernel, Complex.conj_conj]
    have h1 : χ m * conj (χ m) = ((‖χ m‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : conj (χ n) * χ n = ((‖χ n‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc χ m * conj (χ n) * (conj (χ m) * χ n * weilPrimeKernel m n)
        = (χ m * conj (χ m)) * (conj (χ n) * χ n) * weilPrimeKernel m n := by ring
      _ = _ := by rw [h1, h2]; push_cast; ring
  rw [e, hχ.norm_eq m hm, hχ.norm_eq n hn]
  exact_mod_cast by simpa using weilPrimeKernel_nonneg m n

/-! ### The coupled kernel carries exactly the Euler sign -/

/-- A twin trivial on the primes of the horizon is trivial on the horizon. -/
theorem twin_eq_one_of_primes {χ : ℕ → ℂ} (hχ : IsTwin χ) {N : ℕ}
    (hp : ∀ p, p.Prime → p ≤ N → χ p = 1) : ∀ n, 1 ≤ n → n ≤ N → χ n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1 hnN
    rcases eq_or_lt_of_le hn1 with rfl | hn
    · exact hχ.map_one
    · have hmf := Nat.minFac_prime (show n ≠ 1 by omega)
      obtain ⟨k, hk⟩ := Nat.minFac_dvd n
      have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hk; omega
      have hkn : k < n := by
        have := hmf.two_le
        nlinarith
      rw [hk, hχ.map_mul, hp _ hmf (le_trans (Nat.minFac_le (by omega)) hnN),
        ih k hkn hk1 (by omega), one_mul]

/-- The weight `t log p/√p` beats `ω(log p)` once `t ≥ 2`. -/
theorem archLevyDensity_log_lt {p : ℕ} (hp : p.Prime) {t : ℝ} (ht : 2 ≤ t) :
    RHTower.archLevyDensity (Real.log p) < t * (Real.log p / Real.sqrt p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
  have hl2 := Real.log_two_gt_d9
  have hsq : Real.exp (-Real.log p / 2) = 1 / Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp0, one_div, ← Real.exp_neg]
    ring_nf
  have he : Real.exp (-2 * Real.log p) ≤ 1 / 4 := by
    rw [show -2 * Real.log p = Real.log ((p : ℝ) ^ 2)⁻¹ by
      rw [Real.log_inv, Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  unfold RHTower.archLevyDensity
  rw [hsq, div_div, div_lt_iff₀ (by nlinarith)]
  have : t * (Real.log p / Real.sqrt p) * (Real.sqrt p * (1 - Real.exp (-2 * Real.log p))) =
      t * Real.log p * (1 - Real.exp (-2 * Real.log p)) := by field_simp
  rw [this]
  have hA : (3 : ℝ) / 4 ≤ 1 - Real.exp (-2 * Real.log p) := by linarith
  have hB : 2 * 0.6931471803 ≤ t * Real.log p := by nlinarith
  have h3 := mul_le_mul hB hA (by norm_num) (by nlinarith)
  have h4 : (1 : ℝ) < 2 * 0.6931471803 * (3 / 4) := by norm_num
  linarith

/-- **The sign is a gauge-fixing.** For `N ≥ 6` and `t ≥ 2`, the coupled kernel of a twin has a
nonnegative gauge on `[1, N]` iff the twin is trivial on the primes `p ≤ N`. -/
theorem exists_nonneg_gauge_iff {χ : ℕ → ℂ} (hχ : IsTwin χ) {N : ℕ} (hN : 6 ≤ N) {t : ℝ}
    (ht : 2 ≤ t) :
    HasNonnegGauge (coupledKernel χ t) N ↔ ∀ p, p.Prime → p ≤ N → χ p = 1 := by
  constructor
  · rintro ⟨g, hg, hK⟩ p hp hpN
    -- the archimedean kernel fixes the gauge along the successor
    have hsucc : ∀ m, 2 ≤ m → m + 1 ≤ N → g m = g (m + 1) := fun m hm hmN => by
      have h := hK m (mem_Icc.mpr ⟨by omega, by omega⟩) (m + 1) (mem_Icc.mpr ⟨by omega, hmN⟩)
        (by omega)
      rw [coupledKernel, twinPrimeKernel, weilPrimeKernel_succ hm] at h
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
      exact eq_of_conj_mul_nonneg (hg m (mem_Icc.mpr ⟨by omega, by omega⟩))
        (hg (m + 1) (mem_Icc.mpr ⟨by omega, hmN⟩))
        (archAtomKernel_pos (by omega) (by omega) (by omega)) h
    have hconst : ∀ m, 2 ≤ m → m ≤ N → g m = g 2 := fun m hm hmN => by
      induction m, hm using Nat.le_induction with
      | base => rfl
      | succ k hk ih => rw [← hsucc k hk hmN, ih (by omega)]
    have h16 : g 1 = g 6 := by
      have h := hK 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩) 6 (mem_Icc.mpr ⟨by norm_num, hN⟩)
        (by norm_num)
      rw [coupledKernel, twinPrimeKernel, weilPrimeKernel_one_six] at h
      simp only [Complex.ofReal_zero, mul_zero, add_zero] at h
      exact eq_of_conj_mul_nonneg (hg 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩))
        (hg 6 (mem_Icc.mpr ⟨by norm_num, hN⟩)) (archAtomKernel_pos one_pos (by norm_num)
          (by norm_num)) h
    have hg1p : g 1 = g p := by rw [h16, hconst 6 (by norm_num) hN, hconst p hp.two_le hpN]
    -- with the gauge fixed, the pair `(1, p)` forces `χ(p) = 1`
    have h := hK 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩) p (mem_Icc.mpr ⟨hp.one_lt.le, hpN⟩)
      hp.one_lt.ne
    rw [← hg1p] at h
    have hgg : conj (g 1) * g 1 = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        hg 1 (mem_Icc.mpr ⟨le_rfl, by omega⟩)]; simp
    have hχ1 : χ 1 = 1 := hχ.map_one
    rw [hgg, one_mul, coupledKernel, twinPrimeKernel, hχ1, map_one, one_mul,
      weilPrimeKernel_one_prime hp, archAtomKernel, if_neg hp.one_lt.ne, Nat.cast_one,
      Real.log_one, sub_zero, abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
      at h
    rw [Complex.nonneg_iff] at h
    set L := Real.log p / Real.sqrt p
    have hL : 0 < L := div_pos (Real.log_pos (by exact_mod_cast hp.one_lt))
      (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos))
    have hre : 0 ≤ RHTower.archLevyDensity (Real.log p) + t * (L * (χ p).re) := by
      have := h.1; simpa [mul_comm, mul_left_comm, mul_assoc] using this
    have himχ : (χ p).im = 0 := by
      have h2 := h.2
      simp at h2
      rcases h2 with h0 | h0 | h0 <;> linarith
    have hnorm := hχ.norm_eq p hp.ne_zero
    have hχr : χ p = ((χ p).re : ℂ) := Complex.ext (by simp) (by simp [himχ])
    rw [hχr, Complex.norm_real, Real.norm_eq_abs] at hnorm
    rcases abs_eq (zero_le_one) |>.mp hnorm with h1 | h1
    · rw [hχr, h1, Complex.ofReal_one]
    · rw [h1] at hre
      have := archLevyDensity_log_lt hp ht
      linarith
  · intro hp
    have h1 := twin_eq_one_of_primes hχ hp
    refine ⟨fun _ => 1, fun _ _ => norm_one, fun m hm n hn _ => ?_⟩
    rw [coupledKernel, twinPrimeKernel, h1 m (mem_Icc.mp hm).1 (mem_Icc.mp hm).2,
      h1 n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
    simp only [map_one, one_mul]
    exact_mod_cast add_nonneg (archAtomKernel_nonneg m n)
      (mul_nonneg (by linarith) (weilPrimeKernel_nonneg m n))

/-- **The Liouville twin fails visibly**: its coupled kernel has no nonnegative gauge. -/
theorem not_exists_nonneg_gauge_liouville {N : ℕ} (hN : 6 ≤ N) {t : ℝ} (ht : 2 ≤ t) :
    ¬ HasNonnegGauge (coupledKernel PrimeGauge.liouvilleGauge.gaugeChar t) N := by
  rw [exists_nonneg_gauge_iff (isTwin_gaugeChar _) hN ht]
  intro h
  have := h 2 Nat.prime_two (by omega)
  rw [PrimeGauge.gaugeChar_prime _ Nat.prime_two] at this
  simp [PrimeGauge.liouvilleGauge, Nat.prime_two] at this
  norm_num at this

/-- **The Euler point has a nonnegative gauge.** -/
theorem exists_nonneg_gauge_euler (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasNonnegGauge (coupledKernel PrimeGauge.eulerGauge.gaugeChar t) N := by
  refine ⟨fun _ => 1, fun _ _ => norm_one, fun m hm n hn _ => ?_⟩
  rw [coupledKernel, twinPrimeKernel,
    PrimeGauge.gaugeChar_euler (by have := (mem_Icc.mp hm).1; omega),
    PrimeGauge.gaugeChar_euler (by have := (mem_Icc.mp hn).1; omega)]
  simp only [map_one, one_mul]
  exact_mod_cast add_nonneg (archAtomKernel_nonneg m n) (mul_nonneg ht (weilPrimeKernel_nonneg m n))

/-! ### Archimedean characters -/

/-- The archimedean character `n^{iτ}`. -/
def archChar (τ : ℝ) (n : ℕ) : ℂ := (n : ℂ) ^ ((τ : ℂ) * I)

theorem norm_archChar (τ : ℝ) {n : ℕ} (hn : n ≠ 0) : ‖archChar τ n‖ = 1 := by
  rw [archChar, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
  simp

theorem archChar_mul (τ : ℝ) (m n : ℕ) : archChar τ (m * n) = archChar τ m * archChar τ n := by
  unfold archChar; push_cast; exact Complex.natCast_mul_natCast_cpow m n _

theorem conj_archChar_mul_self (τ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    conj (archChar τ n) * archChar τ n = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_archChar τ hn]; simp

/-- The coupled kernel read with the archimedean kernel of `ζ(s − iτ)`,
`conj(m^{iτ}) n^{iτ} A(m, n)`. -/
def shiftedCoupledKernel (τ : ℝ) (χ : ℕ → ℂ) (t : ℝ) (m n : ℕ) : ℂ :=
  conj (archChar τ m) * archChar τ n * archAtomKernel m n + t * twinPrimeKernel χ m n

/-- The twin `χ` measured from the archimedean character: `χ(n) n^{−iτ}`. -/
def relTwin (τ : ℝ) (χ : ℕ → ℂ) (n : ℕ) : ℂ := χ n * conj (archChar τ n)

theorem isTwin_relTwin {χ : ℕ → ℂ} (hχ : IsTwin χ) (τ : ℝ) : IsTwin (relTwin τ χ) := by
  refine ⟨fun m n => ?_, fun n hn => ?_⟩
  · simp only [relTwin, hχ.map_mul, archChar_mul, map_mul]; ring
  · rw [relTwin, norm_mul, Complex.norm_conj, hχ.norm_eq n hn, norm_archChar τ hn, one_mul]

/-- The gauge `g ↦ g · n^{iτ}` intertwines the shifted kernel with the coupled kernel of the relative
twin. -/
theorem gauge_shiftedCoupledKernel (τ : ℝ) (χ : ℕ → ℂ) (t : ℝ) (g : ℕ → ℂ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    conj (g m) * g n * shiftedCoupledKernel τ χ t m n =
      conj (g m * archChar τ m) * (g n * archChar τ n) * coupledKernel (relTwin τ χ) t m n := by
  have ha := conj_archChar_mul_self τ hm
  have hb := conj_archChar_mul_self τ hn
  simp only [shiftedCoupledKernel, coupledKernel, twinPrimeKernel, relTwin, map_mul,
    Complex.conj_conj]
  linear_combination (-(↑t * conj (g m) * g n * conj (χ m) * χ n * ↑(weilPrimeKernel m n)) *
    (conj (archChar τ n) * archChar τ n)) * ha +
    (-(↑t * conj (g m) * g n * conj (χ m) * χ n * ↑(weilPrimeKernel m n))) * hb

/-- **The Lorentzian locus of the torus is the set of archimedean characters.** Read with the
archimedean kernel of `ζ(s − iτ)`, the coupled kernel of a twin has a nonnegative gauge on
`[1, N]` (`N ≥ 6`, `t ≥ 2`) iff `χ(p) = p^{iτ}` for every prime `p ≤ N`. -/
theorem exists_nonneg_gauge_shifted_iff {χ : ℕ → ℂ} (hχ : IsTwin χ) {N : ℕ} (hN : 6 ≤ N)
    {t : ℝ} (ht : 2 ≤ t) (τ : ℝ) :
    HasNonnegGauge (shiftedCoupledKernel τ χ t) N ↔
      ∀ p, p.Prime → p ≤ N → χ p = archChar τ p := by
  have hrel := exists_nonneg_gauge_iff (isTwin_relTwin hχ τ) hN ht
  have hpt : ∀ p, p.Prime → (relTwin τ χ p = 1 ↔ χ p = archChar τ p) := fun p hp => by
    have hb := conj_archChar_mul_self τ hp.ne_zero
    constructor
    · intro h
      have : χ p * (conj (archChar τ p) * archChar τ p) = archChar τ p := by
        rw [← mul_assoc]; exact (congrArg (· * archChar τ p) h).trans (one_mul _)
      rwa [hb, mul_one] at this
    · intro h; rw [relTwin, h, mul_comm, hb]
  constructor
  · rintro ⟨g, hg, hK⟩
    have hrel' : HasNonnegGauge (coupledKernel (relTwin τ χ) t) N := by
      refine ⟨fun n => g n * archChar τ n, fun n hn => ?_, fun m hm n hn hmn => ?_⟩
      · rw [norm_mul, hg n hn, norm_archChar τ (by have := (mem_Icc.mp hn).1; omega), one_mul]
      · rw [← gauge_shiftedCoupledKernel τ χ t g (by have := (mem_Icc.mp hm).1; omega)
          (by have := (mem_Icc.mp hn).1; omega)]
        exact hK m hm n hn hmn
    exact fun p hp hpN => (hpt p hp).mp (hrel.mp hrel' p hp hpN)
  · intro h
    obtain ⟨g, hg, hK⟩ := hrel.mpr fun p hp hpN => (hpt p hp).mpr (h p hp hpN)
    refine ⟨fun n => g n * conj (archChar τ n), fun n hn => ?_, fun m hm n hn hmn => ?_⟩
    · rw [norm_mul, Complex.norm_conj, hg n hn,
        norm_archChar τ (by have := (mem_Icc.mp hn).1; omega), one_mul]
    · have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have e := gauge_shiftedCoupledKernel τ χ t (fun n => g n * conj (archChar τ n)) hm0 hn0
      have hm1 : g m * conj (archChar τ m) * archChar τ m = g m := by
        rw [mul_assoc, conj_archChar_mul_self τ hm0, mul_one]
      have hn1 : g n * conj (archChar τ n) * archChar τ n = g n := by
        rw [mul_assoc, conj_archChar_mul_self τ hn0, mul_one]
      beta_reduce at e ⊢
      rw [hm1, hn1] at e
      rw [e]
      exact hK m hm n hn hmn

/-- **The Kronecker twin is Lorentzian with its own archimedean kernel**: `p^{iτ}` on the primes
admits a nonnegative gauge for the kernel of `ζ(s − iτ)`. -/
theorem exists_nonneg_gauge_kronecker {N : ℕ} (hN : 6 ≤ N) {t : ℝ} (ht : 2 ≤ t) (τ : ℝ) :
    HasNonnegGauge (shiftedCoupledKernel τ (PrimeGauge.kroneckerGauge τ).gaugeChar t) N := by
  refine (exists_nonneg_gauge_shifted_iff (isTwin_gaugeChar _) hN ht τ).mpr fun p hp _ => ?_
  rw [PrimeGauge.gaugeChar_prime _ hp]
  simp [PrimeGauge.kroneckerGauge, hp, archChar]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
