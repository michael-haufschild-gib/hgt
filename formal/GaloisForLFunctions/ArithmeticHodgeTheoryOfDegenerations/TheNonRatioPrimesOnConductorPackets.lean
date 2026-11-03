import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheArchimedeanKernelOfNearAtoms
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilResidualIsTheUpwardDefect

/-!
# The non-ratio primes on conductor packets

At overlap `c` the prime matrix pairs `n` with every `j` at log-distance `< w = c/N` from a
multiple `kn`, not only with `j = kn`; the non-ratio part `NR` keeps these windows. On conductor
packets it is a sum over near pairs.

* **Upward rows are downward rows** (`sum_mul_upwardPrimeRow_eq`): the upward pairing of `x` into
  `y` is the downward pairing of `y` into `x`, so `⟨NR x, y⟩` is a sum of two downward pairings
  (`inner_nonRatio_eq`).
* **Divisor form** (`inner_nonRatio_ramanujan_eq`): grouping `kj = ℓ` turns each downward pairing into
  `Σ_{n, ℓ} c_{e'}(n) (Λ ∗ c_e)(ℓ) G((log ℓ − log n)/w)/(∫φ² √(nℓ))`, the Mangoldt convolution
  truncated at the horizon (`nrSum`).
* **Interior and exterior** (`nrSum_eq_interior_add_exterior`): for `ℓ ≤ N` the convolution is
  `c_e(ℓ) log ℓ − J_e(ℓ)`, with the logarithmic divisor jet `J_e(ℓ) = Σ_{d ∣ (e, ℓ)} μ(e/d) d log d`,
  `e`-periodic with mean `Λ(e)` (`sum_range_ramanujanLogDivisorJet`). The products beyond the
  horizon cost `O(c² log N/N)` (`abs_nrExterior_le`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence
open _root_.RHTower (vonMangoldtAtom)

/-! ### Upward rows are downward rows -/

/-- The upward pairing of `x` into `y` is the downward pairing of `y` into `x`. -/
theorem sum_mul_upwardPrimeRow_eq {g : ℝ → ℝ} {w : ℝ} (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x y : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 N, y n * upwardPrimeRow g N x n =
      ∑ j ∈ Finset.Icc 1 N, x j * downwardPrimeRow g N y j := by
  set K := lagRange (Real.log N + w + 1)
  have hup : ∀ n ∈ Finset.Icc 1 N, upwardPrimeRow g N x n = ∑ k ∈ range K, vonMangoldtAtom k *
      ∑ j ∈ Finset.Icc 1 N, x j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) :=
    fun n hn => upwardPrimeRow_eq_sum hgsupp hw hn x
  have hdown : ∀ j ∈ Finset.Icc 1 N, downwardPrimeRow g N y j = ∑ k ∈ range K, vonMangoldtAtom k *
      ∑ n ∈ Finset.Icc 1 N, y n *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) :=
    fun j hj => downwardPrimeRow_eq_sum hgsupp hw hj y
  have hL : ∑ n ∈ Finset.Icc 1 N, y n * upwardPrimeRow g N x n =
      ∑ n ∈ Finset.Icc 1 N, y n * ∑ k ∈ range K, vonMangoldtAtom k *
        ∑ j ∈ Finset.Icc 1 N, x j *
          (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) :=
    Finset.sum_congr rfl fun n hn => by rw [hup n hn]
  have hR : ∑ j ∈ Finset.Icc 1 N, x j * downwardPrimeRow g N y j =
      ∑ j ∈ Finset.Icc 1 N, x j * ∑ k ∈ range K, vonMangoldtAtom k *
        ∑ n ∈ Finset.Icc 1 N, y n *
          (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) :=
    Finset.sum_congr rfl fun j hj => by rw [hdown j hj]
  rw [hL, hR]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := range K)]
  conv_rhs => rw [Finset.sum_comm (s := Finset.Icc 1 N) (t := range K)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n _ => by ring

/-- **The non-ratio pairing is two downward pairings.** -/
theorem inner_nonRatio_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, y⟫ =
      (∑ n ∈ Finset.Icc 1 N, primeHorizonExtension y n *
          downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n +
        ∑ j ∈ Finset.Icc 1 N, primeHorizonExtension x j *
          downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension y) j) /
        (∫ u, atomDilate φ (c / N) u ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := RenormalizedArithmeticPotentialTheory.atomDilate_facts hφ hsupp hw
  set g := atomDilate φ (c / N)
  rw [real_inner_comm, EuclideanSpace.inner_eq_star_dotProduct]
  change ∑ n : PrimeHorizonIndex N, (Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x) n *
    y n = _
  simp only [fullWeilNonRatioMatrix_row_eq hφ hsupp hM hc hN]
  rw [← sum_mul_upwardPrimeRow_eq hgsupp hw.le N (primeHorizonExtension x)
    (primeHorizonExtension y), ← Finset.sum_add_distrib, Finset.sum_div]
  rw [← Finset.sum_coe_sort (Finset.Icc 1 N)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primeHorizonExtension_coe]
  change (downwardPrimeRow g N (primeHorizonExtension x) n +
    upwardPrimeRow g N (primeHorizonExtension x) n) / (∫ u, g u ^ 2) * y n = _
  ring

/-! ### The divisor form on conductor packets -/

/-- The autocorrelation of a dilated atom: `∫ g(v) g(v + t) dv = w G(t/w)`. -/
theorem bumpCorr_atomDilate_eq (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) (t : ℝ) :
    bumpCorr (atomDilate φ w) t = w * shellAutocorr φ (t / w) := by
  have h := integral_atomDilate_mul_shift (φ := φ) hw (-t)
  have e : bumpCorr (atomDilate φ w) t =
      ∫ u, atomDilate φ w u * atomDilate φ w (u - -t) := by
    rw [bumpCorr]; simp only [sub_neg_eq_add]
  rw [e, h, neg_div, shellAutocorr_neg]

/-- The truncated Mangoldt pairing of two conductors at width `w = c/N`:
`Σ_{n ≤ N} Σ_{ℓ ≤ L, ℓ ≠ n} c_b(n) (Λ ∗ c_a)_{≤ N}(ℓ) G((log ℓ − log n)/w)/(∫φ² √n √ℓ)`. -/
def nrSum (φ : ℝ → ℝ) (c : ℝ) (N a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 (exteriorPrimeCutoff c N),
    (if ℓ = n then 0 else shellAutocorr φ ((Real.log ℓ - Real.log n) / (c / N))) /
      (∫ u, φ u ^ 2) * ramanujanLagCoefficient b n * horizonRamanujanMangoldt a N ℓ /
        (Real.sqrt n * Real.sqrt ℓ)

theorem sum_downward_ramanujan_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (∑ n ∈ Finset.Icc 1 N, primeHorizonExtension (ramanujanHorizonVector b N) n *
        downwardPrimeRow (atomDilate φ (c / N)) N
          (primeHorizonExtension (ramanujanHorizonVector a N)) n) /
      (∫ u, atomDilate φ (c / N) u ^ 2) =
      nrSum φ c N a b / (Real.sqrt a.totient * Real.sqrt b.totient) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := RenormalizedArithmeticPotentialTheory.atomDilate_facts hφ hsupp hw
  set g := atomDilate φ (c / N)
  have hgM : (∫ u, g u ^ 2) = c / N * ∫ u, φ u ^ 2 := integral_atomDilate_sq φ hw
  have hext : ∀ (e : ℕ), 0 < e → ∀ j ∈ Finset.Icc 1 N,
      primeHorizonExtension (ramanujanHorizonVector e N) j =
        (1 / Real.sqrt e.totient) * (ramanujanLagCoefficient e j / Real.sqrt j) := by
    intro e he j hj
    rw [primeHorizonExtension, dif_pos hj]
    change ramanujanPoleProfile e j = _
    rw [ramanujanPoleProfile_eq he]; ring
  rw [Finset.sum_div, nrSum, Finset.sum_div]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hext b hb n hn, downwardPrimeRow_congr_smul (hext a ha)]
  have e1 : 1 / Real.sqrt b.totient * (ramanujanLagCoefficient b n / Real.sqrt n) *
      (1 / Real.sqrt a.totient * downwardPrimeRow g N
        (fun j => ramanujanLagCoefficient a j / Real.sqrt j) n) / (∫ u, g u ^ 2) =
      ramanujanLagCoefficient b n / (Real.sqrt n * (Real.sqrt a.totient * Real.sqrt b.totient)) *
        (downwardPrimeRow g N (fun j => ramanujanLagCoefficient a j / Real.sqrt j) n /
          (∫ u, g u ^ 2)) := by
    field_simp
  rw [e1, downwardRamanujanRow_eq_divisors hc hn hgsupp a, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hcorr : (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) / (∫ u, g u ^ 2) =
      (if ℓ = n then 0 else shellAutocorr φ ((Real.log ℓ - Real.log n) / (c / N))) /
        (∫ u, φ u ^ 2) := by
    split_ifs
    · simp
    · rw [bumpCorr_atomDilate_eq φ hw, hgM]; field_simp
  rw [hcorr]
  field_simp

/-- **The non-ratio pairing on conductor packets.** -/
theorem inner_nonRatio_ramanujan_eq {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hN : 1 ≤ N) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ =
      (nrSum φ c N e e' + nrSum φ c N e' e) / (Real.sqrt e.totient * Real.sqrt e'.totient) := by
  rw [inner_nonRatio_eq hφ hsupp hM hc hN, add_div,
    sum_downward_ramanujan_eq hφ hsupp hM hc hN he he',
    sum_downward_ramanujan_eq hφ hsupp hM hc hN he' he, add_div, mul_comm (Real.sqrt e'.totient)]

/-! ### The logarithmic divisor jet -/

theorem ramanujanLogDivisorJet_add (m n : ℕ) :
    ramanujanLogDivisorJet m (n + m) = ramanujanLogDivisorJet m n := by
  unfold ramanujanLogDivisorJet
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
  simp only [Nat.dvd_add_left hdm]

theorem card_filter_dvd_range {d m : ℕ} (hd : 0 < d) (hdm : d ∣ m) :
    ((range m).filter (fun r => d ∣ r)).card = m / d := by
  have h : (range m).filter (fun r => d ∣ r) =
      (range (m / d)).map ⟨fun i => i * d, fun _ _ h => Nat.eq_of_mul_eq_mul_right hd h⟩ := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hr, i, rfl⟩
      refine ⟨i, ?_, mul_comm i d⟩
      rw [Nat.lt_div_iff_mul_lt' hdm]; linarith [mul_comm d i]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, Dvd.intro_left i rfl⟩
      rw [Nat.lt_div_iff_mul_lt' hdm] at hi; simpa [mul_comm] using hi
  rw [h, Finset.card_map, Finset.card_range]

/-- The divisor jet has mean `Λ(m)` over a period: `Σ_{r < m} J_m(r) = m Λ(m)`. -/
theorem sum_range_ramanujanLogDivisorJet {m : ℕ} (hm : 0 < m) :
    ∑ r ∈ range m, ramanujanLogDivisorJet m r = m * ArithmeticFunction.vonMangoldt m := by
  unfold ramanujanLogDivisorJet
  rw [Finset.sum_comm]
  have hterm : ∀ d ∈ m.divisors, ∑ r ∈ range m, (if d ∣ r then
      (ArithmeticFunction.moebius (m / d) : ℝ) * d * Real.log d else 0) =
      m * ((ArithmeticFunction.moebius (m / d) : ℝ) * Real.log d) := by
    intro d hd
    have hdm := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_dvd_range hd0 hdm, nsmul_eq_mul,
      Nat.cast_div hdm (by exact_mod_cast hd0.ne')]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  have h1 : ArithmeticFunction.vonMangoldt m = ∑ d ∈ m.divisors,
      Real.log d * ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) := by
    rw [← ArithmeticFunction.log_mul_moebius_eq_vonMangoldt, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (ArithmeticFunction.log a) *
        ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) b))]
    simp only [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply]
  rw [h1]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-! ### Interior and exterior products -/

/-- The interior Mangoldt pairing, `ℓ ≤ N`, where `(Λ ∗ c_a)(ℓ) = c_a(ℓ) log ℓ − J_a(ℓ)`. -/
def nrInterior (φ : ℝ → ℝ) (c : ℝ) (N a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Icc 1 N,
    (if ℓ = n then 0 else shellAutocorr φ ((Real.log ℓ - Real.log n) / (c / N))) /
      (∫ u, φ u ^ 2) * ramanujanLagCoefficient b n *
        (Real.log ℓ * ramanujanLagCoefficient a ℓ - ramanujanLogDivisorJet a ℓ) /
          (Real.sqrt n * Real.sqrt ℓ)

/-- The exterior products `N < ℓ ≤ N e^{c/N}`. -/
def nrExterior (φ : ℝ → ℝ) (c : ℝ) (N a b : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Ioc N (exteriorPrimeCutoff c N),
    shellAutocorr φ ((Real.log ℓ - Real.log n) / (c / N)) / (∫ u, φ u ^ 2) *
      ramanujanLagCoefficient b n * horizonRamanujanMangoldt a N ℓ / (Real.sqrt n * Real.sqrt ℓ)

theorem nrSum_eq_interior_add_exterior (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (a b : ℕ) : nrSum φ c N a b = nrInterior φ c N a b + nrExterior φ c N a b := by
  have hNL := (exteriorPrimeCutoff_bounds hc hN).1
  have hsplit : Finset.Icc 1 (exteriorPrimeCutoff c N) =
      Finset.Icc 1 N ∪ Finset.Ioc N (exteriorPrimeCutoff c N) := by
    ext ℓ; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N (exteriorPrimeCutoff c N)) := by
    rw [Finset.disjoint_left]; intro ℓ h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [nrSum, nrInterior, nrExterior, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hℓ1 := (Finset.mem_Icc.mp hℓ).1
    rw [horizonRamanujanMangoldt_of_le (Finset.mem_Icc.mp hℓ).2,
      sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet a hℓ1]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have : ℓ ≠ n := by
      have := (Finset.mem_Ioc.mp hℓ).1; have := (Finset.mem_Icc.mp hn).2; omega
    rw [if_neg this]

section Exterior

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- **The exterior products are negligible**: at most `2(2c + 1)(c + 1) σ(b) φ(a) log(4N)/N`. -/
theorem abs_nrExterior_le {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (hcN : c ≤ N) (a b : ℕ) :
    |nrExterior φ c N a b| ≤ 2 * (2 * c + 1) * (c + 1) * (∑ t ∈ b.divisors, (t : ℝ)) *
      a.totient * Real.log (4 * N) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set w := c / N with hwdef
  have hw : 0 < w := div_pos hc hN0
  have hw1 : w ≤ 1 := (div_le_one hN0).mpr hcN
  set L := exteriorPrimeCutoff c N
  set σ := ∑ t ∈ b.divisors, (t : ℝ)
  have hσ : 0 ≤ σ := by positivity
  set M := ∫ u, φ u ^ 2
  have hNL := (exteriorPrimeCutoff_bounds hc hN).1
  have hLle : (L : ℝ) < N * Real.exp w + 1 := Nat.ceil_lt_add_one (by positivity)
  have hexp : Real.exp w ≤ 1 + 2 * w := by
    have h := Real.abs_exp_sub_one_le (x := w) (by rw [abs_of_pos hw]; exact hw1)
    rw [abs_of_pos hw] at h; linarith [le_abs_self (Real.exp w - 1)]
  have hNw : (N : ℝ) * w = c := by rw [hwdef]; field_simp
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hL3 : (L : ℝ) ≤ 4 * N := by
    have h1 : (N : ℝ) * Real.exp w ≤ N * (1 + 2 * w) := mul_le_mul_of_nonneg_left hexp hN0.le
    linarith
  have hlogL : ∀ ℓ ∈ Finset.Ioc N L, Real.log ℓ ≤ Real.log (4 * N) := fun ℓ hℓ =>
    Real.log_le_log (by
      have h := (Finset.mem_Ioc.mp hℓ).1
      exact_mod_cast (show 0 < ℓ by omega))
      ((by exact_mod_cast (Finset.mem_Ioc.mp hℓ).2 : (ℓ : ℝ) ≤ L).trans hL3)
  have hlog0 : 0 ≤ Real.log (4 * N) := Real.log_nonneg (by linarith)
  set C := 2 * σ * a.totient * Real.log (4 * N) / N with hC
  have hC0 : 0 ≤ C := by positivity
  set Z := N * Real.exp (-w) with hZ
  have hpt : ∀ n ∈ Finset.Icc 1 N, ∀ ℓ ∈ Finset.Ioc N L,
      |shellAutocorr φ ((Real.log ℓ - Real.log n) / w) / M * ramanujanLagCoefficient b n *
        horizonRamanujanMangoldt a N ℓ / (Real.sqrt n * Real.sqrt ℓ)| ≤
        if Z < (n : ℝ) then C else 0 := by
    intro n hn ℓ hℓ
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hn).2
    have hℓN : (N : ℝ) < ℓ := by exact_mod_cast (Finset.mem_Ioc.mp hℓ).1
    have hℓ0 : (0 : ℝ) < ℓ := hN0.trans hℓN
    split_ifs with hz
    · have hG := abs_shellAutocorr_le' hφ hsupp ((Real.log ℓ - Real.log n) / w)
      have hR := abs_horizonRamanujanMangoldt_le a N ℓ
      have hcb := abs_ramanujanLagCoefficient_le b n
      have hsn : Real.sqrt N * Real.exp (-w / 2) ≤ Real.sqrt n := by
        have h1 : Real.sqrt Z = Real.sqrt N * Real.exp (-w / 2) := by
          rw [hZ, Real.sqrt_mul hN0.le, show Real.exp (-w) = Real.exp (-w / 2) ^ 2 by
            rw [← Real.exp_nat_mul]; ring_nf, Real.sqrt_sq (Real.exp_pos _).le]
        rw [← h1]; exact Real.sqrt_le_sqrt hz.le
      have hsl : Real.sqrt N ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt hℓN.le
      have hden : (N : ℝ) * Real.exp (-w / 2) ≤ Real.sqrt n * Real.sqrt ℓ := by
        calc (N : ℝ) * Real.exp (-w / 2) = Real.sqrt N * Real.exp (-w / 2) * Real.sqrt N := by
              rw [mul_right_comm, Real.mul_self_sqrt hN0.le]
          _ ≤ Real.sqrt n * Real.sqrt ℓ := mul_le_mul hsn hsl (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      have he2 : Real.exp (-w / 2) ≥ 1 / 2 := by
        have := Real.add_one_le_exp (-w / 2); linarith
      have hden' : (N : ℝ) / 2 ≤ Real.sqrt n * Real.sqrt ℓ := by nlinarith
      rw [abs_div, abs_mul, abs_mul, abs_div, abs_of_pos hM,
        abs_of_pos (mul_pos (Real.sqrt_pos.mpr hn0) (Real.sqrt_pos.mpr hℓ0))]
      have hlogℓ : Real.log ℓ ≤ Real.log (4 * N) := hlogL ℓ hℓ
      have hnum : |shellAutocorr φ ((Real.log ℓ - Real.log n) / w)| / M *
          |ramanujanLagCoefficient b n| * |horizonRamanujanMangoldt a N ℓ| ≤
          σ * (a.totient * Real.log (4 * N)) := by
        have h1 : |shellAutocorr φ ((Real.log ℓ - Real.log n) / w)| / M ≤ 1 := by
          rw [div_le_one hM]; exact hG
        have h2 : |horizonRamanujanMangoldt a N ℓ| ≤ a.totient * Real.log (4 * N) :=
          hR.trans (mul_le_mul_of_nonneg_left hlogℓ (Nat.cast_nonneg _))
        calc _ ≤ 1 * σ * (a.totient * Real.log (4 * N)) :=
              mul_le_mul (mul_le_mul h1 hcb (abs_nonneg _) zero_le_one) h2 (abs_nonneg _)
                (by positivity)
          _ = _ := by ring
      rw [hC, div_le_div_iff₀ (by positivity) hN0]
      calc _ * N ≤ σ * (a.totient * Real.log (4 * N)) * N :=
            mul_le_mul_of_nonneg_right hnum hN0.le
        _ ≤ 2 * σ * a.totient * Real.log (4 * N) * (Real.sqrt n * Real.sqrt ℓ) := by
            nlinarith [mul_nonneg hσ (mul_nonneg (Nat.cast_nonneg a.totient) hlog0)]
    · push Not at hz
      have hG : shellAutocorr φ ((Real.log ℓ - Real.log n) / w) = 0 := by
        apply shellAutocorr_eq_zero_of_one_le hφ hsupp
        rw [le_div_iff₀ hw, one_mul]
        have h1 : Real.log Z = Real.log N - w := by
          rw [hZ, Real.log_mul hN0.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
        have h2 : Real.log n ≤ Real.log Z := Real.log_le_log hn0 hz
        have h3 : Real.log N < Real.log ℓ := Real.log_lt_log hN0 hℓN
        linarith
      rw [hG]; simp
  have hcardn : (((Finset.Icc 1 N).filter (fun n : ℕ => Z < n)).card : ℝ) ≤ c + 1 := by
    have hZ0 : 0 ≤ Z := by positivity
    have hZN : Z ≤ N := by
      rw [hZ]; exact mul_le_of_le_one_right hN0.le (Real.exp_le_one_iff.mpr (by linarith))
    have h := card_filter_gt_le N hZ0 hZN
    have hNZ : (N : ℝ) - Z ≤ c := by
      rw [hZ]
      have h1 := Real.add_one_le_exp (-w)
      have h2 : (N : ℝ) * (-w + 1) ≤ N * Real.exp (-w) := mul_le_mul_of_nonneg_left h1 hN0.le
      linarith
    linarith
  have hcardℓ : ((Finset.Ioc N L).card : ℝ) ≤ 2 * c + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub hNL]
    have h1 : (N : ℝ) * Real.exp w ≤ N * (1 + 2 * w) := mul_le_mul_of_nonneg_left hexp hN0.le
    linarith
  rw [nrExterior]
  calc _ ≤ ∑ n ∈ Finset.Icc 1 N, ∑ ℓ ∈ Finset.Ioc N L, (if Z < (n : ℝ) then C else 0) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ℓ hℓ => hpt n hn ℓ hℓ)
    _ = ((Finset.Ioc N L).card : ℝ) * (((Finset.Icc 1 N).filter (fun n : ℕ => Z < n)).card * C) := by
        rw [Finset.sum_comm, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter,
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * c + 1) * ((c + 1) * C) :=
        mul_le_mul hcardℓ (mul_le_mul_of_nonneg_right hcardn hC0) (by positivity) (by positivity)
    _ = _ := by rw [hC]; ring

end Exterior

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
