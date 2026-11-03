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
  rw [Finset.sum_congr rfl fun n hn => by rw [hup n hn],
    Finset.sum_congr rfl fun j hj => by rw [hdown j hj]]
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
  rw [hext b hb n hn, downwardPrimeRow_congr_smul (hext a ha), mul_assoc,
    mul_div_assoc, downwardRamanujanRow_eq_divisors hc hn hgsupp a, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have hcorr : (if ℓ = n then 0 else bumpCorr g (Real.log ℓ - Real.log n)) / (∫ u, g u ^ 2) =
      (if ℓ = n then 0 else shellAutocorr φ ((Real.log ℓ - Real.log n) / (c / N))) /
        (∫ u, φ u ^ 2) := by
    split_ifs
    · simp
    · rw [bumpCorr_atomDilate_eq φ hw, hgM]; field_simp
  rw [hcorr]
  ring

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
  rw [show (d ∣ n + m) = (d ∣ n) from propext (Nat.dvd_add_left hdm)]

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
      rw [Nat.lt_div_iff_mul_lt' hdm] at hi; exact hi
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
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m)
    ArithmeticFunction.log_mul_moebius_eq_vonMangoldt
  simp only [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => ArithmeticFunction.log x * (ArithmeticFunction.moebius y : ℝ))] at h
  rw [← h]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [ArithmeticFunction.log_apply, ArithmeticFunction.intCoe_apply]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
