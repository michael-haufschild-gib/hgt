import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity

/-!
# The Hardy–Littlewood tuple series from radical-closed damped rows

Fix a finite set `S` of primes, `P = ∏_{p ∈ S} p`, and the radical-closed damped row
`c(d) = μ(d) d^{-ε}` on the divisors of `P`. Its response is a product of local factors,

`s(n) = ∏_{p ∈ S} g_p(n)`,  `g_p(n) = 1 - p^{-ε}` if `p ∣ n` and `1` otherwise,

so each prime acts on its own residue. By the Chinese remainder theorem every translated moment
factors exactly over `S`:

`(1/P!) Σ_{n < P!} ∏_{i < k} s(n + h_i) = ∏_{p ∈ S} m_p(ε, H)`,  `m_p(ε, H) = (1/p) Σ_{r < p} ∏_i g_p(r + h_i)`.

At `k = 1` the local mean is `1 - p^{-1-ε}`, the density of the row. At zero damping `g_p` is the
indicator of `p ∤ n`, so `m_p(0, H) = 1 - ν_p(H)/p`, where `ν_p(H)` counts the residues occupied by
`-H`. The normalized moments therefore converge:

`∏_{p ∈ S} m_p(ε, H)/(1 - p^{-1-ε})^k → ∏_{p ∈ S} (1 - ν_p(H)/p)/(1 - 1/p)^k`   as `ε → 0`.

For distinct shifts the local factor is within `k²/p²` of `1` once `p` exceeds the spread of `H`.
Hence the product over all primes converges to the Hardy–Littlewood singular series `𝔖(H)` of
prime `k`-tuples. `𝔖(H)` is `0` for inadmissible tuples and positive for admissible ones.
For `H = (0, h)` it is the series of the pair law, `𝔖(h) = Σ_q μ²(q) c_q(h)/φ(q)²`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-! ## §1. Radical-closed rows and their local factors -/

/-- The product of a finite set of primes. -/
def primeSetProduct (S : Finset Nat.Primes) : ℕ := ∏ p ∈ S, (p : ℕ)

theorem primeSetProduct_pos (S : Finset Nat.Primes) : 0 < primeSetProduct S :=
  prod_pos fun p _ => p.prop.pos

/-- The radical-closed damped row on the divisors of `P`. -/
def radicalClosedDampedRow (ε : ℝ) (P d : ℕ) : ℝ :=
  if d ∣ P then (moebius d : ℝ) * (d : ℝ) ^ (-ε) else 0

/-- The local damped factor of the prime `p`. -/
def localDampedFactor (ε : ℝ) (p n : ℕ) : ℝ := if p ∣ n then 1 - (p : ℝ) ^ (-ε) else 1

theorem primeFactors_gcd_primeSetProduct (S : Finset Nat.Primes) (n : ℕ) :
    (Nat.gcd n (primeSetProduct S)).primeFactors =
      (S.map ⟨Subtype.val, Subtype.val_injective⟩).filter (· ∣ n) := by
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_map]
  constructor
  · rintro ⟨hq, hdvd, -⟩
    have hP : q ∣ primeSetProduct S := hdvd.trans (Nat.gcd_dvd_right _ _)
    obtain ⟨p, hpS, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hP
    have := (Nat.prime_dvd_prime_iff_eq hq p.prop).mp hqp
    exact ⟨⟨p, hpS, this.symm⟩, hdvd.trans (Nat.gcd_dvd_left _ _)⟩
  · rintro ⟨⟨p, hpS, rfl⟩, hdvd⟩
    refine ⟨p.prop, Nat.dvd_gcd hdvd (dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hpS), ?_⟩
    exact (Nat.gcd_pos_of_pos_right _ (primeSetProduct_pos S)).ne'

/-- **The response is a product of local factors.** -/
theorem sieveSeq_radicalClosedDampedRow (ε : ℝ) (S : Finset Nat.Primes) (n : ℕ) :
    sieveSeq (primeSetProduct S) (radicalClosedDampedRow ε (primeSetProduct S)) n =
      ∏ p ∈ S, localDampedFactor ε p n := by
  set P := primeSetProduct S
  have hP := primeSetProduct_pos S
  have hg : Nat.gcd n P ≠ 0 := (Nat.gcd_pos_of_pos_right _ hP).ne'
  have hsum : sieveSeq P (radicalClosedDampedRow ε P) n = RHTower.pmPowerDampedDivisorCoeff ε (Nat.gcd n P) := by
    unfold sieveSeq radicalClosedDampedRow RHTower.pmPowerDampedDivisorCoeff
    rw [← sum_filter]
    refine sum_congr ?_ fun d _ => rfl
    ext d
    simp only [mem_filter, mem_Icc, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hb : d ∣ P → 1 ≤ d ∧ d ≤ P := fun hdP =>
      ⟨Nat.pos_of_dvd_of_pos hdP hP, Nat.le_of_dvd hP hdP⟩
    tauto
  rw [hsum, RHTower.pmPowerDampedDivisorCoeff_eq_prod ε hg, primeFactors_gcd_primeSetProduct,
    prod_filter, prod_map]
  rfl

theorem localDampedFactor_periodic (ε : ℝ) (p : ℕ) :
    Function.Periodic (localDampedFactor ε p) p := fun n => by
  simp only [localDampedFactor, Nat.dvd_add_self_right]

/-! ## §2. The Chinese remainder factorization -/

theorem sum_range_mul_of_periodic {F : ℕ → ℝ} {P : ℕ} (hF : Function.Periodic F P) (K : ℕ) :
    ∑ n ∈ range (K * P), F n = K * ∑ n ∈ range P, F n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have : ∑ x ∈ range P, F (K * P + x) = ∑ x ∈ range P, F x :=
      sum_congr rfl fun x _ => by rw [add_comm]; exact hF.nat_mul K x
    rw [this]
    push_cast
    ring

/-- **Chinese remainder factorization over a set of primes.** -/
theorem sum_range_primeSetProduct_prod (S : Finset Nat.Primes) (G : Nat.Primes → ℕ → ℝ)
    (hG : ∀ p, Function.Periodic (G p) (p : ℕ)) :
    ∑ n ∈ range (primeSetProduct S), ∏ p ∈ S, G p n = ∏ p ∈ S, ∑ r ∈ range (p : ℕ), G p r := by
  induction S using Finset.induction_on with
  | empty => simp [primeSetProduct]
  | insert q S hq ih =>
    have hcop : (q : ℕ).Coprime (primeSetProduct S) :=
      Nat.Coprime.prod_right fun p hp => (Nat.coprime_primes q.prop p.prop).mpr
        (fun h => hq (by rw [Subtype.ext h] at *; exact hp))
    have hper : Function.Periodic (fun n => ∏ p ∈ S, G p n) (primeSetProduct S) := fun n => by
      refine prod_congr rfl fun p hp => ?_
      obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp
      have hPm : primeSetProduct S = (p : ℕ) * m := hm
      rw [hPm, mul_comm]
      exact (hG p).nat_mul m n
    have hP : primeSetProduct (insert q S) = (q : ℕ) * primeSetProduct S := by
      simp only [primeSetProduct, prod_insert hq]
    have hsplit : ∀ n, ∏ p ∈ insert q S, G p n = G q n * ∏ p ∈ S, G p n := fun n => prod_insert hq
    rw [hP, sum_congr rfl fun n _ => hsplit n,
      RHTower.DeletionCoprimeWords.coprime_period_sum_mul q.prop.pos (primeSetProduct_pos S) hcop
        (hG q) hper, ih, prod_insert hq]

/-- The local tuple mean `m_p(ε, H) = (1/p) Σ_{r < p} ∏_i g_p(r + h_i)`. -/
def localTupleMean {k : ℕ} (ε : ℝ) (p : ℕ) (H : Fin k → ℕ) : ℝ :=
  (∑ r ∈ range p, ∏ i, localDampedFactor ε p (r + H i)) / p

/-- **Every translated moment of a radical-closed damped row factors over its primes.** -/
theorem translatedMoment_radicalClosedDampedRow {k : ℕ} (ε : ℝ) (S : Finset Nat.Primes)
    (H : Fin k → ℕ) :
    SieveMoments.translatedMoment (primeSetProduct S) (radicalClosedDampedRow ε (primeSetProduct S)) H =
      ∏ p ∈ S, localTupleMean ε p H := by
  set P := primeSetProduct S with hPdef
  have hP := primeSetProduct_pos S
  have hfac : (fun n => ∏ i, sieveSeq P (radicalClosedDampedRow ε P) (n + H i)) =
      fun n => ∏ p ∈ S, ∏ i, localDampedFactor ε p (n + H i) := by
    funext n
    rw [hPdef]
    simp_rw [sieveSeq_radicalClosedDampedRow]
    exact prod_comm
  have hper : ∀ p : Nat.Primes, Function.Periodic (fun n => ∏ i, localDampedFactor ε p (n + H i))
      (p : ℕ) := fun p n => by
    refine prod_congr rfl fun i _ => ?_
    rw [show n + p + H i = n + H i + p by ring]
    exact localDampedFactor_periodic ε p _
  have hperS : Function.Periodic (fun n => ∏ p ∈ S, ∏ i, localDampedFactor ε p (n + H i)) P :=
    fun n => prod_congr rfl fun p hp => by
      obtain ⟨m, hm⟩ := dvd_prod_of_mem (fun p : Nat.Primes => (p : ℕ)) hp
      have hPm : P = (p : ℕ) * m := hm
      rw [hPm, mul_comm]
      exact (hper p).nat_mul m n
  have hdvd : P ∣ P.factorial := Nat.dvd_factorial hP le_rfl
  obtain ⟨K, hK⟩ := hdvd
  unfold SieveMoments.translatedMoment
  rw [hfac, hK, mul_comm P K, sum_range_mul_of_periodic hperS,
    sum_range_primeSetProduct_prod S _ hper]
  have hP0 : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hK0 : (K : ℝ) ≠ 0 := by
    rintro h
    have : K = 0 := by exact_mod_cast h
    rw [this, mul_zero] at hK
    exact (Nat.factorial_pos P).ne' hK
  unfold localTupleMean
  rw [prod_div_distrib]
  push_cast
  simp only [P, primeSetProduct, Nat.cast_prod]
  field_simp

/-! ## §3. Residue counting -/

/-- For `r < p`: `p ∣ r + h` iff `r` is the residue of `-h`. -/
theorem dvd_add_iff_eq_neg_residue {p : ℕ} (hp : 0 < p) {r : ℕ} (hr : r < p) (h : ℕ) :
    p ∣ r + h ↔ r = (p - h % p) % p := by
  have hdiv : h = p * (h / p) + h % p := (Nat.div_add_mod h p).symm
  have ha : h % p < p := Nat.mod_lt h hp
  have hiff : p ∣ r + h ↔ p ∣ r + h % p := by
    rw [hdiv, show r + (p * (h / p) + h % p) = p * (h / p) + (r + h % p) by ring,
      ← hdiv]
    exact Nat.dvd_add_right (dvd_mul_right p _)
  rw [hiff]
  by_cases ha0 : h % p = 0
  · rw [ha0, Nat.sub_zero, Nat.mod_self, add_zero]
    constructor
    · intro hd
      exact Nat.eq_zero_of_dvd_of_lt hd hr
    · rintro rfl
      exact dvd_zero p
  · rw [Nat.mod_eq_of_lt (by omega : p - h % p < p)]
    constructor
    · rintro ⟨c, hc⟩
      have hc2 : c < 2 := by
        by_contra hc2
        have : p * 2 ≤ p * c := Nat.mul_le_mul_left p (by omega)
        omega
      interval_cases c <;> omega
    · intro hre
      exact ⟨1, by omega⟩

/-- The occupied residues of a tuple are the residues of `-h_i`. -/
theorem filter_exists_dvd_eq_image {k p : ℕ} (hp : 0 < p) (H : Fin k → ℕ) :
    (range p).filter (fun r => ∃ i, p ∣ r + H i) = univ.image (fun i => (p - H i % p) % p) := by
  ext r
  simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hr, i, hi⟩
    exact ⟨i, ((dvd_add_iff_eq_neg_residue hp hr (H i)).mp hi).symm⟩
  · rintro ⟨i, rfl⟩
    have hlt : (p - H i % p) % p < p := Nat.mod_lt _ hp
    exact ⟨hlt, i, (dvd_add_iff_eq_neg_residue hp hlt (H i)).mpr rfl⟩

/-- The number `ν_p(H)` of residues occupied by `-H` modulo `p`. -/
def tupleOccupancy {k : ℕ} (p : ℕ) (H : Fin k → ℕ) : ℕ :=
  ((range p).filter fun r => ∃ i, p ∣ r + H i).card

/-- Pairwise incongruent shifts occupy `k` residues. -/
theorem tupleOccupancy_eq_of_incongruent {k p : ℕ} (hp : 0 < p) {H : Fin k → ℕ}
    (hH : ∀ i j, H i % p = H j % p → i = j) : tupleOccupancy p H = k := by
  rw [tupleOccupancy, filter_exists_dvd_eq_image hp, card_image_of_injective, card_univ,
    Fintype.card_fin]
  intro i j hij
  apply hH
  have hi := Nat.mod_lt (H i) hp
  have hj := Nat.mod_lt (H j) hp
  simp only at hij
  by_cases hi0 : H i % p = 0 <;> by_cases hj0 : H j % p = 0
  · omega
  · rw [hi0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega : p - H j % p < p)] at hij
    omega
  · rw [hj0, Nat.sub_zero, Nat.mod_self, Nat.mod_eq_of_lt (by omega : p - H i % p < p)] at hij
    omega
  · rw [Nat.mod_eq_of_lt (by omega : p - H i % p < p),
      Nat.mod_eq_of_lt (by omega : p - H j % p < p)] at hij
    omega

/-! ## §4. Density and the zero-damping limit -/

/-- **The density.** At `k = 1` the local mean is `1 - p^{-1-ε}`. -/
theorem localTupleMean_single (ε : ℝ) {p : ℕ} (hp : 0 < p) (h : ℕ) :
    localTupleMean ε p (fun _ : Fin 1 => h) = 1 - (p : ℝ) ^ (-1 - ε) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold localTupleMean localDampedFactor
  simp only [Finset.univ_unique, Fin.default_eq_zero, prod_singleton]
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcard : ((range p).filter fun r => p ∣ r + h).card = 1 := by
    have := tupleOccupancy_eq_of_incongruent hp (H := fun _ : Fin 1 => h) fun i j _ => Subsingleton.elim i j
    simpa [tupleOccupancy] using this
  have hcard' : ((range p).filter fun r => ¬ p ∣ r + h).card = p - 1 := by
    have := card_filter_add_card_filter_not (s := range p) (fun r => p ∣ r + h)
    rw [card_range, hcard] at this
    omega
  rw [hcard, hcard', Nat.cast_sub hp, Real.rpow_sub hpR, Real.rpow_neg_one]
  have hinv : (p : ℝ) ^ (-ε) * (p : ℝ) ^ ε = 1 := by rw [← Real.rpow_add hpR]; simp
  push_cast
  field_simp
  linarith

/-- At zero damping the local factor is the indicator of `p ∤ n`. -/
theorem localTupleMean_zero {k p : ℕ} (hp : 0 < p) (H : Fin k → ℕ) :
    localTupleMean 0 p H = 1 - (tupleOccupancy p H : ℝ) / p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold localTupleMean localDampedFactor
  simp only [neg_zero, Real.rpow_zero, sub_self]
  have hprod : ∀ r, ∏ i, (if p ∣ r + H i then (0 : ℝ) else 1) =
      if ∃ i, p ∣ r + H i then 0 else 1 := by
    intro r
    split_ifs with hex
    · obtain ⟨i, hi⟩ := hex
      exact prod_eq_zero (mem_univ i) (if_pos hi)
    · simp only [not_exists] at hex
      exact prod_eq_one fun i _ => if_neg (hex i)
  simp_rw [hprod]
  rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
  have hc := card_filter_add_card_filter_not (s := range p) (fun r => ∃ i, p ∣ r + H i)
  rw [card_range] at hc
  have : ((range p).filter fun r => ¬ ∃ i, p ∣ r + H i).card = p - tupleOccupancy p H := by
    unfold tupleOccupancy
    omega
  rw [this, Nat.cast_sub (by unfold tupleOccupancy; omega)]
  field_simp

theorem continuous_localTupleMean {k p : ℕ} (hp : 0 < p) (H : Fin k → ℕ) :
    Continuous fun ε => localTupleMean ε p H := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  unfold localTupleMean localDampedFactor
  refine Continuous.div_const (continuous_finsetSum _ fun r _ =>
    continuous_finsetProd _ fun i _ => ?_) _
  split_ifs
  · exact continuous_const.sub (continuous_const.rpow continuous_neg fun _ => Or.inl hpR.ne')
  · exact continuous_const

/-- The local singular factor `(1 - ν_p(H)/p)/(1 - 1/p)^k`. -/
def tupleSingularFactor {k : ℕ} (p : ℕ) (H : Fin k → ℕ) : ℝ :=
  (1 - (tupleOccupancy p H : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ k

/-- **Zero-damping limit over a finite set of primes.** The normalized translated moments of the
radical-closed damped rows tend to the truncated singular series. -/
theorem tendsto_normalized_translatedMoment {k : ℕ} (S : Finset Nat.Primes) (H : Fin k → ℕ) :
    Tendsto (fun ε => SieveMoments.translatedMoment (primeSetProduct S)
        (radicalClosedDampedRow ε (primeSetProduct S)) H /
          (∏ p ∈ S, (1 - ((p : ℕ) : ℝ) ^ (-1 - ε))) ^ k)
      (𝓝 0) (𝓝 (∏ p ∈ S, tupleSingularFactor p H)) := by
  simp_rw [translatedMoment_radicalClosedDampedRow, ← prod_pow, ← prod_div_distrib]
  refine tendsto_finsetProd _ fun p _ => ?_
  have hp := p.prop.pos
  have hpR : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  have hnum := (continuous_localTupleMean hp H).continuousAt (x := 0) |>.tendsto
  have hden : Tendsto (fun ε : ℝ => (1 - ((p : ℕ) : ℝ) ^ (-1 - ε)) ^ k) (𝓝 0)
      (𝓝 ((1 - 1 / ((p : ℕ) : ℝ)) ^ k)) := by
    have hc : Continuous fun ε : ℝ => (1 - ((p : ℕ) : ℝ) ^ (-1 - ε)) ^ k :=
      (continuous_const.sub (continuous_const.rpow (continuous_const.sub continuous_id)
        fun _ => Or.inl (by positivity))).pow k
    have := hc.continuousAt (x := 0) |>.tendsto
    simpa [Real.rpow_neg_one, one_div] using this
  have hne : (1 - 1 / ((p : ℕ) : ℝ)) ^ k ≠ 0 := by
    apply pow_ne_zero
    have : 1 / ((p : ℕ) : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hpR
    linarith
  have := hnum.div hden hne
  rw [localTupleMean_zero hp] at this
  exact this

/-! ## §5. The singular series over all primes -/

/-- `1 - k²x² ≤ (1 - kx)/(1 - x)^k ≤ 1` for `0 < x < 1` and `kx ≤ 1`. -/
theorem singularFactor_bounds {k : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hkx : (k : ℝ) * x ≤ 1) :
    1 - (k : ℝ) ^ 2 * x ^ 2 ≤ (1 - k * x) / (1 - x) ^ k ∧ (1 - k * x) / (1 - x) ^ k ≤ 1 := by
  have hpos : 0 < (1 - x) ^ k := pow_pos (by linarith) k
  have hbern : 1 - (k : ℝ) * x ≤ (1 - x) ^ k := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) k
    simpa [sub_eq_add_neg, mul_neg] using this
  have hbern2 : 1 + (k : ℝ) * x ≤ (1 + x) ^ k := one_add_mul_le_pow (by linarith) k
  have hprod : (1 - x) ^ k * (1 + x) ^ k ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  constructor
  · rw [le_div_iff₀ hpos]
    have h1 : (1 - x) ^ k * (1 + (k : ℝ) * x) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hbern2 hpos.le).trans hprod
    nlinarith
  · rw [div_le_one hpos]
    exact hbern

/-- The singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)/(1 - 1/p)^k`. -/
def tupleSingularSeries {k : ℕ} (H : Fin k → ℕ) : ℝ := ∏' p : Nat.Primes, tupleSingularFactor p H

theorem tupleSingularFactor_sub_one_bound {k : ℕ} {H : Fin k → ℕ} (hH : Function.Injective H)
    {p : Nat.Primes} (hpB : ∑ i, H i < (p : ℕ)) :
    |tupleSingularFactor p H - 1| ≤ (k : ℝ) ^ 2 * (1 / ((p : ℕ) : ℝ) ^ 2) := by
  have hp := p.prop.pos
  have hpR : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
  have hle : ∀ i, H i < (p : ℕ) := fun i =>
    lt_of_le_of_lt (single_le_sum (fun j _ => Nat.zero_le (H j)) (mem_univ i)) hpB
  have hocc : tupleOccupancy (p : ℕ) H = k := by
    refine tupleOccupancy_eq_of_incongruent hp fun i j hij => hH ?_
    rwa [Nat.mod_eq_of_lt (hle i), Nat.mod_eq_of_lt (hle j)] at hij
  have hkp : k ≤ (p : ℕ) := by
    have := card_le_card (filter_subset (fun r => ∃ i, (p : ℕ) ∣ r + H i) (range (p : ℕ)))
    rw [card_range] at this
    unfold tupleOccupancy at hocc
    omega
  set x : ℝ := 1 / ((p : ℕ) : ℝ)
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by rw [div_lt_one (by linarith)]; exact hpR
  have hkx : (k : ℝ) * x ≤ 1 := by
    simp only [x]
    rw [mul_one_div, div_le_one (by linarith)]
    exact_mod_cast hkp
  obtain ⟨hlo, hhi⟩ := singularFactor_bounds hx0 hx1 hkx
  have heq : tupleSingularFactor p H = (1 - k * x) / (1 - x) ^ k := by
    simp only [tupleSingularFactor, hocc, x]
    ring
  rw [heq, abs_le]
  have : (1 / ((p : ℕ) : ℝ) ^ 2) = x ^ 2 := by simp only [x]; ring
  rw [this]
  constructor <;> nlinarith [sq_nonneg (k : ℝ), sq_nonneg x]

/-- **The singular series converges** for distinct shifts. -/
theorem hasProd_tupleSingularSeries {k : ℕ} {H : Fin k → ℕ} (hH : Function.Injective H) :
    HasProd (fun p : Nat.Primes => tupleSingularFactor p H) (tupleSingularSeries H) := by
  have hsum : Summable fun p : Nat.Primes => tupleSingularFactor p H - 1 := by
    have hs : Summable fun p : Nat.Primes => (k : ℝ) ^ 2 * (1 / ((p : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective).mul_left _
    refine Summable.of_norm_bounded_eventually hs ?_
    have hfin : {p : Nat.Primes | ¬ ∑ i, H i < (p : ℕ)}.Finite := by
      refine (Set.finite_le_nat (∑ i, H i)).preimage (Subtype.val_injective.injOn) |>.subset ?_
      intro p hp
      simp only [not_lt] at hp ⊢
      exact hp
    filter_upwards [hfin.compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hp
    rw [Real.norm_eq_abs]
    exact tupleSingularFactor_sub_one_bound hH hp
  have hm := Real.multipliable_one_add_of_summable hsum
  simp only [add_sub_cancel] at hm
  exact hm.hasProd

/-- **The iterated limit.** Truncated singular series converge to `𝔖(H)` along finite sets of
primes; by `tendsto_normalized_translatedMoment` each truncation is the zero-damping limit of
normalized translated moments of radical-closed damped rows. -/
theorem tendsto_truncated_tupleSingularSeries {k : ℕ} {H : Fin k → ℕ} (hH : Function.Injective H) :
    Tendsto (fun S : Finset Nat.Primes => ∏ p ∈ S, tupleSingularFactor p H) atTop
      (𝓝 (tupleSingularSeries H)) :=
  hasProd_tupleSingularSeries hH

/-- **Inadmissible tuples.** If `-H` occupies every residue modulo some prime, `𝔖(H) = 0`. -/
theorem tupleSingularSeries_eq_zero_of_inadmissible {k : ℕ} {H : Fin k → ℕ} (hH : Function.Injective H)
    {p : Nat.Primes} (hp : tupleOccupancy (p : ℕ) H = p) : tupleSingularSeries H = 0 := by
  refine (hasProd_tupleSingularSeries hH).unique (hasProd_zero_of_exists_eq_zero ⟨p, ?_⟩)
  have hpR : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.pos
  simp [tupleSingularFactor, hp, hpR.ne']

/-- **Admissible tuples.** If `-H` omits a residue modulo every prime, `𝔖(H) > 0`. -/
theorem tupleSingularSeries_pos_of_admissible {k : ℕ} {H : Fin k → ℕ} (hH : Function.Injective H)
    (hadm : ∀ p : Nat.Primes, tupleOccupancy (p : ℕ) H < p) : 0 < tupleSingularSeries H := by
  have hfac : ∀ p : Nat.Primes, 0 < 1 + (tupleSingularFactor p H - 1) := by
    intro p
    have hpR : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.prop.one_lt
    have hlt : (tupleOccupancy (p : ℕ) H : ℝ) < (p : ℕ) := by exact_mod_cast hadm p
    rw [add_sub_cancel]
    unfold tupleSingularFactor
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]
      exact hlt
    · apply pow_pos
      have : 1 / ((p : ℕ) : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hpR
      linarith
  have hsum : Summable fun p : Nat.Primes => tupleSingularFactor p H - 1 := by
    have hm := (hasProd_tupleSingularSeries hH)
    have hs : Summable fun p : Nat.Primes => (k : ℝ) ^ 2 * (1 / ((p : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective Subtype.val_injective).mul_left _
    refine Summable.of_norm_bounded_eventually hs ?_
    have hfin : {p : Nat.Primes | ¬ ∑ i, H i < (p : ℕ)}.Finite := by
      refine (Set.finite_le_nat (∑ i, H i)).preimage (Subtype.val_injective.injOn) |>.subset ?_
      intro p hp
      simp only [not_lt] at hp ⊢
      exact hp
    filter_upwards [hfin.compl_mem_cofinite] with p hp
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hp
    rw [Real.norm_eq_abs]
    exact tupleSingularFactor_sub_one_bound hH hp
  have hprod := hasProd_tupleSingularSeries hH
  have heq : (fun p : Nat.Primes => tupleSingularFactor p H) =
      fun p : Nat.Primes => 1 + (tupleSingularFactor p H - 1) := funext fun p => by ring
  rw [← hprod.tprod_eq, heq, ← Real.rexp_tsum_eq_tprod hfac
    (Real.summable_log_one_add_of_summable hsum)]
  exact Real.exp_pos _

/-! ## §6. Pairs: the Euler form agrees with the Ramanujan form -/

theorem tupleOccupancy_pair {p : ℕ} (hp : 0 < p) (h : ℕ) :
    tupleOccupancy p ![0, h] = if p ∣ h then 1 else 2 := by
  rw [tupleOccupancy, filter_exists_dvd_eq_image hp]
  have himg : (univ.image fun i : Fin 2 => (p - (![0, h] : Fin 2 → ℕ) i % p) % p) =
      {0, (p - h % p) % p} := by
    ext r
    simp only [mem_image, mem_univ, true_and, Fin.exists_fin_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Nat.zero_mod, Nat.sub_zero, Nat.mod_self, mem_insert, mem_singleton]
    tauto
  rw [himg]
  have ha : h % p < p := Nat.mod_lt h hp
  by_cases hdiv : p ∣ h
  · rw [if_pos hdiv, (Nat.dvd_iff_mod_eq_zero).mp hdiv, Nat.sub_zero, Nat.mod_self,
      insert_eq_of_mem (mem_singleton_self 0), card_singleton]
  · have h0 : h % p ≠ 0 := fun h0 => hdiv (Nat.dvd_of_mod_eq_zero h0)
    rw [if_neg hdiv, Nat.mod_eq_of_lt (by omega : p - h % p < p), card_pair (by omega)]

theorem tupleSingularFactor_pair {p : ℕ} (hp : p.Prime) (h : ℕ) :
    tupleSingularFactor p ![0, h] = 1 + ramanujanLagWeight h p / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [tupleSingularFactor, tupleOccupancy_pair hp.pos, ramanujanLagWeight_prime hp]
  split_ifs
  · push_cast
    field_simp
    ring
  · push_cast
    field_simp
    ring

/-- **The Euler form of the pair series is the Ramanujan form.** For `h ≥ 1`,
`∏_p (1 - ν_p(0, h)/p)/(1 - 1/p)² = Σ_q μ²(q) c_q(h)/φ(q)²`. -/
theorem tupleSingularSeries_pair {h : ℕ} (hh : 1 ≤ h) :
    tupleSingularSeries ![0, h] = hardyLittlewoodSingularSeries h := by
  have hinj : Function.Injective (![0, h] : Fin 2 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  refine (hasProd_tupleSingularSeries hinj).unique ?_
  have hf : (fun p : Nat.Primes => tupleSingularFactor p ![0, h]) =
      fun p : Nat.Primes => 1 + ramanujanLagWeight h p / (((p : ℕ) : ℝ) - 1) ^ 2 :=
    funext fun p => tupleSingularFactor_pair p.prop h
  rw [hf]
  exact hasProd_hardyLittlewoodSingularSeries hh

end

end GaloisForLFunctions.BezoutValuationIncidence
