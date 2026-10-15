import GaloisForLFunctions.RHTower.EvenSectorPolarStripCeiling
import GaloisForLFunctions.RHTower.PrimitiveHyperplaneBlindPositivity

/-!
# Even pole-free positivity of weights bounded below forces RH

Let `lam` be Weil-positive on all even compactly supported `C²` tests with `f̂(i/2) = 0`
(`WeilPositiveEvenPolar`): no pole weight and no odd test are involved.

**Theorem** (`riemannHypothesis_of_weilPositiveEvenPolar_of_ge`).  If moreover `lam ≥ −C` on
`n ≥ 2`, then RH holds and `lam = Λ` on `n ≥ 2`.

**Corollary** (`riemannHypothesis_iff_exists_bddBelow_weilPositiveEvenPolar`).  RH holds iff some
weight system bounded below is Weil-positive on even pole-free tests.

**Corollary** (`riemannHypothesis_iff_archimedeanNonnegOnEvenPolarNonnegCone`).  RH holds iff the
archimedean energy is nonnegative on every nonnegative combination of autocorrelations of even tests
with `f̂(i/2) = 0` whose values at every `±log n`, `n ≥ 2`, are nonnegative.  This criterion has no
primes, no zeros, no pole term and only even tests.

Proof.  Even pole-free node tests give `lam(n) ≤ C √n (1 + log n)`
(`exists_abs_le_of_weilPositiveEvenPolar_of_ge`), hence pole-free strip positivity and the
log-density ceiling `Σ_{nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)(log N)²` (`even_log_density_le_of_polar`).
With `lam ≥ −C` the ceiling bounds the dyadic blocks, `Σ_{2^j < n ≤ 2^{j+1}} |lam(n)| ≪ 2^j (j + 1)`
(`block_bound_of_log_density_le_of_ge`), so the Dirichlet series converges absolutely on `Re s > 1`.
The lower bound excludes a negative double pole, and the even Abel pinning
(`realWeil_nonneg_of_polar`) gives even positivity at pole weight one, which is RH with `lam = Λ`.
For the cone criterion, the M. Riesz extension with the pole-free node tests as coordinate tests
produces a nonnegative even pole-free positive weight system.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral OddSector

/-! ## Dyadic blocks from the ceiling -/

theorem sum_Icc_one_div_ge_log (P : ℕ) : Real.log P ≤ ∑ m ∈ Finset.Icc 1 P, (1 : ℝ) / m := by
  have h := log_add_one_le_harmonic P
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hle : Real.log P ≤ Real.log (P + 1) := Real.log_le_log hP0 (by linarith)
  linarith

/-- **Dyadic blocks from the ceiling and a lower bound**, at a general dyadic scale `K`:
`(Σ_{K < n ≤ 2K} |lam(n)| − C K) log(2K) ≤ 2K ((log M)² + C (1 + log M)²)`, `M = (2K)²`. -/
theorem block_bound_aux {lam : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (hlb : ∀ n, 2 ≤ n → -C ≤ lam n)
    {K : ℕ} (hK : 1 ≤ K)
    (hceil : ∑ n ∈ Finset.Icc 2 (2 * K * (2 * K)), ∑ m ∈ Finset.Icc 1 (2 * K * (2 * K)),
        (if n * m ≤ 2 * K * (2 * K) then lam n / (n * m) else 0) ≤
      Real.log ((2 * K * (2 * K) : ℕ) : ℝ) ^ 2) :
    (∑ n ∈ Finset.Ioc K (2 * K), |lam n| - C * K) * Real.log ((2 * K : ℕ) : ℝ) ≤
      (2 * K : ℕ) * (Real.log ((2 * K * (2 * K) : ℕ) : ℝ) ^ 2 +
        C * (1 + Real.log ((2 * K * (2 * K) : ℕ) : ℝ)) ^ 2) := by
  set P : ℕ := 2 * K with hP
  set M : ℕ := P * P with hM
  have hP1 : 1 ≤ P := by omega
  have hPM : P ≤ M := Nat.le_mul_of_pos_right P hP1
  have hblock : ∀ n ∈ Finset.Ioc K P, 2 ≤ n ∧ n ≤ P := fun n hn => by
    have := Finset.mem_Ioc.mp hn; constructor <;> omega
  -- the split `lam = (lam + C) − C`
  set Sa := ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M,
    (if n * m ≤ M then (lam n + C) / (n * m) else 0) with hSa
  set Sc := ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M,
    (if n * m ≤ M then C / (n * m) else 0) with hSc
  have hsplit : ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M,
      (if n * m ≤ M then lam n / (n * m) else 0) = Sa - Sc := by
    rw [hSa, hSc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  -- the constant part
  have hH : ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m ≤ 1 + Real.log M := sum_Icc_inv_le_one_add_log M
  have hH2 : ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n ≤ ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by norm_num))
      fun m _ _ => by positivity
  have hS2 : 0 ≤ ∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n := Finset.sum_nonneg fun n _ => by positivity
  have hScle : Sc ≤ C * (1 + Real.log M) ^ 2 := by
    have h1 : Sc ≤ ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M, C * ((1 : ℝ) / n * (1 / m)) := by
      refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_
      split_ifs
      · rw [show C / ((n : ℝ) * m) = C * (1 / n * (1 / m)) by ring]
      · positivity
    have h2 : ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M, C * ((1 : ℝ) / n * (1 / m)) =
        C * ((∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n) * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
    have h3 : (∑ n ∈ Finset.Icc 2 M, (1 : ℝ) / n) * ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / m ≤
        (1 + Real.log M) * (1 + Real.log M) :=
      mul_le_mul (hH2.trans hH) hH (Finset.sum_nonneg fun m _ => by positivity)
        ((Finset.sum_nonneg fun m _ => by positivity).trans hH)
    rw [h2] at h1
    nlinarith
  -- the block part
  set A := ∑ n ∈ Finset.Ioc K P, (lam n + C) / n with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n hn => by
    have := hlb n (hblock n hn).1
    exact div_nonneg (by linarith) (Nat.cast_nonneg n)
  have hnn : ∀ n ∈ Finset.Icc 2 M, ∀ m ∈ Finset.Icc 1 M,
      0 ≤ (if n * m ≤ M then (lam n + C) / (n * m) else 0) := fun n hn m _ => by
    split_ifs
    · have := hlb n (Finset.mem_Icc.mp hn).1
      exact div_nonneg (by linarith) (by positivity)
    · exact le_rfl
  have hSaA : A * ∑ m ∈ Finset.Icc 1 P, (1 : ℝ) / m ≤ Sa := by
    have e1 : A * ∑ m ∈ Finset.Icc 1 P, (1 : ℝ) / m =
        ∑ n ∈ Finset.Ioc K P, ∑ m ∈ Finset.Icc 1 P,
          (if n * m ≤ M then (lam n + C) / (n * m) else 0) := by
      rw [hAdef, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hnm : n * m ≤ M := Nat.mul_le_mul (hblock n hn).2 (Finset.mem_Icc.mp hm).2
      rw [if_pos hnm]
      field_simp
    have e2 : ∑ n ∈ Finset.Ioc K P, ∑ m ∈ Finset.Icc 1 P,
          (if n * m ≤ M then (lam n + C) / (n * m) else 0) ≤
        ∑ n ∈ Finset.Ioc K P, ∑ m ∈ Finset.Icc 1 M,
          (if n * m ≤ M then (lam n + C) / (n * m) else 0) :=
      Finset.sum_le_sum fun n hn => Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right hPM) fun m hm _ => hnn n
          (Finset.mem_Icc.mpr ⟨(hblock n hn).1, (hblock n hn).2.trans hPM⟩) m hm
    have e3 : ∑ n ∈ Finset.Ioc K P, ∑ m ∈ Finset.Icc 1 M,
          (if n * m ≤ M then (lam n + C) / (n * m) else 0) ≤ Sa :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => Finset.mem_Icc.mpr
        ⟨(hblock n hn).1, (hblock n hn).2.trans hPM⟩) fun n hn _ => Finset.sum_nonneg (hnn n hn)
    rw [e1]; exact e2.trans e3
  have hHP : Real.log P ≤ ∑ m ∈ Finset.Icc 1 P, (1 : ℝ) / m := sum_Icc_one_div_ge_log P
  have hlogP0 : 0 ≤ Real.log P := Real.log_natCast_nonneg P
  -- from `A` to the block sum
  have hcard : ((Finset.Ioc K P).card : ℝ) = K := by
    have hPK : P - K = K := by omega
    rw [Nat.card_Ioc, hPK]
  have hsumA : ∑ n ∈ Finset.Ioc K P, (lam n + C) ≤ (P : ℝ) * A := by
    rw [hAdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn := hblock n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hnP : (n : ℝ) ≤ P := by exact_mod_cast hn.2
    have hlb' := hlb n hn.1
    rw [mul_div_assoc', le_div_iff₀ hn0]
    nlinarith
  have habs : ∑ n ∈ Finset.Ioc K P, |lam n| ≤ ∑ n ∈ Finset.Ioc K P, (lam n + C) + C * K := by
    have h1 : ∑ n ∈ Finset.Ioc K P, |lam n| ≤ ∑ n ∈ Finset.Ioc K P, ((lam n + C) + C) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have := hlb n (hblock n hn).1
      rcases le_total 0 (lam n) with h0 | h0
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_of_nonpos h0]; linarith
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard] at h1
    linarith
  have hfin : A * Real.log P ≤ Real.log M ^ 2 + C * (1 + Real.log M) ^ 2 := by
    have h1 : A * Real.log P ≤ A * ∑ m ∈ Finset.Icc 1 P, (1 : ℝ) / m :=
      mul_le_mul_of_nonneg_left hHP hA0
    have h2 := hceil
    rw [hsplit] at h2
    linarith
  have hPpos : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  calc (∑ n ∈ Finset.Ioc K P, |lam n| - C * K) * Real.log P
      ≤ ((P : ℝ) * A) * Real.log P :=
        mul_le_mul_of_nonneg_right (by linarith) hlogP0
    _ = (P : ℝ) * (A * Real.log P) := by ring
    _ ≤ (P : ℝ) * (Real.log M ^ 2 + C * (1 + Real.log M) ^ 2) :=
        mul_le_mul_of_nonneg_left hfin hPpos

/-- **Dyadic blocks from the ceiling and a lower bound.** -/
theorem block_bound_of_log_density_le_of_ge {lam : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) (j : ℕ)
    (hceil : ∑ n ∈ Finset.Icc 2 (2 * 2 ^ j * (2 * 2 ^ j) : ℕ),
        ∑ m ∈ Finset.Icc 1 (2 * 2 ^ j * (2 * 2 ^ j) : ℕ),
        (if n * m ≤ (2 * 2 ^ j * (2 * 2 ^ j) : ℕ) then lam n / (n * m) else 0) ≤
      Real.log ((2 * 2 ^ j * (2 * 2 ^ j) : ℕ) : ℝ) ^ 2) :
    ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n| ≤ (6 + 29 * C) * 2 ^ j * (j + 1) := by
  have h := block_bound_aux hC hlb (K := 2 ^ j) Nat.one_le_two_pow hceil
  rw [show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
  set S := ∑ n ∈ Finset.Ioc (2 ^ j) (2 * 2 ^ j), |lam n|
  set L := Real.log 2 with hLdef
  have hL2 := Real.log_two_gt_d9
  have hL2' := Real.log_two_lt_d9
  have hlogP : Real.log ((2 * 2 ^ j : ℕ) : ℝ) = (j + 1) * L := by
    push_cast
    rw [show (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) by ring, Real.log_pow]; push_cast; ring
  have hlogM : Real.log ((2 * 2 ^ j * (2 * 2 ^ j) : ℕ) : ℝ) = 2 * ((j + 1) * L) := by
    rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), hlogP]; ring
  have hP : ((2 * 2 ^ j : ℕ) : ℝ) = 2 * 2 ^ j := by push_cast; ring
  have hK : ((2 ^ j : ℕ) : ℝ) = 2 ^ j := by push_cast; ring
  rw [hlogP, hlogM, hP, hK] at h
  have hj1 : (1 : ℝ) ≤ j + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  set x := ((j : ℝ) + 1) * L with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 7 / 10 * (j + 1) := by
    have := mul_le_mul_of_nonneg_left (show L ≤ 7 / 10 by linarith) (by linarith : (0 : ℝ) ≤ j + 1)
    linarith
  have hxge : 69 / 100 * (j + 1) ≤ x := by
    have := mul_le_mul_of_nonneg_left (show 69 / 100 ≤ L by linarith)
      (by linarith : (0 : ℝ) ≤ j + 1)
    linarith
  have h3 : (1 + 2 * x) ^ 2 ≤ 9 * (j + 1) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + 2 * x)
      (show 1 + 2 * x ≤ 3 * (j + 1) by linarith) 2
    nlinarith
  have h4 : (2 * x) ^ 2 ≤ 2 * (j + 1) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 * x)
      (show 2 * x ≤ 7 / 5 * (j + 1) by linarith) 2
    nlinarith
  have h5 : (S - C * 2 ^ j) * x ≤ 2 * 2 ^ j * ((2 + 9 * C) * (j + 1) ^ 2) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h4 (mul_le_mul_of_nonneg_left h3 hC))
      (by positivity : (0 : ℝ) ≤ 2 * 2 ^ j)
    nlinarith
  have hpos : (0 : ℝ) < j + 1 := by linarith
  have h6 : (S - C * 2 ^ j) * L ≤ 2 * 2 ^ j * ((2 + 9 * C) * (j + 1)) := by
    have e : (S - C * 2 ^ j) * x = ((S - C * 2 ^ j) * L) * (j + 1) := by rw [hx]; ring
    have e' : 2 * 2 ^ j * ((2 + 9 * C) * (j + 1) ^ 2) =
        (2 * 2 ^ j * ((2 + 9 * C) * (j + 1))) * (j + 1) := by ring
    rw [e, e'] at h5
    exact le_of_mul_le_mul_right h5 hpos
  have ha : 0 ≤ (2 : ℝ) ^ j * (j + 1) := by positivity
  have hb : 0 ≤ (2 : ℝ) ^ j * C * (j + 1) := by positivity
  have hc : 0 ≤ (2 : ℝ) ^ j * C := by positivity
  have h7 : S - C * 2 ^ j ≤ 2 * 2 ^ j * ((3 + 14 * C) * (j + 1)) := by
    by_cases hS : S - C * 2 ^ j ≤ 0
    · nlinarith
    · push Not at hS
      have h8 := mul_le_mul_of_nonneg_left (show 69 / 100 ≤ L by linarith) hS.le
      nlinarith
  nlinarith

/-- **Absolute convergence on `Re s > 1` for even pole-free positive weights bounded below.** -/
theorem summable_abs_div_rpow_of_weilPositiveEvenPolar_of_ge {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {C : ℝ} (hC : 0 ≤ C) (hlb : ∀ n, 2 ≤ n → -C ≤ lam n)
    {σ : ℝ} (hσ : 1 < σ) : Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenPolar_of_ge hpf hlb
  obtain ⟨N₀, hN₀⟩ := even_log_density_le_of_polar hpf hg (ε := 1 / 2) (by norm_num)
  refine summable_div_rpow_of_block (fun n => abs_nonneg (lam n)) (B := 6 + 29 * C)
    (j₀ := N₀) hσ fun j hj => block_bound_of_log_density_le_of_ge hC hlb j ?_
  have hN : N₀ ≤ 2 * 2 ^ j * (2 * 2 ^ j) := by
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith
  have := hN₀ _ hN
  norm_num at this ⊢
  linarith

/-! ## The rigidity theorem -/

/-- **Even pole-free rigidity for weights bounded below.**  A weight system bounded below that is
Weil-positive on even tests with `f̂(i/2) = 0` is `Λ`, and RH holds. -/
theorem riemannHypothesis_of_weilPositiveEvenPolar_of_ge {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {C : ℝ} (hlb : ∀ n, 2 ≤ n → -C ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  have hC : 0 ≤ max C 0 := le_max_right _ _
  have hlb' : ∀ n, 2 ≤ n → -max C 0 ≤ lam n := fun n hn =>
    (neg_le_neg (le_max_left C 0)).trans (hlb n hn)
  obtain ⟨Cg, -, hg⟩ := exists_abs_le_of_weilPositiveEvenPolar_of_ge hpf hlb'
  have hsl := fun σ (hσ : 1 < σ) =>
    summable_abs_div_rpow_of_weilPositiveEvenPolar_of_ge hpf hC hlb' hσ
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε =>
    even_log_density_le_of_polar hpf hg hε
  have hdp := eventually_neg_le_of_ge hsl hC hlb'
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg' hgc hge =>
    realWeil_nonneg_of_polar hpf hsl hup hdp hg' hgc hge)

theorem weilPositiveEvenPolar_vonMangoldt (hRH : RiemannHypothesis) :
    WeilPositiveEvenPolar fun n => (ArithmeticFunction.vonMangoldt n : ℝ) :=
  weilPositiveEvenPolar_of_weilPositiveEvenAt (weilPositiveEvenAt_one_iff.mpr ⟨hRH, fun _ _ => rfl⟩)

/-- **RH is even pole-free positivity of a weight system bounded below.** -/
theorem riemannHypothesis_iff_exists_bddBelow_weilPositiveEvenPolar :
    RiemannHypothesis ↔ ∃ (C : ℝ) (lam : ℕ → ℝ), (∀ n, 2 ≤ n → -C ≤ lam n) ∧
      WeilPositiveEvenPolar lam := by
  constructor
  · intro hRH
    exact ⟨0, fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      fun n _ => by simp [ArithmeticFunction.vonMangoldt_nonneg],
      weilPositiveEvenPolar_vonMangoldt hRH⟩
  · rintro ⟨C, lam, hlb, hpf⟩
    exact (riemannHypothesis_of_weilPositiveEvenPolar_of_ge hpf hlb).1

/-! ## The even prime-free criterion -/

/-- The pole-free even node test as an element of the even pole-free test class. -/
def evenPolarNodeTest (j : ℕ) : WeilEvenPolarTestFn :=
  ⟨(evenPolarNode j).1, (evenPolarNode j).2, paperFT_evenPolarNode_I_div_two j⟩

/-- Archimedean nonnegativity on the even polar nonnegative cone. -/
def ArchimedeanNonnegOnEvenPolarNonnegCone : Prop :=
  ∀ c : WeilEvenPolarTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1.1 n) →
    0 ≤ c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1)

theorem linearCombination_evenPolarLogVector_apply (c : WeilEvenPolarTestFn →₀ ℝ)
    (j : LogIndex) :
    linearCombination ℝ (fun f : WeilEvenPolarTestFn => logVector f.1) c j =
      c.sum fun f t => t * logValue f.1.1 j := by
  rw [linearCombination_apply, Finsupp.sum_apply]
  simp [logVector_apply]

/-- **The even prime-free Weil criterion.**  RH holds iff the archimedean energy is nonnegative on
every nonnegative combination of autocorrelations of even pole-free tests whose values at every
`±log n`, `n ≥ 2`, are nonnegative. -/
theorem riemannHypothesis_iff_archimedeanNonnegOnEvenPolarNonnegCone :
    RiemannHypothesis ↔ ArchimedeanNonnegOnEvenPolarNonnegCone := by
  constructor
  · intro hRH c hc hnodes
    have hΛ := weilPositiveEvenPolar_vonMangoldt hRH
    have hterm : ∀ f : WeilEvenPolarTestFn,
        linearCombination ℝ (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ))
          (logVector f.1) ≤ weilArchRe (EF.weilTest f.1.1 f.1.1) := fun f => by
      have h := hΛ f.1.1 f.1.2.1 f.1.2.2 f.2.1 f.2.2
      rw [re_weilFullFunctional_eq _ f.1] at h
      linarith
    set v := linearCombination ℝ (fun f : WeilEvenPolarTestFn => logVector f.1) c with hv
    have hv0 : ∀ j : LogIndex, 0 ≤ v j := fun j => by
      rw [hv, linearCombination_evenPolarLogVector_apply]; exact hnodes j j.2
    have hΛv : 0 ≤ linearCombination ℝ
        (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) v := by
      rw [linearCombination_apply]
      exact Finset.sum_nonneg fun j _ =>
        smul_nonneg (hv0 j) ArithmeticFunction.vonMangoldt_nonneg
    have hlin : linearCombination ℝ
        (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) v =
        c.sum fun f t => t * linearCombination ℝ
          (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) (logVector f.1) := by
      rw [hv, linearCombination_apply ℝ (v := fun f : WeilEvenPolarTestFn => logVector f.1),
        map_finsuppSum]
      exact Finsupp.sum_congr fun f _ => by rw [map_smul, smul_eq_mul]
    have hsum : (c.sum fun f t => t * linearCombination ℝ
        (fun j : LogIndex => (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)) (logVector f.1)) ≤
        c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) :=
      Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hterm f) (hc f)
    linarith
  · intro h
    obtain ⟨lam, hlam0, hlamT⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
      (fun f : WeilEvenPolarTestFn => logVector f.1)
      (fun f : WeilEvenPolarTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1))
      (fun _ : LogIndex => (0 : ℝ))
      (fun j => ⟨evenPolarNodeTest j, _, div_pos (mul_pos two_pos (lt_of_lt_of_le
        (by have := integral_narrowBump_sq_pos 0; have := nodeScale_pos j; positivity)
        (le_integral_evenPolarProfile_sq j))) (Real.sqrt_pos.mpr (by
          exact_mod_cast (lt_of_lt_of_le two_pos j.2))), logVector_evenPolarNode j⟩)
      (fun c hc hcT => by
        have h1 := h c hc fun n hn => by
          rw [← linearCombination_evenPolarLogVector_apply c ⟨n, hn⟩]; exact hcT ⟨n, hn⟩
        have e0 : linearCombination ℝ (fun _ : LogIndex => (0 : ℝ))
            (linearCombination ℝ (fun f : WeilEvenPolarTestFn => logVector f.1) c) = 0 := by
          rw [linearCombination_apply]; simp
        have e1 : linearCombination ℝ
            (fun f : WeilEvenPolarTestFn => weilArchRe (EF.weilTest f.1.1 f.1.1)) c =
            c.sum fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1) := by
          rw [linearCombination_apply]; simp only [smul_eq_mul]
        rw [e0, e1]
        exact h1)
    set lam' : ℕ → ℝ := fun n => if hn : 2 ≤ n then lam ⟨n, hn⟩ else 0 with hlam'
    have e : (fun j : LogIndex => lam' (j : ℕ)) = lam := funext fun j => by simp [hlam', j.2]
    have hpf : WeilPositiveEvenPolar lam' := by
      intro f hf hfc hfe h0
      have hT := hlamT ⟨⟨f, hf, hfc⟩, hfe, h0⟩
      rw [re_weilFullFunctional_eq lam' ⟨f, hf, hfc⟩, e]
      exact sub_nonneg.mpr hT
    refine (riemannHypothesis_of_weilPositiveEvenPolar_of_ge hpf (C := 0) fun n hn => ?_).1
    simp only [hlam', dif_pos hn, neg_zero]
    exact hlam0 ⟨n, hn⟩

end RHTower.EvenSector

end
