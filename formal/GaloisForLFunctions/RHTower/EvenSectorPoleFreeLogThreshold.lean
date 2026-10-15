import GaloisForLFunctions.RHTower.EvenSectorPolarRigidity
import GaloisForLFunctions.RHTower.PolarConePartialSumRigidity

/-!
# Even pole-free positivity: the logarithmic threshold for fakes

Let `lam` be Weil-positive on all even tests with `f̂(i/2) = 0` (`WeilPositiveEvenPolar`).

**Theorem** (`riemannHypothesis_of_weilPositiveEvenPolar_of_log_floor`).  If for every `ε > 0` there
is `C` with `lam(n) ≥ −(ε log n + C)` for all `n ≥ 2`, then RH holds and `lam = Λ` on `n ≥ 2`.

**Corollary** (`exists_lt_neg_log_of_weilPositiveEvenPolar`).  An even pole-free positive weight
system other than `Λ` dips below `−ε log n − C` for some `ε > 0` and every `C`.

So any even pole-free fake is at least as negative as a negative double pole (`lam ≈ −c log n`)
along a sequence.  This sharpens the "bounded below" hypothesis of
`riemannHypothesis_of_weilPositiveEvenPolar_of_ge` to the exact scale of a double pole.

Proof.  A floor `−(ε log n + C)` is bounded on each range `n ≤ M`, so the dyadic block bound of the
log-density ceiling (`block_bound_of_log_density_le_of_ge`, applied to the weights truncated below
by that floor beyond `M`) gives `Σ_{2^j < n ≤ 2^{j+1}} |lam(n)| ≪ 2^j (j + 1)²`.  The extra factor
`j + 1` is absorbed by `n^{−δ}`, so the Dirichlet series converges absolutely on `Re s > 1`.
Summing the floor gives partial sums `≥ −ε N log N` eventually, which excludes a negative double
pole (`eventually_neg_le_of_primeWeightPartialSum`).  The even Abel pinning concludes.
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral OddSector

/-- `j + 1 ≤ K 2^{jδ}` with `K = 1 + 1/(δ log 2)`. -/
theorem one_add_le_mul_two_rpow {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    (j : ℝ) + 1 ≤ (1 + 1 / (δ * Real.log 2)) * (2 : ℝ) ^ ((j : ℝ) * δ) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hpos : 0 < δ * Real.log 2 := mul_pos hδ hl
  have hexp : 1 + (j : ℝ) * δ * Real.log 2 ≤ (2 : ℝ) ^ ((j : ℝ) * δ) := by
    rw [Real.rpow_def_of_pos two_pos]
    have := Real.add_one_le_exp (Real.log 2 * ((j : ℝ) * δ))
    nlinarith
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (j : ℝ) + 1 ≤ (1 + 1 / (δ * Real.log 2)) * (1 + (j : ℝ) * δ * Real.log 2) := by
    have e : (1 + 1 / (δ * Real.log 2)) * (1 + (j : ℝ) * δ * Real.log 2) =
        1 + (j : ℝ) * δ * Real.log 2 + 1 / (δ * Real.log 2) + j := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (j : ℝ) * δ * Real.log 2 := by positivity
    have : 0 ≤ 1 / (δ * Real.log 2) := by positivity
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- **Dyadic blocks under a slowly growing floor.** -/
theorem block_bound_of_log_density_le_of_log_floor {lam : ℕ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε)
    (hC : 0 ≤ C) (hlb : ∀ n : ℕ, 2 ≤ n → -(ε * Real.log n + C) ≤ lam n) (j : ℕ)
    (hceil : ∑ n ∈ Finset.Icc 2 (2 * 2 ^ j * (2 * 2 ^ j) : ℕ),
        ∑ m ∈ Finset.Icc 1 (2 * 2 ^ j * (2 * 2 ^ j) : ℕ),
        (if n * m ≤ (2 * 2 ^ j * (2 * 2 ^ j) : ℕ) then lam n / (n * m) else 0) ≤
      Real.log ((2 * 2 ^ j * (2 * 2 ^ j) : ℕ) : ℝ) ^ 2) :
    ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n| ≤
      (6 + 29 * (ε * Real.log ((2 * 2 ^ j * (2 * 2 ^ j) : ℕ) : ℝ) + C)) * 2 ^ j * (j + 1) := by
  set M : ℕ := 2 * 2 ^ j * (2 * 2 ^ j) with hM
  set D : ℝ := ε * Real.log (M : ℝ) + C with hD
  have hlogM : 0 ≤ Real.log (M : ℝ) := Real.log_natCast_nonneg M
  have hD0 : 0 ≤ D := by positivity
  set lam' : ℕ → ℝ := fun n => if n ≤ M then lam n else max (lam n) (-D) with hlam'
  have hlb' : ∀ n, 2 ≤ n → -D ≤ lam' n := fun n hn => by
    simp only [hlam']
    split_ifs with h
    · have h1 := hlb n hn
      have h2 : Real.log n ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast h)
      have := mul_le_mul_of_nonneg_left h2 hε
      linarith
    · exact le_max_right _ _
  have hceil' : ∑ n ∈ Finset.Icc 2 M, ∑ m ∈ Finset.Icc 1 M,
      (if n * m ≤ M then lam' n / (n * m) else 0) ≤ Real.log (M : ℝ) ^ 2 := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m _ => ?_)
      hceil
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    simp only [hlam', if_pos hnM]
  have h := block_bound_of_log_density_le_of_ge hD0 hlb' j hceil'
  refine le_of_eq_of_le (Finset.sum_congr rfl fun n hn => ?_) h
  have hn := Finset.mem_Ioc.mp hn
  have hnM : n ≤ M := by
    have : 2 ^ (j + 1) ≤ M := by
      rw [hM, show 2 ^ (j + 1) = 2 * 2 ^ j by ring]
      exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  simp only [hlam', if_pos hnM]

/-- **Absolute convergence on `Re s > 1` under a logarithmic floor.** -/
theorem summable_abs_div_rpow_of_weilPositiveEvenPolar_of_log_floor {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hlb : ∀ n : ℕ, 2 ≤ n → -(ε * Real.log n + C) ≤ lam n) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
  -- growth
  obtain ⟨Cu, hCu0, hCu⟩ := exists_le_of_weilPositiveEvenPolar hpf
  have hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ (Cu + ε + C) * Real.sqrt n * (1 + Real.log n) := by
    intro n hn
    have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h1 := hCu n hn
    have h2 := hlb n hn
    have hS : 1 + Real.log n ≤ Real.sqrt n * (1 + Real.log n) := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨N₀, hN₀⟩ := even_log_density_le_of_polar hpf hg (ε := 1 / 2) (by norm_num)
  set δ := (σ - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set K := 1 + 1 / (δ * Real.log 2) with hK
  have hK0 : 0 ≤ K := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  set B := (6 + 29 * (ε * 2 * Real.log 2 + C + ε * 2 * Real.log 2)) * K with hB
  have hmain := summable_div_rpow_of_block (f := fun n => |lam n| / (n : ℝ) ^ δ)
    (fun n => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) δ)) (B := B)
    (j₀ := N₀) (σ := σ - δ) (by rw [hδ]; linarith) fun j hj => ?_
  · refine hmain.congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero, Real.zero_rpow (by linarith : σ ≠ 0),
        Real.zero_rpow (by rw [hδ]; linarith : σ - δ ≠ 0), div_zero]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_div, ← Real.rpow_add hn0]; ring_nf
  · have hN : N₀ ≤ 2 * 2 ^ j * (2 * 2 ^ j) := by
      have h1 : j < 2 ^ j := Nat.lt_two_pow_self
      have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
      nlinarith
    have hceil := hN₀ _ hN
    norm_num at hceil
    have hblk := block_bound_of_log_density_le_of_log_floor hε hC hlb j
      (by norm_num; linarith)
    have hlogM : Real.log ((2 * 2 ^ j * (2 * 2 ^ j) : ℕ) : ℝ) = 2 * ((j + 1) * Real.log 2) := by
      push_cast
      rw [show (2 : ℝ) * 2 ^ j * (2 * 2 ^ j) = (2 ^ (j + 1)) ^ 2 by ring, Real.log_pow,
        Real.log_pow]; push_cast; ring
    rw [hlogM] at hblk
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    have hj1 : (1 : ℝ) ≤ j + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
    -- each term is at most `|lam n| 2^{−jδ}`
    have hterm : ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n| / (n : ℝ) ^ δ ≤
        (∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n|) / (2 : ℝ) ^ ((j : ℝ) * δ) := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' := (Finset.mem_Ioc.mp hn).1
      have hjn : (2 : ℝ) ^ ((j : ℝ) * δ) ≤ (n : ℝ) ^ δ := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn'.le) hδ0.le
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hjn
    have hpow : 0 < (2 : ℝ) ^ ((j : ℝ) * δ) := by positivity
    have hjK := one_add_le_mul_two_rpow hδ0 j
    refine hterm.trans ?_
    rw [div_le_iff₀ hpow]
    have hfac : 6 + 29 * (ε * (2 * ((j + 1) * Real.log 2)) + C) ≤
        (6 + 29 * (ε * 2 * Real.log 2 + C + ε * 2 * Real.log 2)) * (j + 1) := by
      have hl2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have a := mul_nonneg (mul_nonneg hε hl2.le) hj0
      have b := mul_nonneg hC hj0
      have c := mul_nonneg hε hl2.le
      nlinarith
    have hX : 0 ≤ 6 + 29 * (ε * 2 * Real.log 2 + C + ε * 2 * Real.log 2) := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
    calc ∑ n ∈ Finset.Ioc (2 ^ j) (2 ^ (j + 1)), |lam n|
        ≤ (6 + 29 * (ε * (2 * ((j + 1) * Real.log 2)) + C)) * 2 ^ j * (j + 1) := hblk
      _ ≤ (6 + 29 * (ε * 2 * Real.log 2 + C + ε * 2 * Real.log 2)) * (j + 1) * 2 ^ j *
          (j + 1) := by gcongr
      _ ≤ (6 + 29 * (ε * 2 * Real.log 2 + C + ε * 2 * Real.log 2)) *
          (K * (2 : ℝ) ^ ((j : ℝ) * δ)) * 2 ^ j * (j + 1) := by gcongr
      _ = B * 2 ^ j * (j + 1) * (2 : ℝ) ^ ((j : ℝ) * δ) := by rw [hB]; ring

/-- **The logarithmic threshold.**  Even pole-free positivity with `lam(n) ≥ −(ε log n + C_ε)` for
every `ε > 0` forces RH and `lam = Λ`. -/
theorem riemannHypothesis_of_weilPositiveEvenPolar_of_log_floor {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam)
    (hlb : ∀ ε > 0, ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → -(ε * Real.log n + C) ≤ lam n) :
    RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  obtain ⟨C₁, hC₁⟩ := hlb 1 one_pos
  have hlb₁ : ∀ n : ℕ, 2 ≤ n → -(1 * Real.log n + max C₁ 0) ≤ lam n := fun n hn =>
    (neg_le_neg (by linarith [le_max_left C₁ 0])).trans (hC₁ n hn)
  have hsl := fun σ (hσ : 1 < σ) => summable_abs_div_rpow_of_weilPositiveEvenPolar_of_log_floor
    hpf zero_le_one (le_max_right _ _) hlb₁ hσ
  obtain ⟨Cu, hCu0, hCu⟩ := exists_le_of_weilPositiveEvenPolar hpf
  have hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ (Cu + 1 + max C₁ 0) * Real.sqrt n * (1 + Real.log n) := by
    intro n hn
    have hn1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; linarith
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have h1 := hCu n hn
    have h2 := hlb₁ n hn
    have hm : 0 ≤ max C₁ 0 := le_max_right _ _
    have hS : 1 + Real.log n ≤ Real.sqrt n * (1 + Real.log n) := by nlinarith
    have hS0 : 0 ≤ Real.sqrt n * (1 + Real.log n) := by positivity
    have hA := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 1 + max C₁ 0)
    have hB := mul_nonneg hCu0 hS0
    rw [abs_le]; constructor <;> nlinarith
  have hup := eventually_le_one_add_of_log_density_le hsl fun _ hε =>
    even_log_density_le_of_polar hpf hg hε
  -- partial sums above `−ε N log N`
  have hS : ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      -(ε * (N * Real.log N)) ≤ WeilSpectral.primeWeightPartialSum lam N := by
    intro ε hε
    obtain ⟨C, hC⟩ := hlb (ε / 4) (by positivity)
    have hev : ∀ᶠ N : ℕ in atTop, |C| ≤ ε / 4 * Real.log N := by
      have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact (ht.eventually_ge_atTop (|C| / (ε / 4))).mono fun N hN => by
        simp only [Function.comp_apply] at hN
        rwa [div_le_iff₀ (by positivity), mul_comm] at hN
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    unfold WeilSpectral.primeWeightPartialSum
    have hlogN : ∀ m ∈ Finset.range (N + 1), Real.log m ≤ Real.log N := fun m hm => by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg N
      · exact Real.log_le_log (by exact_mod_cast hm0)
          (by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hterm : ∀ m ∈ Finset.range (N + 1),
        -(ε / 2 * Real.log N) ≤ (if 2 ≤ m then lam m else 0) := fun m hm => by
      split_ifs with h
      · have h1 := hC m h
        have h2 := mul_le_mul_of_nonneg_left (hlogN m hm) (by positivity : (0 : ℝ) ≤ ε / 4)
        have h3 := le_abs_self C
        linarith
      · have : 0 ≤ ε / 2 * Real.log N := by positivity
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    push_cast at hsum
    have key : ((N : ℝ) + 1) * (ε / 2 * Real.log N) ≤ ε * (N * Real.log N) := by
      have : 0 ≤ ε * Real.log N := by positivity
      nlinarith
    linarith
  have hdp := eventually_neg_le_of_primeWeightPartialSum hsl hS
  exact weilPositiveEvenAt_one_iff.mp (weilPositiveEvenAt_one_of_real fun _ hg' hgc hge =>
    realWeil_nonneg_of_polar hpf hsl hup hdp hg' hgc hge)

/-- **Even pole-free fakes dip to the double-pole scale.** -/
theorem exists_lt_neg_log_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpf : WeilPositiveEvenPolar lam) {n₀ : ℕ} (hn₀ : 2 ≤ n₀)
    (hne : lam n₀ ≠ ArithmeticFunction.vonMangoldt n₀) :
    ∃ ε > 0, ∀ C : ℝ, ∃ n : ℕ, 2 ≤ n ∧ lam n < -(ε * Real.log n + C) := by
  by_contra h
  push Not at h
  exact hne ((riemannHypothesis_of_weilPositiveEvenPolar_of_log_floor hpf h).2 n₀ hn₀)

end RHTower.EvenSector

end
