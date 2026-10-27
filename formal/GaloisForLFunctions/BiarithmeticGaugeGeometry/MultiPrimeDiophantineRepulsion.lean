import GaloisForLFunctions.BiarithmeticGaugeGeometry.QuantitativeCatalanDiophantineRepulsion
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.NumberTheory.PrimeCounting

/-!
# Multi-Prime Diophantine Repulsion of the Liouville Vacuum

A vertical shift `ζ(s + iγ)` imitates the Liouville twin `ζ(2s)/ζ(s)` on a set of primes when every
phase `γ log p` is close to `π` modulo `2π`. For the pair `{2, 3}` the parity gap `2^a ≠ 3^b` gives
`(1 + cos(γ log 2)) + (1 + cos(γ log 3)) ≥ e^{−|γ|}/50` (`liouville_kronecker_repulsion_ge`). This
module uses `N` distinct primes at once, replacing the parity gap by Siegel's lemma and unique
factorization.

**Multi-prime repulsion (`multiPrime_repulsion`).** For distinct primes `p_1, …, p_N`, `N ≥ 2`, and
every `γ ∈ ℝ`,

`Σ_j (1 + cos(γ log p_j)) ≥ γ² e^{−2τL} / (32 N τ²)`,  `L = Σ_j log p_j`,
`τ = (N(|γ|L/π + 1))^{1/(N−1)}`.

Write `γ log p_j = u_j π + δ_j` with `u_j` odd and `|u_j| ≤ |γ|L/π + 1`. Siegel's lemma gives a
nonzero integer vector `t` with `Σ t_j u_j = 0` and `max |t_j| ≤ τ`, so `γ Σ t_j log p_j = Σ t_j δ_j`.
Unique factorization separates `Π p_j^{t_j⁺}` from `Π p_j^{t_j⁻}`, whence
`|Σ t_j log p_j| ≥ e^{−τL}/2` (`abs_sum_mul_log_prime_ge`). Therefore `Σ|δ_j| ≥ |γ| e^{−τL}/(2τ)`,
and `1 + cos(γ log p_j) ≥ δ_j²/8`.

The repulsion exponent drops from `|γ|` to `|γ|^{1/(N−1)}`: an archimedean twist approaches the
Liouville vacuum on `N` primes at most stretched-exponentially fast in the height.

**Every stretched exponent (`exists_primes_repulsion_ge_exp_neg_rpow`).** For every `ε > 0` the
first `N = ⌈1/ε⌉ + 2` primes satisfy `Σ_j (1 + cos(γ log p_j)) ≥ exp(−|γ|^ε)` for all large `|γ|`.
-/

open Real Finset

noncomputable section
set_option autoImplicit false

attribute [local instance] Matrix.seminormedAddCommGroup

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

/-- **Unique factorization separates the two halves of an exponent vector.** For distinct primes
and a nonzero integer vector `t`, `Π p_j^{t_j⁺} ≠ Π p_j^{t_j⁻}`. -/
theorem prod_pow_toNat_ne {N : ℕ} {p : Fin N → ℕ} (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) {t : Fin N → ℤ} (ht : t ≠ 0) :
    ∏ j, p j ^ (t j).toNat ≠ ∏ j, p j ^ (-t j).toNat := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, t j ≠ 0 := by
    by_contra h
    push Not at h
    exact ht (funext h)
  -- `p j₀` divides the side carrying its exponent and not the other
  have hnot : ∀ {s : Fin N → ℤ}, 0 < s j₀ → ¬ p j₀ ∣ ∏ j, p j ^ (-s j).toNat := by
    intro s hs hdvd
    obtain ⟨j, -, hj⟩ := (Prime.dvd_finsetProd_iff (hp j₀).prime _).mp hdvd
    have hpos : (-s j).toNat ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hj
      exact (hp j₀).one_lt.ne' (Nat.dvd_one.mp hj)
    have heq : p j₀ = p j :=
      (Nat.prime_dvd_prime_iff_eq (hp j₀) (hp j)).mp ((hp j₀).dvd_of_dvd_pow hj)
    have hjj := hinj heq
    subst hjj
    omega
  have hdvd : ∀ {s : Fin N → ℤ}, 0 < s j₀ → p j₀ ∣ ∏ j, p j ^ (s j).toNat := fun {s} hs =>
    (dvd_pow_self (p j₀) (by omega)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j₀))
  rcases lt_or_gt_of_ne hj₀ with hneg | hpos
  · intro h
    have h1 := hdvd (s := -t) (by simpa using hneg)
    have h2 := hnot (s := -t) (by simpa using hneg)
    simp only [Pi.neg_apply, neg_neg] at h1 h2
    exact h2 (h ▸ h1)
  · intro h
    exact hnot hpos (h ▸ hdvd hpos)

/-- **Liouville bound for prime logarithms.** For distinct primes and a nonzero integer vector `t`
with `|t_j| ≤ T`, `|Σ t_j log p_j| ≥ e^{−T Σ log p_j}/2`. -/
theorem abs_sum_mul_log_prime_ge {N : ℕ} {p : Fin N → ℕ} (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) {t : Fin N → ℤ} (ht : t ≠ 0) {T : ℝ}
    (hT : ∀ j, |(t j : ℝ)| ≤ T) :
    Real.exp (-(T * ∑ j, Real.log (p j))) / 2 ≤ |∑ j, (t j : ℝ) * Real.log (p j)| := by
  set A : ℕ := ∏ j, p j ^ (t j).toNat with hAdef
  set B : ℕ := ∏ j, p j ^ (-t j).toNat with hBdef
  have hp0 : ∀ j, (0 : ℝ) < p j := fun j => by exact_mod_cast (hp j).pos
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hp j).ne_zero)
  have hB : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hp j).ne_zero)
  have hlogprod : ∀ e : Fin N → ℕ, Real.log (∏ j, p j ^ e j : ℕ) =
      ∑ j, (e j : ℝ) * Real.log (p j) := fun e => by
    rw [Nat.cast_prod, Real.log_prod (fun j _ => by exact_mod_cast pow_ne_zero _ (hp j).ne_zero)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hlog : ∑ j, (t j : ℝ) * Real.log (p j) = Real.log A - Real.log B := by
    rw [hAdef, hBdef, hlogprod, hlogprod, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_mul]
    congr 1
    have h := Int.toNat_sub_toNat_neg (t j)
    have h' : ((t j : ℤ) : ℝ) = (((t j).toNat : ℤ) : ℝ) - (((-t j).toNat : ℤ) : ℝ) := by
      rw [← Int.cast_sub, h]
    rw [h', Int.cast_natCast, Int.cast_natCast]
  -- each half is at most `e^{T L}`
  have hle : ∀ e : Fin N → ℕ, (∀ j, (e j : ℝ) ≤ T) →
      ((∏ j, p j ^ e j : ℕ) : ℝ) ≤ Real.exp (T * ∑ j, Real.log (p j)) := by
    intro e he
    have hpos : (0 : ℝ) < ((∏ j, p j ^ e j : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hp j).ne_zero)
    calc ((∏ j, p j ^ e j : ℕ) : ℝ) = Real.exp (Real.log ((∏ j, p j ^ e j : ℕ) : ℝ)) :=
          (Real.exp_log hpos).symm
      _ = Real.exp (∑ j, (e j : ℝ) * Real.log (p j)) := by rw [hlogprod]
      _ ≤ Real.exp (T * ∑ j, Real.log (p j)) := by
          rw [Finset.mul_sum]
          exact Real.exp_le_exp.mpr (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
            (he j) (Real.log_nonneg (by exact_mod_cast (hp j).one_lt.le)))
  have htoNat : ∀ j, (((t j).toNat : ℕ) : ℝ) ≤ T ∧ (((-t j).toNat : ℕ) : ℝ) ≤ T := by
    intro j
    have h1 : ((t j).toNat : ℤ) ≤ |t j| := by
      rw [Int.toNat_eq_max]; exact max_le (le_abs_self _) (abs_nonneg _)
    have h2 : ((-t j).toNat : ℤ) ≤ |t j| := by
      rw [Int.toNat_eq_max, ← abs_neg]; exact max_le (le_abs_self _) (abs_nonneg _)
    have hTj := hT j
    rw [← Int.cast_abs] at hTj
    constructor
    · exact le_trans (by exact_mod_cast h1) hTj
    · exact le_trans (by exact_mod_cast h2) hTj
  have hgap := abs_log_nat_sub_ge hA hB (prod_pow_toNat_ne hp hinj ht)
  have hAB : (A : ℝ) + B ≤ 2 * Real.exp (T * ∑ j, Real.log (p j)) := by
    have h1 := hle (fun j => (t j).toNat) fun j => (htoNat j).1
    have h2 := hle (fun j => (-t j).toNat) fun j => (htoNat j).2
    linarith
  rw [hlog]
  refine le_trans ?_ hgap
  have hABpos : (0 : ℝ) < (A : ℝ) + B := by positivity
  calc Real.exp (-(T * ∑ j, Real.log (p j))) / 2 =
        1 / (2 * Real.exp (T * ∑ j, Real.log (p j))) := by rw [Real.exp_neg]; field_simp
    _ ≤ 1 / ((A : ℝ) + B) := one_div_le_one_div_of_le hABpos hAB

/-- The Siegel height `τ = (N(|γ|L/π + 1))^{1/(N−1)}` of the repulsion bound. -/
def repulsionScale (N : ℕ) (L γ : ℝ) : ℝ :=
  ((N : ℝ) * (|γ| * L / Real.pi + 1)) ^ ((1 : ℝ) / ((N : ℝ) - 1))

/-- **Multi-prime repulsion of the Liouville vacuum.** For `N ≥ 2` distinct primes and every
`γ ∈ ℝ`, `Σ_j (1 + cos(γ log p_j)) ≥ γ² e^{−2τL}/(32 N τ²)` with `L = Σ_j log p_j` and
`τ = (N(|γ|L/π + 1))^{1/(N−1)}`. -/
theorem multiPrime_repulsion {N : ℕ} (hN : 2 ≤ N) {p : Fin N → ℕ} (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (γ : ℝ) :
    γ ^ 2 * Real.exp (-(2 * repulsionScale N (∑ j, Real.log (p j)) γ *
        ∑ j, Real.log (p j))) /
      (32 * N * repulsionScale N (∑ j, Real.log (p j)) γ ^ 2) ≤
      ∑ j, (1 + Real.cos (γ * Real.log (p j))) := by
  set L : ℝ := ∑ j, Real.log (p j) with hLdef
  set τ : ℝ := repulsionScale N L γ with hτdef
  have hlogp : ∀ j, 0 ≤ Real.log (p j) := fun j =>
    Real.log_nonneg (by exact_mod_cast (hp j).one_lt.le)
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => hlogp j
  have hlogL : ∀ j, Real.log (p j) ≤ L := fun j =>
    Finset.single_le_sum (fun i _ => hlogp i) (Finset.mem_univ j)
  -- odd phase centres `u_j`: `γ log p_j = u_j π + δ_j`
  choose u hu_odd hu_bd hcos using fun j => exists_odd_int_one_add_cos_ge (γ * Real.log (p j))
  set δ : Fin N → ℝ := fun j => γ * Real.log (p j) - (u j : ℝ) * Real.pi with hδdef
  set U : ℝ := |γ| * L / Real.pi + 1 with hUdef
  have hU0 : 0 ≤ U := by positivity
  have hu_U : ∀ j, |(u j : ℝ)| ≤ U := by
    intro j
    have h := hu_bd j
    rw [abs_mul, abs_of_nonneg (hlogp j)] at h
    have h' : |γ| * Real.log (p j) / Real.pi ≤ |γ| * L / Real.pi :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hlogL j) (abs_nonneg γ))
        Real.pi_pos.le
    have habs : ((u j).natAbs : ℝ) = |(u j : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    linarith
  -- Siegel's lemma for the single equation `Σ t_j u_j = 0`
  set A : Matrix (Fin 1) (Fin N) ℤ := fun _ j => u j with hAdef
  have hN1 : 0 < N := by omega
  have hA0 : A ≠ 0 := by
    intro h
    have h0 := congrFun (congrFun h 0) ⟨0, hN1⟩
    simp only [hAdef, Matrix.zero_apply] at h0
    obtain ⟨k, hk⟩ := hu_odd ⟨0, hN1⟩
    omega
  obtain ⟨t, ht0, hAt, htnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le' A
    (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega) hA0
  simp only [Fintype.card_fin, Nat.cast_one] at htnorm
  have hAnorm : ‖A‖ ≤ U := by
    refine (Matrix.norm_le_iff hU0).mpr fun _ j => ?_
    rw [Int.norm_eq_abs]
    exact hu_U j
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hexp0 : 0 ≤ (1 : ℝ) / ((N : ℝ) - 1) := by
    have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
    exact div_nonneg zero_le_one (by linarith)
  have htτ : ‖t‖ ≤ τ := htnorm.trans (Real.rpow_le_rpow (by positivity)
    (mul_le_mul_of_nonneg_left hAnorm hNpos.le) hexp0)
  have ht_le : ∀ j, |(t j : ℝ)| ≤ τ := fun j => by
    have h := norm_le_pi_norm t j
    rw [Int.norm_eq_abs] at h
    exact h.trans htτ
  have hτpos : 0 < τ := by
    obtain ⟨j₀, hj₀⟩ : ∃ j, t j ≠ 0 := by
      by_contra h
      push Not at h
      exact ht0 (funext h)
    have h1 : (1 : ℝ) ≤ |(t j₀ : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj₀
    linarith [ht_le j₀]
  -- elimination: `γ Σ t_j log p_j = Σ t_j δ_j`
  have hsum0 : ∑ j, (t j : ℝ) * (u j : ℝ) = 0 := by
    have h := congrFun hAt 0
    simp only [Matrix.mulVec, dotProduct, hAdef, Pi.zero_apply] at h
    have h' : ((∑ j, u j * t j : ℤ) : ℝ) = 0 := by exact_mod_cast h
    push_cast at h'
    rw [← h']
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have helim : γ * ∑ j, (t j : ℝ) * Real.log (p j) = ∑ j, (t j : ℝ) * δ j := by
    have h : ∑ j, (t j : ℝ) * δ j =
        γ * ∑ j, (t j : ℝ) * Real.log (p j) - Real.pi * ∑ j, (t j : ℝ) * (u j : ℝ) := by
      simp only [hδdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h, hsum0, mul_zero, sub_zero]
  have hgap := abs_sum_mul_log_prime_ge hp hinj ht0 ht_le
  -- `|γ| e^{−τL}/2 ≤ τ Σ |δ_j|`
  have hδsum : |γ| * (Real.exp (-(τ * L)) / 2) ≤ τ * ∑ j, |δ j| := by
    calc |γ| * (Real.exp (-(τ * L)) / 2)
        ≤ |γ| * |∑ j, (t j : ℝ) * Real.log (p j)| :=
          mul_le_mul_of_nonneg_left hgap (abs_nonneg γ)
      _ = |∑ j, (t j : ℝ) * δ j| := by rw [← abs_mul, helim]
      _ ≤ ∑ j, |(t j : ℝ) * δ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, τ * |δ j| := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right (ht_le j) (abs_nonneg _)
      _ = τ * ∑ j, |δ j| := (Finset.mul_sum _ _ _).symm
  -- Cauchy–Schwarz and `1 + cos ≥ δ²/8`
  have hcs : (∑ j, |δ j|) ^ 2 ≤ N * ∑ j, δ j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N))) (f := fun j => |δ j|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    exact h
  have hcos_sum : ∑ j, δ j ^ 2 / 8 ≤ ∑ j, (1 + Real.cos (γ * Real.log (p j))) :=
    Finset.sum_le_sum fun j _ => hcos j
  have hlow : γ ^ 2 * Real.exp (-(2 * τ * L)) / (32 * N * τ ^ 2) ≤ ∑ j, δ j ^ 2 / 8 := by
    rw [← Finset.sum_div]
    have hS : 0 ≤ ∑ j, |δ j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have h1 : (|γ| * (Real.exp (-(τ * L)) / 2)) ^ 2 ≤ (τ * ∑ j, |δ j|) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hδsum 2
    have hexp2 : Real.exp (-(2 * τ * L)) = Real.exp (-(τ * L)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hexp2, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h2 : γ ^ 2 * Real.exp (-(τ * L)) ^ 2 = 4 * (|γ| * (Real.exp (-(τ * L)) / 2)) ^ 2 := by
      rw [mul_pow, div_pow, sq_abs]; ring
    rw [h2]
    have h3 : (τ * ∑ j, |δ j|) ^ 2 ≤ τ ^ 2 * (N * ∑ j, δ j ^ 2) := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hcs (by positivity)
    nlinarith [h1, h3]
  exact hlow.trans hcos_sum

/-- **Repulsion beats every stretched exponential.** For every `ε > 0` there are finitely many
primes (the first `N`) such that `Σ_j (1 + cos(γ log p_j)) ≥ exp(−|γ|^ε)` for all large `|γ|`. -/
theorem exists_primes_repulsion_ge_exp_neg_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ₀ : ℝ, ∀ γ : ℝ, γ₀ ≤ |γ| →
      Real.exp (-|γ| ^ ε) ≤
        ∑ j : Fin N, (1 + Real.cos (γ * Real.log (Nat.nth Nat.Prime j))) := by
  set N : ℕ := ⌈1 / ε⌉₊ + 2 with hNdef
  have hN : 2 ≤ N := by omega
  set p : Fin N → ℕ := fun j => Nat.nth Nat.Prime j with hpdef
  have hp : ∀ j, (p j).Prime := fun j => Nat.prime_nth_prime j
  have hinj : Function.Injective p := fun i j h =>
    Fin.ext (Nat.nth_injective Nat.infinite_setOf_prime h)
  set L : ℝ := ∑ j, Real.log (p j) with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ =>
    Real.log_nonneg (by exact_mod_cast (hp j).one_lt.le)
  set a : ℝ := (1 : ℝ) / ((N : ℝ) - 1) with hadef
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have ha0 : 0 < a := div_pos one_pos (by linarith)
  have haε : a < ε := by
    have hceil : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hNe : (N : ℝ) - 1 = (⌈1 / ε⌉₊ : ℝ) + 1 := by rw [hNdef]; push_cast; ring
    rw [hadef, hNe, div_lt_iff₀ (by positivity)]
    have : 1 / ε * ε = 1 := by field_simp
    nlinarith
  have ha1 : a ≤ 1 := by
    rw [hadef, div_le_one (by linarith)]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set K : ℝ := ((N : ℝ) * (L / Real.pi + 1)) ^ a with hKdef
  have hKpos : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  set C : ℝ := Real.log (32 * N * K ^ 2) with hCdef
  set M : ℝ := 2 * K * L + |C| + 1 with hMdef
  have hKL : 0 ≤ 2 * K * L := by positivity
  have hM1 : 1 ≤ M := by have := abs_nonneg C; linarith
  set b : ℝ := ε - a with hbdef
  have hb : 0 < b := by linarith
  refine ⟨N, max 1 (M ^ (1 / b)), fun γ hγ => ?_⟩
  have hγ1 : 1 ≤ |γ| := le_trans (le_max_left _ _) hγ
  have hγpos : 0 < |γ| := by linarith
  have hγM : M ^ (1 / b) ≤ |γ| := le_trans (le_max_right _ _) hγ
  -- `|γ|^b ≥ M`
  have hgb : M ≤ |γ| ^ b := by
    have h := Real.rpow_le_rpow (by positivity) hγM hb.le
    rwa [← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hb.ne', Real.rpow_one] at h
  have hga : 1 ≤ |γ| ^ a := Real.one_le_rpow hγ1 ha0.le
  have hgaγ : |γ| ^ a ≤ |γ| := by
    simpa using Real.rpow_le_rpow_of_exponent_le hγ1 ha1
  -- the Siegel height grows like `|γ|^a`
  set τ : ℝ := repulsionScale N L γ with hτdef
  have hτpos : 0 < τ := Real.rpow_pos_of_pos (by positivity) _
  have hτ : τ ≤ K * |γ| ^ a := by
    rw [hτdef, repulsionScale, hKdef, ← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ ha0.le
    have hin : |γ| * L / Real.pi + 1 ≤ (L / Real.pi + 1) * |γ| := by
      have h1 : |γ| * L / Real.pi = L / Real.pi * |γ| := by ring
      have h2 : 0 ≤ L / Real.pi := div_nonneg hL0 Real.pi_pos.le
      rw [h1]
      nlinarith
    calc (N : ℝ) * (|γ| * L / Real.pi + 1) ≤ N * ((L / Real.pi + 1) * |γ|) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = N * (L / Real.pi + 1) * |γ| := by ring
  have hτ2 : τ ^ 2 ≤ K ^ 2 * γ ^ 2 := by
    have h1 : τ ≤ K * |γ| := hτ.trans (mul_le_mul_of_nonneg_left hgaγ hKpos.le)
    have h2 := pow_le_pow_left₀ hτpos.le h1 2
    rwa [mul_pow, sq_abs] at h2
  have hexp : Real.exp (-(2 * K * |γ| ^ a * L)) ≤ Real.exp (-(2 * τ * L)) := by
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_right hτ hL0
    nlinarith
  have hmain := multiPrime_repulsion hN hp hinj γ
  have hpos32 : (0 : ℝ) < 32 * N * K ^ 2 := by positivity
  -- `exp(−|γ|^ε) ≤ exp(−2K L |γ|^a)/(32 N K²)`
  have hstep1 : Real.exp (-|γ| ^ ε) ≤ Real.exp (-(2 * K * |γ| ^ a * L)) / (32 * N * K ^ 2) := by
    have hε' : |γ| ^ ε = |γ| ^ a * |γ| ^ b := by
      rw [← Real.rpow_add hγpos, hbdef]; ring_nf
    have hlin : 2 * K * |γ| ^ a * L + C ≤ |γ| ^ ε := by
      rw [hε']
      have hC := le_abs_self C
      have h1 := mul_le_mul_of_nonneg_left hgb (by linarith : (0 : ℝ) ≤ |γ| ^ a)
      have h2 : |C| + 1 ≤ |γ| ^ a * (|C| + 1) := le_mul_of_one_le_left (by positivity) hga
      rw [hMdef] at h1
      nlinarith [h1, h2, hC]
    rw [show Real.exp (-(2 * K * |γ| ^ a * L)) / (32 * N * K ^ 2) =
        Real.exp (-(2 * K * |γ| ^ a * L + C)) by
      rw [neg_add, Real.exp_add, Real.exp_neg C, hCdef, Real.exp_log hpos32, div_eq_mul_inv]]
    exact Real.exp_le_exp.mpr (by linarith)
  have hstep2 : Real.exp (-(2 * K * |γ| ^ a * L)) / (32 * N * K ^ 2) ≤
      γ ^ 2 * Real.exp (-(2 * τ * L)) / (32 * N * τ ^ 2) := by
    rw [div_le_div_iff₀ hpos32 (by positivity)]
    calc Real.exp (-(2 * K * |γ| ^ a * L)) * (32 * N * τ ^ 2)
        ≤ Real.exp (-(2 * τ * L)) * (32 * N * τ ^ 2) :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ Real.exp (-(2 * τ * L)) * (32 * N * (K ^ 2 * γ ^ 2)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [hτ2]) (Real.exp_pos _).le
      _ = γ ^ 2 * Real.exp (-(2 * τ * L)) * (32 * N * K ^ 2) := by ring
  exact hstep1.trans (hstep2.trans hmain)

end GaloisForLFunctions.BiarithmeticGaugeGeometry
