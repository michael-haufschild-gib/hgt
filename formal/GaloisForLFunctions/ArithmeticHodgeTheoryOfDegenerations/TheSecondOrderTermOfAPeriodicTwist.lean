import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsDiagonalInTheRamanujanBasis
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

/-!
# The second-order term of a periodic twist

Every mean-zero periodic twist `χ` of period `M` whose autocorrelation is even,
`C_χ = Σ_{m ∈ S} b_m c_m`, has second-order term `(Σ_m b_m J_{β+1}(m)) βJ/K ‖H‖²_{−(β+1)}`: the
Ramanujan expansion of the autocorrelation evaluated on the conductor counts.

* **Kuzmin–Landau on residue classes** (`norm_partial_cpow_real_le`,
  `norm_partial_shift_dvd_cpow_le`, `norm_partial_periodic_cpow_le`): a residue class `r + Mℤ` is
  the lattice `Mℤ` shifted by a real offset, and Kuzmin–Landau holds for `(x₀ + j)^{iτ}` with a real
  shift; so the partial sums of `χ(n) n^{iτ}` below `π n₀/M` are `O(N/(Mτ))`.
* **Quiet region** (`exists_periodicLow_energy_le`): every mean-zero periodic block has energy
  `O(N^{−1/2})` below `N e^{−A}/M`.
* **Even autocorrelation** (`abs_evenEnergy_sub_le`, `evenTwist_layer_criticalCurve_of_regularBulk`):
  the energy is `2π Σ_m b_m 𝒜^{(m)}_N(c) + O(c/N)` and the sharp form gives the limit.
* **The quadratic character** (`autoCorr_legTwist`, `legendre_layer_criticalCurve_of_regularBulk`):
  the autocorrelation of the Legendre symbol `(·/p)` is `c_p/p` (Jacobsthal), so its window has
  second-order term `((p^{β+1} − 1)/p) βJ/K ‖H‖²`: the conductor-`p` count with weight `1/p`.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Kuzmin–Landau on residue classes -/

/-- **Kuzmin–Landau with a real shift.** For `x₀ > 0`, `0 < τ ≤ π x₀` and `x₀ + k ≤ X`, the partial
sum `Σ_{m≤k} (x₀ + m)^{iτ}` has norm at most `3πX/τ + 1`. -/
theorem norm_partial_cpow_real_le {x₀ X : ℝ} (hx₀ : 0 < x₀) {k : ℕ} (hk : x₀ + k ≤ X) {τ : ℝ}
    (hτ : 0 < τ) (hτn : τ ≤ Real.pi * x₀) :
    ‖∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤
      3 * Real.pi * X / τ + 1 := by
  have hX0 : 0 < X := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set φ : ℕ → ℝ := fun m => m - τ * Real.log (x₀ + m) / (2 * Real.pi) with hφ
  have hterm : ∀ m : ℕ, Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    intro m
    have key : (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) +
        (-(((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I)) := by
      simp only [hφ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  have hconj : ∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (∑ m ∈ range (k + 1),
        Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum]
    exact sum_congr rfl fun m _ => hterm m
  rw [hconj, RCLike.norm_conj]
  set δ := τ / (2 * Real.pi * X) with hδ
  have hδ0 : 0 < δ := by positivity
  have hdiff : ∀ m : ℕ, φ (m + 1) - φ m =
      1 - τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
    intro m
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    simp only [hφ]
    push_cast
    rw [Real.log_div (by linarith) h1.ne', show (x₀ + ((m : ℝ) + 1)) = (x₀ + m) + 1 by ring]
    field_simp
    ring
  have hlog_le : ∀ m : ℕ, Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) ≤ 1 / (x₀ + m) := by
    intro m
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have := Real.log_le_sub_one_of_pos (show 0 < ((x₀ + m : ℝ) + 1) / (x₀ + m) by positivity)
    rw [show ((x₀ + m : ℝ) + 1) / (x₀ + m) - 1 = 1 / (x₀ + m) by field_simp; ring] at this
    exact this
  refine (RHTower.Sieve.kuzminLandau_band φ k hδ0 (fun m hm => ?_) (fun m hm => ?_)
    (fun m hm => ?_)).trans ?_
  · rw [hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have hle := hlog_le m
    have : τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) ≤ 1 / 2 := by
      calc τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m))
          ≤ τ / (2 * Real.pi) * (1 / (x₀ + m)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ τ / (2 * Real.pi) * (1 / x₀) := by
            gcongr
            linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        _ ≤ 1 / 2 := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
    have hδle : δ ≤ 1 / 2 := by
      rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hxX : x₀ ≤ X := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
      have := mul_le_mul_of_nonneg_left hxX Real.pi_pos.le
      linarith
    linarith
  · rw [hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have hge := one_div_add_one_le_log h1
    have hmN : (x₀ + m : ℝ) + 1 ≤ X := by
      have : (m : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hm
      linarith
    have : δ ≤ τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
      calc δ = τ / (2 * Real.pi) * (1 / X) := by rw [hδ]; field_simp
        _ ≤ τ / (2 * Real.pi) * (1 / ((x₀ + m : ℝ) + 1)) := by
            gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
    linarith
  · rw [hdiff, hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have h2 : Real.log (((x₀ + (m + 1 : ℕ) : ℝ) + 1) / (x₀ + (m + 1 : ℕ))) ≤
        Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
      push_cast
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) h1]
      ring_nf
      linarith
    have : 0 ≤ τ / (2 * Real.pi) := by positivity
    have := mul_le_mul_of_nonneg_left h2 this
    linarith
  · have : 3 / (2 * δ) = 3 * Real.pi * X / τ := by rw [hδ]; field_simp
    rw [this]

/-- **Kuzmin–Landau on a residue class.** For `0 < τ ≤ π n₀/M`, `n₀ + k ≤ N` and `s ≤ M`, the partial
sums of `n^{iτ}` over `n ∈ [n₀, n₀ + k]` with `M ∣ n + s` are at most `3πN/(Mτ) + 1`. -/
theorem norm_partial_shift_dvd_cpow_le {M : ℕ} (hM : 0 < M) {s : ℕ} (hs : s ≤ M) {n₀ N k : ℕ}
    (hn₀ : 1 ≤ n₀) (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / M) :
    ‖∑ m ∈ range (k + 1), (if M ∣ n₀ + m + s then
        Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0)‖ ≤
      3 * Real.pi * N / (M * τ) + 1 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set e : ℕ → ℂ := fun t => Complex.exp (((τ * Real.log ((t - s : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
    with he
  have hshift : ∑ m ∈ range (k + 1), (if M ∣ n₀ + m + s then
      Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0) =
      ∑ m ∈ range (k + 1), (if M ∣ (n₀ + s) + m then e ((n₀ + s) + m) else 0) := by
    refine sum_congr rfl fun m _ => ?_
    rw [show n₀ + m + s = n₀ + s + m by ring]
    simp only [he]
    congr 2
    rw [show n₀ + s + m - s = n₀ + m by omega]
  rw [hshift, sum_range_dvd_eq M (n₀ + s) k hM (by omega) e]
  obtain ⟨a, ha⟩ : ∃ a, a = (n₀ + s - 1) / M := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (n₀ + s + k) / M := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have haM : n₀ + s ≤ (a + 1) * M := by
    have := Nat.lt_div_mul_add (a := n₀ + s - 1) hM
    rw [ha, add_mul, one_mul]
    omega
  have hbM : b * M ≤ n₀ + s + k := by rw [hb]; exact Nat.div_mul_le_self _ _
  rcases Nat.lt_or_ge a b with hab | hab
  · set x₀ : ℝ := ((a + 1 : ℕ) : ℝ) - s / M with hx₀
    have hx₀n : (n₀ : ℝ) / M ≤ x₀ := by
      rw [hx₀, div_le_iff₀ hM0, sub_mul, div_mul_cancel₀ _ hM0.ne']
      have : (n₀ : ℝ) + s ≤ ((a + 1 : ℕ) : ℝ) * M := by exact_mod_cast haM
      linarith
    have hx₀0 : 0 < x₀ := lt_of_lt_of_le (by
      have : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      positivity) hx₀n
    have hreidx : ∑ c ∈ Finset.Ioc a b, e (M * c) = ∑ j ∈ range (b - (a + 1) + 1),
        Complex.exp (((τ * Real.log M : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((τ * Real.log (x₀ + j) : ℝ) : ℂ) * Complex.I) := by
      rw [show Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
        show b + 1 - (a + 1) = b - (a + 1) + 1 by omega]
      refine sum_congr rfl fun j _ => ?_
      simp only [he]
      have hj0 : (0 : ℝ) < x₀ + j := by positivity
      rw [← Complex.exp_add]
      congr 1
      have hsub : ((M * (a + 1 + j) - s : ℕ) : ℝ) = (M : ℝ) * (x₀ + j) := by
        have hle : s ≤ M * (a + 1 + j) := le_trans hs (Nat.le_mul_of_pos_right M (by omega))
        rw [Nat.cast_sub hle, hx₀]
        push_cast
        field_simp
        ring
      rw [hsub, Real.log_mul hM0.ne' hj0.ne']
      push_cast
      ring
    rw [hreidx, ← mul_sum, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hτx : τ ≤ Real.pi * x₀ := by
      refine hτn.trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hx₀n Real.pi_pos.le
    have hlast : x₀ + ((b - (a + 1) : ℕ) : ℝ) ≤ N / M := by
      rw [hx₀, Nat.cast_sub (by omega), le_div_iff₀ hM0]
      push_cast
      have : ((b : ℕ) : ℝ) * M ≤ (n₀ : ℝ) + s + k := by exact_mod_cast hbM
      have hNk : (n₀ : ℝ) + k ≤ N := by exact_mod_cast hk
      have : (((a : ℝ) + 1 - s / M + (b - (a + 1))) * M) = (b : ℝ) * M - s := by
        field_simp; ring
      rw [this]
      linarith
    have h := norm_partial_cpow_real_le hx₀0 hlast hτ hτx
    refine h.trans (le_of_eq ?_)
    field_simp
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]; positivity

/-- For `r < M`: `n ≡ r (mod M)` iff `M ∣ n + (M − r)`. -/
theorem mod_eq_iff_dvd_add_sub {M r n : ℕ} (hr : r < M) : n % M = r ↔ M ∣ n + (M - r) := by
  have hM : 0 < M := by omega
  have hrM : r + (M - r) = M := by omega
  constructor
  · intro h
    have h1 : n ≡ r [MOD M] := by
      rw [Nat.ModEq, h, Nat.mod_eq_of_lt hr]
    have h2 : n + (M - r) ≡ r + (M - r) [MOD M] := Nat.ModEq.add_right _ h1
    rw [hrM] at h2
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))
  · intro h
    have h2 : n + (M - r) ≡ r + (M - r) [MOD M] := by
      rw [hrM]
      exact (Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
    have h1 := Nat.ModEq.add_right_cancel' _ h2
    rw [Nat.ModEq, Nat.mod_eq_of_lt hr] at h1
    exact h1

/-- A periodic sequence is the sum of its residue classes: `χ(n) = Σ_{r<M} χ(r) [M ∣ n + M − r]`. -/
theorem periodic_eq_sum_dvd {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n)
    (n : ℕ) : χ n = ∑ r ∈ range M, (if M ∣ n + (M - r) then χ r else 0) := by
  have e : ∀ r ∈ range M, (if M ∣ n + (M - r) then χ r else 0) =
      (if n % M = r then χ r else 0) := fun r hr => by
    have hiff := mod_eq_iff_dvd_add_sub (n := n) (Finset.mem_range.mp hr)
    by_cases h1 : n % M = r
    · rw [if_pos (hiff.mp h1), if_pos h1]
    · rw [if_neg (fun h => h1 (hiff.mpr h)), if_neg h1]
  rw [sum_congr rfl e, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hM)),
    periodic_mod hper]

/-- **Kuzmin–Landau for a periodic twist.** For an `M`-periodic `χ`, `0 < τ ≤ π n₀/M` and
`n₀ + k ≤ N`, the partial sums of `χ(n) n^{iτ}` over `[n₀, n₀ + k]` are at most
`(Σ_{r<M} |χ(r)|)(3πN/(Mτ) + 1)`. -/
theorem norm_partial_periodic_cpow_le {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hper : ∀ n, χ (n + M) = χ n) {n₀ N k : ℕ} (hn₀ : 1 ≤ n₀) (hk : n₀ + k ≤ N) {τ : ℝ}
    (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / M) :
    ‖∑ j ∈ range (k + 1), (χ (n₀ + j) : ℂ) *
        Complex.exp (((τ * Real.log (n₀ + j) : ℝ) : ℂ) * Complex.I)‖ ≤
      (∑ r ∈ range M, |χ r|) * (3 * Real.pi * N / (M * τ) + 1) := by
  have hsplit : ∑ j ∈ range (k + 1), (χ (n₀ + j) : ℂ) *
      Complex.exp (((τ * Real.log (n₀ + j) : ℝ) : ℂ) * Complex.I) =
      ∑ r ∈ range M, (χ r : ℂ) * ∑ j ∈ range (k + 1), (if M ∣ n₀ + j + (M - r) then
        Complex.exp (((τ * Real.log ((n₀ + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [periodic_eq_sum_dvd hM hper (n₀ + j)]
    push_cast
    rw [Finset.sum_mul]
    refine sum_congr rfl fun r _ => ?_
    split_ifs <;> simp
  rw [hsplit, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_partial_shift_dvd_cpow_le hM (by omega) hn₀ hk hτ hτn) (abs_nonneg _)

/-! ### The quiet region of a periodic twist -/

/-- **A periodic block below its first resonance**: for `0 < |τ| ≤ π N e^{−A}/M`,
`|D_x(τ)| ≤ S(3πN/(M|τ|) + 1)(L e^{3A/2} + B e^{A/2})/√N`, `S = Σ_{r<M}|χ(r)|`. -/
theorem norm_dirichletPoly_periodic_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {χ : ℕ → ℝ}
    {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ0 : 0 < |τ|) (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / M) :
    ‖dirichletPoly N (twistedWeights h χ N) τ‖ ≤
      (∑ r ∈ range M, |χ r|) * (3 * Real.pi * N / (M * |τ|) + 1) *
        ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have key : ∀ t : ℝ, 0 < t → t ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / M →
      ‖dirichletPoly N (twistedWeights h χ N) t‖ ≤
        (∑ r ∈ range M, |χ r|) * (3 * Real.pi * N / (M * t) + 1) *
          ((L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) / Real.sqrt N) := by
    intro t ht htN
    set n₀ := windowStart A N with hn₀
    have h1 := one_le_windowStart hN A
    have h2 : n₀ ≤ N := windowStart_le hA
    have htn : t ≤ Real.pi * n₀ / M := by
      refine htN.trans (div_le_div_of_nonneg_right ?_ hM0.le)
      exact mul_le_mul_of_nonneg_left (le_windowStart A N) Real.pi_pos.le
    rw [dirichletPoly_twisted_eq_range hsupp hA _ hN]
    refine (norm_sum_mul_le_of_partial (fun j => horizonWeights h N (n₀ + j))
      (fun j => (χ (n₀ + j) : ℂ) * Complex.exp (((t * Real.log (n₀ + j) : ℝ) : ℂ) *
        Complex.I)) (N - n₀) (B := (∑ r ∈ range M, |χ r|) * (3 * Real.pi * N / (M * t) + 1))
          fun k hk => ?_).trans ?_
    · have := norm_partial_periodic_cpow_le hM hper h1 (show n₀ + k ≤ N by omega) ht htn
      push_cast at this ⊢
      exact this
    · exact mul_le_mul_of_nonneg_left (variation_horizonWeights_le hsupp hA hB hL hN)
        (by positivity)
  rcases lt_or_gt_of_ne (abs_pos.mp hτ0) with hneg | hpos
  · have := key (-τ) (by linarith) (by rw [abs_of_neg hneg] at hτ; exact hτ)
    rw [norm_dirichletPoly_neg, ← abs_of_neg hneg] at this
    exact this
  · rw [abs_of_pos hpos] at hτ ⊢
    exact key τ hpos hτ

/-- Frequencies beyond `√N` and below the first resonance of a periodic block:
`|D_x(τ)|²/N ≤ 18π² S² V²/(M² τ²) + 2S² V²/N²`. -/
theorem periodicLow_large_le {Bh L : ℝ} (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    (hA : 0 ≤ A) (hB : ∀ y, |h y| ≤ Bh) (hL : ∀ u v, |h u - h v| ≤ L * |u - v|) {χ : ℕ → ℝ}
    {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ0 : 0 < |τ|) (hτ : |τ| ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / M) :
    ‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 / N ≤
      18 * Real.pi ^ 2 * (∑ r ∈ range M, |χ r|) ^ 2 / (M : ℝ) ^ 2 *
          (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / τ ^ 2 +
        2 * (∑ r ∈ range M, |χ r|) ^ 2 *
          (L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2)) ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set V := L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) with hV
  set S := ∑ r ∈ range M, |χ r| with hS
  have hD := norm_dirichletPoly_periodic_le hsupp hA hB hL hM hper hN hτ0 hτ
  rw [← hV, ← hS] at hD
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have hsq : (S * (3 * Real.pi * N / (M * |τ|) + 1)) ^ 2 ≤
      2 * (S * (3 * Real.pi * N / (M * |τ|))) ^ 2 + 2 * S ^ 2 := by
    nlinarith [sq_nonneg (S * (3 * Real.pi * N / (M * |τ|)) - S)]
  have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  rw [div_le_iff₀ hN0]
  refine h2.trans ?_
  rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
  refine (mul_le_mul_of_nonneg_right hsq (by positivity)).trans (le_of_eq ?_)
  rw [hτ2]
  have : |τ| ≠ 0 := hτ0.ne'
  field_simp
  ring

/-- Small frequencies of a mean-zero periodic block: for `|τ| ≤ √N`, `|D_x(τ)|²/N ≤ 4W²/N`,
`W = 2 S e^{2A}(L + B)`, `S = Σ_{j<M} |χ(j)|`. -/
theorem periodicLow_small_le (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {Bh : ℝ} (hB : ∀ y, |h y| ≤ Bh) {Lh : NNReal}
    (hLh : LipschitzWith Lh h) {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) {N : ℕ} (hN : 1 ≤ N) {τ : ℝ}
    (hτ : |τ| ≤ Real.sqrt N) :
    ‖dirichletPoly N (twistedWeights h (χ) N) τ‖ ^ 2 / N ≤
      4 * (2 * (∑ j ∈ range m, |χ j|) * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) ^ 2 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : (0 : ℝ) ≤ Lh := Lh.2
  set S := ∑ j ∈ range m, |χ j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hD := norm_sq_dirichletPoly_twisted_le hh hA hsupp hB hLh (hχ) hN τ
  have hK : (Lh : ℝ) + (1 / 2 + |τ|) * Bh ≤ ((Lh : ℝ) + Bh) * (2 * Real.sqrt N) := by
    nlinarith [mul_le_mul_of_nonneg_right hτ hBh0]
  have h1 : 2 * S * (((Lh : ℝ) + (1 / 2 + |τ|) * Bh) * Real.exp (2 * A)) / N ≤
      2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N := by gcongr
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [div_le_div_iff_of_pos_right hN0]
  refine hD.trans ((mul_le_mul_of_nonneg_left h2 hN0.le).trans (le_of_eq ?_))
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  rw [show 2 * S * (((Lh : ℝ) + Bh) * (2 * Real.sqrt N) * Real.exp (2 * A)) / N =
      (2 * S * Real.exp (2 * A) * ((Lh : ℝ) + Bh)) * (2 * Real.sqrt N / N) by ring, mul_pow,
    div_pow, mul_pow 2 (Real.sqrt N), hsq]
  field_simp
  ring

/-- **A mean-zero periodic block is quiet below its first resonance**: the energy on
`|τ| ≤ N e^{−A}/M` is `O(N^{−1/2})` (twisted Riemann sums for `|τ| ≤ √N`, Kuzmin–Landau on the
residue classes beyond). -/
theorem exists_periodicLow_energy_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    {Cφ q : ℝ} (hq : 0 ≤ q) (hCφ : 0 ≤ Cφ)
    (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {χ : ℕ → ℝ} {m : ℕ} (hχ : MeanZeroTwist χ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c →
      ∫ τ in Set.Icc (-((N : ℝ) * Real.exp (-(A + Real.log m))))
          ((N : ℝ) * Real.exp (-(A + Real.log m))),
        ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h (χ) N) τ‖ ^ 2 / N) ≤ C / Real.sqrt N := by
  have hm' : 0 < m := hχ.pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm'
  obtain ⟨Bh, L, hB, hL⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lh, hLh⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_of_window hsupp) hh (by norm_num)
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0; norm_num at this; linarith [abs_nonneg (h 1 - h 0)]
  obtain ⟨W, hW⟩ : ∃ W, W = 2 * (∑ j ∈ range m, |χ j|) * Real.exp (2 * A) *
      ((Lh : ℝ) + Bh) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = L * Real.exp (3 / 2 * A) + Bh * Real.exp (A / 2) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  obtain ⟨a, ha⟩ : ∃ a, a = 18 * Real.pi ^ 2 * (∑ r ∈ range m, |χ r|) ^ 2 / (m : ℝ) ^ 2 * V ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 2 * (∑ r ∈ range m, |χ r|) ^ 2 * V ^ 2 := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  refine ⟨Cφ * (8 * W ^ 2) + 2 * Real.pi * (Cφ * a) + 2 * (Cφ * b), by positivity,
    fun N hN c hc => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsN1 : 1 ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN1
  have hNs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = (N : ℝ) * Real.exp (-(A + Real.log m)) := ⟨_, rfl⟩
  rw [← hT₀]
  have hT₀0 : 0 ≤ T₀ := by rw [hT₀]; positivity
  have hT₀N : T₀ ≤ N := by
    rw [hT₀]
    have : Real.exp (-(A + Real.log m)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ m by
        exact_mod_cast hm')])
    nlinarith
  have hT₀res : T₀ ≤ Real.pi * ((N : ℝ) * Real.exp (-A)) / m := by
    rw [hT₀, neg_add, Real.exp_add, Real.exp_neg (Real.log m), Real.exp_log hm0, le_div_iff₀ hm0]
    have : (N : ℝ) * (Real.exp (-A) * (m : ℝ)⁻¹) * m = N * Real.exp (-A) := by field_simp
    rw [this]
    nlinarith [Real.pi_gt_three, mul_nonneg hN0.le (Real.exp_pos (-A)).le]
  have hφb : ∀ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 ≤ Cφ := fun τ => by
    have := hdecay (c / N * τ)
    rw [show ((c / N * τ : ℝ) : ℂ) = ((c / N : ℝ) : ℂ) * (τ : ℂ) by push_cast; ring] at this
    refine this.trans ?_
    have : (1 + |(c / N * τ)|) ^ (-q) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (c / N * τ)]) (by linarith)
    nlinarith
  have hb₁ : ∀ τ ∈ Set.Icc (-T₀) T₀, |τ| ≤ Real.sqrt N →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (χ) N) τ‖ ^ 2 / N) ≤ Cφ * (4 * W ^ 2 / N) :=
    fun τ _ hτ => by
      have := periodicLow_small_le hh hA hsupp hB hLh hχ hN hτ
      rw [← hW] at this
      exact mul_le_mul (hφb τ) this (by positivity) hCφ
  have hb₂ : ∀ τ ∈ Set.Icc (-T₀) T₀, Real.sqrt N ≤ |τ| →
      ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
        (‖dirichletPoly N (twistedWeights h (χ) N) τ‖ ^ 2 / N) ≤
        Cφ * a / τ ^ 2 + Cφ * (b / (N : ℝ) ^ 2) :=
    fun τ hτ hτs => by
      have hτ0 : 0 < |τ| := lt_of_lt_of_le hsN hτs
      have := periodicLow_large_le hsupp hA hB hL hm' hχ.periodic hN hτ0 ((abs_le.mpr hτ).trans hT₀res)
      rw [← hV, ← ha, ← hb] at this
      refine (mul_le_mul (hφb τ) this (by positivity) hCφ).trans (le_of_eq ?_)
      ring
  have hint : IntegrableOn (fun τ : ℝ => ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
      (‖dirichletPoly N (twistedWeights h (χ) N) τ‖ ^ 2 / N)) (Set.Icc (-T₀) T₀) :=
    (integrable_energyW hφ hφsupp _ hc hN).integrableOn
  have hsplit := setIntegral_Icc_le_of_split hsN hT₀0 hint (by positivity) (by positivity)
    (by positivity) hb₁ hb₂
  refine hsplit.trans ?_
  have e1 : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) = Cφ * (8 * W ^ 2) / Real.sqrt N := by
    rw [eq_div_iff hsN.ne']
    have : 2 * Real.sqrt N * (Cφ * (4 * W ^ 2 / N)) * Real.sqrt N =
        Cφ * (8 * W ^ 2) * ((Real.sqrt N * Real.sqrt N) / N) := by ring
    rw [this, hNs, div_self hN0.ne', mul_one]
  have e2 : 2 * (Cφ * a) * (Real.pi / Real.sqrt N) = 2 * Real.pi * (Cφ * a) / Real.sqrt N := by
    ring
  have e3 : 2 * T₀ * (Cφ * (b / (N : ℝ) ^ 2)) ≤ 2 * (Cφ * b) / Real.sqrt N := by
    have hX : 0 ≤ 2 * (Cφ * b) := by positivity
    have h1 : 2 * T₀ * (Cφ * (b / (N : ℝ) ^ 2)) ≤ 2 * (Cφ * b) / N := by
      have : 2 * (Cφ * b) / N = 2 * N * (Cφ * (b / (N : ℝ) ^ 2)) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine h1.trans (div_le_div_of_nonneg_left hX hsN ?_)
    calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := le_mul_of_one_le_left hsN.le hsN1
      _ = N := hNs
  rw [e1, e2, add_div, add_div]
  linarith


/-! ### Twists with even autocorrelation -/

/-- **The energy of a twist with even autocorrelation**: if `C_χ = Σ_{m ∈ S} b_m c_m`, then
`E_N = 2π Σ_m b_m 𝒜^{(m)}_N(c) + O(c/N)`. -/
theorem abs_evenEnergy_sub_le (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n)
    {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m) (b : ℕ → ℝ)
    (hC : ∀ δ, autoCorr χ M δ = ∑ m ∈ S, b m * autoCorr (ramTwist m) m δ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, 4 * c ≤ N →
      |(∫ τ : ℝ, ‖paperFT (cx φ) (((c / N : ℝ) : ℂ) * τ)‖ ^ 2 *
          (‖dirichletPoly N (twistedWeights h χ N) τ‖ ^ 2 / N)) -
        2 * Real.pi * ∑ m ∈ S, b m * ramAlias φ h m c N| ≤ K * c / N := by
  obtain ⟨K, hK0, hK⟩ := periodicEnergy_le hφ hφsupp hh hA hsupp hM hper
  refine ⟨K, hK0, fun c hc N hcN => ?_⟩
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hmain : 2 * Real.pi / c * ∑ n ∈ Icc 1 N, horizonWeights h N n ^ 2 *
      ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊, autoCorr χ M δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
      2 * Real.pi * ∑ m ∈ S, b m * ramAlias φ h m c N := by
    simp_rw [hC, Finset.sum_mul]
    have e : ∀ n ∈ Icc 1 N, horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
        ∑ m ∈ S, b m * autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹) =
        ∑ m ∈ S, b m * (horizonWeights h N n ^ 2 * ∑ δ ∈ Finset.Icc (-(⌈c⌉₊ : ℤ)) ⌈c⌉₊,
          autoCorr (ramTwist m) m δ * shellAutocorr φ (δ * (c * n / N)⁻¹)) := fun n _ => by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact sum_congr rfl fun δ _ => by ring
    rw [sum_congr rfl e, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [← Finset.mul_sum]
    linear_combination (b m) * ramMain_eq hφ hφsupp h (hS m hm) hc0 hN0
  rw [← hmain]
  exact hK c hc N hcN

/-- **The second-order term of a periodic twist is the Ramanujan expansion of its
autocorrelation.** For a mean-zero `M`-periodic twist whose autocorrelation is even,
`C_χ = Σ_{m ∈ S} b_m c_m` (`m ≥ 2`), along `c^{β+1}/log N → K`:
`c⁻¹⟨W x, x⟩/∫g² → (Σ_m b_m J_{β+1}(m)) βJ/K ∫ e^{−(β+1)y} H²`. -/
theorem evenTwist_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {χ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) {S : Finset ℕ} (hS : ∀ m ∈ S, 1 < m)
    (b : ℕ → ℝ) (hC : ∀ δ, autoCorr χ M δ = ∑ m ∈ S, b m * autoCorr (ramTwist m) m δ) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h χ N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 ((∑ m ∈ S, b m * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsharp := twisted_layer_sharp_of_energy hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp hc1 hcinf
    hclog hχ (fun c N => ∑ m ∈ S, b m * ramAlias φ h m c N)
    (abs_evenEnergy_sub_le hφ hφsupp hh hA hsupp hχ.pos hχ.periodic hS b hC)
    (exists_periodicLow_energy_le hφ hφsupp (by linarith : 0 ≤ q) hCφ hdecay hh hA hsupp hχ)
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  have hterm : Tendsto (fun N : ℕ => Real.log N / (∫ u, φ u ^ 2) *
      ∑ m ∈ S, b m * ramAlias φ h m (c N) N) atTop
      (𝓝 (∑ m ∈ S, b m * (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J / K *
        I))) := by
    have := tendsto_finsetSum S fun m _ =>
      (tendsto_log_mul_ramAlias hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk hh hA hsupp hc1 hK hcrit
        m).const_mul (b m)
    refine this.congr fun N => ?_
    rw [Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : ∑ m ∈ S, b m * (ArithmeticDegenerationTheory.jordanTotient (β + 1) m * β * J /
      K * I) = (∑ m ∈ S, b m * ArithmeticDegenerationTheory.jordanTotient (β + 1) m) * β *
        J / K * I := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

/-! ### The quadratic character -/

theorem sum_zmod_eq_sum_range {R : Type*} [AddCommMonoid R] (q : ℕ) [NeZero q]
    (f : ZMod q → R) : ∑ a : ZMod q, f a = ∑ r ∈ Finset.range q, f (r : ZMod q) := by
  have hfinEquiv (r : Fin q) : ZMod.finEquiv q r = (r.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q =>
        apply ZMod.val_injective
        change r.val = r.val % (q + 1)
        rw [Nat.mod_eq_of_lt r.isLt]
  calc (∑ a : ZMod q, f a) = ∑ r : Fin q, f (ZMod.finEquiv q r) :=
        ((ZMod.finEquiv q).sum_comp f).symm
    _ = ∑ r : Fin q, f (r.val : ZMod q) := by simp_rw [hfinEquiv]
    _ = ∑ r ∈ Finset.range q, f (r : ZMod q) :=
        Fin.sum_univ_eq_sum_range (fun r : ℕ => f (r : ZMod q)) q

/-- The quadratic character `(n/p)` of an odd prime as a real twist. -/
def legTwist (p : RHTower.OddPrime) (n : ℕ) : ℝ :=
  ((quadraticChar (ZMod p.1) (n : ZMod p.1) : ℤ) : ℝ)

theorem legTwist_complex (p : RHTower.OddPrime) (n : ℕ) :
    ((legTwist p n : ℝ) : ℂ) = RHTower.oddPrimeQuadraticCharacter p (n : ZMod p.1) := by
  simp [legTwist, RHTower.oddPrimeQuadraticCharacter]

theorem legTwist_add_self (p : RHTower.OddPrime) (n : ℕ) : legTwist p (n + p.1) = legTwist p n := by
  simp [legTwist]

/-- The quadratic character of an odd prime is a mean-zero twist. -/
theorem meanZeroTwist_legTwist (p : RHTower.OddPrime) : MeanZeroTwist (legTwist p) p.1 where
  pos := p.2.1.pos
  periodic := legTwist_add_self p
  mean_zero := by
    haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩
    have h := RHTower.oddPrimeQuadraticCharacter_sum_zero p
    rw [sum_zmod_eq_sum_range] at h
    have h2 : ((∑ r ∈ range p.1, legTwist p r : ℝ) : ℂ) = 0 := by
      push_cast
      simp_rw [legTwist_complex]
      exact h
    exact_mod_cast h2

theorem ramTwist_prime {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ramTwist p n = (if p ∣ n then (p : ℝ) else 0) - 1 := by
  rw [ramTwist, Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℝ) *
      (if b ∣ n then (b : ℝ) else 0)), Nat.Prime.divisors hp,
    Finset.sum_pair (Ne.symm hp.one_lt.ne')]
  simp [Nat.div_self hp.pos, ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- **The autocorrelation of the quadratic character** is `c_p/p`: `p⁻¹Σ_{r<p} (r/p)((r+s)/p) =
(p [p ∣ s] − 1)/p`. -/
theorem autoCorr_legTwist (p : RHTower.OddPrime) (δ : ℤ) :
    autoCorr (legTwist p) p.1 δ = (p.1 : ℝ)⁻¹ * autoCorr (ramTwist p.1) p.1 δ := by
  haveI : NeZero p.1 := ⟨p.2.1.ne_zero⟩
  have hp0 : 0 < p.1 := p.2.1.pos
  rw [autoCorr_ramTwist hp0, periodicExt_ramTwist_eq hp0, autoCorr, periodMean]
  simp_rw [periodicExt_add_nat hp0 (legTwist_add_self p)]
  congr 1
  set s := (δ % (p.1 : ℤ)).toNat with hs
  have hcorr := RHTower.oddPrime_quadratic_shiftCorrelation p 0 (s : ZMod p.1)
  rw [sum_zmod_eq_sum_range] at hcorr
  simp only [add_zero] at hcorr
  have hsum : ((∑ r ∈ range p.1, legTwist p r * legTwist p (r + s) : ℝ) : ℂ) =
      if (0 : ZMod p.1) = s then (p.1 : ℂ) - 1 else -1 := by
    push_cast
    simp_rw [legTwist_complex]
    rw [← hcorr]
    exact sum_congr rfl fun r _ => by push_cast; ring
  have hram : ∑ x ∈ p.1.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℝ) *
      (if (x.2 : ℤ) ∣ δ then (x.2 : ℝ) else 0) = (if (0 : ZMod p.1) = s then (p.1 : ℝ) - 1 else -1) := by
    rw [← periodicExt_ramTwist_eq hp0, periodicExt, ← hs, ramTwist_prime p.2.1]
    have hiff : p.1 ∣ s ↔ (0 : ZMod p.1) = s := by
      rw [eq_comm, ZMod.natCast_eq_zero_iff]
    by_cases hd : p.1 ∣ s
    · rw [if_pos hd, if_pos (hiff.mp hd)]
    · rw [if_neg hd, if_neg (fun h => hd (hiff.mpr h))]; ring
  rw [hram]
  have h2 : (∑ r ∈ range p.1, legTwist p r * legTwist p (r + s) : ℝ) =
      if (0 : ZMod p.1) = s then (p.1 : ℝ) - 1 else -1 := by
    have := hsum
    split_ifs at this ⊢ <;> exact_mod_cast this
  exact h2

/-- **The quadratic-character window.** For an odd prime `p`, along `c^{β+1}/log N → K`, the window
twisted by the Legendre symbol `(n/p)` has
`c⁻¹⟨W x, x⟩/∫g² → ((p^{β+1} − 1)/p) βJ/K ∫ e^{−(β+1)y} H²`: the conductor-`p` count with weight
`1/p`, since the autocorrelation of `(·/p)` is `c_p/p`. -/
theorem legendre_layer_criticalCurve_of_regularBulk (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β J : ℝ} (hβ : 0 ≤ β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    (p : RHTower.OddPrime) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (legTwist p) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (((p.1 : ℝ) ^ (β + 1) - 1) / p.1 * β * J / K *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  have hlim := evenTwist_layer_criticalCurve_of_regularBulk hφ hφsupp hφ2 hq hCφ hdecay hβ hbulk
    hh hA hsupp hc1 hK hcrit (meanZeroTwist_legTwist p) (S := {p.1})
    (by intro m hm; rw [Finset.mem_singleton] at hm; rw [hm]; exact p.2.1.one_lt)
    (fun _ => (p.1 : ℝ)⁻¹) (fun δ => by rw [Finset.sum_singleton, autoCorr_legTwist])
  have hJ : ArithmeticDegenerationTheory.jordanTotient (β + 1) p.1 = (p.1 : ℝ) ^ (β + 1) - 1 := by
    rw [ArithmeticDegenerationTheory.jordanTotient, Nat.Prime.divisors p.2.1,
      Finset.sum_pair (Ne.symm p.2.1.one_lt.ne')]
    simp [Nat.div_self p.2.1.pos, ArithmeticFunction.moebius_apply_prime p.2.1]
    ring
  rw [Finset.sum_singleton, hJ] at hlim
  convert hlim using 2
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
