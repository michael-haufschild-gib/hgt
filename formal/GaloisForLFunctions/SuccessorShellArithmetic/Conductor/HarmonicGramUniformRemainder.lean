import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramTorsionEnergy
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon

/-!
# A common horizon remainder for the harmonic conductor Gram

Complete-period Plancherel bounds the absolute mass of a centered product
of normalized Ramanujan modes. Abel summation then gives a uniform tail
bound to its exact torsion-intersection limit. The sharp two-sided
large sieve gives the quadratic remainder without summing entrywise errors.
-/

open Finset Filter ArithmeticFunction
open scoped Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedBiarithmeticGeometry
  ArithmeticEffectivityTheory BezoutValuationIncidence
noncomputable section

private theorem harmonic_tail_bound {a : ℕ → ℝ} {B L : ℝ}
    (hB : ∀ l k : ℕ, l ≤ k → |∑ n ∈ Ico l k, a n| ≤ B)
    (hlim : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℝ)) atTop (𝓝 L)) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, a n / (n : ℝ)) - L| ≤ B / ((N : ℝ) + 1) := by
  have ht (M : ℕ) (hNM : N ≤ M) :
      |(∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N, a n / (n : ℝ)| ≤ B / ((N : ℝ) + 1) := by
    have h := HTGeometry.abs_sum_Ico_div_add_le (r := 0) hB (N + 1) (M + 1) (by positivity)
    have he := Finset.sum_Ico_consecutive (f := fun n => a n / (n : ℝ))
      (show 1 ≤ N + 1 by omega) (show N + 1 ≤ M + 1 by omega)
    simp only [Ico_add_one_right_eq_Icc] at he h
    have he' : (∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N, a n / (n : ℝ) = ∑ n ∈ Icc (N + 1) M, a n / (n : ℝ) := by
      linarith only [he]
    rw [he']
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using h
  have h := le_of_tendsto ((hlim.sub_const (∑ n ∈ Icc 1 N, a n / (n : ℝ))).abs) (by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact ht M hNM)
  rwa [abs_sub_comm] at h

private theorem harmonic_tail_bound_of_windows {a : ℕ → ℝ} {B L : ℝ}
    (hB : ∀ A K : ℕ, |∑ n ∈ Icc (A + 1) (A + K), a n| ≤ B)
    (hlim : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℝ)) atTop (𝓝 L)) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, a n / (n : ℝ)) - L| ≤ B / ((N : ℝ) + 1) := by
  have ht (M : ℕ) (hNM : N ≤ M) :
      |(∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N, a n / (n : ℝ)| ≤ B / ((N : ℝ) + 1) := by
    have hpartial (t : ℕ) (_ : t ≤ M - N) :
        |∑ j ∈ range t, a (N + 1 + j)| ≤ B := by
      have h := hB N t
      rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range] at h
      simpa only [show N + t + 1 - (N + 1) = t by omega] using h
    have h := HTGeometry.abs_sum_mul_le_of_finite_partial
      (g := fun i => a (N + 1 + i))
      (w := fun i => 1 / ((N + 1 + i : ℕ) : ℝ)) (M - N) hpartial
      (fun i => by positivity)
      (fun i => by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        linarith)
    have he := Finset.sum_Ico_consecutive (f := fun n => a n / (n : ℝ))
      (show 1 ≤ N + 1 by omega) (show N + 1 ≤ M + 1 by omega)
    simp only [Ico_add_one_right_eq_Icc] at he
    have he' : (∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N, a n / (n : ℝ) = ∑ n ∈ Icc (N + 1) M, a n / (n : ℝ) := by
      linarith only [he]
    rw [he', ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simpa only [show M + 1 - (N + 1) = M - N by omega, Nat.add_zero,
      Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_comm] using h
  have h := le_of_tendsto ((hlim.sub_const (∑ n ∈ Icc 1 N, a n / (n : ℝ))).abs) (by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact ht M hNM)
  rwa [abs_sub_comm] at h

private theorem normalized_common_period_square {m q : ℕ} (hm : 0 < m)
    (hmq : m ∣ q) (hq : 0 < q) :
    (∑ n ∈ range q, normalizedRamanujanMode m n ^ 2) = (q : ℝ) := by
  have h := periodMean_normalizedRamanujanMode_mul hm hm hmq hmq hq
  simp only [periodMean, ite_true, ← pow_two] at h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  exact (div_eq_iff hqR).mp h |>.trans (one_mul _)

private theorem normalized_product_period_mass {m l q : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmq : m ∣ q) (hlq : l ∣ q) (hq : 0 < q) :
    (∑ n ∈ range q, |normalizedRamanujanMode m n * normalizedRamanujanMode l n -
      (if m = l then 1 else 0)|) ≤ 2 * (q : ℝ) := by
  let δ : ℝ := if m = l then 1 else 0
  have hδ : 0 ≤ δ ∧ δ ≤ 1 := by dsimp only [δ]; split_ifs <;> norm_num
  have hpoint (n : ℕ) :
      |normalizedRamanujanMode m n * normalizedRamanujanMode l n - δ| ≤
      (normalizedRamanujanMode m n ^ 2 + normalizedRamanujanMode l n ^ 2) / 2 + δ := by
    have hp : |normalizedRamanujanMode m n * normalizedRamanujanMode l n| ≤
        (normalizedRamanujanMode m n ^ 2 + normalizedRamanujanMode l n ^ 2) / 2 := by
      rw [abs_mul]
      nlinarith only [sq_nonneg (|normalizedRamanujanMode m n| - |normalizedRamanujanMode l n|),
        sq_abs (normalizedRamanujanMode m n), sq_abs (normalizedRamanujanMode l n)]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hδ.1]; exact add_le_add hp le_rfl)
  calc
    _ ≤ ∑ n ∈ range q,
        ((normalizedRamanujanMode m n ^ 2 + normalizedRamanujanMode l n ^ 2) / 2 + δ) :=
      sum_le_sum fun n _ => hpoint n
    _ = ((q : ℝ) + q) / 2 + (q : ℝ) * δ := by
      rw [sum_add_distrib, ← sum_div, sum_add_distrib,
        normalized_common_period_square hm hmq hq, normalized_common_period_square hl hlq hq]
      simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hδ.2 (Nat.cast_nonneg q)
      linarith only [h]

private theorem centered_normalized_product_harmonic (m l N : ℕ) :
    (∑ n ∈ Icc 1 N,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n -
        (if m = l then 1 else 0)) / (n : ℝ)) =
      (∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        (if m = l then 1 else 0) * (harmonic N : ℝ) := by
  simp only [sub_div, sum_sub_distrib]
  congr 1
  rw [← HTGeometry.sum_Icc_one_div_eq_harmonic, mul_sum]
  apply sum_congr rfl
  intro n _
  ring

/-- Harmonic centering leaves the torsion finite part with a uniform `4ml/(N+1)` remainder. -/
theorem abs_normalizedRamanujan_harmonicGram_torsion_remainder {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        (if m = l then 1 else 0) * (harmonic N : ℝ) +
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))| ≤
      4 * (m : ℝ) * l / ((N : ℝ) + 1) := by
  let q := m * l
  let δ : ℝ := if m = l then 1 else 0
  let a : ℕ → ℝ := fun n => normalizedRamanujanMode m n * normalizedRamanujanMode l n - δ
  let I := orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))
  have hq : 0 < q := Nat.mul_pos hm hl
  have hmq : m ∣ q := dvd_mul_right m l
  have hlq : l ∣ q := dvd_mul_left l m
  have hpm : Function.Periodic (normalizedRamanujanMode m) q := by
    simpa only [q, Nat.cast_id, Nat.mul_comm] using (normalizedRamanujanMode_periodic hm).nat_mul l
  have hpl : Function.Periodic (normalizedRamanujanMode l) q := by
    simpa only [q, Nat.cast_id] using (normalizedRamanujanMode_periodic hl).nat_mul m
  have hper : Function.Periodic a q := fun n => by dsimp only [a]; rw [hpm, hpl]
  have hmean := periodMean_normalizedRamanujanMode_mul hm hl hmq hlq hq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hzero : (∑ n ∈ range q, a n) = 0 := by
    simp only [periodMean] at hmean
    have he := (div_eq_iff hqR).mp hmean
    simp only [a, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    dsimp only [δ]
    linear_combination he
  have hB (j k : ℕ) (hjk : j ≤ k) : |∑ n ∈ Ico j k, a n| ≤ 4 * (q : ℝ) := by
    have h := HTGeometry.abs_sum_Ico_le_of_periodic hq hper hzero j k hjk
    have hv := normalized_product_period_mass hm hl hmq hlq hq
    change (∑ n ∈ range q, |a n|) ≤ 2 * (q : ℝ) at hv
    linarith only [h, hv]
  have hG : Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        δ * Real.log T) atTop (𝓝 (δ * Real.eulerMascheroniConstant - I)) := by
    simpa only [δ, I, ite_mul, one_mul, zero_mul] using
      tendsto_normalizedRamanujan_harmonicGram_torsion hm hl
  have hH := Real.tendsto_harmonic_sub_log.const_mul δ
  have hlim := hG.sub hH
  have hv : (δ * Real.eulerMascheroniConstant - I) - δ * Real.eulerMascheroniConstant = -I := by ring
  rw [hv] at hlim
  have ha : Tendsto (fun T : ℕ => ∑ n ∈ Icc 1 T, a n / (n : ℝ)) atTop (𝓝 (-I)) := by
    refine hlim.congr fun T => ?_
    change _ = ∑ n ∈ Icc 1 T,
      (normalizedRamanujanMode m n * normalizedRamanujanMode l n - (if m = l then 1 else 0)) /
        (n : ℝ)
    rw [centered_normalized_product_harmonic]
    dsimp only [δ]
    ring
  have h := harmonic_tail_bound hB ha N
  change |(∑ n ∈ Icc 1 N,
    (normalizedRamanujanMode m n * normalizedRamanujanMode l n - (if m = l then 1 else 0)) /
      (n : ℝ)) - -I| ≤ 4 * (q : ℝ) / ((N : ℝ) + 1) at h
  rw [centered_normalized_product_harmonic, sub_neg_eq_add] at h
  simpa only [I, q, Nat.cast_mul, mul_assoc] using h

#print axioms abs_normalizedRamanujan_harmonicGram_torsion_remainder

/-- Replacing the harmonic number by its logarithm adds only the diagonal `1/N` remainder. -/
theorem abs_normalizedRamanujan_harmonicGram_log_remainder {m l N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hN : 1 ≤ N) :
    |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) -
        (if m = l then Real.log N else 0) -
        ((if m = l then Real.eulerMascheroniConstant else 0) -
          orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)))| ≤
      4 * (m : ℝ) * l / ((N : ℝ) + 1) + (if m = l then 1 else 0) / (N : ℝ) := by
  let G := ∑ n ∈ Icc 1 N,
    normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)
  let δ : ℝ := if m = l then 1 else 0
  let I := orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))
  have hδ : 0 ≤ δ := by dsimp only [δ]; split_ifs <;> norm_num
  have he (x : ℝ) : (if m = l then x else 0) = δ * x := by
    dsimp only [δ]
    split_ifs <;> ring
  have hr : |G - δ * (harmonic N : ℝ) + I| ≤ 4 * (m : ℝ) * l / ((N : ℝ) + 1) :=
    abs_normalizedRamanujan_harmonicGram_torsion_remainder hm hl N
  have hh := _root_.HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hN
  change |G - (if m = l then Real.log N else 0) -
    ((if m = l then Real.eulerMascheroniConstant else 0) - I)| ≤
      4 * (m : ℝ) * l / ((N : ℝ) + 1) + δ / N
  rw [he, he]
  calc
    _ = |(G - δ * (harmonic N : ℝ) + I) +
        δ * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)| := by
      congr 1
      ring
    _ ≤ |G - δ * (harmonic N : ℝ) + I| +
        |δ * ((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant)| := abs_add_le _ _
    _ ≤ 4 * (m : ℝ) * l / ((N : ℝ) + 1) + δ * (1 / N) := by
      rw [abs_mul, abs_of_nonneg hδ]
      exact add_le_add hr (mul_le_mul_of_nonneg_left hh hδ)
    _ = _ := by ring

#print axioms abs_normalizedRamanujan_harmonicGram_log_remainder

private theorem normalized_coefficient_selfMass (Q : ℕ) (a : ℕ → ℝ) :
    ArithmeticElectrostatics.selfMass Q (fun m => a m / Real.sqrt (m.totient : ℝ)) =
      ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  unfold ArithmeticElectrostatics.selfMass
  apply sum_congr rfl
  intro m hm
  have hφ : (m.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (mem_Icc.mp hm).1).ne'
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  field_simp [hφ]

private theorem centered_packet_harmonic (F : ℕ → ℝ) (M : ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, (F n ^ 2 - M) / (n : ℝ)) =
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) - (harmonic N : ℝ) * M := by
  simp only [sub_div, sum_sub_distrib]
  congr 1
  rw [← HTGeometry.sum_Icc_one_div_eq_harmonic, sum_mul]
  apply sum_congr rfl
  intro n _
  ring

private theorem normalized_packet_harmonic_limit (Q : ℕ) (a : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      ((∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 -
        ∑ m ∈ Icc 1 Q, a m ^ 2) / (n : ℝ)) atTop
      (𝓝 (-ArithmeticElectrostatics.torsionPairing Q
        (fun m => a m / Real.sqrt (m.totient : ℝ)))) := by
  let f : ℕ → ℝ := fun m => a m / Real.sqrt (m.totient : ℝ)
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  let M := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := ArithmeticElectrostatics.torsionPairing Q f
  have hpacket (n : ℕ) :
      (∑ m ∈ Icc 1 Q, f m * ramanujanLagCoefficient m n) = F n := by
    apply sum_congr rfl
    intro m hm
    rw [normalizedRamanujanMode_eq_coefficient (mem_Icc.mp hm).1]
    dsimp only [f]
    ring
  have hmass : (∑ m ∈ Icc 1 Q, (m.totient : ℝ) * f m ^ 2) = M :=
    normalized_coefficient_selfMass Q a
  have hbase : Tendsto (fun N : ℕ =>
      (∑ n ∈ Icc 1 N, F n ^ 2 / (n : ℝ)) - M * Real.log N)
      atTop (𝓝 (Real.eulerMascheroniConstant * M - T)) := by
    have h := tendsto_ramanujanPacket_harmonic_torsion (Icc 1 Q)
      (fun m hm => (mem_Icc.mp hm).1) f
    rw [hmass] at h
    refine h.congr fun N => ?_
    congr 1
    exact sum_congr rfl fun n _ => by rw [hpacket]
  have hlim := hbase.sub (Real.tendsto_harmonic_sub_log.const_mul M)
  have hv : (Real.eulerMascheroniConstant * M - T) - M * Real.eulerMascheroniConstant = -T := by ring
  rw [hv] at hlim
  refine hlim.congr fun N => ?_
  change _ = ∑ n ∈ Icc 1 N, (F n ^ 2 - M) / (n : ℝ)
  rw [centered_packet_harmonic]
  ring

/-- The two-sided large sieve retains all conductor cancellation in the harmonic tail. -/
theorem abs_harmonicGram_quadratic_torsion_remainder {Q : ℕ}
    (hQ : 2 ≤ Q) (N : ℕ) (a : ℕ → ℝ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        (harmonic N : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
        ArithmeticElectrostatics.torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))| ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1)) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let F : ℕ → ℝ := fun n => ∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n
  let M := ∑ m ∈ Icc 1 Q, a m ^ 2
  have hwindow (A K : ℕ) :
      |∑ n ∈ Icc (A + 1) (A + K), (F n ^ 2 - M)| ≤ (Q : ℝ) * ((Q : ℝ) - 1) * M := by
    have hcard : (Icc (A + 1) (A + K)).card = K := by
      rw [Nat.card_Icc]
      omega
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hcard]
    exact CriticalArithmeticCorrelationTheory.abs_ramanujanPacket_window_discrepancy_le hQ a A K
  have h := harmonic_tail_bound_of_windows hwindow (normalized_packet_harmonic_limit Q a) N
  rw [centered_packet_harmonic, sub_neg_eq_add] at h
  exact h.trans_eq (by ring)

/-- The actual finite-horizon harmonic Gram differs from `log N` times identity by a logarithmic operator budget. -/
theorem abs_harmonicGram_sub_log_mass_le {Q : ℕ} (hQ : 2 ≤ Q)
    {N : ℕ} (hN : 1 ≤ N) (a : ℕ → ℝ) :
    |(∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)) -
        Real.log N * (∑ m ∈ Icc 1 Q, a m ^ 2)| ≤
      (|Real.eulerMascheroniConstant| + 4 * Real.log Q + (Real.log 4 + 4) +
        (Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1) + 1 / N) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let A := ∑ n ∈ Icc 1 N,
    (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m n) ^ 2 / (n : ℝ)
  let M := ∑ m ∈ Icc 1 Q, a m ^ 2
  let T := ArithmeticElectrostatics.torsionPairing Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  have hM : 0 ≤ M := sum_nonneg fun m _ => sq_nonneg (a m)
  have hr : |A - (harmonic N : ℝ) * M + T| ≤
      ((Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1)) * M :=
    abs_harmonicGram_quadratic_torsion_remainder hQ N a
  have ht : |T| ≤ (4 * Real.log Q + (Real.log 4 + 4)) * M := by
    simpa only [normalized_coefficient_selfMass] using
      abs_torsionPairing_le_log Q (fun m => a m / Real.sqrt (m.totient : ℝ))
  have hh : |(harmonic N : ℝ) - Real.log N| ≤ |Real.eulerMascheroniConstant| + 1 / N := by
    have h := _root_.HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hN
    calc
      _ = |((harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant) +
          Real.eulerMascheroniConstant| := by congr 1; ring
      _ ≤ _ + |Real.eulerMascheroniConstant| := abs_add_le _ _
      _ ≤ 1 / N + |Real.eulerMascheroniConstant| := add_le_add h le_rfl
      _ = _ := by ring
  change |A - Real.log N * M| ≤ _
  calc
    _ = |(A - (harmonic N : ℝ) * M + T) + ((harmonic N : ℝ) - Real.log N) * M - T| := by
      congr 1
      ring
    _ ≤ |A - (harmonic N : ℝ) * M + T| +
        |((harmonic N : ℝ) - Real.log N) * M| + |T| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ((Q : ℝ) * ((Q : ℝ) - 1) / ((N : ℝ) + 1)) * M +
        (|Real.eulerMascheroniConstant| + 1 / N) * M +
        (4 * Real.log Q + (Real.log 4 + 4)) * M := by
      rw [abs_mul, abs_of_nonneg hM]
      exact add_le_add (add_le_add hr (mul_le_mul_of_nonneg_right hh hM)) ht
    _ = _ := by ring

#print axioms abs_harmonicGram_quadratic_torsion_remainder
#print axioms abs_harmonicGram_sub_log_mass_le

end
end GaloisForLFunctions.SuccessorShellArithmetic
