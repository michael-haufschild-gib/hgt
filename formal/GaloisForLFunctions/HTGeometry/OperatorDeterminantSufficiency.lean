/-
# The sufficiency half of the determinant-completion law, on the operator side

Beside the greedy truncation of a Schatten-`p` operator there is always room -- an orthonormal
family in the orthogonal complement of the finite-dimensional subspace carrying the truncation.
Putting a vanishing micro-spectrum block there produces a finite-rank operator whose power traces
below the order are exactly the prescribed jet coefficients and whose Schatten distance to the
original operator still vanishes.  The order-shift identity then turns the *plain* determinant of
the approximant into `exp(Q)` times its order-`p` regularized determinant, and Schatten continuity
of the regularized determinant finishes the limit.

Main results:
* `hasRankLE_pow_succ`, `opTrace_add_pow_succ_of_orthogonal` — powers of an orthogonal sum.
* `approxNumber_neg`, `schattenNorm_neg` — the Schatten data is even.
* `schattenNorm_greedy_sub_rpow_le` — the greedy error never exceeds the operator in `p`-energy.
* `exists_finiteRank_tendsto_opSchattenDet_one` — **the sufficiency half of `(DC)` on the operator
  side**: finite-rank approximants converging in the Schatten norm whose plain determinants
  converge to `exp(Q)·det_p`.
-/
import GaloisForLFunctions.HTGeometry.BlockOperatorSchatten
import GaloisForLFunctions.HTGeometry.GreedySupportComplement
import GaloisForLFunctions.HTGeometry.TracePowerDetOrderShift
import GaloisForLFunctions.HTGeometry.SchattenFiniteRankDensity
import GaloisForLFunctions.HTGeometry.SpectralDeterminantSufficiency
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.ConnesConsaniTraceClassReduction

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

theorem multiset_sum_eq_finSum_real (S : Multiset ℂ) (f : ℂ → ℝ) :
    (S.map f).sum = ∑ i, f (multisetIndex S i) := by
  conv_lhs => rw [← Multiset.coe_toList S]
  rw [Multiset.map_coe, Multiset.sum_coe]
  have hlist : S.toList.map f
      = List.ofFn (fun i : Fin S.toList.length => f (multisetIndex S i)) := by
    rw [show (fun i : Fin S.toList.length => f (multisetIndex S i)) = f ∘ S.toList.get from rfl,
      ← List.map_ofFn, List.ofFn_get]
  rw [hlist, List.sum_ofFn]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Powers of an orthogonal sum -/

omit [CompleteSpace H] in
theorem hasRankLE_pow_succ {A : H →L[ℂ] H} {a : ℕ} (hA : HasRankLE A a) (k : ℕ) :
    HasRankLE (A ^ (k + 1)) a := by
  obtain ⟨V, hV, hle, hmem⟩ := hA
  refine ⟨V, hV, hle, fun x => ?_⟩
  rw [pow_succ']
  exact hmem _

theorem opTrace_add_pow_succ_of_orthogonal {A B : H →L[ℂ] H} {a b : ℕ}
    (hA : HasRankLE A a) (hB : HasRankLE B b) (hab : A * B = 0) (hba : B * A = 0) (k : ℕ) :
    opTrace ((A + B) ^ (k + 1)) = opTrace (A ^ (k + 1)) + opTrace (B ^ (k + 1)) := by
  rw [add_pow_succ_of_mul_eq_zero hab hba k]
  exact opTrace_add_of_memSchattenClass_one
    (memSchattenClass_one_of_hasRankLE (hasRankLE_pow_succ hA k))
    (memSchattenClass_one_of_hasRankLE (hasRankLE_pow_succ hB k))

/-! ## The Schatten data is even -/

theorem approxNumber_neg (X : H →L[ℂ] H) (n : ℕ) : approxNumber (-X) n = approxNumber X n := by
  have h := approxNumber_smul X (-1 : ℂ) n
  simpa using h

theorem schattenNorm_neg {p : ℝ} (X : H →L[ℂ] H) : schattenNorm p (-X) = schattenNorm p X := by
  rw [schattenNorm, schattenNorm]
  congr 1
  exact tsum_congr fun n => by rw [approxNumber_neg]

theorem memSchattenClass_neg {p : ℝ} {X : H →L[ℂ] H} (h : MemSchattenClass p X) :
    MemSchattenClass p (-X) :=
  h.congr fun n => by rw [approxNumber_neg]

/-! ## The greedy error never exceeds the operator -/

variable {T : H →L[ℂ] H}

theorem tsum_rpow_approxNumber_greedy_le {p : ℝ} (hp : 0 < p) (hcpt : IsCompactOperator T)
    (hT : MemSchattenClass p T) (N : ℕ) :
    (∑' k, approxNumber (T - greedyTrunc T N) k ^ p) ≤ ∑' k, approxNumber T k ^ p := by
  refine (tsum_rpow_approxNumber_sub_greedyTrunc_le hp hcpt hT N).trans ?_
  have hsum : Summable fun n => singVal T n ^ p := summable_singVal_rpow hcpt hT
  have hsplit := hsum.sum_add_tsum_nat_add N
  have hhead : (0 : ℝ) ≤ ∑ i ∈ Finset.range N, singVal T i ^ p :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singVal_nonneg _ _) p
  have hcongr : (∑' k, singVal T (N + k) ^ p) = ∑' k, singVal T (k + N) ^ p :=
    tsum_congr fun k => by rw [Nat.add_comm]
  have htail : (∑' k, singVal T (k + N) ^ p) ≤ ∑' n, singVal T n ^ p := by linarith [hsplit]
  rw [hcongr]
  refine htail.trans (le_of_eq (tsum_congr fun n => ?_))
  rw [approxNumber_eq_singVal hcpt n]

theorem schattenNorm_greedy_sub_rpow_le {p : ℝ} (hp : 0 < p) (hcpt : IsCompactOperator T)
    (hT : MemSchattenClass p T) (N : ℕ) :
    schattenNorm p (greedyTrunc T N - T) ^ p ≤ schattenNorm p T ^ p := by
  rw [schattenNorm_rpow_eq_tsum hp, schattenNorm_rpow_eq_tsum hp]
  have hneg : ∀ k, approxNumber (greedyTrunc T N - T) k = approxNumber (T - greedyTrunc T N) k := by
    intro k
    rw [show greedyTrunc T N - T = -(T - greedyTrunc T N) by abel, approxNumber_neg]
  calc (∑' k, approxNumber (greedyTrunc T N - T) k ^ p)
      = ∑' k, approxNumber (T - greedyTrunc T N) k ^ p := tsum_congr fun k => by rw [hneg k]
    _ ≤ ∑' k, approxNumber T k ^ p := tsum_rpow_approxNumber_greedy_le hp hcpt hT N

/-! ## The sufficiency half of `(DC)` on the operator side -/

set_option maxHeartbeats 2000000 in
/-- **The sufficiency half of `(DC)` on the operator side.**  For every Schatten-`p` operator on an
infinite-dimensional Hilbert space and every jet of degree below `p` with vanishing constant term
there are finite-rank operators converging to it in the Schatten norm whose *plain* determinants
converge to `exp(Q)` times its order-`p` regularized determinant. -/
theorem exists_finiteRank_tendsto_opSchattenDet_one (hH : ¬ FiniteDimensional ℂ H) {p : ℕ}
    (hp : 0 < p) (hT : MemSchattenClass (p : ℝ) T)
    {Q : Polynomial ℂ} (hdeg : Q.natDegree ≤ p - 1) (hQ0 : Q.coeff 0 = 0) :
    ∃ (F : ℕ → H →L[ℂ] H) (C : ℝ), 1 ≤ C ∧
      (∀ n, ∃ N : ℕ, HasRankLE (F n) N) ∧
      (∀ n, MemSchattenClass (p : ℝ) (F n)) ∧
      (∀ n, schattenNorm (p : ℝ) (F n) ≤ C) ∧
      schattenNorm (p : ℝ) T ≤ C ∧
      Tendsto (fun n => schattenNorm (p : ℝ) (F n - T)) atTop (nhds 0) ∧
      (∀ (n : ℕ) (z : ℂ), ‖z‖ * (2 * C) < 1 →
        opSchattenDet 1 (F n) z
          = opSchattenDet p (F n) z * Complex.exp (Polynomial.eval z Q)) ∧
      ∀ z : ℂ, ‖z‖ * (2 * C) < 1 →
        Tendsto (fun n => opSchattenDet 1 (F n) z) atTop
          (nhds (opSchattenDet p T z * Complex.exp (Polynomial.eval z Q))) := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hcpt : IsCompactOperator T := hT.isCompactOperator hpR
  -- the micro-spectrum correcting the greedy truncation at each order
  have hblock : ∀ n : ℕ, ∃ S : Multiset ℂ,
      (∀ k, 1 ≤ k → k ≤ p - 1 → (S.map fun w => w ^ k).sum
        = -(k : ℂ) * Q.coeff k - opTrace (greedyTrunc T n ^ k)) ∧
      ((S.map fun w => ‖w‖ ^ p).sum < 1 / (n + 1 : ℝ)) := fun n =>
    exists_multiset_moment_realization p (p - 1) (by omega)
      (fun k => -(k : ℂ) * Q.coeff k - opTrace (greedyTrunc T n ^ k)) (1 / (n + 1 : ℝ))
      (by positivity)
  choose Sm hSmom hScost using hblock
  -- the room beside the truncation
  have hbeside : ∀ n : ℕ, ∃ e : Fin (Sm n).toList.length → H, Orthonormal ℂ e ∧
      (∀ i, greedyTrunc T n (e i) = 0) ∧ (∀ i x, ⟪e i, greedyTrunc T n x⟫_ℂ = 0) := fun n =>
    exists_orthonormal_beside_greedyTrunc hH T n (Sm n).toList.length
  choose ev hev hev0 hev1 using hbeside
  obtain ⟨Bl, hBl⟩ : ∃ Bl : ℕ → H →L[ℂ] H,
      ∀ n, Bl n = blockOp (ev n) (multisetIndex (Sm n)) := ⟨_, fun n => rfl⟩
  obtain ⟨F, hFe⟩ : ∃ F : ℕ → H →L[ℂ] H, ∀ n, F n = greedyTrunc T n + Bl n := ⟨_, fun n => rfl⟩
  -- ranks
  have hArank : ∀ n, HasRankLE (greedyTrunc T n) n := fun n => hasRankLE_greedyTrunc T n
  have hBrank : ∀ n, HasRankLE (Bl n) (Sm n).toList.length := by
    intro n; rw [hBl n]; exact hasRankLE_blockOp (ev n) (multisetIndex (Sm n))
  have hFrank : ∀ n, HasRankLE (F n) (n + (Sm n).toList.length) := by
    intro n; rw [hFe n]; exact (hArank n).add (hBrank n)
  -- the block is orthogonal to the truncation in both orders
  have hAB : ∀ n, greedyTrunc T n * Bl n = 0 := by
    intro n
    rw [hBl n]
    exact comp_blockOp_eq_zero (greedyTrunc T n) (hev0 n) (multisetIndex (Sm n))
  have hBA : ∀ n, Bl n * greedyTrunc T n = 0 := by
    intro n
    rw [hBl n]
    exact blockOp_comp_eq_zero (greedyTrunc T n) (hev1 n) (multisetIndex (Sm n))
  -- the power traces split, and the block's are the multiset moments
  have htrF : ∀ n k, opTrace (F n ^ (k + 1))
      = opTrace (greedyTrunc T n ^ (k + 1)) + opTrace (Bl n ^ (k + 1)) := by
    intro n k
    rw [hFe n]
    exact opTrace_add_pow_succ_of_orthogonal (hArank n) (hBrank n) (hAB n) (hBA n) k
  have htrB : ∀ n k, opTrace (Bl n ^ (k + 1)) = ((Sm n).map fun w => w ^ (k + 1)).sum := by
    intro n k
    rw [hBl n, blockOp_pow (hev n) (multisetIndex (Sm n)) k,
      opTrace_blockOp (hev n) (fun i => multisetIndex (Sm n) i ^ (k + 1)),
      multiset_sum_eq_finSum (Sm n) (fun w => w ^ (k + 1))]
  -- the low power traces are exactly the prescribed jet
  have hlow : ∀ n k, 1 ≤ k → k ≤ p - 1 → opTrace (F n ^ k) = -(k : ℂ) * Q.coeff k := by
    intro n k hk1 hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [htrF n j, htrB n j, hSmom n (j + 1) hk1 hk2]
    ring
  -- Schatten memberships
  have hBmem : ∀ n, MemSchattenClass (p : ℝ) (Bl n) := fun n =>
    memSchattenClass_of_hasRankLE hpR (hBrank n)
  have hFmem : ∀ n, MemSchattenClass (p : ℝ) (F n) := fun n =>
    memSchattenClass_of_hasRankLE hpR (hFrank n)
  have hATeq : ∀ n, greedyTrunc T n - T = -(T - greedyTrunc T n) := fun n => by abel
  have hATmem : ∀ n, MemSchattenClass (p : ℝ) (greedyTrunc T n - T) := by
    intro n
    rw [hATeq n]
    exact memSchattenClass_neg (memSchattenClass_sub_greedyTrunc hpR hcpt hT n)
  have hFTeq : ∀ n, F n - T = (greedyTrunc T n - T) + Bl n := by
    intro n; rw [hFe n]; abel
  have hDmem : ∀ n, MemSchattenClass (p : ℝ) (F n - T) := by
    intro n
    rw [hFTeq n]
    exact memSchattenClass_add hpR (hATmem n) (hBmem n)
  -- the block energy vanishes
  have hBenergy : ∀ n, schattenNorm (p : ℝ) (Bl n) ^ (p : ℝ) ≤ 1 / (n + 1 : ℝ) := by
    intro n
    rw [hBl n]
    refine (schattenNorm_blockOp_rpow_le (hev n) (multisetIndex (Sm n)) hpR).trans ?_
    have heq : (∑ i, ‖multisetIndex (Sm n) i‖ ^ (p : ℝ))
        = ((Sm n).map fun w => ‖w‖ ^ p).sum := by
      rw [multiset_sum_eq_finSum_real (Sm n) (fun w => ‖w‖ ^ p)]
      exact Finset.sum_congr rfl fun i _ => Real.rpow_natCast _ p
    rw [heq]
    exact (hScost n).le
  have hBtend : Tendsto (fun n => schattenNorm (p : ℝ) (Bl n)) atTop (nhds 0) := by
    have hmaj : Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) ^ (1 / (p : ℝ))) atTop (nhds 0) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / (p : ℝ))) 0 :=
        Real.continuousAt_rpow_const 0 (1 / (p : ℝ)) (Or.inr (by positivity))
      have hcomp := hcont.tendsto.comp h0
      rwa [Real.zero_rpow (by positivity : (1 : ℝ) / (p : ℝ) ≠ 0)] at hcomp
    refine squeeze_zero (fun n => schattenNorm_nonneg _ _) (fun n => ?_) hmaj
    have hnn : (0 : ℝ) ≤ schattenNorm (p : ℝ) (Bl n) := schattenNorm_nonneg _ _
    calc schattenNorm (p : ℝ) (Bl n)
        = (schattenNorm (p : ℝ) (Bl n) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
          rw [← Real.rpow_mul hnn, mul_one_div, div_self hpR.ne', Real.rpow_one]
      _ ≤ (1 / ((n : ℝ) + 1)) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (Real.rpow_nonneg hnn _) (hBenergy n) (by positivity)
  have hATtend : Tendsto (fun n => schattenNorm (p : ℝ) (greedyTrunc T n - T)) atTop (nhds 0) := by
    refine (tendsto_schattenNorm_sub_greedyTrunc hpR hcpt hT).congr fun N => ?_
    rw [hATeq N, schattenNorm_neg]
  have hDtend : Tendsto (fun n => schattenNorm (p : ℝ) (F n - T)) atTop (nhds 0) := by
    refine (tendsto_schattenNorm_add hpR hATmem hBmem hATtend hBtend).congr fun n => ?_
    rw [hFTeq n]
  -- the uniform Schatten bound
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 ^ ((p : ℝ) + 1) *
      (2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1)
        + schattenNorm (p : ℝ) T ^ (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max 1 (K ^ (1 / (p : ℝ))) := ⟨_, rfl⟩
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have htwo : (0 : ℝ) ≤ 2 ^ ((p : ℝ) + 1) := Real.rpow_nonneg (by norm_num) _
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hK]
    have hTp : (0 : ℝ) ≤ schattenNorm (p : ℝ) T ^ (p : ℝ) :=
      Real.rpow_nonneg (schattenNorm_nonneg _ _) _
    exact mul_nonneg htwo (by nlinarith [mul_nonneg htwo (by linarith :
      (0:ℝ) ≤ schattenNorm (p : ℝ) T ^ (p : ℝ) + 1)])
  have hCA : ∀ n, schattenNorm (p : ℝ) (F n) ≤ C := by
    intro n
    have hBone : schattenNorm (p : ℝ) (Bl n) ^ (p : ℝ) ≤ 1 := by
      refine (hBenergy n).trans ?_
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hATle : schattenNorm (p : ℝ) (greedyTrunc T n - T) ^ (p : ℝ)
        ≤ schattenNorm (p : ℝ) T ^ (p : ℝ) := schattenNorm_greedy_sub_rpow_le hpR hcpt hT n
    have hDle : schattenNorm (p : ℝ) (F n - T) ^ (p : ℝ)
        ≤ 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1) := by
      have h := schattenNorm_add_rpow_le hpR (hATmem n) (hBmem n)
      rw [← hFTeq n] at h
      nlinarith [h, hATle, hBone]
    have hFle : schattenNorm (p : ℝ) (F n) ^ (p : ℝ) ≤ K := by
      have h := schattenNorm_add_rpow_le hpR (hDmem n) hT
      rw [show F n - T + T = F n by abel] at h
      rw [hK]
      nlinarith [h, hDle]
    have hnn : (0 : ℝ) ≤ schattenNorm (p : ℝ) (F n) := schattenNorm_nonneg _ _
    calc schattenNorm (p : ℝ) (F n)
        = (schattenNorm (p : ℝ) (F n) ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
          rw [← Real.rpow_mul hnn, mul_one_div, div_self hpR.ne', Real.rpow_one]
      _ ≤ K ^ (1 / (p : ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hFle (by positivity)
      _ ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hB1 : (1 : ℝ) ≤ 2 * C := by linarith
  have hCT : schattenNorm (p : ℝ) T ≤ C := by
    have hnn : (0 : ℝ) ≤ schattenNorm (p : ℝ) T := schattenNorm_nonneg _ _
    have hcast : ((p : ℝ) + 1) = ((p + 1 : ℕ) : ℝ) := by push_cast; ring
    have h2 : (1 : ℝ) ≤ 2 ^ ((p : ℝ) + 1) := by
      rw [hcast, Real.rpow_natCast]
      exact one_le_pow₀ (by norm_num)
    have hTp : (0 : ℝ) ≤ schattenNorm (p : ℝ) T ^ (p : ℝ) := Real.rpow_nonneg hnn _
    have hTpK : schattenNorm (p : ℝ) T ^ (p : ℝ) ≤ K := by
      rw [hK]
      have hx : (0 : ℝ) ≤ schattenNorm (p : ℝ) T ^ (p : ℝ) + 1 := by linarith
      have hA1 : schattenNorm (p : ℝ) T ^ (p : ℝ) + 1
          ≤ 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h2) hx]
      have hy : (0 : ℝ) ≤ 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1)
          + schattenNorm (p : ℝ) T ^ (p : ℝ) := by linarith
      have hA2 : 2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1)
            + schattenNorm (p : ℝ) T ^ (p : ℝ)
          ≤ 2 ^ ((p : ℝ) + 1) * (2 ^ ((p : ℝ) + 1) * (schattenNorm (p : ℝ) T ^ (p : ℝ) + 1)
            + schattenNorm (p : ℝ) T ^ (p : ℝ)) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h2) hy]
      linarith
    calc schattenNorm (p : ℝ) T = (schattenNorm (p : ℝ) T ^ (p : ℝ)) ^ (1 / (p : ℝ)) := by
          rw [← Real.rpow_mul hnn, mul_one_div, div_self hpR.ne', Real.rpow_one]
      _ ≤ K ^ (1 / (p : ℝ)) := Real.rpow_le_rpow hTp hTpK (by positivity)
      _ ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hshift : ∀ (n : ℕ) (z : ℂ), ‖z‖ * (2 * C) < 1 → opSchattenDet 1 (F n) z
      = opSchattenDet p (F n) z * Complex.exp (Polynomial.eval z Q) := by
    intro n z hz
    have hbound : ∀ k : ℕ, ‖(fun m => opTrace (F n ^ m)) (k + p)‖
        ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
      fun k => norm_opTrace_pow_add_le hp (hFmem n) hC1 (hCA n) k
    have hord := tracePowerDet_order_shift (τ := fun m => opTrace (F n ^ m)) hp hB1 hbound hz
      (q := 1) hp
    have hterm : ∀ m ∈ Finset.Ico 1 p,
        tracePowerTerm (fun m => opTrace (F n ^ m)) z m = -(Q.coeff m * z ^ m) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hmne : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      show z ^ m / (m : ℂ) * opTrace (F n ^ m) = -(Q.coeff m * z ^ m)
      rw [hlow n m hm.1 (by omega)]
      field_simp
    have hhead : (∑ m ∈ Finset.Ico 1 p, tracePowerTerm (fun m => opTrace (F n ^ m)) z m)
        = -Polynomial.eval z Q := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, eval_eq_sum_shift hp hdeg hQ0 z,
        Finset.sum_Ico_eq_sum_range]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_comm]
    rw [opSchattenDet_eq_tracePowerDet, opSchattenDet_eq_tracePowerDet, hord, hhead, neg_neg]
  refine ⟨F, C, hC1, fun n => ⟨n + (Sm n).toList.length, hFrank n⟩, hFmem, hCA, hCT, hDtend,
    hshift, ?_⟩
  intro z hz
  have hdetp : Tendsto (fun n => opSchattenDet p (F n) z) atTop (nhds (opSchattenDet p T z)) :=
    tendsto_opSchattenDet_of_tendsto_schattenNorm hp hFmem hT hDmem hC1 hCA hDtend hz
  exact (hdetp.mul_const (Complex.exp (Polynomial.eval z Q))).congr fun n => (hshift n z hz).symm

end

end GaloisForLFunctions.HTGeometry
