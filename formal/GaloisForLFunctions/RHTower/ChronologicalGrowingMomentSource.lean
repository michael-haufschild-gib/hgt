import GaloisForLFunctions.RHTower.ChronologicalHalfTailGram
import GaloisForLFunctions.RHTower.ChronologicalMobiusHalfPrefixMoments
import GaloisForLFunctions.RHTower.ChronologicalZeroChargeTailBounds
import GaloisForLFunctions.RHTower.ChronologicalBoseKernelJets
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# An unconditional bounded source with increasing matched moments

Fix `m ≥ 0`, `N ≥ 1`, `M = ⌊N/2⌋` and the moment vector `v(x) = (x⁻¹, 1, x, x³, …, x^{2m-1})`.
With the tail Gram matrix `G_N = Σ_{M < k ≤ N} v(k/N) v(k/N)ᵀ`, the scaled target
`τ = (0, -2, -(2j/B_{2j}) N^{-(2j-1)})` and `b_N = τ - Σ_{k ≤ M} μ(k) v(k/N)`, put
`c_N = G_N⁻¹ b_N` and assign the tail `a_k = c_N · v(k/N)`.  When `G_N` is invertible the row
`a_k = μ(k)` (`k ≤ M`), `a_k = c_N · v(k/N)` (`M < k ≤ N`) satisfies exactly

  `Σ a_k/k = 0`,  `Σ a_k = -2`,  `Σ a_k k^{2j-1} = -2j/B_{2j}` (`1 ≤ j ≤ m`).

For fixed `m`, `N⁻¹ G_N` is uniformly coercive and `b_N/N → 0` (prime number theorem), so
`c_N → 0` and the tail coefficients tend to zero uniformly; the row is admissible
(`G_N` invertible, tail in `[-1, 1]`) for all large `N`.  Taking at each `N` the largest admissible
`m ≤ N` gives unit-bounded rows with `m_N → ∞`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology Moebius

noncomputable section

namespace RHTower

/-! ### The construction -/

/-- The moment vector `v(k/N)`. -/
def gmVec (m N k : ℕ) (i : Fin (m + 2)) : ℝ := ((k : ℝ) / N) ^ gmExp m i

/-- The tail Gram matrix `G_N = Σ_{M < k ≤ N} v(k/N) v(k/N)ᵀ`. -/
def gmGram (m N : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  fun i j => ∑ k ∈ Finset.Ioc (N / 2) N, gmVec m N k i * gmVec m N k j

/-- The scaled moment targets: harmonic charge `0`, constant `-2`, odd jets
`-(2j/B_{2j}) N^{-(2j-1)}` at `e_i = 2j - 1`. -/
def gmTarget (m N : ℕ) (i : Fin (m + 2)) : ℝ :=
  if (i : ℕ) = 0 then 0 else if (i : ℕ) = 1 then -2 else
    -((2 * ((i : ℕ) - 1) : ℕ) / (bernoulli (2 * ((i : ℕ) - 1)) : ℝ)) * (N : ℝ) ^ (-gmExp m i)

/-- The right-hand side `b_N = τ - Σ_{k ≤ M} μ(k) v(k/N)`. -/
def gmRhs (m N : ℕ) (i : Fin (m + 2)) : ℝ :=
  gmTarget m N i - ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * gmVec m N k i

/-- The least-squares coefficients `c_N = G_N⁻¹ b_N`. -/
def gmCoeff (m N : ℕ) : Fin (m + 2) → ℝ := (gmGram m N)⁻¹.mulVec (gmRhs m N)

/-- The tail coefficient `c_N · v(k/N)`. -/
def gmTail (m N k : ℕ) : ℝ := ∑ i, gmCoeff m N i * gmVec m N k i

/-- The row: Möbius head through `⌊N/2⌋`, Gram tail through `N`, zero beyond. -/
def gmRow (m N k : ℕ) : ℝ :=
  if k = 0 then 0 else if k ≤ N / 2 then ((μ k : ℤ) : ℝ) else if k ≤ N then gmTail m N k else 0

/-- Admissibility of the order `m` at `N`: invertible Gram matrix and a unit-bounded tail. -/
def GmAdmissible (N m : ℕ) : Prop :=
  IsUnit (gmGram m N).det ∧ ∀ k ∈ Finset.Ioc (N / 2) N, |gmTail m N k| ≤ 1

/-! ### Exact moments of admissible rows -/

theorem gmGram_mulVec (m N : ℕ) (c : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    (gmGram m N).mulVec c i = ∑ k ∈ Finset.Ioc (N / 2) N, gmVec m N k i *
      ∑ j, c j * gmVec m N k j := by
  simp only [Matrix.mulVec, dotProduct, gmGram, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

theorem gmGram_mulVec_gmCoeff {m N : ℕ} (h : IsUnit (gmGram m N).det) :
    (gmGram m N).mulVec (gmCoeff m N) = gmRhs m N := by
  rw [gmCoeff, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]

/-- **The scaled moments of an admissible row are the targets.** -/
theorem sum_gmRow_mul_gmVec {m N : ℕ} (h : IsUnit (gmGram m N).det) (i : Fin (m + 2)) :
    ∑ k ∈ Finset.Ioc 0 N, gmRow m N k * gmVec m N k i = gmTarget m N i := by
  have hMN : N / 2 ≤ N := Nat.div_le_self N 2
  rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le (N / 2)) hMN]
  have hhead : ∑ k ∈ Finset.Ioc 0 (N / 2), gmRow m N k * gmVec m N k i =
      ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * gmVec m N k i :=
    Finset.sum_congr rfl fun k hk => by
      obtain ⟨hk0, hkM⟩ := Finset.mem_Ioc.mp hk
      rw [gmRow, if_neg hk0.ne', if_pos hkM]
  have htail : ∑ k ∈ Finset.Ioc (N / 2) N, gmRow m N k * gmVec m N k i =
      (gmGram m N).mulVec (gmCoeff m N) i := by
    rw [gmGram_mulVec]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkM, hkN⟩ := Finset.mem_Ioc.mp hk
    rw [gmRow, if_neg (by omega), if_neg (by omega), if_pos hkN, gmTail]
    ring
  rw [hhead, htail, gmGram_mulVec_gmCoeff h, gmRhs]
  ring

theorem gmExp_zero (m : ℕ) : gmExp m ⟨0, by omega⟩ = -1 := by simp [gmExp]

theorem gmExp_one (m : ℕ) : gmExp m ⟨1, by omega⟩ = 0 := by simp [gmExp]

theorem gmExp_succ {m j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ m) :
    gmExp m ⟨j + 1, by omega⟩ = ((2 * j - 1 : ℕ) : ℤ) := by
  simp only [gmExp]
  rw [if_neg (by omega), if_neg (by omega)]
  push_cast [show 1 ≤ 2 * j by omega]
  ring

/-- **The exact constraints of an admissible row.** -/
theorem gmRow_moments {m N : ℕ} (hN : 0 < N) (h : IsUnit (gmGram m N).det) :
    chronologicalHarmonicCharge (gmRow m N) N = 0 ∧
      ∑ k ∈ Finset.Ioc 0 N, gmRow m N k = -2 ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ m → ∑ k ∈ Finset.Ioc 0 N, gmRow m N k * (k : ℝ) ^ (2 * j - 1) =
        -(2 * j) / (bernoulli (2 * j) : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨?_, ?_, fun j hj hjm => ?_⟩
  · have h0 := sum_gmRow_mul_gmVec h ⟨0, by omega⟩
    simp only [gmVec, gmExp_zero, gmTarget] at h0
    rw [chronologicalHarmonicCharge]
    have hrw : ∀ k ∈ Finset.Ioc 0 N, gmRow m N k * ((k : ℝ) / N) ^ (-1 : ℤ) =
        N * (gmRow m N k / k) := fun k hk => by
      have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hk).1.ne'
      rw [zpow_neg_one, inv_div]; field_simp
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum] at h0
    exact (mul_eq_zero.mp h0).resolve_left hNr.ne'
  · have h1 := sum_gmRow_mul_gmVec h ⟨1, by omega⟩
    simp only [gmVec, gmExp_one, zpow_zero, mul_one, gmTarget] at h1
    simpa using h1
  · have hi := sum_gmRow_mul_gmVec h ⟨j + 1, by omega⟩
    simp only [gmVec, gmExp_succ hj hjm, zpow_natCast, gmTarget] at hi
    rw [if_neg (by omega), if_neg (by omega), show j + 1 - 1 = j by omega] at hi
    have hNp : (N : ℝ) ^ (2 * j - 1) ≠ 0 := pow_ne_zero _ hNr.ne'
    have hrw : ∀ k ∈ Finset.Ioc 0 N, gmRow m N k * ((k : ℝ) / N) ^ (2 * j - 1) =
        (gmRow m N k * (k : ℝ) ^ (2 * j - 1)) / (N : ℝ) ^ (2 * j - 1) := fun k _ => by
      rw [div_pow]; ring
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_div, zpow_neg, zpow_natCast,
      div_eq_iff hNp] at hi
    rw [hi]
    push_cast
    field_simp

/-! ### Eventual admissibility of each fixed order -/

theorem Ioc_filter_half (N : ℕ) :
    (Finset.Ioc 0 N).filter (fun k : ℕ => N / 2 < k) = Finset.Ioc (N / 2) N := by
  ext k; simp only [Finset.mem_filter, Finset.mem_Ioc]; omega

theorem gmGram_eq (m N : ℕ) (hN : 0 < N) (i j : Fin (m + 2)) :
    gmGram m N i j = N * gmGramDisc m N i j := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [gmGramDisc, ← mul_assoc, mul_one_div_cancel hNr, one_mul, ← Finset.sum_filter,
    Ioc_filter_half, gmGram]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : ((k : ℝ) / N) ≠ 0 := div_ne_zero (by
    exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hk).1).ne') hNr
  rw [gmVec, gmVec, zpow_add₀ hk]

theorem dotProduct_gmGram_mulVec (m N : ℕ) (hN : 0 < N) (c : Fin (m + 2) → ℝ) :
    ∑ i, c i * (gmGram m N).mulVec c i = N * gramQuadForm (gmGramDisc m N) c := by
  simp only [Matrix.mulVec, dotProduct, gmGram_eq m N hN, gramQuadForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem abs_gmVec_le {m N k : ℕ} (hk : k ∈ Finset.Ioc (N / 2) N) (i : Fin (m + 2)) :
    |gmVec m N k i| ≤ 2 := by
  obtain ⟨hkM, hkN⟩ := Finset.mem_Ioc.mp hk
  have hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx1 : (k : ℝ) / N ≤ 1 := (div_le_one hNr).mpr (by exact_mod_cast hkN)
  have hxh : (1 / 2 : ℝ) ≤ (k : ℝ) / N := by
    rw [le_div_iff₀ hNr]
    have : (N : ℝ) < 2 * k := by
      have := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp hkM
      exact_mod_cast (by omega : N < 2 * k)
    linarith
  have hx0 : (0 : ℝ) < (k : ℝ) / N := by linarith
  rw [gmVec, abs_of_pos (zpow_pos hx0 _)]
  calc ((k : ℝ) / N) ^ gmExp m i ≤ ((k : ℝ) / N) ^ (-1 : ℤ) :=
        zpow_le_zpow_right_of_le_one₀ hx0 hx1 (gmExp_ge m i)
    _ ≤ 2 := by
        rw [zpow_neg_one, inv_le_comm₀ hx0 (by norm_num)]; linarith

/-- **Coercivity and the scaled inverse bound.**  For all large `N` the Gram matrix is invertible
and `N G_N⁻¹` is bounded: `√(Σ ((G_N⁻¹ y)ᵢ)²) ≤ √(Σ yᵢ²)/(λN)` for every `y`. -/
theorem exists_gmGram_inverse_bound (m : ℕ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → IsUnit (gmGram m N).det ∧
      ∀ y : Fin (m + 2) → ℝ, Real.sqrt (∑ i, ((gmGram m N)⁻¹.mulVec y i) ^ 2) ≤
        Real.sqrt (∑ i, y i ^ 2) / (lam * N) := by
  obtain ⟨lam, hlam, N₀, hQ⟩ := exists_gmGramDisc_coercive m
  refine ⟨lam, hlam, N₀ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hcoer : ∀ c : Fin (m + 2) → ℝ,
      lam * N * ∑ i, c i ^ 2 ≤ ∑ i, c i * (gmGram m N).mulVec c i := by
    intro c
    rw [dotProduct_gmGram_mulVec m N hNpos]
    have := hQ N (by omega) c
    nlinarith
  have hdet : IsUnit (gmGram m N).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : (gmGram m N).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hc := hcoer (x - y)
    rw [h0] at hc
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hc
    have hsum : ∑ i, (x - y) i ^ 2 = 0 := by
      have hnn : 0 ≤ ∑ i, (x - y) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      nlinarith [mul_pos hlam hNr]
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ((x - y) j))).mp hsum i
      (Finset.mem_univ i)
    exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  refine ⟨hdet, fun y => ?_⟩
  set c := (gmGram m N)⁻¹.mulVec y with hc
  have hGc : (gmGram m N).mulVec c = y := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hcs : lam * N * ∑ i, c i ^ 2 ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
    refine (hcoer c).trans ?_
    rw [hGc]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hS : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [le_div_iff₀ (by positivity)]
  rcases (Real.sqrt_nonneg (∑ i, c i ^ 2)).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have h1 : Real.sqrt (∑ i, c i ^ 2) * (lam * N * Real.sqrt (∑ i, c i ^ 2)) ≤
        Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
      calc Real.sqrt (∑ i, c i ^ 2) * (lam * N * Real.sqrt (∑ i, c i ^ 2))
          = lam * N * (Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, c i ^ 2)) := by ring
        _ = lam * N * ∑ i, c i ^ 2 := by rw [Real.mul_self_sqrt hS]
        _ ≤ _ := hcs
    have := le_of_mul_le_mul_left h1 hpos
    linarith

/-- **Coercivity and the coefficient bound.**  For all large `N` the Gram matrix is invertible and
`√(Σ cᵢ²) ≤ √(Σ bᵢ²)/(λN)`. -/
theorem exists_gmGram_coercive (m : ℕ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      IsUnit (gmGram m N).det ∧
        Real.sqrt (∑ i, gmCoeff m N i ^ 2) ≤ Real.sqrt (∑ i, gmRhs m N i ^ 2) / (lam * N) := by
  obtain ⟨lam, hlam, N₀, h⟩ := exists_gmGram_inverse_bound m
  exact ⟨lam, hlam, N₀, fun N hN => ⟨(h N hN).1, (h N hN).2 (gmRhs m N)⟩⟩

/-- **The scaled Gram matrices converge entrywise** to `∫_{1/2}^1 v vᵀ`. -/
theorem tendsto_gmGramDisc (m : ℕ) (i j : Fin (m + 2)) :
    Tendsto (fun N : ℕ => gmGramDisc m N i j) atTop (𝓝 (gmGramLim m i j)) := by
  obtain ⟨C, hC⟩ := exists_abs_halfTailSum_zpow_sub_le (gmExp m i + gmExp m j)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (|C| / ε)
  refine ⟨N₁ + 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  rw [Real.dist_eq]
  refine lt_of_le_of_lt ((hC N hNpos).trans (div_le_div_of_nonneg_right (le_abs_self C)
    hNr.le)) ?_
  rw [div_lt_iff₀ hNr]
  have : |C| / ε < N := hN₁.trans (by exact_mod_cast (by omega : N₁ < N))
  rw [div_lt_iff₀ hε] at this
  linarith

/-- **The scaled right-hand side tends to zero** (prime number theorem). -/
theorem tendsto_gmRhs_div (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun N : ℕ => gmRhs m N i / N) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsplit : ∀ N : ℕ, gmRhs m N i / N = gmTarget m N i * (1 / N) -
      (1 / (N : ℝ)) * ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * gmVec m N k i := by
    intro N; rw [gmRhs]; ring
  simp only [hsplit]
  rw [show (0 : ℝ) = 0 - 0 by ring]
  obtain ⟨i, hi⟩ := i
  rcases i with _ | _ | j
  · -- harmonic channel
    refine Tendsto.sub (by simp [gmTarget]) ?_
    refine tendsto_halfPrefix_moebius_harmonic.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (Finset.mem_Ioc.mp hk).1.ne'
    rw [gmVec, gmExp_zero, zpow_neg_one, inv_div]; field_simp
  · -- constant channel
    refine Tendsto.sub ?_ ?_
    · simpa [gmTarget] using hinv.const_mul (-2)
    · have he1 : gmExp m ⟨0 + 1, hi⟩ = 0 := by simp [gmExp]
      refine (tendsto_halfPrefix_moebius_pow 0).congr fun N => ?_
      simp only [gmVec, he1, zpow_zero, pow_zero]
  · -- odd jet channels, `e = 2(j+1) - 1`
    have hj1 : 1 ≤ j + 1 := by omega
    have hjm : j + 1 ≤ m := by omega
    have he := gmExp_succ (m := m) hj1 hjm
    set B : ℝ := |((2 * (j + 1) : ℕ) : ℝ) / (bernoulli (2 * (j + 1)) : ℝ)| with hB
    refine Tendsto.sub ?_ ?_
    · have hbound : ∀ N : ℕ, 0 < N → |gmTarget m N ⟨j + 2, hi⟩ * (1 / N)| ≤ B * (1 / N) := by
        intro N hN
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
        simp only [gmTarget]
        rw [if_neg (by omega), if_neg (by omega), show j + 2 - 1 = j + 1 by omega,
          show (⟨j + 2, hi⟩ : Fin (m + 2)) = ⟨j + 1 + 1, by omega⟩ from rfl, he, abs_mul,
          abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_of_le_one_right (abs_nonneg _) ?_
        rw [abs_of_pos (zpow_pos (by positivity) _), zpow_neg, zpow_natCast]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hNr)
      have hlim : Tendsto (fun N : ℕ => B * (1 / (N : ℝ))) atTop (𝓝 0) := by
        simpa using hinv.const_mul B
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Real.norm_eq_abs]; exact hbound N hN
    · have he' : gmExp m ⟨j + 2, hi⟩ = ((2 * (j + 1) - 1 : ℕ) : ℤ) := he
      refine (tendsto_halfPrefix_moebius_pow (2 * (j + 1) - 1)).congr fun N => ?_
      simp only [gmVec, he', zpow_natCast]

/-- **For each fixed order the tail coefficients tend to zero uniformly.** -/
theorem eventually_abs_gmTail_le (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, IsUnit (gmGram m N).det ∧
      ∀ k ∈ Finset.Ioc (N / 2) N, |gmTail m N k| ≤ ε := by
  obtain ⟨lam, hlam, N₀, hco⟩ := exists_gmGram_coercive m
  have hsum : Tendsto (fun N : ℕ => ∑ i, (gmRhs m N i / N) ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (s := Finset.univ)
      (fun i _ => (tendsto_gmRhs_div m i).pow 2)
    simpa using this
  have hsqrt := hsum.sqrt
  rw [Real.sqrt_zero] at hsqrt
  set K : ℝ := 2 * Real.sqrt (m + 2) / lam with hK
  have hK0 : 0 < K := by positivity
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 0,
    hsqrt.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / K))] with N hN hNpos hsmall
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨hdet, hcb⟩ := hco N hN
  refine ⟨hdet, fun k hk => ?_⟩
  have hscale : Real.sqrt (∑ i, gmRhs m N i ^ 2) / (lam * N) =
      Real.sqrt (∑ i, (gmRhs m N i / N) ^ 2) / lam := by
    have : ∑ i, (gmRhs m N i / N) ^ 2 = (∑ i, gmRhs m N i ^ 2) / (N : ℝ) ^ 2 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [div_pow]
    rw [this, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hNr.le]
    field_simp
  rw [hscale] at hcb
  have hl1 : ∑ i, |gmCoeff m N i| ≤ Real.sqrt (m + 2) * Real.sqrt (∑ i, gmCoeff m N i ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i : Fin (m + 2) => |gmCoeff m N i|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.le_sqrt_of_sq_le ?_
    exact_mod_cast h
  calc |gmTail m N k| ≤ ∑ i, |gmCoeff m N i| * 2 := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_gmVec_le hk i) (abs_nonneg _)
    _ = 2 * ∑ i, |gmCoeff m N i| := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ 2 * (Real.sqrt (m + 2) * (Real.sqrt (∑ i, (gmRhs m N i / N) ^ 2) / lam)) := by
        gcongr
        exact hl1.trans (mul_le_mul_of_nonneg_left hcb (Real.sqrt_nonneg _))
    _ = K * Real.sqrt (∑ i, (gmRhs m N i / N) ^ 2) := by rw [hK]; ring
    _ ≤ K * (ε / K) := mul_le_mul_of_nonneg_left hsmall.le hK0.le
    _ = ε := by field_simp

/-- **Every fixed order is eventually admissible.** -/
theorem eventually_gmAdmissible (m : ℕ) : ∀ᶠ N : ℕ in atTop, GmAdmissible N m :=
  eventually_abs_gmTail_le m one_pos

/-- **The Gram tail is the unique least-squares solution.**  Every tail with the same scaled
moments differs from the Gram tail by a vector orthogonal to the sampled moment columns, so
`Σ a'_k² = Σ a_k² + Σ (a'_k - a_k)²`. -/
theorem sum_sq_tail_eq_add {m N : ℕ} (h : IsUnit (gmGram m N).det) (a' : ℕ → ℝ)
    (ha' : ∀ i, ∑ k ∈ Finset.Ioc (N / 2) N, a' k * gmVec m N k i = gmRhs m N i) :
    ∑ k ∈ Finset.Ioc (N / 2) N, a' k ^ 2 = ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k ^ 2 +
      ∑ k ∈ Finset.Ioc (N / 2) N, (a' k - gmTail m N k) ^ 2 := by
  have hcross : ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k * (a' k - gmTail m N k) = 0 := by
    have hGc : ∀ i, ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k * gmVec m N k i = gmRhs m N i := by
      intro i
      rw [← gmGram_mulVec_gmCoeff h, gmGram_mulVec]
      exact Finset.sum_congr rfl fun k _ => by rw [gmTail]; ring
    set d : ℕ → ℝ := fun k => a' k - gmTail m N k with hd
    have horth : ∀ i, ∑ k ∈ Finset.Ioc (N / 2) N, d k * gmVec m N k i = 0 := by
      intro i
      simp only [hd, sub_mul, Finset.sum_sub_distrib, ha', hGc, sub_self]
    calc ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k * d k
        = ∑ i, gmCoeff m N i * ∑ k ∈ Finset.Ioc (N / 2) N, d k * gmVec m N k i := by
          simp only [gmTail, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by simp [horth]
  have hexp : ∀ k, a' k ^ 2 = gmTail m N k ^ 2 + 2 * (gmTail m N k * (a' k - gmTail m N k)) +
      (a' k - gmTail m N k) ^ 2 := fun k => by ring
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hcross, mul_zero, add_zero]

/-- Minimality and uniqueness of the least-squares tail. -/
theorem gmTail_leastSquares {m N : ℕ} (h : IsUnit (gmGram m N).det) (a' : ℕ → ℝ)
    (ha' : ∀ i, ∑ k ∈ Finset.Ioc (N / 2) N, a' k * gmVec m N k i = gmRhs m N i) :
    ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k ^ 2 ≤ ∑ k ∈ Finset.Ioc (N / 2) N, a' k ^ 2 ∧
      (∑ k ∈ Finset.Ioc (N / 2) N, a' k ^ 2 = ∑ k ∈ Finset.Ioc (N / 2) N, gmTail m N k ^ 2 →
        ∀ k ∈ Finset.Ioc (N / 2) N, a' k = gmTail m N k) := by
  have heq := sum_sq_tail_eq_add h a' ha'
  have hnn : 0 ≤ ∑ k ∈ Finset.Ioc (N / 2) N, (a' k - gmTail m N k) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨by linarith, fun hE k hk => ?_⟩
  have h0 : ∑ k ∈ Finset.Ioc (N / 2) N, (a' k - gmTail m N k) ^ 2 = 0 := by linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (a' j - gmTail m N j)).mp h0 k hk
  exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

/-- **The least-squares coefficients tend to zero** for each fixed order. -/
theorem tendsto_gmCoeff (m : ℕ) :
    Tendsto (fun N : ℕ => Real.sqrt (∑ i, gmCoeff m N i ^ 2)) atTop (𝓝 0) := by
  obtain ⟨lam, hlam, N₀, hco⟩ := exists_gmGram_coercive m
  have hsum : Tendsto (fun N : ℕ => Real.sqrt (∑ i, (gmRhs m N i / N) ^ 2) / lam)
      atTop (𝓝 0) := by
    have := tendsto_finsetSum (s := Finset.univ) (fun i _ => (tendsto_gmRhs_div m i).pow 2)
    simpa using (this.sqrt).div_const lam
  refine squeeze_zero' (Eventually.of_forall fun N => Real.sqrt_nonneg _) ?_ hsum
  filter_upwards [eventually_ge_atTop N₀, eventually_gt_atTop 0] with N hN hNpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  refine (hco N hN).2.trans_eq ?_
  have : ∑ i, (gmRhs m N i / N) ^ 2 = (∑ i, gmRhs m N i ^ 2) / (N : ℝ) ^ 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by rw [div_pow]
  rw [this, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hNr.le]
  field_simp

/-! ### The diagonal order and the source -/

open Classical in
/-- The diagonal order `m_N`: the largest admissible `m ≤ N` (`0` if there is none). -/
def gmOrder (N : ℕ) : ℕ := Nat.findGreatest (fun m => GmAdmissible N m) N

open Classical in
/-- **The growing-jet source.** The admissible row of order `m_N`, or the zero row if the order
`m_N` is not admissible (which happens for only finitely many `N`). -/
def growingMomentSource (N k : ℕ) : ℝ :=
  if GmAdmissible N (gmOrder N) then gmRow (gmOrder N) N k else 0

theorem abs_gmRow_le {m N : ℕ} (h : GmAdmissible N m) (k : ℕ) : |gmRow m N k| ≤ 1 := by
  unfold gmRow
  split_ifs with h0 hM hN
  · simp
  · exact_mod_cast abs_moebius_le_one
  · exact h.2 k (Finset.mem_Ioc.mpr ⟨by omega, hN⟩)
  · simp

/-- **Unit coefficient budget.** -/
theorem abs_growingMomentSource_le (N k : ℕ) : |growingMomentSource N k| ≤ 1 := by
  classical
  unfold growingMomentSource
  split_ifs with h
  · exact abs_gmRow_le h k
  · simp

/-- **The matched order grows without bound.** -/
theorem tendsto_gmOrder : Tendsto gmOrder atTop atTop := by
  classical
  refine tendsto_atTop.mpr fun m => ?_
  filter_upwards [eventually_gmAdmissible m, eventually_ge_atTop m] with N hA hmN
  exact Nat.le_findGreatest hmN hA

theorem eventually_gmAdmissible_gmOrder : ∀ᶠ N : ℕ in atTop, GmAdmissible N (gmOrder N) := by
  classical
  filter_upwards [eventually_gmAdmissible 0] with N hA
  exact Nat.findGreatest_spec (Nat.zero_le N) hA

theorem eventually_growingMomentSource_eq :
    ∀ᶠ N : ℕ in atTop, growingMomentSource N = gmRow (gmOrder N) N ∧
      GmAdmissible N (gmOrder N) := by
  classical
  filter_upwards [eventually_gmAdmissible_gmOrder] with N hA
  exact ⟨funext fun k => by rw [growingMomentSource, if_pos hA], hA⟩

/-- **An unconditional bounded source with increasing matched moments.**  Unit-bounded rows with
`m_N → ∞` such that, for all large `N`, the row carries the exact Möbius prefix through `⌊N/2⌋`,
zero harmonic charge, total mass `-2`, and the odd moments `Σ a_k k^{2j-1} = -2j/B_{2j}` for
`1 ≤ j ≤ m_N`. -/
theorem growingMomentSource_spec :
    (∀ N k, |growingMomentSource N k| ≤ 1) ∧ Tendsto gmOrder atTop atTop ∧
      ∀ᶠ N : ℕ in atTop,
        (∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → growingMomentSource N k = μ k) ∧
        chronologicalHarmonicCharge (growingMomentSource N) N = 0 ∧
        ∑ k ∈ Finset.Ioc 0 N, growingMomentSource N k = -2 ∧
        ∀ j : ℕ, 1 ≤ j → j ≤ gmOrder N →
          ∑ k ∈ Finset.Ioc 0 N, growingMomentSource N k * (k : ℝ) ^ (2 * j - 1) =
            -(2 * j) / (bernoulli (2 * j) : ℝ) := by
  refine ⟨abs_growingMomentSource_le, tendsto_gmOrder, ?_⟩
  filter_upwards [eventually_growingMomentSource_eq, eventually_gt_atTop 0] with N hN hNpos
  obtain ⟨heq, hA⟩ := hN
  rw [heq]
  obtain ⟨hc, hs, ho⟩ := gmRow_moments hNpos hA.1
  refine ⟨fun k hk hkM => ?_, hc, hs, ho⟩
  rw [gmRow, if_neg (by omega), if_pos hkM]

/-- The source rows satisfy the hypotheses of the zero-charge tail bounds for all large `N`. -/
theorem eventually_growingMomentSource_zeroCharge :
    ∀ᶠ N : ℕ in atTop, (∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → growingMomentSource N k = μ k) ∧
      (∀ k ∈ Finset.Ioc 0 N, |growingMomentSource N k| ≤ 1) ∧
      chronologicalHarmonicCharge (growingMomentSource N) N = 0 := by
  filter_upwards [growingMomentSource_spec.2.2] with N hN
  exact ⟨hN.1, fun k _ => abs_growingMomentSource_le N k, hN.2.1⟩

/-- **Jets at `t = 0`.**  For all large `N` the analytic residual of the source vanishes at `0`
together with its first `m_N` odd derivatives, while every even derivative of positive order
equals `1`. -/
theorem growingMomentSource_jets :
    ∀ᶠ N : ℕ in atTop, heatErrorExt (growingMomentSource N) N 0 = 0 ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ gmOrder N →
        iteratedDeriv (2 * j - 1) (heatErrorExt (growingMomentSource N) N) 0 = 0) ∧
      (∀ j : ℕ, 1 ≤ j → iteratedDeriv (2 * j) (heatErrorExt (growingMomentSource N) N) 0 = 1) := by
  filter_upwards [growingMomentSource_spec.2.2] with N hN
  exact heatErrorExt_jets hN.2.2.1 hN.2.2.2

/-- **Convergence away from zero.**  For every `δ > 0` the residuals tend to zero uniformly on
`[δ, ∞)` and in `L²([δ, ∞))`. -/
theorem growingMomentSource_tendsto_away_from_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ∫ t in Ioi δ, chronologicalHeatError (growingMomentSource N) N t ^ 2)
        atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, δ ≤ t →
        |chronologicalHeatError (growingMomentSource N) N t| ≤ ε := by
  have hqδ : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hδ)
  have hd : 0 < 1 - Real.exp (-δ) := by linarith
  have hK : Tendsto (fun N : ℕ => ((N / 2 + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp
      (Nat.tendsto_div_const_atTop two_ne_zero))
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(((N / 2 + 1 : ℕ) : ℝ) * δ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hK.atTop_mul_const hδ)
  refine ⟨?_, fun ε hε => ?_⟩
  · have hbound : ∀ᶠ N : ℕ in atTop,
        ∫ t in Ioi δ, chronologicalHeatError (growingMomentSource N) N t ^ 2 ≤
          2 * Real.exp (-(2 * (N / 2 + 1 : ℕ) * δ)) /
            ((N / 2 + 1 : ℕ) * (1 - Real.exp (-δ)) ^ 4) := by
      filter_upwards [eventually_growingMomentSource_zeroCharge] with N hN
      exact integral_sq_heatError_Ioi_le_of_zeroCharge hN.1 hN.2.1 hN.2.2 hδ
    have hlim : Tendsto (fun N : ℕ => 2 * Real.exp (-(2 * ((N / 2 + 1 : ℕ) : ℝ) * δ)) /
        (((N / 2 + 1 : ℕ) : ℝ) * (1 - Real.exp (-δ)) ^ 4)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun N : ℕ => Real.exp (-(2 * ((N / 2 + 1 : ℕ) : ℝ) * δ))) atTop (𝓝 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp
          ((hK.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_mul_const hδ)
      have h3 : Tendsto (fun N : ℕ => (((N / 2 + 1 : ℕ) : ℝ) * (1 - Real.exp (-δ)) ^ 4)⁻¹)
          atTop (𝓝 0) := (hK.atTop_mul_const (by positivity)).inv_tendsto_atTop
      simpa [div_eq_mul_inv, mul_assoc] using (h2.const_mul 2).mul h3
    exact squeeze_zero' (Eventually.of_forall fun N => setIntegral_nonneg measurableSet_Ioi
      fun t _ => sq_nonneg _) hbound hlim
  · have hsmall : ∀ᶠ N : ℕ in atTop,
        2 * Real.exp (-(((N / 2 + 1 : ℕ) : ℝ) * δ)) / (1 - Real.exp (-δ)) ^ 2 ≤ ε := by
      have : Tendsto (fun N : ℕ => 2 * Real.exp (-(((N / 2 + 1 : ℕ) : ℝ) * δ)) /
          (1 - Real.exp (-δ)) ^ 2) atTop (𝓝 0) := by
        simpa using (hexp.const_mul 2).div_const ((1 - Real.exp (-δ)) ^ 2)
      exact this.eventually (ge_mem_nhds hε)
    filter_upwards [eventually_growingMomentSource_zeroCharge, hsmall] with N hN hN'
    exact fun t ht => (abs_heatError_le_of_zeroCharge_of_le hN.1 hN.2.1 hN.2.2 hδ ht).trans hN'

/-- **The logarithmic window.** For all large `N`, `∫_{log N/N}^∞ r_N² ≤ 64/(log N)²`. -/
theorem growingMomentSource_logWindow :
    ∀ᶠ N : ℕ in atTop, ∫ t in Ioi (Real.log N / N),
      chronologicalHeatError (growingMomentSource N) N t ^ 2 ≤ 64 / Real.log N ^ 2 := by
  filter_upwards [eventually_growingMomentSource_zeroCharge, eventually_ge_atTop 4] with N hN h4
  exact integral_sq_heatError_Ioi_log_le_of_zeroCharge hN.1 hN.2.1 hN.2.2 h4

/-- **Full `L²` convergence of the source reduces to its rescaled logarithmic window.** -/
theorem growingMomentSource_L2_iff_window :
    Tendsto (fun N : ℕ => chronologicalL2Norm (chronologicalHeatError (growingMomentSource N) N))
        atTop (𝓝 0) ↔
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ u in (0 : ℝ)..Real.log N,
        chronologicalHeatError (growingMomentSource N) N (u / N) ^ 2) atTop (𝓝 0) :=
  tendsto_L2Norm_iff_logWindow_of_zeroCharge eventually_growingMomentSource_zeroCharge

end RHTower
