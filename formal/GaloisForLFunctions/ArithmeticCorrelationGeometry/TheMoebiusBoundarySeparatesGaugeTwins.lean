import GaloisForLFunctions.ArithmeticCorrelationGeometry.MixedGramsOfAnAffineOrbitAreLinearIncidences
import GaloisForLFunctions.RHTower.HardyLittlewoodExponentLaw
import GaloisForLFunctions.HTGeometry.SquarefreeDensityLowerBound

/-!
# The Möbius boundary separates gauge twins

Put the Möbius source `μ(j) j^{−1/2}` on the horizon and pair it on the escaped cells of
`j ↦ aj + b` with the flat critical source `j^{−1/2}`. The escaped pairing is
`Σ_{(N−b)/a < j ≤ N} μ(j)/j` (`escapedPairing_moebiusSource`).

* **The Möbius boundary vanishes** (`tendsto_escapedPairing_moebiusSource`). By the prime number
  theorem in the form `Σ_{n ≤ N} μ(n)/n → 0`, the signed boundary of every affine map tends to `0`
  as the horizon grows, for every multiplier `a` and translation `b`.
* **Its gauge twin keeps a boundary** (`escapedPairing_moebiusTwin_ge`). Twisting by the Liouville
  sign `λ`, a completely multiplicative sign, gives `λμ = μ²` (`liouville_mul_moebius`): the same
  moduli and the same value on every multiplicatively coincident monomial. Its boundary is
  `Σ μ(j)²/j` over the escaped cells, at least `r/100` whenever `2^r ≤ a`: every dyadic block
  carries squarefree density at least `1/50`.

So two sources with identical multiplicative data are separated by the boundary correction of a
finite presentation, at a horizon-uniform scale (`moebius_boundary_separates_twin`). The separation
is arithmetic — the cancellation of `μ` at the critical weight, i.e. the prime number theorem — and
it lives entirely in the escaped cells: the boundary is where a mixed law can see a gauge point.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open BiarithmeticGeometry SignedSuccessorArithmetic

/-! ### Sources on the positive cells -/

/-- The source `j ↦ f(j)` on the positive cells, vanishing at the origin. -/
def cellSource (N : ℕ) (f : ℕ → ℝ) : HorizonSpace N := fun j => if j.val = 0 then 0 else f j.val

/-- **The escaped pairing of two cell sources is a sum over the escaped range.** -/
theorem escapedPairing_cellSource (N : ℕ) (a : ℕ+) (b : ℕ) (f g : ℕ → ℝ) :
    escapedPairing N a b (cellSource N f) (cellSource N g) =
      ∑ j ∈ Ioc ((N - b) / a) N, f j * g j := by
  simp only [escapedPairing, cellSource]
  rw [Fin.sum_univ_eq_sum_range (fun j => if N < (a : ℕ) * j + b then
      (if j = 0 then (0 : ℝ) else f j) * (if j = 0 then (0 : ℝ) else g j) else 0) (N + 1)]
  rw [← Finset.sum_filter, ← Finset.sum_filter_add_sum_filter_not _ (· = 0)]
  have h0 : ∑ j ∈ ((range (N + 1)).filter fun j => N < (a : ℕ) * j + b).filter (· = 0),
      (if j = 0 then (0 : ℝ) else f j) * (if j = 0 then (0 : ℝ) else g j) = 0 :=
    Finset.sum_eq_zero fun j hj => by rw [(Finset.mem_filter.mp hj).2]; simp
  rw [h0, zero_add]
  have hset : ((range (N + 1)).filter fun j => N < (a : ℕ) * j + b).filter (fun j => ¬ j = 0) =
      Ioc ((N - b) / a) N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hjN, hesc⟩, hj0⟩
      exact ⟨(lt_mul_add_iff a.pos (Nat.one_le_iff_ne_zero.mpr hj0)).mp hesc, by omega⟩
    · rintro ⟨hlt, hjN⟩
      have hj1 : 1 ≤ j := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hlt)
      exact ⟨⟨by omega, (lt_mul_add_iff a.pos hj1).mpr hlt⟩, by omega⟩
  rw [hset]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hj).1)
  rw [if_neg hj0, if_neg hj0]

/-- The Möbius source `μ(j) j^{−1/2}`. -/
def moebiusSource (N : ℕ) : HorizonSpace N :=
  cellSource N fun j => (μ j : ℝ) * ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹

/-- The flat critical source `j^{−1/2}`. -/
def flatSource (N : ℕ) : HorizonSpace N := cellSource N fun j => ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹

theorem inv_sqrt_mul_inv_sqrt {j : ℕ} (hj : j ≠ 0) :
    ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹ * ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹ = 1 / (j : ℝ) := by
  have hpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj
  rw [← mul_inv, ← Real.rpow_add hpos]
  norm_num

/-- **The Möbius boundary.** -/
theorem escapedPairing_moebiusSource (N : ℕ) (a : ℕ+) (b : ℕ) :
    escapedPairing N a b (moebiusSource N) (flatSource N) =
      ∑ j ∈ Ioc ((N - b) / a) N, (μ j : ℝ) / j := by
  rw [moebiusSource, flatSource, escapedPairing_cellSource]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj0 : j ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hj).1)
  rw [mul_assoc, inv_sqrt_mul_inv_sqrt hj0]
  ring

/-! ### The Möbius boundary vanishes -/

/-- `Σ_{M < j ≤ N} μ(j)/j` as a difference of partial sums. -/
theorem sum_Ioc_moebius_div (M N : ℕ) (h : M ≤ N) :
    ∑ j ∈ Ioc M N, (μ j : ℝ) / j =
      ∑ n ∈ range (N + 1), (μ n : ℝ) / n - ∑ n ∈ range (M + 1), (μ n : ℝ) / n := by
  rw [eq_sub_iff_add_eq, Finset.range_eq_Ico, Finset.range_eq_Ico, add_comm,
    ← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_consecutive _ (by omega) (by omega)]

/-- **The signed boundary of the Möbius source vanishes.** -/
theorem tendsto_escapedPairing_moebiusSource (a : ℕ+) (b : ℕ) :
    Tendsto (fun N => escapedPairing N a b (moebiusSource N) (flatSource N)) atTop (𝓝 0) := by
  simp_rw [escapedPairing_moebiusSource]
  have hS := RHTower.tendsto_sum_range_succ_moebius_div
  have hM := hS.comp (tendsto_escapeStart (b := b) a.pos)
  have := hS.sub hM
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [sum_Ioc_moebius_div _ _ div_le_self_sub]

/-! ### The gauge twin keeps a boundary -/

/-- **`λμ = μ²`.** -/
theorem liouville_mul_moebius (n : ℕ) :
    ((ArithmeticFunction.liouville n : ℤ) : ℝ) * (μ n : ℝ) = (μ n : ℝ) ^ 2 := by
  by_cases hsq : Squarefree n
  · have hn : n ≠ 0 := hsq.ne_zero
    rw [ArithmeticFunction.liouville_apply hn, ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    ring
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- The Liouville twin of the Möbius source is the source `μ(j)² j^{−1/2}`. -/
theorem signTwist_liouville_moebiusSource (N : ℕ) :
    signTwist N CMSign.liouville (moebiusSource N) =
      cellSource N fun j => (μ j : ℝ) ^ 2 * ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹ := by
  funext j
  simp only [signTwist, moebiusSource, cellSource]
  by_cases hj : j.val = 0
  · simp [hj]
  · rw [if_neg hj, if_neg hj, CMSign.liouville_val hj, ← mul_assoc, liouville_mul_moebius]

/-- Every dyadic block carries Möbius mass at least `1/100`. -/
theorem sum_dyadic_moebius_sq_div_ge {K : ℕ} (hK : 1 ≤ K) :
    (1 / 100 : ℝ) ≤ ∑ j ∈ Ioc K (2 * K), (μ j : ℝ) ^ 2 / j := by
  classical
  have hcard := RHTower.card_filter_squarefree_Ioc_ge K
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hterm : ∀ j ∈ Ioc K (2 * K), (if Squarefree j then (1 / (2 * K : ℝ)) else 0) ≤
      (μ j : ℝ) ^ 2 / j := by
    intro j hj
    have hj := Finset.mem_Ioc.mp hj
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    split_ifs with hsq
    · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
      push_cast
      have h1 : ((-1 : ℝ) ^ ArithmeticFunction.cardFactors j) ^ 2 = 1 := by
        rw [sq, ← mul_pow]; norm_num
      rw [h1]
      have : (j : ℝ) ≤ 2 * K := by exact_mod_cast hj.2
      exact one_div_le_one_div_of_le hjpos this
    · positivity
  calc (1 / 100 : ℝ) = (K / 50) * (1 / (2 * K)) := by field_simp; norm_num
    _ ≤ (#((Ioc K (2 * K)).filter Squarefree) : ℝ) * (1 / (2 * K)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ j ∈ Ioc K (2 * K), (if Squarefree j then (1 / (2 * K : ℝ)) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- `r` consecutive dyadic blocks above `K` carry Möbius mass at least `r/100`. -/
theorem sum_Ioc_pow_moebius_sq_div_ge {K : ℕ} (hK : 1 ≤ K) (r : ℕ) :
    (r / 100 : ℝ) ≤ ∑ j ∈ Ioc K (2 ^ r * K), (μ j : ℝ) ^ 2 / j := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hK' : 1 ≤ 2 ^ r * K := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsplit : Ioc K (2 ^ (r + 1) * K) = Ioc K (2 ^ r * K) ∪ Ioc (2 ^ r * K) (2 * (2 ^ r * K)) := by
      rw [show 2 ^ (r + 1) * K = 2 * (2 ^ r * K) by ring]
      exact (Finset.Ioc_union_Ioc_eq_Ioc (by nlinarith [Nat.one_le_two_pow (n := r)])
        (by omega)).symm
    have hdisj : Disjoint (Ioc K (2 ^ r * K)) (Ioc (2 ^ r * K) (2 * (2 ^ r * K))) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_Ioc] at h1 h2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have := sum_dyadic_moebius_sq_div_ge hK'
    push_cast
    linarith

/-- **The gauge twin keeps a boundary.** If `2^r ≤ a` and the escape start is positive, the
Liouville twin of the Möbius source has escaped pairing at least `r/100` with the flat source. -/
theorem escapedPairing_moebiusTwin_ge {N : ℕ} {a : ℕ+} {b r : ℕ} (hr : 2 ^ r ≤ (a : ℕ))
    (hM : 1 ≤ (N - b) / a) :
    (r / 100 : ℝ) ≤ escapedPairing N a b (signTwist N CMSign.liouville (moebiusSource N))
      (flatSource N) := by
  rw [signTwist_liouville_moebiusSource, flatSource, escapedPairing_cellSource]
  have hsub : Ioc ((N - b) / a) (2 ^ r * ((N - b) / a)) ⊆ Ioc ((N - b) / a) N := by
    intro j hj
    simp only [Finset.mem_Ioc] at hj ⊢
    refine ⟨hj.1, hj.2.trans ?_⟩
    calc 2 ^ r * ((N - b) / a) ≤ (a : ℕ) * ((N - b) / a) := Nat.mul_le_mul_right _ hr
      _ ≤ N - b := Nat.mul_div_le _ _
      _ ≤ N := Nat.sub_le _ _
  have hterm : ∀ j ∈ Ioc ((N - b) / a) N, (μ j : ℝ) ^ 2 * ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹ *
      ((j : ℝ) ^ (1 / 2 : ℝ))⁻¹ = (μ j : ℝ) ^ 2 / j := by
    intro j hj
    have hj0 : j ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hj).1)
    rw [mul_assoc, inv_sqrt_mul_inv_sqrt hj0]
    ring
  rw [Finset.sum_congr rfl hterm]
  calc (r / 100 : ℝ) ≤ ∑ j ∈ Ioc ((N - b) / a) (2 ^ r * ((N - b) / a)), (μ j : ℝ) ^ 2 / j :=
        sum_Ioc_pow_moebius_sq_div_ge hM r
    _ ≤ ∑ j ∈ Ioc ((N - b) / a) N, (μ j : ℝ) ^ 2 / j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => by positivity

/-- **The Möbius boundary separates gauge twins.** For every dilation `a ≥ 2`: the Möbius source
has vanishing boundary, while its Liouville twin — same moduli, same multiplicatively coincident
monomials — has boundary at least `1/100` at every large horizon. -/
theorem moebius_boundary_separates_twin {a : ℕ+} (ha : 2 ≤ (a : ℕ)) (b : ℕ) :
    Tendsto (fun N => escapedPairing N a b (moebiusSource N) (flatSource N)) atTop (𝓝 0) ∧
    ∀ᶠ N in atTop, (1 / 100 : ℝ) ≤
      escapedPairing N a b (signTwist N CMSign.liouville (moebiusSource N)) (flatSource N) := by
  refine ⟨tendsto_escapedPairing_moebiusSource a b, ?_⟩
  filter_upwards [(tendsto_escapeStart (b := b) a.pos).eventually_ge_atTop 1] with N hN
  have := escapedPairing_moebiusTwin_ge (N := N) (b := b) (r := 1) (by simpa using ha) hN
  simpa using this

end GaloisForLFunctions.ArithmeticCorrelationGeometry
