import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HarmonicCouplingForcesSourceBlindness

/-!
# The exact Fejér barrier

A nonnegative cosine polynomial `P(θ) = Σ_{k ≤ K} a_k cos(kθ)` of degree `K ≥ 1` satisfies
`a₁ ≤ 2cos(π/(K+2)) · a₀`, and the constant is attained (`cosinePolynomial_first_le_fejer`,
`fejer_barrier_attained`, `fejer_barrier_sharp`).

*Certificate.* Put `N = K + 2`, `α = π/N` and let `θ_j = (2j+1)α`, `j < N`, be the roots of
`z^N = −1` (`fejerNode`). Their moments `Σ_j cos(kθ_j)` vanish for `1 ≤ k ≤ N−1`
(`sum_cos_odd_nodes_eq_zero`). The weights `cos α − cos θ_j ≥ 0` (`fejerWeight`) kill every moment
`2 ≤ k ≤ K` and give `Σ_j (cos α − cos θ_j) P(θ_j) = N (cos α · a₀ − a₁/2)` (`fejer_quadrature`).

*Extremal.* The profile `b_j = sin((j+1)α)`, `j ≤ K`, has Fejér autocorrelation `a₀ = Σ b_j² = N/2`
and `a₁ = 2 Σ b_j b_{j+1} = N cos α`. So `|Σ b_j e^{ijθ}|²` meets the bound.

In de la Vallée Poussin's coupling `a₀` weighs the pole and `a₁` the aligned zero. At degree `K` the
purchase ratio is therefore exactly `2cos(π/(K+2))`: `1` at `K = 1`, `√2` at `K = 2`, increasing to
`2` without reaching it.
-/

open Finset Real

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- The odd nodes `θ_j = (2j+1)π/N`, the arguments of the roots of `z^N = −1`. -/
noncomputable def fejerNode (N j : ℕ) : ℝ := (2 * j + 1) * π / N

/-- The quadrature weight `cos(π/N) − cos θ_j`. -/
noncomputable def fejerWeight (N j : ℕ) : ℝ := Real.cos (π / N) - Real.cos (fejerNode N j)

/-- Telescoping sum of cosines along an arithmetic progression. -/
theorem two_sin_mul_sum_cos (φ β : ℝ) (N : ℕ) :
    2 * Real.sin β * ∑ j ∈ range N, Real.cos (φ + 2 * j * β) =
      Real.sin (φ + (2 * N - 1) * β) - Real.sin (φ - β) := by
  induction N with
  | zero => simp [sub_eq_add_neg]
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : φ + (2 * ((N + 1 : ℕ) : ℝ) - 1) * β = (φ + 2 * N * β) + β := by push_cast; ring
    have h2 : φ + (2 * (N : ℝ) - 1) * β = (φ + 2 * N * β) - β := by ring
    rw [h1, h2, Real.sin_add (φ + 2 * N * β) β, Real.sin_sub (φ + 2 * N * β) β]
    ring

/-- A full progression of `N` angles with step `2kπ/N`, `1 ≤ k ≤ N − 1`, has zero cosine sum. -/
theorem sum_cos_progression_eq_zero (φ : ℝ) {N k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ∑ j ∈ range N, Real.cos (φ + 2 * j * (k * π / N)) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hN.ne'
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hs : Real.sin (k * π / N) ≠ 0 := by
    refine (Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos hk' Real.pi_pos) hN) ?_).ne'
    rw [div_lt_iff₀ hN]
    have : (k : ℝ) < N := by exact_mod_cast hkN
    nlinarith [Real.pi_pos]
  have h := two_sin_mul_sum_cos φ (k * π / N) N
  have hNk : (N : ℝ) * (k * π / N) = k * π := by field_simp
  have hper : φ + (2 * N - 1) * (k * π / N) = (φ - k * π / N) + (k : ℕ) * (2 * π) := by
    linear_combination 2 * hNk
  rw [hper, Real.sin_add_nat_mul_two_pi, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero hs)

/-- Moments of the odd nodes: `Σ_{j<N} cos(kθ_j) = 0` for `1 ≤ k ≤ N−1`. -/
theorem sum_cos_odd_nodes_eq_zero {N k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ∑ j ∈ range N, Real.cos (k * fejerNode N j) = 0 := by
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_)
    (sum_cos_progression_eq_zero (k * π / N) hk hkN)
  unfold fejerNode
  congr 1
  ring

/-- Every odd node lies in `[α, 2π − α]`, so its weight is nonnegative. -/
theorem fejerWeight_nonneg {N j : ℕ} (hj : j < N) : 0 ≤ fejerWeight N j := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  unfold fejerWeight fejerNode
  rcases le_or_gt ((2 * j + 1 : ℝ)) N with h | h
  · have hle : π / N ≤ (2 * j + 1) * π / N := by
      rw [div_le_div_iff_of_pos_right hN']
      nlinarith [Real.pi_pos]
    have hpi : (2 * j + 1) * π / N ≤ π := by
      rw [div_le_iff₀ hN']
      nlinarith [Real.pi_pos]
    exact sub_nonneg.mpr (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi hle)
  · -- Reflect `θ_j` to `2π − θ_j ∈ [α, π]`.
    have hθ : Real.cos ((2 * j + 1) * π / N) = Real.cos ((2 * N - 2 * j - 1) * π / N) := by
      have e : (2 * N - 2 * j - 1) * π / N = 2 * π - (2 * j + 1) * π / N := by
        field_simp
        ring
      rw [e, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
      ring
    have hle : π / N ≤ (2 * N - 2 * j - 1) * π / N := by
      rw [div_le_div_iff_of_pos_right hN']
      nlinarith [Real.pi_pos]
    have hpi : (2 * N - 2 * j - 1) * π / N ≤ π := by
      rw [div_le_iff₀ hN']
      nlinarith [Real.pi_pos]
    rw [hθ]
    exact sub_nonneg.mpr (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hpi hle)

/-- Weighted moment `k = 0`: `Σ_j w_j = N cos α`. -/
theorem sum_fejerWeight {N : ℕ} (hN : 2 ≤ N) :
    ∑ j ∈ range N, fejerWeight N j = N * Real.cos (π / N) := by
  have h1 := sum_cos_odd_nodes_eq_zero (N := N) (k := 1) le_rfl (by omega)
  simp only [Nat.cast_one, one_mul] at h1
  unfold fejerWeight
  rw [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_zero]

/-- Weighted moment `k = 1`: `Σ_j w_j cos θ_j = −N/2`. -/
theorem sum_fejerWeight_mul_cos {N : ℕ} (hN : 3 ≤ N) :
    ∑ j ∈ range N, fejerWeight N j * Real.cos (fejerNode N j) = -(N : ℝ) / 2 := by
  have hterm : ∀ j, fejerWeight N j * Real.cos (fejerNode N j) =
      Real.cos (π / N) * Real.cos (((1 : ℕ) : ℝ) * fejerNode N j) - 1 / 2 -
        Real.cos (((2 : ℕ) : ℝ) * fejerNode N j) / 2 := by
    intro j
    unfold fejerWeight
    rw [Nat.cast_one, one_mul, Nat.cast_two, sub_mul, ← sq, Real.cos_sq]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_div,
    sum_cos_odd_nodes_eq_zero (N := N) (k := 1) le_rfl (by omega),
    sum_cos_odd_nodes_eq_zero (N := N) (k := 2) (by norm_num) (by omega),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Weighted moments `2 ≤ k ≤ N − 2` vanish. -/
theorem sum_fejerWeight_mul_cos_high {N m : ℕ} (hm : m + 4 ≤ N) :
    ∑ j ∈ range N, fejerWeight N j * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j) = 0 := by
  have hterm : ∀ j, fejerWeight N j * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j) =
      Real.cos (π / N) * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j) -
        (Real.cos (((m + 3 : ℕ) : ℝ) * fejerNode N j) +
          Real.cos (((m + 1 : ℕ) : ℝ) * fejerNode N j)) / 2 := by
    intro j
    unfold fejerWeight
    have e1 : ((m + 3 : ℕ) : ℝ) * fejerNode N j =
        ((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j + fejerNode N j := by push_cast; ring
    have e2 : ((m + 1 : ℕ) : ℝ) * fejerNode N j =
        ((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j - fejerNode N j := by push_cast; ring
    rw [e1, e2, Real.cos_add, Real.cos_sub]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_div, Finset.sum_add_distrib,
    sum_cos_odd_nodes_eq_zero (N := N) (k := m + 1 + 1) (by omega) (by omega),
    sum_cos_odd_nodes_eq_zero (N := N) (k := m + 3) (by omega) (by omega),
    sum_cos_odd_nodes_eq_zero (N := N) (k := m + 1) (by omega) (by omega)]
  ring

/-- **Fejér quadrature.** For every cosine polynomial of degree `K ≥ 1`, with `N = K + 2`,
`Σ_{j<N} (cos α − cos θ_j) P(θ_j) = N (cos α · a₀ − a₁/2)`. -/
theorem fejer_quadrature (a : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    ∑ j ∈ range (K + 2), fejerWeight (K + 2) j *
        HTGeometry.cosinePolynomial a K (fejerNode (K + 2) j) =
      (K + 2 : ℕ) * (Real.cos (π / (K + 2 : ℕ)) * a 0 - a 1 / 2) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le' hK
  set N := L + 1 + 2 with hN
  -- Split `P` into its constant, first and higher modes.
  have hexp : ∀ j, fejerWeight N j * HTGeometry.cosinePolynomial a (L + 1) (fejerNode N j) =
      (∑ m ∈ range L, a (m + 1 + 1) *
          (fejerWeight N j * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j))) +
        a 1 * (fejerWeight N j * Real.cos (fejerNode N j)) + a 0 * fejerWeight N j := by
    intro j
    have hs : fejerWeight N j * ∑ m ∈ range L, a (m + 1 + 1) *
          Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j) =
        ∑ m ∈ range L, a (m + 1 + 1) *
          (fejerWeight N j * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    unfold HTGeometry.cosinePolynomial
    rw [Finset.sum_range_succ', Finset.sum_range_succ', mul_add, mul_add, hs]
    simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, zero_add, Nat.cast_one, one_mul]
    ring
  have hhigh : ∑ m ∈ range L, ∑ j ∈ range N, a (m + 1 + 1) *
      (fejerWeight N j * Real.cos (((m + 1 + 1 : ℕ) : ℝ) * fejerNode N j)) = 0 :=
    Finset.sum_eq_zero fun m hm => by
      rw [← Finset.mul_sum, sum_fejerWeight_mul_cos_high (by simp at hm; omega), mul_zero]
  rw [Finset.sum_congr rfl fun j _ => hexp j, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_comm, hhigh, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_fejerWeight_mul_cos (by omega), sum_fejerWeight (by omega)]
  ring

/-- **The exact Fejér barrier.** A nonnegative cosine polynomial of degree `K ≥ 1` satisfies
`a₁ ≤ 2cos(π/(K+2)) a₀`. -/
theorem cosinePolynomial_first_le_fejer {a : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (hP : ∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) :
    a 1 ≤ 2 * Real.cos (π / (K + 2 : ℕ)) * a 0 := by
  have hnn : 0 ≤ ∑ j ∈ range (K + 2), fejerWeight (K + 2) j *
      HTGeometry.cosinePolynomial a K (fejerNode (K + 2) j) :=
    Finset.sum_nonneg fun j hj =>
      mul_nonneg (fejerWeight_nonneg (Finset.mem_range.mp hj)) (hP _)
  rw [fejer_quadrature a hK] at hnn
  have h := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < (K + 2 : ℕ))).mp hnn
  linarith

/-! ### The extremal profile -/

/-- The extremal profile `b_j = sin((j+1)π/(K+2))`. -/
noncomputable def fejerExtremal (K j : ℕ) : ℝ := Real.sin ((j + 1) * π / (K + 2 : ℕ))

/-- Off the diagonal, the Fejér autocorrelation at lag `m` is twice the lagged inner product. -/
theorem fejerAutoCoeff_eq_lag (M : ℕ) (b : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) :
    ArithmeticCastelnuovoSeveri.fejerAutoCoeff M b m =
      2 * ∑ j ∈ range (M + 1 - m), b j * b (j + m) := by
  have hS : (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p => ArithmeticCastelnuovoSeveri.natDist p.1 p.2 = m) =
        ((range (M + 1 - m)).map ⟨fun j => (j, j + m), fun x y h => by
          simpa using congrArg Prod.fst h⟩) ∪
        ((range (M + 1 - m)).map ⟨fun j => (j + m, j), fun x y h => by
          simpa using congrArg Prod.snd h⟩) := by
    ext ⟨p, q⟩
    simp only [ArithmeticCastelnuovoSeveri.natDist, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hp, hq⟩, h⟩
      rcases le_total p q with hpq | hpq
      · exact Or.inl ⟨p, by omega, rfl, by omega⟩
      · exact Or.inr ⟨q, by omega, by omega, rfl⟩
    · rintro (⟨j, hj, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩) <;> exact ⟨⟨by omega, by omega⟩, by omega⟩
  have hdisj : Disjoint ((range (M + 1 - m)).map ⟨fun j => (j, j + m), fun x y h => by
        simpa using congrArg Prod.fst h⟩)
      ((range (M + 1 - m)).map ⟨fun j => (j + m, j), fun x y h => by
        simpa using congrArg Prod.snd h⟩) := by
    rw [Finset.disjoint_left]
    rintro ⟨p, q⟩ h1 h2
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk,
      Prod.mk.injEq] at h1 h2
    obtain ⟨j, -, rfl, rfl⟩ := h1
    obtain ⟨i, -, h, h'⟩ := h2
    omega
  unfold ArithmeticCastelnuovoSeveri.fejerAutoCoeff
  rw [hS, Finset.sum_union hdisj, Finset.sum_map, Finset.sum_map, two_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- At lag `0` the Fejér autocorrelation is `Σ_{j ≤ M} b_j²`. -/
theorem fejerAutoCoeff_zero_eq (M : ℕ) (b : ℕ → ℝ) :
    ArithmeticCastelnuovoSeveri.fejerAutoCoeff M b 0 = ∑ j ∈ range (M + 1), b j * b j := by
  have hS : (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
      (fun p => ArithmeticCastelnuovoSeveri.natDist p.1 p.2 = 0) =
        (range (M + 1)).map ⟨fun j => (j, j), fun x y h => by
          simpa using congrArg Prod.fst h⟩ := by
    ext ⟨p, q⟩
    simp only [ArithmeticCastelnuovoSeveri.natDist, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hp, _⟩, h⟩
      exact ⟨p, hp, rfl, by omega⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      exact ⟨⟨hj, hj⟩, by omega⟩
  unfold ArithmeticCastelnuovoSeveri.fejerAutoCoeff
  rw [hS, Finset.sum_map]
  rfl

/-- `Σ_{j ≤ K} cos(2(j+1)π/(K+2)) = −1`: a full period of even nodes minus the node `0`. -/
theorem sum_cos_even_nodes (K : ℕ) :
    ∑ j ∈ range (K + 1), Real.cos (2 * ((j : ℝ) + 1) * π / (K + 2 : ℕ)) = -1 := by
  have h := sum_cos_progression_eq_zero 0 (N := K + 2) (k := 1) le_rfl (by omega)
  rw [Finset.sum_range_succ'] at h
  have hterm : ∀ j ∈ range (K + 1),
      Real.cos (0 + 2 * ((j + 1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) * π / ((K + 2 : ℕ) : ℝ))) =
        Real.cos (2 * ((j : ℝ) + 1) * π / (K + 2 : ℕ)) := fun j _ => by
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm] at h
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, Real.cos_zero] at h
  linarith

/-- `Σ_{j < M} cos((2j+3)π/(M+2)) = −2cos(π/(M+2))`: the odd nodes without the two nearest to
`0`. -/
theorem sum_cos_odd_inner (M : ℕ) :
    ∑ j ∈ range M, Real.cos ((2 * (j : ℝ) + 3) * π / (M + 2 : ℕ)) =
      -2 * Real.cos (π / (M + 2 : ℕ)) := by
  have h := sum_cos_odd_nodes_eq_zero (N := M + 2) (k := 1) le_rfl (by omega)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at h
  have hD : ((M + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hfirst : Real.cos (((1 : ℕ) : ℝ) * fejerNode (M + 2) 0) = Real.cos (π / (M + 2 : ℕ)) := by
    unfold fejerNode
    congr 1
    push_cast
    ring
  have hlast : Real.cos (((1 : ℕ) : ℝ) * fejerNode (M + 2) (M + 1)) =
      Real.cos (π / (M + 2 : ℕ)) := by
    have e : ((1 : ℕ) : ℝ) * fejerNode (M + 2) (M + 1) = 2 * π - π / (M + 2 : ℕ) := by
      unfold fejerNode
      rw [Nat.cast_one, one_mul, eq_sub_iff_add_eq, ← add_div, div_eq_iff hD]
      push_cast
      ring
    rw [e, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
    ring
  have hmid : ∀ j ∈ range M, Real.cos (((1 : ℕ) : ℝ) * fejerNode (M + 2) (j + 1)) =
      Real.cos ((2 * (j : ℝ) + 3) * π / (M + 2 : ℕ)) := fun j _ => by
    unfold fejerNode
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl hmid, hfirst, hlast] at h
  linarith

/-- `Σ_{j ≤ K} sin²((j+1)α) = N/2`. -/
theorem fejerExtremal_sq_sum (K : ℕ) :
    ∑ j ∈ range (K + 1), fejerExtremal K j * fejerExtremal K j = (K + 2 : ℕ) / 2 := by
  have hsq : ∀ j : ℕ, fejerExtremal K j * fejerExtremal K j =
      1 / 2 - Real.cos (2 * ((j : ℝ) + 1) * π / (K + 2 : ℕ)) / 2 := fun j => by
    unfold fejerExtremal
    rw [← sq, Real.sin_sq_eq_half_sub]
    have e : 2 * (((j : ℝ) + 1) * π / (K + 2 : ℕ)) = 2 * ((j : ℝ) + 1) * π / (K + 2 : ℕ) := by
      ring
    rw [e]
  rw [Finset.sum_congr rfl fun j _ => hsq j, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_div, sum_cos_even_nodes, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- `Σ_{j < K} sin((j+1)α) sin((j+2)α) = (N/2) cos α`. -/
theorem fejerExtremal_lag_sum (K : ℕ) :
    ∑ j ∈ range K, fejerExtremal K j * fejerExtremal K (j + 1) =
      (K + 2 : ℕ) / 2 * Real.cos (π / (K + 2 : ℕ)) := by
  have hprod : ∀ j : ℕ, fejerExtremal K j * fejerExtremal K (j + 1) =
      (Real.cos (π / (K + 2 : ℕ)) - Real.cos ((2 * (j : ℝ) + 3) * π / (K + 2 : ℕ))) / 2 :=
    fun j => by
      unfold fejerExtremal
      have e1 : π / (K + 2 : ℕ) = (((j + 1 : ℕ) : ℝ) + 1) * π / (K + 2 : ℕ) -
          ((j : ℝ) + 1) * π / (K + 2 : ℕ) := by push_cast; ring
      have e2 : (2 * (j : ℝ) + 3) * π / (K + 2 : ℕ) = ((j : ℝ) + 1) * π / (K + 2 : ℕ) +
          (((j + 1 : ℕ) : ℝ) + 1) * π / (K + 2 : ℕ) := by push_cast; ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]
      ring
  rw [Finset.sum_congr rfl fun j _ => hprod j, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_cos_odd_inner K, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

/-- The autocorrelation coefficients of the extremal profile. -/
noncomputable def fejerExtremalCoeff (K : ℕ) : ℕ → ℝ :=
  ArithmeticCastelnuovoSeveri.fejerAutoCoeff K (fejerExtremal K)

theorem fejerExtremalCoeff_zero (K : ℕ) : fejerExtremalCoeff K 0 = (K + 2 : ℕ) / 2 := by
  rw [fejerExtremalCoeff, fejerAutoCoeff_zero_eq, fejerExtremal_sq_sum]

theorem fejerExtremalCoeff_one {K : ℕ} (hK : 1 ≤ K) :
    fejerExtremalCoeff K 1 = (K + 2 : ℕ) * Real.cos (π / (K + 2 : ℕ)) := by
  rw [fejerExtremalCoeff, fejerAutoCoeff_eq_lag K _ le_rfl hK, Nat.add_sub_cancel,
    fejerExtremal_lag_sum]
  ring

/-- **The Fejér barrier is attained.** The extremal autocorrelation is a nonnegative cosine
polynomial of degree `K` with `a₀ = N/2 > 0` and `a₁ = 2cos(π/N) a₀`. -/
theorem fejer_barrier_attained {K : ℕ} (hK : 1 ≤ K) :
    (∀ θ, 0 ≤ HTGeometry.cosinePolynomial (fejerExtremalCoeff K) K θ) ∧
      0 < fejerExtremalCoeff K 0 ∧
      fejerExtremalCoeff K 1 = 2 * Real.cos (π / (K + 2 : ℕ)) * fejerExtremalCoeff K 0 := by
  refine ⟨ArithmeticCastelnuovoSeveri.cosinePolynomial_fejerAutoCoeff_nonneg K _, ?_, ?_⟩
  · rw [fejerExtremalCoeff_zero]
    positivity
  · rw [fejerExtremalCoeff_zero, fejerExtremalCoeff_one hK]
    ring

/-- **Sharpness.** No constant below `2cos(π/(K+2))` bounds the purchase ratio at degree `K`. -/
theorem fejer_barrier_sharp {K : ℕ} (hK : 1 ≤ K) {c : ℝ}
    (hc : ∀ a : ℕ → ℝ, (∀ θ, 0 ≤ HTGeometry.cosinePolynomial a K θ) → a 1 ≤ c * a 0) :
    2 * Real.cos (π / (K + 2 : ℕ)) ≤ c := by
  obtain ⟨hP, h0, h1⟩ := fejer_barrier_attained hK
  have := hc _ hP
  rw [h1] at this
  exact le_of_mul_le_mul_right this h0

end GaloisForLFunctions.MultiplicativePositivityGeometry
