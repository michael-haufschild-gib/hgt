import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertiaCertifiesSixteenTwentyFirsts

/-!
# The coalescence blind spot is exact through third order

`HigherInertiaCertifiesSixteenTwentyFirsts` shows that fourth-order inertia certifies `16/21` at the
sine-kernel moments `(4/3, 2, 13/4)`. This module locates the input that number needs.

* **Third order adds nothing** (`cubic_value_le_two_thirds`). The blind-spot configuration — four
  orthonormal simple critical zeros and one coalesced pair, `Ĥ = diag(1, 1, 1, 1, 2)`, `N = 6` —
  lies in the zero-side model and has normalized moments `(1, 4/3, 2, 10/3)`
  (`blindSpot_moments`). Its first three moments are the sine-kernel ones, so every polynomial
  weight of degree at most three that is valid on the model certifies at most `2/3` at
  `(κ₂, κ₃) = (4/3, 2)`: the value of the rank–trace weight `2x − x²`.
* **Fourth order needs an upper bound on `κ₄`** (`quartic_value_le`). For every degree-four weight
  valid on the model, `value ≤ 2/3 + (κ₄ − 10/3) c₄`. To beat `2/3` below `κ₄ = 10/3` the
  coefficient `c₄` must be negative, so the certificate decreases in `κ₄`: only an upper bound on
  the fourth moment helps.
* **The frequency budget of a cycle** (`triangle_variation_le`, `square_variation_le`,
  `square_variation_attained`). The `k`-th moment of a bandwidth-`λ` Gram matrix is a `k`-level
  correlation sum whose test function is the cyclic product of `k` kernels with frequencies in
  `[−λ/2, λ/2]`; at vertex `i` the frequency is `ξ_i = u_{i−1} − u_i`. For `k = 3`,
  `Σ|ξ_i| ≤ 2λ`; for `k = 4`, `Σ|ξ_i| ≤ 4λ`, attained by alternating edge frequencies. Inside the
  correlation range `Σ|ξ_i| < 2` the cubic moment is available for `λ < 1`, the quartic only for
  `λ < 1/2`.
* **Rank cap** (`sum_le_card_of_isInertiaCertificate`): an admissible weight sums to at most the
  dimension, so at bandwidth `λ` (dimension `λN`) it certifies at most `λ`.

Together: inertia certificates of order at most four built from correlations inside the range
certify at most `2/3` — the cubic moment is blind and the quartic one is out of range at `λ ≥ 1/2`
— and the `16/21` of fourth order requires the fourth moment at bandwidth near one, a
beyond-threshold input. With `κ₂ = 4/3, κ₃ = 2` the quartic weight reaches `3/4` iff
`κ₄ ≤ 2503/768` (`three_quarters_le_qStarValue_iff`). The pair-pair (diagonal) part of the fourth
moment alone, `κ₄ = 49/15`, would give `544/735` (`qStar_value_diagonal`); the sine kernel's
off-diagonal correction `−1/60` brings `κ₄` to `13/4` and the value to `16/21`.
-/

open Matrix Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia

open RiemannGaussian.HermitianRankTrace

/-! ### The frequency budget of a cycle -/

/-- Around a triangle the total frequency variation is twice the range. -/
theorem triangle_variation_le {a b x y z : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hz : z ∈ Set.Icc a b) : |x - y| + |y - z| + |z - x| ≤ 2 * (b - a) := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy; obtain ⟨hz1, hz2⟩ := hz
  rcases le_total x y with h1 | h1 <;> rcases le_total y z with h2 | h2 <;>
    rcases le_total z x with h3 | h3 <;>
    simp only [abs_of_nonneg, abs_of_nonpos, sub_nonneg, sub_nonpos, h1, h2, h3] <;> linarith

/-- Around a square the total frequency variation is at most four times the range. -/
theorem square_variation_le {a b w x y z : ℝ} (hw : w ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b) :
    |w - x| + |x - y| + |y - z| + |z - w| ≤ 4 * (b - a) := by
  obtain ⟨hw1, hw2⟩ := hw; obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy; obtain ⟨hz1, hz2⟩ := hz
  have e : ∀ s t : ℝ, s ∈ Set.Icc a b → t ∈ Set.Icc a b → |s - t| ≤ b - a := fun s t hs ht =>
    abs_sub_le_iff.mpr ⟨by linarith [hs.2, ht.1], by linarith [hs.1, ht.2]⟩
  linarith [e w x ⟨hw1, hw2⟩ ⟨hx1, hx2⟩, e x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩,
    e y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩, e z w ⟨hz1, hz2⟩ ⟨hw1, hw2⟩]

/-- The bound for squares is attained by alternating frequencies. -/
theorem square_variation_attained (a b : ℝ) (hab : a ≤ b) :
    |a - b| + |b - a| + |a - b| + |b - a| = 4 * (b - a) := by
  rw [abs_sub_comm a b, abs_of_nonneg (sub_nonneg.mpr hab)]; ring

/-! ### Rank cap -/

/-- An admissible weight sums to at most the dimension. -/
theorem sum_le_card_of_isInertiaCertificate {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {q : ℝ → ℝ} (hq : IsInertiaCertificate q) :
    ∑ i, q (hH.eigenvalues₀ i) ≤ Fintype.card n := by
  calc ∑ i, q (hH.eigenvalues₀ i) ≤ ∑ _i : Fin (Fintype.card n), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => hq.1 _
    _ = Fintype.card n := by simp

/-! ### The blind-spot configuration -/

/-- Indices: four simple critical zeros and one coalesced pair. -/
abbrev BlindIdx := Fin 4 ⊕ Fin 1

/-- The blind-spot spectrum `(1, 1, 1, 1, 2)`. -/
def blindVal : BlindIdx → ℝ := Sum.elim (fun _ => 1) fun _ => 2

/-- Unit columns of the simple zeros. -/
def blindW (j : Fin 4) : BlindIdx → ℂ := Pi.single (Sum.inl j) ((1 : ℝ) : ℂ)

/-- The coalesced pair: one column of squared norm `2`. -/
def blindA (j : Fin 1) : BlindIdx → ℂ := Pi.single (Sum.inr j) ((Real.sqrt 2 : ℝ) : ℂ)

theorem vecMulVec_single_star_blind (i : BlindIdx) (x : ℝ) :
    vecMulVec (Pi.single i (x : ℂ)) (star (Pi.single i (x : ℂ))) =
      diagonal (Pi.single i ((x ^ 2 : ℝ) : ℂ)) := by
  ext a b
  rw [vecMulVec_apply, diagonal_apply, Pi.star_apply]
  rcases eq_or_ne a i with rfl | ha
  · rcases eq_or_ne b a with rfl | hb
    · simp [sq, Complex.conj_ofReal]
    · simp [hb, hb.symm]
  · simp [Pi.single_apply, ha]

theorem blindSpot_eq_diagonal :
    ∑ j, vecMulVec (blindW j) (star (blindW j)) +
        ∑ j, vecMulVec (blindA j) (star (blindA j)) - 0 =
      diagonal fun i => (blindVal i : ℂ) := by
  have hdiag : ∀ {ι : Type} [Fintype ι] (f : ι → BlindIdx → ℂ),
      ∑ j, diagonal (f j) = diagonal (∑ j, f j) := fun f =>
    (map_sum (diagonalAddMonoidHom BlindIdx ℂ) f Finset.univ).symm
  simp only [blindW, blindA, vecMulVec_single_star_blind, sub_zero, hdiag, diagonal_add]
  congr 1
  funext i
  rcases i with j | j
  · simp only [Finset.sum_apply, Pi.single_apply, Sum.inl.injEq, reduceCtorEq, ite_false,
      Finset.sum_const_zero, add_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [blindVal]
  · simp only [Finset.sum_apply, Pi.single_apply, Sum.inr.injEq, reduceCtorEq, ite_false,
      Finset.sum_const_zero, zero_add, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp [blindVal]

theorem blindSpot_isHermitian :
    (∑ j, vecMulVec (blindW j) (star (blindW j)) +
        ∑ j, vecMulVec (blindA j) (star (blindA j)) - 0).IsHermitian := by
  rw [blindSpot_eq_diagonal]
  exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [Complex.conj_ofReal])

/-- The coalesced pair carries trace `2`. -/
theorem blindSpot_norm :
    (2 * Fintype.card (Fin 1) : ℝ) ≤
      ∑ j, ∑ k, Complex.normSq (blindA j k) - ((0 : Matrix BlindIdx BlindIdx ℂ).trace).re := by
  have h : ∀ j : Fin 1, ∑ k, Complex.normSq (blindA j k) = 2 := fun j => by
    rw [Finset.sum_eq_single (Sum.inr j)]
    · simp [blindA, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    · intro b _ hb; simp [blindA, hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp [h]

/-- **The blind spot has the sine-kernel first three moments**: `tr Ĥ^k = 4 + 2^k`, i.e.
`6 (1, 4/3, 2, 10/3)`. -/
theorem blindSpot_moments (k : ℕ) :
    (((diagonal fun i : BlindIdx => (blindVal i : ℂ)) ^ k).trace).re = 4 + 2 ^ k := by
  have e : ((diagonal fun i : BlindIdx => (blindVal i : ℂ)) ^ k).trace =
      ((4 + 2 ^ k : ℝ) : ℂ) := by
    simp only [diagonal_pow, trace_diagonal, Pi.pow_apply, Fintype.sum_sum_type, blindVal,
      Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [e, Complex.ofReal_re]

/-- The census inequality of a quartic weight on the blind spot, in moments. -/
theorem blindSpot_value (c₁ c₂ c₃ c₄ : ℝ)
    (hvalid : ∑ i, (c₁ * blindSpot_isHermitian.eigenvalues₀ i +
      c₂ * blindSpot_isHermitian.eigenvalues₀ i ^ 2 +
      c₃ * blindSpot_isHermitian.eigenvalues₀ i ^ 3 +
        c₄ * blindSpot_isHermitian.eigenvalues₀ i ^ 4) ≤ Fintype.card (Fin 4)) :
    c₁ + c₂ * (4 / 3) + c₃ * 2 + c₄ * (10 / 3) ≤ 2 / 3 := by
  have hH := blindSpot_isHermitian
  set H := ∑ j, vecMulVec (blindW j) (star (blindW j)) +
    ∑ j, vecMulVec (blindA j) (star (blindA j)) - 0
  have hHd : H = diagonal fun i => (blindVal i : ℂ) := blindSpot_eq_diagonal
  have hsum : ∑ i, (c₁ * hH.eigenvalues₀ i + c₂ * hH.eigenvalues₀ i ^ 2 +
      c₃ * hH.eigenvalues₀ i ^ 3 + c₄ * hH.eigenvalues₀ i ^ 4) =
      c₁ * ((H ^ 1).trace).re + c₂ * ((H ^ 2).trace).re + c₃ * ((H ^ 3).trace).re +
        c₄ * ((H ^ 4).trace).re := by
    have e : ∀ k : ℕ, ((H ^ k).trace).re = ∑ i, hH.eigenvalues i ^ k := fun k =>
      (GaloisForLFunctions.HTGeometry.sum_pow_eigenvalues_eq_trace_pow_re' hH k).symm
    rw [← sum_eigenvalues_reindex hH (fun x => c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4),
      e 4, e 3, e 2, e 1]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, pow_one]
  rw [hsum, hHd, blindSpot_moments, blindSpot_moments, blindSpot_moments,
    blindSpot_moments] at hvalid
  simp only [Fintype.card_fin] at hvalid
  norm_num at hvalid
  linarith

/-- **Third order adds nothing.** Every cubic weight valid on the blind spot certifies at most
`2/3` at the sine-kernel moments `(κ₂, κ₃) = (4/3, 2)`, the value of the rank–trace weight. -/
theorem cubic_value_le_two_thirds (c₁ c₂ c₃ : ℝ)
    (hvalid : ∑ i, (c₁ * blindSpot_isHermitian.eigenvalues₀ i +
      c₂ * blindSpot_isHermitian.eigenvalues₀ i ^ 2 +
        c₃ * blindSpot_isHermitian.eigenvalues₀ i ^ 3) ≤ Fintype.card (Fin 4)) :
    c₁ + c₂ * (4 / 3) + c₃ * 2 ≤ 2 / 3 := by
  have h := blindSpot_value c₁ c₂ c₃ 0 (by simpa using hvalid)
  linarith

/-- The rank–trace weight attains `2/3` at `κ₂ = 4/3`. -/
theorem rankTrace_value : (2 : ℝ) - 4 / 3 = 2 / 3 := by norm_num

/-- **Fourth order needs an upper bound on `κ₄`.** For every quartic weight valid on the blind spot,
the value at `(4/3, 2, κ₄)` is at most `2/3 + (κ₄ − 10/3) c₄`; beating `2/3` with `κ₄ < 10/3` forces
`c₄ < 0`. -/
theorem quartic_value_le (c₁ c₂ c₃ c₄ κ₄ : ℝ)
    (hvalid : ∑ i, (c₁ * blindSpot_isHermitian.eigenvalues₀ i +
      c₂ * blindSpot_isHermitian.eigenvalues₀ i ^ 2 +
      c₃ * blindSpot_isHermitian.eigenvalues₀ i ^ 3 +
        c₄ * blindSpot_isHermitian.eigenvalues₀ i ^ 4) ≤ Fintype.card (Fin 4)) :
    c₁ + c₂ * (4 / 3) + c₃ * 2 + c₄ * κ₄ ≤ 2 / 3 + (κ₄ - 10 / 3) * c₄ := by
  have h := blindSpot_value c₁ c₂ c₃ c₄ hvalid
  linarith

theorem neg_coeff_of_beats_two_thirds {c₁ c₂ c₃ c₄ κ₄ : ℝ} (hκ : κ₄ < 10 / 3)
    (hvalid : ∑ i, (c₁ * blindSpot_isHermitian.eigenvalues₀ i +
      c₂ * blindSpot_isHermitian.eigenvalues₀ i ^ 2 +
      c₃ * blindSpot_isHermitian.eigenvalues₀ i ^ 3 +
        c₄ * blindSpot_isHermitian.eigenvalues₀ i ^ 4) ≤ Fintype.card (Fin 4))
    (hbeat : 2 / 3 < c₁ + c₂ * (4 / 3) + c₃ * 2 + c₄ * κ₄) : c₄ < 0 := by
  have h := quartic_value_le c₁ c₂ c₃ c₄ κ₄ hvalid
  by_contra hc
  push Not at hc
  nlinarith

/-- At the diagonal (pair-pair) fourth moment `κ₄ = 3 + 4/15`, which the prime side gives at
bandwidth one when the off-diagonal product correlations are dropped, the quartic weight certifies
`544/735 ≈ 0.740`: above `2/3`, below `3/4`. -/
theorem qStar_value_diagonal :
    qStarValue (4 / 3) 2 (49 / 15) = 544 / 735 ∧ (2 : ℝ) / 3 < 544 / 735 ∧
      (544 : ℝ) / 735 < 3 / 4 := by
  unfold qStarValue; norm_num

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HigherInertia
