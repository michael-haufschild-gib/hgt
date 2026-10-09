import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriSpectral

/-!
# The positive-part pair field

The spectral horizontal Lamzouri inequality (`HorizontalPacket.spectral_four_mass_bound`) bounds
the cross term `2 tr(Φ_R Φ_P⁺)` from below by `2 Σ_{x ∈ M} max(G(f_x), 0)`, where
`G(ψ) = ⟪Φ_P ψ, ψ⟫` and `Φ_P = Σ_p 2m_p (g_p ⊗ g_p − h_p ⊗ h_p)`. The sharp quantity is the
positive part itself: `⟪Φ_P⁺ψ, ψ⟫ = Σ_j (λ_j)⁺ ⟪e_j, ψ⟫²` for any orthonormal eigenbasis `(e_j, λ_j)`
of the pair form (`positivePartForm`).

* **Positive-part inequality** (`HorizontalPacket.spectral_four_mass_bound_positivePart`).
  `4·mass − E − 2N + 2 Σ_{x∈M} ⟪Φ_P⁺ f_x, f_x⟫ + bonus ≤ Σ_H (2‖f‖² − 1) + Σ_M (2‖f‖² − 1)`.
  It contains the pair-field form, because `max(G(ψ), 0) ≤ ⟪Φ_P⁺ψ, ψ⟫`
  (`max_weightedForm_le_positivePartForm`).
* **Free condition** (`HorizontalPacket.four_mass_sub_energy_le_of_positivePart`). A mixed point
  costs nothing as soon as `⟪Φ_P⁺ f_x, f_x⟫ ≥ ‖f_x‖² − ½`.
* **Eigenvector floor** (`positivePartForm_ge_of_eigen`). If `u` is an eigenvector of the pair
  form with eigenvalue `λ ≥ 0`, then `λ⟪u, ψ⟫² ≤ ‖u‖² ⟪Φ_P⁺ψ, ψ⟫` for every `ψ`.
* **Approximate eigenvectors** (`positivePartForm_ge_of_residual`). With residual `R = Φu − λu`
  and `0 < δ ≤ λ`, `(λ − δ)((|⟪u, ψ⟫| − ‖R‖‖ψ‖/δ)⁺)² ≤ ‖u‖² ⟪Φ_P⁺ψ, ψ⟫`.
* **Decoupled pairs** (`HorizontalPacket.positivePart_ge_of_decoupled`). Suppose the even vector
  `g_p` is orthogonal to `h_p` and to `g_q, h_q` for every other pair `q`. Then
  `⟪Φ_P⁺ψ, ψ⟫ ≥ 2m_p⟪g_p, ψ⟫²` for every `ψ`, whatever the overlaps `⟪h_q, ψ⟫`.

In `G` the other pairs enter through the interference term `Σ_{q≠p} 2m_q⟪h_q, f_x⟫²`, which can be
arbitrarily large. In the positive part they act only through the overlap of the own even vector
with the other pairs' vectors.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The positive part of a diagonalised form -/

section PositivePart

variable {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)

/-- `⟪Φ⁺ψ, ψ⟫ = Σ_j (λ_j)⁺ ⟪e_j, ψ⟫²` for a diagonalisation `(e, λ)`. -/
def positivePartForm (ψ : V) : ℝ := ∑ j, max (ev j) 0 * ⟪e j, ψ⟫ ^ 2

theorem positivePartForm_nonneg (ψ : V) : 0 ≤ positivePartForm e ev ψ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (le_max_right _ _) (sq_nonneg _)

variable {κ : Type*} [Fintype κ] {c : κ → ℝ} {w : κ → V}

/-- `max(Q(ψ), 0) ≤ ⟪Q⁺ψ, ψ⟫`. -/
theorem max_weightedForm_le_positivePartForm
    (hd : ∀ v, weightedForm c w v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) (ψ : V) :
    max (weightedForm c w ψ) 0 ≤ positivePartForm e ev ψ := by
  refine max_le ?_ (positivePartForm_nonneg e ev ψ)
  rw [hd]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)

/-- Polarisation of a diagonalisation. -/
theorem weightedBilin_eq (hd : ∀ v, weightedForm c w v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) (u v : V) :
    ∑ k, c k * (⟪w k, u⟫ * ⟪w k, v⟫) = ∑ j, ev j * (⟪e j, u⟫ * ⟪e j, v⟫) := by
  have h1 := hd (u + v)
  have h2 := hd u
  have h3 := hd v
  simp only [weightedForm, inner_add_right, add_sq, mul_add, Finset.sum_add_distrib] at h1 h2 h3
  have e1 : ∑ k, c k * (2 * ⟪w k, u⟫ * ⟪w k, v⟫) = 2 * ∑ k, c k * (⟪w k, u⟫ * ⟪w k, v⟫) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ j, ev j * (2 * ⟪e j, u⟫ * ⟪e j, v⟫) = 2 * ∑ j, ev j * (⟪e j, u⟫ * ⟪e j, v⟫) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- **Eigenvector floor.** If `ev_j ⟪e_j, u⟫ = λ ⟪e_j, u⟫` for all `j` and `λ ≥ 0`, then
`λ⟪u, ψ⟫² ≤ ‖u‖² ⟪Φ⁺ψ, ψ⟫`. -/
theorem positivePartForm_ge_of_eigen {u : V} {lam : ℝ} (hlam : 0 ≤ lam)
    (heig : ∀ j, ev j * ⟪e j, u⟫ = lam * ⟪e j, u⟫) (ψ : V) :
    lam * ⟪u, ψ⟫ ^ 2 ≤ ‖u‖ ^ 2 * positivePartForm e ev ψ := by
  classical
  set a : Fin n → ℝ := fun j => ⟪e j, u⟫
  set b : Fin n → ℝ := fun j => if a j = 0 then 0 else ⟪e j, ψ⟫
  have hpars : ⟪u, ψ⟫ = ∑ j, a j * b j := by
    rw [← e.sum_inner_mul_inner u ψ]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [a, b]
    split_ifs with h
    · rw [real_inner_comm, h]; ring
    · rw [real_inner_comm]
  have hcs : (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * ∑ j, b j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hnorm : ∑ j, a j ^ 2 = ‖u‖ ^ 2 := sum_sq_inner_orthonormalBasis e u
  have hb : lam * ∑ j, b j ^ 2 ≤ positivePartForm e ev ψ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [b]
    split_ifs with h
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (le_max_right _ _) (sq_nonneg _)
    · have hev : ev j = lam := mul_right_cancel₀ h (heig j)
      rw [hev, max_eq_left hlam]
  rw [hpars]
  calc lam * (∑ j, a j * b j) ^ 2 ≤ lam * ((∑ j, a j ^ 2) * ∑ j, b j ^ 2) :=
        mul_le_mul_of_nonneg_left hcs hlam
    _ = (∑ j, a j ^ 2) * (lam * ∑ j, b j ^ 2) := by ring
    _ ≤ ‖u‖ ^ 2 * positivePartForm e ev ψ := by
        rw [hnorm]; exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

/-- **Approximate-eigenvector floor.** Let `R = Φu − λu` be the residual of `u` under the form's
operator `Φ = weightedOp c w`. For `0 < δ ≤ λ` and every `ψ`,
`(λ − δ)·((|⟪u, ψ⟫| − ‖R‖‖ψ‖/δ)⁺)² ≤ ‖u‖² ⟪Φ⁺ψ, ψ⟫`. The spectral mass of `u` below `λ − δ` is at
most `‖R‖²/δ²`. -/
theorem positivePartForm_ge_of_residual
    (hd : ∀ v, weightedForm c w v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) (u ψ : V) {lam δ : ℝ}
    (hδ : 0 < δ) (hδl : δ ≤ lam) :
    (lam - δ) * max (|⟪u, ψ⟫| - ‖weightedOp c w u - lam • u‖ / δ * ‖ψ‖) 0 ^ 2 ≤
      ‖u‖ ^ 2 * positivePartForm e ev ψ := by
  classical
  set R := weightedOp c w u - lam • u with hR
  set r := ‖R‖ with hr
  set a : Fin n → ℝ := fun j => ⟪e j, u⟫ with ha
  set b : Fin n → ℝ := fun j => ⟪e j, ψ⟫ with hb
  -- coordinates of the residual
  have hRj : ∀ j, ⟪e j, R⟫ = (ev j - lam) * a j := by
    intro j
    have hT : ⟪e j, weightedOp c w u⟫ = ev j * a j := by
      rw [real_inner_comm, inner_weightedOp_left]
      have h := weightedBilin_eq e ev hd u (e j)
      have hsum : ∑ i, ev i * (⟪e i, u⟫ * ⟪e i, e j⟫) = ev j * ⟪e j, u⟫ := by
        rw [Finset.sum_eq_single j]
        · rw [real_inner_self_eq_norm_sq, e.orthonormal.1 j]; ring
        · intro i _ hij; rw [e.orthonormal.2 hij]; ring
        · simp
      rw [hsum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hR, inner_sub_right, real_inner_smul_right, hT]
    ring
  have hr2 : r ^ 2 = ∑ j, ((ev j - lam) * a j) ^ 2 := by
    rw [hr, ← sum_sq_inner_orthonormalBasis e R]
    exact Finset.sum_congr rfl fun j _ => by rw [hRj]
  have hu2 : ∑ j, a j ^ 2 = ‖u‖ ^ 2 := sum_sq_inner_orthonormalBasis e u
  have hψ2 : ∑ j, b j ^ 2 = ‖ψ‖ ^ 2 := sum_sq_inner_orthonormalBasis e ψ
  set S := Finset.univ.filter fun j => lam - δ ≤ ev j with hS
  set Sc := Finset.univ.filter fun j => ¬ lam - δ ≤ ev j with hSc
  -- the spectral mass of `u` below `λ − δ`
  have hlow : δ ^ 2 * ∑ j ∈ Sc, a j ^ 2 ≤ r ^ 2 := by
    rw [hr2, Finset.mul_sum]
    calc ∑ j ∈ Sc, δ ^ 2 * a j ^ 2 ≤ ∑ j ∈ Sc, ((ev j - lam) * a j) ^ 2 :=
          Finset.sum_le_sum fun j hj => by
            have hj' := (Finset.mem_filter.mp hj).2
            have h1 : δ ≤ lam - ev j := by linarith
            have h2 : δ ^ 2 ≤ (ev j - lam) ^ 2 := by nlinarith
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
      _ ≤ ∑ j, ((ev j - lam) * a j) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => sq_nonneg _
  have hbSc : ∑ j ∈ Sc, b j ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [← hψ2]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun j _ _ => sq_nonneg _
  have hcsc : (∑ j ∈ Sc, a j * b j) ^ 2 ≤ (r / δ * ‖ψ‖) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Sc a b
    have hA : ∑ j ∈ Sc, a j ^ 2 ≤ r ^ 2 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc (∑ j ∈ Sc, a j * b j) ^ 2 ≤ (∑ j ∈ Sc, a j ^ 2) * ∑ j ∈ Sc, b j ^ 2 := h
      _ ≤ r ^ 2 / δ ^ 2 * ‖ψ‖ ^ 2 :=
          mul_le_mul hA hbSc (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      _ = (r / δ * ‖ψ‖) ^ 2 := by ring
  have hlowabs : |∑ j ∈ Sc, a j * b j| ≤ r / δ * ‖ψ‖ :=
    abs_le_of_sq_le_sq hcsc (by positivity)
  -- the part of `u` at or above `λ − δ`
  have hcs : (∑ j ∈ S, a j * b j) ^ 2 ≤ ‖u‖ ^ 2 * ∑ j ∈ S, b j ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S a b
    have hA : ∑ j ∈ S, a j ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [← hu2]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun j _ _ => sq_nonneg _
    exact h.trans (mul_le_mul_of_nonneg_right hA (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hpos : (lam - δ) * ∑ j ∈ S, b j ^ 2 ≤ positivePartForm e ev ψ := by
    rw [Finset.mul_sum]
    calc ∑ j ∈ S, (lam - δ) * b j ^ 2 ≤ ∑ j ∈ S, max (ev j) 0 * b j ^ 2 :=
          Finset.sum_le_sum fun j hj => by
            have hj' := (Finset.mem_filter.mp hj).2
            exact mul_le_mul_of_nonneg_right (le_trans hj' (le_max_left _ _)) (sq_nonneg _)
      _ ≤ positivePartForm e ev ψ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ => mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hsplit : ⟪u, ψ⟫ = ∑ j ∈ S, a j * b j + ∑ j ∈ Sc, a j * b j := by
    rw [hS, hSc, Finset.sum_filter_add_sum_filter_not, ← e.sum_inner_mul_inner u ψ]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  -- assemble
  have hmax : max (|⟪u, ψ⟫| - r / δ * ‖ψ‖) 0 ^ 2 ≤ (∑ j ∈ S, a j * b j) ^ 2 := by
    rcases le_total (|⟪u, ψ⟫| - r / δ * ‖ψ‖) 0 with h | h
    · rw [max_eq_right h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]; exact sq_nonneg _
    · rw [max_eq_left h]
      have htri : |⟪u, ψ⟫| ≤ |∑ j ∈ S, a j * b j| + |∑ j ∈ Sc, a j * b j| := by
        rw [hsplit]; exact abs_add_le _ _
      have hge : |⟪u, ψ⟫| - r / δ * ‖ψ‖ ≤ |∑ j ∈ S, a j * b j| := by linarith
      calc (|⟪u, ψ⟫| - r / δ * ‖ψ‖) ^ 2 ≤ |∑ j ∈ S, a j * b j| ^ 2 :=
            pow_le_pow_left₀ h hge 2
        _ = (∑ j ∈ S, a j * b j) ^ 2 := sq_abs _
  have hld : 0 ≤ lam - δ := by linarith
  calc (lam - δ) * max (|⟪u, ψ⟫| - r / δ * ‖ψ‖) 0 ^ 2
      ≤ (lam - δ) * (‖u‖ ^ 2 * ∑ j ∈ S, b j ^ 2) :=
        mul_le_mul_of_nonneg_left (hmax.trans hcs) hld
    _ = ‖u‖ ^ 2 * ((lam - δ) * ∑ j ∈ S, b j ^ 2) := by ring
    _ ≤ ‖u‖ ^ 2 * positivePartForm e ev ψ := mul_le_mul_of_nonneg_left hpos (sq_nonneg _)

end PositivePart

/-! ### The positive-part four-trace bound -/

/-- **Positive-part form of the general spectral bound.** As
`spectral_four_trace_bound_general`, with `max(Q_P(w_k), 0)` replaced by `⟪Φ_P⁺ w_k, w_k⟫` for a
given diagonalisation `(e, λ)` of the pair form. -/
theorem spectral_four_trace_bound_positivePart [FiniteDimensional ℝ V]
    {κR κP ι : Type*} [Fintype κR] [Fintype κP] [Fintype ι] {n : ℕ}
    (cR : κR → ℝ) (wR : κR → V) (cP : κP → ℝ) (wP : κP → V) (g : ι → V) (NP : ℝ)
    (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
    (hdP : ∀ v, weightedForm cP wP v = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    (hc : ∀ k, cR k = 1 ∨ 2 ≤ cR k)
    (hcap : ∀ v, (∀ p, ⟪g p, v⟫ = 0) → weightedForm cP wP v ≤ 0)
    (hN : 2 * (Fintype.card ι : ℝ) ≤ NP) (M : Finset κR) (hM : ∀ k ∈ M, cR k = 1) :
    4 * (∑ k, cR k * ‖wR k‖ ^ 2 + ∑ l, cP l * ‖wP l‖ ^ 2)
        - (∑ k, cR k * (weightedForm cR wR (wR k) + weightedForm cP wP (wR k))
          + ∑ l, cP l * (weightedForm cR wR (wP l) + weightedForm cP wP (wP l)))
        - 2 * (∑ k, cR k + NP) + 2 * ∑ k ∈ M, positivePartForm e ev (wR k)
        + max (∑ l, cP l * ‖wP l‖ ^ 2 - 2 * Fintype.card ι) 0 ^ 2 / Fintype.card ι
      ≤ ∑ k, if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0 := by
  classical
  obtain ⟨f, μ, hdR⟩ := exists_weightedForm_diag cR wR
  set ν : Fin n → ℝ := fun j => max (-ev j) 0
  set Pp : κR → ℝ := fun k => positivePartForm e ev (wR k)
  have hER := sum_weight_mul_weightedForm_eq cR wR f μ hdR
  have htR := sum_weight_mul_norm_sq_eq cR wR f μ hdR
  have hEP := sum_weight_mul_weightedForm_eq cP wP e ev hdP
  have htP := sum_weight_mul_norm_sq_eq cP wP e ev hdP
  have hX := sum_weightedForm_comm cR wR cP wP
  have hXsplit : ∑ k, cR k * weightedForm cP wP (wR k) =
      ∑ k, cR k * Pp k - ∑ j, ν j * weightedForm cR wR (e j) := by
    have h1 : ∀ k, weightedForm cP wP (wR k) = Pp k - ∑ j, ν j * ⟪e j, wR k⟫ ^ 2 := fun k => by
      rw [hdP]
      simp only [Pp, positivePartForm, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases le_total 0 (ev j) with h | h
      · simp only [ν, max_eq_left h, max_eq_right (by linarith : -ev j ≤ 0)]; ring
      · simp only [ν, max_eq_right h, max_eq_left (by linarith : 0 ≤ -ev j)]; ring
    simp_rw [h1, mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp_rw [Finset.mul_sum, weightedForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [real_inner_comm]; ring
  have hXpos : ∑ k ∈ M, Pp k ≤ ∑ k, cR k * Pp k := by
    calc ∑ k ∈ M, Pp k = ∑ k ∈ M, cR k * Pp k :=
          Finset.sum_congr rfl fun k hk => by rw [hM k hk, one_mul]
      _ ≤ ∑ k, cR k * Pp k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M) fun k _ _ =>
            mul_nonneg (weight_pos_of_one_or_two_le cR hc k).le (positivePartForm_nonneg e ev _)
  have hreal := neg_le_sum_lamzouriFourExcess cR wR f μ hdR hc
  have hsplitR : ∑ k, (2 * cR k + if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0) =
      2 * ∑ k, cR k + ∑ k, (if cR k < 2 then 2 * ‖wR k‖ ^ 2 - 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hexc : ∑ i, lamzouriFourExcess (μ i) =
      ∑ i, μ i ^ 2 - 4 * ∑ i, μ i - ∑ i, max (μ i - 2) 0 ^ 2 := by
    simp only [lamzouriFourExcess, Finset.sum_sub_distrib, Finset.mul_sum]
  have hcount := card_positiveEigen_le cP wP g e ev hdP hcap
  have hpair := pair_energy_bound ev (Fintype.card ι) NP (by exact_mod_cast hcount) hN
  have hcross := two_mul_sum_le_cross cR wR f μ hdR e ν fun j => le_max_right _ _
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hER, hEP, hX, hXsplit, htR, htP]
  rw [hexc, hsplitR] at hreal
  linarith

namespace HorizontalPacket

variable {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP]
variable (P : HorizontalPacket V ι₂ ιH ιM ιP)

/-- **Positive-part horizontal Lamzouri inequality.** For any orthonormal diagonalisation
`(e, λ)` of the pair form `G`,
`4·mass − E − 2N + 2 Σ_{x ∈ M} ⟪Φ_P⁺ f_x, f_x⟫ + ((tr Φ_P − 2P)⁺)²/P
≤ Σ_H (2‖f‖² − 1) + Σ_M (2‖f‖² − 1)`. -/
theorem spectral_four_mass_bound_positivePart [FiniteDimensional ℝ V] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
    (hd : ∀ v, P.pairField v = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) :
    4 * P.mass - P.energy - 2 * P.count + 2 * ∑ x, positivePartForm e ev (P.fM x)
        + max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP
      ≤ ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
  classical
  set M : Finset (ι₂ ⊕ ιH ⊕ ιM) :=
    Finset.univ.map ⟨fun x => Sum.inr (Sum.inr x), fun x y h => by simpa using h⟩
  have hc : ∀ k, P.realWeight k = 1 ∨ 2 ≤ P.realWeight k := by
    rintro (i | j)
    · exact Or.inr (hm₂ i)
    · exact Or.inl rfl
  have hcap : ∀ v, (∀ p, ⟪P.g p, v⟫ = 0) → weightedForm P.pairWeight P.pairVec v ≤ 0 := by
    intro v hv
    rw [← P.pairField_eq, pairField]
    refine Finset.sum_nonpos fun p _ => ?_
    rw [hv p]
    have := hmP p
    nlinarith [sq_nonneg ⟪P.h p, v⟫]
  have hN : 2 * (Fintype.card ιP : ℝ) ≤ 2 * ∑ p, P.mP p := by
    have := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hmP p
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  have hMmem : ∀ k ∈ M, P.realWeight k = 1 := by
    intro k hk
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hk
    rfl
  have hdP : ∀ v, weightedForm P.pairWeight P.pairVec v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 :=
    fun v => by rw [← P.pairField_eq, hd]
  have hmain := spectral_four_trace_bound_positivePart P.realWeight P.realVec P.pairWeight
    P.pairVec P.g (2 * ∑ p, P.mP p) e ev hdP hc hcap hN M hMmem
  have hslack : (∑ k, if P.realWeight k < 2 then 2 * ‖P.realVec k‖ ^ 2 - 1 else 0) =
      ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) + ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) := by
    simp only [realWeight, realVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    have h₂ : ∀ i, ¬ P.m₂ i < 2 := fun i => not_lt.mpr (hm₂ i)
    simp [h₂]
  have hMsum : ∑ k ∈ M, positivePartForm e ev (P.realVec k) =
      ∑ x, positivePartForm e ev (P.fM x) := by
    rw [Finset.sum_map]
    rfl
  have hmass : P.mass = ∑ k, P.realWeight k * ‖P.realVec k‖ ^ 2 +
      ∑ l, P.pairWeight l * ‖P.pairVec l‖ ^ 2 := P.sum_wt_mul_split fun v => ‖v‖ ^ 2
  have henergy : P.energy =
      ∑ k, P.realWeight k * (weightedForm P.realWeight P.realVec (P.realVec k) +
          weightedForm P.pairWeight P.pairVec (P.realVec k)) +
        ∑ l, P.pairWeight l * (weightedForm P.realWeight P.realVec (P.pairVec l) +
          weightedForm P.pairWeight P.pairVec (P.pairVec l)) := by
    rw [P.energy_eq_sum_diagForm, P.sum_wt_mul_split P.diagForm]
    simp only [P.diagForm_eq_split]
  have hcountR : ∑ k, P.realWeight k + 2 * ∑ p, P.mP p = P.count := by
    simp only [count, realWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_sum, Nat.cast_add]
    ring
  have htrace : ∑ l, P.pairWeight l * ‖P.pairVec l‖ ^ 2 = P.pairTrace := by
    simp only [pairTrace, pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hslack, hMsum, ← hmass, ← henergy, hcountR, htrace] at hmain
  exact hmain

/-- **Positive-part free condition.** If every mixed point has `⟪Φ_P⁺ f_x, f_x⟫ ≥ ‖f_x‖² − 1/2`,
then `4·mass − E − 2N ≤ #H`. -/
theorem four_mass_sub_energy_le_of_positivePart [FiniteDimensional ℝ V] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
    (hd : ∀ v, P.pairField v = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) (hH : ∀ i, ‖P.fH i‖ ≤ 1)
    (hG : ∀ x, ‖P.fM x‖ ^ 2 - 1 / 2 ≤ positivePartForm e ev (P.fM x)) :
    4 * P.mass - P.energy - 2 * P.count ≤ (Fintype.card ιH : ℝ) := by
  have h := P.spectral_four_mass_bound_positivePart e ev hd hm₂ hmP
  have hb : 0 ≤ max (P.pairTrace - 2 * Fintype.card ιP) 0 ^ 2 / Fintype.card ιP := by positivity
  have hHsum : ∑ i, (2 * ‖P.fH i‖ ^ 2 - 1) ≤ (Fintype.card ιH : ℝ) := by
    have : ∀ i, 2 * ‖P.fH i‖ ^ 2 - 1 ≤ 1 := fun i => by
      have := hH i; nlinarith [norm_nonneg (P.fH i)]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => this i
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hs
  have hM : ∑ x, (2 * ‖P.fM x‖ ^ 2 - 1) ≤ 2 * ∑ x, positivePartForm e ev (P.fM x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => by linarith [hG x]
  linarith

omit [Fintype ι₂] [Fintype ιH] [Fintype ιM] in
/-- **Decoupled pairs.** If the even vector `g_p` is orthogonal to `h_p` and to `g_q, h_q` for every
other pair `q`, then `⟪Φ_P⁺ψ, ψ⟫ ≥ 2m_p⟪g_p, ψ⟫²` for every `ψ`, independently of the odd vectors
of the other pairs. -/
theorem positivePart_ge_of_decoupled {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ)
    (hd : ∀ v, P.pairField v = ∑ j, ev j * ⟪e j, v⟫ ^ 2) (hmP : ∀ p, 1 ≤ P.mP p) (p : ιP)
    (hgh : ⟪P.g p, P.h p⟫ = 0)
    (hgq : ∀ q, q ≠ p → ⟪P.g q, P.g p⟫ = 0 ∧ ⟪P.h q, P.g p⟫ = 0) (ψ : V) :
    2 * P.mP p * ⟪P.g p, ψ⟫ ^ 2 ≤ positivePartForm e ev ψ := by
  classical
  have hdP : ∀ v, weightedForm P.pairWeight P.pairVec v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 :=
    fun v => by rw [← P.pairField_eq, hd]
  set lam := 2 * P.mP p * ‖P.g p‖ ^ 2 with hlam
  have hlam0 : 0 ≤ lam := by have := hmP p; positivity
  -- `g_p` is an eigenvector of the pair form
  have hbil : ∀ v, ∑ l, P.pairWeight l * (⟪P.pairVec l, P.g p⟫ * ⟪P.pairVec l, v⟫) =
      lam * ⟪P.g p, v⟫ := by
    intro v
    simp only [pairWeight, pairVec, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single p]
    · have hhg : ⟪P.h p, P.g p⟫ = 0 := by rw [real_inner_comm]; exact hgh
      rw [hhg, real_inner_self_eq_norm_sq, hlam]; ring
    · intro q _ hq; rw [(hgq q hq).2]; ring
    · simp
    · intro q _ hq; rw [(hgq q hq).1]; ring
    · simp
  have heig : ∀ j, ev j * ⟪e j, P.g p⟫ = lam * ⟪e j, P.g p⟫ := by
    intro j
    have h := weightedBilin_eq e ev hdP (P.g p) (e j)
    rw [hbil] at h
    have hsum : ∑ i, ev i * (⟪e i, P.g p⟫ * ⟪e i, e j⟫) = ev j * ⟪e j, P.g p⟫ := by
      rw [Finset.sum_eq_single j]
      · rw [real_inner_self_eq_norm_sq, e.orthonormal.1 j]; ring
      · intro i _ hij; rw [e.orthonormal.2 hij]; ring
      · simp
    rw [hsum, real_inner_comm] at h
    linarith
  have hfloor := positivePartForm_ge_of_eigen e ev hlam0 heig ψ
  rcases eq_or_ne (P.g p) 0 with h0 | h0
  · rw [h0, inner_zero_left]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact positivePartForm_nonneg e ev ψ
  · have hn : 0 < ‖P.g p‖ ^ 2 := by positivity
    rw [hlam] at hfloor
    have : ‖P.g p‖ ^ 2 * (2 * P.mP p * ⟪P.g p, ψ⟫ ^ 2) ≤
        ‖P.g p‖ ^ 2 * positivePartForm e ev ψ := by linarith
    exact le_of_mul_le_mul_left this hn

end HorizontalPacket

end GaloisForLFunctions.HilbertMetric
