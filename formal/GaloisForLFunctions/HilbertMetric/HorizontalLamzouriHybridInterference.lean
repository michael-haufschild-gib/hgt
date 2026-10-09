import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriOddAngleCriterion

/-!
# Hybrid interference: large odd vectors by angle, small ones by weight

Let `Q(v) = α⟪u, v⟫² − Σ_{k∈L} b_k⟪h_k, v⟫² − Σ_{k∈S} b'_k⟪h'_k, v⟫²`, `α, b, b' ≥ 0`. The large
family `L` is controlled by an angle `κ`: `|⟪d, u⟫| ≤ κ‖d‖` on `span{h_k : k ∈ L}`. The small family
`S` is controlled only by its weighted overlaps
`Σ_{k∈S} b'_k (|⟪h'_k, u⟫| + ‖h'_k‖κ)² ≤ σ²`.

**Theorem** (`positivePartForm_ge_of_hybridInterference`). If `κ < ‖u‖` and
`0 < λ₀ ≤ α(‖u‖² − κ²) − σ²/(‖u‖² − κ²)`, then for every `f`
`α ((|⟪u, f⟫| − (κ + √(σ²/(4λ₀)))‖f‖)⁺)² ≤ ⟪Q⁺f, f⟫`.

No Gram condition on the small family is needed, and the large family enters only through the
angle `κ`. The interference therefore splits into a scale-free part (vectors larger than `u`, few)
and a weighted part (vectors smaller than `u`, possibly many).

**Proof.** Let `P` project onto `span h` and `v₀ = u − Pu`, so that `‖Pu‖ ≤ κ`,
`‖v₀‖² ≥ ‖u‖² − κ²` and `Q(v₀) ≥ λ₀‖v₀‖² > 0`. Hence `Q` has exactly one positive eigenvalue
`λ ≥ λ₀`, with eigenvector `z = λ(λ + B)⁻¹u` and `d = u − z`, where `B = Σ b h⊗h + Σ b' h'⊗h'`.
Split `d = d₁ + d₂`, where `(λ + B)d₁ = B Pu` and `(λ + B)d₂ = B v₀`. Then:
* `‖d₁‖ ≤ ‖Pu‖ ≤ κ`, because `⟪d₁, Pu − d₁⟫ ≥ 0`;
* `‖d₂‖² ≤ ⟪Bv₀, v₀⟫/(4λ) ≤ σ²/(4λ₀)`, by Cauchy–Schwarz for `B` and `√(ab) − a ≤ b/4`;
  here `⟪Bv₀, v₀⟫` only sees the small family, since `v₀ ⊥ span h`.

The positive part at `f` is then at least `α⟪z, f⟫² ≥ α(|⟪u, f⟫| − ‖d‖‖f‖)²`.
-/

open scoped RealInnerProductSpace
open Finset Module

noncomputable section

namespace GaloisForLFunctions.HilbertMetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Cauchy–Schwarz for a nonnegative weighted family:
`(Σ c_k a_k b_k)² ≤ (Σ c_k a_k²)(Σ c_k b_k²)`. -/
theorem sq_sum_weight_mul_le {ι : Type*} (s : Finset ι) {c a b : ι → ℝ}
    (hc : ∀ k, 0 ≤ c k) :
    (∑ k ∈ s, c k * (a k * b k)) ^ 2 ≤ (∑ k ∈ s, c k * a k ^ 2) * ∑ k ∈ s, c k * b k ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => Real.sqrt (c k) * a k)
    (fun k => Real.sqrt (c k) * b k)
  have e1 : ∀ k, Real.sqrt (c k) * a k * (Real.sqrt (c k) * b k) = c k * (a k * b k) := fun k => by
    rw [show Real.sqrt (c k) * a k * (Real.sqrt (c k) * b k) =
      (Real.sqrt (c k) * Real.sqrt (c k)) * (a k * b k) by ring, Real.mul_self_sqrt (hc k)]
  have e2 : ∀ k (x : ι → ℝ), (Real.sqrt (c k) * x k) ^ 2 = c k * x k ^ 2 := fun k x => by
    rw [mul_pow, Real.sq_sqrt (hc k)]
  simp only [e1, e2] at h
  exact h

/-! ### The resolvent split -/

section Resolvent

variable {ι : Type*} [Fintype ι] (cB : ι → ℝ) (wB : ι → V)

omit [FiniteDimensional ℝ V] in
theorem weightedOp_inner_nonneg (hcB0 : ∀ k, 0 ≤ cB k) (v : V) :
    0 ≤ ⟪weightedOp cB wB v, v⟫ := by
  rw [inner_weightedOp_self]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hcB0 k) (sq_nonneg _)

omit [FiniteDimensional ℝ V] in
theorem weightedOp_inner_sq_le (hcB0 : ∀ k, 0 ≤ cB k) (x v : V) :
    ⟪weightedOp cB wB x, v⟫ ^ 2 ≤ ⟪weightedOp cB wB x, x⟫ * ⟪weightedOp cB wB v, v⟫ := by
  rw [inner_weightedOp_left, inner_weightedOp_left, inner_weightedOp_left]
  have h := sq_sum_weight_mul_le Finset.univ (c := cB) (a := fun k => ⟪wB k, x⟫)
    (b := fun k => ⟪wB k, v⟫) hcB0
  have e1 : ∀ y z, ∑ k, cB k * ⟪wB k, y⟫ * ⟪wB k, z⟫ =
      ∑ k, cB k * (⟪wB k, y⟫ * ⟪wB k, z⟫) := fun y z =>
    Finset.sum_congr rfl fun k _ => by ring
  rw [e1, e1, e1]
  have e2 : ∀ y, ∑ k, cB k * (⟪wB k, y⟫ * ⟪wB k, y⟫) = ∑ k, cB k * ⟪wB k, y⟫ ^ 2 := fun y =>
    Finset.sum_congr rfl fun k _ => by ring
  rw [e2, e2]
  exact h

/-- **Resolvent split.** If `λ > 0` and `λd + Bd = Bu` for a nonnegative weighted operator `B`,
then for any `p`: `‖d‖ ≤ ‖p‖ + √(⟪B(u − p), u − p⟫/(4λ))`. -/
theorem norm_le_of_resolvent (hcB0 : ∀ k, 0 ≤ cB k) {lam : ℝ}
    (hlam : 0 < lam) {u pu d : V}
    (hd : lam • d + weightedOp cB wB d = weightedOp cB wB u) :
    ‖d‖ ≤ ‖pu‖ + Real.sqrt (⟪weightedOp cB wB (u - pu), u - pu⟫ / (4 * lam)) := by
  set Bop := weightedOp cB wB with hBop
  set Tm : V →ₗ[ℝ] V := lam • LinearMap.id + Bop with hTm
  have hTapply : ∀ v, Tm v = lam • v + Bop v := fun v => by simp [hTm]
  have hTinj : Function.Injective Tm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : ⟪Tm v, v⟫ = 0 := by rw [hv, inner_zero_left]
    rw [hTapply, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h1
    have h2 := weightedOp_inner_nonneg cB wB hcB0 v
    have h3 : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3)
  obtain ⟨d₁, hd₁⟩ := (LinearMap.injective_iff_surjective.mp hTinj) (Bop pu)
  obtain ⟨v0, hv0⟩ : ∃ v0 : V, v0 = u - pu := ⟨_, rfl⟩
  rw [← hv0]
  obtain ⟨d₂, hd₂⟩ : ∃ d₂ : V, d₂ = d - d₁ := ⟨_, rfl⟩
  have hTd₂ : Tm d₂ = Bop v0 := by
    rw [hd₂, map_sub, hTapply d, hd, hd₁, hv0, map_sub]
  -- `‖d₁‖ ≤ ‖p‖`
  have hd₁n : ‖d₁‖ ≤ ‖pu‖ := by
    have h1 : lam • d₁ = Bop (pu - d₁) := by
      rw [map_sub, ← hd₁, hTapply]; abel
    have h2 : 0 ≤ ⟪d₁, pu - d₁⟫ := by
      have := weightedOp_inner_nonneg cB wB hcB0 (pu - d₁)
      rw [← hBop, ← h1, real_inner_smul_left] at this
      exact (mul_nonneg_iff_of_pos_left hlam).mp this
    rw [inner_sub_right, real_inner_self_eq_norm_sq] at h2
    have h3 := real_inner_le_norm d₁ pu
    rcases eq_or_lt_of_le (norm_nonneg d₁) with h0 | hpos
    · rw [← h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_left (by nlinarith) hpos
  -- `‖d₂‖² ≤ ⟪Bv₀, v₀⟫/(4λ)`
  have hd₂n : ‖d₂‖ ^ 2 ≤ ⟪Bop v0, v0⟫ / (4 * lam) := by
    obtain ⟨x, hx⟩ : ∃ x : V, x = v0 - d₂ := ⟨_, rfl⟩
    have h1 : lam • d₂ = Bop x := by
      rw [hx, map_sub, ← hTd₂, hTapply]; abel
    have h2 : lam * ‖d₂‖ ^ 2 = ⟪Bop x, v0⟫ - ⟪Bop x, x⟫ := by
      rw [← h1, real_inner_smul_left, real_inner_smul_left, hx, inner_sub_right,
        real_inner_self_eq_norm_sq]
      ring
    have hcs := weightedOp_inner_sq_le cB wB hcB0 x v0
    have hxx := weightedOp_inner_nonneg cB wB hcB0 x
    have hvv := weightedOp_inner_nonneg cB wB hcB0 v0
    have h3 : ⟪Bop x, v0⟫ - ⟪Bop x, x⟫ ≤ ⟪Bop v0, v0⟫ / 4 := by
      have hsq : ⟪Bop x, v0⟫ ^ 2 ≤ (⟪Bop x, x⟫ + ⟪Bop v0, v0⟫ / 4) ^ 2 := by
        nlinarith [sq_nonneg (⟪Bop x, x⟫ - ⟪Bop v0, v0⟫ / 4)]
      have := (abs_le_of_sq_le_sq' hsq (by linarith)).2
      linarith
    rw [div_mul_eq_div_div, le_div_iff₀ hlam]
    nlinarith
  have hsplit : d = d₁ + d₂ := by rw [hd₂]; abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hd₁n (Real.le_sqrt_of_sq_le hd₂n))

end Resolvent

/-! ### The eigenvector floor with a residual -/

omit [FiniteDimensional ℝ V] in
/-- **Eigenvector floor.** Let `Q(v) = α⟪u, v⟫² − ⟪Bv, v⟫` (with `B ≥ 0` weighted) be diagonalised by
`(e, λ)`, with exactly one positive eigenvalue `λ_{j₀}`. Then there is `d` with
`λ_{j₀}d + Bd = Bu` and `α((|⟪u, f⟫| − ‖d‖‖f‖)⁺)² ≤ ⟪Q⁺f, f⟫` for every `f`. -/
theorem exists_resolvent_floor {ι : Type*} [Fintype ι] {n : ℕ}
    (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) (u : V)
    (cB : ι → ℝ) (hcB0 : ∀ k, 0 ≤ cB k) (wB : ι → V)
    (hd : ∀ v, α * ⟪u, v⟫ ^ 2 - ⟪weightedOp cB wB v, v⟫ = ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    {j₀ : Fin n} (hj₀ : 0 < ev j₀) (honly : ∀ j, j ≠ j₀ → ev j ≤ 0) :
    ∃ d : V, ev j₀ • d + weightedOp cB wB d = weightedOp cB wB u ∧
      ∀ f, α * max (|⟪u, f⟫| - ‖d‖ * ‖f‖) 0 ^ 2 ≤ positivePartForm e ev f := by
  classical
  set Bop := weightedOp cB wB with hBop
  set lam := ev j₀ with hlam
  set w₀ := e j₀ with hw₀
  have hw₀n : ‖w₀‖ = 1 := e.orthonormal.1 j₀
  -- polarisation
  have hpol : ∀ v x, α * (⟪u, v⟫ * ⟪u, x⟫) - ⟪Bop v, x⟫ =
      ∑ j, ev j * (⟪e j, v⟫ * ⟪e j, x⟫) := fun v x => by
    set c : Unit ⊕ ι → ℝ := Sum.elim (fun _ => α) fun k => -cB k
    set w : Unit ⊕ ι → V := Sum.elim (fun _ => u) wB
    have hdw : ∀ v, weightedForm c w v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := fun v => by
      rw [← hd, hBop, inner_weightedOp_self]
      simp only [weightedForm, c, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [← weightedBilin_eq e ev hdw v x, hBop, inner_weightedOp_left]
    simp only [c, w, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    have : ∑ k, cB k * ⟪wB k, v⟫ * ⟪wB k, x⟫ = ∑ k, cB k * (⟪wB k, v⟫ * ⟪wB k, x⟫) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [this]
    ring
  have hPp : ∀ f, positivePartForm e ev f = lam * ⟪w₀, f⟫ ^ 2 := fun f => by
    unfold positivePartForm
    rw [Finset.sum_eq_single j₀]
    · rw [max_eq_left hj₀.le]
    · intro j _ hj; rw [max_eq_right (honly j hj)]; ring
    · simp
  set s := α * ⟪u, w₀⟫ with hs
  have heig : s • u - Bop w₀ = lam • w₀ := by
    refine ext_inner_right ℝ fun x => ?_
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left]
    have h1 := hpol w₀ x
    have h2 : ∑ j, ev j * (⟪e j, w₀⟫ * ⟪e j, x⟫) = lam * ⟪w₀, x⟫ := by
      rw [Finset.sum_eq_single j₀]
      · rw [hw₀, real_inner_self_eq_norm_sq, e.orthonormal.1 j₀]; ring
      · intro j _ hj; rw [hw₀, e.orthonormal.2 hj]; ring
      · simp
    rw [h2] at h1
    rw [hs]
    linarith
  have hBw : Bop w₀ = s • u - lam • w₀ := by rw [← heig]; abel
  have hs0 : s ≠ 0 := by
    intro hs0
    have h1 : ⟪Bop w₀, w₀⟫ = -lam := by
      rw [hBw, hs0, zero_smul, zero_sub, inner_neg_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hw₀n]
      ring
    linarith [weightedOp_inner_nonneg cB wB hcB0 w₀]
  obtain ⟨z, hz⟩ : ∃ z : V, z = (lam / s) • w₀ := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : V, d = u - z := ⟨_, rfl⟩
  have hss : lam / s * s = lam := div_mul_cancel₀ lam hs0
  have hdB : lam • d = Bop z := by
    have e1 : (lam / s) • (s • u - lam • w₀) = lam • u - (lam * (lam / s)) • w₀ := by
      rw [smul_sub, smul_smul, smul_smul, hss, mul_comm]
    rw [hdd, hz, map_smul, hBw, e1, smul_sub, smul_smul]
  refine ⟨d, ?_, fun f => ?_⟩
  · rw [hdB, ← map_add]
    congr 1
    rw [hdd]; abel
  have hdz : 0 ≤ ⟪d, z⟫ := by
    have : lam * ⟪d, z⟫ = ⟪Bop z, z⟫ := by rw [← hdB, real_inner_smul_left]
    exact (mul_nonneg_iff_of_pos_left hj₀).mp (this ▸ weightedOp_inner_nonneg cB wB hcB0 z)
  have huz : ‖z‖ ^ 2 ≤ ⟪u, z⟫ := by
    have : ⟪u, z⟫ = ‖z‖ ^ 2 + ⟪d, z⟫ := by
      rw [hdd, inner_sub_left, real_inner_self_eq_norm_sq]; ring
    linarith
  have hlamz : lam = α * ⟪u, z⟫ := by
    have : α * ⟪u, z⟫ = lam / s * s := by rw [hz, real_inner_smul_right, hs]; ring
    rw [this, hss]
  have hne : lam / s ≠ 0 := div_ne_zero hj₀.ne' hs0
  have hzn : ‖z‖ ^ 2 = (lam / s) ^ 2 := by
    rw [hz, norm_smul, hw₀n, mul_one, Real.norm_eq_abs, sq_abs]
  have hzpos : 0 < ‖z‖ ^ 2 := by
    rw [hzn]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have hwf : ⟪w₀, f⟫ ^ 2 = ⟪z, f⟫ ^ 2 / ‖z‖ ^ 2 := by
    rw [hzn, hz, real_inner_smul_left, mul_pow]
    field_simp
  have hmain : α * ⟪z, f⟫ ^ 2 ≤ positivePartForm e ev f := by
    rw [hPp, hwf, mul_div_assoc', le_div_iff₀ hzpos, hlamz]
    have := mul_le_mul_of_nonneg_left huz (mul_nonneg hα (sq_nonneg ⟪z, f⟫))
    nlinarith
  have hzf : max (|⟪u, f⟫| - ‖d‖ * ‖f‖) 0 ^ 2 ≤ ⟪z, f⟫ ^ 2 := by
    rcases le_total (|⟪u, f⟫| - ‖d‖ * ‖f‖) 0 with hle | hle
    · rw [max_eq_right hle]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg _
    · rw [max_eq_left hle]
      have hu : ⟪u, f⟫ = ⟪z, f⟫ + ⟪d, f⟫ := by rw [hdd, inner_sub_left]; ring
      have hdf : |⟪d, f⟫| ≤ ‖d‖ * ‖f‖ := abs_real_inner_le_norm d f
      have : |⟪u, f⟫| - ‖d‖ * ‖f‖ ≤ |⟪z, f⟫| := by
        rw [hu]; linarith [abs_add_le ⟪z, f⟫ ⟪d, f⟫]
      calc (|⟪u, f⟫| - ‖d‖ * ‖f‖) ^ 2 ≤ |⟪z, f⟫| ^ 2 := pow_le_pow_left₀ hle this 2
        _ = ⟪z, f⟫ ^ 2 := sq_abs _
  exact (mul_le_mul_of_nonneg_left hzf hα).trans hmain

/-! ### The hybrid floor -/

/-- **Hybrid interference floor.** -/
theorem positivePartForm_ge_of_hybridInterference {ιL ιS : Type*} [Fintype ιL] [Fintype ιS]
    {n : ℕ} (e : OrthonormalBasis (Fin n) ℝ V) (ev : Fin n → ℝ) {α : ℝ} (hα : 0 ≤ α) (u : V)
    (bL : ιL → ℝ) (hbL : ∀ k, 0 ≤ bL k) (hL : ιL → V)
    (bS : ιS → ℝ) (hbS : ∀ k, 0 ≤ bS k) (hS : ιS → V)
    (hd : ∀ v, α * ⟪u, v⟫ ^ 2 - ∑ k, bL k * ⟪hL k, v⟫ ^ 2 - ∑ k, bS k * ⟪hS k, v⟫ ^ 2 =
      ∑ j, ev j * ⟪e j, v⟫ ^ 2)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : ∀ d ∈ Submodule.span ℝ (Set.range hL), |⟪d, u⟫| ≤ κ * ‖d‖)
    {σ2 lam0 : ℝ} (hσ : ∑ k, bS k * (|⟪hS k, u⟫| + ‖hS k‖ * κ) ^ 2 ≤ σ2)
    (hgap : κ ^ 2 < ‖u‖ ^ 2) (hlam0 : 0 < lam0)
    (hlam0le : lam0 ≤ α * (‖u‖ ^ 2 - κ ^ 2) - σ2 / (‖u‖ ^ 2 - κ ^ 2)) (f : V) :
    α * max (|⟪u, f⟫| - (κ + Real.sqrt (σ2 / (4 * lam0))) * ‖f‖) 0 ^ 2 ≤
      positivePartForm e ev f := by
  classical
  have hσ0 : 0 ≤ σ2 := le_trans (Finset.sum_nonneg fun k _ =>
    mul_nonneg (hbS k) (sq_nonneg _)) hσ
  set cB : ιL ⊕ ιS → ℝ := Sum.elim bL bS with hcB
  set wB : ιL ⊕ ιS → V := Sum.elim hL hS with hwB
  have hcB0 : ∀ k, 0 ≤ cB k := by rintro (k | k); exacts [hbL k, hbS k]
  have hBform : ∀ v, ⟪weightedOp cB wB v, v⟫ =
      ∑ k, bL k * ⟪hL k, v⟫ ^ 2 + ∑ k, bS k * ⟪hS k, v⟫ ^ 2 := fun v => by
    rw [inner_weightedOp_self]
    simp only [weightedForm, cB, wB, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have hd' : ∀ v, α * ⟪u, v⟫ ^ 2 - ⟪weightedOp cB wB v, v⟫ = ∑ j, ev j * ⟪e j, v⟫ ^ 2 :=
    fun v => by rw [hBform, ← hd]; ring
  -- the projection onto the large span
  set K := Submodule.span ℝ (Set.range hL) with hK
  set pu := K.starProjection u with hpu
  set v0 := u - pu with hv0
  have hpuK : pu ∈ K := K.starProjection_apply_mem u
  have hv0K : ∀ x ∈ K, ⟪v0, x⟫ = 0 := fun x hx => Submodule.starProjection_inner_eq_zero u x hx
  have hv0L : ∀ k, ⟪hL k, v0⟫ = 0 := fun k => by
    rw [real_inner_comm]; exact hv0K _ (Submodule.subset_span (Set.mem_range_self k))
  have hpuv0 : ⟪pu, v0⟫ = 0 := by rw [real_inner_comm]; exact hv0K pu hpuK
  have hu_eq : u = pu + v0 := by rw [hv0]; abel
  have hpunorm : ‖pu‖ ≤ κ := by
    have h1 : ‖pu‖ ^ 2 = ⟪pu, u⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      conv_rhs => rw [hu_eq]
      rw [inner_add_right, hpuv0, add_zero]
    have h2 := hκ pu hpuK
    rcases eq_or_lt_of_le (norm_nonneg pu) with h0 | hpos
    · rw [← h0]; exact hκ0
    · have : ‖pu‖ ^ 2 ≤ κ * ‖pu‖ := by rw [h1]; exact (le_abs_self _).trans h2
      nlinarith
  have hpyth : ‖u‖ ^ 2 = ‖pu‖ ^ 2 + ‖v0‖ ^ 2 := by
    rw [hu_eq, norm_add_sq_real, hpuv0]; ring
  set t := ‖v0‖ ^ 2 with ht
  set m := ‖u‖ ^ 2 - κ ^ 2 with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  have htm : m ≤ t := by rw [hm, ht]; nlinarith [hpunorm, norm_nonneg pu]
  have ht0 : 0 < t := lt_of_lt_of_le hm0 htm
  -- the small overlaps along `v₀`
  have hSv0 : ∑ k, bS k * ⟪hS k, v0⟫ ^ 2 ≤ σ2 := by
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) hσ
    refine mul_le_mul_of_nonneg_left ?_ (hbS k)
    have h1 : |⟪hS k, v0⟫| ≤ |⟪hS k, u⟫| + ‖hS k‖ * κ := by
      rw [hv0, inner_sub_right]
      refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hpunorm (norm_nonneg _))
    calc ⟪hS k, v0⟫ ^ 2 = |⟪hS k, v0⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (|⟪hS k, u⟫| + ‖hS k‖ * κ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hBv0 : ⟪weightedOp cB wB v0, v0⟫ ≤ σ2 := by
    rw [hBform]
    simp only [hv0L, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero, zero_add]
    exact hSv0
  have huv0 : ⟪u, v0⟫ = t := by
    rw [ht, ← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hu_eq]
    rw [inner_add_left, hpuv0, zero_add]
  have hQv0 : lam0 * t ≤ ∑ j, ev j * ⟪e j, v0⟫ ^ 2 := by
    rw [← hd' v0, huv0]
    have h1 : lam0 * t ≤ (α * m - σ2 / m) * t :=
      mul_le_mul_of_nonneg_right (by rw [hm]; linarith [hlam0le]) ht0.le
    have h2 : σ2 ≤ σ2 / m * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
      exact mul_le_mul_of_nonneg_left htm hσ0
    have h3 : α * m * t ≤ α * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left htm (mul_nonneg hα ht0.le)
      nlinarith
    nlinarith
  -- the unique positive eigenvalue dominates `λ₀`
  have hcap : ∀ v, (∀ _p : Unit, ⟪u, v⟫ = 0) →
      weightedForm (Sum.elim (fun _ : Unit => α) fun k => -cB k)
        (Sum.elim (fun _ : Unit => u) wB) v ≤ 0 := fun v hv => by
    have : weightedForm (Sum.elim (fun _ : Unit => α) fun k => -cB k)
        (Sum.elim (fun _ : Unit => u) wB) v = α * ⟪u, v⟫ ^ 2 - ⟪weightedOp cB wB v, v⟫ := by
      rw [inner_weightedOp_self]
      simp only [weightedForm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [this, hv ()]
    have := weightedOp_inner_nonneg cB wB hcB0 v
    nlinarith
  have hdw : ∀ v, weightedForm (Sum.elim (fun _ : Unit => α) fun k => -cB k)
      (Sum.elim (fun _ : Unit => u) wB) v = ∑ j, ev j * ⟪e j, v⟫ ^ 2 := fun v => by
    rw [← hd' v, inner_weightedOp_self]
    simp only [weightedForm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Finset.univ_unique, Finset.sum_singleton, neg_mul, Finset.sum_neg_distrib]
    ring
  have hcard := card_positiveEigen_le _ _ (fun _ : Unit => u) e ev hdw hcap
  rw [Fintype.card_unit] at hcard
  obtain ⟨j₀, hj₀⟩ : ∃ j, 0 < ev j := by
    by_contra hcon
    push Not at hcon
    have : ∑ j, ev j * ⟪e j, v0⟫ ^ 2 ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (hcon j) (sq_nonneg _)
    nlinarith [mul_pos hlam0 ht0]
  have honly : ∀ j, j ≠ j₀ → ev j ≤ 0 := fun j hj => by
    by_contra hcon
    push Not at hcon
    exact hj (Finset.card_le_one.mp hcard j (by simp [hcon]) j₀ (by simp [hj₀]))
  have hlamge : lam0 ≤ ev j₀ := by
    have h1 : ∑ j, ev j * ⟪e j, v0⟫ ^ 2 ≤ ev j₀ * t := by
      rw [ht, ← sum_sq_inner_orthonormalBasis e v0, Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rcases eq_or_ne j j₀ with h | h
      · rw [h]
      · linarith [honly j h]
    exact le_of_mul_le_mul_right (hQv0.trans h1) ht0
  -- the floor
  obtain ⟨d, hdres, hfloor⟩ := exists_resolvent_floor e ev hα u cB hcB0 wB hd' hj₀ honly
  have hdn := norm_le_of_resolvent cB wB hcB0 hj₀ (pu := pu) hdres
  have hdn' : ‖d‖ ≤ κ + Real.sqrt (σ2 / (4 * lam0)) := by
    refine hdn.trans (add_le_add hpunorm (Real.sqrt_le_sqrt ?_))
    rw [show u - pu = v0 from rfl]
    have h4 : 0 < 4 * lam0 := by linarith
    calc ⟪weightedOp cB wB v0, v0⟫ / (4 * ev j₀) ≤ σ2 / (4 * ev j₀) :=
          div_le_div_of_nonneg_right hBv0 (by linarith)
      _ ≤ σ2 / (4 * lam0) := div_le_div_of_nonneg_left hσ0 h4 (by linarith)
  refine le_trans ?_ (hfloor f)
  refine mul_le_mul_of_nonneg_left ?_ hα
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le_max ?_ le_rfl) 2
  have := mul_le_mul_of_nonneg_right hdn' (norm_nonneg f)
  linarith

end GaloisForLFunctions.HilbertMetric
