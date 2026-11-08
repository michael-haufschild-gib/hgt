import Mathlib

/-!
# The critical weight: what survives of a positive count as `δ → 0`

A count at weight `δ > 0` can be positive for two different reasons, and only one of them survives
the passage to the critical weight `δ = 0`.

**Damping is lossless.** The damping weight `ρ^{|ν|}`, `ρ = e^{−δ}`, is Toeplitz positive for
`0 ≤ ρ ≤ 1` (`toeplitz_dampWeight_posSemidef`, the Kac–Murdock–Szegő matrices, by an explicit
rank-one decomposition). By the Schur product theorem damping preserves Toeplitz positivity
(`toeplitzPositive_damp`), and conversely positivity of every damped kernel forces positivity of the
undamped one (`toeplitzPositive_of_damped`). So a count that is a damping of a positive object at
every `δ > 0` is positive at `δ = 0`, with no loss: its sign is decided at the critical weight.
A critical layer — unimodular modes with nonnegative weights — is Toeplitz positive
(`toeplitzPositive_criticalLayer`), so its damped counts are positive at every weight.

**Renormalization carries no sign.** A raw count that is positive at `δ > 0` only after a diagonal
self-energy `c(δ) → ∞` has been added says nothing at `δ = 0`: for every real symmetric form `Q`,
`Q + c(δ)·1` is eventually positive semidefinite while `(Q + c(δ)·1) − c(δ)·1 = Q`
(`eventually_posSemidef_add_counterterm`), and `Q` may be indefinite (`not_posSemidef_swap`). The
renormalized torsion forms on `ℓ²(n^δ)` are of this second kind: raw positive, renormalized by a
logarithmic counterterm, indefinite in the limit. A count at the critical weight must therefore be
of the first kind, a damping of something positive, not a renormalization.
-/

open Matrix Complex Finset Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

/-- The Toeplitz matrix `[k(i − j)]` of a kernel on the levels `0, …, n − 1`. -/
def toeplitz (k : ℤ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j => k ((i : ℤ) - j)

/-- A kernel is **Toeplitz positive** if all its Toeplitz matrices are positive semidefinite. -/
def ToeplitzPositive (k : ℤ → ℂ) : Prop := ∀ n, (toeplitz k n).PosSemidef

/-- The damping weight `ρ^{|ν|}`. -/
def dampWeight (ρ : ℝ) (ν : ℤ) : ℂ := ((ρ ^ ν.natAbs : ℝ) : ℂ)

/-- The Kac–Murdock–Szegő coefficients `c₀ = 1`, `c_k = 1 − ρ²` for `k ≥ 1`. -/
def kmsCoeff (ρ : ℝ) (k : ℕ) : ℝ := if k = 0 then 1 else 1 - ρ ^ 2

/-- `Σ_{k ≤ m} c_k ρ^{d + 2(m − k)} = ρ^d`. -/
theorem sum_kmsCoeff (ρ : ℝ) : ∀ m d : ℕ,
    ∑ k ∈ range (m + 1), kmsCoeff ρ k * ρ ^ (d + 2 * (m - k)) = ρ ^ d
  | 0, d => by simp [kmsCoeff]
  | m + 1, d => by
    rw [Finset.sum_range_succ]
    have hIH := sum_kmsCoeff ρ m (d + 2)
    have hrw : ∑ k ∈ range (m + 1), kmsCoeff ρ k * ρ ^ (d + 2 * (m + 1 - k)) =
        ∑ k ∈ range (m + 1), kmsCoeff ρ k * ρ ^ (d + 2 + 2 * (m - k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      congr 2
      omega
    rw [hrw, hIH, kmsCoeff, if_neg (Nat.succ_ne_zero m), Nat.sub_self, mul_zero, add_zero,
      pow_add]
    ring

/-- The rank-one vector `v_k = (ρ^{i−k})_{i ≥ k}`. -/
def kmsVec (ρ : ℝ) (n : ℕ) (k : Fin n) : Fin n → ℂ :=
  fun i => if (k : ℕ) ≤ i then ((ρ ^ ((i : ℕ) - k) : ℝ) : ℂ) else 0

theorem kms_entry (ρ : ℝ) (n : ℕ) (i j : Fin n) :
    ∑ k : Fin n, (kmsCoeff ρ k : ℂ) * (kmsVec ρ n k i * star (kmsVec ρ n k j)) =
      dampWeight ρ ((i : ℤ) - j) := by
  -- reduce to the closed form with `m = min i j`, `d = |i − j|`
  have hstar : ∀ k : Fin n, star (kmsVec ρ n k j) = kmsVec ρ n k j := fun k => by
    unfold kmsVec; split_ifs <;> simp [Complex.conj_ofReal]
  simp_rw [hstar]
  have hterm : ∀ k : Fin n, (kmsCoeff ρ k : ℂ) * (kmsVec ρ n k i * kmsVec ρ n k j) =
      if (k : ℕ) ≤ min (i : ℕ) j then
        (((kmsCoeff ρ k) * ρ ^ (((i : ℤ) - j).natAbs + 2 * (min (i : ℕ) j - k)) : ℝ) : ℂ)
      else 0 := by
    intro k
    unfold kmsVec
    by_cases hki : (k : ℕ) ≤ i <;> by_cases hkj : (k : ℕ) ≤ j
    · rw [if_pos hki, if_pos hkj, if_pos (le_min hki hkj)]
      push_cast
      rw [← pow_add]
      congr 2
      omega
    all_goals simp [hki, hkj]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hmin : min (i : ℕ) j < n := lt_of_le_of_lt (min_le_left _ _) i.2
  -- the filter is `{k < n : k ≤ min i j}`, i.e. `range (min i j + 1)`
  have hsum : ∑ k ∈ (univ : Finset (Fin n)).filter (fun k : Fin n => (k : ℕ) ≤ min (i : ℕ) j),
      ((kmsCoeff ρ k * ρ ^ (((i : ℤ) - j).natAbs + 2 * (min (i : ℕ) j - k)) : ℝ) : ℂ) =
      ∑ k ∈ range (min (i : ℕ) j + 1),
        ((kmsCoeff ρ k * ρ ^ (((i : ℤ) - j).natAbs + 2 * (min (i : ℕ) j - k)) : ℝ) : ℂ) := by
    refine Finset.sum_bij (fun k _ => (k : ℕ)) (fun k hk => ?_) (fun a _ b _ h => Fin.ext h)
      (fun b hb => ⟨⟨b, by have := Finset.mem_range.1 hb; omega⟩, ?_, rfl⟩) (fun _ _ => rfl)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 hb)
  rw [hsum, ← Complex.ofReal_sum, sum_kmsCoeff, dampWeight]

/-- **Kac–Murdock–Szegő.** The damping weight `ρ^{|ν|}` is Toeplitz positive for `0 ≤ ρ ≤ 1`. -/
theorem toeplitz_dampWeight_posSemidef {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) :
    (toeplitz (dampWeight ρ) n).PosSemidef := by
  have heq : toeplitz (dampWeight ρ) n =
      ∑ k : Fin n, (kmsCoeff ρ k) • vecMulVec (kmsVec ρ n k) (star (kmsVec ρ n k)) := by
    ext i j
    rw [Matrix.sum_apply, toeplitz, ← kms_entry]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Complex.real_smul]
  rw [heq]
  refine posSemidef_sum _ fun k _ => (posSemidef_vecMulVec_self_star _).smul ?_
  unfold kmsCoeff
  split_ifs
  · exact zero_le_one
  · nlinarith

/-- **Damping preserves Toeplitz positivity** (Schur product theorem). -/
theorem toeplitzPositive_damp {k : ℤ → ℂ} (hk : ToeplitzPositive k) {ρ : ℝ} (h0 : 0 ≤ ρ)
    (h1 : ρ ≤ 1) : ToeplitzPositive fun ν => dampWeight ρ ν * k ν := by
  intro n
  have : toeplitz (fun ν => dampWeight ρ ν * k ν) n =
      (toeplitz (dampWeight ρ) n).hadamard (toeplitz k n) := by
    ext i j; rfl
  rw [this]
  exact (toeplitz_dampWeight_posSemidef h0 h1 n).hadamard (hk n)

theorem dampWeight_one (ν : ℤ) : dampWeight 1 ν = 1 := by simp [dampWeight]

/-- **Damping is lossless.** A Hermitian kernel all of whose damped kernels, `0 < ρ < 1`, are
Toeplitz positive is Toeplitz positive. -/
theorem toeplitzPositive_of_damped {k : ℤ → ℂ} (hherm : ∀ ν, k (-ν) = starRingEnd ℂ (k ν))
    (h : ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ToeplitzPositive fun ν => dampWeight ρ ν * k ν) :
    ToeplitzPositive k := by
  intro n
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [conjTranspose_apply, toeplitz]
    rw [show ((j : ℤ) - i) = -((i : ℤ) - j) by ring, hherm, RCLike.star_def, Complex.conj_conj]
  · set f : ℝ → ℂ := fun ρ =>
      star x ⬝ᵥ (toeplitz (fun ν => dampWeight ρ ν * k ν) n) *ᵥ x with hf
    have hcont : Continuous f := by
      simp only [hf, dotProduct, mulVec, toeplitz, dampWeight]
      fun_prop
    have hf1 : f 1 = star x ⬝ᵥ (toeplitz k n) *ᵥ x := by
      simp only [hf, dampWeight_one, one_mul]
    have hmem : ∀ᶠ ρ in 𝓝[Set.Ioo 0 1] (1 : ℝ), f ρ ∈ Set.Ici (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact ((posSemidef_iff_dotProduct_mulVec.1 (h ρ hρ.1 hρ.2 n)).2 x)
    have hne : (𝓝[Set.Ioo 0 1] (1 : ℝ)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]
      exact ⟨zero_le_one, le_rfl⟩
    have := isClosed_Ici.mem_of_tendsto ((hcont.tendsto 1).mono_left nhdsWithin_le_nhds) hmem
    rw [← hf1]
    exact this

/-- **A critical layer is Toeplitz positive.** Unimodular modes `z_i` with nonnegative weights
`b_i`: the kernel `Σ_i b_i z_iᵛ` is Toeplitz positive. -/
theorem toeplitzPositive_criticalLayer {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1) (b : ι → ℝ) (hb : ∀ i ∈ s, 0 ≤ b i) :
    ToeplitzPositive fun ν => ∑ i ∈ s, (b i : ℂ) * z i ^ ν := by
  intro n
  have hz0 : ∀ i ∈ s, z i ≠ 0 := fun i hi h => by simpa [h] using hz i hi
  have heq : toeplitz (fun ν => ∑ i ∈ s, (b i : ℂ) * z i ^ ν) n =
      ∑ i ∈ s, b i • vecMulVec (fun j : Fin n => z i ^ (j : ℕ))
        (star fun j : Fin n => z i ^ (j : ℕ)) := by
    ext j l
    rw [Matrix.sum_apply, toeplitz]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Complex.real_smul, RCLike.star_def,
      map_pow, ← Complex.inv_eq_conj (hz i hi), inv_pow, zpow_sub₀ (hz0 i hi), zpow_natCast,
      zpow_natCast, div_eq_mul_inv]
  rw [heq]
  exact posSemidef_sum _ fun i hi => (posSemidef_vecMulVec_self_star _).smul (hb i hi)

/-! ### Renormalization carries no sign -/

/-- A diagonal counterterm at least the total mass of a real symmetric form makes it positive
semidefinite. -/
theorem posSemidef_add_smul_one {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.IsHermitian)
    {c : ℝ} (hc : ∑ i, ∑ j, |Q i j| ≤ c) : (Q + c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine hQ.add ?_
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, star_trivial]
  · have hsq : ∀ i j, |x i| * |x j| ≤ ∑ l, x l ^ 2 := fun i j => by
      have hi := Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l))
        (Finset.mem_univ i)
      have hj := Finset.single_le_sum (f := fun l => x l ^ 2) (fun l _ => sq_nonneg (x l))
        (Finset.mem_univ j)
      nlinarith [abs_nonneg (x i), abs_nonneg (x j), sq_abs (x i), sq_abs (x j),
        sq_nonneg (|x i| - |x j|)]
    have hform : star x ⬝ᵥ (Q + c • 1) *ᵥ x =
        (∑ i, ∑ j, x i * Q i j * x j) + c * ∑ l, x l ^ 2 := by
      rw [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul,
        star_trivial, smul_eq_mul]
      congr 1
      · simp only [dotProduct, mulVec, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · simp only [dotProduct, sq]
    rw [hform]
    have hlow : -(∑ i, ∑ j, |Q i j| * ∑ l, x l ^ 2) ≤ ∑ i, ∑ j, x i * Q i j * x j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 : |x i * Q i j * x j| = |Q i j| * (|x i| * |x j|) := by
        rw [abs_mul, abs_mul]; ring
      have h2 := neg_abs_le (x i * Q i j * x j)
      have h3 : |Q i j| * (|x i| * |x j|) ≤ |Q i j| * ∑ l, x l ^ 2 :=
        mul_le_mul_of_nonneg_left (hsq i j) (abs_nonneg _)
      linarith
    have hmass : ∑ i, ∑ j, |Q i j| * ∑ l, x l ^ 2 = (∑ i, ∑ j, |Q i j|) * ∑ l, x l ^ 2 := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul ..).symm
    have hpos : 0 ≤ ∑ l, x l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
    nlinarith

/-- **No sign survives a divergent counterterm.** For every real symmetric form `Q` and every
counterterm `c(δ) → ∞` as `δ → 0⁺`, the raw forms `Q + c(δ)·1` are eventually positive semidefinite,
and they renormalize to `Q`. -/
theorem eventually_posSemidef_add_counterterm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.IsHermitian) {c : ℝ → ℝ} (hc : Tendsto c (𝓝[>] 0) atTop) :
    (∀ᶠ δ in 𝓝[>] 0, (Q + c δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ∧
      ∀ δ, (Q + c δ • (1 : Matrix (Fin n) (Fin n) ℝ)) - c δ • 1 = Q := by
  refine ⟨?_, fun δ => add_sub_cancel_right _ _⟩
  filter_upwards [hc.eventually_ge_atTop (∑ i, ∑ j, |Q i j|)] with δ hδ
  exact posSemidef_add_smul_one hQ hδ

/-- The swap form `[[0, 1], [1, 0]]` is indefinite: renormalized limits of positive raw forms can
have either sign. -/
theorem not_posSemidef_swap : ¬ (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
  intro h
  have := (posSemidef_iff_dotProduct_mulVec.1 h).2 ![1, -1]
  simp [dotProduct, mulVec, Fin.sum_univ_two] at this
  linarith

end GaloisForLFunctions.InfiniteRankWeilTheory
