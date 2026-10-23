import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Adverse profiles cannot vanish

A signed energy `Q(u) = ⟪T u, u⟫` on a real inner product space, `T` bounded and symmetric.  An
**adverse sequence** is a sequence of unit-bounded profiles `u_n` with `Q(u_n) → μ < 0`.  The
question of profile decomposition is where the negativity goes.

* **Energy splitting** (`tendsto_energy_splitting`): if `u_n ⇀ u` weakly, then
  `Q(u_n) − Q(u) − Q(u_n − u) → 0`.  A bounded signed form never mixes a weak limit with its
  remainder.
* **Compact negativity** (`CompactlyNegative`): for every `ε > 0` the form is bounded below by a
  finite-rank charge and `ε ‖·‖²`.  Then the energy is weakly lower semicontinuous along bounded
  sequences (`energy_le_of_weakConv`), and **adverse sequences cannot vanish**
  (`adverse_weakLimit`): the weak limit `u` is nonzero, `‖u‖ ≤ 1`, and `Q(u) ≤ μ ‖u‖²` — it is at
  least as adverse as the sequence.  A ground state below zero is attained.
* **Escape** (`adverse_escape_of_orthonormal`): when the negative part is not compact — `Q = −‖·‖²`
  on an orthonormal sequence — the adverse sequence `e_n` converges weakly to `0`, where `Q = 0`.
  The noncompact directions of the negative part are the only escape channels.

The arithmetic reading: at fixed support the prime and polar charges are compact against the
archimedean energy, so negative ground energies have genuine adverse profiles; uniformity across
growing support, rank or height is exactly the loss of compact negativity.
-/

open Filter Topology RealInnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Weak convergence: every inner product converges. -/
def WeakConv (u : ℕ → H) (u₀ : H) : Prop :=
  ∀ v : H, Tendsto (fun n => ⟪u n, v⟫) atTop (𝓝 ⟪u₀, v⟫)

/-- The signed energy `⟪T u, u⟫`. -/
def signedEnergy (T : H →L[ℝ] H) (u : H) : ℝ := ⟪T u, u⟫

/-- `T` is symmetric. -/
def IsSymmetricOp (T : H →L[ℝ] H) : Prop := ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

theorem signedEnergy_add {T : H →L[ℝ] H} (hT : IsSymmetricOp T) (x y : H) :
    signedEnergy T (x + y) = signedEnergy T x + 2 * ⟪T x, y⟫ + signedEnergy T y := by
  unfold signedEnergy
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hT y x, real_inner_comm (T x) y]
  ring

theorem WeakConv.inner_sub_tendsto_zero {u : ℕ → H} {u₀ : H} (h : WeakConv u u₀) (v : H) :
    Tendsto (fun n => ⟪v, u n - u₀⟫) atTop (𝓝 0) := by
  have h1 := (h v).sub_const ⟪u₀, v⟫
  simp only [sub_self] at h1
  refine h1.congr fun n => ?_
  rw [inner_sub_right, real_inner_comm v (u n), real_inner_comm v u₀]

/-- **Energy splitting** under weak convergence. -/
theorem tendsto_energy_splitting {T : H →L[ℝ] H} (hT : IsSymmetricOp T) {u : ℕ → H} {u₀ : H}
    (h : WeakConv u u₀) :
    Tendsto (fun n => signedEnergy T (u n) - signedEnergy T u₀ - signedEnergy T (u n - u₀))
      atTop (𝓝 0) := by
  have e : ∀ n, signedEnergy T (u n) - signedEnergy T u₀ - signedEnergy T (u n - u₀) =
      2 * ⟪T u₀, u n - u₀⟫ := by
    intro n
    have := signedEnergy_add hT u₀ (u n - u₀)
    rw [add_sub_cancel] at this
    linarith
  simp only [e]
  simpa using (h.inner_sub_tendsto_zero (T u₀)).const_mul 2

/-- The finite-rank charge `Σ_i ⟪φ_i, u⟫²`. -/
def finiteRankCharge {ι : Type*} [Fintype ι] (φ : ι → H) (u : H) : ℝ := ∑ i, ⟪φ i, u⟫ ^ 2

theorem WeakConv.tendsto_finiteRankCharge {u : ℕ → H} {u₀ : H} (h : WeakConv u u₀)
    {ι : Type*} [Fintype ι] (φ : ι → H) :
    Tendsto (fun n => finiteRankCharge φ (u n - u₀)) atTop (𝓝 0) := by
  have := tendsto_finsetSum (Finset.univ : Finset ι)
    fun i _ => (h.inner_sub_tendsto_zero (φ i)).pow 2
  simpa [finiteRankCharge] using this

/-- **Compact negativity**: for every `ε > 0`, `Q ≥ −(finite-rank charge) − ε ‖·‖²`. -/
def CompactlyNegative (T : H →L[ℝ] H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (φ : Fin m → H), ∀ u,
    -finiteRankCharge φ u - ε * ‖u‖ ^ 2 ≤ signedEnergy T u

/-- A form bounded below by one finite-rank charge is compactly negative. -/
theorem compactlyNegative_of_finiteRank {T : H →L[ℝ] H} {m : ℕ} (φ : Fin m → H)
    (h : ∀ u, -finiteRankCharge φ u ≤ signedEnergy T u) : CompactlyNegative T := by
  intro ε hε
  refine ⟨m, φ, fun u => ?_⟩
  have := h u
  have : 0 ≤ ε * ‖u‖ ^ 2 := by positivity
  linarith

/-- **Weak lower semicontinuity** of a compactly negative energy along bounded sequences. -/
theorem energy_le_of_weakConv {T : H →L[ℝ] H} (hT : IsSymmetricOp T) (hK : CompactlyNegative T)
    {u : ℕ → H} {u₀ : H} (h : WeakConv u u₀) {B : ℝ} (hB : ∀ n, ‖u n - u₀‖ ≤ B) {μ : ℝ}
    (hμ : Tendsto (fun n => signedEnergy T (u n)) atTop (𝓝 μ)) :
    signedEnergy T u₀ ≤ μ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set δ := ε / (2 * (B ^ 2 + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨m, φ, hφ⟩ := hK δ hδpos
  -- `Q(u₀) = Q(u_n) − Q(u_n − u₀) − 2⟪T u₀, u_n − u₀⟫ ≤ Q(u_n) + K(u_n − u₀) + δ B² + o(1)`
  have hlim : Tendsto (fun n => signedEnergy T (u n) + finiteRankCharge φ (u n - u₀) -
      (signedEnergy T (u n) - signedEnergy T u₀ - signedEnergy T (u n - u₀))) atTop
      (𝓝 (μ + 0 - 0)) :=
    (hμ.add (h.tendsto_finiteRankCharge φ)).sub (tendsto_energy_splitting hT h)
  have hbound : ∀ n, signedEnergy T u₀ ≤ signedEnergy T (u n) + finiteRankCharge φ (u n - u₀) -
      (signedEnergy T (u n) - signedEnergy T u₀ - signedEnergy T (u n - u₀)) + δ * B ^ 2 := by
    intro n
    have h1 := hφ (u n - u₀)
    have h2 : ‖u n - u₀‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB n) 2
    have h3 : δ * ‖u n - u₀‖ ^ 2 ≤ δ * B ^ 2 := mul_le_mul_of_nonneg_left h2 hδpos.le
    linarith
  have hle : signedEnergy T u₀ ≤ μ + δ * B ^ 2 := by
    have := ge_of_tendsto' (hlim.add_const (δ * B ^ 2)) hbound
    simpa using this
  have hsmall : δ * B ^ 2 < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Weak limits of unit-bounded sequences are unit-bounded. -/
theorem norm_le_one_of_weakConv {u : ℕ → H} {u₀ : H} (h : WeakConv u u₀)
    (hu : ∀ n, ‖u n‖ ≤ 1) : ‖u₀‖ ≤ 1 := by
  have hlim := h u₀
  rw [real_inner_self_eq_norm_sq] at hlim
  have hb : ∀ n, ⟪u n, u₀⟫ ≤ ‖u₀‖ := fun n =>
    (real_inner_le_norm _ _).trans (by simpa using mul_le_mul_of_nonneg_right (hu n) (norm_nonneg u₀))
  have h2 : ‖u₀‖ ^ 2 ≤ ‖u₀‖ := le_of_tendsto' hlim hb
  nlinarith [norm_nonneg u₀]

/-- **Adverse sequences cannot vanish.**  Under compact negativity, a unit-bounded adverse sequence
`Q(u_n) → μ < 0` converging weakly to `u₀` has `u₀ ≠ 0`, `‖u₀‖ ≤ 1` and `Q(u₀) ≤ μ ‖u₀‖²`. -/
theorem adverse_weakLimit {T : H →L[ℝ] H} (hT : IsSymmetricOp T) (hK : CompactlyNegative T)
    {u : ℕ → H} {u₀ : H} (h : WeakConv u u₀) (hu : ∀ n, ‖u n‖ ≤ 1) {μ : ℝ} (hμ0 : μ < 0)
    (hμ : Tendsto (fun n => signedEnergy T (u n)) atTop (𝓝 μ)) :
    u₀ ≠ 0 ∧ ‖u₀‖ ≤ 1 ∧ signedEnergy T u₀ ≤ μ * ‖u₀‖ ^ 2 := by
  have hn := norm_le_one_of_weakConv h hu
  have hB : ∀ n, ‖u n - u₀‖ ≤ 2 := fun n => (norm_sub_le _ _).trans (by linarith [hu n])
  have hQ := energy_le_of_weakConv hT hK h hB hμ
  have hne : u₀ ≠ 0 := by
    rintro rfl
    simp [signedEnergy] at hQ
    linarith
  refine ⟨hne, hn, ?_⟩
  have h1 : ‖u₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u₀]
  nlinarith

/-- **Escape through a noncompact negative part.**  For `Q = −‖·‖²` an orthonormal sequence is an
adverse sequence with energy `−1` whose weak limit is `0`, where the energy is `0`. -/
theorem adverse_escape_of_orthonormal {e : ℕ → H} (he : Orthonormal ℝ e) :
    WeakConv e 0 ∧ (∀ n, ‖e n‖ = 1) ∧ ∀ n, -‖e n‖ ^ 2 = -1 := by
  refine ⟨fun v => ?_, fun n => he.1 n, fun n => by rw [he.1 n]; norm_num⟩
  simp only [inner_zero_left]
  have hs : Summable fun n => ⟪e n, v⟫ ^ 2 := by
    have := he.inner_products_summable v
    simpa [real_inner_comm, sq] using this
  have h2 := hs.tendsto_atTop_zero
  have h3 : Tendsto (fun n => |⟪e n, v⟫|) atTop (𝓝 0) := by
    have := h2.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h3

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
