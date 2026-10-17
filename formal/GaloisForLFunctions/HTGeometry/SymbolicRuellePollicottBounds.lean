import GaloisForLFunctions.HTGeometry.SymbolicTransferHolomorphy
import GaloisForLFunctions.HTGeometry.OuterSpectralContinuation

/-!
# Growth of periodic-orbit sums and partition functions

For a roof potential `φ ≥ r_min > 0` with `|φ| ≤ R₀`, the real periodic-orbit sums
`Z_L(σ) = Σ_{σ^L p = p} e^{−σ φ^L(p)}` satisfy

* `periodicSumR_le_of_le`: `Z_L(σ) ≤ e^{L(σ' − σ)R₀} Z_L(σ')` for `σ ≤ σ'`;
* `periodicSumR_le_decay`: `Z_L(σ) ≤ e^{−L(σ − σ') r_min} Z_L(σ')` for `σ' ≤ σ`;
* `exists_periodicSumR_le`: if `Σ Z_L(σ)/L < ∞` then `Z_L(σ) ≤ B L`.

Combined with the closing lemma this bounds the partition functions of the transfer operator:
`Φₙ(σ) ≤ K e^{n κ}` on `σ > 1 − ε` with `κ = ε (2R₀ + 1)` (`partitionFun_le_exp`), and
`Φₙ(σ) ≤ c τⁿ`, `τ < 1`, on `σ > 1` (`exists_partitionFun_le_geometric`).
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset Filter Topology Metric

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop}

variable (A) in
/-- The real periodic-orbit sum `Z_L(σ) = Σ_{σ^L p = p} e^{−σ φ^L(p)}`. -/
def periodicSumR (φ : (ℕ → Fin k) → ℝ) (L : ℕ) [NeZero L] (σ : ℝ) : ℝ :=
  ∑ p ∈ periodicPoints A L, Real.exp (-(σ * birkhoff φ L p))

variable (A) in
/-- The complex periodic-orbit sums `zₙ(s) = Σ_{σⁿp = p} e^{−s φⁿ(p)}`, with `z₀ = 0`. -/
def periodicZ (φ : (ℕ → Fin k) → ℝ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => fun s => ∑ p ∈ periodicPoints A (n + 1), Complex.exp (-(s * birkhoff φ (n + 1) p))

theorem periodicSumR_nonneg (φ : (ℕ → Fin k) → ℝ) (L : ℕ) [NeZero L] (σ : ℝ) :
    0 ≤ periodicSumR A φ L σ :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

theorem differentiable_periodicZ (φ : (ℕ → Fin k) → ℝ) (n : ℕ) :
    Differentiable ℂ (periodicZ A φ n) := by
  cases n with
  | zero => exact differentiable_const 0
  | succ n =>
    show Differentiable ℂ fun s => ∑ p ∈ periodicPoints A (n + 1),
      Complex.exp (-(s * birkhoff φ (n + 1) p))
    fun_prop

/-- `|zₙ(s)| ≤ Zₙ(Re s)`. -/
theorem norm_periodicZ_le (φ : (ℕ → Fin k) → ℝ) (n : ℕ) (s : ℂ) :
    ‖periodicZ A φ (n + 1) s‖ ≤ periodicSumR A φ (n + 1) s.re := by
  show ‖∑ p ∈ periodicPoints A (n + 1), Complex.exp (-(s * birkhoff φ (n + 1) p))‖ ≤ _
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  exact norm_cexp_neg_mul_ofReal s _

/-- For real `σ`, `zₙ(σ) = Zₙ(σ)`. -/
theorem periodicZ_ofReal (φ : (ℕ → Fin k) → ℝ) (n : ℕ) (σ : ℝ) :
    periodicZ A φ (n + 1) σ = (periodicSumR A φ (n + 1) σ : ℂ) := by
  show ∑ p ∈ periodicPoints A (n + 1), Complex.exp (-((σ : ℂ) * birkhoff φ (n + 1) p)) = _
  rw [periodicSumR, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

section Growth

variable {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}


/-- `Z_L(σ) ≤ e^{L(σ' − σ)R₀} Z_L(σ')` for `σ ≤ σ'`. -/
theorem periodicSumR_le_of_le (hb : ∀ y, IsAdmissible A y → |φ y| ≤ R₀) {L : ℕ} [NeZero L]
    {σ σ' : ℝ} (h : σ ≤ σ') :
    periodicSumR A φ L σ ≤ Real.exp (L * (σ' - σ) * R₀) * periodicSumR A φ L σ' := by
  rw [periodicSumR, periodicSumR, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpa : IsAdmissible A p := (mem_periodicPoints.mp hp).1
  have hbL := abs_birkhoff_le hb L hpa
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : (σ' - σ) * birkhoff φ L p ≤ (σ' - σ) * (L * R₀) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbL) (by linarith)
  nlinarith

/-- `Z_L(σ) ≤ e^{−L(σ − σ') r_min} Z_L(σ')` for `σ' ≤ σ`. -/
theorem periodicSumR_le_decay {rmin : ℝ} (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y) {L : ℕ}
    [NeZero L] {σ σ' : ℝ} (h : σ' ≤ σ) :
    periodicSumR A φ L σ ≤ Real.exp (-(L * (σ - σ') * rmin)) * periodicSumR A φ L σ' := by
  rw [periodicSumR, periodicSumR, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpa : IsAdmissible A p := (mem_periodicPoints.mp hp).1
  have hlow : L * rmin ≤ birkhoff φ L p := by
    rw [birkhoff]
    calc (L : ℝ) * rmin = ∑ _i ∈ Finset.range L, rmin := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.range L, φ (shiftBy i p) :=
          Finset.sum_le_sum fun i _ => hmin _ (hpa.shiftBy i)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : (σ - σ') * (L * rmin) ≤ (σ - σ') * birkhoff φ L p :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  nlinarith

/-- **Summability gives linear growth**: `Z_{n+1}(σ) ≤ B (n + 1)`. -/
theorem exists_periodicSumR_le {σ : ℝ}
    (hsum : Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1)) :
    ∃ B, 0 ≤ B ∧ ∀ n : ℕ, periodicSumR A φ (n + 1) σ ≤ B * ((n : ℝ) + 1) := by
  have hnn : ∀ n : ℕ, 0 ≤ periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1) := fun n =>
    div_nonneg (periodicSumR_nonneg _ _ _) (by positivity)
  refine ⟨∑' n : ℕ, periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1), tsum_nonneg hnn, fun n => ?_⟩
  have hle := hsum.le_tsum n fun m _ => hnn m
  rwa [div_le_iff₀ (by positivity)] at hle

/-- A linear bound at all periods `n + 1` is a linear bound at every positive period. -/
theorem periodicSumR_le_of_succ {σ B : ℝ}
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) σ ≤ B * ((n : ℝ) + 1)) (L : ℕ) [NeZero L] :
    periodicSumR A φ L σ ≤ B * L := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by have := NeZero.pos L; omega⟩
  have := hB L'
  push_cast
  exact this

/-- `n + M ≤ (M + 1/ε) e^{nε}`. -/
theorem nat_add_le_exp {ε : ℝ} (hε : 0 < ε) (n M : ℕ) :
    ((n : ℝ) + M) ≤ (M + ε⁻¹) * Real.exp (n * ε) := by
  have h1 := Real.add_one_le_exp (n * ε)
  have h2 : (1 : ℝ) ≤ Real.exp (n * ε) := Real.one_le_exp (by positivity)
  have hn : (n : ℝ) ≤ ε⁻¹ * Real.exp (n * ε) := by
    rw [inv_mul_eq_div, le_div_iff₀ hε]; nlinarith
  have hM : (M : ℝ) ≤ M * Real.exp (n * ε) := le_mul_of_one_le_right (Nat.cast_nonneg M) h2
  nlinarith

/-- **Partition functions on the half-plane `σ > 1 − ε`**:
`Φₙ(σ) ≤ K e^{n ε (2R₀ + 1)}`. -/
theorem partitionFun_le_exp {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    (hφ : IsHolderPotential A φ R₀ C θ) (hR₀ : 0 ≤ R₀) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpos : ∀ y, IsAdmissible A y → 0 ≤ φ y) {ε B : ℝ} (hε : 0 < ε) (hB0 : 0 ≤ B)
    (hB : ∀ n : ℕ, periodicSumR A φ (n + 1) (1 + ε) ≤ B * ((n : ℝ) + 1))
    {σ : ℝ} (hσ : 1 - ε < σ) {n : ℕ} (hn : 1 ≤ n) (x : ℕ → Fin k) :
    partitionFun A φ σ n x ≤ (Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀)) * B *
      (M + ε⁻¹) * Real.exp (M * (2 * ε) * R₀)) * Real.exp (n * (ε * (2 * R₀ + 1))) := by
  haveI : NeZero (n + (M - 1)) := ⟨by omega⟩
  set L := n + (M - 1) with hLdef
  have h1 := partitionFun_le_periodicSum hmix hM hφ hθ0 hθ1 σ hn x
  have hL : ((L : ℕ) : ℝ) ≤ n + M := by
    rw [hLdef]; push_cast [Nat.cast_sub hM]; linarith
  have hZ : periodicSumR A φ L σ ≤ Real.exp (L * (2 * ε) * R₀) * (B * L) := by
    have hBL : periodicSumR A φ L (1 + ε) ≤ B * L := periodicSumR_le_of_succ hB L
    by_cases hσ' : σ ≤ 1 + ε
    · refine (periodicSumR_le_of_le hφ.bound hσ').trans ?_
      refine mul_le_mul (Real.exp_le_exp.mpr ?_) hBL (periodicSumR_nonneg _ _ _) (Real.exp_pos _).le
      have : 1 + ε - σ ≤ 2 * ε := by linarith
      have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
      have := mul_nonneg (mul_nonneg hL0 (sub_nonneg.mpr this)) hR₀
      nlinarith
    · have hdec := periodicSumR_le_decay (rmin := 0) hpos (L := L) (σ' := 1 + ε) (σ := σ)
        (by linarith)
      rw [mul_zero, neg_zero, Real.exp_zero, one_mul] at hdec
      refine hdec.trans (hBL.trans ?_)
      exact le_mul_of_one_le_left (by positivity) (Real.one_le_exp (by positivity))
  set K₁ := Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀))
  have hK₁ : 0 ≤ K₁ := (Real.exp_pos _).le
  calc partitionFun A φ σ n x ≤ K₁ * periodicSumR A φ L σ := h1
    _ ≤ K₁ * (Real.exp (L * (2 * ε) * R₀) * (B * L)) := mul_le_mul_of_nonneg_left hZ hK₁
    _ ≤ K₁ * (Real.exp ((n + M) * (2 * ε) * R₀) * (B * ((M + ε⁻¹) * Real.exp (n * ε)))) := by
        have e1 : Real.exp (L * (2 * ε) * R₀) ≤ Real.exp ((n + M) * (2 * ε) * R₀) := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_right hL (by positivity : (0 : ℝ) ≤ 2 * ε * R₀)
          nlinarith
        have e2 : B * L ≤ B * ((M + ε⁻¹) * Real.exp (n * ε)) :=
          mul_le_mul_of_nonneg_left (hL.trans (nat_add_le_exp hε n M)) hB0
        exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (Real.exp_pos _).le) hK₁
    _ = (K₁ * B * (M + ε⁻¹) * Real.exp (M * (2 * ε) * R₀)) *
          Real.exp (n * (ε * (2 * R₀ + 1))) := by
        rw [show (n + M : ℝ) * (2 * ε) * R₀ = M * (2 * ε) * R₀ + n * (2 * ε * R₀) by ring,
          Real.exp_add]
        rw [show n * (ε * (2 * R₀ + 1)) = n * (2 * ε * R₀) + n * ε by ring, Real.exp_add]
        ring

/-- **Geometric decay of partition functions on `σ > 1`.** -/
theorem exists_partitionFun_le_geometric {M : ℕ} (hmix : IsMixing A M) (hM : 1 ≤ M)
    (hφ : IsHolderPotential A φ R₀ C θ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {rmin : ℝ}
    (hrmin : 0 < rmin) (hmin : ∀ y, IsAdmissible A y → rmin ≤ φ y)
    (hsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => periodicSumR A φ (n + 1) σ / ((n : ℝ) + 1))
    {σ : ℝ} (hσ : 1 < σ) :
    ∃ c τ : ℝ, 0 ≤ c ∧ 0 ≤ τ ∧ τ < 1 ∧
      ∀ n : ℕ, 1 ≤ n → ∀ x, partitionFun A φ σ n x ≤ c * τ ^ n := by
  set σ' := (1 + σ) / 2
  have hσ' : 1 < σ' := by simp only [σ']; linarith
  obtain ⟨B, hB0, hB⟩ := exists_periodicSumR_le (hsum σ' hσ')
  set lam := (σ - σ') * rmin
  have hlam : 0 < lam := mul_pos (by simp only [σ']; linarith) hrmin
  set K₁ := Real.exp (|σ| * (C / (1 - θ) + (M - 1) * R₀))
  refine ⟨K₁ * B * (2 / lam), Real.exp (-(lam / 2)), by positivity, (Real.exp_pos _).le,
    Real.exp_lt_one.mpr (by linarith), fun n hn x => ?_⟩
  haveI : NeZero (n + (M - 1)) := ⟨by omega⟩
  set L := n + (M - 1) with hLdef
  have h1 := partitionFun_le_periodicSum hmix hM hφ hθ0 hθ1 σ hn x
  have hBL : periodicSumR A φ L σ' ≤ B * L := periodicSumR_le_of_succ hB L
  have hdec := periodicSumR_le_decay hmin (L := L) (σ := σ) (σ' := σ')
    (by simp only [σ']; linarith)
  have hLn : (n : ℝ) ≤ L := by rw [hLdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (M - 1)]
  have hkey : (L : ℝ) * Real.exp (-(L * lam)) ≤ (2 / lam) * Real.exp (-(n * (lam / 2))) := by
    have e1 := Real.add_one_le_exp (L * (lam / 2))
    have e2 : (L : ℝ) ≤ (2 / lam) * Real.exp (L * (lam / 2)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam]; nlinarith [Nat.cast_nonneg (α := ℝ) L]
    calc (L : ℝ) * Real.exp (-(L * lam)) ≤ (2 / lam) * Real.exp (L * (lam / 2)) *
          Real.exp (-(L * lam)) := mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
      _ = (2 / lam) * Real.exp (-(L * (lam / 2))) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ (2 / lam) * Real.exp (-(n * (lam / 2))) := by
          gcongr
  calc partitionFun A φ σ n x ≤ K₁ * periodicSumR A φ L σ := h1
    _ ≤ K₁ * (Real.exp (-(L * (σ - σ') * rmin)) * (B * L)) := by
        refine mul_le_mul_of_nonneg_left (hdec.trans ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hBL (Real.exp_pos _).le
    _ = K₁ * B * (L * Real.exp (-(L * lam))) := by
        simp only [lam]; ring_nf
    _ ≤ K₁ * B * ((2 / lam) * Real.exp (-(n * (lam / 2)))) := by
        gcongr
    _ = K₁ * B * (2 / lam) * Real.exp (-(lam / 2)) ^ n := by
        rw [← Real.exp_nat_mul]; ring_nf

end Growth

end

end GaloisForLFunctions.HTGeometry.Symbolic
