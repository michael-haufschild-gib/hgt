/-
# Naturality of the determinant completion

The regularized determinant sees its operator only through the power traces, so every naturality
statement of the completion law is a trace identity.  Power traces add across an internal direct
sum -- a pair of operators annihilating each other in both orders -- and the determinant of a sum
of power traces is the product of the determinants, so the completed character is multiplicative on
direct sums.  Power traces are similarity invariants, by bounded cyclicity of the Schatten-1 trace,
so the completed character is invariant under conjugation by any invertible bounded operator, in
particular by a unitary.

Main results:
* `tracePowerDet_add` — **the determinant is multiplicative in the power traces**.
* `opSchattenDet_add_of_orthogonal` — **direct-sum multiplicativity** of the operator determinant.
* `memSchattenClass_comp_right`, `memSchattenClass_comp_left` — the Schatten ideal property.
* `pow_conj_of_inverse`, `opTrace_conj` — **similarity invariance of the power traces**.
* `opSchattenDet_conj` — **similarity invariance of the completed determinant**.
-/
import GaloisForLFunctions.HTGeometry.DeterminantJetUniqueness
import GaloisForLFunctions.HTGeometry.ApproxNumberMultiplicative
import GaloisForLFunctions.RHTower.TraceClassCyclicity

open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-! ## The determinant is multiplicative in the power traces -/

theorem tracePowerDetExp_add {p : ℕ} (hp : 0 < p) {τ σ : ℕ → ℂ} {B S : ℝ} (hB1 : 1 ≤ B)
    (hτ : ∀ k, ‖τ (k + p)‖ ≤ S * B ^ k) (hσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    tracePowerDetExp p (fun m => τ m + σ m) z
      = tracePowerDetExp p τ z + tracePowerDetExp p σ z := by
  rw [tracePowerDetExp, tracePowerDetExp, tracePowerDetExp,
    ← (summable_tracePowerDetExp hp hB1 hτ hz).tsum_add (summable_tracePowerDetExp hp hB1 hσ hz)]
  exact tsum_congr fun k => by ring

/-- **The determinant is multiplicative in the power traces.** -/
theorem tracePowerDet_add {p : ℕ} (hp : 0 < p) {τ σ : ℕ → ℂ} {B S : ℝ} (hB1 : 1 ≤ B)
    (hτ : ∀ k, ‖τ (k + p)‖ ≤ S * B ^ k) (hσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hz : ‖z‖ * B < 1) :
    tracePowerDet p (fun m => τ m + σ m) z = tracePowerDet p τ z * tracePowerDet p σ z := by
  rw [tracePowerDet, tracePowerDet, tracePowerDet, tracePowerDetExp_add hp hB1 hτ hσ hz,
    neg_add, Complex.exp_add]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Direct sums -/

theorem opTrace_add_pow_of_orthogonal {p : ℕ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass (p : ℝ) A) (hB : MemSchattenClass (p : ℝ) B)
    (hab : A * B = 0) (hba : B * A = 0) (k : ℕ) :
    opTrace ((A + B) ^ (k + p)) = opTrace (A ^ (k + p)) + opTrace (B ^ (k + p)) := by
  have hA1 : MemSchattenClass 1 (A ^ (k + p)) := memSchattenClass_one_pow_add hp hA k
  have hB1 : MemSchattenClass 1 (B ^ (k + p)) := memSchattenClass_one_pow_add hp hB k
  obtain ⟨j, hj⟩ : ∃ j, k + p = j + 1 := ⟨k + p - 1, by omega⟩
  rw [hj] at hA1 hB1 ⊢
  rw [add_pow_succ_of_mul_eq_zero hab hba j]
  exact opTrace_add_of_memSchattenClass_one hA1 hB1

/-- **Direct-sum multiplicativity of the operator determinant.**  Two Schatten-`p` operators that
annihilate each other in both orders -- an internal direct sum -- have multiplicative order-`p`
determinants. -/
theorem opSchattenDet_add_of_orthogonal {p : ℕ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass (p : ℝ) A) (hB : MemSchattenClass (p : ℝ) B)
    (hab : A * B = 0) (hba : B * A = 0) {C : ℝ} (hC1 : 1 ≤ C)
    (hCA : schattenNorm (p : ℝ) A ≤ C) (hCB : schattenNorm (p : ℝ) B ≤ C)
    {z : ℂ} (hz : ‖z‖ * (2 * C) < 1) :
    opSchattenDet p (A + B) z = opSchattenDet p A z * opSchattenDet p B z := by
  have hB1' : (1 : ℝ) ≤ 2 * C := by linarith
  have hboundA : ∀ k : ℕ, ‖(fun m => opTrace (A ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hA hC1 hCA k
  have hboundB : ∀ k : ℕ, ‖(fun m => opTrace (B ^ m)) (k + p)‖
      ≤ ((1 + (p : ℝ)) * C ^ (p : ℝ)) * (2 * C) ^ k :=
    fun k => norm_opTrace_pow_add_le hp hB hC1 hCB k
  have hcongr : opSchattenDet p (A + B) z
      = tracePowerDet p (fun m => opTrace (A ^ m) + opTrace (B ^ m)) z := by
    rw [opSchattenDet_eq_tracePowerDet]
    refine tracePowerDet_congr (fun m hm => ?_) z
    obtain ⟨k, rfl⟩ : ∃ k, m = k + p := ⟨m - p, by omega⟩
    exact opTrace_add_pow_of_orthogonal hp hA hB hab hba k
  rw [hcongr, tracePowerDet_add hp hB1' hboundA hboundB hz,
    ← opSchattenDet_eq_tracePowerDet, ← opSchattenDet_eq_tracePowerDet]

/-! ## The Schatten ideal property -/

omit [CompleteSpace H] in
theorem memSchattenClass_comp_right {p : ℝ} (hp : 0 < p) {S T : H →L[ℂ] H}
    (hS : MemSchattenClass p S) : MemSchattenClass p (S ∘L T) := by
  refine (hS.mul_right (‖T‖ ^ p)).of_nonneg_of_le
    (fun n => Real.rpow_nonneg (approxNumber_nonneg _ n) p) fun n => ?_
  have hle : approxNumber (S ∘L T) n ≤ approxNumber S n * ‖T‖ := by
    have h := approxNumber_comp_add_le S T n 0
    rwa [Nat.add_zero, approxNumber_zero_eq_norm] at h
  calc approxNumber (S ∘L T) n ^ p ≤ (approxNumber S n * ‖T‖) ^ p :=
        Real.rpow_le_rpow (approxNumber_nonneg _ n) hle hp.le
    _ = approxNumber S n ^ p * ‖T‖ ^ p :=
        Real.mul_rpow (approxNumber_nonneg _ n) (norm_nonneg T)

omit [CompleteSpace H] in
theorem memSchattenClass_comp_left {p : ℝ} (hp : 0 < p) {S T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) : MemSchattenClass p (S ∘L T) := by
  refine (hT.mul_left (‖S‖ ^ p)).of_nonneg_of_le
    (fun n => Real.rpow_nonneg (approxNumber_nonneg _ n) p) fun n => ?_
  have hle : approxNumber (S ∘L T) n ≤ ‖S‖ * approxNumber T n := by
    have h := approxNumber_comp_add_le S T 0 n
    rwa [Nat.zero_add, approxNumber_zero_eq_norm] at h
  calc approxNumber (S ∘L T) n ^ p ≤ (‖S‖ * approxNumber T n) ^ p :=
        Real.rpow_le_rpow (approxNumber_nonneg _ n) hle hp.le
    _ = ‖S‖ ^ p * approxNumber T n ^ p :=
        Real.mul_rpow (norm_nonneg S) (approxNumber_nonneg _ n)

/-! ## Similarity invariance -/

omit [CompleteSpace H] in
theorem pow_conj_of_inverse {A V W : H →L[ℂ] H} (hVW : W * V = 1) (hWV : V * W = 1) :
    ∀ m : ℕ, (V * A * W) ^ m = V * A ^ m * W := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one, hWV]
  | succ m ih =>
      have h1 : (V * A * W) ^ (m + 1) = V * A ^ m * W * (V * A * W) := by
        rw [pow_succ, ih]
      have h2 : V * A ^ m * W * (V * A * W) = V * (A ^ m * ((W * V) * (A * W))) := by
        simp only [mul_assoc]
      have h3 : V * (A ^ m * ((W * V) * (A * W))) = V * A ^ (m + 1) * W := by
        rw [hVW, one_mul, pow_succ]
        simp only [mul_assoc]
      rw [h1, h2, h3]

/-- **Similarity invariance of the power traces.** -/
theorem opTrace_conj {B V W : H →L[ℂ] H} (hB : MemSchattenClass 1 B)
    (hVW : W * V = 1) : opTrace (V * B * W) = opTrace B := by
  have hBW : MemSchattenClass 1 (B * W) := memSchattenClass_comp_right one_pos hB
  have key : opTrace (V ∘L (B * W)) = opTrace ((B * W) ∘L V) := hBW.one_opTrace_comp_comm V
  have hR : ((B * W) ∘L V) = B := by
    show (B * W) * V = B
    rw [mul_assoc, hVW, mul_one]
  calc opTrace (V * B * W) = opTrace (V ∘L (B * W)) := by rw [mul_assoc]; rfl
    _ = opTrace ((B * W) ∘L V) := key
    _ = opTrace B := by rw [hR]

/-- **Similarity invariance of the completed determinant.**  Conjugating by any invertible bounded
operator -- in particular by a unitary -- leaves the order-`p` regularized determinant unchanged. -/
theorem opSchattenDet_conj {p : ℕ} (hp : 0 < p) {A V W : H →L[ℂ] H}
    (hA : MemSchattenClass (p : ℝ) A) (hVW : W * V = 1) (hWV : V * W = 1) (z : ℂ) :
    opSchattenDet p (V * A * W) z = opSchattenDet p A z := by
  rw [opSchattenDet_eq_tracePowerDet, opSchattenDet_eq_tracePowerDet]
  refine tracePowerDet_congr (fun m hm => ?_) z
  obtain ⟨k, rfl⟩ : ∃ k, m = k + p := ⟨m - p, by omega⟩
  rw [pow_conj_of_inverse hVW hWV]
  exact opTrace_conj (memSchattenClass_one_pow_add hp hA k) hVW

end

end GaloisForLFunctions.HTGeometry
