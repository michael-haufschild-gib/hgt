import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheFrobeniusLadderIsMetzler
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSuccessorConnectionIsTheArchimedeanGaugeField
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheHeckeCocycleOfRenormalization

/-!
# Frobenius is conformal, Hecke is a boost

What would replace Frobenius in Lorentzian terms? Over `𝔽_q` the pullback `(F × 1)^*` acts on the
cycles `H, V, Γ_k` by `H ↦ qH`, `V ↦ V`, `Γ_k ↦ Γ_{k+1}`: a **nonnegative conformal map** of the
Frobenius Gram with factor `q` that generates the whole ladder from `Γ_0`
(`frobeniusPullback_conformal`). Over `ℤ` the three candidate maps on the atoms behave differently.

* **Hecke dilations are isometries.** `n ↦ pn` preserves the coupled kernel of every twin
  (`coupledKernel_mul_left`) and acts on the pole plane by the boost `diag(p^{−1/2}, p^{1/2})`
  (`boost_isometry`): conformal factor one. A boost cannot produce the Hasse–Weil inequality,
  which Weil reads off the factor `q`.
* **Power maps (Adams operations) are not conformal.** `n ↦ n^k`, `k ≥ 2`, scales the prime kernel
  by `2^{(1−k)/2}` on `(1, 2)` and by `2^{1−k}` on `(1, 4)` (`not_conformal_powerMap`).
* **The successor is not conformal.** It sends a profile of vanishing prime form to one of positive
  prime form (`not_conformal_succShift`).

No map of the atoms available over `ℤ` is a conformal Lorentzian map with factor `≠ 1`: Frobenius
over `𝔽_q` is a symmetry of a *different kind* (conformal) from every symmetry over `ℤ`
(isometries).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticCastelnuovoSeveri ArithmeticEffectivityTheory ArithmeticElectrostatics
  ArithmeticIntersectionTheory

/-! ### Over `𝔽_q`: Frobenius is a nonnegative conformal map -/

variable {ι : Type*} [Fintype ι]

theorem graphPair_succ_succ (D : CurveDatum ι) (k l : ℕ) :
    D.graphPair (k + 1) (l + 1) = D.q * D.graphPair k l := by
  have hd : Nat.dist (k + 1) (l + 1) = Nat.dist k l := by
    unfold Nat.dist; omega
  rw [CurveDatum.graphPair, CurveDatum.graphPair, hd,
    show min (k + 1) (l + 1) = min k l + 1 by omega, pow_succ]
  ring

/-- The shift of the ladder `Γ_k ↦ Γ_{k+1}`. -/
def ladderShift (K : ℕ) : Matrix (Fin (K + 2)) (Fin (K + 1)) ℝ :=
  Matrix.of fun k' k => if k' = k.succ then 1 else 0

/-- **Frobenius pullback** `(F × 1)^*`: `H ↦ qH`, `V ↦ V`, `Γ_k ↦ Γ_{k+1}`. -/
def frobeniusPullback (D : CurveDatum ι) (K : ℕ) :
    Matrix (Fin 2 ⊕ Fin (K + 2)) (Fin 2 ⊕ Fin (K + 1)) ℝ :=
  fromBlocks !![D.q, 0; 0, 1] 0 0 (ladderShift K)

theorem frobeniusPullback_nonneg (D : CurveDatum ι) (K : ℕ) (a b) :
    0 ≤ frobeniusPullback D K a b := by
  have hq : 0 ≤ D.q := by linarith [D.one_lt_q]
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;> simp [frobeniusPullback, hq]
  · simp [frobeniusPullback]
  · simp [frobeniusPullback]
  · simp only [frobeniusPullback, fromBlocks_apply₂₂, ladderShift, Matrix.of_apply]
    split_ifs <;> norm_num

/-- **Frobenius is conformal with factor `q`**: `Tᵀ G_{K+1} T = q G_K`. -/
theorem frobeniusPullback_conformal (D : CurveDatum ι) (K : ℕ) :
    (frobeniusPullback D K)ᵀ * frobeniusGram D (K + 1) * frobeniusPullback D K =
      D.q • frobeniusGram D K := by
  have hR : ∀ {r : Type} [Fintype r] (M : Matrix r (Fin (K + 2)) ℝ),
      M * ladderShift K = Matrix.of fun a k => M a k.succ := fun M => by
    ext a k; simp [mul_apply, ladderShift]
  have hL : ∀ {c : Type} [Fintype c] (M : Matrix (Fin (K + 2)) c ℝ),
      (ladderShift K)ᵀ * M = Matrix.of fun k b => M k.succ b := fun M => by
    ext k b; simp [mul_apply, ladderShift, transpose_apply]
  rw [frobeniusPullback, frobeniusGram, frobeniusGram, fromBlocks_transpose, fromBlocks_multiply,
    fromBlocks_multiply, fromBlocks_smul]
  simp only [transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · ext a b; fin_cases a <;> fin_cases b <;>
      simp [realPolePlane, mul_apply, Fin.sum_univ_two]
  · rw [Matrix.mul_assoc, hR]
    ext a k
    fin_cases a <;> simp [frobeniusPoleRow, mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  · rw [hL, ← transpose_transpose (Matrix.of fun k b => _)]
    ext k a
    fin_cases a <;> simp [frobeniusPoleRow, mul_apply, Fin.sum_univ_two, pow_succ] <;> ring
  · rw [hL, hR]
    ext k l
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, frobeniusGraphBlock,
      Fin.val_succ]
    exact graphPair_succ_succ D k l

/-! ### Over `ℤ`: Hecke dilations are isometries -/

/-- **The coupled kernel is Hecke invariant**: `K(pm, pn) = K(m, n)` for every twin. -/
theorem coupledKernel_mul_left {χ : ℕ → ℂ} (hχ : IsTwin χ) (t : ℝ) {p m n : ℕ} (hp : 0 < p)
    (hm : 0 < m) (hn : 0 < n) : coupledKernel χ t (p * m) (p * n) = coupledKernel χ t m n := by
  have harch : archAtomKernel (p * m) (p * n) = archAtomKernel m n := by
    unfold archAtomKernel
    by_cases h : m = n
    · subst h; simp
    · have h' : p * m ≠ p * n := fun e => h (Nat.eq_of_mul_eq_mul_left hp e)
      rw [if_neg h, if_neg h']
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      congr 2; ring
  have hp' : p ≠ 0 := hp.ne'
  have htw : twinPrimeKernel χ (p * m) (p * n) = twinPrimeKernel χ m n := by
    unfold twinPrimeKernel
    rw [hχ.map_mul, hχ.map_mul, weilPrimeKernel_mul_left hp, map_mul]
    have hpp : conj (χ p) * χ p = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ.norm_eq p hp']; simp
    linear_combination (conj (χ m) * χ n * (weilPrimeKernel m n : ℂ)) * hpp
  rw [coupledKernel, coupledKernel, harch, htw]

/-- The boost `diag(p^{−1/2}, p^{1/2})` of the pole plane. -/
def boost (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![(Real.sqrt p)⁻¹, 0; 0, Real.sqrt p]

/-- **The boost is an isometry of the pole plane**: conformal factor one. -/
theorem boost_isometry {p : ℝ} (hp : 0 < p) : (boost p)ᵀ * realPolePlane * boost p = realPolePlane := by
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [boost, realPolePlane, mul_apply, Fin.sum_univ_two, hs]

/-! ### Power maps and the successor are not conformal -/

theorem weilPrimeKernel_one_two_pow {k : ℕ} (hk : 1 ≤ k) :
    weilPrimeKernel 1 (2 ^ k) = Real.log 2 / Real.sqrt ((2 : ℝ) ^ k) := by
  unfold weilPrimeKernel
  have hne : (1 : ℕ) ≠ 2 ^ k := (Nat.one_lt_two_pow (by omega)).ne
  rw [if_pos ⟨one_dvd _, hne⟩, Nat.div_one, ArithmeticFunction.vonMangoldt_apply_pow (by omega),
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast; rfl

theorem weilPrimeKernel_one_two_pow_even {j : ℕ} (hj : 1 ≤ j) :
    weilPrimeKernel 1 (2 ^ (2 * j)) = Real.log 2 / 2 ^ j := by
  rw [weilPrimeKernel_one_two_pow (by omega), pow_mul', Real.sqrt_sq (by positivity)]

/-- **Adams operations are not conformal** for the prime kernel: `n ↦ n^k` (`k ≥ 2`) scales the
pair `(1, 4)` by `2^{1−k}` and the pair `(1, 16)` by `4^{1−k}`. -/
theorem not_conformal_powerMap {k : ℕ} (hk : 2 ≤ k) :
    ¬ ∃ c : ℝ, ∀ m n : ℕ, weilPrimeKernel (m ^ k) (n ^ k) = c * weilPrimeKernel m n := by
  rintro ⟨c, hc⟩
  have h4 := hc 1 4
  have h16 := hc 1 16
  rw [one_pow, show (4 : ℕ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num,
    show (4 : ℕ) = 2 ^ (2 * 1) by norm_num, weilPrimeKernel_one_two_pow_even (by omega),
    weilPrimeKernel_one_two_pow_even le_rfl] at h4
  rw [one_pow, show (16 : ℕ) ^ k = 2 ^ (2 * (2 * k)) by rw [pow_mul, pow_mul]; norm_num,
    show (16 : ℕ) = 2 ^ (2 * 2) by norm_num, weilPrimeKernel_one_two_pow_even (by omega),
    weilPrimeKernel_one_two_pow_even (by norm_num)] at h16
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set X : ℝ := 2 ^ k with hX
  have hpos : 0 < X := by positivity
  have h2k : (2 : ℝ) ^ (2 * k) = X ^ 2 := by rw [hX, ← pow_mul, mul_comm]
  rw [h2k] at h16
  have e4 : Real.log 2 * 2 = c * Real.log 2 * X := by
    field_simp at h4; linarith
  have e16 : Real.log 2 * 4 = c * Real.log 2 * X ^ 2 := by
    field_simp at h16; linarith
  have hX2 : Real.log 2 * (X - 2) = 0 := by nlinarith
  have hX2' : X = 2 := by
    rcases mul_eq_zero.mp hX2 with h | h
    · linarith
    · linarith
  have : (2 : ℝ) ^ 2 ≤ X := by rw [hX]; exact pow_le_pow_right₀ (by norm_num) hk
  norm_num at this
  linarith

/-- **The successor is not conformal**: no constant `c` has `P_{N+1}(Sx) = c P_N(x)` for all
profiles. -/
theorem not_conformal_succShift :
    ¬ ∃ c : ℝ, ∀ (N : ℕ) (x : ℕ → ℝ),
      atomicWeilForm (N + 1) (succShiftProfile x) = c * atomicWeilForm N x := by
  rintro ⟨c, hc⟩
  have hzero : atomicWeilForm 5 (fun n => if n = 2 ∨ n = 5 then 1 else 0) = 0 := by
    have k25 : weilPrimeKernel 2 5 = 0 :=
      weilPrimeKernel_eq_zero_of_coprime (by norm_num) (by norm_num) (by norm_num)
    simp only [atomicWeilForm, show Icc 1 5 = {1, 2, 3, 4, 5} by decide]
    norm_num [weilPrimeKernel_self, k25, weilPrimeKernel_comm 5 2]
  have := atomicWeilForm_succShift_not_monotone.2
  rw [hc 5, hzero, mul_zero] at this
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
