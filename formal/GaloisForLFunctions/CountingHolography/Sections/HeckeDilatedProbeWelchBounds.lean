import GaloisForLFunctions.CountingHolography.Sections.PrimeDisplacementGramAndModeQuotients
import GaloisForLFunctions.HTGeometry.SpectralEnsembleEigenvalueBound
import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetSecularAndWallRigidity
import Mathlib.Algebra.Order.Chebyshev

/-!
# Hecke-Dilated Negative Probe Welch Bounds and Single-Quartet Correlation Floors

By the Born-rule isometry (`CountingHolography.integerProbe_dilate`), every positive integer
dilation `T_d` preserves the spline Krein square `integerProbe` identically. Embedding `m` Hecke
dilations `T_{d_0} a_0, ..., T_{d_{m-1}} a_0` of a single negative integer probe `a_0` into a common
ambient cutoff `M ≥ d_i N_0` combines Hecke covariance with the negative-index Welch trace inequality:

1. **Ambient Hecke isometry, joint scale invariance, and prime-multiplier disjointness**
   (`integerProbe_heckeDilateAt`, `probePairing_heckeDilateAt_mul_left`,
   `disjoint_activeConductors_heckeDilateAt_of_sep`,
   `disjoint_activeConductors_heckeDilateAt_of_primes`):
   Each `heckeDilateAt` has exact self-pairing `integerProbe N₀ a₀`, cross-pairings are invariant
   under simultaneous dilation `(d₁, d₂, M) ↦ (k d₁, k d₂, k M)`, and conductor supports are
   disjoint whenever `d₁ N₀ < d₂` or whenever `d₁ ≠ d₂` are primes exceeding `N₀`.

2. **Finite-right-support Welch floor across arbitrary Hecke multipliers**
   (`finite_right_support_heckeDilate_energy`, `exists_heckeDilate_pair_correlation`):
   If `#(rightZeros zetaZeroConfig) ≤ r`, any `m` Hecke dilations of any negative probe `a₀` satisfy
   `m (m - r) Q(a₀)² ≤ r ∑_{i ≠ j} ⟨T_{d_i} a₀, T_{d_j} a₀⟩²`, and for `m ≥ 2` some pair `i ≠ j`
   satisfies `(m - r) Q(a₀)² ≤ r (m - 1) ⟨T_{d_i} a₀, T_{d_j} a₀⟩²`.

3. **Single-quartet correlation floor (`1/2` at `m = 3`, asymptotic `1/√2`) and converse exclusion**
   (`singleQuartet_heckeDilate_welch_bound`, `singleQuartet_three_heckeDilates_pair_ge_half`,
   `four_le_rightZeros_of_three_heckeDilates`):
   Under `HasSingleOffLineQuartet ρ₀` (`r = 2`), every triple of Hecke dilations of a negative probe
   contains a pair with `|⟨T_{d_i} a₀, T_{d_j} a₀⟩| ≥ |Q(a₀)| / 2`, while as `m → ∞` the maximum
   squared correlation is at least `(m - 2) / (2 (m - 1)) → 1/2`. Conversely, any triple of Hecke
   dilations with total off-diagonal squared pairing `< (3/2) Q(a₀)²` forces `#(rightZeros) ≥ 4` and
   excludes `HasSingleOffLineQuartet` globally.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable section
set_option autoImplicit false

open Finset Matrix Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.CountingHolography.Sections

open ArithmeticScatteringHolography CountingHolography HTGeometry
open HeckeKreinToeplitz ArithmeticCastelnuovoSeveri RenormalizedIntersectionTheory
open Zeta23 ExclusionOfTheCriticalState

/-! ## 1. Ambient Hecke dilation into a common cutoff `M ≥ d N₀` -/

/-- Index embedding sending atom `i + 1` (`i : Fin N₀`) to `d * (i + 1)` inside `Fin M`. -/
def heckeDilateIndex {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M) (i : Fin N₀) : Fin M :=
  ⟨d * ((i : ℕ) + 1) - 1, by
    have h1 : d * ((i : ℕ) + 1) ≤ d * N₀ := Nat.mul_le_mul_left d i.2
    have h2 : 1 ≤ d * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega⟩

theorem heckeDilateIndex_val_add_one {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M) (i : Fin N₀) :
    (heckeDilateIndex hd hM i : ℕ) + 1 = d * ((i : ℕ) + 1) := by
  have h2 : 1 ≤ d * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [heckeDilateIndex]
  omega

theorem heckeDilateIndex_injective {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M) :
    Function.Injective (heckeDilateIndex hd hM) := by
  intro i j hij
  have h := congrArg (fun k : Fin M => (k : ℕ) + 1) hij
  rw [heckeDilateIndex_val_add_one, heckeDilateIndex_val_add_one] at h
  have hij_add := Nat.eq_of_mul_eq_mul_left hd h
  exact Fin.ext (by omega)

/-- Ambient Hecke dilation `T_d a₀ : Fin M → ℤ` extending `a₀` by `0` outside `{d(i+1)}`. -/
def heckeDilateAt {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M) (a₀ : Fin N₀ → ℤ) : Fin M → ℤ :=
  Function.extend (heckeDilateIndex hd hM) a₀ 0

@[simp] theorem heckeDilateAt_apply_index {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M)
    (a₀ : Fin N₀ → ℤ) (i : Fin N₀) :
    heckeDilateAt hd hM a₀ (heckeDilateIndex hd hM i) = a₀ i :=
  (heckeDilateIndex_injective hd hM).extend_apply a₀ 0 i

theorem heckeDilateAt_eq_zero_of_not_mem_range {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M)
    (a₀ : Fin N₀ → ℤ) {k : Fin M} (hk : ¬ ∃ i : Fin N₀, heckeDilateIndex hd hM i = k) :
    heckeDilateAt hd hM a₀ k = 0 :=
  Function.extend_apply' _ _ _ hk

theorem heckeDilateAt_add {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M)
    (a b : Fin N₀ → ℤ) :
    heckeDilateAt hd hM (a + b) = heckeDilateAt hd hM a + heckeDilateAt hd hM b := by
  funext k
  by_cases hk : ∃ i : Fin N₀, heckeDilateIndex hd hM i = k
  · obtain ⟨i, rfl⟩ := hk
    simp
  · simp [heckeDilateAt_eq_zero_of_not_mem_range hd hM _ hk]

/-- **Exact ambient Hecke isometry:** `integerProbe M (heckeDilateAt hd hM a₀) = integerProbe N₀ a₀`. -/
theorem integerProbe_heckeDilateAt {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M)
    (a₀ : Fin N₀ → ℤ) :
    integerProbe M (heckeDilateAt hd hM a₀) = integerProbe N₀ a₀ := by
  have hcast : (fun k : Fin M => ((heckeDilateAt hd hM a₀ k : ℤ) : ℂ)) =
      Function.extend (heckeDilateIndex hd hM) (fun i : Fin N₀ => (a₀ i : ℂ)) 0 := by
    funext k
    by_cases hk : ∃ i : Fin N₀, heckeDilateIndex hd hM i = k
    · obtain ⟨i, rfl⟩ := hk
      simp [(heckeDilateIndex_injective hd hM).extend_apply]
    · simp [heckeDilateAt, Function.extend_apply' _ _ _ hk]
  unfold integerProbe
  rw [hcast, hermQuad_extend (heckeDilateIndex_injective hd hM)]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, atomGram_eq_ratio]
  have hval_i : ((heckeDilateIndex hd hM i : ℕ) : ℝ) + 1 = (d : ℝ) * ((i : ℝ) + 1) := by
    exact_mod_cast heckeDilateIndex_val_add_one hd hM i
  have hval_j : ((heckeDilateIndex hd hM j : ℕ) : ℝ) + 1 = (d : ℝ) * ((j : ℝ) + 1) := by
    exact_mod_cast heckeDilateIndex_val_add_one hd hM j
  rw [hval_i, hval_j, mul_div_mul_left _ _ (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]

@[simp] theorem probePairing_heckeDilateAt_self {M d N₀ : ℕ} (hd : 0 < d) (hM : d * N₀ ≤ M)
    (a₀ : Fin N₀ → ℤ) :
    probePairing M (heckeDilateAt hd hM a₀) (heckeDilateAt hd hM a₀) = integerProbe N₀ a₀ := by
  rw [probePairing_self, integerProbe_heckeDilateAt]

/-- Composition law `T_k (T_d a₀) = T_{k d} a₀`. -/
theorem heckeDilateAt_comp {K M k d N₀ : ℕ} (hk : 0 < k) (hd : 0 < d)
    (hM : d * N₀ ≤ M) (hK : k * M ≤ K) (a₀ : Fin N₀ → ℤ) :
    heckeDilateAt hk hK (heckeDilateAt hd hM a₀) =
      heckeDilateAt (Nat.mul_pos hk hd)
        (by calc (k * d) * N₀ = k * (d * N₀) := Nat.mul_assoc k d N₀
              _ ≤ k * M := Nat.mul_le_mul_left k hM
              _ ≤ K := hK) a₀ := by
  have hkd : 0 < k * d := Nat.mul_pos hk hd
  have hkdM : (k * d) * N₀ ≤ K :=
    (Nat.mul_assoc k d N₀).symm ▸ (Nat.mul_le_mul_left k hM).trans hK
  have hidx : ∀ i : Fin N₀,
      heckeDilateIndex hk hK (heckeDilateIndex hd hM i) = heckeDilateIndex hkd hkdM i := by
    intro i
    apply Fin.ext
    have h1 := heckeDilateIndex_val_add_one hk hK (heckeDilateIndex hd hM i)
    have h2 := heckeDilateIndex_val_add_one hd hM i
    have h3 := heckeDilateIndex_val_add_one hkd hkdM i
    rw [h2, ← Nat.mul_assoc] at h1
    omega
  funext r
  by_cases hr : ∃ i : Fin N₀, heckeDilateIndex hkd hkdM i = r
  · obtain ⟨i, rfl⟩ := hr
    rw [heckeDilateAt_apply_index, ← hidx i, heckeDilateAt_apply_index, heckeDilateAt_apply_index]
  · rw [heckeDilateAt_eq_zero_of_not_mem_range hkd hkdM a₀ hr]
    by_cases hr' : ∃ j : Fin M, heckeDilateIndex hk hK j = r
    · obtain ⟨j, rfl⟩ := hr'
      rw [heckeDilateAt_apply_index]
      refine heckeDilateAt_eq_zero_of_not_mem_range hd hM a₀ ?_
      rintro ⟨i, rfl⟩
      exact hr ⟨i, (hidx i).symm⟩
    · exact heckeDilateAt_eq_zero_of_not_mem_range hk hK _ hr'

/-- **Joint Hecke scale invariance of cross-pairings:** scaling `(d₁, d₂, M)` by `k ≥ 1` preserves
`probePairing` identically. -/
theorem probePairing_heckeDilateAt_mul_left {M d₁ d₂ N₀ k : ℕ}
    (hk : 0 < k) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hM₁ : d₁ * N₀ ≤ M) (hM₂ : d₂ * N₀ ≤ M) (a b : Fin N₀ → ℤ) :
    probePairing (k * M)
      (heckeDilateAt (Nat.mul_pos hk hd₁)
        (by calc (k * d₁) * N₀ = k * (d₁ * N₀) := Nat.mul_assoc _ _ _
              _ ≤ k * M := Nat.mul_le_mul_left k hM₁) a)
      (heckeDilateAt (Nat.mul_pos hk hd₂)
        (by calc (k * d₂) * N₀ = k * (d₂ * N₀) := Nat.mul_assoc _ _ _
              _ ≤ k * M := Nat.mul_le_mul_left k hM₂) b) =
    probePairing M (heckeDilateAt hd₁ hM₁ a) (heckeDilateAt hd₂ hM₂ b) := by
  rw [← heckeDilateAt_comp hk hd₁ hM₁ le_rfl a,
    ← heckeDilateAt_comp hk hd₂ hM₂ le_rfl b,
    probePairing_eq_polar, probePairing_eq_polar,
    ← heckeDilateAt_add hk le_rfl,
    integerProbe_heckeDilateAt, integerProbe_heckeDilateAt, integerProbe_heckeDilateAt]

/-- Scale separation `d₁ * N₀ < d₂` makes the active conductors of `T_{d₁} a` and `T_{d₂} b`
disjoint for arbitrary probes `a, b : Fin N₀ → ℤ`. -/
theorem disjoint_activeConductors_heckeDilateAt_of_sep {M d₁ d₂ N₀ : ℕ}
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hM₁ : d₁ * N₀ ≤ M) (hM₂ : d₂ * N₀ ≤ M)
    (hsep : d₁ * N₀ < d₂) (a b : Fin N₀ → ℤ) :
    Disjoint (activeConductors (heckeDilateAt hd₁ hM₁ a))
      (activeConductors (heckeDilateAt hd₂ hM₂ b)) := by
  rw [disjoint_activeConductors_iff]
  intro r
  by_cases h1 : ∃ i : Fin N₀, heckeDilateIndex hd₁ hM₁ i = r
  · right
    obtain ⟨i, hi⟩ := h1
    refine heckeDilateAt_eq_zero_of_not_mem_range hd₂ hM₂ b ?_
    rintro ⟨j, hj⟩
    have hc1 := heckeDilateIndex_val_add_one hd₁ hM₁ i
    have hc2 := heckeDilateIndex_val_add_one hd₂ hM₂ j
    rw [hi] at hc1
    rw [hj] at hc2
    have hle1 : d₁ * ((i : ℕ) + 1) ≤ d₁ * N₀ := Nat.mul_le_mul_left d₁ i.2
    have hge2 : d₂ ≤ d₂ * ((j : ℕ) + 1) := Nat.le_mul_of_pos_right d₂ (Nat.succ_pos _)
    omega
  · left
    exact heckeDilateAt_eq_zero_of_not_mem_range hd₁ hM₁ a h1

/-- Distinct prime multipliers `p₁ ≠ p₂` exceeding `N₀` produce disjoint active conductor sets even
inside the same dyadic shell. -/
theorem disjoint_activeConductors_heckeDilateAt_of_primes {M p₁ p₂ N₀ : ℕ}
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hne : p₁ ≠ p₂)
    (hN₁ : N₀ < p₁) (hM₁ : p₁ * N₀ ≤ M) (hM₂ : p₂ * N₀ ≤ M) (a b : Fin N₀ → ℤ) :
    Disjoint (activeConductors (heckeDilateAt hp₁.pos hM₁ a))
      (activeConductors (heckeDilateAt hp₂.pos hM₂ b)) := by
  rw [disjoint_activeConductors_iff]
  intro r
  by_cases h1 : ∃ i : Fin N₀, heckeDilateIndex hp₁.pos hM₁ i = r
  · right
    obtain ⟨i, hi⟩ := h1
    refine heckeDilateAt_eq_zero_of_not_mem_range hp₂.pos hM₂ b ?_
    rintro ⟨j, hj⟩
    have hc1 := heckeDilateIndex_val_add_one hp₁.pos hM₁ i
    have hc2 := heckeDilateIndex_val_add_one hp₂.pos hM₂ j
    rw [hi] at hc1
    rw [hj] at hc2
    have hdvd_mul : p₁ ∣ p₂ * ((j : ℕ) + 1) := ⟨(i : ℕ) + 1, hc2.symm.trans hc1⟩
    rcases hp₁.dvd_mul.mp hdvd_mul with hp12 | hp1j
    · exact hne ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hp12)
    · have hle := Nat.le_of_dvd (Nat.succ_pos j) hp1j
      have hj_le : (j : ℕ) + 1 ≤ N₀ := j.2
      omega
  · left
    exact heckeDilateAt_eq_zero_of_not_mem_range hp₁.pos hM₁ a h1

/-! ## 2. Finite-right-support Welch lower bounds across Hecke dilations -/

private theorem neg_trace_sq_le_hermNegIndex_mul_trace_sq {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}
    (hH : H.IsHermitian) (ht : H.trace.re ≤ 0) :
    H.trace.re ^ 2 ≤ (hermNegIndex H : ℝ) * ((H ^ 2).trace).re := by
  let e := hH.eigenvalues
  let S := univ.filter (fun i => e i < 0)
  have htr : ∑ i, e i = H.trace.re := by
    have h := (congrArg Complex.re hH.trace_eq_sum_eigenvalues).symm
    rw [Complex.re_sum] at h
    simpa only [Complex.ofReal_re] using h
  have hpart := sum_filter_add_sum_filter_not univ (fun i => e i < 0) e
  have hrest : 0 ≤ ∑ i ∈ univ.filter (fun i => ¬ e i < 0), e i :=
    sum_nonneg fun i hi => le_of_not_gt (mem_filter.mp hi).2
  have hle : -H.trace.re ≤ ∑ i ∈ S, -e i := by
    rw [sum_neg_distrib]
    change -H.trace.re ≤ -(∑ i ∈ univ.filter (fun i => e i < 0), e i)
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => -e i)
  simp only [neg_sq] at hcs
  have hsub := sum_le_sum_of_subset_of_nonneg (filter_subset (fun i => e i < 0) univ)
    (fun i _ _ => sq_nonneg (e i))
  rw [negIndex_eq_card_neg_eigenvalues hH, ← sum_sq_eigenvalues_eq_trace_sq_re hH]
  calc H.trace.re ^ 2 = (-H.trace.re) ^ 2 := (neg_sq _).symm
    _ ≤ (S.card : ℝ) * ∑ i ∈ S, e i ^ 2 :=
        (pow_le_pow_left₀ (neg_nonneg.mpr ht) hle 2).trans hcs
    _ ≤ (S.card : ℝ) * ∑ i, e i ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg S.card)

private theorem hermNegIndex_probeGramMatrix_le_rightZeros {m M : ℕ}
    (fam : Fin m → (Fin M → ℤ)) :
    (hermNegIndex (probeGramMatrix M fam) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard := by
  rw [rightZeros_encard_eq_sectionIndex]
  simp only [sectionMatrix_eq_atomGram]
  exact (show (hermNegIndex (probeGramMatrix M fam) : ℕ∞) ≤ hermNegIndex (atomGram M) by
    exact_mod_cast hermNegIndex_probeGramMatrix_le M fam).trans
      (le_iSup (fun K : ℕ => (hermNegIndex (atomGram K) : ℕ∞)) M)

/-- **Hecke-dilated Welch energy theorem.**
For any negative integer probe `a₀` (`integerProbe N₀ a₀ < 0`) and any `m` positive multipliers
`d : Fin m → ℕ` inside cutoff `M`, `#(rightZeros zetaZeroConfig) ≤ r` forces
`m (m - r) Q(a₀)² ≤ r ∑_{i ≠ j} ⟨T_{d_i} a₀, T_{d_j} a₀⟩²`. -/
theorem finite_right_support_heckeDilate_energy {r m M N₀ : ℕ}
    (hr : (rightZeros zetaZeroConfig).encard ≤ r)
    {a₀ : Fin N₀ → ℤ} (hneg : integerProbe N₀ a₀ < 0)
    (d : Fin m → ℕ) (hd : ∀ i : Fin m, 0 < d i) (hM : ∀ i : Fin m, d i * N₀ ≤ M) :
    (m : ℝ) * ((m : ℝ) - r) * (integerProbe N₀ a₀) ^ 2 ≤
      (r : ℝ) * ∑ i : Fin m, ∑ j ∈ univ.erase i,
        (probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)) ^ 2 := by
  let fam : Fin m → (Fin M → ℤ) := fun i => heckeDilateAt (hd i) (hM i) a₀
  let H : Matrix (Fin m) (Fin m) ℂ := probeGramMatrix M fam
  have hH : H.IsHermitian := probeGramMatrix_isHermitian M fam
  have hself : ∀ i : Fin m, probePairing M (fam i) (fam i) = integerProbe N₀ a₀ := fun i =>
    probePairing_heckeDilateAt_self (hd i) (hM i) a₀
  have htr : H.trace.re = (m : ℝ) * integerProbe N₀ a₀ := by
    simp only [H, probeGramMatrix, Matrix.trace, Matrix.diag_apply, Matrix.of_apply,
      Complex.re_sum, Complex.ofReal_re, hself, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have htr_le : H.trace.re ≤ 0 := by
    rw [htr]; exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hneg.le
  have hrow : ∀ i : Fin m, ∑ j : Fin m, (probePairing M (fam i) (fam j)) ^ 2 =
      (integerProbe N₀ a₀) ^ 2 + ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2 := by
    intro i
    rw [← add_sum_erase univ _ (mem_univ i), hself i]
  have htr2 : ((H ^ 2).trace).re =
      (m : ℝ) * (integerProbe N₀ a₀) ^ 2 +
        ∑ i : Fin m, ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2 := by
    simp only [H, probeGramMatrix, sq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.of_apply, Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    calc (∑ i : Fin m, ∑ j : Fin m, probePairing M (fam i) (fam j) * probePairing M (fam j) (fam i))
        = ∑ i : Fin m, ∑ j : Fin m, (probePairing M (fam i) (fam j)) ^ 2 := by
          refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
          rw [probePairing_symm M (fam j) (fam i), sq]
      _ = (m : ℝ) * (integerProbe N₀ a₀) ^ 2 +
            ∑ i : Fin m, ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2 := by
          simp only [hrow, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcs := neg_trace_sq_le_hermNegIndex_mul_trace_sq hH htr_le
  rw [htr, htr2] at hcs
  have hidx : hermNegIndex H ≤ r := by
    exact_mod_cast (hermNegIndex_probeGramMatrix_le_rightZeros fam).trans hr
  have htr2_nn : 0 ≤ (m : ℝ) * (integerProbe N₀ a₀) ^ 2 +
      ∑ i : Fin m, ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2 :=
    add_nonneg (by positivity) (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
  have hidx_mul : (hermNegIndex H : ℝ) *
      ((m : ℝ) * (integerProbe N₀ a₀) ^ 2 +
        ∑ i : Fin m, ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2) ≤
      (r : ℝ) * ((m : ℝ) * (integerProbe N₀ a₀) ^ 2 +
        ∑ i : Fin m, ∑ j ∈ univ.erase i, (probePairing M (fam i) (fam j)) ^ 2) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hidx) htr2_nn
  nlinarith

/-- **Pairwise Hecke-dilation Welch bound.**
Under `#(rightZeros zetaZeroConfig) ≤ r`, among any `m ≥ 2` Hecke dilations of a negative probe `a₀`
there exist `i ≠ j` satisfying `(m - r) Q(a₀)² ≤ r (m - 1) ⟨T_{d_i} a₀, T_{d_j} a₀⟩²`. -/
theorem exists_heckeDilate_pair_correlation {r m M N₀ : ℕ} (hm : 2 ≤ m)
    (hr : (rightZeros zetaZeroConfig).encard ≤ r)
    {a₀ : Fin N₀ → ℤ} (hneg : integerProbe N₀ a₀ < 0)
    (d : Fin m → ℕ) (hd : ∀ i : Fin m, 0 < d i) (hM : ∀ i : Fin m, d i * N₀ ≤ M) :
    ∃ i j : Fin m, i ≠ j ∧
      ((m : ℝ) - r) * (integerProbe N₀ a₀) ^ 2 ≤
        (r : ℝ) * ((m : ℝ) - 1) *
          (probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)) ^ 2 := by
  by_contra! h
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let fam : Fin m → (Fin M → ℤ) := fun i => heckeDilateAt (hd i) (hM i) a₀
  have hrow : ∀ i : Fin m,
      ∑ j ∈ univ.erase i, ((r : ℝ) * ((m : ℝ) - 1) * (probePairing M (fam i) (fam j)) ^ 2) <
        ∑ _j ∈ univ.erase i, (((m : ℝ) - r) * (integerProbe N₀ a₀) ^ 2) := by
    intro i
    have hcard : (univ.erase i).card = m - 1 := by simp
    refine sum_lt_sum_of_nonempty (card_pos.mp (by omega)) fun j hj => ?_
    exact h i j (mem_erase.mp hj).1.symm
  have hsum_lt := sum_lt_sum_of_nonempty (s := univ) univ_nonempty fun i _ => hrow i
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
  simp only [← mul_sum, sum_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin,
    nsmul_eq_mul, hcast] at hsum_lt
  have hwelch := finite_right_support_heckeDilate_energy hr hneg d hd hM
  have hm1_nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    linarith
  have hmul := mul_le_mul_of_nonneg_left hwelch hm1_nn
  dsimp [fam] at hsum_lt
  nlinarith

/-! ## 3. Single-quartet Welch floor (`r = 2`) and three-dilation converse exclusion -/

private theorem rightZeros_encard_le_two_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) :
    (rightZeros zetaZeroConfig).encard ≤ 2 := by
  have hsub : rightZeros zetaZeroConfig ⊆ ({ρ₀, conj ρ₀} : Set ℂ) := by
    rintro z ⟨hz_car, hz_re⟩
    have hmem : z ∈ zeroQuartetSet ρ₀ := by
      rw [← hq.2.2]
      exact ⟨hz_car, ne_of_gt hz_re⟩
    simp only [zeroQuartetSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso; simp at hz_re; linarith [hq.1]
    · exfalso; simp at hz_re; linarith [hq.1]
  calc (rightZeros zetaZeroConfig).encard
      ≤ ({ρ₀, conj ρ₀} : Set ℂ).encard := Set.encard_le_encard hsub
    _ ≤ 2 := Set.encard_pair_le ρ₀ (conj ρ₀)

/-- **Single-quartet Hecke-dilation Welch bound.**
Under `HasSingleOffLineQuartet ρ₀`, any `m ≥ 2` Hecke dilations of a negative probe `a₀` satisfy
`m (m - 2) Q(a₀)² ≤ 2 ∑_{i ≠ j} ⟨T_{d_i} a₀, T_{d_j} a₀⟩²` and admit `i ≠ j` with
`(m - 2) Q(a₀)² ≤ 2 (m - 1) ⟨T_{d_i} a₀, T_{d_j} a₀⟩²`. -/
theorem singleQuartet_heckeDilate_welch_bound {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {m M N₀ : ℕ} (hm : 2 ≤ m)
    {a₀ : Fin N₀ → ℤ} (hneg : integerProbe N₀ a₀ < 0)
    (d : Fin m → ℕ) (hd : ∀ i : Fin m, 0 < d i) (hM : ∀ i : Fin m, d i * N₀ ≤ M) :
    (m : ℝ) * ((m : ℝ) - 2) * (integerProbe N₀ a₀) ^ 2 ≤
      2 * ∑ i : Fin m, ∑ j ∈ univ.erase i,
        (probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)) ^ 2 ∧
    ∃ i j : Fin m, i ≠ j ∧
      ((m : ℝ) - 2) * (integerProbe N₀ a₀) ^ 2 ≤
        2 * ((m : ℝ) - 1) *
          (probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)) ^ 2 := by
  have hr2 := rightZeros_encard_le_two_of_singleQuartet hq
  exact ⟨by simpa using finite_right_support_heckeDilate_energy hr2 hneg d hd hM,
    by simpa using exists_heckeDilate_pair_correlation hm hr2 hneg d hd hM⟩

/-- **Three-dilation `1/2`-correlation floor under `HasSingleOffLineQuartet ρ₀`.**
For any negative integer probe `a₀` and any three positive multipliers `d : Fin 3 → ℕ`, a lone
off-line quartet forces some distinct pair `(i, j)` to satisfy
`|⟨T_{d_i} a₀, T_{d_j} a₀⟩| ≥ (-integerProbe N₀ a₀) / 2`. -/
theorem singleQuartet_three_heckeDilates_pair_ge_half {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {M N₀ : ℕ}
    {a₀ : Fin N₀ → ℤ} (hneg : integerProbe N₀ a₀ < 0)
    (d : Fin 3 → ℕ) (hd : ∀ i : Fin 3, 0 < d i) (hM : ∀ i : Fin 3, d i * N₀ ≤ M) :
    ∃ i j : Fin 3, i ≠ j ∧
      (-integerProbe N₀ a₀) / 2 ≤
        |probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)| := by
  obtain ⟨-, i, j, hij, hpair⟩ :=
    singleQuartet_heckeDilate_welch_bound hq (by decide : 2 ≤ 3) hneg d hd hM
  refine ⟨i, j, hij, ?_⟩
  have hsq : ((-integerProbe N₀ a₀) / 2) ^ 2 ≤
      |probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)| ^ 2 := by
    rw [sq_abs]
    push_cast at hpair
    linarith
  exact le_of_sq_le_sq hsq (abs_nonneg _)

/-- **Converse single-quartet exclusion from three weakly-correlated Hecke dilations.**
If any negative integer probe `a₀` admits three positive multipliers `d : Fin 3 → ℕ` whose
off-diagonal squared pairings sum to strictly less than `(3/2) Q(a₀)²`, then
`(4 : ℕ∞) ≤ #(rightZeros zetaZeroConfig)` and `∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀`. -/
theorem four_le_rightZeros_of_three_heckeDilates {M N₀ : ℕ}
    {a₀ : Fin N₀ → ℤ} (hneg : integerProbe N₀ a₀ < 0)
    (d : Fin 3 → ℕ) (hd : ∀ i : Fin 3, 0 < d i) (hM : ∀ i : Fin 3, d i * N₀ ≤ M)
    (hlow : 2 * ∑ i : Fin 3, ∑ j ∈ univ.erase i,
      (probePairing M (heckeDilateAt (hd i) (hM i) a₀) (heckeDilateAt (hd j) (hM j) a₀)) ^ 2 <
        3 * (integerProbe N₀ a₀) ^ 2) :
    ((4 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard ∧
      ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  have hnRH : ¬ RiemannHypothesis := fun hRH =>
    (not_lt_of_ge (riemannHypothesis_iff_integerProbes.mp hRH N₀ a₀)) hneg
  have hno_q : ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
    intro ρ₀ hq
    have hge := (singleQuartet_heckeDilate_welch_bound hq (by decide : 2 ≤ 3) hneg d hd hM).1
    push_cast at hge
    linarith
  have hge4 : ((4 : ℕ) : ℕ∞) ≤ (rightZeros zetaZeroConfig).encard :=
    (no_singleOffLineQuartet_iff_rh_or_four_le_rightZeros.mp hno_q).resolve_left hnRH
  exact ⟨hge4, hno_q⟩

end GaloisForLFunctions.CountingHolography.Sections

end
