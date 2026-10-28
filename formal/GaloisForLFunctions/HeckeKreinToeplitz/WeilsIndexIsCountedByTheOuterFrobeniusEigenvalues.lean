import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheTrickleDownInequalityIsTheSquareRootCount

/-!
# Weil's index is counted by the outer Frobenius eigenvalues

The calibration of the theory over `𝔽_q`. A curve datum `D` (normalized Frobenius eigenvalues `β_i`,
closed under conjugation and under `β ↦ 1/β` by the functional equation) has the **trace kernel**
`n ↦ Σ_i β_i^n` on `ℤ` (`CurveDatum.traceKernel`), a Hermitian kernel on the one-generator lattice.

**Krein–Langer decomposition** (`traceKernel_eq`). The reflection `σ = fe ∘ conj` sends `β_i` to
`1/β̄_i`, so it pairs the eigenvalues outside the unit circle with those inside. The trace kernel is
the positive-definite sum of the unitary eigenvalues plus one hyperbolic pair `β^n + β̄^{−n}` for each
outer eigenvalue.

**Index formula** (`negIndex_traceKernel`). Its negative index is the number of distinct eigenvalues
of modulus `> 1`; merged eigenvalues add positive multiplicities, so no class cancels.

**Weil's theorem as index zero** (`negIndex_traceKernel_eq_zero_tfae`). Index zero ⇔ every
`|β_i| = 1` ⇔ the square-root count `N_k ≥ q^k + 1 − C q^{k/2}` ⇔ (for nonnegative counts) the
trickle-down inequality on every Frobenius ladder. The global law (a count) computes the index; the
golden datum `1 − 5X + 5X²`, which has every soft structure, has index exactly one
(`negIndex_golden_traceKernel`).
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (CurveDatum goldenDatum)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### Positive-definite kernels: sums and unitary characters -/

section PosDef

variable {G : Type*} [Group G]

theorem isPosDefKernel_finset_sum {J : Type*} (s : Finset J) {k : J → G → ℂ}
    (hk : ∀ j ∈ s, IsPosDefKernel (k j)) : IsPosDefKernel fun u => ∑ j ∈ s, k j u :=
  ⟨isHermKernel_finset_sum s fun j hj => (hk j hj).1, fun n x c => by
    rw [hermQuad_gram_sum]
    exact sum_nonneg fun j hj => (hk j hj).hermQuad_nonneg x c⟩

theorem IsPosDefKernel.add {p₁ p₂ : G → ℂ} (h₁ : IsPosDefKernel p₁) (h₂ : IsPosDefKernel p₂) :
    IsPosDefKernel fun u => p₁ u + p₂ u :=
  ⟨h₁.1.add h₂.1, fun n x c => by
    rw [hermQuad_gram_add]; exact add_nonneg (h₁.hermQuad_nonneg x c) (h₂.hermQuad_nonneg x c)⟩

/-- A unitary character is a positive-definite kernel. -/
theorem isPosDefKernel_of_unitary {χ : G →* ℂ} (hχ : IsUnitaryChar χ) : IsPosDefKernel χ := by
  have hk : (fun u => χ u) = pairKernel χ (1 / 2) := by
    funext u
    rw [pairKernel, reflectChar_eq_of_unitary hχ]
    simp only [map_div₀, map_one, Complex.conj_ofNat]
    ring
  have hh : IsHermKernel (fun u => χ u) := hk ▸ isHermKernel_pairKernel χ _
  refine ⟨hh, fun n x c => ?_⟩
  rw [show (χ : G → ℂ) = pairKernel χ (1 / 2) from hk, hermQuad_gram_pairKernel_of_unitary hχ]
  exact mul_nonneg (mul_nonneg zero_le_two (by norm_num)) (Complex.normSq_nonneg _)

end PosDef

/-! ### Characters of `ℤ` -/

theorem reflectChar_valChar {v : ℂ} (hv : v ≠ 0) : reflectChar (valChar v) = valChar (conj v)⁻¹ := by
  have hv' : (conj v)⁻¹ ≠ 0 := inv_ne_zero (star_ne_zero.mpr hv)
  refine MonoidHom.ext fun n => ?_
  simp only [reflectChar_apply, valChar, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hv, if_neg hv',
    toAdd_inv, zpow_neg, map_inv₀, map_zpow₀, inv_zpow']

theorem norm_valChar {v : ℂ} (hv : v ≠ 0) (n : Multiplicative ℤ) :
    ‖valChar v n‖ = ‖v‖ ^ Multiplicative.toAdd n := by
  simp only [valChar, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hv, norm_zpow]

theorem isUnitaryChar_valChar {v : ℂ} (hv : ‖v‖ = 1) : IsUnitaryChar (valChar v) := fun n => by
  rw [norm_valChar (by rintro rfl; simp at hv), hv, one_zpow]

theorem zpowersHom_ofAdd_one (n : Multiplicative ℤ) :
    zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd 1) n = n := by
  rw [zpowersHom_apply, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

/-! ### The trace kernel of a curve datum -/

namespace CurveDatumKernel

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem β_ne_zero (i : ι) : D.β i ≠ 0 := right_ne_zero_of_mul_eq_one (D.β_fePerm i)

/-- The reflection `σ = fe ∘ conj` of the eigenvalues: `β_{σ i} = 1/β̄_i`. -/
def reflectPerm : Equiv.Perm ι := D.conjPerm.trans D.fePerm

theorem β_reflectPerm (i : ι) : D.β (reflectPerm D i) = (conj (D.β i))⁻¹ := by
  have h := D.β_fePerm (D.conjPerm i)
  rw [D.β_conjPerm] at h
  exact eq_inv_of_mul_eq_one_left h

theorem norm_β_reflectPerm (i : ι) : ‖D.β (reflectPerm D i)‖ = ‖D.β i‖⁻¹ := by
  rw [β_reflectPerm, norm_inv, Complex.norm_conj]

/-- The outer eigenvalues, `|β_i| > 1`. -/
def outer : Finset ι := univ.filter fun i => 1 < ‖D.β i‖

end CurveDatumKernel

open CurveDatumKernel

/-- The trace kernel `n ↦ Σ_i β_i^n` of a curve datum on `ℤ`. -/
def traceKernel {ι : Type*} [Fintype ι] (D : CurveDatum ι) : Multiplicative ℤ → ℂ :=
  fun n => ∑ i, valChar (D.β i) n

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Krein–Langer decomposition of the trace kernel.** Unitary eigenvalues give a
positive-definite part; each outer eigenvalue `β` with its reflection `1/β̄` gives one hyperbolic
pair. -/
theorem traceKernel_eq (n : Multiplicative ℤ) :
    traceKernel D n = ∑ i ∈ univ.filter (fun i => ‖D.β i‖ = 1), valChar (D.β i) n +
      ∑ i ∈ outer D, pairKernel (valChar (D.β i)) 1 n := by
  classical
  set f : ι → ℂ := fun i => valChar (D.β i) n
  have hpos : ∀ i, 0 < ‖D.β i‖ := fun i => norm_pos_iff.mpr (β_ne_zero D i)
  -- split the eigenvalues into unitary, outer and inner
  have hsplit : ∑ i, f i = ∑ i ∈ univ.filter (fun i => ‖D.β i‖ = 1), f i +
      (∑ i ∈ outer D, f i + ∑ i ∈ univ.filter (fun i => ‖D.β i‖ < 1), f i) := by
    have e1 : univ.filter (fun i => ¬ ‖D.β i‖ = 1 ∧ 1 < ‖D.β i‖) = outer D := by
      ext i
      simp only [outer, mem_filter, mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨h.ne', h⟩⟩
    have e2 : univ.filter (fun i => ¬ ‖D.β i‖ = 1 ∧ ¬ 1 < ‖D.β i‖) =
        univ.filter (fun i => ‖D.β i‖ < 1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨fun h => lt_of_le_of_ne (not_lt.mp h.2) h.1, fun h => ⟨h.ne, not_lt.mpr h.le⟩⟩
    rw [← sum_filter_add_sum_filter_not univ (fun i => ‖D.β i‖ = 1) f,
      ← sum_filter_add_sum_filter_not (univ.filter fun i => ¬ ‖D.β i‖ = 1)
        (fun i => 1 < ‖D.β i‖) f, filter_filter, filter_filter, e1, e2]
  -- the inner eigenvalues are the reflections of the outer ones
  have hinner : ∑ i ∈ univ.filter (fun i => ‖D.β i‖ < 1), f i =
      ∑ i ∈ outer D, f (reflectPerm D i) := by
    refine (sum_equiv (reflectPerm D) (fun i => ?_) fun i _ => rfl).symm
    simp only [outer, mem_filter, mem_univ, true_and, norm_β_reflectPerm, inv_lt_one₀ (hpos i)]
  rw [traceKernel, hsplit, hinner, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [f, pairKernel, one_mul, map_one, reflectChar_valChar (β_ne_zero D i),
    β_reflectPerm]

/-- The unitary part of the trace kernel is positive definite. -/
theorem isPosDefKernel_unitaryPart :
    IsPosDefKernel fun n => ∑ i ∈ univ.filter (fun i => ‖D.β i‖ = 1), valChar (D.β i) n :=
  isPosDefKernel_finset_sum _ fun i hi =>
    isPosDefKernel_of_unitary (isUnitaryChar_valChar (mem_filter.mp hi).2)

theorem valChar_β_ofAdd_one (i : ι) : valChar (D.β i) (Multiplicative.ofAdd 1) = D.β i :=
  valChar_ofAdd_one (β_ne_zero D i)

/-- **The index of the trace kernel is the number of distinct outer eigenvalues.** -/
theorem negIndex_traceKernel : negIndex (traceKernel D) = ((outer D).image D.β).card := by
  classical
  set P : Multiplicative ℤ → ℂ :=
    fun n => ∑ i ∈ univ.filter (fun i => ‖D.β i‖ = 1), valChar (D.β i) n
  have hk : traceKernel D = (fun n => P n + ∑ i : outer D, pairKernel (valChar (D.β i)) 1 n) ∘
      zpowersHom (Multiplicative ℤ) (Multiplicative.ofAdd 1) := by
    funext n
    rw [Function.comp_apply, zpowersHom_ofAdd_one, traceKernel_eq,
      ← (outer D).sum_coe_sort (fun i => pairKernel (valChar (D.β i)) 1 n)]
  have hout : ∀ i : outer D, 1 < ‖D.β i‖ := fun i => (mem_filter.mp i.2).2
  have hV1 : ∀ i : outer D, ‖valChar (D.β i) (Multiplicative.ofAdd 1)‖ ≠ 1 := fun i => by
    rw [valChar_β_ofAdd_one]; exact (hout i).ne'
  have hV2 : ∀ i k : outer D, valChar (D.β i) (Multiplicative.ofAdd 1) ≠
      (conj (valChar (D.β k) (Multiplicative.ofAdd 1)))⁻¹ := fun i k h => by
    rw [valChar_β_ofAdd_one, valChar_β_ofAdd_one] at h
    have h1 := hout i
    rw [h, norm_inv, Complex.norm_conj] at h1
    exact absurd h1 (not_lt.mpr (inv_le_one_of_one_le₀ (hout k).le))
  rw [hk, negIndex_zpowers_eq_card_classes (isPosDefKernel_unitaryPart D)
    (fun i : outer D => valChar (D.β i)) (fun _ => 1) _ hV1 hV2, filter_true_of_mem fun v hv => ?_]
  · congr 2
    ext v
    simp only [mem_image, mem_univ, true_and, valChar_β_ofAdd_one, Subtype.exists, exists_prop]
  · obtain ⟨j, -, rfl⟩ := mem_image.mp hv
    rw [classWeight, sum_const, nsmul_eq_mul, mul_one, Nat.cast_ne_zero, ← pos_iff_ne_zero,
      card_pos]
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩

/-- Some eigenvalue is outer iff the datum is not unitary (the reflection pairs inner and outer). -/
theorem outer_eq_empty_iff : outer D = ∅ ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h i
    have hi : ¬ 1 < ‖D.β i‖ := fun hi => by
      have : i ∈ outer D := mem_filter.mpr ⟨mem_univ _, hi⟩
      rw [h] at this; exact Finset.notMem_empty _ this
    have hσ : ¬ 1 < ‖D.β (reflectPerm D i)‖ := fun hσ => by
      have : reflectPerm D i ∈ outer D := mem_filter.mpr ⟨mem_univ _, hσ⟩
      rw [h] at this; exact Finset.notMem_empty _ this
    rw [norm_β_reflectPerm, not_lt] at hσ
    have hpos : 0 < ‖D.β i‖ := norm_pos_iff.mpr (β_ne_zero D i)
    exact le_antisymm (not_lt.mp hi) ((inv_le_one₀ hpos).mp hσ)
  · intro h
    exact filter_false_of_mem fun i _ => by rw [h i]; exact lt_irrefl 1

/-- **Weil's theorem as index zero.** For a curve datum, the trace kernel has no negative square iff
the eigenvalues are unitary iff the square-root count holds. -/
theorem negIndex_traceKernel_eq_zero_iff :
    negIndex (traceKernel D) = 0 ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [negIndex_traceKernel, Nat.cast_eq_zero, card_eq_zero, image_eq_empty, outer_eq_empty_iff]

theorem negIndex_traceKernel_eq_zero_iff_count :
    negIndex (traceKernel D) = 0 ↔
      ∃ C : ℝ, ∀ k, D.q ^ k + 1 - C * D.sqrtq ^ k ≤ D.pointCount k := by
  rw [negIndex_traceKernel_eq_zero_iff,
    ArithmeticLorentzianGeometry.unitary_iff_exists_pointCount_ge]

/-- With nonnegative counts, index zero is the trickle-down inequality on every Frobenius ladder. -/
theorem negIndex_traceKernel_eq_zero_iff_trickleDown (hN : ∀ j, 1 ≤ j → 0 ≤ D.pointCount j) :
    negIndex (traceKernel D) = 0 ↔
      ∀ K, ArithmeticLorentzianGeometry.WeightedTrickleDown
        (ArithmeticLorentzianGeometry.frobeniusWeight D K)
        (ArithmeticLorentzianGeometry.frobeniusGram D K) := by
  rw [negIndex_traceKernel_eq_zero_iff,
    ArithmeticLorentzianGeometry.forall_weightedTrickleDown_iff_unitary D hN]

/-- **The golden datum has index exactly one**: one outer eigenvalue, the golden ratio. -/
theorem negIndex_golden_traceKernel : negIndex (traceKernel goldenDatum) = 1 := by
  rw [negIndex_traceKernel]
  have hβ0 : goldenDatum.β 0 = ((Real.goldenRatio : ℝ) : ℂ) := rfl
  have hβ1 : goldenDatum.β 1 = ((Real.goldenRatio⁻¹ : ℝ) : ℂ) := rfl
  have h : outer goldenDatum = {0} := by
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, outer, mem_filter, mem_univ, true_and, mem_singleton, hβ0,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.goldenRatio_pos]
      exact iff_of_true Real.one_lt_goldenRatio rfl
    · simp only [Fin.mk_one, outer, mem_filter, mem_univ, true_and, mem_singleton, hβ1,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr Real.goldenRatio_pos)]
      exact iff_of_false (not_lt.mpr (inv_le_one_of_one_le₀ Real.one_lt_goldenRatio.le))
        (by decide)
  rw [h, image_singleton, card_singleton, Nat.cast_one]

end GaloisForLFunctions.HeckeKreinToeplitz
