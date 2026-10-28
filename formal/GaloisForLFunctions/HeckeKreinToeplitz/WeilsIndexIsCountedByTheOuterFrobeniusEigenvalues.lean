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
  positivity

end PosDef

/-! ### Characters of `ℤ` -/

theorem reflectChar_valChar {v : ℂ} (hv : v ≠ 0) : reflectChar (valChar v) = valChar (conj v)⁻¹ := by
  have hv' : (conj v)⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero _).mpr hv)
  ext n
  simp only [reflectChar_apply, valChar, MonoidHom.coe_mk, OneHom.coe_mk, if_neg hv, if_neg hv',
    toAdd_inv, zpow_neg, map_inv₀, map_zpow₀, inv_zpow']
  rw [inv_inv]

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
  have hsplit : ∑ i, f i = ∑ i ∈ univ.filter (fun i => ‖D.β i‖ = 1), f i +
      ∑ i ∈ outer D, f i + ∑ i ∈ univ.filter (fun i => ‖D.β i‖ < 1), f i := by
    rw [← sum_filter_add_sum_filter_not univ (fun i => ‖D.β i‖ = 1) f, add_assoc]
    congr 1
    rw [sum_filter_filter_eq? ]
    sorry
  sorry

end GaloisForLFunctions.HeckeKreinToeplitz
