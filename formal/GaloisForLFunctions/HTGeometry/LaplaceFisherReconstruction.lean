import GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Laplace–Fisher reconstruction from inverse response Grams

**Moore–Penrose inverse.**  A symmetric operator `T` on a finite-dimensional inner product space
restricts to an automorphism of its polar sector `(ker T)ᗮ`; `T† = ι ∘ (T|)⁻¹ ∘ proj` satisfies the
Penrose identities `T T† T = T`, `T† T T† = T†`, with `T T† = T† T` the orthogonal projection onto
`(ker T)ᗮ`.

**Gram energy.**  For `Φ : V → H` with finite-dimensional `V`, `G = Φ*Φ` and `b = Φ* u`, one has
`b ∈ ran G` and `⟨b, G† b⟩ = ‖Π u‖²`, `Π` the orthogonal projection onto `ran Φ`: `c = G† b` solves
`G c = b`, so `u - Φ c ⊥ ran Φ`, `Φ c = Π u` and `‖Φ c‖² = ⟨c, G c⟩ = ⟨b, c⟩`.

**Laplace–Fisher identity.**  For a probability law `P` on `[0, ∞)` let
`φ_n(x) = e^{-nx} - L_P(n)` in `H_P = L²_0(P)`.  If `u ∈ H_P` is orthogonal to every `φ_n`, `n ≥ 1`,
then the finite measures `u⁺ P` and `u⁻ P` have equal integer Laplace transforms, so `u = 0`
(`HalfLineLaplaceTomography`); hence the centered characters span a dense subspace of `H_P`.  For a
finite reporter set `F` with Gram matrix `G_F(m,n) = L_P(m+n) - L_P(m) L_P(n)` and responses
`b_n = ⟨u, φ_n⟩`, the energies `b_F* G_F† b_F = ‖Π_F u‖²` increase with `F` and exhaust the Fisher
mass `‖u‖²` `(CTL.15)`.  A single character gives `‖u‖² ≥ b_n² / V_n`, with equality exactly on the
line through `φ_n` `(CTL.17)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.LaplaceTomography

/-! ### The Moore–Penrose inverse of a symmetric operator -/

section MoorePenrose

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {T : V →ₗ[ℝ] V} (hT : T.IsSymmetric)

/-- The polar sector `(ker T)ᗮ`. -/
abbrev polarSector (T : V →ₗ[ℝ] V) : Submodule ℝ V := (LinearMap.ker T)ᗮ

omit [FiniteDimensional ℝ V] in
include hT in
theorem apply_mem_polarSector (x : V) : T x ∈ polarSector T := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hT z x, LinearMap.mem_ker.1 hz, inner_zero_left]

/-- `T` restricted to its polar sector. -/
def sectorMap : polarSector T →ₗ[ℝ] polarSector T :=
  (T.domRestrict _).codRestrict _ fun x => apply_mem_polarSector hT x

omit [FiniteDimensional ℝ V] in
include hT in
theorem sectorMap_injective : Function.Injective (sectorMap hT) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have h0 : T x = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hx)
  have hmem : (x : V) ∈ LinearMap.ker T ⊓ polarSector T := ⟨h0, x.2⟩
  rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact (Submodule.mem_bot ℝ).2 (Subtype.ext hmem)

/-- `T` is an automorphism of its polar sector. -/
def sectorEquiv : polarSector T ≃ₗ[ℝ] polarSector T :=
  LinearEquiv.ofBijective (sectorMap hT)
    ⟨sectorMap_injective hT, LinearMap.injective_iff_surjective.1 (sectorMap_injective hT)⟩

/-- **The Moore–Penrose inverse** `T† = ι ∘ (T|_{(ker T)ᗮ})⁻¹ ∘ proj_{(ker T)ᗮ}`. -/
def moorePenrose : V →ₗ[ℝ] V :=
  (polarSector T).subtype ∘ₗ (sectorEquiv hT).symm.toLinearMap ∘ₗ
    ((polarSector T).orthogonalProjectionOnto : V →ₗ[ℝ] polarSector T)

theorem moorePenrose_mem (y : V) : moorePenrose hT y ∈ polarSector T :=
  ((sectorEquiv hT).symm _).2

/-- `T T† = proj_{(ker T)ᗮ}`. -/
theorem apply_moorePenrose (y : V) :
    T (moorePenrose hT y) = (polarSector T).starProjection y := by
  have h := (sectorEquiv hT).apply_symm_apply ((polarSector T).orthogonalProjectionOnto y)
  have h2 := congrArg Subtype.val h
  exact h2

/-- `T† T = proj_{(ker T)ᗮ}`. -/
theorem moorePenrose_apply (x : V) :
    moorePenrose hT (T x) = (polarSector T).starProjection x := by
  have hTx : (polarSector T).orthogonalProjectionOnto (T x) = ⟨T x, apply_mem_polarSector hT x⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (⟨T x, apply_mem_polarSector hT x⟩ :
      polarSector T)
  have hP : sectorEquiv hT ((polarSector T).orthogonalProjectionOnto x) =
      ⟨T x, apply_mem_polarSector hT x⟩ := by
    apply Subtype.ext
    show T ((polarSector T).starProjection x) = T x
    have hker : x - (polarSector T).starProjection x ∈ LinearMap.ker T := by
      have := Submodule.sub_starProjection_mem_orthogonal (K := polarSector T) x
      rwa [Submodule.orthogonal_orthogonal] at this
    have := LinearMap.mem_ker.1 hker
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  show ((sectorEquiv hT).symm ((polarSector T).orthogonalProjectionOnto (T x)) : V) = _
  rw [hTx, ← hP, LinearEquiv.symm_apply_apply]
  rfl

/-- **Penrose identities.** -/
theorem moorePenrose_penrose :
    (∀ x, T (moorePenrose hT (T x)) = T x) ∧
      (∀ y, moorePenrose hT (T (moorePenrose hT y)) = moorePenrose hT y) ∧
      (∀ x y, ⟪T (moorePenrose hT x), y⟫ = ⟪x, T (moorePenrose hT y)⟫) ∧
      (∀ x y, ⟪moorePenrose hT (T x), y⟫ = ⟪x, moorePenrose hT (T y)⟫) := by
  refine ⟨fun x => ?_, fun y => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [apply_moorePenrose, Submodule.starProjection_eq_self_iff.2 (apply_mem_polarSector hT x)]
  · rw [moorePenrose_apply, Submodule.starProjection_eq_self_iff.2 (moorePenrose_mem hT y)]
  · rw [apply_moorePenrose, apply_moorePenrose, Submodule.inner_starProjection_left_eq_right]
  · rw [moorePenrose_apply, moorePenrose_apply, Submodule.inner_starProjection_left_eq_right]

end MoorePenrose

/-! ### Inverse-Gram energy -/

section Gram

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : V →L[ℝ] H)

/-- The Gram operator `G = Φ* Φ`. -/
def gramOp : V →ₗ[ℝ] V := ((ContinuousLinearMap.adjoint Φ).comp Φ : V →L[ℝ] V)

theorem inner_gramOp (x y : V) : ⟪x, gramOp Φ y⟫ = ⟪Φ x, Φ y⟫ := by
  show ⟪x, ContinuousLinearMap.adjoint Φ (Φ y)⟫ = _
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem gramOp_isSymmetric : (gramOp Φ).IsSymmetric := fun x y => by
  rw [real_inner_comm, inner_gramOp, inner_gramOp, real_inner_comm]

/-- The inverse-Gram energy `⟨b, G† b⟩`. -/
def gramEnergy (b : V) : ℝ := ⟪b, moorePenrose (gramOp_isSymmetric Φ) b⟫

/-- **Inverse-Gram energy is projection energy**: `⟨Φ* u, G† Φ* u⟩ = ‖Π_{ran Φ} u‖²`, and
`Φ* u ∈ ran G`. -/
theorem gramEnergy_adjoint (u : H) :
    ContinuousLinearMap.adjoint Φ u ∈ LinearMap.range (gramOp Φ) ∧
      gramEnergy Φ (ContinuousLinearMap.adjoint Φ u) =
        ‖(LinearMap.range (Φ : V →ₗ[ℝ] H)).starProjection u‖ ^ 2 := by
  set G := gramOp Φ
  set hG := gramOp_isSymmetric Φ
  set b := ContinuousLinearMap.adjoint Φ u
  set c := moorePenrose hG b
  have hkerΦ : ∀ z, G z = 0 → Φ z = 0 := fun z hz => by
    have h := inner_gramOp Φ z z
    rw [show G z = 0 from hz, inner_zero_right, real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg (Φ z)])
  have hb : b ∈ polarSector G := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [ContinuousLinearMap.adjoint_inner_right, hkerΦ z (LinearMap.mem_ker.1 hz), inner_zero_left]
  have hGc : G c = b := by
    rw [apply_moorePenrose, Submodule.starProjection_eq_self_iff.2 hb]
  have hproj : (LinearMap.range (Φ : V →ₗ[ℝ] H)).starProjection u = Φ c := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨c, rfl⟩ ?_
    rintro _ ⟨v, rfl⟩
    show ⟪u - Φ c, Φ v⟫ = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, map_sub,
      show ContinuousLinearMap.adjoint Φ (Φ c) = G c from rfl, hGc, sub_self, inner_zero_left]
  refine ⟨⟨c, hGc⟩, ?_⟩
  rw [hproj, ← real_inner_self_eq_norm_sq, ← inner_gramOp, hGc, gramEnergy, real_inner_comm]

end Gram

/-! ### The centered integer characters -/

theorem integrable_exp_mul {μ : Measure ℝ≥0} {f : ℝ≥0 → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) * f x) μ :=
  hf.bdd_mul (f := fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ)))) (c := 1) (by fun_prop)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
      exact mul_nonneg (Nat.cast_nonneg n) x.2)

variable (P : Measure ℝ≥0) [IsProbabilityMeasure P]

/-- `L_P(n) = ∫ e^{-nx} dP` `(CTL.11)`. -/
def laplaceP (n : ℕ) : ℝ := ∫ x, Real.exp (-(n * (x : ℝ))) ∂P

theorem laplaceP_mem_Icc (n : ℕ) : laplaceP P n ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun x => (Real.exp_pos _).le, ?_⟩
  calc laplaceP P n ≤ ∫ _x, (1 : ℝ) ∂P := integral_mono (integrable_exp_neg_mul P n)
        (integrable_const 1) fun x => by
          show Real.exp (-(n * (x : ℝ))) ≤ 1
          rw [Real.exp_le_one_iff, neg_nonpos]
          exact mul_nonneg (Nat.cast_nonneg n) x.2
    _ = 1 := by simp

theorem memLp_centered (n : ℕ) :
    MemLp (fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) - laplaceP P n) 2 P := by
  refine MemLp.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  have h1 : Real.exp (-(n * (x : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg (Nat.cast_nonneg n) x.2
  have h2 := laplaceP_mem_Icc P n
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.exp_pos (-(n * (x : ℝ))), h2.1, h2.2]

/-- The centered character `φ_n = e^{-nx} - L_P(n)` in `L²(P)` `(CTL.11)`. -/
def centeredChar (n : ℕ) : Lp ℝ 2 P := (memLp_centered P n).toLp _

theorem coeFn_centeredChar (n : ℕ) :
    (centeredChar P n : ℝ≥0 → ℝ) =ᵐ[P] fun x => Real.exp (-(n * (x : ℝ))) - laplaceP P n :=
  MemLp.coeFn_toLp _

/-- The constant `1` in `L²(P)`. -/
def constOne : Lp ℝ 2 P := (memLp_const (p := 2) (μ := P) (1 : ℝ)).toLp _

theorem coeFn_constOne : (constOne P : ℝ≥0 → ℝ) =ᵐ[P] fun _ => 1 := MemLp.coeFn_toLp _

/-- The mean-zero space `H_P = L²_0(P)`. -/
def meanZero : Submodule ℝ (Lp ℝ 2 P) := (ℝ ∙ constOne P)ᗮ

theorem integrable_Lp (u : Lp ℝ 2 P) : Integrable u P :=
  (Lp.memLp u).integrable (by norm_num)

omit [IsProbabilityMeasure P] in
theorem inner_Lp_apply (u v : Lp ℝ 2 P) : ⟪u, v⟫ = ∫ x, u x * v x ∂P := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem inner_constOne (u : Lp ℝ 2 P) : ⟪constOne P, u⟫ = ∫ x, u x ∂P := by
  rw [inner_Lp_apply]
  exact integral_congr_ae ((coeFn_constOne P).mono fun x hx => by simp only [hx, one_mul])

theorem integral_constOne : ∫ x, constOne P x ∂P = 1 := by
  rw [integral_congr_ae (coeFn_constOne P)]
  simp

theorem mem_meanZero_iff (u : Lp ℝ 2 P) : u ∈ meanZero P ↔ ∫ x, u x ∂P = 0 := by
  rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_constOne]

theorem inner_centeredChar (n : ℕ) (u : Lp ℝ 2 P) :
    ⟪centeredChar P n, u⟫ =
      ∫ x, Real.exp (-(n * (x : ℝ))) * u x ∂P - laplaceP P n * ∫ x, u x ∂P := by
  rw [inner_Lp_apply, ← integral_const_mul,
    ← integral_sub (integrable_exp_mul (integrable_Lp P u) n) ((integrable_Lp P u).const_mul _)]
  exact integral_congr_ae ((coeFn_centeredChar P n).mono fun x hx => by
    simp only [hx]
    ring)

/-- **`(CTL.13)`**: for a mean-zero score `u`, `⟨φ_n, u⟩ = ∫ e^{-nx} u dP = b_n(uP)`. -/
theorem inner_centeredChar_of_mem {u : Lp ℝ 2 P} (hu : u ∈ meanZero P) (n : ℕ) :
    ⟪centeredChar P n, u⟫ = ∫ x, Real.exp (-(n * (x : ℝ))) * u x ∂P := by
  rw [inner_centeredChar, (mem_meanZero_iff P u).1 hu, mul_zero, sub_zero]

theorem centeredChar_mem (n : ℕ) : centeredChar P n ∈ meanZero P := by
  rw [mem_meanZero_iff, integral_congr_ae (coeFn_centeredChar P n),
    integral_sub (integrable_exp_neg_mul P n) (integrable_const _)]
  simp [laplaceP]

/-- **`(CTL.14)`**: `⟨φ_m, φ_n⟩ = L_P(m + n) - L_P(m) L_P(n)`. -/
theorem inner_centeredChar_centeredChar (m n : ℕ) :
    ⟪centeredChar P m, centeredChar P n⟫ = laplaceP P (m + n) - laplaceP P m * laplaceP P n := by
  rw [inner_centeredChar, (mem_meanZero_iff P _).1 (centeredChar_mem P n), mul_zero, sub_zero]
  have hexp : ∀ x : ℝ≥0,
      Real.exp (-(m * (x : ℝ))) * (Real.exp (-(n * (x : ℝ))) - laplaceP P n) =
        Real.exp (-((m + n : ℕ) * (x : ℝ))) - laplaceP P n * Real.exp (-(m * (x : ℝ))) :=
    fun x => by
      rw [mul_sub, ← Real.exp_add]
      push_cast
      ring_nf
  calc ∫ x, Real.exp (-(m * (x : ℝ))) * centeredChar P n x ∂P
      = ∫ x, (Real.exp (-((m + n : ℕ) * (x : ℝ))) -
          laplaceP P n * Real.exp (-(m * (x : ℝ)))) ∂P :=
        integral_congr_ae ((coeFn_centeredChar P n).mono fun x hx => by
          show Real.exp (-(m * (x : ℝ))) * centeredChar P n x = _
          rw [hx]
          exact hexp x)
    _ = laplaceP P (m + n) - laplaceP P n * laplaceP P m := by
        rw [integral_sub (integrable_exp_neg_mul P _) ((integrable_exp_neg_mul P m).const_mul _),
          integral_const_mul]
        rfl
    _ = _ := by ring


/-! ### The score current `J = uP` -/

/-- The finite signed current `J = uP` of a score `u ∈ L²(P)`, with its character responses
`b_n(uP) = ∫ e^{-nx} u dP` and mass `J(Ω) = ∫ u dP`. -/
theorem charResponse_withDensityᵥ (u : Lp ℝ 2 P) (n : ℕ) :
    charResponse (P.withDensityᵥ u) n = ∫ x, Real.exp (-(n * (x : ℝ))) * u x ∂P ∧
      P.withDensityᵥ u univ = ∫ x, u x ∂P := by
  have hint := integrable_Lp P u
  have hm : Measurable (u : ℝ≥0 → ℝ) := (Lp.stronglyMeasurable u).measurable
  haveI := isFiniteMeasure_withDensity_ofReal hint.2
  haveI := isFiniteMeasure_withDensity_ofReal hint.neg.2
  refine ⟨?_, by rw [withDensityᵥ_apply hint MeasurableSet.univ, Measure.restrict_univ]⟩
  have hb : ∀ (μ : Measure ℝ≥0) [IsFiniteMeasure μ],
      VectorMeasure.Integrable μ.toSignedMeasure fun x : ℝ≥0 => Real.exp (-(n * (x : ℝ))) :=
    fun μ _ => by
      show Integrable _ (VectorMeasure.variation _)
      rw [Measure.variation_toSignedMeasure]
      exact integrable_exp_neg_mul _ n
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hint, charResponse,
    VectorMeasure.integral_sub_vectorMeasure (hb _) (hb _), VectorMeasure.integral_toSignedMeasure,
    VectorMeasure.integral_toSignedMeasure,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (-(u x)))
      hm.neg.ennreal_ofReal
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top), ← integral_sub]
  · refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal']
    rcases le_total 0 (u x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  · exact (integrable_exp_mul hint.pos_part n).congr (ae_of_all _ fun x => by
      simp only [smul_eq_mul, ENNReal.toReal_ofReal']; ring)
  · exact (integrable_exp_mul hint.neg_part n).congr (ae_of_all _ fun x => by
      simp only [smul_eq_mul, ENNReal.toReal_ofReal']; ring)

/-! ### Completeness of the centered characters -/

/-- **Uniqueness**: a mean-zero score orthogonal to every `φ_n`, `n ≥ 1`, vanishes. -/
theorem eq_zero_of_inner_centeredChar {u : Lp ℝ 2 P} (hu : u ∈ meanZero P)
    (h : ∀ n : ℕ, 1 ≤ n → ⟪centeredChar P n, u⟫ = 0) : u = 0 := by
  have hm : Measurable (u : ℝ≥0 → ℝ) := (Lp.stronglyMeasurable u).measurable
  set fp : ℝ≥0 → ℝ≥0 := fun x => Real.toNNReal (u x)
  set fn : ℝ≥0 → ℝ≥0 := fun x => Real.toNNReal (-u x)
  have hfp : Measurable fp := hm.real_toNNReal
  have hfn : Measurable fn := hm.neg.real_toNNReal
  have hint := integrable_Lp P u
  have hlep : ∀ x, (fp x : ℝ≥0∞) ≤ ‖u x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hlen : ∀ x, (fn x : ℝ≥0∞) ≤ ‖u x‖ₑ := fun x => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have hfinp : ∫⁻ x, (fp x : ℝ≥0∞) ∂P ≠ ∞ :=
    ne_top_of_le_ne_top hint.hasFiniteIntegral.ne (lintegral_mono hlep)
  have hfinn : ∫⁻ x, (fn x : ℝ≥0∞) ∂P ≠ ∞ :=
    ne_top_of_le_ne_top hint.hasFiniteIntegral.ne (lintegral_mono hlen)
  haveI := isFiniteMeasure_withDensity hfinp
  haveI := isFiniteMeasure_withDensity hfinn
  have hpos_int : Integrable (fun x => (fp x : ℝ)) P :=
    hint.pos_part.congr (ae_of_all _ fun x => by simp [fp, Real.coe_toNNReal'])
  have hneg_int : Integrable (fun x => (fn x : ℝ)) P :=
    hint.neg_part.congr (ae_of_all _ fun x => by simp [fn, Real.coe_toNNReal'])
  have hlap : ∀ n : ℕ,
      ∫ x, Real.exp (-(n * (x : ℝ))) ∂(P.withDensity fun x => (fp x : ℝ≥0∞)) -
        ∫ x, Real.exp (-(n * (x : ℝ))) ∂(P.withDensity fun x => (fn x : ℝ≥0∞)) =
        ∫ x, Real.exp (-(n * (x : ℝ))) * u x ∂P := fun n => by
    rw [integral_withDensity_eq_integral_smul hfp, integral_withDensity_eq_integral_smul hfn,
      ← integral_sub ((integrable_exp_mul hpos_int n).congr (ae_of_all _ fun x => by
        simp only [NNReal.smul_def, smul_eq_mul]; ring))
        ((integrable_exp_mul hneg_int n).congr (ae_of_all _ fun x => by
        simp only [NNReal.smul_def, smul_eq_mul]; ring))]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, fp, fn, Real.coe_toNNReal']
    rcases le_total 0 (u x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have heq : P.withDensity (fun x => (fp x : ℝ≥0∞)) = P.withDensity fun x => (fn x : ℝ≥0∞) := by
    refine measure_eq_of_laplace_eq fun n => ?_
    rw [← sub_eq_zero, hlap]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using (mem_meanZero_iff P u).1 hu
    · rw [← inner_centeredChar_of_mem P hu]
      exact h n hn
  rw [withDensity_eq_iff hfp.coe_nnreal_ennreal.aemeasurable hfn.coe_nnreal_ennreal.aemeasurable
    hfinp] at heq
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [heq] with x hx
  simp only [fp, fn, ENNReal.coe_inj, Pi.zero_apply] at hx ⊢
  have := congrArg NNReal.toReal hx
  rw [Real.coe_toNNReal', Real.coe_toNNReal'] at this
  rcases le_total 0 (u x) with h0 | h0
  · rw [max_eq_left h0, max_eq_right (by linarith)] at this; exact this
  · rw [max_eq_right h0, max_eq_left (by linarith)] at this; linarith

/-- The reporters `φ_n`, `n ≥ 1`. -/
def reporter (n : ℕ+) : Lp ℝ 2 P := centeredChar P n

/-- **Theorem 4.1, density**: the centered integer characters span a dense subspace of
`H_P = L²_0(P)`. -/
theorem closure_span_reporter :
    (Submodule.span ℝ (Set.range (reporter P))).topologicalClosure = meanZero P := by
  set S := Submodule.span ℝ (Set.range (reporter P))
  refine le_antisymm (Submodule.topologicalClosure_minimal _ ((Submodule.span_le).2 ?_)
    (Submodule.isClosed_orthogonal _)) ?_
  · rintro _ ⟨n, rfl⟩
    exact centeredChar_mem P n
  · rw [← Submodule.orthogonal_orthogonal_eq_closure]
    show (ℝ ∙ constOne P)ᗮ ≤ Sᗮᗮ
    refine Submodule.orthogonal_le ?_
    intro w hw
    set c := ∫ x, w x ∂P
    have hv : w - c • constOne P ∈ meanZero P := by
      rw [meanZero, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
        inner_smul_right, inner_constOne, inner_constOne, integral_constOne]
      ring
    have h0 := eq_zero_of_inner_centeredChar P hv fun n hn => by
      rw [inner_sub_right, inner_smul_right]
      have h1 : ⟪centeredChar P n, w⟫ = 0 := by
        have := Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩ : reporter P ⟨n, hn⟩ ∈ S) hw
        exact this
      have h2 : ⟪centeredChar P n, constOne P⟫ = 0 := by
        rw [real_inner_comm, inner_constOne, ← (mem_meanZero_iff P _).1 (centeredChar_mem P n)]
      rw [h1, h2, mul_zero, sub_zero]
    rw [sub_eq_zero] at h0
    rw [h0]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)


/-! ### Finite reporter families and the Laplace–Fisher identity `(CTL.15)` -/

/-- The character responses `b_n = ⟨φ_n, u⟩`, `n ≥ 1`. -/
def response (u : Lp ℝ 2 P) (n : ℕ+) : ℝ := ⟪reporter P n, u⟫

/-- The reporter map `Φ_F : ℝ^F → L²(P)`, `c ↦ Σ_{n ∈ F} c_n φ_n`. -/
def reporterMap (F : Finset ℕ+) : EuclideanSpace ℝ F →L[ℝ] Lp ℝ 2 P :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ∑ i : F, c i • reporter P i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

theorem reporterMap_apply (F : Finset ℕ+) (c : EuclideanSpace ℝ F) :
    reporterMap P F c = ∑ i : F, c i • reporter P i := rfl

theorem reporterMap_single (F : Finset ℕ+) (i : F) :
    reporterMap P F (EuclideanSpace.single i 1) = reporter P i := by
  rw [reporterMap_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

/-- The reporter subspace is the span of `φ_n`, `n ∈ F`. -/
theorem range_reporterMap (F : Finset ℕ+) :
    LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P) =
      Submodule.span ℝ (reporter P '' (F : Set ℕ+)) := by
  refine le_antisymm ?_ ((Submodule.span_le).2 ?_)
  · rintro _ ⟨c, rfl⟩
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩)
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨EuclideanSpace.single ⟨n, hn⟩ 1, reporterMap_single P F ⟨n, hn⟩⟩

/-- **`(CTL.14)`**: the Gram matrix `G_F(m,n) = L_P(m+n) - L_P(m) L_P(n)`. -/
theorem gram_entry (F : Finset ℕ+) (i j : F) :
    ⟪EuclideanSpace.single i (1 : ℝ), gramOp (reporterMap P F) (EuclideanSpace.single j 1)⟫ =
      laplaceP P ((i : ℕ+) + (j : ℕ+) : ℕ+) - laplaceP P (i : ℕ+) * laplaceP P (j : ℕ+) := by
  rw [inner_gramOp, reporterMap_single, reporterMap_single, reporter, reporter,
    inner_centeredChar_centeredChar, PNat.add_coe]

/-- The response vector `b_F = (b_n)_{n ∈ F}`. -/
def responseVec (b : ℕ+ → ℝ) (F : Finset ℕ+) : EuclideanSpace ℝ F :=
  WithLp.toLp 2 fun i : F => b i

theorem adjoint_reporterMap (F : Finset ℕ+) (u : Lp ℝ 2 P) :
    ContinuousLinearMap.adjoint (reporterMap P F) u = responseVec (response P u) F := by
  refine PiLp.ext fun i => ?_
  have h := ContinuousLinearMap.adjoint_inner_right (reporterMap P F) (EuclideanSpace.single i 1) u
  rw [EuclideanSpace.inner_single_left, reporterMap_single] at h
  simp only [map_one, one_mul] at h
  rw [h, responseVec, PiLp.toLp_apply]
  rfl

/-- The inverse-Gram energy `b_F* G_F† b_F` of a response sequence. -/
def responseEnergy (b : ℕ+ → ℝ) (F : Finset ℕ+) : ℝ :=
  gramEnergy (reporterMap P F) (responseVec b F)

/-- The orthogonal projection onto `span {φ_n : n ∈ F}`. -/
def reporterProjection (F : Finset ℕ+) : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)).starProjection

/-- **Finite inverse-Gram energy**: `b_F ∈ ran G_F` and `b_F* G_F† b_F = ‖Π_F u‖²`. -/
theorem responseEnergy_eq (u : Lp ℝ 2 P) (F : Finset ℕ+) :
    responseVec (response P u) F ∈ LinearMap.range (gramOp (reporterMap P F)) ∧
      responseEnergy P (response P u) F = ‖reporterProjection P F u‖ ^ 2 := by
  have h := gramEnergy_adjoint (reporterMap P F) u
  rw [adjoint_reporterMap] at h
  exact h

omit [IsProbabilityMeasure P] in
theorem norm_sq_eq_projection (K : Submodule ℝ (Lp ℝ 2 P)) [K.HasOrthogonalProjection]
    (u : Lp ℝ 2 P) : ‖u‖ ^ 2 = ‖K.starProjection u‖ ^ 2 + ‖u - K.starProjection u‖ ^ 2 := by
  rw [Submodule.norm_sq_eq_add_norm_sq_starProjection u K, Submodule.starProjection_orthogonal_val]

omit [IsProbabilityMeasure P] in
theorem norm_sub_starProjection_le_of_mem (K : Submodule ℝ (Lp ℝ 2 P))
    [K.HasOrthogonalProjection] (u : Lp ℝ 2 P) {x : Lp ℝ 2 P} (hx : x ∈ K) :
    ‖u - K.starProjection u‖ ≤ ‖u - x‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨x, hx⟩ : K)

/-- The energies are bounded by the Fisher mass, with equality exactly on the reporter span:
the sharp multivariate lower bound. -/
theorem responseEnergy_le (u : Lp ℝ 2 P) (F : Finset ℕ+) :
    responseEnergy P (response P u) F ≤ ‖u‖ ^ 2 ∧
      (responseEnergy P (response P u) F = ‖u‖ ^ 2 ↔
        u ∈ Submodule.span ℝ (reporter P '' (F : Set ℕ+))) := by
  rw [(responseEnergy_eq P u F).2, reporterProjection]
  have h := norm_sq_eq_projection P
    (LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)) u
  refine ⟨by nlinarith [sq_nonneg ‖u - (LinearMap.range
    (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)).starProjection u‖], ?_⟩
  rw [← range_reporterMap, ← Submodule.starProjection_eq_self_iff]
  constructor
  · intro he
    have h0 : ‖u - (LinearMap.range
        (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)).starProjection u‖ ^ 2 = 0 := by
      linarith
    rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at h0
    exact h0.symm
  · intro he
    rw [he] at h ⊢

/-- **Monotonicity**: the energies increase with the reporter set. -/
theorem responseEnergy_mono (u : Lp ℝ 2 P) {F F' : Finset ℕ+} (h : F ⊆ F') :
    responseEnergy P (response P u) F ≤ responseEnergy P (response P u) F' := by
  have hKK : LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P) ≤
      LinearMap.range (reporterMap P F' : EuclideanSpace ℝ F' →ₗ[ℝ] Lp ℝ 2 P) := by
    rw [range_reporterMap, range_reporterMap]
    exact Submodule.span_mono (Set.image_mono (by exact_mod_cast h))
  rw [(responseEnergy_eq P u F).2, (responseEnergy_eq P u F').2, reporterProjection,
    reporterProjection]
  set K := LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)
  set K' := LinearMap.range (reporterMap P F' : EuclideanSpace ℝ F' →ₗ[ℝ] Lp ℝ 2 P)
  have h1 := norm_sq_eq_projection P K u
  have h2 := norm_sq_eq_projection P K' u
  have h3 := norm_sub_starProjection_le_of_mem P K' u (hKK (K.starProjection_apply_mem u))
  nlinarith [norm_nonneg (u - K'.starProjection u), norm_nonneg (u - K.starProjection u)]

/-- **Theorem 4.1, `(CTL.15)`**: for every mean-zero score, the finite inverse-Gram energies of
its character response exhaust its Fisher mass. -/
theorem isLUB_responseEnergy {u : Lp ℝ 2 P} (hu : u ∈ meanZero P) :
    IsLUB (Set.range (responseEnergy P (response P u))) (‖u‖ ^ 2) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨F, rfl⟩
    exact (responseEnergy_le P u F).1
  · by_contra hlt
    push Not at hlt
    set δ := ‖u‖ ^ 2 - b
    have hδ : 0 < δ := by simp only [δ]; linarith
    have hcl : u ∈ closure (Submodule.span ℝ (Set.range (reporter P)) : Set (Lp ℝ 2 P)) := by
      rw [← Submodule.topologicalClosure_coe, closure_span_reporter]
      exact hu
    obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.1 hcl (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
    set F := c.support
    have hvF : (c.sum fun i a => a • reporter P i) ∈
        LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P) := by
      rw [range_reporterMap]
      exact Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have h1 := norm_sq_eq_projection P
      (LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)) u
    have h2 := norm_sub_starProjection_le_of_mem P
      (LinearMap.range (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)) u hvF
    have h3 : ‖u - c.sum fun i a => a • reporter P i‖ ^ 2 < δ := by
      rw [← dist_eq_norm]
      calc dist u _ ^ 2 < Real.sqrt δ ^ 2 :=
            pow_lt_pow_left₀ hdist dist_nonneg two_ne_zero
        _ = δ := Real.sq_sqrt hδ.le
    have h4 := hb ⟨F, rfl⟩
    rw [(responseEnergy_eq P u F).2, reporterProjection] at h4
    nlinarith [norm_nonneg (u - (LinearMap.range
      (reporterMap P F : EuclideanSpace ℝ F →ₗ[ℝ] Lp ℝ 2 P)).starProjection u),
      norm_nonneg (u - c.sum fun i a => a • reporter P i)]

/-- **Theorem 4.1**: the energies converge to the Fisher mass along the directed set of finite
reporter families. -/
theorem tendsto_responseEnergy {u : Lp ℝ 2 P} (hu : u ∈ meanZero P) :
    Tendsto (responseEnergy P (response P u)) atTop (𝓝 (‖u‖ ^ 2)) :=
  tendsto_atTop_isLUB (fun _ _ h => responseEnergy_mono P u h) (isLUB_responseEnergy P hu)

/-- The intrinsic response norm `‖b‖²_resp = sup_F b_F* G_F† b_F` `(CTL.16)`. -/
def responseNormSq (b : ℕ+ → ℝ) : ℝ := ⨆ F, responseEnergy P b F

/-- **`(CTL.16)`**: the complete character response is an isometry for the intrinsic response
norm. -/
theorem responseNormSq_eq {u : Lp ℝ 2 P} (hu : u ∈ meanZero P) :
    responseNormSq P (response P u) = ‖u‖ ^ 2 :=
  (isLUB_responseEnergy P hu).ciSup_eq

/-! ### One-character Fisher bound `(CTL.17)` -/

/-- **Corollary 4.2**: `V_n = L_P(2n) - L_P(n)² = ‖φ_n‖²`; if `V_n > 0` then
`‖u‖² ≥ b_n²/V_n`, with equality exactly when `u` is a multiple of `φ_n`. -/
theorem fisher_ge_one_character (n : ℕ+) (u : Lp ℝ 2 P)
    (hV : 0 < laplaceP P (2 * (n : ℕ)) - laplaceP P n ^ 2) :
    ‖reporter P n‖ ^ 2 = laplaceP P (2 * (n : ℕ)) - laplaceP P n ^ 2 ∧
      response P u n ^ 2 / (laplaceP P (2 * (n : ℕ)) - laplaceP P n ^ 2) ≤ ‖u‖ ^ 2 ∧
      (response P u n ^ 2 / (laplaceP P (2 * (n : ℕ)) - laplaceP P n ^ 2) = ‖u‖ ^ 2 ↔
        ∃ r : ℝ, u = r • reporter P n) := by
  have hV' : ‖reporter P n‖ ^ 2 = laplaceP P (2 * (n : ℕ)) - laplaceP P n ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, reporter, inner_centeredChar_centeredChar, two_mul, sq]
  have hφ : reporter P n ≠ 0 := fun h0 => by
    rw [h0, norm_zero] at hV'
    linarith
  have hcs : response P u n ^ 2 ≤ ‖reporter P n‖ ^ 2 * ‖u‖ ^ 2 := by
    have := abs_real_inner_le_norm (reporter P n) u
    rw [response, ← sq_abs, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  refine ⟨hV', ?_, ?_⟩
  · rw [div_le_iff₀ hV, ← hV', mul_comm]
    exact hcs
  · rw [div_eq_iff hV.ne', ← hV']
    constructor
    · intro he
      by_cases hu0 : u = 0
      · exact ⟨0, by rw [hu0, zero_smul]⟩
      · have habs : ‖⟪reporter P n, u⟫‖ = ‖reporter P n‖ * ‖u‖ := by
          rw [Real.norm_eq_abs]
          have h2 : |⟪reporter P n, u⟫| ^ 2 = (‖reporter P n‖ * ‖u‖) ^ 2 := by
            rw [sq_abs, mul_pow, mul_comm (‖reporter P n‖ ^ 2)]
            exact he
          exact (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h2
        obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hφ hu0).1 habs
        exact ⟨r, hr⟩
    · rintro ⟨r, rfl⟩
      rw [response, inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
      ring_nf
      rw [sq_abs]
      ring

/-! ### Conditional selection `(CTL.29)`–`(CTL.31)` -/

/-- **`(CTL.31)`**: a mean-zero score current all of whose integer responses vanish is zero and
carries zero Fisher mass. -/
theorem score_eq_zero_of_responses {u : Lp ℝ 2 P} (hu : u ∈ meanZero P)
    (h : ∀ n : ℕ, 1 ≤ n → ∫ x, Real.exp (-(n * (x : ℝ))) * u x ∂P = 0) :
    u = 0 ∧ ‖u‖ ^ 2 = 0 := by
  have hu0 := eq_zero_of_inner_centeredChar P hu fun n hn => by
    rw [inner_centeredChar_of_mem P hu]
    exact h n hn
  exact ⟨hu0, by rw [hu0, norm_zero]; ring⟩

end GaloisForLFunctions.HTGeometry.LaplaceTomography
