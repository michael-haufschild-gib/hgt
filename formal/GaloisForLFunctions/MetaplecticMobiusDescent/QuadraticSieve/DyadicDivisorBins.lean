/-
Dyadic divisor bins adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.DivisorBlocksAndKernelTransfer

/-!
# Dyadic divisor bins

Dyadic column lengths and divisor bins `divisorDyadicBin` count the divisor families in the
block estimates; norm-ball counting removes their cardinalities. Unique coprime splitting of
divisors (`QuadraticDivisorSplit`).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory QuadraticKernelTransfer DivisorBlockCauchy
open scoped SchwartzMap

section
variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

/-- Divisor block cost before estimating the two finite divisor families. -/
def divisorBlockCost (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  (S.card : ℝ) * T.card * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
    (divisorConstant ε hε * N ^ ε) ^ 4 * (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2)

def originalTerm (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p) : ℂ :=
  if (left j).val ⊔ (right k).val = ⊤ then
    star (canonicalQuadraticRow (left j) (primaryIdealGenerator (rows i).val) * (if D ∣ (left j).val then a j else 0)) *
      (canonicalQuadraticRow (right k) (primaryIdealGenerator (rows i).val) * (if E ∣ (right k).val then b k else 0)) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_phase (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (D E : Ideal O) (i : m) (j : n) (k : p)
    (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    originalTerm rows left right (fun j => a j * star (kernelLogPhase t (y j)))
      (fun k => b k * kernelLogPhase t (z k)) D E i j k =
    originalTerm rows left right a b D E i j k * kernelLogPhase t (y j + z k) := by
  unfold originalTerm
  rw [kernelLogPhase_add]
  by_cases hc : (left j).val ⊔ (right k).val = ⊤ <;>
    by_cases hD : D ∣ (left j).val <;> by_cases hE : E ∣ (right k).val <;>
      simp only [hc, hD, hE, ↓reduceIte, mul_zero, zero_mul, star_zero, star_mul, star_star] ; ring

theorem canonical_original_divisor_block_phase_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) (hN : 0 ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ))
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (y : n → ℝ) (z : p → ℝ) (t : ℝ) :
    (∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * kernelLogPhase t (y j + z k)‖) ≤
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ M N a b) := by
  have hb := original_divisor_block_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright
    (fun j => a j * star (kernelLogPhase t (y j))) (fun k => b k * kernelLogPhase t (z k))
  simp only [norm_mul, norm_star, kernelLogPhase_norm, mul_one] at hb
  change (∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k,
    originalTerm rows left right (fun j => a j * star (kernelLogPhase t (y j)))
      (fun k => b k * kernelLogPhase t (z k)) D E i j k‖) ^ 2 ≤
    divisorBlockCost ε hε S T D₁ D₂ M N a b at hb
  simp only [originalTerm_phase] at hb
  have hcost : 0 ≤ divisorBlockCost ε hε S T D₁ D₂ M N a b := (sq_nonneg _).trans hb
  have hs := Real.sq_sqrt hcost
  have hp := Real.sqrt_nonneg (divisorBlockCost ε hε S T D₁ D₂ M N a b)
  have hsum : 0 ≤ ∑ D ∈ S, ∑ E ∈ T, ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * kernelLogPhase t (y j + z k)‖ := by positivity
  nlinarith only [hb, hs, hp, hsum]
end

theorem canonical_original_radial_divisor_block_bound
    (W : 𝓢(ℝ, ℂ)) (L₁ L₂ L₃ : ℝ) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ M N : ℝ) (_hD₁ : 0 < D₁) (_hD₂ : 0 < D₂) (_hN : 0 ≤ N)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ))
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ))
        (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
        (_hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
        (_hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (x : S → T → m → ℝ) (y : n → ℝ) (z : p → ℝ),
        (∀ D E i, |x D E i| ≤ L₁) → (∀ j, |y j| ≤ L₂) → (∀ k, |z k| ≤ L₃) →
        (1 + R) ^ A * (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
          originalTerm rows left right a b D.val E.val i j k *
            paperRadialFourier W (R * Real.exp (x D E i + (y j + z k)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ M N a b) := by
  obtain ⟨C, hC, hker⟩ := radial_matrix_kernel_transfer W L₁ (L₂ + L₃) hL₁ (add_nonneg hL₂ hL₃) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n p _ _ _ _ _ _ ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
    rows left right hr hl hri hrows hleft hright a b x y z hx hy hz
  let c : (S × T × m) → (n × p) → ℂ := fun i j =>
    originalTerm rows left right a b i.1.val i.2.1.val i.2.2 j.1 j.2
  have hp (t : ℝ) : (∑ i : S × T × m, ‖∑ j : n × p, c i j * kernelLogPhase t (y j.1 + z j.2)‖) ≤
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ M N a b) := by
    have hb := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ M N hD₁ hD₂ hN hS hT
      rows left right hr hl hri hrows hleft hright a b y z t
    simp only [c, Fintype.sum_prod_type]
    let v : Ideal O → Ideal O → ℝ := fun D E => ∑ i,
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * kernelLogPhase t (y j + z k)‖
    change (∑ D : S, ∑ E : T, v D.val E.val) ≤ _
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, v D E.val)]
    have he (D : Ideal O) := Finset.sum_coe_sort T (v D)
    simp_rw [he]
    exact hb
  have hb := hker R hR c (fun i => x i.1 i.2.1 i.2.2) (fun j => y j.1 + z j.2)
    (Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ M N a b)) (Real.sqrt_nonneg _)
    (fun i => hx i.1 i.2.1 i.2.2)
    (fun j => (abs_add_le _ _).trans (add_le_add (hy j.1) (hz j.2))) hp
  simpa only [c, Fintype.sum_prod_type] using hb

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

def middleRatio (B b D₁ d D₂ e : ℝ) : ℝ := Real.sqrt (B / b) * (D₁ / d) * (D₂ / e)

theorem middleRatio_bounds (B b D₁ d D₂ e : ℝ)
    (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    1 / 4 ≤ middleRatio B b D₁ d D₂ e ∧ middleRatio B b D₁ d D₂ e ≤ 2 := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hu1 : 1 ≤ Real.sqrt (B / b) := by
    have hq : 1 ≤ B / b := (le_div_iff₀ hb0).mpr (by simpa using hb.2)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  have hu2 : Real.sqrt (B / b) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    apply (div_le_iff₀ hb0).mpr
    nlinarith
  have hv : (1 / 2 : ℝ) ≤ D₁ / d ∧ D₁ / d ≤ 1 :=
    ⟨(le_div_iff₀ hd0).mpr (by linarith), (div_le_one hd0).mpr hd.1⟩
  have hw : (1 / 2 : ℝ) ≤ D₂ / e ∧ D₂ / e ≤ 1 :=
    ⟨(le_div_iff₀ he0).mpr (by linarith), (div_le_one he0).mpr he.1⟩
  have hv0 : 0 ≤ D₁ / d := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hv.1
  have hw0 : 0 ≤ D₂ / e := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hw.1
  have hvw1 : (1 / 4 : ℝ) ≤ (D₁ / d) * (D₂ / e) := by
    nlinarith [mul_le_mul hv.1 hw.1 (by norm_num : (0 : ℝ) ≤ 1 / 2) hv0]
  have hvw2 : (D₁ / d) * (D₂ / e) ≤ 1 := by
    nlinarith [mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 1)]
  unfold middleRatio
  constructor
  · nlinarith [mul_le_mul hu1 hvw1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.sqrt_nonneg (B / b))]
  · nlinarith [mul_le_mul hu2 hvw2 (mul_nonneg hv0 hw0) (by norm_num : (0 : ℝ) ≤ 2)]

theorem middleRatio_log_bound (r : ℝ) (hr : (1 / 4 : ℝ) ≤ r ∧ r ≤ 2) : |Real.log r| ≤ 4 := by
  have hr0 : 0 < r := by linarith
  have hi : r⁻¹ ≤ 4 := by
    have h : (1 : ℝ) / r ≤ 4 := (div_le_iff₀ hr0).mpr (by linarith)
    simpa only [one_div] using h
  have h₁ := Real.log_le_sub_one_of_pos hr0
  have h₂ := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem middleRatio_argument (M B b D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (Real.sqrt (M / B) * q / (D₁ * D₂)) * Real.exp (Real.log (middleRatio B b D₁ d D₂ e)) =
      Real.sqrt (M / b) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_log hr]
  have hs : Real.sqrt (M / B) * Real.sqrt (B / b) = Real.sqrt (M / b) := by
    rw [← Real.sqrt_mul (div_nonneg hM.le hB.le)]
    congr 1
    field_simp
  unfold middleRatio
  calc
    _ = (Real.sqrt (M / B) * Real.sqrt (B / b)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [hs]

theorem actual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N) (_hM : 0 < M)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
        (_hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
        (_hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + Real.sqrt (M / B) * ‖ringComplex h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k *
              paperRadialFourier W
                (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 0 0 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  let R := Real.sqrt (M / B) * ‖ringComplex h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (Real.sqrt_pos.mpr (div_pos hM hB0))
    (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i).val) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i) hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁0 hD₂0 (zero_le_one.trans hN)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1) rows left right hr hl hri
    (fun i => (hrows i).2) hleft hright a b x (fun _ => 0) (fun _ => 0) hx
    (fun _ => by simp) (fun _ => by simp)
  have harg (D : S) (E : T) (i : m) : R * Real.exp (x D E i + (0 + 0)) =
      Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) := by
    simp only [add_zero]
    exact middleRatio_argument _ _ _ _ _ _ _ _ hM hB0 (hrows i) hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

theorem column_sqrt_ratio_bounds (N n : ℝ) (hN : 0 < N) (hn : N / 2 ≤ n ∧ n ≤ N) :
    1 / 4 ≤ Real.sqrt (n / N) ∧ Real.sqrt (n / N) ≤ 2 := by
  have hq0 : 0 ≤ n / N := div_nonneg (by linarith) hN.le
  have hq1 : (1 / 2 : ℝ) ≤ n / N := (le_div_iff₀ hN).mpr (by linarith)
  have hq2 : n / N ≤ 1 := (div_le_one hN).mpr hn.2
  have hs := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg (n / N)
  constructor <;> nlinarith

theorem dual_middle_sqrt_identity (M B b N i j F : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : 0 < b) (hN : 0 < N)
    (hi : 0 < i) (hj : 0 < j) (hF : 0 < F) :
    N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N) =
      Real.sqrt (F * i * j / (M * b)) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity),
    Real.sq_sqrt (show 0 ≤ B / b by positivity), Real.sq_sqrt (show 0 ≤ i / N by positivity),
    Real.sq_sqrt (show 0 ≤ j / N by positivity), Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity)]
  field_simp

theorem dual_middle_argument (M B b N i j F D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) (hF : 0 < F)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (N * Real.sqrt (F / (M * B)) * q / (D₁ * D₂)) *
      Real.exp (Real.log (middleRatio B b D₁ d D₂ e) +
        (Real.log (Real.sqrt (i / N)) + Real.log (Real.sqrt (j / N)))) =
      Real.sqrt (F * i * j / (M * b)) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr,
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hi0 hN)),
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hj0 hN))]
  unfold middleRatio
  calc
    _ = (N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [dual_middle_sqrt_identity M B b N i j F hM hB hb0 hN hi0 hj0 hF]

theorem actual_dual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M F : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N)
        (_hM : 0 < M) (_hF : 0 < F)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
        (_hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
        (_hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + N * Real.sqrt (F / (M * B)) * ‖ringComplex h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
              (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
                (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 4 4 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by linarith
  let R := N * Real.sqrt (F / (M * B)) * ‖ringComplex h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (mul_pos hN0 (Real.sqrt_pos.mpr (by positivity)))
    (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i).val) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  let y : n → ℝ := fun j => Real.log (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) / N))
  let z : p → ℝ := fun k => Real.log (Real.sqrt ((Ideal.absNorm (right k).val : ℝ) / N))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i) hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have hy (j : n) : |y j| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hleft j))
  have hz (k : p) : |z k| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hright k))
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁0 hD₂0 (zero_le_one.trans hN)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1) rows left right hr hl hri
    (fun i => (hrows i).2) (fun j => (hleft j).2)
    (fun k => (hright k).2) a b x y z hx hy hz
  have harg (D : S) (E : T) (i : m) (j : n) (k : p) : R * Real.exp (x D E i + (y j + z k)) =
      Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
        (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) :=
    dual_middle_argument _ _ _ _ _ _ _ _ _ _ _ _ hM hB0 (hrows i) hN0 (hleft j) (hright k) hF
      hD₁0 (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he


theorem principal_middle_prefactor_bound (M B b D₁ d D₂ e : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d) (hD₂ : 0 < D₂) (he : D₂ ≤ e) :
    Real.sqrt (M / b) / (d * e) ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd
  have he0 : 0 < e := hD₂.trans_le he
  have hq : M / b ≤ 4 * (M / B) := by
    calc
      _ ≤ (4 * M) / B := (div_le_div_iff₀ hb0 hB).mpr (by nlinarith [mul_nonneg hM.le (show 0 ≤ 4 * b - B by linarith)])
      _ = _ := by ring
  have hs : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
    have hh := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4] at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt (M / B)) / (d * e) := div_le_div_of_nonneg_right hs (mul_pos hd0 he0).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hD₁ hD₂)
      (mul_le_mul hd he hD₂.le hd0.le)

theorem principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf D E i)
  exact principal_middle_prefactor_bound M B _ D₁ _ D₂ _ hM hB (hrows i) hD₁
    (hS D.val D.property) hD₂ (hT E.val E.property)


theorem dual_principal_prefactor_identity (M F b i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    (M / (Real.sqrt (i * j) * F)) * Real.sqrt (F * i * j / (M * b)) =
      Real.sqrt ((M / F) / b) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ i * j by positivity),
    Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity),
    Real.sq_sqrt (show 0 ≤ (M / F) / b by positivity)]
  field_simp

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

def originalMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose

def dualMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

theorem actual_original_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt (M / B) / (D₁ * D₂)) * originalMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M
    hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ originalMiddleConstant W * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T (fun i => (rows i).val) _ (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) by positivity)

theorem actual_dual_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
          (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt ((M / F) / B) / (D₁ * D₂)) * dualMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M F
    hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ dualMiddleConstant W * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T (fun i => (rows i).val) _ (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF)
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) by positivity)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory
open scoped SchwartzMap

def nonzeroLatticeEnvelopeConstant : ℝ :=
  4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass

theorem nonzeroLatticeEnvelopeConstant_nonneg :
    0 ≤ nonzeroLatticeEnvelopeConstant := by
  have := eisensteinCauchyMass_nonneg
  unfold nonzeroLatticeEnvelopeConstant
  positivity

theorem scaled_cauchy_nonzero_mass (t : ℝ) (ht : 0 < t) :
    t * (∑' h : {h : O // h ≠ 0},
      ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) ≤
        nonzeroLatticeEnvelopeConstant := by
  let F : ℝ → ℂ := fun x => (((1 + x) ^ 2)⁻¹ : ℝ)
  have hF (x : ℝ) (hx : 0 ≤ x) : (1 + x) ^ 2 * ‖F x‖ ≤ 1 := by
    dsimp only [F]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_inv_cancel₀ (by positivity : (1 + x) ^ 2 ≠ 0)]
  have hh := lattice_profile_nonzero_scaled_bound F 1 (by norm_num) hF t ht
  change t * (∑' h : {h : O // h ≠ 0}, ‖F (t * ‖ringComplex h.val‖ ^ 2)‖) ≤
    nonzeroLatticeEnvelopeConstant * 1 at hh
  simpa only [F, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ ((1 + t * ‖ringComplex _‖ ^ 2) ^ 2)⁻¹ by positivity),
    mul_one] using hh

theorem nonzero_lattice_envelope_sum
    (t C : ℝ) (ht : 0 < t) (hC : 0 ≤ C)
    (f : {h : O // h ≠ 0} → ℝ) (hf : ∀ h, 0 ≤ f h)
    (hbound : ∀ h, (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 * f h ≤ C) :
    Summable f ∧ t * (∑' h, f h) ≤ nonzeroLatticeEnvelopeConstant * C := by
  have hp (h : {h : O // h ≠ 0}) :
      f h ≤ C * ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hbound h
  have hs := (scaled_eisenstein_cauchy_summable t ht).subtype (fun h : O => h ≠ 0)
  have hfs : Summable f := Summable.of_nonneg_of_le hf hp (hs.mul_left C)
  refine ⟨hfs, ?_⟩
  have hh := hfs.tsum_le_tsum hp (hs.mul_left C)
  rw [tsum_mul_left] at hh
  calc
    _ ≤ t * (C * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hh ht.le
    _ = C * (t * ∑' h : {h : O // h ≠ 0},
        ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2)⁻¹) := by ring
    _ ≤ C * nonzeroLatticeEnvelopeConstant :=
      mul_le_mul_of_nonneg_left (scaled_cauchy_nonzero_mass t ht) hC
    _ = _ := mul_comm _ _


end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve

section
open Eisenstein MeasureTheory

def originalMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose

def dualMiddleDecayConstant (W : 𝓢(ℝ, ℂ)) : ℝ :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose

theorem originalMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ originalMiddleDecayConstant W :=
  (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem dualMiddleDecayConstant_nonneg (W : 𝓢(ℝ, ℂ)) :
    0 ≤ dualMiddleDecayConstant W :=
  (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.1

theorem divisorBlockCost_mono_coefficients
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O)) (D₁ D₂ B N : ℝ) (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (a a₀ : n → ℂ) (b b₀ : p → ℂ)
    (ha : ∀ j, ‖a j‖ ≤ ‖a₀ j‖) (hb : ∀ k, ‖b k‖ ≤ ‖b₀ k‖) :
    divisorBlockCost ε hε S T D₁ D₂ B N a b ≤ divisorBlockCost ε hε S T D₁ D₂ B N a₀ b₀ := by
  have hA := sieveNorm_nonneg B (N / D₁)
  have hB := sieveNorm_nonneg B (N / D₂)
  unfold divisorBlockCost
  gcongr
  · exact ha _
  · exact hb _

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

def dualMiddleAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
        (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (h : O) :
    0 ≤ originalMiddleAt W S T rows left right a b M h := by
  unfold originalMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (h : O) :
    0 ≤ dualMiddleAt W S T rows left right a b M F h := by
  unfold dualMiddleAt
  positivity

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows ha hb

theorem actual_original_middle_all_frequencies
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
        2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W *
          Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a₀ b₀) := by
  let t := Real.sqrt (M / B) / (D₁ * D₂)
  have ht : 0 < t := by dsimp only [t]; positivity
  let C := originalMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (originalMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 *
        originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ 2 * t * C := by
    have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M
      hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ originalMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε S T D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (originalMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T (fun i => (rows i).val)
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h.val‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : Real.sqrt (M / B) * ‖ringComplex h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖ringComplex h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt (M / B) / (D₁ * D₂) = 2 * t := by dsimp only [t]; ring
    rw [hpre] at hp
    change originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 * (2 * t * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = 2 * t * ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ 2 * t * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t (2 * t * C) ht (by positivity)
    _ (fun h => originalMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * (2 * t * C) := hv
    _ = _ := by dsimp only [C]; ring

end

theorem dual_middle_scale_identity (M F B N : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N) :
    Real.sqrt ((M / F) / B) = (M / (F * N)) * (N * Real.sqrt (F / (M * B))) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ (M / F) / B by positivity),
    Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem actual_dual_middle_all_frequencies
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
        (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N)) *
          Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a₀ b₀) := by
  let t := (N * Real.sqrt (F / (M * B))) / (D₁ * D₂)
  let r := M / (F * N)
  have ht : 0 < t := by dsimp only [t]; positivity
  have hr0 : 0 < r := by dsimp only [r]; positivity
  let C := dualMiddleDecayConstant W * Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a₀ b₀)
  have hC : 0 ≤ C := mul_nonneg (dualMiddleDecayConstant_nonneg W) (Real.sqrt_nonneg _)
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 *
        dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ (2 * t * r) * C := by
    have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 2).choose_spec.2 ε hε S T D₁ D₂ B N M F
      hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright (a h.val) (b h.val) h.val h.property
    change _ ≤ dualMiddleDecayConstant W *
      Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N (a h.val) (b h.val)) at hk
    have hcost := divisorBlockCost_mono_coefficients ε hε S T D₁ D₂ B N
      (by linarith) (by linarith) (a h.val) a₀ (b h.val) b₀ (ha h.val) (hb h.val)
    have hk' := hk.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcost)
      (dualMiddleDecayConstant_nonneg W))
    have hp := principal_middle_prefactor_sum S T (fun i => (rows i).val)
      (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right (a h.val) (b h.val) D.val E.val i j k *
        paperRadialFourier W (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
          (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h.val‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖)
      (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF) (by linarith) (by linarith) (by linarith)
      (fun i => (hrows i).1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    have harg : N * Real.sqrt (F / (M * B)) * ‖ringComplex h.val‖ ^ 2 / (D₁ * D₂) =
        t * ‖ringComplex h.val‖ ^ 2 := by dsimp only [t]; ring
    rw [harg] at hk'
    have hpre : 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) = 2 * t * r := by
      rw [dual_middle_scale_identity M F B N hM hF (by linarith) (by linarith)]
      dsimp only [t, r]
      ring
    rw [hpre] at hp
    change dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val ≤ _ at hp
    calc
      _ ≤ (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 * ((2 * t * r) * _) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = (2 * t * r) * ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 * _) := by ring
      _ ≤ (2 * t * r) * C := mul_le_mul_of_nonneg_left hk' (by positivity)
  obtain ⟨hs, hv⟩ := nonzero_lattice_envelope_sum t ((2 * t * r) * C) ht (by positivity)
    _ (fun h => dualMiddleAt_nonneg W S T rows left right (a h.val) (b h.val) M F h.val) hpoint
  refine ⟨hs, (mul_le_mul_iff_right₀ ht).mp ?_⟩
  calc
    _ ≤ nonzeroLatticeEnvelopeConstant * ((2 * t * r) * C) := hv
    _ = _ := by dsimp only [C, r]; ring

end

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein DivisorBlockCauchy
open scoped SchwartzMap

theorem HasSieveExponent.reverse {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      sieveNorm M N ≤ C * (M * N) ^ ε * (N + M ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h ε hε
  refine ⟨262144 * C, by positivity, ?_⟩
  intro M N hM hN
  calc
    _ ≤ 262144 * sieveNorm N M := sieveNorm_reverse M N
    _ ≤ 262144 * (C * (N * M) ^ ε * (N + M ^ α)) :=
      mul_le_mul_of_nonneg_left (hb N M hN hM) (by norm_num)
    _ = _ := by rw [mul_comm N M]; ring

theorem sqrt_divisor_sieve_pair_le (M N D₁ D₂ Q C : ℝ)
    (hN : 0 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hQ : 0 ≤ Q) (hC : 0 ≤ C)
    (h₁ : sieveNorm M (N / D₁) ≤ C * (N / D₁ + Q))
    (h₂ : sieveNorm M (N / D₂) ≤ C * (N / D₂ + Q)) :
    Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
      C * (N + Q * (D₁ * D₂)) := by
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hD₁le : D₁ ≤ D₁ * D₂ := by nlinarith
  have hD₂le : D₂ ≤ D₁ * D₂ := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ D₁ * D₂ * (C * (N / D₁ + Q)) * (C * (N / D₂ + Q)) := by
      gcongr
      exact sieveNorm_nonneg _ _
    _ = C ^ 2 * ((N + Q * D₁) * (N + Q * D₂)) := by field_simp
    _ ≤ C ^ 2 * ((N + Q * (D₁ * D₂)) * (N + Q * (D₁ * D₂))) := by gcongr
    _ = _ := by ring

theorem HasSieveExponent.divisor_pair {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N D₁ D₂ : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ D₁ → 1 ≤ D₂ → D₁ ≤ N → D₂ ≤ N →
      Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) ≤
        C * (M * N) ^ ε * (N + M ^ α * (D₁ * D₂)) := by
  intro ε hε
  obtain ⟨C, hC, hb⟩ := h.reverse ε hε
  refine ⟨C, hC, ?_⟩
  intro M N D₁ D₂ hM hN hD₁ hD₂ hD₁N hD₂N
  have hbound (D : ℝ) (hD : 1 ≤ D) (hDN : D ≤ N) :
      sieveNorm M (N / D) ≤ (C * (M * N) ^ ε) * (N / D + M ^ α) := by
    have hD0 : 0 < D := by linarith
    have hND : 1 ≤ N / D := (le_div_iff₀ hD0).mpr (by simpa using hDN)
    apply (hb M (N / D) hM hND).trans
    have hprod : M * (N / D) ≤ M * N := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_self (by linarith) hD
    gcongr
  exact sqrt_divisor_sieve_pair_le M N D₁ D₂ (M ^ α) (C * (M * N) ^ ε)
    (by linarith) hD₁ hD₂ (Real.rpow_nonneg (by linarith) _) (by positivity)
    (hbound D₁ hD₁ hD₁N) (hbound D₂ hD₂ hD₂N)

section
variable {n p : Type*} [Fintype n] [Fintype p]

/-- The two column energies and divisor multiplicities, after counting dyadic divisor families. -/
def divisorEnergyFactor (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  (2 * diagonalControl sieveCutoff) * (divisorConstant ε hε * N ^ ε) ^ 2 *
    Real.sqrt (∑ j, ‖a j‖ ^ 2) * Real.sqrt (∑ k, ‖b k‖ ^ 2)

lemma divisorEnergyFactor_nonneg (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) (b : p → ℂ) :
    0 ≤ divisorEnergyFactor ε hε N a b := by
  have hd := diagonalControl_nonneg sieveCutoff
  unfold divisorEnergyFactor
  positivity

/-- Norm-ball counting removes the cardinalities of the two divisor families. -/
theorem divisorBlockCost_sqrt_bound (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ M N : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hS : ∀ D ∈ S, (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
    (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ M N a b) ≤
      divisorEnergyFactor ε hε N a b *
        Real.sqrt (D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂)) := by
  have hA := sieveNorm_nonneg M (N / D₁)
  have hB := sieveNorm_nonneg M (N / D₂)
  have hd := diagonalControl_nonneg sieveCutoff
  have ha : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb : 0 ≤ ∑ k, ‖b k‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : 0 ≤ D₁ * D₂ * sieveNorm M (N / D₁) * sieveNorm M (N / D₂) := by positivity
  have hcs := finite_ideal_card_bound S (2 * D₁) (by linarith) hS
  have hct := finite_ideal_card_bound T (2 * D₂) (by linarith) hT
  have hc : (S.card : ℝ) * T.card ≤ (2 * diagonalControl sieveCutoff) ^ 2 * D₁ * D₂ := by
    calc
      _ ≤ (diagonalControl sieveCutoff * (2 * D₁)) *
          (diagonalControl sieveCutoff * (2 * D₂)) :=
        mul_le_mul hcs hct (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (divisorEnergyFactor_nonneg ε hε N a b) (Real.sqrt_nonneg _), ?_⟩
  simp only [divisorEnergyFactor, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp]
  calc
    _ ≤ ((2 * diagonalControl sieveCutoff) ^ 2 * D₁ * D₂) *
        sieveNorm M (N / D₁) * sieveNorm M (N / D₂) *
        (divisorConstant ε hε * N ^ ε) ^ 4 * (∑ j, ‖a j‖ ^ 2) * (∑ k, ‖b k‖ ^ 2) := by
      unfold divisorBlockCost
      gcongr
    _ = _ := by ring

end

def divisorExponentConstant {α : ℝ} (h : HasSieveExponent α) (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  (h.divisor_pair δ hδ).choose

lemma divisorExponentConstant_pos {α : ℝ} (h : HasSieveExponent α) (δ : ℝ) (hδ : 0 < δ) :
    0 < divisorExponentConstant h δ hδ := (h.divisor_pair δ hδ).choose_spec.1

theorem divisor_cost_with_constant {α : ℝ} (h : HasSieveExponent α) (δ : ℝ) (hδ : 0 < δ)
    {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O)) (B N D₁ D₂ : ℝ)
    (hB : 1 ≤ B) (hN : 1 ≤ N) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂)
    (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
    (hT : ∀ E ∈ T, (Ideal.absNorm E : ℝ) ≤ 2 * D₂) (a : n → ℂ) (b : p → ℂ) :
    Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) ≤
      divisorEnergyFactor ε hε N a b *
        (divisorExponentConstant h δ hδ * (B * N) ^ δ * (N + B ^ α * (D₁ * D₂))) := by
  apply (divisorBlockCost_sqrt_bound ε hε S T D₁ D₂ B N hD₁ hD₂ hS hT a b).trans
  exact mul_le_mul_of_nonneg_left
    ((h.divisor_pair δ hδ).choose_spec.2 B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N)
    (divisorEnergyFactor_nonneg ε hε N a b)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

theorem sqrt_div_mul_rpow (M B α : ℝ) (hM : 0 ≤ M) (hB : 0 < B) :
    Real.sqrt (M / B) * B ^ α = Real.sqrt M * B ^ (α - 1 / 2) := by
  rw [Real.rpow_sub hB, ← Real.sqrt_eq_rpow, Real.sqrt_div hM]
  ring

theorem original_middle_scale_shape (M B N D T α : ℝ)
    (hM : 0 ≤ M) (hB : 0 < B) (hD : D ≤ T * Real.sqrt (M / B)) :
    N + B ^ α * D ≤ N + T * Real.sqrt M * B ^ (α - 1 / 2) := by
  calc
    _ ≤ N + B ^ α * (T * Real.sqrt (M / B)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hB.le α))
    _ = _ := by rw [mul_left_comm (B ^ α) T, mul_comm (B ^ α), sqrt_div_mul_rpow M B α hM hB]; ring

theorem dual_middle_scale_shape (M F B N D T α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hN : 0 < N)
    (hD : D ≤ T * (N * Real.sqrt (F / (M * B)))) :
    (M / (F * N)) * (N + B ^ α * D) ≤
      M / F + T * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hratio : 0 ≤ M / (F * N) := by positivity
  calc
    _ ≤ (M / (F * N)) * (N + B ^ α * (T * (N * Real.sqrt (F / (M * B))))) := by gcongr
    _ = M / F + T * (Real.sqrt ((M / F) / B) * B ^ α) := by
      rw [dual_middle_scale_identity M F B N hM hF hB hN]
      field_simp

    _ = _ := by rw [sqrt_div_mul_rpow (M / F) B α (by positivity) hB]; ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_block
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * Real.sqrt (M / B)) :
    (∑' h : {h : O // h ≠ 0},
      originalMiddleAt W S T rows left right (a h.val) (b h.val) M h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + U * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε S T B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N
    (fun D hD => (hS D hD).2) (fun E hE => (hT E hE).2) a₀ b₀
  have hs := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (originalMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc hk)
    _ = ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          (N + B ^ α * (D₁ * D₂)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (original_middle_scale_shape M B N (D₁ * D₂) U α hM.le (by linarith) hcut) (by positivity)

theorem HasSieveExponent.dual_middle_block
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hcut : D₁ * D₂ ≤ U * (N * Real.sqrt (F / (M * B)))) :
    (∑' h : {h : O // h ≠ 0},
      dualMiddleAt W S T rows left right (a h.val) (b h.val) M F h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + U * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε S T B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N
    (fun D hD => (hS D hD).2) (fun E hE => (hT E hE).2) a₀ b₀
  have hs := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).2
  have hk : 0 ≤ 2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W :=
    mul_nonneg (mul_nonneg (by norm_num) nonzeroLatticeEnvelopeConstant_nonneg) (dualMiddleDecayConstant_nonneg W)
  have hf := divisorEnergyFactor_nonneg ε hε N a₀ b₀
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) * (M / (F * N))) *
        (divisorEnergyFactor ε hε N a₀ b₀ *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
          ((M / (F * N)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁ * D₂) U α hM hF (by linarith) (by linarith) hcut) (by positivity)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

theorem sqrt_scale_shell_upper (M B b : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hb : B / 2 ≤ b) : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
  simpa only [one_mul, div_one] using principal_middle_prefactor_bound
    M B b 1 1 1 1 hM hB hb (by norm_num) le_rfl (by norm_num) le_rfl

theorem original_middle_rectangle_upper (M B b D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * Real.sqrt (M / b)) :
    D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B) := by
  calc
    _ ≤ d * e := mul_le_mul hd he hD₂ (hD₁.trans hd)
    _ ≤ U * Real.sqrt (M / b) := hcut
    _ ≤ U * (2 * Real.sqrt (M / B)) :=
      mul_le_mul_of_nonneg_left (sqrt_scale_shell_upper M B b hM hB hb) hU
    _ = _ := by ring

theorem dual_middle_rectangle_upper (M F B b N D₁ D₂ d e U : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : B / 2 ≤ b) (hN : 0 ≤ N) (hU : 0 ≤ U)
    (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂) (hd : D₁ ≤ d) (he : D₂ ≤ e)
    (hcut : d * e ≤ U * (N * Real.sqrt (F / (M * b)))) :
    D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B))) := by
  have harg (z : ℝ) : F / (M * z) = (F / M) / z := by ring
  simp only [harg] at hcut ⊢
  have hh := original_middle_rectangle_upper (F / M) B b D₁ D₂ d e (U * N)
    (div_pos hF hM) hB hb (mul_nonneg hU hN) hD₁ hD₂ hd he
    (by simpa only [mul_assoc] using hcut)
  simpa only [mul_assoc] using hh

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

def dualMiddleWindowAt (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ D : S, ∑ E : T, ∑ i, if P (D.val * E.val) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) /
        (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalMiddleWindowAt W S T rows left right a b M P h ∧
    originalMiddleWindowAt W S T rows left right a b M P h ≤
      originalMiddleAt W S T rows left right a b M h := by
  classical
  constructor
  · unfold originalMiddleWindowAt
    positivity
  · unfold originalMiddleWindowAt originalMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_bounds (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ dualMiddleWindowAt W S T rows left right a b M F P h ∧
    dualMiddleWindowAt W S T rows left right a b M F P h ≤
      dualMiddleAt W S T rows left right a b M F h := by
  classical
  constructor
  · unfold dualMiddleWindowAt
    positivity
  · unfold dualMiddleWindowAt dualMiddleAt
    gcongr with D _ E _ i _
    split_ifs <;> first | exact le_rfl | positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    originalMiddleWindowAt W S T rows left right a b M P h = 0 := by
  classical
  simp only [originalMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_zero (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hP : ∀ (D : S) (E : T) i, ¬ P (D.val * E.val) i) :
    dualMiddleWindowAt W S T rows left right a b M F P h = 0 := by
  classical
  simp only [dualMiddleWindowAt, hP, ite_false, Finset.sum_const_zero]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊

theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases j with _ | j
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

lemma positive_ideal_dyadic_exists (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    ∃ j ∈ Finset.range (columnDyadicLength N + 1),
      (2 : ℝ)^j/2 < (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^j := by
  have hp : 1 ≤ Ideal.absNorm D := by exact_mod_cast hD
  exact exists_dyadic_shell (Ideal.absNorm D) (columnDyadicLength N) hp
    (hDN.trans (columnDyadicLength_cover N))

def divisorDyadicLabel (N : ℝ) (D : Ideal O) : Fin (columnDyadicLength N+1) :=
  if h : 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N then
    ⟨(positive_ideal_dyadic_exists N D h.1 h.2).choose,
      Finset.mem_range.mp (positive_ideal_dyadic_exists N D h.1 h.2).choose_spec.1⟩
  else ⟨0,by omega⟩

def divisorDyadicBin (S : Finset (Ideal O)) (N : ℝ)
    (j : Fin (columnDyadicLength N+1)) : Finset (Ideal O) :=
  S.filter (fun D => divisorDyadicLabel N D = j)

def divisorDyadicScale (j : ℕ) : ℝ := max 1 ((2 : ℝ)^j/2)

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem divisorDyadicBin_scale_le (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (hj : (divisorDyadicBin S N j).Nonempty) :
    divisorDyadicScale j.val ≤ N := by
  obtain ⟨D,hD⟩ := hj
  exact (divisorDyadicBin_bounds S N hS j D hD).1.trans (hS D (Finset.mem_filter.mp hD).1).2

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

theorem sum_divisorDyadicRectangles {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (N : ℝ) (f : Ideal O → Ideal O → A) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) =
      ∑ j : Fin (columnDyadicLength N+1), ∑ k : Fin (columnDyadicLength N+1),
        ∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E := by
  calc
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ E ∈ T, f D E := sum_divisorDyadicBins S N _
    _ = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j,
        ∑ k : Fin (columnDyadicLength N+1), ∑ E ∈ divisorDyadicBin T N k, f D E := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro D hD
      exact sum_divisorDyadicBins T N (f D)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm


theorem divisor_dyadic_sum_le (S T : Finset (Ideal O)) (N : ℝ)
    (f : Ideal O → Ideal O → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k : Fin (columnDyadicLength N + 1),
      (divisorDyadicBin S N j).Nonempty → (divisorDyadicBin T N k).Nonempty →
      (∑ D ∈ divisorDyadicBin S N j, ∑ E ∈ divisorDyadicBin T N k, f D E) ≤ C) :
    (∑ D ∈ S, ∑ E ∈ T, f D E) ≤ ((columnDyadicLength N + 1 : ℕ) : ℝ)^2 * C := by
  rw [sum_divisorDyadicRectangles S T N f]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      by_cases hS : (divisorDyadicBin S N j).Nonempty
      · by_cases hT : (divisorDyadicBin T N k).Nonempty
        · exact hb j k hS hT
        · simpa only [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty, Finset.sum_const_zero] using hC
      · simpa only [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty] using hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_two]; ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

lemma kernelLogPhase_zero (t : ℝ) : kernelLogPhase t 0 = 1 := by
  simp [kernelLogPhase]

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap


section

open scoped BigOperators Classical SchwartzMap

section
open Eisenstein MeasureTheory

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
  (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
  (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
  (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
  (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)

include hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT hr hl hri hrows ha hb

theorem HasSieveExponent.original_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_original_middle_all_frequencies ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    originalMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * Real.sqrt (M / B)
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.original_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply original_middle_rectangle_upper M B (Ideal.absNorm (rows i).val) D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM (by linarith) (hrows i).1 hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) = fun _ => 0 :=
      funext (fun h => originalMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.dual_middle_window
    (hU : 0 ≤ U) (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F) (P : Ideal O → m → Prop)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U *
        (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
        divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
          (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)) := by
  have hs0 := (actual_dual_middle_all_frequencies ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W hleft hright).1
  have hbounds (h : {h : O // h ≠ 0}) :=
    dualMiddleWindowAt_bounds W S T rows left right (a h.val) (b h.val) M F P h.val
  have hs := Summable.of_nonneg_of_le (fun h => (hbounds h).1) (fun h => (hbounds h).2) hs0
  refine ⟨hs, ?_⟩
  by_cases hcut : D₁ * D₂ ≤ (2 * U) * (N * Real.sqrt (F / (M * B)))
  · exact (hs.tsum_le_tsum (fun h => (hbounds h).2) hs0).trans
      (hexp.dual_middle_block deltaLoss hδ ε hε S T D₁ D₂ B N M (2 * U)
        hD₁ hD₂ hB hN hD₁N hD₂N hM hS hT rows left right hr hl hri hrows a₀ b₀ a b ha hb W F hF hleft hright hcut)
  · have hp (D : S) (E : T) (i : m) : ¬ P (D.val * E.val) i := by
      intro hh
      apply hcut
      apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i).val) N D₁ D₂
        (Ideal.absNorm D.val) (Ideal.absNorm E.val) U hM hF (by linarith) (hrows i).1 (by linarith) hU
        (by linarith) (by linarith) (hS D.val D.property).1 (hT E.val E.property).1
      simpa only [map_mul, Nat.cast_mul] using hP D E i hh
    have hz : (fun h : {h : O // h ≠ 0} =>
        dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) = fun _ => 0 :=
      funext (fun h => dualMiddleWindowAt_eq_zero W S T rows left right (a h.val) (b h.val) M F P h.val hp)
    rw [hz, tsum_zero]
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

end

section
open Eisenstein MeasureTheory

theorem large_principal_scale_shape (X N Q D V : ℝ) (hD : 0 < D)
    (hcut : X * N ≤ V * D) :
    (X / D) * (N + Q * D) ≤ V + X * Q := by
  have hh : X * N / D ≤ V := (div_le_iff₀ hD).mpr hcut
  calc
    _ = X * N / D + X * Q := by field_simp
    _ ≤ _ := add_le_add hh le_rfl

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalCorrectionAt (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) : ℝ :=
  ∑ D : S, ∑ E : T, ∑ i,
    (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖

variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
  (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
  (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
  (a : n → ℂ) (b : p → ℂ)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hleft hright

theorem principalCorrectionAt_bound :
    principalCorrectionAt S T rows left right a b M ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  have hh := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N (by linarith) (by linarith) (by linarith)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    rows left right hr hl hri (fun i => (hrows i).2) hleft hright a b
    (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add, kernelLogPhase_zero, mul_one] at hh
  have heq : (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖) =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ := by
    rw [Finset.sum_coe_sort S (fun D => ∑ E : T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E.val i j k‖)]
    apply Finset.sum_congr rfl
    intro D hD
    exact Finset.sum_coe_sort T (fun E => ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)
  have hp := principal_middle_prefactor_sum S T (fun i => (rows i).val)
    (fun D E i => ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k‖)
    (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM (by linarith) (by linarith) (by linarith)
    (fun i => (hrows i).1) (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
  change principalCorrectionAt S T rows left right a b M ≤ _ at hp
  rw [heq] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hh (by positivity))

theorem HasSieveExponent.large_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N) (V : ℝ)
    (hcut : Real.sqrt (M / B) * N ≤ V * (D₁ * D₂)) :
    principalCorrectionAt S T rows left right a b M ≤
      2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (V + Real.sqrt M * B ^ (α - 1 / 2)) := by
  have hb := principalCorrectionAt_bound ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε S T B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N
    (fun D hD => (hS D hD).2) (fun E hE => (hT E hE).2) a b
  have hf := divisorEnergyFactor_nonneg ε hε N a b
  have hconst := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2 * Real.sqrt (M / B) / (D₁ * D₂)) *
        (divisorEnergyFactor ε hε N a b *
          (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss * (N + B ^ α * (D₁ * D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        ((Real.sqrt (M / B) / (D₁ * D₂)) * (N + B ^ α * (D₁ * D₂))) := by ring
    _ ≤ (2 * divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss)) *
        (V + Real.sqrt (M / B) * B ^ α) := mul_le_mul_of_nonneg_left
      (large_principal_scale_shape _ _ _ _ _ (by positivity) hcut) (by positivity)
    _ = _ := by rw [sqrt_div_mul_rpow M B α hM.le (by linarith)]

end

section
open Eisenstein MeasureTheory

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem sum_two_subtype_pools {A : Type*} [AddCommMonoid A]
    (S T : Finset (Ideal O)) (f : Ideal O → Ideal O → A) :
    (∑ D : S, ∑ E : T, f D.val E.val) = ∑ D ∈ S, ∑ E ∈ T, f D E := by
  rw [Finset.sum_coe_sort S (fun D => ∑ E : T, f D E.val)]
  apply Finset.sum_congr rfl
  intro D hD
  exact Finset.sum_coe_sort T (f D)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold originalMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) * ‖ringComplex h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    originalMiddleWindowAt W S T rows left right a b M P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M P h := by
  classical
  simp_rw [originalMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.original_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := originalMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    originalMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.original_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply originalMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply originalMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      originalMiddleWindowAt W S T rows left right (a h.val) (b h.val) M P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact originalMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

open Eisenstein MeasureTheory

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_eq_finset (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D * E) i then
        (Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) /
          ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
        ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
          (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) / (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
            ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0 := by
  classical
  unfold dualMiddleWindowAt
  exact sum_two_subtype_pools (A := ℝ) S T (fun D E => ∑ i, if P (D * E) i then
    (Real.sqrt ((M / F) / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ))) *
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * paperRadialFourier W
      (Real.sqrt (F * (Ideal.absNorm (left j).val : ℝ) * (Ideal.absNorm (right k).val : ℝ) / (M * (Ideal.absNorm (rows i).val : ℝ))) * ‖ringComplex h‖ ^ 2 /
        ((Ideal.absNorm D : ℝ) * (Ideal.absNorm E : ℝ)))‖ else 0)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dualMiddleWindowAt_dyadic (W : 𝓢(ℝ, ℂ)) (S T : Finset (Ideal O)) (N : ℝ)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) (h : O) :
    dualMiddleWindowAt W S T rows left right a b M F P h =
      ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1),
        dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          rows left right a b M F P h := by
  classical
  simp_rw [dualMiddleWindowAt_eq_finset]
  exact sum_divisorDyadicRectangles (A := ℝ) S T N _

theorem HasSieveExponent.dual_middle_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (S T : Finset (Ideal O)) (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ N)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, N / 2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N / 2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ (D : S) (E : T) i, P (D.val * E.val) i →
      (Ideal.absNorm (D.val * E.val) : ℝ) ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i).val : ℝ))))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))) := by
  classical
  let V := (2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2))
  have hV : 0 ≤ V := by
    have h1 := nonzeroLatticeEnvelopeConstant_nonneg
    have h2 := dualMiddleDecayConstant_nonneg W
    have h3 := divisorEnergyFactor_nonneg ε hε N a₀ b₀
    have h4 := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    positivity
  let f := fun (j k : Fin (columnDyadicLength N + 1)) (h : {h : O // h ≠ 0}) =>
    dualMiddleWindowAt W (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      rows left right (a h.val) (b h.val) M F P h.val
  have hf (j k : Fin (columnDyadicLength N + 1)) : Summable (f j k) ∧ (∑' h, f j k h) ≤ V := by
    by_cases hSj : (divisorDyadicBin S N j).Nonempty
    · by_cases hTk : (divisorDyadicBin T N k).Nonempty
      · exact hexp.dual_middle_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
          (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M U
          (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN
          (divisorDyadicBin_scale_le S N hS j hSj) (divisorDyadicBin_scale_le T N hT k hTk)
          hM (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
          rows left right hr hl hri hrows a₀ b₀ a b ha hb hU W F hF P hleft hright
          (fun D E i hp => hP
            ⟨D.val, (Finset.mem_filter.mp D.property).1⟩
            ⟨E.val, (Finset.mem_filter.mp E.property).1⟩ i hp)
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hTk
        have he : f j k = fun _ => 0 := by
          funext h
          apply dualMiddleWindowAt_eq_zero
          intro D E i hp
          have hh := E.property
          simp only [hz, Finset.notMem_empty] at hh
        rw [he]
        simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hSj
      have he : f j k = fun _ => 0 := by
        funext h
        apply dualMiddleWindowAt_eq_zero
        intro D E i hp
        have hh := D.property
        simp only [hz, Finset.notMem_empty] at hh
      rw [he]
      simpa only [tsum_zero] using And.intro (summable_zero : Summable (fun _ : {h : O // h ≠ 0} => (0 : ℝ))) hV
  have he : (fun h : {h : O // h ≠ 0} =>
      dualMiddleWindowAt W S T rows left right (a h.val) (b h.val) M F P h.val) =
      fun h => ∑ j, ∑ k, f j k h := by
    funext h
    exact dualMiddleWindowAt_dyadic W S T N rows left right (a h.val) (b h.val) M F P h.val
  rw [he]
  refine ⟨summable_sum (fun j _ => summable_sum (fun k _ => (hf j k).1)), ?_⟩
  rw [Summable.tsum_finsetSum (fun j _ => summable_sum (fun k _ => (hf j k).1))]
  calc
    _ = ∑ j, ∑ k, ∑' h, f j k h := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Summable.tsum_finsetSum (fun k _ => (hf j k).1)
    _ ≤ ∑ j : Fin (columnDyadicLength N + 1), ∑ k : Fin (columnDyadicLength N + 1), V :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => (hf j k).2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, V, pow_two]; ring

end

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.QuadraticDivisorSplit
open Eisenstein UniqueFactorizationMonoid

theorem exists_unique_split (B C D : Ideal O) (hBC : IsCoprime B C)
    (hD : D ∣ B * C) :
    ∃! x : Ideal O × Ideal O, x.1 ∣ B ∧ x.2 ∣ C ∧ x.1 * x.2 = D := by
  obtain ⟨D₁, D₂, h₁, h₂, hprod⟩ := exists_dvd_and_dvd_of_dvd_mul hD
  refine ⟨(D₁, D₂), ⟨h₁, h₂, hprod.symm⟩, ?_⟩
  intro y hy
  apply Prod.ext
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.mono hy.1 h₂).dvd_of_dvd_mul_right
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_right _ _
    · apply (hBC.mono h₁ hy.2.1).dvd_of_dvd_mul_right
      rw [hy.2.2, hprod]
      exact dvd_mul_right _ _
  · apply associated_iff_eq.mp
    apply associated_of_dvd_dvd
    · apply (hBC.symm.mono hy.2.1 h₁).dvd_of_dvd_mul_left
      rw [← hprod, ← hy.2.2]
      exact dvd_mul_left _ _
    · apply (hBC.symm.mono h₂ hy.1).dvd_of_dvd_mul_left
      rw [hy.2.2, hprod]
      exact dvd_mul_left _ _

theorem split_product_injective (B C : Ideal O) (hBC : IsCoprime B C) :
    Function.Injective (fun x : {x : Ideal O × Ideal O // x.1 ∣ B ∧ x.2 ∣ C} =>
      x.val.1 * x.val.2) := by
  intro x y hxy
  have hD : x.val.1 * x.val.2 ∣ B * C := mul_dvd_mul x.property.1 x.property.2
  obtain ⟨z, hz, huniq⟩ := exists_unique_split B C (x.val.1 * x.val.2) hBC hD
  apply Subtype.ext
  exact (huniq x.val ⟨x.property.1, x.property.2, rfl⟩).trans
    (huniq y.val ⟨y.property.1, y.property.2, hxy.symm⟩).symm



theorem divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)

theorem sum_divisors_coprime_product (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he


end SchwartzPlanePoisson.QuadraticDivisorSplit

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
