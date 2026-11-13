/-
Principal majorants and bad-prime sectors adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.DyadicDivisorBins

/-!
# Principal majorants and bad-prime sectors

Column divisor pools and the principal majorants of the quadratic pair terms. Squarefree
ideals split into a divisor of the fixed mask and an admissible row; summing the finitely many
bad-prime sectors removes admissibility from reflected rows.
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
open Eisenstein MeasureTheory
open scoped SchwartzMap

section
lemma divisorPool_filter (S : Finset (Ideal O)) (B : Ideal O) (hB : B ≠ 0)
    (hS : ∀ D, D ∣ B → D ∈ S) :
    S.filter (fun D => D ∣ B) = idealDivisors B := by
  ext D
  simp only [Finset.mem_filter, mem_idealDivisors hB]
  exact ⟨And.right, fun h => ⟨hS D h,h⟩⟩

lemma divisor_product_delta (S T : Finset (Ideal O)) (B C d : Ideal O)
    (hB : B ≠ 0) (hC : C ≠ 0) (hBC : IsCoprime B C)
    (hS : ∀ D, D ∣ B → D ∈ S) (hT : ∀ E, E ∣ C → E ∈ T)
    (f : Ideal O → ℂ) :
    (∑ D ∈ S, if D ∣ B then
      ∑ E ∈ T, if E ∣ C then (if D*E=d then f (D*E) else 0) else 0 else 0) =
      if d ∣ B*C then f d else 0 := by
  have hs := QuadraticDivisorSplit.sum_divisors_coprime_product B C hB hC hBC
    (fun q => if q=d then f q else 0)
  have hleft : (∑ q ∈ idealDivisors (B*C), if q=d then f q else 0) =
      if d ∣ B*C then f d else 0 := by
    simp [mem_idealDivisors (mul_ne_zero hB hC)]
  rw [hleft] at hs
  rw [← divisorPool_filter S B hB hS, ← divisorPool_filter T C hC hT] at hs
  simpa only [Finset.sum_filter] using hs.symm

private lemma four_sums_exchange {α β γ deltaLoss : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (V : Finset deltaLoss)
    (f : α → β → γ → deltaLoss → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, ∑ d ∈ V, f a b c d) =
      ∑ c ∈ U, ∑ d ∈ V, ∑ a ∈ S, ∑ b ∈ T, f a b c d := by
  have h : (∑ ab ∈ S ×ˢ T, ∑ cd ∈ U ×ˢ V, f ab.1 ab.2 cd.1 cd.2) =
      ∑ cd ∈ U ×ˢ V, ∑ ab ∈ S ×ˢ T, f ab.1 ab.2 cd.1 cd.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

private lemma three_sums_exchange {α β γ : Type*}
    (S : Finset α) (T : Finset β) (U : Finset γ) (f : α → β → γ → ℝ) :
    (∑ a ∈ S, ∑ b ∈ T, ∑ c ∈ U, f a b c) =
      ∑ b ∈ T, ∑ c ∈ U, ∑ a ∈ S, f a b c := by
  have h : (∑ a ∈ S, ∑ bc ∈ T ×ˢ U, f a bc.1 bc.2) =
      ∑ bc ∈ T ×ˢ U, ∑ a ∈ S, f a bc.1 bc.2 := Finset.sum_comm
  simpa only [Finset.sum_product] using h

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalTerm_product_divisor (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m) (j : n) (k : p)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      originalTerm rows left right a b D E i j k * F (D*E) i j k else 0) =
    (if d ∣ (left j).val*(right k).val then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) := by
  by_cases hc : (left j).val ⊔ (right k).val = ⊤
  · have hd := divisor_product_delta S T (left j).val (right k).val d (hleft j) (hright k) (Ideal.isCoprime_iff_sup_eq.mpr hc)
      (hS j) (hT k) (fun q =>
        star (canonicalQuadraticRow (left j) (primaryIdealGenerator (rows i).val) * a j) *
          (canonicalQuadraticRow (right k) (primaryIdealGenerator (rows i).val) * b k) * F q i j k)
    calc
      _ = (∑ D ∈ S, if D ∣ (left j).val then ∑ E ∈ T, if E ∣ (right k).val then
          (if D*E=d then
            star (canonicalQuadraticRow (left j) (primaryIdealGenerator (rows i).val) * a j) *
              (canonicalQuadraticRow (right k) (primaryIdealGenerator (rows i).val) * b k) * F (D*E) i j k
          else 0) else 0 else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases hd : D ∣ (left j).val
        · simp only [if_pos hd]
          apply Finset.sum_congr rfl
          intro E hE
          by_cases he : E ∣ (right k).val <;> by_cases hde : D*E=d <;>
            simp [originalTerm,hc,hd,he,hde]
        · simp [originalTerm,hc,hd]
      _ = _ := by simpa [originalTerm,hc] using hd
  · simp [originalTerm,hc]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_product_divisor (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (d : Ideal O) (i : m)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T)
    (F : Ideal O → m → n → p → ℂ) :
    (∑ j, ∑ k, if d ∣ (left j).val*(right k).val then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0) =
    ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
      (∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k) else 0 := by
  calc
    _ = ∑ j, ∑ k, ∑ D ∈ S, ∑ E ∈ T, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      exact (originalTerm_product_divisor S T rows left right a b d i j k hleft hright hS hT F).symm
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ j, ∑ k, if D*E=d then
        originalTerm rows left right a b D E i j k * F (D*E) i j k else 0 :=
      four_sums_exchange Finset.univ Finset.univ S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      by_cases h : D*E=d <;> simp [h]

omit [Fintype m] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalColumnSum_divisor_rectangles (K S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (i : m)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T)
    (P : Ideal O → m → Prop) [DecidablePred (fun d => P d i)]
    (F : Ideal O → m → n → p → ℂ) :
    (∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ (left j).val*(right k).val then
      originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
    ∑ D ∈ S, ∑ E ∈ T, if D*E ∈ K then if P (D*E) i then
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k‖ else 0 else 0 := by
  let B := fun D E => ∑ j, ∑ k, originalTerm rows left right a b D E i j k * F (D*E) i j k
  have hpoint (d : Ideal O) :
      (if P d i then ‖∑ j, ∑ k, if d ∣ (left j).val*(right k).val then
        originalTerm rows left right a b 1 1 i j k * F d i j k else 0‖ else 0) ≤
      ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 := by
    by_cases hp : P d i
    · simp only [hp, and_true]
      rw [originalColumnSum_product_divisor S T rows left right a b d i hleft hright hS hT F]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro D hD
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro E hE
      by_cases h : D*E=d <;> simp [h,B]
    · simp [hp]
  calc
    _ ≤ ∑ d ∈ K, ∑ D ∈ S, ∑ E ∈ T, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      Finset.sum_le_sum (fun d hd => hpoint d)
    _ = ∑ D ∈ S, ∑ E ∈ T, ∑ d ∈ K, if D*E=d ∧ P d i then ‖B D E‖ else 0 :=
      three_sums_exchange K S T _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro E hE
      have heq (d : Ideal O) : (if D*E=d ∧ P d i then ‖B D E‖ else 0) =
          if d=D*E then (if P (D*E) i then ‖B D E‖ else 0) else 0 := by
        by_cases h : d=D*E
        · subst d
          simp
        · simp [h,Ne.symm h]
      simp_rw [heq]
      simp only [Finset.sum_ite_eq', B]

end

def columnDivisorPool {n : Type*} [Fintype n] (left : n → Ideal O) : Finset (Ideal O) :=
  Finset.univ.biUnion (fun j => idealDivisors (left j))

theorem mem_columnDivisorPool_of_dvd {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (j : n) (D : Ideal O)
    (hD : D ∣ left j) : D ∈ columnDivisorPool left := by
  apply Finset.mem_biUnion.mpr
  exact ⟨j,Finset.mem_univ j,(mem_idealDivisors (hleft j)).mpr hD⟩

theorem columnDivisorPool_norm_bounds {n : Type*} [Fintype n]
    (left : n → Ideal O) (hleft : ∀ j, left j ≠ 0) (N : ℝ)
    (hN : ∀ j, (Ideal.absNorm (left j) : ℝ) ≤ N)
    (D : Ideal O) (hD : D ∈ columnDivisorPool left) :
    1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N := by
  obtain ⟨j,hj,hDj⟩ := Finset.mem_biUnion.mp hD
  have hd := (mem_idealDivisors (hleft j)).mp hDj
  have hDz : D ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hd
    exact hleft j hd
  have hDN : Ideal.absNorm D ≤ Ideal.absNorm (left j) :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (fun h => hleft j (Ideal.absNorm_eq_zero_iff.mp h)))
      (map_dvd Ideal.absNorm hd)
  refine ⟨?_,(Nat.cast_le.mpr hDN).trans (hN j)⟩
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hDz (Ideal.absNorm_eq_zero_iff.mp h))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

theorem norm_double_sum_real_factor {n p : Type*} [Fintype n] [Fintype p]
    (u : n → p → ℂ) (z : ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖∑ j, ∑ k, u j k * ((c : ℂ) * z)‖ = c * ‖∑ j, ∑ k, u j k * z‖ := by
  simp only [← Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalPrincipalKernel (W : 𝓢(ℝ, ℂ)) (rows : m → QuadraticIdeal) (M : ℝ) (h : O)
    (d : Ideal O) (i : m) : ℂ :=
  ((Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) / (Ideal.absNorm d : ℝ) : ℝ) : ℂ) *
    paperRadialFourier W (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) *
      ‖ringComplex h‖ ^ 2 / (Ideal.absNorm d : ℝ))

def originalProductDivisorMiddleAt (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ (left j).val * (right k).val then
      originalTerm rows left right a b 1 1 i j k * originalPrincipalKernel W rows M h d i else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_nonneg (W : 𝓢(ℝ, ℂ)) (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O) :
    0 ≤ originalProductDivisorMiddleAt W K rows left right a b M P h := by
  classical
  unfold originalProductDivisorMiddleAt
  positivity

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem originalProductDivisorMiddleAt_le_window
    (W : 𝓢(ℝ, ℂ)) (K S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) (h : O)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T) :
    originalProductDivisorMiddleAt W K rows left right a b M P h ≤
      originalMiddleWindowAt W S T rows left right a b M (fun d i => d ∈ K ∧ P d i) h := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P (fun d i _ _ => originalPrincipalKernel W rows M h d i)
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  rw [originalMiddleWindowAt_eq_finset]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : D * E ∈ K
  · by_cases hpi : P (D * E) i
    · simp only [hd, hpi, and_self, ite_true]
      unfold originalPrincipalKernel
      simp only [map_mul, Nat.cast_mul]
      exact norm_double_sum_real_factor _ _ _ (by positivity)
    · simp only [hd, hpi, and_false, ite_false, ite_true]
  · simp only [hd, false_and, ite_false]

theorem HasSieveExponent.original_product_divisor_middle {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (K : Finset (Ideal O)) (B N M U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (a₀ : n → ℂ) (b₀ : p → ℂ) (a : O → n → ℂ) (b : O → p → ℂ)
    (ha : ∀ h j, ‖a h j‖ ≤ ‖a₀ j‖) (hb : ∀ h k, ‖b h k‖ ≤ ‖b₀ k‖)
    (W : 𝓢(ℝ, ℂ)) (P : Ideal O → m → Prop)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hP : ∀ d ∈ K, ∀ i, P d i →
      (Ideal.absNorm d : ℝ) ≤ U * Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ))) :
    Summable (fun h : {h : O // h ≠ 0} =>
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ∧
    (∑' h : {h : O // h ≠ 0},
      originalProductDivisorMiddleAt W K rows left right (a h.val) (b h.val) M P h.val) ≤
      ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * originalMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a₀ b₀ * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
            (N + (2 * U) * Real.sqrt M * B ^ (α - 1 / 2))) := by
  let S := columnDivisorPool (fun j => (left j).val)
  let T := columnDivisorPool (fun k => (right k).val)
  have hl0 : ∀ j, (left j).val ≠ 0 := fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1
  have hr0 : ∀ k, (right k).val ≠ 0 := fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1
  have hs := hexp.original_middle_pool deltaLoss hδ ε hε S T B N M U hB hN hM hU
    (columnDivisorPool_norm_bounds (fun j => (left j).val) hl0 N hleft)
    (columnDivisorPool_norm_bounds (fun k => (right k).val) hr0 N hright)
    rows left right hr hl hri hrows a₀ b₀ a b ha hb W (fun d i => d ∈ K ∧ P d i) hleft hright
    (fun D E i hp => hP _ hp.1 i hp.2)
  have hdom (h : {h : O // h ≠ 0}) := originalProductDivisorMiddleAt_le_window W K S T
    rows left right (a h.val) (b h.val) M P h.val hl0 hr0
    (mem_columnDivisorPool_of_dvd (fun j => (left j).val) hl0)
    (mem_columnDivisorPool_of_dvd (fun k => (right k).val) hr0)
  have ht := Summable.of_nonneg_of_le
    (fun h : {h : O // h ≠ 0} => originalProductDivisorMiddleAt_nonneg W K rows left right
      (a h.val) (b h.val) M P h.val) hdom hs.1
  exact ⟨ht, (ht.tsum_le_tsum hdom hs.1).trans hs.2⟩

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

section
def halfShellFactor (N q : ℝ) : ℝ := Real.sqrt (N/2) / Real.sqrt q

lemma halfShellFactor_nonneg (N q : ℝ) : 0 ≤ halfShellFactor N q := by
  unfold halfShellFactor
  positivity

lemma halfShellFactor_le_one (N q : ℝ) (hq : 0 < q) (h : N/2 ≤ q) :
    halfShellFactor N q ≤ 1 := by
  unfold halfShellFactor
  exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.sqrt_le_sqrt h)

lemma halfShellFactor_pair (M F N i j : ℝ) (hN : 0 < N) (hi : 0 < i) (hj : 0 < j)
    (hF : 0 < F) :
    (2*M/(F*N))*halfShellFactor N i*halfShellFactor N j =
      M/(Real.sqrt (i*j)*F) := by
  unfold halfShellFactor
  rw [Real.sqrt_mul hi.le]
  have hs := Real.sq_sqrt (show 0 ≤ N/2 by positivity)
  have hsi := (Real.sqrt_pos.mpr hi).ne'
  have hsj := (Real.sqrt_pos.mpr hj).ne'
  field_simp
  rw [hs]
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def smallPrincipalCorrection (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) : ℝ :=
  ∑ D ∈ S, ∑ E ∈ T, ∑ i,
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k *
      ((M/(Real.sqrt ((Ideal.absNorm (left j).val : ℝ)*(Ideal.absNorm (right k).val : ℝ))*F) : ℝ) : ℂ)‖

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma originalTerm_real_scaling
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (u : n → ℝ) (v : p → ℝ)
    (D E : Ideal O) (i : m) (j : n) (k : p) :
    originalTerm rows left right (fun j => a j*(u j:ℂ)) (fun k => b k*(v k:ℂ)) D E i j k =
      originalTerm rows left right a b D E i j k * (u j:ℂ) * (v k:ℂ) := by
  unfold originalTerm
  by_cases hc : (left j).val ⊔ (right k).val = ⊤ <;>
    by_cases hd : D ∣ (left j).val <;> by_cases he : E ∣ (right k).val <;>
    simp only [hc,hd,he,ite_true,ite_false,mul_zero,zero_mul,star_zero,star_mul,Complex.star_def,
      Complex.conj_ofReal] ; ring

theorem smallPrincipalCorrection_bound
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      (2*M/(F*N))*Real.sqrt (divisorBlockCost ε hε S T D₁ D₂ B N a b) := by
  have hN0 : 0 < N := by linarith
  let u := fun j => halfShellFactor N (Ideal.absNorm (left j).val : ℝ)
  let v := fun k => halfShellFactor N (Ideal.absNorm (right k).val : ℝ)
  let a' := fun j => a j*(u j:ℂ)
  let b' := fun k => b k*(v k:ℂ)
  have hu (j) : 0 ≤ u j ∧ u j ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hleft j).1]) (hleft j).1⟩
  have hv (k) : 0 ≤ v k ∧ v k ≤ 1 :=
    ⟨halfShellFactor_nonneg _ _,halfShellFactor_le_one _ _ (by linarith [(hright k).1]) (hright k).1⟩
  have ha (j) : ‖a' j‖ ≤ ‖a j‖ := by
    simp only [a',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hu j).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hu j).2
  have hb (k) : ‖b' k‖ ≤ ‖b k‖ := by
    simp only [b',norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hv k).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hv k).2
  have ht (D E : Ideal O) (i j k) :
      originalTerm rows left right a b D E i j k *
        ((M/(Real.sqrt ((Ideal.absNorm (left j).val : ℝ)*(Ideal.absNorm (right k).val : ℝ))*F) : ℝ) : ℂ) =
      ((2*M/(F*N):ℝ):ℂ)*originalTerm rows left right a' b' D E i j k := by
    have hid := halfShellFactor_pair M F N (Ideal.absNorm (left j).val : ℝ) (Ideal.absNorm (right k).val : ℝ)
      hN0 (by linarith [(hleft j).1]) (by linarith [(hright k).1]) hF
    rw [←hid, show originalTerm rows left right a' b' D E i j k =
      originalTerm rows left right a b D E i j k*(u j:ℂ)*(v k:ℂ) from
      originalTerm_real_scaling rows left right a b u v D E i j k]
    push_cast
    dsimp only [u,v]
    ring
  have hblock := canonical_original_divisor_block_phase_bound ε hε S T D₁ D₂ B N (by linarith) (by linarith) (by linarith)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)
    rows left right hr hl hri hrows (fun j => (hleft j).2)
      (fun k => (hright k).2) a' b' (fun _ => 0) (fun _ => 0) 0
  simp only [zero_add,kernelLogPhase_zero,mul_one] at hblock
  have hcost := divisorBlockCost_mono_coefficients ε hε S T D₁ D₂ B N (by linarith) (by linarith) a' a b' b ha hb
  have heq : smallPrincipalCorrection S T rows left right a b M F =
      (2*M/(F*N))*(∑ D ∈ S, ∑ E ∈ T, ∑ i, ‖∑ j, ∑ k, originalTerm rows left right a' b' D E i j k‖) := by
    unfold smallPrincipalCorrection
    simp_rw [ht,←Finset.mul_sum]
    simp only [norm_mul,Complex.norm_of_nonneg (show 0 ≤ 2*M/(F*N) by positivity)]
    simp_rw [←Finset.mul_sum]
  rw [heq]
  exact mul_le_mul_of_nonneg_left (hblock.trans (Real.sqrt_le_sqrt hcost)) (by positivity)

end

open Eisenstein

theorem HasSieveExponent.small_principal_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (hcut : D₁*D₂ ≤ U*(N*Real.sqrt (F/(M*B)))) :
    smallPrincipalCorrection S T rows left right a b M F ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+U*Real.sqrt (M/F)*B^(α-1/2)) := by
  have hb := smallPrincipalCorrection_bound ε hε S T D₁ D₂ B N M F hD₁ hD₂ hN hM hF hS hT
    rows left right hr hl hri hrows hleft hright a b
  have hc := divisor_cost_with_constant hexp deltaLoss hδ ε hε S T B N D₁ D₂ hB hN hD₁ hD₂ hD₁N hD₂N
    (fun D hD => (hS D hD).2) (fun E hE => (hT E hE).2) a b
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hC := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  calc
    _ ≤ (2*M/(F*N))*(divisorEnergyFactor ε hε N a b*
        (divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss*(N+B^α*(D₁*D₂)))) :=
      hb.trans (mul_le_mul_of_nonneg_left hc (by positivity))
    _ = (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss))*
        ((M/(F*N))*(N+B^α*(D₁*D₂))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_middle_scale_shape M F B N (D₁*D₂) U α hM hF (by linarith) (by linarith) hcut)
      (by positivity)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

theorem finite_principal_triangle
    {m n p D : Type*} [Fintype m] [Fintype n] [Fintype p] [Fintype D]
    (muCoefficient : D → ℂ) (hμ : ∀ d, ‖muCoefficient d‖ ≤ 1) (A : m → n → p → D → ℂ) :
    ‖∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d‖ ≤
      ∑ i, ∑ d, ‖∑ j, ∑ k, A i j k d‖ := by
  classical
  have he : (∑ i, ∑ j, ∑ k, ∑ d, muCoefficient d * A i j k d) =
      ∑ i, ∑ d, muCoefficient d * (∑ j, ∑ k, A i j k d) := by
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset p)) (t := (Finset.univ : Finset D)),
      Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset D))]
    simp only [Finset.mul_sum]
  rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hμ d)

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def signedProductDivisorSum (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors ((left j).val*(right k).val), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ)*H d i j k else 0

def correctionRectangleMajorant (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * H (D*E) i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  let pairCols : n × p → Ideal O := fun x => (left x.1).val*(right x.2).val
  let K := columnDivisorPool pairCols
  have hpair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1) (hright x.2)
  have hK : ∀ j k d, d ∣ (left j).val*(right k).val → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hpair (j,k) d hd
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K ((left j).val*(right k).val) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ (left j).val*(right k).val <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ (left j).val*(right k).val then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ (left j).val*(right k).val then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  by_cases hd : D*E ∈ K
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

theorem HasSieveExponent.small_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val:ℝ) ∧ (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val:ℝ) ∧ (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val:ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro E _
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => (hrows i).2) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i).val) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.small_principal_divisor_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val:ℝ) ∧ (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val:ℝ) ∧ (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val:ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  let S := columnDivisorPool (fun j => (left j).val)
  let T := columnDivisorPool (fun k => (right k).val)
  have hl0 : ∀ j, (left j).val ≠ 0 := fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1
  have hr0 : ∀ k, (right k).val ≠ 0 := fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1
  have hS := columnDivisorPool_norm_bounds (fun j => (left j).val) hl0 N (fun j => (hleft j).2)
  have hT := columnDivisorPool_norm_bounds (fun k => (right k).val) hr0 N (fun k => (hright k).2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd (fun j => (left j).val) hl0) (mem_columnDivisorPool_of_dvd (fun k => (right k).val) hr0)).trans
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)

end
end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

section
variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def largePrincipalWindow (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    (Real.sqrt (M / (Ideal.absNorm (rows i).val : ℝ)) /
      ((Ideal.absNorm D : ℝ)*(Ideal.absNorm E : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalWindow_le (S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) :
    largePrincipalWindow S T rows left right a b M P ≤
      principalCorrectionAt S T rows left right a b M := by
  classical
  unfold principalCorrectionAt
  rw [sum_two_subtype_pools S T (fun D E => ∑ i,
    (Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)))*
      ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k‖)]
  unfold largePrincipalWindow
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> first | exact le_rfl | positivity

theorem HasSieveExponent.large_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M V : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hV : 0 ≤ V) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2*D₂)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (V+Real.sqrt M*B^(α-1/2)) := by
  classical
  by_cases hc : Real.sqrt (M/B)*N ≤ V*(D₁*D₂)
  · exact (largePrincipalWindow_le S T rows left right a b M P).trans
      (HasSieveExponent.large_principal_correction ε hε S T D₁ D₂ B N M hD₁ hD₂ hB hN hM hS hT
        rows left right hr hl hri hrows hleft hright a b hexp deltaLoss hδ hD₁N hD₂N V hc)
  · have hz : largePrincipalWindow S T rows left right a b M P = 0 := by
      unfold largePrincipalWindow
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        have hlo := hP D hD E hE i hp
        have hhi : (Ideal.absNorm (D*E):ℝ) ≤ 4*(D₁*D₂) := by
          rw [map_mul, Nat.cast_mul]
          calc
            _ ≤ (2*D₁)*(2*D₂) := mul_le_mul (hS D hD).2 (hT E hE).2 (by positivity) (by linarith)
            _ = _ := by ring
        nlinarith
      simp only [hn, ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.large_principal_pool {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ N)
    (hT : ∀ E ∈ T, 1 ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ N)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i →
      Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm (D*E):ℝ)) :
    largePrincipalWindow S T rows left right a b M P ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  classical
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.large_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M V
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hV
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P
      (fun D hD E hE i hp => hP D (Finset.mem_filter.mp hD).1 E (Finset.mem_filter.mp hE).1 i hp)

end

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def principalDivisorCorrection (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors ((left j).val*(right k).val), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

def largePrincipalProductAt (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop) : ℝ := by
  classical
  exact ∑ i, ∑ d ∈ K, if P d i then
    ‖∑ j, ∑ k, if d ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma largePrincipalProductAt_le_window (K S T : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hS : ∀ j D, D ∣ (left j).val → D ∈ S) (hT : ∀ k E, E ∣ (right k).val → E ∈ T) :
    largePrincipalProductAt K rows left right a b M P ≤
      largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) := by
  classical
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P
    (fun d i _ _ => ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ))
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans_eq
  unfold largePrincipalWindow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hd : D*E ∈ K
  · by_cases hi : P (D*E) i
    · simp only [hd, hi, and_self, ite_true, map_mul, Nat.cast_mul]
      simp only [←Finset.sum_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/
          ((Ideal.absNorm D:ℝ)*(Ideal.absNorm E:ℝ)) by positivity)]
      ring
    · simp only [hd, hi, and_false, ite_true, ite_false]
  · simp only [hd, false_and, ite_false]

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma principalDivisorCorrection_le_product (K : Finset (Ideal O))
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (P : Ideal O → m → Prop)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hK : ∀ j k d, d ∣ (left j).val*(right k).val → d ∈ K) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      largePrincipalProductAt K rows left right a b M P := by
  classical
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d.val:ℝ):ℝ):ℂ) else 0 else 0
  have he : principalDivisorCorrection rows left right a b M P =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val : ℂ)*A i j k d := by
    unfold principalDivisorCorrection
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K ((left j).val*(right k).val) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k *
        ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ (left j).val*(right k).val <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => norm_ideal_moebius_le_one d.val) A).trans_eq
  unfold largePrincipalProductAt
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then
    if d ∣ (left j).val*(right k).val then originalTerm rows left right a b 1 1 i j k *
      ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 else 0‖)]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]

theorem HasSieveExponent.principal_divisor_correction {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M V : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hV : 0 ≤ V)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → Real.sqrt (M/B)*N ≤ (V/4)*(Ideal.absNorm d:ℝ)) :
    ‖principalDivisorCorrection rows left right a b M P‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (V+Real.sqrt M*B^(α-1/2))) := by
  let S := columnDivisorPool (fun j => (left j).val)
  let T := columnDivisorPool (fun k => (right k).val)
  let pairCols : n × p → Ideal O := fun x => (left x.1).val*(right x.2).val
  let K := columnDivisorPool pairCols
  have hl0 : ∀ j, (left j).val ≠ 0 := fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1
  have hr0 : ∀ k, (right k).val ≠ 0 := fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1
  have hp0 : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hl0 x.1) (hr0 x.2)
  have hk : ∀ j k d, d ∣ (left j).val*(right k).val → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hp0 (j,k) d hd
  calc
    _ ≤ largePrincipalProductAt K rows left right a b M P :=
      principalDivisorCorrection_le_product K rows left right a b M P hl0 hr0 hk
    _ ≤ largePrincipalWindow S T rows left right a b M (fun d i => d ∈ K ∧ P d i) :=
      largePrincipalProductAt_le_window K S T rows left right a b M P hl0 hr0
        (mem_columnDivisorPool_of_dvd (fun j => (left j).val) hl0) (mem_columnDivisorPool_of_dvd (fun k => (right k).val) hr0)
    _ ≤ _ := hexp.large_principal_pool deltaLoss hδ ε hε S T B N M V hB hN hM hV
      (columnDivisorPool_norm_bounds (fun j => (left j).val) hl0 N hleft)
      (columnDivisorPool_norm_bounds (fun k => (right k).val) hr0 N hright)
      rows left right hr hl hri hrows hleft hright a b _
      (fun D _ E _ i hp => hP (D*E) i hp.2)

lemma source_large_cut_lower (M B b N T d : ℝ)
    (hM : 0 < M) (_hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) (hN : 0 ≤ N) (hT : 0 < T)
    (hd : T*Real.sqrt (M/b) ≤ d) :
    Real.sqrt (M/B)*N ≤ ((4*N/T)/4)*d := by
  have hs : Real.sqrt (M/B) ≤ Real.sqrt (M/b) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hb hbB)
  have hsd : Real.sqrt (M/B) ≤ d/T := (le_div_iff₀ hT).mpr (by nlinarith)
  calc
    _ ≤ (d/T)*N := mul_le_mul_of_nonneg_right hsd hN
    _ = _ := by ring

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp


theorem HasSieveExponent.source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ)) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b M (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N M (4*N/T) hB hN hM (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact source_large_cut_lower M B (Ideal.absNorm (rows i).val) N T (Ideal.absNorm d) hM (by linarith)
    (by linarith [(hrows i).1]) (hrows i).2 (by linarith) hT ((hZ i).trans hd.le)

theorem HasSieveExponent.dual_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val:ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i).val) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).1]) (hrows i).2 (by linarith) hT ((hZ i).trans hd.le)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_large_principal_normalization
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, (rows i).val ≠ 0) (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0) :
    (∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
      (((M/(Real.sqrt ((Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ))*F):ℝ):ℂ) *
        ((Real.sqrt (F*(Ideal.absNorm (left j).val:ℝ)*(Ideal.absNorm (right k).val:ℝ)/
          (M*(Ideal.absNorm (rows i).val:ℝ))):ℝ):ℂ) *
        ∑ d ∈ idealDivisors ((left j).val*(right k).val), if P d i then
          (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0)) =
      principalDivisorCorrection rows left right a b (M/F) P := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold principalDivisorCorrection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [←Complex.ofReal_mul, dual_principal_prefactor_identity M F (Ideal.absNorm (rows i).val)
    (Ideal.absNorm (left j).val) (Ideal.absNorm (right k).val) hM hF (hpos _ (hrows i))
      (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  · simp only [hd,ite_false,mul_zero]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

theorem sqrt_norm_divisor_scale (M B q : ℝ) (hM : 0 ≤ M) (_hB : 0 ≤ B) (hq : 0 < q) :
    Real.sqrt (M / B) / q = Real.sqrt ((M / q ^ 2) / B) := by
  rw [Real.sqrt_div hM, Real.sqrt_div (by positivity : 0 ≤ M / q ^ 2), Real.sqrt_div hM, Real.sqrt_sq hq.le]
  ring


theorem weightedDivisorCorrection_coprime_mask (G C : Ideal O)
    (hG : G ≠ 0) (hC : C ≠ 0) (hGC : IsCoprime G C) (X Z : ℝ) :
    (∑ d ∈ idealDivisors (G*C), if Z < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*((X/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
    ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      ∑ d ∈ idealDivisors C, if Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((X/(Ideal.absNorm q:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
  classical
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG hC hGC]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG).mp hq
  have hdC := (mem_idealDivisors hC).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
  have hNq : 0 < (Ideal.absNorm q:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hlow : Z < (Ideal.absNorm q:ℝ)*(Ideal.absNorm d:ℝ) ↔
      Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) := by
    constructor
    · intro hz
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hz
  simp only [map_mul,Nat.cast_mul,hlow,(hGC.mono hqG hdC).isRelPrime.moebius_mul,Int.cast_mul]
  by_cases hp : Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)
  · simp only [hp,ite_true]
    push_cast
    ring
  · simp only [hp,ite_false,mul_zero]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def maskedPrincipalDivisorCorrection (G : Ideal O)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (G*((left j).val*(right k).val)), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem maskedPrincipalDivisorCorrection_eq
    (G : Ideal O) (hG : G ≠ 0)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Z : m → ℝ)
    (hleft : ∀ j, (left j).val ≠ 0) (hright : ∀ k, (right k).val ≠ 0)
    (hGl : ∀ j, IsCoprime G (left j).val) (hGr : ∀ k, IsCoprime G (right k).val) :
    maskedPrincipalDivisorCorrection G rows left right a b M Z =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
          (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)) := by
  classical
  have ht (i : m) (j : n) (k : p) :
      (∑ d ∈ idealDivisors (G*((left j).val*(right k).val)), if Z i < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*
          ((Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        ∑ d ∈ idealDivisors ((left j).val*(right k).val), if Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i).val:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
    rw [weightedDivisorCorrection_coprime_mask G _ hG (mul_ne_zero (hleft j) (hright k))
      ((hGl j).mul_right (hGr k))]
    apply Finset.sum_congr rfl
    intro q hq
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hNq : 0 < (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
  unfold maskedPrincipalDivisorCorrection
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset m)) (t := idealDivisors G)]
  simp only [principalDivisorCorrection,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring_nf

theorem HasSieveExponent.masked_source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (hG : G ≠ 0)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val:ℝ) ∧ (Ideal.absNorm (rows i).val:ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val:ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val:ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j).val) (hGr : ∀ k, IsCoprime G (right k).val)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ)) ≤ Z i) :
    ‖maskedPrincipalDivisorCorrection G rows left right a b M Z‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2)))) := by
  classical
  let V := ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (4*N/T+Real.sqrt M*B^(α-1/2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
        (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ))‖ ≤ V := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1 ≤ (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : 0 < (Ideal.absNorm q:ℝ) := by linarith
    have hZq (i : m) : T*Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i).val:ℝ)) ≤
        Z i/(Ideal.absNorm q:ℝ) := by
      rw [←sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
      calc
        _ = (T*Real.sqrt (M/(Ideal.absNorm (rows i).val:ℝ)))/(Ideal.absNorm q:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (hZ i) hqpos.le
    apply (hexp.source_large_principal_sum deltaLoss hδ ε hε B N (M/(Ideal.absNorm q:ℝ)^2) T
      hB hN (by positivity) hT rows left right hr hl hri hrows hleft hright a b
        (fun i => Z i/(Ideal.absNorm q:ℝ)) hZq).trans
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [maskedPrincipalDivisorCorrection_eq G hG rows left right a b M hM.le Z
    (fun j => primaryIdealGenerator_ne_zero_ideal _ (left j).property.1) (fun k => primaryIdealGenerator_ne_zero_ideal _ (right k).property.1) hGl hGr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,V]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

/-- Squarefree ideals split into a divisor of the fixed mask and an admissible row. -/
def quadraticBadSector (B : {I : Ideal O // Squarefree I}) :
    idealDivisors (quadraticMaskIdeal 1) :=
  (squarefreeIdealSplit (quadraticMaskIdeal 1) (quadraticMaskIdeal_squarefree 1) B).1

def quadraticGoodRow (B : {I : Ideal O // Squarefree I}) : QuadraticIdeal :=
  let H := (squarefreeIdealSplit (quadraticMaskIdeal 1) (quadraticMaskIdeal_squarefree 1) B).2
  ⟨H.val, quadraticIdealAdmissible_of_mask_coprime 1 H.val H.property.1 H.property.2⟩

lemma quadraticBadSector_good_product (B : {I : Ideal O // Squarefree I}) :
    (quadraticBadSector B).val * (quadraticGoodRow B).val = B.val :=
  quadraticIdeal_mul_quotient (Ideal.dvd_iff_le.mpr le_sup_left)

lemma quadraticBadSector_ne_zero (D : idealDivisors (quadraticMaskIdeal 1)) : D.val ≠ 0 :=
  ne_zero_of_dvd_ne_zero (quadraticMaskIdeal_squarefree 1).ne_zero
    ((mem_idealDivisors (quadraticMaskIdeal_squarefree 1).ne_zero).mp D.property)

lemma quadraticBadSector_norm_ge_one (D : idealDivisors (quadraticMaskIdeal 1)) :
    (1 : ℝ) ≤ Ideal.absNorm D.val := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (quadraticBadSector_ne_zero D))

lemma quadraticGoodRow_injective_on_sector (B C : {I : Ideal O // Squarefree I})
    (hD : quadraticBadSector B = quadraticBadSector C)
    (hG : quadraticGoodRow B = quadraticGoodRow C) : B = C := by
  apply Subtype.ext
  rw [← quadraticBadSector_good_product B, ← quadraticBadSector_good_product C, hD, hG]

lemma quadraticGoodRow_norm_le (B : {I : Ideal O // Squarefree I}) :
    (Ideal.absNorm (quadraticGoodRow B).val : ℝ) ≤ Ideal.absNorm B.val := by
  rw [← quadraticBadSector_good_product B, map_mul, Nat.cast_mul]
  exact le_mul_of_one_le_left (Nat.cast_nonneg _) (quadraticBadSector_norm_ge_one _)

namespace CanonicalQuadraticSieve

/-- The ideal pair character allows the reflected row to contain either excluded prime. -/
def unrestrictedPairTerm {m n p : Type*}
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if (left j).val ⊔ (right k).val = ⊤ then
    star (a j) * b k * canonicalQuadraticPairIdeal (left j) (right k) (rows i) else 0

/-- Within a fixed bad-prime sector, the pair character is a bounded coefficient twist. -/
lemma unrestrictedPairTerm_sector {m n p : Type*}
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (D : idealDivisors (quadraticMaskIdeal 1)) (hD : ∀ i, quadraticBadSector (rows i) = D)
    (i : m) (j : n) (k : p) :
    unrestrictedPairTerm (fun i => (rows i).val) left right a b i j k =
      originalTerm (fun i => quadraticGoodRow (rows i)) left right
        (fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator D.val))
        (fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator D.val)) 1 1 i j k := by
  have hp : (rows i).val = D.val * (quadraticGoodRow (rows i)).val := by
    rw [← quadraticBadSector_good_product (rows i), hD i]
  unfold unrestrictedPairTerm originalTerm
  by_cases hc : (left j).val ⊔ (right k).val = ⊤
  · simp only [hc, ite_true, one_dvd]
    rw [hp, canonicalQuadraticPairIdeal_mul (left j) (right k) (hray j k),
      canonicalQuadraticPairIdeal_primary (left j) (right k) (hray j k)
        (quadraticGoodRow (rows i)).val (quadraticGoodRow (rows i)).property.1]
    simp only [canonicalQuadraticPairIdeal, star_mul, canonicalQuadraticRow_star]
    ring
  · simp only [hc, ite_false]

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hd := diagonalControl_nonneg sieveCutoff
  unfold divisorEnergyFactor
  gcongr

def smallPrincipalMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)))

lemma smallPrincipalMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  positivity

lemma smallPrincipalMajorant_mono {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B' B N M F U : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB' : 0 ≤ B') (hB : B' ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    smallPrincipalMajorant hexp deltaLoss hδ ε hε B' N M F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have ha0 : 0 ≤ α-1/2 := by linarith
  have hB0 : 0 ≤ B := hB'.trans hB
  unfold smallPrincipalMajorant
  gcongr

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedSmallPrincipalSum
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors ((left j).val * (right k).val), if P d i then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) *
          (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) : ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedSmallPrincipalSum_sector
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (D : idealDivisors (quadraticMaskIdeal 1)) (hD : ∀ i, quadraticBadSector (rows i) = D) :
    unrestrictedSmallPrincipalSum (fun i => (rows i).val) left right a b M F P =
      signedProductDivisorSum (fun i => quadraticGoodRow (rows i)) left right
        (fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator D.val))
        (fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator D.val)) P
        (fun _ _ j k => ((M / (Real.sqrt ((Ideal.absNorm (left j).val : ℝ) *
          (Ideal.absNorm (right k).val : ℝ)) * F) : ℝ) : ℂ)) := by
  unfold unrestrictedSmallPrincipalSum signedProductDivisorSum
  simp_rw [unrestrictedPairTerm_sector rows left right a b hray D hD]

theorem HasSieveExponent.small_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d : ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val : ℝ)))))
    (D : idealDivisors (quadraticMaskIdeal 1)) (hD : ∀ i, quadraticBadSector (rows i) = D) :
    ‖unrestrictedSmallPrincipalSum (fun i => (rows i).val) left right a b M F P‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedSmallPrincipalSum, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b
      (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm D.val
    let good := fun i => quadraticGoodRow (rows i)
    let a' := fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator D.val)
    let b' := fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator D.val)
    have hQ : 1 ≤ Q := quadraticBadSector_norm_ge_one D
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i).val : ℝ) = Q*(Ideal.absNorm (good i).val : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (quadraticBadSector_good_product (rows i))
      rw [hD i] at hi
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (quadraticGoodRow_injective_on_sector _ _ ((hD i).trans (hD k).symm) h)
    have hg (i : m) : (B/Q)/2 ≤ (Ideal.absNorm (good i).val : ℝ) ∧
        (Ideal.absNorm (good i).val : ℝ) ≤ B/Q := by
      constructor
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).mpr
        have hx := (hrows i).1
        rw [hn i] at hx
        nlinarith only [hx]
      · exact (le_div_iff₀ hQp).mpr (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2)
    have hgoodpos (i : m) : 0 < (Ideal.absNorm (good i).val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (good i).property.1))
    have hBQ : 1 ≤ B/Q := by
      have hh : (1 : ℝ) ≤ Ideal.absNorm (good i₀).val := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
          (primaryIdealGenerator_ne_zero_ideal _ (good i₀).property.1))
      exact hh.trans (hg i₀).2
    have hPg (d : Ideal O) (i : m) (hp : P d i) : (Ideal.absNorm d : ℝ) ≤
        U*(N*Real.sqrt (F/(M*(Ideal.absNorm (good i).val : ℝ)))) := by
      apply (hP d i hp).trans
      have hng := quadraticGoodRow_norm_le (rows i)
      have hgpos := hgoodpos i
      gcongr
    rw [unrestrictedSmallPrincipalSum_sector rows left right a b M F P hray D hD]
    have hbnd := hexp.small_principal_divisor_sum deltaLoss hδ ε hε (B/Q) N M F U hBQ hN hM hF hU
      good left right hgr hl hri hg hleft hright a' b' P hPg
    change ‖signedProductDivisorSum good left right a' b' P _‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b
    apply hbnd.trans
    apply smallPrincipalMajorant_mono hexp hα deltaLoss hδ ε hε (B/Q) B N M F U a a' b b'
      (by positivity) (div_le_self (by linarith) hQ) (by linarith) hM.le hF.le hU
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)


/-- Summing the finitely many fixed-prime sectors removes admissibility from reflected rows. -/
theorem HasSieveExponent.unrestricted_small_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, N/2 ≤ (Ideal.absNorm (left j).val : ℝ) ∧ (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, N/2 ≤ (Ideal.absNorm (right k).val : ℝ) ∧ (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d : ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val : ℝ))))) :
    ‖unrestrictedSmallPrincipalSum (fun i => (rows i).val) left right a b M F P‖ ≤
      ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ) *
        smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  let σ := fun i => quadraticBadSector (rows i)
  have hs : unrestrictedSmallPrincipalSum (fun i => (rows i).val) left right a b M F P =
      ∑ D : idealDivisors (quadraticMaskIdeal 1), unrestrictedSmallPrincipalSum
        (fun i : {i // σ i = D} => (rows i.val).val) left right a b M F (fun d i => P d i.val) := by
    unfold unrestrictedSmallPrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (D : idealDivisors (quadraticMaskIdeal 1)) :
      ‖unrestrictedSmallPrincipalSum (fun i : {i // σ i = D} => (rows i.val).val)
        left right a b M F (fun d i => P d i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
    hexp.small_principal_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = D} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun d i => P d i.val) (fun d i => hP d i.val)
      D (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _D : idealDivisors (quadraticMaskIdeal 1),
        smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
      Finset.sum_le_sum (fun D _ => hb D)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

lemma smallPrincipalMajorant_bad_scale {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U Q : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hQ : 1 ≤ Q)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    (1/Q)*smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have hQp : 0 < Q := by linarith
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have hp : ((B/Q)*N)^deltaLoss ≤ (B*N)^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    exact mul_le_mul_of_nonneg_right (div_le_self hB hQ) hN
  have hs := dual_bad_sector_scale M F B Q U α hM hF hB hQ hU hα
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  calc
    _ = ((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a' b'*(divisorExponentConstant hexp deltaLoss hδ*((B/Q)*N)^deltaLoss)*
        ((1/Q)*(M*Q/F+(2*U)*Real.sqrt (M*Q/F)*(B/Q)^(α-1/2)))) := by ring
    _ ≤ _ := by gcongr

lemma sqrt_sector_scale (M F Q b : ℝ) (hM : 0 < M) (hF : 0 < F) (hQ : 0 < Q) (hb : 0 < b) :
    Real.sqrt ((M/F)/(Q*b)) = (1/Q)*Real.sqrt (((M*Q)/F)/b) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (show 0 ≤ (M/F)/(Q*b) by positivity),
    Real.sq_sqrt (show 0 ≤ ((M*Q)/F)/b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedLargePrincipalSum
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors ((left j).val * (right k).val), if Z i < (Ideal.absNorm d : ℝ) then
      (UniqueFactorizationMonoid.moebius d : ℂ) *
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i) : ℝ))/(Ideal.absNorm d : ℝ) : ℝ) : ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedLargePrincipalSum_sector
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (D : idealDivisors (quadraticMaskIdeal 1)) (hD : ∀ i, quadraticBadSector (rows i) = D) :
    unrestrictedLargePrincipalSum (fun i => (rows i).val) left right a b M F Z =
      ((1/(Ideal.absNorm D.val : ℝ) : ℝ) : ℂ) *
        principalDivisorCorrection (fun i => quadraticGoodRow (rows i)) left right
          (fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator D.val))
          (fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator D.val))
          ((M*(Ideal.absNorm D.val : ℝ))/F) (fun d i => Z i < (Ideal.absNorm d : ℝ)) := by
  classical
  have hQp : 0 < (Ideal.absNorm D.val : ℝ) := lt_of_lt_of_le zero_lt_one (quadraticBadSector_norm_ge_one D)
  unfold unrestrictedLargePrincipalSum principalDivisorCorrection
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hray D hD i j k]
  have hn : (Ideal.absNorm (rows i).val : ℝ) =
      (Ideal.absNorm D.val : ℝ) * (Ideal.absNorm (quadraticGoodRow (rows i)).val : ℝ) := by
    have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
      (quadraticBadSector_good_product (rows i))
    rw [hD i] at hi
    simpa only [map_mul, Nat.cast_mul] using hi.symm
  have hgpos : 0 < (Ideal.absNorm (quadraticGoodRow (rows i)).val : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (primaryIdealGenerator_ne_zero_ideal _ (quadraticGoodRow (rows i)).property.1))
  rw [hn, sqrt_sector_scale M F _ _ hM hF hQp hgpos]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Z i < (Ideal.absNorm d : ℝ)
  · simp only [hd, ite_true, Complex.ofReal_div, Complex.ofReal_mul]
    ring
  · simp only [hd, ite_false, mul_zero]

theorem HasSieveExponent.large_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val : ℝ)))) ≤ Z i)
    (D : idealDivisors (quadraticMaskIdeal 1)) (hD : ∀ i, quadraticBadSector (rows i) = D) :
    ‖unrestrictedLargePrincipalSum (fun i => (rows i).val) left right a b M F Z‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedLargePrincipalSum, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a b
      (by linarith) (by linarith) hM.le hF.le (by norm_num)
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm D.val
    let good := fun i => quadraticGoodRow (rows i)
    let a' := fun j => a j * canonicalQuadraticRow (left j) (cubicIdealGenerator D.val)
    let b' := fun k => b k * canonicalQuadraticRow (right k) (cubicIdealGenerator D.val)
    have hQ : 1 ≤ Q := quadraticBadSector_norm_ge_one D
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i).val : ℝ) = Q*(Ideal.absNorm (good i).val : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (quadraticBadSector_good_product (rows i))
      rw [hD i] at hi
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (quadraticGoodRow_injective_on_sector _ _ ((hD i).trans (hD k).symm) h)
    have hg (i : m) : (B/Q)/2 ≤ (Ideal.absNorm (good i).val : ℝ) ∧
        (Ideal.absNorm (good i).val : ℝ) ≤ B/Q := by
      constructor
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).mpr
        have hx := (hrows i).1
        rw [hn i] at hx
        nlinarith only [hx]
      · exact (le_div_iff₀ hQp).mpr (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2)
    have hgoodpos (i : m) : 0 < (Ideal.absNorm (good i).val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (primaryIdealGenerator_ne_zero_ideal _ (good i).property.1))
    have hBQ : 1 ≤ B/Q := by
      have hh : (1 : ℝ) ≤ Ideal.absNorm (good i₀).val := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
          (primaryIdealGenerator_ne_zero_ideal _ (good i₀).property.1))
      exact hh.trans (hg i₀).2
    have hZg (i : m) : T*(N*Real.sqrt (F/((M*Q)*(Ideal.absNorm (good i).val : ℝ)))) ≤ Z i := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_large_principal_sum deltaLoss hδ ε hε (B/Q) N (M*Q) F T hBQ hN
      (by positivity) hF (by linarith) good left right hgr hl hri hg hleft hright a' b' Z hZg
    have hmajor : ‖principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d : ℝ))‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F (1/2) a' b' := by
      apply hbnd.trans
      have ht : 4/T ≤ 1 := (div_le_one (by linarith : 0<T)).mpr hT
      have hlead : 4*(M*Q)/(F*T) ≤ (M*Q)/F := by
        calc
          _ = ((M*Q)/F)*(4/T) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) ht
      have he := divisorEnergyFactor_nonneg ε hε N a' b'
      have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
      unfold smallPrincipalMajorant
      norm_num only [show (2 : ℝ)*(1/2)=1 by norm_num, one_mul]
      gcongr
    have htr := unrestrictedLargePrincipalSum_sector rows left right a b M F Z hM hF hray D hD
    change unrestrictedLargePrincipalSum (fun i => (rows i).val) left right a b M F Z =
      ((1/Q : ℝ) : ℂ) * principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d : ℝ)) at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/Q)]
    apply (mul_le_mul_of_nonneg_left hmajor (by positivity)).trans
    apply smallPrincipalMajorant_bad_scale hexp hα deltaLoss hδ ε hε B N M F (1/2) Q a a' b b'
      (by linarith) (by linarith) hM hF (by norm_num) hQ
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → {I : Ideal O // Squarefree I})
    (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, B/2 ≤ (Ideal.absNorm (rows i).val : ℝ) ∧ (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hleft : ∀ j, (Ideal.absNorm (left j).val : ℝ) ≤ N)
    (hright : ∀ k, (Ideal.absNorm (right k).val : ℝ) ≤ N)
    (hray : ∀ j k, quadraticColumnRay (left j) = quadraticColumnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i).val : ℝ)))) ≤ Z i) :
    ‖unrestrictedLargePrincipalSum (fun i => (rows i).val) left right a b M F Z‖ ≤
      ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ) *
        smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  let σ := fun i => quadraticBadSector (rows i)
  have hs : unrestrictedLargePrincipalSum (fun i => (rows i).val) left right a b M F Z =
      ∑ D : idealDivisors (quadraticMaskIdeal 1), unrestrictedLargePrincipalSum
        (fun i : {i // σ i = D} => (rows i.val).val) left right a b M F (fun i => Z i.val) := by
    unfold unrestrictedLargePrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (D : idealDivisors (quadraticMaskIdeal 1)) :
      ‖unrestrictedLargePrincipalSum (fun i : {i // σ i = D} => (rows i.val).val)
        left right a b M F (fun i => Z i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
    hexp.large_principal_sector hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
      (fun i : {i // σ i = D} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun i => Z i.val) (fun i => hZ i.val)
      D (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _D : idealDivisors (quadraticMaskIdeal 1),
        smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
      Finset.sum_le_sum (fun D _ => hb D)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein

lemma finite_ideal_family_card_bound {m : Type*} [Fintype m]
    (rows : m → Ideal O) (hr : Function.Injective rows) (B : ℝ) (hB : 1 ≤ B)
    (hrows : ∀ i, (Ideal.absNorm (rows i) : ℝ) ≤ B) :
    (Fintype.card m : ℝ) ≤ diagonalControl sieveCutoff * B := by
  classical
  have hb := finite_ideal_card_bound (Finset.univ.image rows) B hB (by
    intro I hI
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hI
    exact hrows i)
  rw [Finset.card_image_iff.mpr hr.injOn, Finset.card_univ] at hb
  exact hb

namespace CanonicalQuadraticSieve

lemma originalTerm_one_norm_le {m n p : Type*}
    (rows : m → QuadraticIdeal) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖originalTerm rows left right a b 1 1 i j k‖ ≤ ‖a j‖ * ‖b k‖ := by
  classical
  simp only [originalTerm, one_dvd, ite_true]
  split_ifs with hc
  · simp only [one_dvd, ite_true, norm_mul, norm_star]
    exact mul_le_mul
      (mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _))
      (mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _))
      (by positivity) (norm_nonneg _)
  · simp only [norm_zero]
    positivity

lemma unrestrictedPairTerm_norm_le {m n p : Type*}
    (rows : m → Ideal O) (left : n → QuadraticIdeal) (right : p → QuadraticIdeal)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖unrestrictedPairTerm rows left right a b i j k‖ ≤ ‖a j‖ * ‖b k‖ := by
  classical
  unfold unrestrictedPairTerm
  split_ifs
  · simp only [norm_mul, norm_star]
    exact mul_le_of_le_one_right (by positivity) (canonicalQuadraticPairIdeal_norm_le_one _ _ _)
  · simp only [norm_zero]
    positivity

/-- A uniform pairwise error costs one row count and one column count after Cauchy–Schwarz. -/
theorem finite_pair_error_bound {m n : Type*} [Fintype m] [Fintype n]
    (pair error : m → n → n → ℂ) (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hp : ∀ i j k, ‖pair i j k‖ ≤ ‖a j‖ * ‖a k‖)
    (he : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, pair i j k * error i j k‖ ≤
      (Fintype.card m : ℝ) * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs : (∑ j, ‖a j‖) ^ 2 ≤ (Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
    simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun _ => (1 : ℝ))
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖pair i j k * error i j k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => norm_sum_le _ _))))
    _ ≤ ∑ _i : m, ∑ j, ∑ k, (‖a j‖ * ‖a k‖) * E := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hp i j k) (he i j k) (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * E * (∑ j, ‖a j‖) ^ 2 := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ (Fintype.card m : ℝ) * E * ((Fintype.card n : ℝ) * ∑ j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = _ := by ring

/-- Counting the two ideal families gives the uniform source error estimate. -/
theorem original_pair_error_ideal_bound {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ B)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (he : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k * error i j k‖ ≤
      (diagonalControl sieveCutoff) ^ 2 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hcr := finite_ideal_family_card_bound (fun i => (rows i).val)
    (Subtype.val_injective.comp hr) B hB hrows
  have hcc := finite_ideal_family_card_bound (fun j => (cols j).val)
    (Subtype.val_injective.comp hc) N hN hcols
  have hd := diagonalControl_nonneg sieveCutoff
  apply (finite_pair_error_bound (originalTerm rows cols cols a a 1 1) error a E hE
    (originalTerm_one_norm_le rows cols cols a a) he).trans
  calc
    _ ≤ (diagonalControl sieveCutoff * B) * (diagonalControl sieveCutoff * N) * E * ∑ j, ‖a j‖ ^ 2 := by
      gcongr
    _ = _ := by ring

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma primeSupport_quadraticMaskIdeal (D : Ideal O) :
    primeSupport (quadraticMaskIdeal D) = quadraticMaskPrimes D := by
  have hf : normalizedFactors (quadraticMaskIdeal D) = (quadraticMaskPrimes D).val := by
    have hp : ∀ P ∈ (quadraticMaskPrimes D).val, Prime P := fun P hP => quadraticMaskPrimes_prime D P hP
    simpa [quadraticMaskIdeal] using normalizedFactors_prod_of_prime hp
  simp only [primeSupport, hf, Finset.val_toFinset]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma quadraticMaskIdeal_supported_factor (D : Ideal O) (hD : quadraticSupported D) :
    quadraticMaskIdeal D = quadraticMaskIdeal 1 * ∏ P ∈ primeSupport D, P := by
  have h1 : quadraticMaskPrimes 1 = {ramifiedIdeal, cubicTwoIdeal} := by
    simp only [quadraticMaskPrimes, primeSupport, normalizedFactors_one,
      Multiset.toFinset_zero, Finset.union_empty]
  have hd : Disjoint ({ramifiedIdeal, cubicTwoIdeal} : Finset (Ideal O)) (primeSupport D) := by
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    have hpD := dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hQ)
    obtain ⟨hr, ht⟩ := (quadraticSupported_iff_bad_not_dvd D).mp hD
    rcases Finset.mem_insert.mp hP with rfl | hP
    · exact hr hpD
    · rw [Finset.mem_singleton.mp hP] at hpD
      exact ht hpD
  simp only [quadraticMaskIdeal, quadraticMaskPrimes, Finset.prod_union hd]
  rw [show ({ramifiedIdeal, cubicTwoIdeal} ∪ primeSupport (1 : Ideal O)) =
    ({ramifiedIdeal, cubicTwoIdeal} : Finset (Ideal O)) from h1]

/-- The fixed excluded primes cost a constant factor in every conductor norm. -/
lemma quadraticMaskIdeal_norm_bound (D : Ideal O) (hD : quadraticSupported D) :
    (Ideal.absNorm (quadraticMaskIdeal D) : ℝ) ≤
      (Ideal.absNorm (quadraticMaskIdeal 1) : ℝ) * (Ideal.absNorm D : ℝ) := by
  have hD0 := primaryIdealGenerator_ne_zero_ideal D hD.1
  have hn : Ideal.absNorm (∏ P ∈ primeSupport D, P) ≤ Ideal.absNorm D :=
    Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
      (map_dvd Ideal.absNorm (support_product_dvd hD0 Finset.Subset.rfl))
  rw [quadraticMaskIdeal_supported_factor D hD, map_mul, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hn) (Nat.cast_nonneg _)

end SchwartzPlanePoisson

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
