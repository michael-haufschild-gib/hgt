import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm
import GaloisForLFunctions.HTGeometry.PsdHankelJetVanishing

/-!
# Nonpositive column subspaces have dimension bounded by negative index

A finite-index kernel admits a positive completion by finitely many linear
evaluation features. These features are injective on every nonpositive
column subspace: a vector in their kernel has zero positive energy, annihilates
the completed form, and then vanishes by nondegeneracy of the column pairing.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- A zero-energy vector annihilates a positive Hermitian form. -/
private theorem sesq_pairing_zero_of_diag {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B : V → V →ₗ[ℂ] ℂ) (hh : ∀ v w, B v w = conj (B w v))
    (hp : ∀ v, 0 ≤ (B v v).re) {v : V} (hv : B v v = 0) (w : V) : B v w = 0 := by
  have hadd (x y z : V) : B (x + y) z = B x z + B y z := by
    rw [hh, map_add, map_add, ← hh x z, ← hh y z]
  have hsmul (c : ℂ) (x y : V) : B (c • x) y = conj c * B x y := by
    rw [hh, map_smul, smul_eq_mul, map_mul, ← hh x y]
  have hre (z : V) : (B v z).re = 0 := by
    have hcs := symmBilin_sq_le (S := fun x y => (B x y).re)
      (comb := fun t x y => x + (t : ℂ) • y) (fun t x y => by
        simp only [hadd, hsmul, map_add, map_smul, smul_eq_mul,
          Complex.conj_ofReal]
        rw [hh y x]
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.conj_re, zero_mul, sub_zero]
        ring) hp v z
    rw [hv, Complex.zero_re, zero_mul] at hcs
    nlinarith only [hcs, sq_nonneg (B v z).re]
  apply Complex.ext
  · exact hre w
  · have hz := hre (I • w)
    simpa only [map_smul, smul_eq_mul, Complex.mul_re, I_re, I_im,
      zero_mul, one_mul, zero_sub, neg_eq_zero, Complex.zero_im] using hz

variable {G : Type*} [Group G]

private def columnFeature (k : G → ℂ) {n m : ℕ} (x₀ : Fin n → G)
    (w : Fin m → Fin n → ℂ) (i : Fin m) : kernelColumnSpan k →ₗ[ℂ] ℂ where
  toFun v := ∑ b, w i b * (v : G → ℂ) (x₀ b)
  map_add' v z := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    exact sum_congr rfl fun b _ => by ring

private def columnCompletedPairing (k : G → ℂ) {n m : ℕ} (x₀ : Fin n → G)
    (w : Fin m → Fin n → ℂ) (v : kernelColumnSpan k) : kernelColumnSpan k →ₗ[ℂ] ℂ :=
  kernelColumnPairing k v + ∑ i, conj (columnFeature k x₀ w i v) • columnFeature k x₀ w i

private theorem columnCompletedPairing_apply (k : G → ℂ) {n m : ℕ} (x₀ : Fin n → G)
    (w : Fin m → Fin n → ℂ) (v z : kernelColumnSpan k) :
    columnCompletedPairing k x₀ w v z = kernelColumnPairing k v z +
      ∑ i, conj (columnFeature k x₀ w i v) * columnFeature k x₀ w i z := by
  simp only [columnCompletedPairing, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

private theorem columnCompletedPairing_conj {k : G → ℂ} (hk : IsHermKernel k)
    {n m : ℕ} (x₀ : Fin n → G) (w : Fin m → Fin n → ℂ) (v z : kernelColumnSpan k) :
    columnCompletedPairing k x₀ w v z = conj (columnCompletedPairing k x₀ w z v) := by
  simp only [columnCompletedPairing_apply, map_add, map_sum, map_mul, conj_conj]
  rw [kernelColumnPairing_conj_symm hk v z]
  congr 1
  exact sum_congr rfl fun i _ => mul_comm _ _

private theorem columnCompletedPairing_nonneg {k : G → ℂ} (hk : IsHermKernel k)
    {n₀ m : ℕ} (x₀ : Fin n₀ → G) (w : Fin m → Fin n₀ → ℂ)
    (hφ : ∀ (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ),
      0 ≤ hermQuad (gram k x) c +
        ∑ i, normSq (∑ a, c a * ∑ b, w i b * k ((x₀ b)⁻¹ * x a)))
    (v : kernelColumnSpan k) : 0 ≤ (columnCompletedPairing k x₀ w v v).re := by
  obtain ⟨n, x, c, rfl⟩ := exists_kernelColumnPoint_fin_sum k v
  have hB : (kernelColumnPairing k (∑ j, c j • kernelColumnPoint k (x j))
      (∑ j, c j • kernelColumnPoint k (x j))).re = hermQuad (gram k x) c := by
    rw [kernelColumnPairing_sum_points hk, hermQuad_gram]
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, kernelColumnPoint, kernelColumn, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hF (i : Fin m) : columnFeature k x₀ w i (∑ j, c j • kernelColumnPoint k (x j)) =
      ∑ a, c a * ∑ b, w i b * k ((x₀ b)⁻¹ * x a) := by
    rw [map_sum]
    apply sum_congr rfl
    intro a _
    rw [map_smul, smul_eq_mul]
    rfl
  have hn (z : ℂ) : (conj z * z).re = normSq z := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  simpa only [columnCompletedPairing_apply, Complex.add_re, Complex.re_sum, hn, hB, hF] using
    hφ n x c

/-- Every nonpositive column subspace has dimension at most the negative index. -/
theorem finite_nonpositive_column_subspace {k : G → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) (W : Submodule ℂ (kernelColumnSpan k))
    (hW : ∀ v ∈ W, (kernelColumnPairing k v v).re ≤ 0) :
    Module.Finite ℂ W ∧ Module.finrank ℂ W ≤ r := by
  classical
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.coe_ne_top r) hi)
  have hmr : m ≤ r := by
    rw [← hm] at hi
    exact_mod_cast hi
  obtain ⟨n₀, x₀, w, hφ⟩ := exists_pontryagin_decomposition hk hm.symm
  let L : W →ₗ[ℂ] (Fin m → ℂ) :=
    LinearMap.pi (fun i => (columnFeature k x₀ w i).comp W.subtype)
  have hzero (v : W) (hv : L v = 0) : v = 0 := by
    have hF (i : Fin m) : columnFeature k x₀ w i (v : kernelColumnSpan k) = 0 :=
      congrFun hv i
    have hCv : columnCompletedPairing k x₀ w (v : kernelColumnSpan k) v = 0 := by
      have hle : (columnCompletedPairing k x₀ w (v : kernelColumnSpan k) v).re ≤ 0 := by
        simpa only [columnCompletedPairing_apply, hF, map_zero, zero_mul,
          Finset.sum_const_zero, add_zero] using hW v v.property
      apply Complex.ext
      · exact le_antisymm hle (columnCompletedPairing_nonneg hk x₀ w hφ v)
      · have he := congrArg Complex.im (columnCompletedPairing_conj hk x₀ w v v)
        simp only [Complex.conj_im] at he
        change (columnCompletedPairing k x₀ w (v : kernelColumnSpan k) v).im = 0
        linarith only [he]
    have hB (z : kernelColumnSpan k) : kernelColumnPairing k z v = 0 := by
      have hz := sesq_pairing_zero_of_diag (columnCompletedPairing k x₀ w)
        (columnCompletedPairing_conj hk x₀ w) (columnCompletedPairing_nonneg hk x₀ w hφ) hCv z
      have hz' : columnCompletedPairing k x₀ w z (v : kernelColumnSpan k) = 0 := by
        rw [columnCompletedPairing_conj hk x₀ w z v, hz, map_zero]
      simpa only [columnCompletedPairing_apply, hF, mul_zero, Finset.sum_const_zero, add_zero]
        using hz'
    exact Subtype.ext (kernelColumnPairing_nondegenerate hk v hB)
  have hinj : Function.Injective L := by
    intro v z hvz
    have hz : L (v - z) = 0 := by
      funext i
      change (∑ b, w i b * ((v.val : G → ℂ) (x₀ b) -
        (z.val : G → ℂ) (x₀ b))) = 0
      rw [Finset.sum_congr rfl (fun b _ => mul_sub (w i b) _ _), Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun hvz i)
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have he := congrArg (fun a : W => (a.val : G → ℂ) g) (hzero (v - z) hz)
    change (v.val : G → ℂ) g - (z.val : G → ℂ) g = 0 at he
    exact sub_eq_zero.mp he
  letI : Module.Finite ℂ W := Module.Finite.of_injective L hinj
  refine ⟨inferInstance, ?_⟩
  have hdim : Module.finrank ℂ W ≤ m := by
    simpa using (LinearMap.finrank_le_finrank_of_injective hinj)
  exact hdim.trans hmr

/-- Every totally isotropic column subspace has dimension at most the negative index. -/
theorem finite_isotropic_column_subspace {k : G → ℂ} (hk : IsHermKernel k) {r : ℕ}
    (hi : negIndex k ≤ r) (W : Submodule ℂ (kernelColumnSpan k))
    (hW : ∀ v ∈ W, ∀ z ∈ W, kernelColumnPairing k v z = 0) :
    Module.Finite ℂ W ∧ Module.finrank ℂ W ≤ r := by
  apply finite_nonpositive_column_subspace hk hi W
  intro v hv
  rw [hW v hv v hv, Complex.zero_re]

#print axioms finite_nonpositive_column_subspace
#print axioms finite_isotropic_column_subspace
end GaloisForLFunctions.HeckeKreinToeplitz
