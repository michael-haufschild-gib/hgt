import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationIndexOfACycle
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures

/-!
# The Hecke orbit kernel of a zero configuration

For a zero configuration `Z` and a real test `f`, the **Hecke orbit kernel** is the function
`K(u) = W_Z(f, f(· − log u))` on the Hecke lattice `ℚ_{>0}` (`orbitKernel`). Its Gram matrix on a
family `u_a` is the Weil Gram matrix of the translates `f(· − log u_a)` (`gram_orbitKernel`), so the
kernel carries the Weil form of the whole rational Hecke orbit of `f`. It is Hermitian
(`isHermKernel_orbitKernel`).

**The arithmetic index law** (`negIndex_orbitKernel`). For a tempered configuration, the negative
index of `K` on `ℚ_{>0}` is the number of zeros right of the line that `f` sees. The same holds
after pulling back along any homomorphism into `ℚ_{>0}` whose scales are dense in `[0, ∞)`
(`negIndex_orbitKernel_comp`); for two distinct primes the sublattice `⟨p, q⟩` suffices
(`negIndex_orbitKernel_twoPrime`).

The tool behind the reduction to distinct shifts is `hermNegIndex_gram_le_image`: repeated points
in a family add no negative square, because the Gram form factors through the coefficient sums on
the fibres.
-/

open Complex Finset
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests zeroGram DenseShifts W_conj_symm
  denseShifts_ratHecke)
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri renaming translate → shiftTest
open GaloisForLFunctions.ArithmeticOrientationGeometry (seenRightZeros orientationIndex_law
  cx_scaleShift_eq_translate Wsummand_scaleShift)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-! ### Repeated points add no negative square -/

section Distinct

variable {G : Type*} [Group G] [DecidableEq G]

omit [Group G] in
/-- Regrouping a Toeplitz sum by the fibres of a family. -/
theorem sum_fibre_toeplitz {ι : Type*} [Fintype ι] (x : ι → G) (F : G → G → ℂ) (c : ι → ℂ) :
    ∑ g ∈ univ.image x, ∑ h ∈ univ.image x,
        conj (∑ a ∈ univ.filter (fun a => x a = g), c a) * F g h *
          ∑ b ∈ univ.filter (fun b => x b = h), c b =
      ∑ a, ∑ b, conj (c a) * F (x a) (x b) * c b := by
  have hm : ∀ a ∈ (univ : Finset ι), x a ∈ univ.image x := fun a _ => mem_image_of_mem _ (mem_univ a)
  have inner : ∀ g a, x a = g → ∑ h ∈ univ.image x,
      conj (c a) * F g h * ∑ b ∈ univ.filter (fun b => x b = h), c b =
        ∑ b, conj (c a) * F (x a) (x b) * c b := fun g a hg => by
    rw [← sum_fiberwise_of_maps_to hm]
    refine sum_congr rfl fun h _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun b hb => ?_
    rw [(mem_filter.mp hb).2, hg]
  rw [← sum_fiberwise_of_maps_to hm]
  refine sum_congr rfl fun g _ => ?_
  simp only [map_sum, sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun a ha => inner g a (mem_filter.mp ha).2

/-- **Repeated points add no negative square.** -/
theorem hermNegIndex_gram_le_image (k : G → ℂ) {ι : Type*} [Fintype ι] (x : ι → G) :
    hermNegIndex (gram k x) ≤ hermNegIndex (gram k fun g : univ.image x => (g : G)) := by
  set s := univ.image x
  let L : (ι → ℂ) →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun c g => ∑ a ∈ univ.filter (fun a => x a = g), c a
      map_add' := fun c d => funext fun g => by simp only [Pi.add_apply, sum_add_distrib]
      map_smul' := fun t c => funext fun g => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum] }
  refine hermNegIndex_le_of_hermQuad_eq _ _ L fun c => ?_
  rw [hermQuad_gram, hermQuad_gram]
  congr 1
  have := sum_fibre_toeplitz x (fun g h => k (g⁻¹ * h)) c
  rw [← this, ← s.sum_coe_sort]
  refine sum_congr rfl fun g _ => ?_
  rw [← s.sum_coe_sort]
  rfl

end Distinct

/-! ### Matrix reindexing -/

theorem hermQuad_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix κ κ ℂ)
    (e : ι ≃ κ) (c : ι → ℂ) : hermQuad (M.submatrix e e) c = hermQuad M (c ∘ e.symm) := by
  simp only [hermQuad, dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply,
    Function.comp_apply]
  congr 1
  rw [← e.sum_comp]
  refine sum_congr rfl fun a _ => ?_
  rw [← e.sum_comp]
  simp

/-! ### The Hecke orbit kernel -/

theorem scale_heckeLogScale_injective : Function.Injective (scale heckeLogScale) := fun u v h => by
  rw [scale_heckeLogScale, scale_heckeLogScale] at h
  have hu : (0 : ℝ) < ((u : ℚ) : ℝ) := by exact_mod_cast u.2
  have hv : (0 : ℝ) < ((v : ℚ) : ℝ) := by exact_mod_cast v.2
  exact Subtype.ext (Rat.cast_injective (Real.log_injOn_pos hu hv h))

/-- The scales of `ℚ_{>0}` are dense in `[0, ∞)`. -/
theorem denseShifts_range_scale : DenseShifts (Set.range (scale heckeLogScale)) := fun v hv ε hε => by
  obtain ⟨d, ⟨r, hr0, rfl⟩, hd⟩ := denseShifts_ratHecke v hv ε hε
  exact ⟨_, ⟨⟨r, hr0⟩, rfl⟩, hd⟩

/-- The Hecke orbit kernel `K(u) = W(f, f(· − log u))`. -/
def orbitKernel (Z : ZeroConfig) (f : ℝ → ℝ) : HeckeLattice → ℂ :=
  fun u => Z.W (cx f) (shiftTest (scale heckeLogScale u) (cx f))

/-- Both sides of the orbit kernel as one exponential sum over the zeros. -/
theorem W_shiftTest_shiftTest (Z : ZeroConfig) (f : ℝ → ℝ) (s t : ℝ) :
    Z.W (shiftTest s (cx f)) (shiftTest t (cx f)) =
      ∑' ρ : Z.carrier, cexp ((s - t) * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx f) ρ := by
  rw [ZeroConfig.W]
  refine tsum_congr fun ρ => ?_
  rw [← cx_scaleShift_eq_translate, ← cx_scaleShift_eq_translate, Wsummand_scaleShift]

theorem orbitKernel_eq (Z : ZeroConfig) (f : ℝ → ℝ) (u : HeckeLattice) :
    orbitKernel Z f u = Z.W (shiftTest 0 (cx f)) (shiftTest (scale heckeLogScale u) (cx f)) := by
  rw [orbitKernel, show shiftTest 0 (cx f) = cx f from funext fun v => by
    simp [ArithmeticCastelnuovoSeveri.translate]]

/-- **The Gram matrix of the orbit kernel is the Weil Gram matrix of the translates.** -/
theorem gram_orbitKernel (Z : ZeroConfig) (f : ℝ → ℝ) {ι : Type*} (x : ι → HeckeLattice) :
    gram (orbitKernel Z f) x = zeroGram Z fun a => shiftTest (scale heckeLogScale (x a)) (cx f) := by
  ext a b
  simp only [gram, zeroGram]
  rw [orbitKernel_eq, W_shiftTest_shiftTest, W_shiftTest_shiftTest, scale_mul, scale_inv]
  refine tsum_congr fun ρ => ?_
  congr 2
  push_cast
  ring

/-- The orbit kernel is Hermitian. -/
theorem isHermKernel_orbitKernel (Z : ZeroConfig) (f : ℝ → ℝ) : IsHermKernel (orbitKernel Z f) :=
  fun u => by
    rw [orbitKernel_eq, orbitKernel_eq, W_conj_symm, W_shiftTest_shiftTest,
      W_shiftTest_shiftTest, scale_inv]
    refine tsum_congr fun ρ => ?_
    congr 2
    push_cast
    ring

/-- **The arithmetic index law on `ℚ_{>0}`.** The negative index of the Hecke orbit kernel of a
real test on a tempered configuration is the number of zeros right of the line it sees. -/
theorem negIndex_orbitKernel_le (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : negIndex (orbitKernel Z f) ≤ (seenRightZeros Z f).encard := by
  classical
  rw [negIndex_le_iff]
  intro n x
  refine (Nat.cast_le.mpr (hermNegIndex_gram_le_image _ x)).trans ?_
  set s := univ.image x
  set S : Finset ℝ := s.image (scale heckeLogScale)
  have hSD : (S : Set ℝ) ⊆ Set.range (scale heckeLogScale) := fun t ht => by
    obtain ⟨u, -, rfl⟩ := mem_image.mp ht
    exact ⟨u, rfl⟩
  let e : s ≃ S := Equiv.ofBijective (fun g => ⟨scale heckeLogScale g, mem_image_of_mem _ g.2⟩)
    ⟨fun g g' h => Subtype.ext (scale_heckeLogScale_injective (congrArg Subtype.val h)),
      fun t => by
        obtain ⟨u, hu, ht⟩ := mem_image.mp t.2
        exact ⟨⟨u, hu⟩, Subtype.ext ht⟩⟩
  have hgram : gram (orbitKernel Z f) (fun g : s => (g : HeckeLattice)) =
      (zeroGram Z fun t : S => shiftTest t (cx f)).submatrix e e := by
    rw [gram_orbitKernel]; rfl
  have hle : hermNegIndex (gram (orbitKernel Z f) fun g : s => (g : HeckeLattice)) ≤
      hermNegIndex (zeroGram Z fun t : S => shiftTest t (cx f)) := by
    rw [hgram]
    exact hermNegIndex_le_of_hermQuad_eq _ _ (LinearMap.funLeft ℂ ℂ e.symm) fun c => by
      rw [hermQuad_submatrix_equiv]
      rfl
  exact (orientationIndex_law Z hZ hf denseShifts_range_scale _).mp ⟨S, hSD, hle⟩

/-- Any homomorphism into `ℚ_{>0}` with dense scales carries the whole index of the orbit kernel. -/
theorem le_negIndex_orbitKernel_comp (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {K : Type*} [Group K] (φ : K →* HeckeLattice)
    (hD : DenseShifts (Set.range fun h => scale heckeLogScale (φ h))) :
    (seenRightZeros Z f).encard ≤ negIndex (orbitKernel Z f ∘ φ) := by
  refine ENat.forall_natCast_le_iff_le.mp fun m hm => ?_
  obtain ⟨S, hSD, hle⟩ := (orientationIndex_law Z hZ hf hD m).mpr hm
  choose y hy using fun t : S => hSD t.2
  have hgram : gram (orbitKernel Z f ∘ φ) y = zeroGram Z fun t : S => shiftTest t (cx f) := by
    have : gram (orbitKernel Z f ∘ φ) y = gram (orbitKernel Z f) (φ ∘ y) := by
      ext a b; simp [gram, map_mul, map_inv]
    rw [this, gram_orbitKernel]
    ext a b
    simp only [zeroGram, Function.comp_apply, hy]
  exact (Nat.cast_le.mpr (hgram ▸ hle)).trans (hermNegIndex_gram_le_negIndex _ y)

/-- **The arithmetic index law.** -/
theorem negIndex_orbitKernel (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) : negIndex (orbitKernel Z f) = (seenRightZeros Z f).encard :=
  le_antisymm (negIndex_orbitKernel_le Z hZ hf)
    (le_negIndex_orbitKernel_comp Z hZ hf (MonoidHom.id _) denseShifts_range_scale)

/-- The same index on every sublattice with dense scales. -/
theorem negIndex_orbitKernel_comp (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {K : Type*} [Group K] (φ : K →* HeckeLattice)
    (hD : DenseShifts (Set.range fun h => scale heckeLogScale (φ h))) :
    negIndex (orbitKernel Z f ∘ φ) = (seenRightZeros Z f).encard :=
  le_antisymm ((negIndex_comp_le _ φ).trans (negIndex_orbitKernel_le Z hZ hf))
    (le_negIndex_orbitKernel_comp Z hZ hf φ hD)

/-- The scales of the two-prime sublattice are dense. -/
theorem denseShifts_twoPrimeLattice {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    DenseShifts (Set.range fun h : twoPrimeLattice hp hq =>
      scale heckeLogScale ((twoPrimeLattice hp hq).subtype h)) := fun v _ ε hε => by
  have hdense : Dense (AddSubgroup.closure {Real.log p, Real.log q} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (RHTower.irrational_log_ratio hq hp hpq.symm)
  obtain ⟨d, hd, hdv⟩ := Metric.dense_iff.mp hdense v ε hε
  obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hdv
  refine ⟨d, ⟨⟨primeElt hp ^ m * primeElt hq ^ n, Subgroup.mem_closure_pair.mpr ⟨m, n, rfl⟩⟩, ?_⟩,
    by rw [Metric.mem_ball, Real.dist_eq] at hd; exact hd⟩
  change scale heckeLogScale (primeElt hp ^ m * primeElt hq ^ n) = d
  rw [scale_mul, scale_zpow, scale_zpow, scale_primeElt, scale_primeElt, ← hmn, zsmul_eq_mul,
    zsmul_eq_mul]

/-- **Two primes carry the whole index of the orbit kernel.** -/
theorem negIndex_orbitKernel_twoPrime (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    negIndex (orbitKernel Z f ∘ (twoPrimeLattice hp hq).subtype) = (seenRightZeros Z f).encard :=
  negIndex_orbitKernel_comp Z hZ hf _ (denseShifts_twoPrimeLattice hp hq hpq)

end GaloisForLFunctions.HeckeKreinToeplitz
