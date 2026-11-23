import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCoordinateAlgebras
import GaloisForLFunctions.HTGeometry.IntegralClosureLocalizationEquiv
import Mathlib.RingTheory.Localization.AsSubring

/-! Standard chart intersections invert the product of the corresponding
affine coordinates. Normalization commutes with this localization. -/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F]
  {d : ℕ} {x : Fin (d + 1) → F} {I : Finset (Fin (d + 1))} {i : Fin (d + 1)}

theorem rA_mono {J : Finset (Fin (d + 1))} (h : I ⊆ J) : rA k x I ≤ rA k x J := by
  refine Algebra.adjoin_le fun y hy => ?_
  obtain ⟨a, ha, b, rfl⟩ := hy
  exact Algebra.subset_adjoin ⟨a, h ha, b, rfl⟩

variable (k) in
/-- The product of the coordinate ratios being inverted on an intersection. -/
def chartDenominator (x : Fin (d + 1) → F) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)) : rA k x {i} :=
  ⟨∏ j ∈ I, x j / x i, Subalgebra.prod_mem _ fun j _ =>
    Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩⟩

theorem chartDenominator_ne_zero (h : IsPd k x) :
    (chartDenominator k x I i : F) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => div_ne_zero (h.ne j) (h.ne i)

private theorem inv_chartDenominator_mem :
    (chartDenominator k x I i : F)⁻¹ ∈ rA k x I := by
  rw [show (chartDenominator k x I i : F) = ∏ j ∈ I, x j / x i from rfl, ← Finset.prod_inv_distrib]
  refine Subalgebra.prod_mem _ fun j hj => ?_
  rw [inv_div]
  exact Algebra.subset_adjoin ⟨j, hj, i, rfl⟩

local notation "A" => rA k x (Singleton.singleton i)
local notation "C" => rA k x I
local notation "s" => chartDenominator k x I i

/-- The inclusion from one chart into a chart intersection as an algebra. -/
abbrev chartIntersectionAlgebra (hi : i ∈ I) : Algebra A C := by
  have hle : A ≤ C := rA_mono (Finset.singleton_subset_iff.mpr hi)
  exact (Subalgebra.inclusion hle).toRingHom.toAlgebra

theorem chartIntersection_tower (hi : i ∈ I) :
    letI := chartIntersectionAlgebra (k := k) (x := x) hi
    IsScalarTower A C F := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  exact .of_algebraMap_eq fun _ => rfl

private theorem mem_rA_iff_fraction (h : IsPd k x) (hi : i ∈ I) (y : F) :
    y ∈ C ↔ ∃ a : A, ∃ n : ℕ, y = (a : F) * ((s : F) ^ n)⁻¹ := by
  classical
  letI : IsFractionRing A F := h.isFractionRing_rA i
  let M := Submonoid.powers s
  have hM : M ≤ nonZeroDivisors A := by
    rintro _ ⟨n, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_of_ne_zero (fun e =>
      chartDenominator_ne_zero h (congrArg Subtype.val e))) n
  let L := Localization.subalgebra.ofField F M hM
  have hmem (z : F) : z ∈ L ↔
      ∃ (a q : A) (_ : q ∈ M), z = algebraMap A F a * (algebraMap A F q)⁻¹ := Iff.rfl
  have hs : (s : F)⁻¹ ∈ L := (hmem _).mpr
    ⟨1, s, ⟨1, pow_one _⟩, by change _ = 1 * _; rw [one_mul] <;> rfl⟩
  have hratio (j : Fin (d + 1)) : x j / x i ∈ L :=
    L.algebraMap_mem ⟨_, Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩⟩
  have hle : C ≤ L.restrictScalars k := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨l, hl, j, rfl⟩
    have hp : (∏ a ∈ I.erase l, x a / x i) ∈ L :=
      Subalgebra.prod_mem _ fun a _ => hratio a
    have hfac : x l / x i * (∏ a ∈ I.erase l, x a / x i) = (s : F) :=
      I.mul_prod_erase (fun a => x a / x i) hl
    have hinv : (x l / x i)⁻¹ ∈ L := by
      have he : (∏ a ∈ I.erase l, x a / x i) * (s : F)⁻¹ = (x l / x i)⁻¹ := by
        rw [← hfac, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀
          (Finset.prod_ne_zero_iff.mpr fun a _ => div_ne_zero (h.ne a) (h.ne i)), one_mul]
      rw [← he]
      exact L.mul_mem hp hs
    change x j / x l ∈ L
    rw [← div_div_div_cancel_right₀ (h.ne i) (x j) (x l), div_eq_mul_inv]
    exact L.mul_mem (hratio j) hinv
  constructor
  · intro hy
    obtain ⟨a, q, ⟨n, rfl⟩, e⟩ := (hmem y).mp (hle hy)
    exact ⟨a, n, e⟩
  · rintro ⟨a, n, rfl⟩
    rw [← inv_pow]
    exact (C).mul_mem (rA_mono (Finset.singleton_subset_iff.mpr hi) a.property)
      ((C).pow_mem inv_chartDenominator_mem n)

/-- Standard intersections are principal localizations of the affine
coordinate chart. -/
theorem chartIntersection_isLocalization (h : IsPd k x) (hi : i ∈ I) :
    letI := chartIntersectionAlgebra (k := k) (x := x) hi
    IsLocalization.Away s C := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  refine (isLocalization_iff (Submonoid.powers s) C).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨((s : F)⁻¹) ^ n, (C).pow_mem inv_chartDenominator_mem n⟩, ?_⟩
    apply Subtype.ext
    change (s : F) ^ n * ((s : F)⁻¹) ^ n = 1
    rw [← mul_pow, mul_inv_cancel₀ (chartDenominator_ne_zero h), one_pow]
  · intro c
    obtain ⟨a, n, hc⟩ := (mem_rA_iff_fraction h hi c).mp c.property
    refine ⟨⟨a, ⟨s ^ n, ⟨n, rfl⟩⟩⟩, Subtype.ext ?_⟩
    change (c : F) * (s : F) ^ n = (a : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (chartDenominator_ne_zero h)), mul_one]
  · intro a b hab
    exact ⟨1, congrArg (fun r : A => 1 * r)
      (Subtype.ext (congrArg (fun r : C => (r : F)) hab))⟩

end GlobalTheory.PD
