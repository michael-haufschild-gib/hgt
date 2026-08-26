import GaloisForLFunctions.RHTower.PrimeUHFFiniteStageUnitaryDensity
import GaloisForLFunctions.HTGeometry.PolarTransportUnitary
import GaloisForLFunctions.HTGeometry.CfcNormBound
import GaloisForLFunctions.HTGeometry.InverseSqrtPerturbation
import GaloisForLFunctions.HTGeometry.UnitaryLocalLogNullhomotopy
import GaloisForLFunctions.HTGeometry.LoopOpenCoverDecomposition
import Mathlib.Topology.PartitionOfUnity

/-!
# Relative finite-stage approximation in prime UHF algebras

Continuous maps into the completed prime UHF algebra can be approximated, relative to a closed
zero boundary, by one literal finite matrix stage.  Quantitative polar correction upgrades this
to finite-stage unitary paths and endpoint-fixed nullhomotopies.
-/

open Filter Topology
open scoped ContinuousFunctionalCalculus Ring
open GaloisForLFunctions.HTGeometry

namespace PrimeQuasiLocalCharge

noncomputable section

def cstarInvSqrtNearOne {A : Type*} [CStarAlgebra A] (a : A) : A :=
  cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a

theorem cstarSpectrum_subset_nearOneWindow
    {A : Type*} [CStarAlgebra A] [NormOneClass A]
    {a : A} (hnorm : ‖a - 1‖ ≤ 1 / 2) :
    spectrum ℝ a ⊆ GaloisForLFunctions.HTGeometry.nearOneWindow := by
  intro t ht
  have hmapone : (algebraMap ℝ A) 1 = 1 := map_one _
  have hsub : t - 1 ∈ spectrum ℝ (a - 1) := by
    rw [← hmapone, ← spectrum.sub_singleton_eq]
    exact ⟨t, ht, 1, rfl, rfl⟩
  have hball := spectrum.subset_closedBall_norm (𝕜 := ℝ) (a - 1) hsub
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
  have habs : |t - 1| ≤ 1 / 2 := le_trans hball hnorm
  rw [abs_le] at habs
  constructor <;> [linarith [habs.1]; linarith [habs.2]]

theorem isSelfAdjoint_cstarInvSqrtNearOne
    {A : Type*} [CStarAlgebra A] (a : A) :
    IsSelfAdjoint (cstarInvSqrtNearOne a) := by
  rw [cstarInvSqrtNearOne]
  exact cfc_predicate (R := ℝ) _ a

theorem cstarInvSqrtNearOne_mul_mul
    {A : Type*} [CStarAlgebra A] [NormOneClass A]
    {a : A} (ha : IsSelfAdjoint a) (hnorm : ‖a - 1‖ ≤ 1 / 2) :
    cstarInvSqrtNearOne a * a * cstarInvSqrtNearOne a = 1 := by
  have hspec := cstarSpectrum_subset_nearOneWindow hnorm
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (spectrum ℝ a) :=
    GaloisForLFunctions.HTGeometry.continuousOn_invSqrtFun.mono hspec
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ a) := continuousOn_id
  have ha' : a = cfc (fun t : ℝ => t) a := (cfc_id ℝ a).symm
  have h1 : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a * cfc (fun t : ℝ => t) a
      = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t) a :=
    (cfc_mul _ _ a hcont hid).symm
  have h2 : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t) a
      * cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a
      = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2)) a :=
    (cfc_mul _ _ a (hcont.mul hid) hcont).symm
  calc
    cstarInvSqrtNearOne a * a * cstarInvSqrtNearOne a =
        cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a * cfc (fun t : ℝ => t) a *
          cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a := by
            rw [cstarInvSqrtNearOne, ← ha']
    _ = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2)) a := by
      rw [h1, h2]
    _ = cfc (fun _ : ℝ => (1 : ℝ)) a := by
      refine cfc_congr ?_
      intro t ht
      have hpos : 0 < t :=
        GaloisForLFunctions.HTGeometry.pos_of_mem_nearOneWindow (hspec ht)
      have hsum : t ^ (-(1 : ℝ) / 2 + 1 + -(1 : ℝ) / 2) =
          t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2) := by
        rw [Real.rpow_add hpos, Real.rpow_add hpos, Real.rpow_one]
      have hzero : (-(1 : ℝ) / 2 + 1 + -(1 : ℝ) / 2) = 0 := by norm_num
      rw [hzero, Real.rpow_zero] at hsum
      exact hsum.symm
    _ = 1 := cfc_one ℝ a

theorem cstarInvSqrtNearOne_one
    {A : Type*} [CStarAlgebra A] [Nontrivial A] :
    cstarInvSqrtNearOne (1 : A) = 1 := by
  rw [cstarInvSqrtNearOne]
  have hcg : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (1 : A) =
      cfc (fun _ : ℝ => (1 : ℝ)) (1 : A) := by
    refine cfc_congr ?_
    intro t ht
    rw [spectrum.one_eq, Set.mem_singleton_iff] at ht
    rw [ht]
    norm_num
  rw [hcg]
  exact cfc_one ℝ _

theorem norm_cstarInvSqrtNearOne_sub_one_le
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    {a : A} (ha : IsSelfAdjoint a) (hnorm : ‖a - 1‖ ≤ 1 / 2) :
    ‖cstarInvSqrtNearOne a - 1‖ ≤ ‖a - 1‖ := by
  have hspec := cstarSpectrum_subset_nearOneWindow hnorm
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (spectrum ℝ a) :=
    GaloisForLFunctions.HTGeometry.continuousOn_invSqrtFun.mono hspec
  have hconst : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ a) := continuousOn_const
  have heq : cstarInvSqrtNearOne a - 1 =
      cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) - 1) a := by
    change cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) a - 1 = _
    rw [← cfc_one ℝ a ha]
    exact (cfc_sub _ _ a hcont hconst).symm
  rw [heq]
  apply GaloisForLFunctions.HTGeometry.norm_cfc_le_of_forall_le
    (fun t : ℝ => t ^ (-(1 : ℝ) / 2) - 1) a (hcont.sub hconst) ha
  intro t ht
  have htpos : 0 < t :=
    GaloisForLFunctions.HTGeometry.pos_of_mem_nearOneWindow (hspec ht)
  have hrpow : t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul htpos.le]
    norm_num
  have hshift : t - 1 ∈ spectrum ℝ (a - 1) := by
    have hmapone : (algebraMap ℝ A) 1 = 1 := map_one _
    rw [← hmapone, ← spectrum.sub_singleton_eq]
    exact ⟨t, ht, 1, rfl, rfl⟩
  have hshiftNorm := spectrum.norm_le_norm_of_mem hshift
  have hhalf : |1 - t| ≤ 1 / 2 := by
    have hw := hspec ht
    rw [abs_le]
    constructor <;> linarith [hw.1, hw.2]
  have hscalar :=
    GaloisForLFunctions.HTGeometry.abs_inv_sqrt_one_sub_sub_one_le hhalf
  have hscalar' : |(Real.sqrt t)⁻¹ - 1| ≤ |1 - t| := by
    simpa [one_div] using hscalar
  rw [hrpow]
  change |(Real.sqrt t)⁻¹ - 1| ≤ ‖a - 1‖
  refine hscalar'.trans ?_
  simpa [Real.norm_eq_abs, abs_sub_comm] using hshiftNorm

def cstarPolarNearOne {A : Type*} [CStarAlgebra A] (a : A) : A :=
  a * cstarInvSqrtNearOne (star a * a)

theorem cstarPolarNearOne_unitary
    {A : Type*} [CStarAlgebra A] [Nontrivial A] (u : unitary A) :
    cstarPolarNearOne (u : A) = (u : A) := by
  rw [cstarPolarNearOne, u.property.1, cstarInvSqrtNearOne_one, mul_one]

theorem isSelfAdjoint_star_mul_self {A : Type*} [CStarAlgebra A] (a : A) :
    IsSelfAdjoint (star a * a) := by
  unfold IsSelfAdjoint
  simp

theorem continuous_cstarPolarNearOne_comp
    {A X : Type*} [CStarAlgebra A] [NormOneClass A]
    [Nontrivial A] [TopologicalSpace X] {f : X → A} (hf : Continuous f)
    (hsmall : ∀ x, ‖star (f x) * f x - 1‖ ≤ 1 / 2) :
    Continuous (fun x => cstarPolarNearOne (f x)) := by
  have hgram : Continuous (fun x => star (f x) * f x) := by fun_prop
  have hcfc := continuousOn_cfc (𝕜 := ℝ) A
    GaloisForLFunctions.HTGeometry.isCompact_nearOneWindow
    (fun t : ℝ => t ^ (-(1 : ℝ) / 2))
    GaloisForLFunctions.HTGeometry.continuousOn_invSqrtFun
  have hmem : ∀ x, star (f x) * f x ∈
      {a : A | IsSelfAdjoint a ∧
        spectrum ℝ a ⊆ GaloisForLFunctions.HTGeometry.nearOneWindow} := by
    intro x
    exact ⟨isSelfAdjoint_star_mul_self (f x),
      cstarSpectrum_subset_nearOneWindow (hsmall x)⟩
  have hinv : Continuous (fun x =>
      cstarInvSqrtNearOne (star (f x) * f x)) := by
    exact hcfc.comp_continuous hgram hmem
  exact hf.mul hinv

theorem cstarPolarNearOne_star_mul_self
    {A : Type*} [CStarAlgebra A] [NormOneClass A]
    {a : A} (hnorm : ‖star a * a - 1‖ ≤ 1 / 2) :
    star (cstarPolarNearOne a) * cstarPolarNearOne a = 1 := by
  set S := cstarInvSqrtNearOne (star a * a) with hS
  have hSsa : IsSelfAdjoint S := isSelfAdjoint_cstarInvSqrtNearOne _
  have hkey : S * (star a * a) * S = 1 :=
    cstarInvSqrtNearOne_mul_mul (isSelfAdjoint_star_mul_self a) hnorm
  rw [cstarPolarNearOne, ← hS, star_mul, hSsa.star_eq]
  calc
    S * star a * (a * S) = S * (star a * a) * S := by noncomm_ring
    _ = 1 := hkey

theorem norm_cstarPolarNearOne_sub_self_le
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    {a : A} (hnorm : ‖star a * a - 1‖ ≤ 1 / 2) :
    ‖cstarPolarNearOne a - a‖ ≤ ‖a‖ * ‖star a * a - 1‖ := by
  have hfactor : cstarPolarNearOne a - a =
      a * (cstarInvSqrtNearOne (star a * a) - 1) := by
    rw [cstarPolarNearOne, mul_sub, mul_one]
  rw [hfactor]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
    (norm_cstarInvSqrtNearOne_sub_one_le (isSelfAdjoint_star_mul_self a) hnorm)
    (norm_nonneg _))

theorem norm_cstarPolarNearOne_sub_unitary_lt_one
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (a : A) (u : unitary A)
    (hsmall : ‖a - (u : A)‖ ≤ 1 / 16) :
    ‖cstarPolarNearOne a - (u : A)‖ < 1 := by
  let δ := ‖a - (u : A)‖
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδsmall : δ ≤ 1 / 16 := hsmall
  have hgram : ‖star a * a - 1‖ ≤ δ * (2 + δ) :=
    norm_star_mul_self_sub_one_le_of_unitary a u
  have hgramHalf : ‖star a * a - 1‖ ≤ 1 / 2 := by
    have hnorm0 : 0 ≤ ‖star a * a - 1‖ := norm_nonneg _
    nlinarith
  have haNorm : ‖a‖ ≤ 1 + δ := by
    have htri := norm_add_le (a - (u : A)) (u : A)
    rw [sub_add_cancel, norm_unitary_coe_eq_one] at htri
    simpa [δ, add_comm] using htri
  have hcorr : ‖cstarPolarNearOne a - a‖ ≤ (1 + δ) * (δ * (2 + δ)) := by
    calc
      ‖cstarPolarNearOne a - a‖ ≤ ‖a‖ * ‖star a * a - 1‖ :=
        norm_cstarPolarNearOne_sub_self_le hgramHalf
      _ ≤ (1 + δ) * (δ * (2 + δ)) :=
        mul_le_mul haNorm hgram (norm_nonneg _) (by positivity)
  have hcorrLinear : ‖cstarPolarNearOne a - a‖ ≤ 6 * δ := by
    refine hcorr.trans ?_
    have hleft : 1 + δ ≤ 2 := by linarith
    have hright : 2 + δ ≤ 3 := by linarith
    calc
      (1 + δ) * (δ * (2 + δ)) ≤ 2 * (δ * (2 + δ)) :=
        mul_le_mul_of_nonneg_right hleft (by positivity)
      _ ≤ 2 * (δ * 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hright hδ0) (by norm_num)
      _ = 6 * δ := by ring
  have htri := norm_add_le (cstarPolarNearOne a - a) (a - (u : A))
  have hsplit : cstarPolarNearOne a - (u : A) =
      (cstarPolarNearOne a - a) + (a - (u : A)) := by abel
  rw [← hsplit] at htri
  have hδeq : ‖a - (u : A)‖ = δ := rfl
  rw [hδeq] at htri
  nlinarith

theorem norm_cstarPolarNearOne_sub_unitary_le_seven_mul
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (a : A) (u : unitary A)
    (hsmall : ‖a - (u : A)‖ ≤ 1 / 16) :
    ‖cstarPolarNearOne a - (u : A)‖ ≤ 7 * ‖a - (u : A)‖ := by
  let δ := ‖a - (u : A)‖
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδsmall : δ ≤ 1 / 16 := hsmall
  have hgram : ‖star a * a - 1‖ ≤ δ * (2 + δ) :=
    norm_star_mul_self_sub_one_le_of_unitary a u
  have hgramHalf : ‖star a * a - 1‖ ≤ 1 / 2 := by
    nlinarith [norm_nonneg (star a * a - 1)]
  have haNorm : ‖a‖ ≤ 1 + δ := by
    have htri := norm_add_le (a - (u : A)) (u : A)
    rw [sub_add_cancel, norm_unitary_coe_eq_one] at htri
    simpa [δ, add_comm] using htri
  have hcorr : ‖cstarPolarNearOne a - a‖ ≤ 6 * δ := by
    calc
      ‖cstarPolarNearOne a - a‖ ≤ ‖a‖ * ‖star a * a - 1‖ :=
        norm_cstarPolarNearOne_sub_self_le hgramHalf
      _ ≤ (1 + δ) * (δ * (2 + δ)) :=
        mul_le_mul haNorm hgram (norm_nonneg _) (by positivity)
      _ ≤ 2 * (δ * 3) := by
        exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left (by linarith) hδ0)
          (by positivity) (by norm_num)
      _ = 6 * δ := by ring
  have htri := norm_add_le (cstarPolarNearOne a - a) (a - (u : A))
  have hsplit : cstarPolarNearOne a - (u : A) =
      (cstarPolarNearOne a - a) + (a - (u : A)) := by abel
  rw [← hsplit] at htri
  have hδeq : ‖a - (u : A)‖ = δ := rfl
  rw [hδeq] at htri ⊢
  linarith

def cstarPolarUnitaryNear
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (a : A) (u : unitary A)
    (hsmall : ‖a - (u : A)‖ ≤ 1 / 16) : unitary A := by
  let P := cstarPolarNearOne a
  let δ := ‖a - (u : A)‖
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hδsmall : δ ≤ 1 / 16 := hsmall
  have hgram : ‖star a * a - 1‖ ≤ δ * (2 + δ) :=
    norm_star_mul_self_sub_one_le_of_unitary a u
  have hgramHalf : ‖star a * a - 1‖ ≤ 1 / 2 := by
    have hnorm0 : 0 ≤ ‖star a * a - 1‖ := norm_nonneg _
    nlinarith
  have hiso : star P * P = 1 := cstarPolarNearOne_star_mul_self hgramHalf
  have hPnear : ‖P - (u : A)‖ < 1 :=
    norm_cstarPolarNearOne_sub_unitary_lt_one a u hsmall
  have hrelNorm : ‖star (u : A) * P - 1‖ < 1 := by
    have hfactor : star (u : A) * P - 1 =
        star (u : A) * (P - (u : A)) := by
      rw [mul_sub, u.property.1]
    rw [hfactor]
    calc
      ‖star (u : A) * (P - (u : A))‖ ≤
          ‖star (u : A)‖ * ‖P - (u : A)‖ := norm_mul_le _ _
      _ = ‖P - (u : A)‖ := by
        rw [norm_star, norm_unitary_coe_eq_one, one_mul]
      _ < 1 := hPnear
  have hrel : IsUnit (star (u : A) * P) := by
    have h := isUnit_one_sub_of_norm_lt_one
      (x := 1 - star (u : A) * P) (by
        rw [← neg_sub, norm_neg]
        exact hrelNorm)
    simpa using h
  have hu : IsUnit (u : A) := by
    exact ⟨⟨(u : A), star (u : A), u.property.2, u.property.1⟩, rfl⟩
  have hPunit : IsUnit P := by
    have h := hu.mul hrel
    rw [← mul_assoc, u.property.2, one_mul] at h
    exact h
  refine ⟨P, hiso, ?_⟩
  apply hPunit.mul_right_cancel
  calc
    (P * star P) * P = P * (star P * P) := by rw [mul_assoc]
    _ = P := by rw [hiso, mul_one]
    _ = 1 * P := by rw [one_mul]

def cstarAffineSegment {A : Type*} [CStarAlgebra A]
    (u v : A) (t : unitInterval) : A :=
  u + (t : ℝ) • (v - u)

theorem continuous_cstarAffineSegment
    {A : Type*} [CStarAlgebra A] (u v : A) :
    Continuous (cstarAffineSegment u v) := by
  unfold cstarAffineSegment
  fun_prop

theorem cstarAffineSegment_self
    {A : Type*} [CStarAlgebra A] (u : A) (t : unitInterval) :
    cstarAffineSegment u u t = u := by
  rw [cstarAffineSegment, sub_self, smul_zero, add_zero]

theorem norm_cstarAffineSegment_sub_left_le
    {A : Type*} [CStarAlgebra A] (u v : A) (t : unitInterval) :
    ‖cstarAffineSegment u v t - u‖ ≤ ‖v - u‖ := by
  rw [cstarAffineSegment, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg t.property.1]
  exact mul_le_of_le_one_left (norm_nonneg _) t.property.2

def cstarPolarSegment
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (u v : unitary A) (hclose : ‖(v : A) - (u : A)‖ ≤ 1 / 16) :
    Path u v := by
  have hnear : ∀ t, ‖cstarAffineSegment (u : A) (v : A) t - (u : A)‖ ≤ 1 / 16 :=
    fun t => (norm_cstarAffineSegment_sub_left_le _ _ t).trans hclose
  have hgram : ∀ t,
      ‖star (cstarAffineSegment (u : A) (v : A) t) *
          cstarAffineSegment (u : A) (v : A) t - 1‖ ≤ 1 / 2 := by
    intro t
    have h := norm_star_mul_self_sub_one_le_of_unitary
      (cstarAffineSegment (u : A) (v : A) t) u
    have hn := norm_nonneg
      (cstarAffineSegment (u : A) (v : A) t - (u : A))
    nlinarith [hnear t]
  let F : unitInterval → unitary A := fun t =>
    cstarPolarUnitaryNear (cstarAffineSegment (u : A) (v : A) t) u (hnear t)
  have hF : Continuous F := by
    apply continuous_induced_rng.mpr
    change Continuous (fun t => cstarPolarNearOne
      (cstarAffineSegment (u : A) (v : A) t))
    exact continuous_cstarPolarNearOne_comp
      (continuous_cstarAffineSegment _ _) hgram
  refine
    { toFun := F
      continuous_toFun := hF
      source' := ?_
      target' := ?_ }
  · apply Subtype.ext
    change cstarPolarNearOne (cstarAffineSegment (u : A) (v : A) 0) = (u : A)
    rw [cstarAffineSegment]
    simpa using cstarPolarNearOne_unitary u
  · apply Subtype.ext
    change cstarPolarNearOne (cstarAffineSegment (u : A) (v : A) 1) = (v : A)
    rw [cstarAffineSegment]
    simpa using cstarPolarNearOne_unitary v

theorem norm_cstarPolarSegment_sub_left_le
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    (u v : unitary A) (hclose : ‖(v : A) - (u : A)‖ ≤ 1 / 16)
    (t : unitInterval) :
    ‖((cstarPolarSegment u v hclose t : unitary A) : A) - (u : A)‖ ≤
        7 * ‖(v : A) - (u : A)‖ := by
  change ‖cstarPolarNearOne (cstarAffineSegment (u : A) (v : A) t) - (u : A)‖ ≤ _
  exact (norm_cstarPolarNearOne_sub_unitary_le_seven_mul _ u
    ((norm_cstarAffineSegment_sub_left_le _ _ t).trans hclose)).trans
      (mul_le_mul_of_nonneg_left
        (norm_cstarAffineSegment_sub_left_le _ _ t) (by norm_num))

def unitaryPathsHomotopyOfNormSubLtTwo
    {A : Type*} [CStarAlgebra A] [NormOneClass A] [Nontrivial A]
    {x₀ x₁ : unitary A} (p q : Path x₀ x₁)
    (hclose : ∀ t, ‖(q t : A) - (p t : A)‖ < 2) :
    p.Homotopy q := by
  let r : unitInterval → unitary A := fun t => star (p t) * q t
  have hrclose : ∀ t, ‖((r t : unitary A) : A) - 1‖ < 2 := by
    intro t
    have hfactor : ((r t : unitary A) : A) - 1 =
        star (p t : A) * ((q t : A) - (p t : A)) := by
      change star (p t : A) * (q t : A) - 1 = _
      rw [mul_sub, (p t).property.1]
    rw [hfactor]
    calc
      ‖star (p t : A) * ((q t : A) - (p t : A))‖ ≤
          ‖star (p t : A)‖ * ‖(q t : A) - (p t : A)‖ := norm_mul_le _ _
      _ = ‖(q t : A) - (p t : A)‖ := by
        rw [norm_star, norm_unitary_coe_eq_one, one_mul]
      _ < 2 := hclose t
  have hrcont : Continuous r := by
    unfold r
    fun_prop
  have harg : Continuous (fun t => Unitary.argSelfAdjoint (r t)) := by
    apply Unitary.continuousOn_argSelfAdjoint.comp_continuous hrcont
    intro t
    simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hrclose t
  have harg_one : Unitary.argSelfAdjoint (1 : unitary A) = 0 := by
    simpa using (argSelfAdjoint_expUnitary
      (x := (0 : selfAdjoint A)) (by simpa using Real.pi_pos))
  let Hmap : C(unitInterval × unitInterval, unitary A) :=
    ⟨fun st => p st.2 * selfAdjoint.expUnitary
        ((st.1 : ℝ) • Unitary.argSelfAdjoint (r st.2)), by
      apply Continuous.mul (p.continuous.comp continuous_snd)
        (selfAdjoint.continuous_expUnitary.comp
          ((continuous_subtype_val.comp continuous_fst).smul
            (harg.comp continuous_snd)))⟩
  refine
    { toContinuousMap := Hmap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    simp [Hmap]
  · intro t
    change p t * selfAdjoint.expUnitary
      ((1 : ℝ) • Unitary.argSelfAdjoint (r t)) = q t
    rw [one_smul, expUnitary_argSelfAdjoint (hrclose t)]
    apply Subtype.ext
    change (p t : A) * (star (p t : A) * (q t : A)) = (q t : A)
    rw [← mul_assoc, (p t).property.2, one_mul]
  · intro t x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hrzero : r 0 = 1 := by
        apply Subtype.ext
        change star (p 0 : A) * (q 0 : A) = 1
        rw [p.source, q.source]
        exact x₀.property.1
      simp [Hmap, hrzero, harg_one]
    · have hrone : r 1 = 1 := by
        apply Subtype.ext
        change star (p 1 : A) * (q 1 : A) = 1
        rw [p.target, q.target]
        exact x₁.property.1
      simp [Hmap, hrone, harg_one]

theorem matrixAFStageToAlgebraicLimit_transition
    (localDim : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    matrixAFStageToAlgebraicLimit localDim j
        (matrixAFStageTransition localDim i j hij A) =
      matrixAFStageToAlgebraicLimit localDim i A := by
  change (⟦⟨j, matrixAFStageTransition localDim i j hij A⟩⟧ :
      PrimeAFAlgebraicLimit localDim) = ⟦⟨i, A⟩⟧
  symm
  rw [DirectLimit.eq_of_le ⟨i, A⟩ j hij]

theorem matrixAFStageToUHF_transition
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (A : PrimeAFMatrixStageAlgebra localDim i) :
    matrixAFStageToUHF j (matrixAFStageTransition localDim i j hij A) =
      matrixAFStageToUHF i A := by
  exact congrArg UniformSpace.Completion.coe'
    (matrixAFStageToAlgebraicLimit_transition localDim hij A)

def matrixAFStageUnitaryTransition
    (localDim : ℕ → ℕ) {i j : ℕ} (hij : i ≤ j) :
    Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ →*
      Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim j)) ℂ where
  toFun U := ⟨matrixAFStageTransition localDim i j hij U, by
    rcases U.property with ⟨h₁, h₂⟩
    constructor
    · rw [← map_star, ← map_mul, h₁, map_one]
    · rw [← map_star, ← map_mul, h₂, map_one]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' U V := by
    apply Subtype.ext
    exact map_mul _ _ _

theorem matrixAFStageUnitaryToUHF_transition
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    {i j : ℕ} (hij : i ≤ j)
    (U : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim i)) ℂ) :
    matrixAFStageUnitaryToUHF j
        (matrixAFStageUnitaryTransition localDim hij U) =
      matrixAFStageUnitaryToUHF i U := by
  apply Subtype.ext
  exact matrixAFStageToUHF_transition (localDim := localDim) hij
    (U : PrimeAFMatrixStageAlgebra localDim i)

theorem continuous_matrixAFStageUnitaryTransition
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    {i j : ℕ} (hij : i ≤ j) :
    Continuous (matrixAFStageUnitaryTransition localDim hij) := by
  apply Continuous.subtype_mk
  have hiso : Isometry (fun U : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ =>
      matrixAFStageTransition localDim i j hij
        (U : PrimeAFMatrixStageAlgebra localDim i)) := by
    apply Isometry.of_dist_eq
    intro U V
    calc
      dist (matrixAFStageTransition localDim i j hij
          (U : PrimeAFMatrixStageAlgebra localDim i))
          (matrixAFStageTransition localDim i j hij
            (V : PrimeAFMatrixStageAlgebra localDim i)) =
          ‖matrixAFStageTransition localDim i j hij
            (U : PrimeAFMatrixStageAlgebra localDim i) -
            matrixAFStageTransition localDim i j hij
              (V : PrimeAFMatrixStageAlgebra localDim i)‖ := dist_eq_norm _ _
      _ = ‖(U : PrimeAFMatrixStageAlgebra localDim i) - V‖ := by
        rw [← map_sub, norm_matrixAFStageTransition hd hij]
      _ = dist U V := by rw [Subtype.dist_eq, dist_eq_norm]
  exact hiso.continuous

theorem continuous_matrixAFStageTransition
    {localDim : ℕ → ℕ} (hd : ∀ k, 0 < localDim k)
    {i j : ℕ} (hij : i ≤ j) :
    Continuous (matrixAFStageTransition localDim i j hij) := by
  apply Isometry.continuous
  apply Isometry.of_dist_eq
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    norm_matrixAFStageTransition hd hij]

theorem exists_matrixAFStage_norm_sub_lt
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (a : PrimeUHFAlgebra localDim) {ε : ℝ} (hε : 0 < ε) :
    ∃ (i : ℕ) (A : PrimeAFMatrixStageAlgebra localDim i),
      ‖matrixAFStageToUHF i A - a‖ < ε := by
  obtain ⟨q, hq⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt a hε
  have hq' : ‖(q : PrimeUHFAlgebra localDim) - a‖ < ε := by
    rw [← dist_eq_norm]
    simpa [dist_comm] using hq
  induction q using DirectLimit.induction with
  | ih i A =>
      exact ⟨i, A, hq'⟩

set_option maxHeartbeats 800000 in
theorem exists_commonStageContinuousMap_relative_approximation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (r : X → PrimeUHFAlgebra localDim) (hr : Continuous r)
    (bd : Set X) (hbd : IsClosed bd) (hrbd : ∀ x ∈ bd, r x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (g : X → PrimeAFMatrixStageAlgebra localDim N),
      Continuous g ∧ (∀ x ∈ bd, g x = 0) ∧
        ∀ x, ‖matrixAFStageToUHF N (g x) - r x‖ ≤ 2 * ε := by
  let U : Option X → Set X
    | none => r ⁻¹' Metric.ball 0 ε
    | some y => bdᶜ ∩ r ⁻¹' Metric.ball (r y) ε
  have hUOpen : ∀ j, IsOpen (U j) := by
    intro j
    cases j with
    | none => exact Metric.isOpen_ball.preimage hr
    | some y => exact hbd.isOpen_compl.inter (Metric.isOpen_ball.preimage hr)
  have hUCover : Set.univ ⊆ ⋃ j, U j := by
    intro x _
    by_cases hx : x ∈ bd
    · apply Set.mem_iUnion.mpr
      refine ⟨none, ?_⟩
      change dist (r x) 0 < ε
      rw [hrbd x hx, dist_self]
      exact hε
    · apply Set.mem_iUnion.mpr
      refine ⟨some x, ?_⟩
      exact ⟨hx, by simpa using hε⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUOpen hUCover
  let ι := {j : Option X // j ∈ S}
  let V : ι → Set X := fun j => U j
  letI : Fintype ι := FinsetCoe.fintype S
  have hVOpen : ∀ j, IsOpen (V j) := fun j => hUOpen j
  have hVCover : Set.univ ⊆ ⋃ j, V j := by
    intro x _
    have hx := hS (Set.mem_univ x)
    rcases Set.mem_iUnion.mp hx with ⟨j, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hjS, hxU⟩
    exact Set.mem_iUnion.mpr ⟨⟨j, hjS⟩, hxU⟩
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate
    (s := (Set.univ : Set X)) isClosed_univ V hVOpen hVCover
  let centerValue : ι → PrimeUHFAlgebra localDim := fun j =>
    match j.1 with
    | none => 0
    | some y => r y
  have happ : ∀ j : ι, ∃ (i : ℕ) (A : PrimeAFMatrixStageAlgebra localDim i),
      ‖matrixAFStageToUHF i A - centerValue j‖ < ε ∧
        (j.1 = none → A = 0) := by
    intro j
    cases hj : j.1 with
    | none =>
        refine ⟨0, 0, ?_, fun _ => rfl⟩
        simp [centerValue, hj, hε]
    | some y =>
        obtain ⟨i, A, hA⟩ := exists_matrixAFStage_norm_sub_lt (r y) hε
        exact ⟨i, A, by simpa [centerValue, hj] using hA, fun h => by cases h⟩
  choose i A hA hAzero using happ
  let N := ∑ j : ι, i j
  have hiN : ∀ j, i j ≤ N := by
    intro j
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (i k)) (Finset.mem_univ j)
  let B : ι → PrimeAFMatrixStageAlgebra localDim N := fun j =>
    matrixAFStageTransition localDim (i j) N (hiN j) (A j)
  have hBmap : ∀ j, matrixAFStageToUHF N (B j) =
      matrixAFStageToUHF (i j) (A j) := by
    intro j
    exact matrixAFStageToUHF_transition (hiN j) (A j)
  let g : X → PrimeAFMatrixStageAlgebra localDim N := fun x =>
    ∑ j : ι, ((φ j x : ℝ) : ℂ) • B j
  have hgContinuous : Continuous g := by
    unfold g
    fun_prop
  have hsum (x : X) : ∑ j : ι, φ j x = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact φ.sum_eq_one (Set.mem_univ x)
  have hgBd : ∀ x ∈ bd, g x = 0 := by
    intro x hx
    change (∑ j : ι, ((φ j x : ℝ) : ℂ) • B j) = 0
    rw [Finset.sum_eq_zero]
    intro j _
    by_cases hφzero : φ j x = 0
    · simp [hφzero]
    · have hxV : x ∈ V j := hφ j (subset_tsupport _ hφzero)
      cases hj : j.1 with
      | none =>
          have hBj : B j = 0 := by
            change matrixAFStageTransition localDim (i j) N (hiN j) (A j) = 0
            rw [hAzero j hj, map_zero]
          rw [hBj, smul_zero]
      | some y =>
          have hxV' : x ∈ bdᶜ ∩ r ⁻¹' Metric.ball (r y) ε := by
            simpa [V, U, hj] using hxV
          have : x ∈ bdᶜ := hxV'.1
          exact absurd hx this
  refine ⟨N, g, hgContinuous, hgBd, ?_⟩
  intro x
  have hactive : ∀ j : ι, φ j x ≠ 0 →
      ‖matrixAFStageToUHF N (B j) - r x‖ ≤ 2 * ε := by
    intro j hφnonzero
    have hxV : x ∈ V j := hφ j (subset_tsupport _ hφnonzero)
    cases hj : j.1 with
    | none =>
        have hBj : B j = 0 := by
          change matrixAFStageTransition localDim (i j) N (hiN j) (A j) = 0
          rw [hAzero j hj, map_zero]
        have hxr : ‖r x‖ < ε := by
          have hxV' : r x ∈ Metric.ball 0 ε := by
            simpa [V, U, hj] using hxV
          have : dist (r x) 0 < ε := hxV'
          simpa [dist_eq_norm] using this
        rw [hBj, map_zero, zero_sub, norm_neg]
        exact hxr.le.trans (by linarith)
    | some y =>
        have hxV' : x ∈ bdᶜ ∩ r ⁻¹' Metric.ball (r y) ε := by
          simpa [V, U, hj] using hxV
        have hcenter : ‖matrixAFStageToUHF N (B j) - r y‖ < ε := by
          rw [hBmap]
          simpa [centerValue, hj] using hA j
        have hxy : ‖r x - r y‖ < ε := by
          have : dist (r x) (r y) < ε := hxV'.2
          simpa [dist_eq_norm] using this
        have htri := norm_add_le
          (matrixAFStageToUHF N (B j) - r y) (r y - r x)
        have hsplit : matrixAFStageToUHF N (B j) - r x =
            (matrixAFStageToUHF N (B j) - r y) + (r y - r x) := by abel
        rw [← hsplit] at htri
        rw [norm_sub_rev] at hxy
        linarith
  have hterm : ∀ j : ι,
      ‖((φ j x : ℝ) : ℂ) •
        (matrixAFStageToUHF N (B j) - r x)‖ ≤
      φ j x * (2 * ε) := by
    intro j
    by_cases hzero : φ j x = 0
    · simp [hzero]
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (φ.nonneg j x)]
      exact mul_le_mul_of_nonneg_left (hactive j hzero) (φ.nonneg j x)
  have hcomplexSum : ∑ j : ι, (((φ j x : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hsum x
  have hdecomp : matrixAFStageToUHF N (g x) - r x =
      ∑ j : ι, ((φ j x : ℝ) : ℂ) •
        (matrixAFStageToUHF N (B j) - r x) := by
    change matrixAFStageToUHF N
      (∑ j : ι, ((φ j x : ℝ) : ℂ) • B j) - r x = _
    rw [map_sum]
    simp_rw [map_smul]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hcomplexSum, one_smul]
  rw [hdecomp]
  calc
    ‖∑ j : ι, ((φ j x : ℝ) : ℂ) •
        (matrixAFStageToUHF N (B j) - r x)‖ ≤
        ∑ j : ι, ‖((φ j x : ℝ) : ℂ) •
          (matrixAFStageToUHF N (B j) - r x)‖ := norm_sum_le _ _
    _ ≤ ∑ j : ι, φ j x * (2 * ε) := Finset.sum_le_sum fun j _ => hterm j
    _ = 2 * ε := by rw [← Finset.sum_mul, hsum, one_mul]

def finiteStagePolarUnitaryOfGram
    {d : ℕ} [Nonempty (Fin d)] (A : Matrix (Fin d) (Fin d) ℂ)
    (hgram : ‖star A * A - 1‖ ≤ 1 / 2) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨cstarPolarNearOne A, by
    have hiso := cstarPolarNearOne_star_mul_self hgram
    exact ⟨hiso, RHTower.finiteMatrix_isometry_is_unitary _ hiso⟩⟩

theorem continuous_finiteStagePolarUnitaryOfGram_comp
    {d : ℕ} [Nonempty (Fin d)] {X : Type*} [TopologicalSpace X]
    (A : X → Matrix (Fin d) (Fin d) ℂ) (hA : Continuous A)
    (hgram : ∀ x, ‖star (A x) * A x - 1‖ ≤ 1 / 2) :
    Continuous (fun x => finiteStagePolarUnitaryOfGram (A x) (hgram x)) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun x => cstarPolarNearOne (A x))
  exact continuous_cstarPolarNearOne_comp hA hgram

set_option maxHeartbeats 1000000 in
theorem exists_finiteStage_nullhomotopy_of_UHF_nullhomotopy
    {localDim : ℕ → ℕ} [Fact (∀ k, 0 < localDim k)]
    (i : ℕ)
    (p : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim i)) ℂ) 1)
    (H : (matrixAFStageToUHFBasedPath i p).Homotopy (Path.refl 1)) :
    ∃ (M : ℕ) (hiM : i ≤ M),
      ((p.map (continuous_matrixAFStageUnitaryTransition Fact.out hiM)).cast
        (map_one (matrixAFStageUnitaryTransition localDim hiM)).symm
        (map_one (matrixAFStageUnitaryTransition localDim hiM)).symm).Homotopic
        (Path.refl 1) := by
  let X := unitInterval × unitInterval
  let bd : Set X :=
    {st | st.1 = 0} ∪ {st | st.1 = 1} ∪ {st | st.2 = 0} ∪ {st | st.2 = 1}
  have hbd : IsClosed bd := by
    exact (((isClosed_singleton.preimage continuous_fst).union
      (isClosed_singleton.preimage continuous_fst)).union
      (isClosed_singleton.preimage continuous_snd)).union
      (isClosed_singleton.preimage continuous_snd)
  let b : X → PrimeUHFAlgebra localDim := fun st =>
    (((1 - (st.1 : ℝ) : ℝ) : ℂ) •
      (matrixAFStageUnitaryToUHF i (p st.2) : PrimeUHFAlgebra localDim)) +
      (((st.1 : ℝ) : ℂ) • (1 : PrimeUHFAlgebra localDim))
  have hb : Continuous b := by
    have hu : Continuous (fun st : X => matrixAFStageUnitaryToUHF i (p st.2)) :=
      (continuous_matrixAFStageUnitaryToUHF i).comp
        (p.continuous.comp continuous_snd)
    have hucoe : Continuous (fun st : X =>
        (matrixAFStageUnitaryToUHF i (p st.2) : PrimeUHFAlgebra localDim)) :=
      continuous_subtype_val.comp hu
    have hc₀ : Continuous (fun st : X => (((1 - (st.1 : ℝ) : ℝ) : ℂ))) := by
      change Continuous (fun st : unitInterval × unitInterval =>
        (((1 - (st.1 : ℝ) : ℝ) : ℂ)))
      fun_prop
    have hc₁ : Continuous (fun st : X => (((st.1 : ℝ) : ℂ))) := by
      change Continuous (fun st : unitInterval × unitInterval =>
        (((st.1 : ℝ) : ℂ)))
      fun_prop
    unfold b
    exact (hc₀.smul hucoe).add (hc₁.smul continuous_const)
  let r : X → PrimeUHFAlgebra localDim := fun st => (H st : PrimeUHFAlgebra localDim) - b st
  have hr : Continuous r := by
    unfold r
    exact (continuous_subtype_val.comp H.continuous).sub hb
  have hrbd : ∀ st ∈ bd, r st = 0 := by
    intro st hst
    simp only [bd, Set.mem_union, Set.mem_setOf_eq] at hst
    rcases hst with ((h₀ | h₁) | h₀) | h₁
    · have hpair : st = (0, st.2) := Prod.ext h₀ rfl
      have hHu : H st = matrixAFStageToUHFBasedPath i p st.2 := by
        rw [hpair]
        exact H.map_zero_left st.2
      have hH := congrArg Subtype.val hHu
      change (H st : PrimeUHFAlgebra localDim) =
        matrixAFStageToUHF i (p st.2 : PrimeAFMatrixStageAlgebra localDim i) at hH
      change (H st : PrimeUHFAlgebra localDim) - b st = 0
      rw [hH]
      simp [b, h₀]
      change matrixAFStageToUHF i (p st.2 : PrimeAFMatrixStageAlgebra localDim i) -
        matrixAFStageToUHF i (p st.2 : PrimeAFMatrixStageAlgebra localDim i) = 0
      exact sub_self _
    · have hpair : st = (1, st.2) := Prod.ext h₁ rfl
      have hHu : H st = (Path.refl 1) st.2 := by
        rw [hpair]
        exact H.map_one_left st.2
      have hH := congrArg Subtype.val hHu
      change (H st : PrimeUHFAlgebra localDim) = 1 at hH
      change (H st : PrimeUHFAlgebra localDim) - b st = 0
      rw [hH]
      simp [b, h₁]
    · have hHt := H.prop' st.1 st.2 (by simp [h₀])
      have hp₀ : p st.2 = 1 := (congrArg p h₀).trans p.source
      have hHu₀ : H st = matrixAFStageToUHFBasedPath i p st.2 := hHt
      have hMap₀ : matrixAFStageToUHFBasedPath i p st.2 = 1 := by
        apply Subtype.ext
        change matrixAFStageToUHF i
          (p st.2 : PrimeAFMatrixStageAlgebra localDim i) = 1
        rw [hp₀]
        exact map_one _
      have hHu : H st = 1 := hHu₀.trans hMap₀
      have hH := congrArg Subtype.val hHu
      change (H st : PrimeUHFAlgebra localDim) - b st = 0
      rw [hH]
      have hbOne : b st = 1 := by
        have hbdef : b st = (((1 - (st.1 : ℝ) : ℝ) : ℂ) •
          (matrixAFStageUnitaryToUHF i (p st.2) : PrimeUHFAlgebra localDim)) +
          (((st.1 : ℝ) : ℂ) • 1) := by
            rfl
        have hup : (matrixAFStageUnitaryToUHF i (p st.2) :
            PrimeUHFAlgebra localDim) = 1 := congrArg Subtype.val hMap₀
        rw [hbdef, hup]
        rw [← add_smul]
        convert one_smul ℂ (1 : PrimeUHFAlgebra localDim) using 1
        push_cast
        ring
      rw [hbOne]
      change (1 : PrimeUHFAlgebra localDim) - 1 = 0
      exact sub_self _
    · have hHt := H.prop' st.1 st.2 (by simp [h₁])
      have hp₁ : p st.2 = 1 := (congrArg p h₁).trans p.target
      have hHu₁ : H st = matrixAFStageToUHFBasedPath i p st.2 := hHt
      have hMap₁ : matrixAFStageToUHFBasedPath i p st.2 = 1 := by
        apply Subtype.ext
        change matrixAFStageToUHF i
          (p st.2 : PrimeAFMatrixStageAlgebra localDim i) = 1
        rw [hp₁]
        exact map_one _
      have hHu : H st = 1 := hHu₁.trans hMap₁
      have hH := congrArg Subtype.val hHu
      change (H st : PrimeUHFAlgebra localDim) - b st = 0
      rw [hH]
      have hbOne : b st = 1 := by
        have hbdef : b st = (((1 - (st.1 : ℝ) : ℝ) : ℂ) •
          (matrixAFStageUnitaryToUHF i (p st.2) : PrimeUHFAlgebra localDim)) +
          (((st.1 : ℝ) : ℂ) • 1) := by
            rfl
        have hup : (matrixAFStageUnitaryToUHF i (p st.2) :
            PrimeUHFAlgebra localDim) = 1 := congrArg Subtype.val hMap₁
        rw [hbdef, hup]
        rw [← add_smul]
        convert one_smul ℂ (1 : PrimeUHFAlgebra localDim) using 1
        push_cast
        ring
      rw [hbOne]
      change (1 : PrimeUHFAlgebra localDim) - 1 = 0
      exact sub_self _
  let ε : ℝ := 1 / 1024
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨N, g, hg, hgbd, hgclose⟩ :=
    exists_commonStageContinuousMap_relative_approximation r hr bd hbd hrbd hε
  let M := i + N
  have hiM : i ≤ M := Nat.le_add_right i N
  have hNM : N ≤ M := by omega
  let pM : unitInterval → Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim M)) ℂ := fun t =>
    matrixAFStageUnitaryTransition localDim hiM (p t)
  let gM : X → PrimeAFMatrixStageAlgebra localDim M := fun st =>
    matrixAFStageTransition localDim N M hNM (g st)
  have hgM : Continuous gM := by
    unfold gM
    exact (continuous_matrixAFStageTransition Fact.out hNM).comp hg
  have hmapgM : ∀ st, matrixAFStageToUHF M (gM st) =
      matrixAFStageToUHF N (g st) := by
    intro st
    exact matrixAFStageToUHF_transition hNM (g st)
  let B : X → PrimeAFMatrixStageAlgebra localDim M := fun st =>
    (((1 - (st.1 : ℝ) : ℝ) : ℂ) •
      (pM st.2 : PrimeAFMatrixStageAlgebra localDim M)) +
      (((st.1 : ℝ) : ℂ) • (1 : PrimeAFMatrixStageAlgebra localDim M))
  have hB : Continuous B := by
    have hpM : Continuous pM :=
      (continuous_matrixAFStageUnitaryTransition Fact.out hiM).comp p.continuous
    have hpMcoe : Continuous (fun t =>
        (pM t : PrimeAFMatrixStageAlgebra localDim M)) :=
      continuous_subtype_val.comp hpM
    have hc₀ : Continuous (fun st : X => (((1 - (st.1 : ℝ) : ℝ) : ℂ))) := by
      change Continuous (fun st : unitInterval × unitInterval =>
        (((1 - (st.1 : ℝ) : ℝ) : ℂ)))
      fun_prop
    have hc₁ : Continuous (fun st : X => (((st.1 : ℝ) : ℂ))) := by
      change Continuous (fun st : unitInterval × unitInterval =>
        (((st.1 : ℝ) : ℂ)))
      fun_prop
    unfold B
    exact (hc₀.smul (hpMcoe.comp continuous_snd)).add
      (hc₁.smul continuous_const)
  let A : X → PrimeAFMatrixStageAlgebra localDim M := fun st => B st + gM st
  have hA : Continuous A := hB.add hgM
  have hmapB : ∀ st, matrixAFStageToUHF M (B st) = b st := by
    intro st
    change matrixAFStageToUHF M
      ((((1 - (st.1 : ℝ) : ℝ) : ℂ) •
        (pM st.2 : PrimeAFMatrixStageAlgebra localDim M)) +
        (((st.1 : ℝ) : ℂ) • (1 : PrimeAFMatrixStageAlgebra localDim M))) = _
    rw [map_add, map_smul, map_smul, map_one]
    change _ = (((1 - (st.1 : ℝ) : ℝ) : ℂ) •
      (matrixAFStageUnitaryToUHF i (p st.2) : PrimeUHFAlgebra localDim)) + _
    have hpMmap : matrixAFStageToUHF M
        (pM st.2 : PrimeAFMatrixStageAlgebra localDim M) =
        matrixAFStageToUHF i (p st.2 : PrimeAFMatrixStageAlgebra localDim i) :=
      matrixAFStageToUHF_transition hiM
        (p st.2 : PrimeAFMatrixStageAlgebra localDim i)
    rw [hpMmap]
    rfl
  have hclose : ∀ st, ‖matrixAFStageToUHF M (A st) -
      (H st : PrimeUHFAlgebra localDim)‖ ≤ 2 * ε := by
    intro st
    have hc := hgclose st
    change ‖matrixAFStageToUHF M (B st + gM st) -
      (H st : PrimeUHFAlgebra localDim)‖ ≤ _
    rw [map_add, hmapB, hmapgM]
    have heq : b st + matrixAFStageToUHF N (g st) - (H st : PrimeUHFAlgebra localDim) =
        matrixAFStageToUHF N (g st) - r st := by
      change b st + matrixAFStageToUHF N (g st) - (H st : PrimeUHFAlgebra localDim) =
        matrixAFStageToUHF N (g st) - ((H st : PrimeUHFAlgebra localDim) - b st)
      abel
    rw [heq]
    exact hc
  have hgram : ∀ st, ‖star (A st) * A st - 1‖ ≤ 1 / 2 := by
    intro st
    have hdef := norm_star_mul_self_sub_one_le_of_unitary
      (matrixAFStageToUHF M (A st)) (H st)
    have hnorm : ‖matrixAFStageToUHF M (A st) -
        (H st : PrimeUHFAlgebra localDim)‖ ≤ 2 * ε := hclose st
    calc
      ‖star (A st) * A st - 1‖ =
          ‖matrixAFStageToUHF M (star (A st) * A st - 1)‖ :=
        (norm_matrixAFStageToUHF M _).symm
      _ = ‖star (matrixAFStageToUHF M (A st)) *
          matrixAFStageToUHF M (A st) - 1‖ := by
        rw [map_sub, map_mul, map_star, map_one]
      _ ≤ ‖matrixAFStageToUHF M (A st) - (H st : PrimeUHFAlgebra localDim)‖ *
          (2 + ‖matrixAFStageToUHF M (A st) - (H st : PrimeUHFAlgebra localDim)‖) := hdef
      _ ≤ 1 / 2 := by
        have hn := norm_nonneg (matrixAFStageToUHF M (A st) -
          (H st : PrimeUHFAlgebra localDim))
        norm_num [ε] at hnorm ⊢
        nlinarith
  letI : Nonempty (Fin (matrixAFStageDimension localDim M)) :=
    Fin.pos_iff_nonempty.mp (matrixAFStageDimension_pos Fact.out M)
  let P : X → Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim M)) ℂ := fun st =>
    finiteStagePolarUnitaryOfGram (A st) (hgram st)
  have hP : Continuous P :=
    continuous_finiteStagePolarUnitaryOfGram_comp A hA hgram
  let pMPath : Path (matrixAFStageUnitaryTransition localDim hiM 1)
      (matrixAFStageUnitaryTransition localDim hiM 1) :=
    p.map (continuous_matrixAFStageUnitaryTransition Fact.out hiM)
  let pMBased : Path (1 : Matrix.unitaryGroup
      (Fin (matrixAFStageDimension localDim M)) ℂ) 1 :=
    pMPath.cast (map_one (matrixAFStageUnitaryTransition localDim hiM)).symm
      (map_one (matrixAFStageUnitaryTransition localDim hiM)).symm
  refine ⟨M, hiM, ?_⟩
  change pMBased.Homotopic (Path.refl 1)
  refine ⟨{
    toContinuousMap := ⟨P, hP⟩
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    apply Subtype.ext
    change cstarPolarNearOne (A (0, t)) = (pM t : PrimeAFMatrixStageAlgebra localDim M)
    have hg₀ : gM (0, t) = 0 := by
      change matrixAFStageTransition localDim N M hNM (g (0, t)) = 0
      rw [hgbd]
      · exact map_zero _
      · simp [bd]
    have hA₀ : A (0, t) = (pM t : PrimeAFMatrixStageAlgebra localDim M) := by
      change B (0, t) + gM (0, t) = _
      rw [hg₀, add_zero]
      change ((((1 - (0 : ℝ) : ℝ) : ℂ) •
        (pM t : PrimeAFMatrixStageAlgebra localDim M)) +
        ((((0 : ℝ) : ℂ)) • (1 : PrimeAFMatrixStageAlgebra localDim M))) = _
      simp
    rw [hA₀]
    exact cstarPolarNearOne_unitary (pM t)
  · intro t
    apply Subtype.ext
    change cstarPolarNearOne (A (1, t)) = 1
    have hg₁ : gM (1, t) = 0 := by
      change matrixAFStageTransition localDim N M hNM (g (1, t)) = 0
      rw [hgbd]
      · exact map_zero _
      · simp [bd]
    have hA₁ : A (1, t) = 1 := by
      change B (1, t) + gM (1, t) = _
      rw [hg₁, add_zero]
      change ((((1 - (1 : ℝ) : ℝ) : ℂ) •
        (pM t : PrimeAFMatrixStageAlgebra localDim M)) +
        ((((1 : ℝ) : ℂ)) • (1 : PrimeAFMatrixStageAlgebra localDim M))) = _
      simp
    rw [hA₁]
    exact cstarPolarNearOne_unitary
      (1 : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim M)) ℂ)

  · intro s t ht
    have ht' := ht
    have hpBased : pMBased t = 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht'
      rcases ht' with rfl | rfl
      · exact pMBased.source
      · exact pMBased.target
    change P (s, t) = pMBased t
    rw [hpBased]
    apply Subtype.ext
    change cstarPolarNearOne (A (s, t)) = 1
    have hgb : gM (s, t) = 0 := by
      change matrixAFStageTransition localDim N M hNM (g (s, t)) = 0
      rw [hgbd]
      · exact map_zero _
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl <;> simp [bd]
    have hpmt : pM t = 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · simp [pM, p.source]
      · simp [pM, p.target]
    have hAb : A (s, t) = 1 := by
      change B (s, t) + gM (s, t) = _
      rw [hgb, add_zero]
      change ((((1 - (s : ℝ) : ℝ) : ℂ) •
        (pM t : PrimeAFMatrixStageAlgebra localDim M)) +
        ((((s : ℝ) : ℂ)) • (1 : PrimeAFMatrixStageAlgebra localDim M))) = _
      have hpmtcoe : (pM t : PrimeAFMatrixStageAlgebra localDim M) = 1 := by
        exact congrArg Subtype.val hpmt
      rw [hpmtcoe, ← add_smul]
      convert one_smul ℂ (1 : PrimeAFMatrixStageAlgebra localDim M) using 1
      push_cast
      ring
    rw [hAb]
    exact cstarPolarNearOne_unitary
      (1 : Matrix.unitaryGroup (Fin (matrixAFStageDimension localDim M)) ℂ)

end
end PrimeQuasiLocalCharge
