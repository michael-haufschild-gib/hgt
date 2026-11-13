/-
Zeros near the detector adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.LogarithmicInputs
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PhysicalProbes

/-!
# Zeros near the detector

Zero maxima on buffered disks (`HeckeDetectorZeros`), dyadic bridges and rectangle bounds;
twist profiles of the inverse amplification, their support and smoothness.
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
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Set Filter
open scoped Classical Topology
namespace HeckeDetectorZeros
open HeckeFamily

def rectangle (T : ℝ) : Set ℂ :=
  {s | (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}

theorem rectangle_compact (T : ℝ) : IsCompact (rectangle T) := by
  have heq : rectangle T = Set.Icc (51/100 : ℝ) 1 ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [rectangle, Set.mem_setOf_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def zeros (χ : Character) (T : ℝ) : Set ℂ := {s ∈ rectangle T | LFunction χ s = 0}

theorem zeros_finite (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) :
    (zeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (LFunction_entire_nonprincipal χ hχ)
  have hcod := ha.preimage_zero_mem_codiscreteWithin
    (LFunction_ne_zero_of_one_lt_re χ (by norm_num : 1 < (2 : ℂ).re))
    (Set.mem_univ (2 : ℂ)) isConnected_univ
  have hfin := (rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (rectangle T)) hcod)
  convert hfin using 1
  ext s
  simp [zeros]

def zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) : Finset ℂ :=
  (zeros_finite χ hχ T).toFinset

@[simp] theorem mem_zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) (s : ℂ) :
    s ∈ zeroFinset χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeros, rectangle, Set.mem_setOf_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i => (zeroFinset (χ i) (hχ i) T).image (fun s => (i,s)))

@[simp] theorem mem_familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) (s : ℂ) :
    (i,s) ∈ familyZeros χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction (χ i) s = 0 := by
  simp [familyZeros]

def realParts (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((familyZeros χ hχ T).image (fun p => p.2.re))

theorem realParts_nonempty (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (realParts χ hχ T).Nonempty := Finset.insert_nonempty _ _

def zeroMaximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : ℝ :=
  (realParts χ hχ T).max' (realParts_nonempty χ hχ T)

theorem zeroMaximum_mem (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    zeroMaximum χ hχ T ∈ realParts χ hχ T := Finset.max'_mem _ _

theorem zeroMaximum_bounds (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (51/100 : ℝ) ≤ zeroMaximum χ hχ T ∧ zeroMaximum χ hχ T ≤ 1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨⟨i,s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
      exact (mem_familyZeros χ hχ T i s |>.mp hs).2.1

theorem zero_re_le_maximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) {s : ℂ} (hs : (51/100 : ℝ) ≤ s.re)
    (ht : |s.im| ≤ T) (hz : LFunction (χ i) s = 0) : s.re ≤ zeroMaximum χ hχ T := by
  have hle : s.re ≤ 1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s), (mem_familyZeros χ hχ T i s).mpr ⟨hs, hle, ht, hz⟩, rfl⟩)

theorem maximum_attained (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ)
    (hmax : (51/100 : ℝ) < zeroMaximum χ hχ T) :
    ∃ i s, LFunction (χ i) s = 0 ∧ |s.im| ≤ T ∧ s.re = zeroMaximum χ hχ T := by
  have hm := zeroMaximum_mem χ hχ T
  rcases Finset.mem_insert.mp hm with hm | hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩, hs, heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_familyZeros χ hχ T i s).mp hs
    exact ⟨i,s,hz.2.2.2,hz.2.2.1,heq⟩

theorem zeroMaximum_mono (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    {T T' : ℝ} (hT : T ≤ T') : zeroMaximum χ hχ T ≤ zeroMaximum χ hχ T' := by
  rcases lt_or_ge (51/100 : ℝ) (zeroMaximum χ hχ T) with hm | hm
  · obtain ⟨i,s,hz,ht,heq⟩ := maximum_attained χ hχ T hm
    rw [← heq]
    apply zero_re_le_maximum χ hχ T' i _ (ht.trans hT) hz
    rw [heq]
    exact hm.le
  · exact hm.trans (zeroMaximum_bounds χ hχ T').1

theorem nonzero_on_buffered_disk (χ : ι → Character) (hχ : ∀ j, (χ j).residue ≠ 1)
    (T a e : ℝ) (i : ℕ) (hT : 2 < T) (ha : (51/100 : ℝ) ≤ a) (he : 0 < e)
    (hmax : zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e)
    (j : ι) (t : ℝ) (ht : |t| ≤ (3*i+2 : ℕ)*T)
    {s : ℂ} (hs : s ∈ Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e)) :
    LFunction (χ j) s ≠ 0 := by
  have hn : ‖s-((2 : ℂ)+t*Complex.I)‖ ≤ 2-a-2*e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2 : ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2 : ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e ≤ s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im| ≤ 3*(i+1 : ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  intro hz
  have hle := zero_re_le_maximum χ hχ (3*(i+1 : ℕ)*T) j (by linarith) him hz
  linarith

theorem exists_actual_buffered_bin (χ : ι → Character)
    (hχ : ∀ j, (χ j).residue ≠ 1) (T e : ℝ) (hT : 2 < T) (he : 0 < e)
    (n : ℕ) (hn : 0 < n) (hwidth : (49/100 : ℝ) ≤ n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a ≤ 1 ∧ a ≤ zeroMaximum χ hχ (3*i*T) ∧
      zeroMaximum χ hχ (3*i*T) < a+e ∧
      zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e ∧
      (51/100 < a → ∃ j s, LFunction (χ j) s = 0 ∧ a ≤ s.re ∧
        s.re < a+e ∧ |s.im| ≤ 3*i*T) ∧
      (∀ j t, |t| ≤ (3*i+2 : ℕ)*T → ∀ s ∈
        Metric.closedBall ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction (χ j) s ≠ 0) := by
  let M : ℕ → ℝ := fun j => zeroMaximum χ hχ (3*(j+1 : ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _ => zeroMaximum_bounds χ hχ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,ht,hs⟩ := maximum_attained χ hχ (3*(i+1 : ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,by rw [hs]; exact hlo,by rw [hs]; exact hhi,ht⟩
  · intro j t ht s hs
    apply nonzero_on_buffered_disk χ hχ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α := ℝ) k]) he hnext j t ht hs

end HeckeDetectorZeros

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Set Metric
namespace HeckeDyadicControl
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

theorem original_disk_control (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ (χ : Character), χ.residue ≠ 1 → ∀ a t : ℝ,
      1/2≤ a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), LFunction χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ hχ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue ≠ 1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have hregular : regular ψ = LFunction ψ := regular_eq_nonprincipal ψ hψ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    rw [hregular]
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  rw [hregular] at hbound
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : LFunction χ z = LFunction ψ z*factors χ.modulus ψ z :=
    LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      (LFunction ψ z)⁻¹*(factors χ.modulus ψ z)⁻¹ := by
    rw [HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos]
    simp only [HeckeReciprocal.reciprocal, if_neg hψ]
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖LFunction ψ z‖+‖(LFunction ψ z)⁻¹‖)*
        (Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (LFunction ψ z))
      have h2 := mul_le_mul_of_nonneg_left hdel2 (norm_nonneg ((LFunction ψ z)⁻¹))
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_original_control (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue ≠ 1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T) < a+2*e →
      ∀ (j : ι) (t : ℝ), |t| ≤ (3*i+2 : ℕ)*T →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖ ≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j t ht z hz
  exact hbound (χ j) (hχ j) a t (by linarith) ha'
    (fun w hw => HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
      hmax j t ht (ball_subset_closedBall hw)) z hz

end HeckeDyadicControl

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace HeckeDyadic
open HeckeFamily HeckeLogarithmic HeckeReciprocalGrowth

theorem presentationComplexity_mono_height (χ : Character) {t H : ℝ}
    (ht : |t|≤ H) : presentationComplexity χ t≤ presentationComplexity χ H := by
  unfold presentationComplexity complexity
  have hH : 0≤ H := (abs_nonneg t).trans ht
  rw [abs_of_nonneg hH]
  gcongr

theorem buffered_rectangle_control (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (z : ℂ), a+6*e≤ z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
        C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨C,hC,hbound⟩ := HeckeDyadicControl.buffered_original_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2 : ℂ)+z.im*I)=((z.re-2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith : z.re-2≤0)]
    linarith
  have hz2 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-2*e) :=
    closedBall_subset_closedBall (by linarith) hz6
  refine ⟨HeckeDetectorZeros.nonzero_on_buffered_disk χ hχ T a e i hT ha he
    hmax j z.im hzi hz2, ?_⟩
  apply (hbound χ hχ T a i hT ha ha' hmax j z.im hzi z hz6).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow
  · unfold presentationComplexity complexity
    positivity
  · exact presentationComplexity_mono_height _ hzi
  · exact hε.le

theorem translated_rectangle_mem {a e σ freq l r H T : ℝ}
    (hl : a+6*e≤ l+σ) (hr : r+σ≤2) (hlr : l≤ r) (hT : 0≤ T)
    (hfreq : |freq|+T≤ H) {s : ℂ} (hs : s ∈ (uIcc l r ×ℂ uIcc (-T) T)) :
    a+6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧
      |(s+shift σ freq).im|≤ H := by
  have hs' : s.re ∈ Icc l r ∧ s.im ∈ Icc (-T) T := by
    change s.re ∈ uIcc l r ∧ s.im ∈ uIcc (-T) T at hs
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤ T)] using hs
  have hsi : |s.im|≤ T := abs_le.mpr hs'.2
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.1]
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.2]
  · have hi : (s+shift σ freq).im=s.im-freq := by simp [shift,sub_eq_add_neg]
    rw [hi]
    exact (abs_sub _ _).trans (by linarith)

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace HeckeDyadic
open HeckeFamily

theorem norm_four_sides (A B C D : ℂ) :
    ‖A+I*(B-C)+D‖≤‖A‖+‖B‖+‖C‖+‖D‖ := by
  have h₁ := norm_add_le (A+I*(B-C)) D
  have h₂ := norm_add_le A (I*(B-C))
  have h₃ := norm_sub_le B C
  simp only [norm_mul,norm_I,one_mul] at h₂
  linarith

theorem polynomial_bound_of_rectangle (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K : ℝ) (n : ℕ)
    (hD : 1≤ D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤ T)
    (hC₂ : 0≤ C₂) (hCn : 0≤ Cn) (hK : 0≤ K)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤ C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤ K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*K*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0< D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤ T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ K T hDp hC₂ hK hT
    hm₂ (fun t ht => hs _ (hmem l t ⟨le_rfl,hlr⟩ ht))
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤ Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

theorem polynomial_bound_of_rectangle_split (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) (W : ℝ → ℂ) (a b : ℝ) (ha : 0< a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T C₂ Cn K Kc : ℝ) (n : ℕ)
    (hD : 1≤ D) (hlr : l≤ r) (hr : 1< r+σ) (hT : 0≤ T)
    (hC₂ : 0≤ C₂) (hCn : 0≤ Cn) (hK : 0≤ K) (hKc : 0≤ Kc)
    (hm₂ : ∀ t : ℝ, (1+|t|)^2*‖mellin W ((l : ℂ)+t*I)‖≤ C₂)
    (hmn : ∀ x ∈ Icc l r, ∀ t : ℝ,
      (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn)
    (hcentralSeries : ∀ t ∈ Icc (-T) T, ‖series χ inverse ((l : ℂ)+t*I+shift σ freq)‖≤ Kc)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0)
    (hs : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T),
      ‖series χ inverse (s+shift σ freq)‖≤ K) :
    ‖polynomial χ inverse W D σ freq‖≤(1/(2*Real.pi))*
      (C₂*D^(l+σ-1/2)*Kc*Real.pi +
       2*(Cn*D^(r+σ-1/2)*K/(1+T)^n)*|r-l| +
       (Cn*D^(r+σ-1/2)*HeckeReciprocalBound.bound (r+σ))/(1+T)^n*Real.pi) := by
  have hDp : 0< D := by linarith
  have hmem (x t : ℝ) (hx : x∈Icc l r) (ht : t∈Icc (-T) T) :
      ((x : ℂ)+t*I) ∈ (uIcc l r ×ℂ uIcc (-T) T) := by
    change (((x : ℂ)+t*I).re∈uIcc l r) ∧ (((x : ℂ)+t*I).im∈uIcc (-T) T)
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤ T)] using And.intro hx ht
  have hcentral := central_segment_bound χ inverse W D l σ freq C₂ Kc T hDp hC₂ hKc hT
    hm₂ hcentralSeries
  have hm (x : ℝ) (hx : x∈Icc l r) (t : ℝ) :
      (1+|t|)^n*‖mellin W ((x : ℂ)+t*I)‖≤ Cn := by
    apply le_trans _ (hmn x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · omega
  have hbottom := horizontal_join_bound χ inverse W D σ freq l r (-T) Cn K n hD hlr hCn hK
    (fun x hx => hm x hx (-T)) (fun x hx => hs _ (hmem x (-T) hx ⟨le_rfl,by linarith⟩))
  have htop := horizontal_join_bound χ inverse W D σ freq l r T Cn K n hD hlr hCn hK
    (fun x hx => hm x hx T) (fun x hx => hs _ (hmem x T hx ⟨by linarith,le_rfl⟩))
  simp only [abs_neg,abs_of_nonneg hT,ofReal_neg] at hbottom htop
  have htail := absolute_tail_bound χ inverse W D r σ freq Cn T n hDp hr hCn hT
    (hmn r ⟨hlr,le_rfl⟩)
  rw [polynomial_finite_shift χ hχ inverse W a b ha hWs hW D σ freq l r T hDp hr hT hz,
    norm_mul]
  have hnorm : ‖(1/(2*Real.pi) : ℂ)‖=(1/(2*Real.pi) : ℝ) := by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_four_sides _ _ _ _).trans (by linarith)

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem buffered_polynomial_bound (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤ D → 0≤ V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤ C₂ → 0≤ Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
      ‖polynomial (χ j) inverse W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(a+6*e-1/2)*K*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*K/(1+V)^n)*|2-a-6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨C,hC,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let K := C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε
  have hK : 0≤ K := mul_nonneg hC.le (Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _)
  have hlr : a+6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    translated_rectangle_mem (a:=a) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : a+6*e≤ a+6*e-σ+σ) (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
  have hz {s : ℂ} (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :=
    hrect χ hχ T a i hT ha ha' hmax j (s+shift σ freq) (hmem hs).1 (hmem hs).2.1 (hmem hs).2.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (a+6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) inverse (s+shift σ freq)‖≤ K := by
    have hb := (hz hs).2
    cases inverse
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans hb
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans hb
  have hbound := polynomial_bound_of_rectangle (χ j) (hχ j) inverse W A B hA hWs hW
    D σ freq (a+6*e-σ) (2-σ) V C₂ Cn K n hD hlr (by linarith) hV hC₂ hCn hK hm₂ hmn
    (fun _ hs _ => (hz hs).1) hseries
  dsimp only [K] at hbound
  convert hbound using 1 ; congr 2 <;> ring_nf

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace HeckeDyadicReflection
open HeckeFamily HeckePresentation HeckeFiniteDeletion

theorem family_reflected_bound : ∃ C : ℝ, 0< C ∧ ∀ η : Character,
    FiniteFourier.IsPrimitiveOnIdeals η.residue → η.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction η s‖≤ C*(η.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction η (1-conj s)‖ := by
  obtain ⟨C,hC,hbound⟩ := primitive_reflected_bound
  refine ⟨C,hC,?_⟩
  intro η hp hη s hl hr
  have h := hbound (generator η) (principalResidue η) (principalResidue_unit η)
    (principalResidue_primitive η hp) (principalResidue_ne_one η hη) s hl hr
  have hi : HeckePrimitive.character (generator η) (principalResidue η)⁻¹
      (HeckePrimitive.inverse_unit_trivial (generator η) (principalResidue η) (principalResidue_unit η)) =
      (principalCharacter η).inverse := rfl
  rw [hi,LFunction_inverse_conj (principalCharacter η) (principalResidue_ne_one η hη),
    norm_conj,map_sub,map_one] at h
  change ‖LFunction (principalCharacter η) s‖≤ _ at h
  rw [LFunction_principalCharacter η hη,LFunction_principalCharacter η hη] at h
  simpa only [HeckeStripActual.conductor,span_generator] using h

theorem LFunction_eq_of_mask_entire (χ ψ : Character) (hχ : χ.residue≠1)
    (hmask : ∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) (s : ℂ) :
    LFunction χ s=LFunction ψ s*factors χ.modulus ψ s := by
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have ha := LFunction_entire_nonprincipal χ hχ
  have hb : Differentiable ℂ (fun z => LFunction ψ z*factors χ.modulus ψ z) :=
    (LFunction_entire_nonprincipal ψ hψ).mul (factors_differentiable _ _)
  have he : LFunction χ=(fun z => LFunction ψ z*factors χ.modulus ψ z) := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr ha).eq_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hb) (z₀ := (2 : ℂ))
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num : (1 : ℝ)<(2 : ℂ).re)] with z hz
    exact LFunction_eq_of_mask_right χ ψ hmask hz
  exact congr_fun he s

theorem original_reflected_bound : ∃ C : ℝ, 0< C ∧ ∀ χ ψ : Character,
    FiniteFourier.IsPrimitiveOnIdeals ψ.residue → χ.residue≠1 →
    (∀ J : Ideal O, idealCoeff χ J=
      if IsCoprime J χ.modulus then idealCoeff ψ J else 0) →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤ C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
      ‖LFunction χ (1-conj s)‖*
      (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) := by
  obtain ⟨C,hC,hbound⟩ := family_reflected_bound
  refine ⟨C,hC,?_⟩
  intro χ ψ hp hχ hmask s hl hr
  have hψ : ψ.residue≠1 := fun h => hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
  have h := hbound ψ hp hψ s hl hr
  have hd : factors χ.modulus ψ (1-conj s)≠0 := factors_ne_zero _ _ (by simp; linarith)
  have he : LFunction ψ (1-conj s)=LFunction χ (1-conj s)*(factors χ.modulus ψ (1-conj s))⁻¹ := by
    rw [LFunction_eq_of_mask_entire χ ψ hχ hmask]
    field_simp
  rw [he,norm_mul] at h
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (C*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        (‖LFunction χ (1-conj s)‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖))*
          ‖factors χ.modulus ψ s‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem original_reflected_subpower (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ χ : Character, χ.residue≠1 →
    ∀ s : ℂ, -(1/10 : ℝ)≤ s.re → s.re≤1/2 →
    ‖LFunction χ s‖≤ C*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
      (3+|s.im|)^2*‖LFunction χ (1-conj s)‖ := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_bound
  obtain ⟨Cl,hCl,hleft⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound ε hε
  obtain ⟨Cr,hCr,hright⟩ := HeckeDeletionBounds.factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cg*Cl*Cr,by positivity,?_⟩
  intro χ hχ s hl hr
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hR : 0<((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hd₁ := hleft χ.modulus ψ s
  have hd₂ : ‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε := by
    have h := hright χ.modulus ψ (1-conj s) (by simp; linarith)
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans h
  have hd : ‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖≤
      (Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
    calc
      _ ≤ (Cl*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε))*
          (Cr*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) :=
        mul_le_mul hd₁ hd₂ (norm_nonneg _) (mul_nonneg hCl.le (Real.rpow_nonneg hR.le _))
      _ = _ := by
        have he : ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε =
            ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε) := by
          rw [←Real.rpow_add hR]
          congr 1
          ring
        calc
          _ = (Cl*Cr)*(((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+ε)*
              ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^ε) := by ring
          _ = _ := by rw [he]
  have hQ' : (ψ.modulus.absNorm : ℝ)^(1/2-s.re)≤(χ.modulus.absNorm : ℝ)^(1/2-s.re) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by linarith)
  calc
    _ ≤ Cg*(ψ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        (‖factors χ.modulus ψ s‖*‖(factors χ.modulus ψ (1-conj s))⁻¹‖) :=
      hreflect χ ψ hp hχ hmask s hl hr
    _ ≤ Cg*(χ.modulus.absNorm : ℝ)^(1/2-s.re)*(3+|s.im|)^2*
        ‖LFunction χ (1-conj s)‖*
        ((Cl*Cr)*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)) := by
      apply mul_le_mul _ hd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      gcongr
    _ = _ := by ring

end HeckeDyadicReflection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex Set
namespace HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds HeckeDyadicReflection

theorem radical_norm_ge_one (M : Ideal O) : 1≤((HeckeDeletionBounds.radical M).absNorm : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (radical_ne_zero M))

theorem buffered_reflected_line_control (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (s : ℂ), s.re=1-a-6*e → |s.im|≤(3*i+2 : ℕ)*T →
      ‖LFunction (χ j) s‖≤ C*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  obtain ⟨Cg,hCg,hreflect⟩ := original_reflected_subpower ε hε
  obtain ⟨Cb,hCb,hrect⟩ := buffered_rectangle_control e ε he he' hε
  refine ⟨Cg*Cb,mul_pos hCg hCb,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j s hs him
  have hwre : (1-conj s).re=a+6*e := by simp; linarith
  have hwim : (1-conj s).im=s.im := by simp
  have hw := hrect χ hχ T a i hT ha ha' hmax j (1-conj s)
    (by rw [hwre]) (by rw [hwre]; linarith) (by rwa [hwim])
  have hL : ‖LFunction (χ j) (1-conj s)‖≤
      Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans hw.2
  have href := hreflect (χ j) (hχ j) s (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : 1/2-s.re=a-1/2+6*e := by rw [hs]; ring
  rw [hexp] at href
  have hR : ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)≤
      ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε) := by
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤6*e := max_le (by rw [hs]; linarith) (by positivity)
    linarith
  calc
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)^(max (-s.re) 0+2*ε)*
        (3+|s.im|)^2*‖LFunction (χ j) (1-conj s)‖ := href
    _ ≤ Cg*((χ j).modulus.absNorm : ℝ)^(a-1/2+6*e)*
        ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)^(6*e+2*ε)*
        (3+(3*i+2 : ℕ)*T)^2*(Cb*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε) := by
      gcongr
    _ = _ := by ring

theorem original_upper_strip (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0< C ∧ ∀ χ : Character, χ.residue≠1 → ∀ s : ℂ,
      -(1/10 : ℝ)≤ s.re →
      ‖LFunction χ s‖≤ C*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
        ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+ε)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := factors_any_re_subpower_bound ε hε
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp hs
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hQ' : (ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)≤(χ.modulus.absNorm : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤
      Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+ε) := by
    apply (hdel χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    apply Real.rpow_le_rpow_of_exponent_le (radical_norm_ge_one _)
    have hm : max (-s.re) 0≤1/10 := max_le (by linarith) (by norm_num)
    linarith
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  rw [LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+ε)) :=
      mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*(3+|s.im|)^2)*
        (Cd*((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+ε)) := by
      gcongr
      linarith
    _ = _ := by ring

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth HeckeDeletionBounds

theorem reflected_polynomial_bound (e ε : ℝ)
    (he : 0< e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ Cg Cr : ℝ, 0< Cg ∧ 0< Cr ∧
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (D σ freq V C₂ Cn : ℝ) (n : ℕ), 1≤ D → 0≤ V →
      |freq|+V≤(3*i+2 : ℕ)*T → 0≤ C₂ → 0≤ Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      let H := (3*i+2 : ℕ)*T
      let Q := ((χ j).modulus.absNorm : ℝ)
      let R := ((HeckeDeletionBounds.radical (χ j).modulus).absNorm : ℝ)
      let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
      let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
        (presentationComplexity (χ j) H)^ε
      ‖polynomial (χ j) false W D σ freq‖≤(1/(2*Real.pi))*
        (C₂*D^(1/2-a-6*e)*Kr*Real.pi +
         2*(Cn*D^(3/2 : ℝ)*Kg/(1+V)^n)*|1+a+6*e| +
         (Cn*D^(3/2 : ℝ)*HeckeReciprocalBound.bound 2)/(1+V)^n*Real.pi) := by
  obtain ⟨Cg,hCg,hglobal⟩ := original_upper_strip ε hε
  obtain ⟨Cr,hCr,hreflect⟩ := buffered_reflected_line_control e ε he he' hε
  refine ⟨Cg,Cr,hCg,hCr,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    D σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only
  let H : ℝ := (3*i+2 : ℕ)*T
  let Q : ℝ := (χ j).modulus.absNorm
  let R : ℝ := (HeckeDeletionBounds.radical (χ j).modulus).absNorm
  let Kg := Cg*Q^(3/5 : ℝ)*R^(1/10+ε)*(3+H)^2
  let Kr := Cr*Q^(a-1/2+6*e)*R^(6*e+2*ε)*(3+H)^2*
    (presentationComplexity (χ j) H)^ε
  have hKg : 0≤ Kg := by dsimp [Kg,Q,R]; positivity
  have hKr : 0≤ Kr := by dsimp [Kr,Q,R,presentationComplexity,HeckeLogarithmic.complexity]; positivity
  have hlr : 1-a-6*e-σ≤2-σ := by linarith
  have hmem {s : ℂ} (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      1-a-6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧ |(s+shift σ freq).im|≤ H := by
    have h := translated_rectangle_mem (a:=1-a-12*e) (e:=e) (σ:=σ) (freq:=freq)
      (by linarith : 1-a-12*e+6*e≤1-a-6*e-σ+σ)
      (by linarith : 2-σ+σ≤2) hlr hV hfreq hs
    constructor
    · linarith [h.1]
    · exact h.2
  have hseries (s : ℂ) (hs : s ∈ (uIcc (1-a-6*e-σ) (2-σ) ×ℂ uIcc (-V) V)) :
      ‖series (χ j) false (s+shift σ freq)‖≤ Kg := by
    have h := hglobal (χ j) (hχ j) (s+shift σ freq) (by linarith [(hmem hs).1])
    apply h.trans
    dsimp [Kg,Q,R]
    gcongr
    exact (hmem hs).2.2
  have hcentral (t : ℝ) (ht : t∈Icc (-V) V) :
      ‖series (χ j) false (((1-a-6*e-σ : ℝ) : ℂ)+t*I+shift σ freq)‖≤ Kr := by
    have him : |t-freq|≤ H := (abs_sub _ _).trans (by
      have ht' := abs_le.mpr ht
      change |t|+|freq|≤ H
      linarith)
    apply hreflect χ hχ T a i hT ha ha' hmax j
    · simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero,shift_re]
      ring
    · simpa [shift,sub_eq_add_neg,H] using him
  have hb := polynomial_bound_of_rectangle_split (χ j) (hχ j) false W A B hA hWs hW
    D σ freq (1-a-6*e-σ) (2-σ) V C₂ Cn Kg Kr n hD hlr (by linarith)
    hV hC₂ hCn hKg hKr hm₂ hmn hcentral (fun _ _ h => Bool.false_ne_true h |>.elim) hseries
  dsimp only [Kg,Kr,Q,R,H] at hb
  convert hb using 1 ; congr 2 <;> ring_nf

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace HeckeDyadic
open HeckeFamily HeckeDeletionBounds HeckeReciprocalGrowth HeckeLogarithmic

theorem presentation_cost (χ : Character) (U H ε : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (hH : 0≤ H) (hε : 0≤ε) (hε' : ε≤1) :
    (presentationComplexity χ H)^ε≤2*U^(2*ε)*(3+H)^2 := by
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hbase : 1≤3+H := by linarith
  have hc := presentationComplexity_le_of_modulus_le χ U H hQ
  rw [abs_of_nonneg hH] at hc
  have hp : (presentationComplexity χ H)^ε≤(2*U^2*(3+H)^2)^ε :=
    Real.rpow_le_rpow (by unfold presentationComplexity complexity; positivity) hc hε
  have he : (2*U^2*(3+H)^2)^ε=(2 : ℝ)^ε*U^(2*ε)*(3+H)^(2*ε) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) (by positivity)]
    simp only [←Real.rpow_natCast,←Real.rpow_mul (by linarith : 0≤ U),
      ←Real.rpow_mul (by linarith : 0≤3+H),Nat.cast_ofNat]
  rw [he] at hp
  have h2 : (2 : ℝ)^ε≤2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hε'
  have hh : (3+H)^(2*ε)≤(3+H)^2 := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
  exact hp.trans (mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) _))
    hh (Real.rpow_nonneg (by linarith) _) (by positivity))

theorem positive_central_cost (χ : Character) (U H a e ε η r : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (hH : 0≤ H) (hε : 0≤ε) (hε' : ε≤1)
    (hheight : (3+H)^4≤ U^η) :
    (U^r)^(a+6*e-1/2)*(presentationComplexity χ H)^ε≤
      2*U^((a-1/2+6*e)*r+2*ε+η) := by
  have hU : 0< U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hh : (3+H)^2≤ U^η := by
    apply le_trans _ hheight
    exact pow_le_pow_right₀ (by linarith) (by decide : 2≤4)
  calc
    _ ≤ (U^r)^(a+6*e-1/2)*(2*U^(2*ε)*U^η) :=
      mul_le_mul_of_nonneg_left ((presentation_cost χ U H ε hQ hH hε hε').trans
        (mul_le_mul_of_nonneg_left hh (by positivity))) (by positivity)
    _ = _ := by
      rw [positive_scale_exponent U a e r hU]
      rw [Real.rpow_add hU,Real.rpow_add hU]
      ring

theorem reflected_central_cost (χ : Character) (U H a e ε η m : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (hH : 0≤ H) (ha : 1/2≤ a)
    (he : 0≤ e) (hε : 0≤ε) (hε' : ε≤1) (hheight : (3+H)^4≤ U^η) :
    (χ.modulus.absNorm : ℝ)^(a-1/2+6*e)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(6*e+2*ε)*(3+H)^2*
      (presentationComplexity χ H)^ε*(U^m)^(1/2-a-6*e)≤
      2*U^((a-1/2)*(1-m)+6*e*(2-m)+4*ε+η) := by
  have hU : 0< U := lt_of_lt_of_le zero_lt_one ((HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ)
  have hcost := reflected_conductor_cost χ U a e ε hQ ha he hε
  have hcomplex := presentation_cost χ U H ε hQ hH hε hε'
  have hcomplex0 : 0≤(presentationComplexity χ H)^ε := Real.rpow_nonneg (by
    unfold presentationComplexity complexity
    positivity) _
  calc
    _ ≤ U^(a-1/2+12*e+2*ε)*(3+H)^2*(2*U^(2*ε)*(3+H)^2)*(U^m)^(1/2-a-6*e) := by
      gcongr
    _ = 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*(3+H)^4 := by ring
    _ ≤ 2*(U^(a-1/2+12*e+2*ε)*(U^m)^(1/2-a-6*e))*U^(2*ε)*U^η :=
      mul_le_mul_of_nonneg_left hheight (by positivity)
    _ = _ := by
      rw [reflected_scale_exponent U a e ε m hU]
      calc
        _ = 2*(U^((a-1/2)*(1-m)+6*e*(2-m)+2*ε)*U^(2*ε)*U^η) := by ring
        _ = 2*U^(((a-1/2)*(1-m)+6*e*(2-m)+2*ε)+2*ε+η) := by
          rw [←Real.rpow_add hU,←Real.rpow_add hU]
        _ = _ := by congr 2; ring

theorem direct_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (hH : 0≤ H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤ r) (hrR : r≤ R) (hheight : (3+H)^4≤ U^η) :
    (U^r)^(3/2 : ℝ)*(presentationComplexity χ H)^κ≤2*U^(2*R+2+η) := by
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have h := positive_central_cost χ U H 2 0 κ η r hQ hH hκ hκ' hheight
  norm_num only [mul_zero,add_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hU
  nlinarith

theorem reflected_external_cost (χ : Character) (U H κ η r R : ℝ)
    (hQ : (χ.modulus.absNorm : ℝ)≤ U) (hH : 0≤ H) (hκ : 0≤κ) (hκ' : κ≤1)
    (hr : 0≤ r) (hrR : r≤ R) (hheight : (3+H)^4≤ U^η) :
    (U^r)^(3/2 : ℝ)*(χ.modulus.absNorm : ℝ)^(3/5 : ℝ)*
      ((HeckeDeletionBounds.radical χ.modulus).absNorm : ℝ)^(1/10+κ)*(3+H)^2≤ U^(2*R+2+η) := by
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one χ).trans hQ
  have hUp : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hR := (radical_norm_le_modulus χ).trans hQ
  have hh : (3+H)^2≤ U^η :=
    (pow_le_pow_right₀ (by linarith) (by decide : 2≤4)).trans hheight
  calc
    _ ≤ (U^r)^(3/2 : ℝ)*U^(3/5 : ℝ)*U^(1/10+κ)*U^η := by
      gcongr
    _ = U^(r*(3/2)+(3/5)+(1/10+κ)+η) := by
      rw [←Real.rpow_mul hUp.le,←Real.rpow_add hUp,←Real.rpow_add hUp,←Real.rpow_add hUp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_direct_bound (e κ : ℝ) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤ U → 0≤ r → r≤ R → 0≤η → 0≤ V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤ U^η → 0≤ C₂ → 0≤ Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((a+6*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x ∈ Icc (a+6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      ‖polynomial (χ j) inverse W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2+6*e)*r+2*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cb,hCb,hbound⟩ := buffered_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤ E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cb*Real.pi+8*Cb+E*Real.pi
  have hC : 0< C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤ H := by dsimp [H]; positivity
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤ U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j inverse W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := positive_central_cost (χ j) U H a e κ η r hQ hH hκ.le hκ' hheight
  have hexternal := direct_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤ U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |2-a-6*e|≤2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hc : C₂*(U^r)^(a+6*e-1/2)*(Cb*(presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η) := by
    calc
      _ = (C₂*Cb*Real.pi)*((U^r)^(a+6*e-1/2)*(presentationComplexity (χ j) H)^κ) := by ring
      _ ≤ (C₂*Cb*Real.pi)*(2*U^((a-1/2+6*e)*r+2*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cb*(presentationComplexity (χ j) H)^κ)/(1+V)^n)*|2-a-6*e|≤
      (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cb*((U^r)^(3/2 : ℝ)*(presentationComplexity (χ j) H)^κ)/(1+V)^n*|2-a-6*e| := by ring
      _ ≤ 2*Cn*Cb*(2*U^(2*R+2+η))/(1+V)^n*2 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cb*Real.pi≤ C := by dsimp [C]; nlinarith [mul_nonneg hE Real.pi_pos.le]
  have heC : 8*Cb+E*Real.pi≤ C := by dsimp [C]; nlinarith [Real.pi_pos]
  calc
    _ ≤ (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cb*Real.pi)*C₂*U^((a-1/2+6*e)*r+2*κ+η)+
        (8*Cb+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace HeckeDyadic
open HeckeFamily HeckeReciprocalGrowth

theorem scaled_reflected_bound (e κ : ℝ) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hκ' : κ≤1) :
    ∃ C : ℝ, 0< C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2< T → 51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)< a+2*e →
      ∀ (j : ι) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ (U r R η σ freq V C₂ Cn : ℝ) (n : ℕ),
      (χ j).modulus.absNorm≤ U → 0≤ r → r≤ R → 0≤η → 0≤ V →
      |freq|+V≤(3*i+2 : ℕ)*T → (3+(3*i+2 : ℕ)*T)^4≤ U^η → 0≤ C₂ → 0≤ Cn →
      (∀ t : ℝ, (1+|t|)^2*‖mellin W (((1-a-6*e-σ : ℝ) : ℂ)+t*I)‖≤ C₂) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ Cn) →
      ‖polynomial (χ j) false W (U^r) σ freq‖≤
        C*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+C*Cn*U^(2*R+2+η)/(1+V)^n := by
  obtain ⟨Cg,Cr,hCg,hCr,hbound⟩ := reflected_polynomial_bound e κ he he' hκ
  let E := HeckeReciprocalBound.bound 2
  have hE : 0≤ E := tsum_nonneg (fun _ => norm_nonneg _)
  let C := 1+2*Cr*Real.pi+6*Cg+E*Real.pi
  have hC : 0< C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq V C₂ Cn n hQ hr hrR hη hV hfreq hheight hC₂ hCn hm₂ hmn
  let H : ℝ := (3*i+2 : ℕ)*T
  have hH : 0≤ H := by dsimp [H]; positivity
  have hU : 1≤ U := (HeckeLogarithmicInput.modulus_norm_ge_one (χ j)).trans hQ
  have hUp : 0< U := lt_of_lt_of_le zero_lt_one hU
  have hD : 1≤ U^r := Real.one_le_rpow hU hr
  have hb := hbound χ hχ T a i hT ha ha' hmax j W A B hA hWs hW
    (U^r) σ freq V C₂ Cn n hD hV hfreq hC₂ hCn hm₂ hmn
  dsimp only at hb
  have hcentral := reflected_central_cost (χ j) U H a e κ η r hQ hH (by linarith) he.le hκ.le hκ' hheight
  have hexternal := reflected_external_cost (χ j) U H κ η r R hQ hH hκ.le hκ' hr hrR hheight
  have hpow : (U^r)^(3/2 : ℝ)≤ U^(2*R+2+η) := by
    rw [←Real.rpow_mul hUp.le]
    exact Real.rpow_le_rpow_of_exponent_le hU (by nlinarith)
  have hwidth : |1+a+6*e|≤3 := abs_le.mpr ⟨by linarith,by linarith⟩
  let Q : ℝ := (χ j).modulus.absNorm
  let Rad : ℝ := (HeckeDeletionBounds.radical (χ j).modulus).absNorm
  have hc : C₂*(U^r)^(1/2-a-6*e)*(Cr*Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
      (presentationComplexity (χ j) H)^κ)*Real.pi≤
      (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η) := by
    calc
      _ = (C₂*Cr*Real.pi)*(Q^(a-1/2+6*e)*Rad^(6*e+2*κ)*(3+H)^2*
        (presentationComplexity (χ j) H)^κ*(U^r)^(1/2-a-6*e)) := by ring
      _ ≤ (C₂*Cr*Real.pi)*(2*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)) :=
        mul_le_mul_of_nonneg_left hcentral (by positivity)
      _ = _ := by ring
  have hj : 2*(Cn*(U^r)^(3/2 : ℝ)*(Cg*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n)*|1+a+6*e|≤
      (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ = 2*Cn*Cg*((U^r)^(3/2 : ℝ)*Q^(3/5 : ℝ)*Rad^(1/10+κ)*(3+H)^2)/(1+V)^n*|1+a+6*e| := by ring
      _ ≤ 2*Cn*Cg*U^(2*R+2+η)/(1+V)^n*3 := by gcongr
      _ = _ := by ring
  have ht : (Cn*(U^r)^(3/2 : ℝ)*E)/(1+V)^n*Real.pi≤
      (E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
    calc
      _ ≤ (Cn*U^(2*R+2+η)*E)/(1+V)^n*Real.pi := by gcongr
      _ = _ := by ring
  have hfac : 1/(2*Real.pi)≤(1 : ℝ) := by
    apply (div_le_one (by positivity)).mpr
    linarith [Real.pi_gt_three]
  have hcomp : 0≤(presentationComplexity (χ j) H)^κ := Real.rpow_nonneg (by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity) _
  apply (hb.trans (mul_le_of_le_one_left (by positivity) hfac)).trans
  change _ ≤ _ at hc hj ht
  have hcC : 2*Cr*Real.pi≤ C := by dsimp [C]; nlinarith only [hCg,mul_nonneg hE Real.pi_pos.le]
  have heC : 6*Cg+E*Real.pi≤ C := by dsimp [C]; nlinarith only [mul_pos hCr Real.pi_pos]
  calc
    _ ≤ (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg)*Cn*U^(2*R+2+η)/(1+V)^n+(E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by
      exact add_le_add (add_le_add hc hj) ht
    _ = (2*Cr*Real.pi)*C₂*U^((a-1/2)*(1-r)+6*e*(2-r)+4*κ+η)+
        (6*Cg+E*Real.pi)*Cn*U^(2*R+2+η)/(1+V)^n := by ring
    _ ≤ _ := by gcongr

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical Topology ContDiff
open Set Complex
namespace HeckeDyadic
open HeckeFamily

theorem source_dyadic_bounds (R dmax τ ε e κ η : ℝ)
    (hR : 0≤ R) (hdmax : 0≤ dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hη : 0≤η)
    (hbudget : 12*e*(R+2)+8*κ+2*η≤ε)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0≤ profileBound k) :
    ∃ n : ℕ, ∃ C : ℝ, 0< C ∧
    ∀ (Z d : ℝ), 1≤ Z → 0≤ d → d≤ dmax → 2< Z^τ →
    ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*(Z^τ))< a+2*e →
      ∀ (j : ι) (inverse : Bool) (W : ℝ → ℂ) (A B : ℝ),
      0< A → Function.support W⊆Icc A B → ContDiff ℝ ∞ W →
      ∀ r σ freq : ℝ, (χ j).modulus.absNorm≤ Z^d → 0≤ r → r≤ R →
      |freq|+(Z^τ)/2≤(3*i+2 : ℕ)*(Z^τ) →
      (3+(3*i+2 : ℕ)*(Z^τ))^4≤(Z^d)^η →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^2*‖mellin W ((x : ℂ)+t*I)‖≤ profileBound 2) →
      (∀ x ∈ Icc (1-a-6*e-σ) (2-σ), ∀ t : ℝ,
        (1+|t|)^(n+2)*‖mellin W ((x : ℂ)+t*I)‖≤ profileBound (n+2)) →
      ‖polynomial (χ j) inverse W ((Z^d)^r) σ freq‖^2≤ C*(Z^d)^((2*a-1)*r+ε) ∧
      ‖polynomial (χ j) false W ((Z^d)^r) σ freq‖^2≤ C*(Z^d)^((2*a-1)*min r (1-r)+ε) := by
  obtain ⟨Cd,hCd,hdirect⟩ := scaled_direct_bound e κ he he' hκ hκ'
  obtain ⟨Cr,hCr,hreflect⟩ := scaled_reflected_bound e κ he he' hκ hκ'
  obtain ⟨n,htail⟩ := uniform_external_tail_order τ dmax (2*R+2+η) (R+1)
    hτ hdmax (by positivity) (by positivity)
  let K := Cd+Cr
  have hK : 0< K := add_pos hCd hCr
  let M := K*profileBound 2
  let E := K*profileBound (n+2)*(2 : ℝ)^n
  let C := (M+E)^2+1
  have hM : 0≤ M := mul_nonneg hK.le (hprofile 2)
  have hE : 0≤ E := mul_nonneg (mul_nonneg hK.le (hprofile (n+2))) (by positivity)
  refine ⟨n,C,by dsimp [C]; positivity,?_⟩
  intro Z d hZ hd hd' hT ι _ χ hχ a i ha ha' hmax j inverse W A B hA hWs hW
    r σ freq hQ hr hrR hfreq hheight hm₂ hmn
  let U := Z^d
  have hU : 1≤ U := Real.one_le_rpow hZ hd
  have hV : 0≤ Z^τ/2 := by positivity
  have hleft : a+6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨by linarith,by linarith⟩
  have hleft' : 1-a-6*e-σ ∈ Icc (1-a-6*e-σ) (2-σ) := ⟨le_rfl,by linarith⟩
  have hsub : Icc (a+6*e-σ) (2-σ)⊆Icc (1-a-6*e-σ) (2-σ) := by
    intro x hx
    exact ⟨hleft.1.trans hx.1,hx.2⟩
  have hD (inv : Bool) := hdirect χ hχ (Z^τ) a i hT ha ha' hmax j inv W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2))
    (hm₂ _ hleft) (fun x hx => hmn x (hsub hx))
  have hP := hreflect χ hχ (Z^τ) a i hT ha ha' hmax j W A B hA hWs hW
    U r R η σ freq (Z^τ/2) (profileBound 2) (profileBound (n+2)) n hQ hr hrR hη hV
    hfreq hheight (hprofile 2) (hprofile (n+2)) (hm₂ _ hleft') hmn
  have hCdK : Cd≤ K := le_add_of_nonneg_right hCr.le
  have hCrK : Cr≤ K := le_add_of_nonneg_left hCd.le
  have hnormD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖≤
        M*U^((a-1/2)*r+(6*e*r+2*κ+η))+
          K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply (hD inv).trans
    dsimp only [M]
    have hexp : (a-1/2+6*e)*r+2*κ+η=(a-1/2)*r+(6*e*r+2*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hnormP : ‖polynomial (χ j) false W (U^r) σ freq‖≤
      M*U^((a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η))+
        K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n := by
    apply hP.trans
    dsimp only [M]
    have hexp : (a-1/2)*(1-r)+6*e*(2-r)+4*κ+η=
        (a-1/2)*(1-r)+(6*e*(2-r)+4*κ+η) := by ring
    rw [hexp]
    gcongr <;> exact hprofile _
  have hfinish (z : ℂ) (p b : ℝ) (hp : -(R+1)≤ p) (hb : 2*b≤ε)
      (hz : ‖z‖≤ M*U^(p+b)+K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n) :
      ‖z‖^2≤ C*U^(2*p+ε) := by
    have ht := htail Z d p hZ hd hd' hp
    have herror : K*profileBound (n+2)*U^(2*R+2+η)/(1+Z^τ/2)^n≤ E*U^p := by
      calc
        _ = (K*profileBound (n+2))*(U^(2*R+2+η)/(1+Z^τ/2)^n) := by ring
        _ ≤ (K*profileBound (n+2))*((2 : ℝ)^n*U^p) :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg hK.le (hprofile _))
        _ = _ := by dsimp [E]; ring
    have hn := hz.trans (add_le_add (le_refl _) herror)
    have hs := squared_bound_of_central_and_error z U M E p b ε hU hM hE hε.le hb hn
    apply hs.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    dsimp [C]
    linarith
  have hpos : 0≤(a-1/2)*r := mul_nonneg (by linarith) hr
  have href : -(R+1)≤(a-1/2)*(1-r) := by
    have hp : (a-1/2)*r≤(1/2)*R := mul_le_mul (by linarith) hrR hr (by norm_num)
    nlinarith
  have hbud := central_squared_exponents R a e κ η ε r r hR he.le hκ.le hη hrR hr hbudget
  have hbD : 2*(6*e*r+2*κ+η)≤ε := by nlinarith [hbud.1]
  have hbP : 2*(6*e*(2-r)+4*κ+η)≤ε := by nlinarith [hbud.2]
  have hfinalD (inv : Bool) :
      ‖polynomial (χ j) inv W (U^r) σ freq‖^2≤ C*U^((2*a-1)*r+ε) := by
    convert hfinish _ ((a-1/2)*r) (6*e*r+2*κ+η) (by linarith) hbD (hnormD inv) using 1 ;
      congr 2 ; ring
  have hfinalP : ‖polynomial (χ j) false W (U^r) σ freq‖^2≤ C*U^((2*a-1)*(1-r)+ε) := by
    convert hfinish _ ((a-1/2)*(1-r)) (6*e*(2-r)+4*κ+η) href hbP hnormP using 1 ;
      congr 2 ; ring
  exact ⟨hfinalD inverse,min_plain_bound _ C U (2*a-1) r ε (hfinalD false) hfinalP⟩

end HeckeDyadic

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open Set Complex
namespace HeckeDetectorDyadicBridge
lemma norm_phase (x D : ℝ) (hx : 0< x) (hD : 0< D) (s : ℂ) (t : ℝ) :
    (x : ℂ)^(-s)*kernelLogPhase t (Real.log (x/D)) =
      (D : ℂ)^(-s)*((x/D : ℝ) : ℂ)^(-HeckeDyadic.shift s.re (2*Real.pi*t-s.im)) := by
  have hxD : 0< x/D := div_pos hx hD
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxD.ne')]
  rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_log hD.le,
    ← Complex.ofReal_log hxD.le]
  unfold kernelLogPhase HeckeDyadic.shift
  rw [← Complex.exp_add, ← Complex.exp_add, Real.log_div hx.ne' hD.ne']
  congr 1
  have hs : s=(s.re : ℂ)+(s.im : ℂ)*I := (Complex.re_add_im s).symm
  rw [hs]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    sub_zero, add_zero, add_im, mul_im, mul_one, zero_add]
  push_cast
  ring


end HeckeDetectorDyadicBridge

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def twistProfile (W : ℝ→ℂ) (σ freq x : ℝ) : ℂ := W x*(x : ℂ)^(-shift σ freq)

theorem twistProfile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (twistProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [twistProfile,hw])

theorem polynomial_twistProfile (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) :
    polynomial χ inv (twistProfile W σ freq) D 0 0=polynomial χ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp [HeckeDyadic.summand,twistProfile,HeckeDyadic.shift,mul_assoc]

theorem twistProfile_smooth (W : ℝ→ℂ) (σ freq a b : ℝ) (ha : 0< a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (twistProfile W σ freq) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0< x
  · have he : twistProfile W σ freq =ᶠ[nhds x]
        (fun y : ℝ => W y*Complex.exp ((Real.log y : ℂ)*(-shift σ freq))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      unfold twistProfile
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ←Complex.ofReal_log hy.le]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply hW.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp x
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    exact hl.mul contDiffAt_const
  · have hxa : x< a := lt_of_le_of_lt (le_of_not_gt hx) ha
    have he : twistProfile W σ freq =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [twistProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he

end HeckeInverseAmplification

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
