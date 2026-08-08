import GaloisForLFunctions.HTGeometry.MaximalVolumeReplicaTargetSkeletonLaw
import GaloisForLFunctions.HTGeometry.ReturnExcisedMinimalIncidenceRankLaw
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def finiteDesignGram {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) (w : C → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ c, (w c) • Matrix.vecMulVec (target c) (star (target c))

def finiteDesignRows {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) (i : Fin n) : EuclideanSpace ℂ C :=
  WithLp.toLp 2 (fun c => star (target c i))

theorem finiteDesignGram_uniform_eq_gram
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (target : C → Fin n → ℂ) :
    finiteDesignGram target (fun _ => (Fintype.card C : ℝ)⁻¹) =
      (Fintype.card C : ℝ)⁻¹ • Matrix.gram ℂ (finiteDesignRows target) := by
  classical
  ext i j
  simp only [finiteDesignGram, Matrix.sum_apply, Matrix.smul_apply,
    Complex.real_smul, Matrix.vecMulVec, finiteDesignRows,
    Matrix.gram_apply, inner_toLp_eq_finiteComplexInner,
    finiteComplexInner, Matrix.of_apply, Pi.star_apply,
    starRingEnd_apply, star_star]
  rw [Finset.mul_sum]

theorem finiteDesignRows_linearIndependent
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    LinearIndependent ℂ (finiteDesignRows target) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  obtain ⟨b, hb⟩ := exists_targetTuple_det_ne_zero_of_span_eq_top target hspan
  have hzero : (finiteTargetMatrix target b)ᵀ.mulVec (star a) = 0 := by
    ext j
    have hj := congrFun (congrArg WithLp.ofLp ha) (b j)
    simpa [finiteDesignRows, Matrix.mulVec, dotProduct, finiteTargetMatrix,
      mul_comm] using congrArg star hj
  have hunitDet : IsUnit ((finiteTargetMatrix target b)ᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hb
  have hunit : IsUnit (finiteTargetMatrix target b)ᵀ :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunitDet
  have hstar : star a = 0 := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr hunit
    simpa using hzero
  have ha : a = 0 := star_injective (by simpa using hstar)
  exact congrFun ha

theorem finiteDesignGram_uniform_posDef
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (target : C → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    (finiteDesignGram target (fun _ => (Fintype.card C : ℝ)⁻¹)).PosDef := by
  rw [finiteDesignGram_uniform_eq_gram]
  have hcard : (0 : ℝ) < (Fintype.card C : ℝ)⁻¹ := by positivity
  exact (Matrix.posDef_gram_of_linearIndependent
    (finiteDesignRows_linearIndependent target hspan)).smul hcard

theorem finiteDesignGram_posSemidef
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) {w : C → ℝ}
    (hw : w ∈ stdSimplex ℝ C) :
    (finiteDesignGram target w).PosSemidef := by
  classical
  unfold finiteDesignGram
  apply Matrix.posSemidef_sum Finset.univ
  intro c _
  exact (Matrix.posSemidef_vecMulVec_self_star (target c)).smul (hw.1 c)

theorem continuous_finiteDesignGram_det_re
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) :
    Continuous (fun w : C → ℝ => (finiteDesignGram target w).det.re) := by
  unfold finiteDesignGram
  fun_prop

theorem uniformWeight_mem_stdSimplex
    {C : Type*} [Fintype C] [Nonempty C] :
    (fun _ : C => (Fintype.card C : ℝ)⁻¹) ∈ stdSimplex ℝ C := by
  constructor
  · intro c
    positivity
  · simp [nsmul_eq_mul]

theorem exists_finiteDesignGram_det_maximizer
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (target : C → Fin n → ℂ) :
    ∃ w ∈ stdSimplex ℝ C,
      ∀ q ∈ stdSimplex ℝ C,
        (finiteDesignGram target q).det.re ≤
          (finiteDesignGram target w).det.re := by
  classical
  obtain ⟨w, hw, hmax⟩ :=
    (isCompact_stdSimplex ℝ C).exists_isMaxOn
      ⟨(fun _ : C => (Fintype.card C : ℝ)⁻¹),
        uniformWeight_mem_stdSimplex⟩
      (continuous_finiteDesignGram_det_re target).continuousOn
  exact ⟨w, hw, hmax⟩

theorem exists_finiteDesignGram_posDef_maximizer
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (target : C → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C,
      (finiteDesignGram target w).PosDef ∧
      ∀ q ∈ stdSimplex ℝ C,
        (finiteDesignGram target q).det.re ≤
          (finiteDesignGram target w).det.re := by
  classical
  obtain ⟨w, hw, hmax⟩ := exists_finiteDesignGram_det_maximizer target
  have hunif := finiteDesignGram_uniform_posDef target hspan
  have hposUnif : 0 <
      (finiteDesignGram target
        (fun _ : C => (Fintype.card C : ℝ)⁻¹)).det.re := by
    exact (RCLike.pos_iff.mp hunif.det_pos).1
  have hpos : 0 < (finiteDesignGram target w).det.re :=
    lt_of_lt_of_le hposUnif (hmax _ uniformWeight_mem_stdSimplex)
  have hdet : (finiteDesignGram target w).det ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hpd : (finiteDesignGram target w).PosDef :=
    (finiteDesignGram_posSemidef target hw).posDef_iff_det_ne_zero.mpr hdet
  exact ⟨w, hw, hpd, hmax⟩

def finiteDesignLeverage {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) (w : C → ℝ) (c : C) : ℂ :=
  star (target c) ⬝ᵥ (finiteDesignGram target w)⁻¹.mulVec (target c)

def finiteDesignSegment {C : Type*} [DecidableEq C]
    (w : C → ℝ) (c : C) (s : ℝ) : C → ℝ :=
  fun j => (1 - s) * w j + s * if j = c then 1 else 0

theorem finiteDesignSegment_mem_stdSimplex
    {C : Type*} [Fintype C] [DecidableEq C]
    {w : C → ℝ} (hw : w ∈ stdSimplex ℝ C) (c : C)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    finiteDesignSegment w c s ∈ stdSimplex ℝ C := by
  constructor
  · intro j
    unfold finiteDesignSegment
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hs.2) (hw.1 j))
      (mul_nonneg hs.1 (by split <;> simp))
  · simp [finiteDesignSegment, Finset.sum_add_distrib, ← Finset.mul_sum,
      hw.2]

theorem finiteDesignGram_segment
    {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (target : C → Fin n → ℂ) (w : C → ℝ) (c : C) (s : ℝ) :
    finiteDesignGram target (finiteDesignSegment w c s) =
      (1 - s) • finiteDesignGram target w +
        s • Matrix.vecMulVec (target c) (star (target c)) := by
  classical
  ext i j
  simp only [finiteDesignGram, finiteDesignSegment, Matrix.sum_apply,
    Matrix.smul_apply, Complex.real_smul, Matrix.vecMulVec,
    Matrix.add_apply, Matrix.of_apply, Pi.star_apply]
  let A : C → ℂ := fun x ↦ target x i * star (target x j)
  change (∑ x, (((1 - s) * w x + s * if x = c then 1 else 0 : ℝ) : ℂ) * A x) =
    ((1 - s : ℝ) : ℂ) * (∑ x, (w x : ℂ) * A x) + (s : ℂ) * A c
  push_cast
  have hfirst :
      (∑ x, (1 - (s : ℂ)) * ((w x : ℂ) * A x)) =
        (1 - (s : ℂ)) * ∑ x, (w x : ℂ) * A x := by
    rw [Finset.mul_sum]
  have hsecond :
      (∑ x, (s : ℂ) * (((if x = c then 1 else 0 : ℝ) : ℂ) * A x)) =
        (s : ℂ) * A c := by
    calc
      (∑ x, (s : ℂ) * (((if x = c then 1 else 0 : ℝ) : ℂ) * A x)) =
          (s : ℂ) * ∑ x, (((if x = c then 1 else 0 : ℝ) : ℂ) * A x) :=
        (Finset.mul_sum _ _ _).symm
      _ = (s : ℂ) * A c := by
        congr 1
        rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)
          (fun b _ hb => by simp [hb])]
        simp
  calc
    (∑ x, ((1 - (s : ℂ)) * (w x : ℂ) +
        (s : ℂ) * ((if x = c then 1 else 0 : ℝ) : ℂ)) * A x) =
        (∑ x, (1 - (s : ℂ)) * ((w x : ℂ) * A x)) +
          ∑ x, (s : ℂ) *
            (((if x = c then 1 else 0 : ℝ) : ℂ) * A x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (1 - (s : ℂ)) * (∑ x, (w x : ℂ) * A x) +
          (s : ℂ) * A c := by rw [hfirst, hsecond]

theorem det_add_smul_vecMulVec_self_star
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : IsUnit M.det) (v : Fin n → ℂ) (t : ℝ) :
    (M + t • Matrix.vecMulVec v (star v)).det =
      M.det * (1 + (t : ℂ) * (star v ⬝ᵥ M⁻¹.mulVec v)) := by
  classical
  have houter :
      t • Matrix.vecMulVec v (star v) =
        Matrix.replicateCol Unit ((t : ℂ) • v) *
          Matrix.replicateRow Unit (star v) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, mul_assoc]
  rw [houter, Matrix.det_add_replicateCol_mul_replicateRow hM]
  congr 1
  rw [Matrix.det_unique, Matrix.add_apply, Matrix.one_apply_eq]
  congr 1
  simp only [Matrix.mul_apply, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

theorem finiteDesignLeverage_nonneg
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) {w : C → ℝ}
    (hpd : (finiteDesignGram target w).PosDef) (c : C) :
    0 ≤ finiteDesignLeverage target w c := by
  exact hpd.inv.posSemidef.dotProduct_mulVec_nonneg (target c)

theorem finiteDesignGram_segment_det
    {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (target : C → Fin (n + 1) → ℂ) (w : C → ℝ) (c : C) (s : ℝ)
    (hpd : (finiteDesignGram target w).PosDef) (hs : s ≠ 1) :
    (finiteDesignGram target (finiteDesignSegment w c s)).det =
      (finiteDesignGram target w).det *
        ((1 - (s : ℂ)) ^ n *
          ((1 - (s : ℂ)) + (s : ℂ) * finiteDesignLeverage target w c)) := by
  classical
  have hsC : (1 - (s : ℂ)) ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hs.symm)
  have hunit : IsUnit (finiteDesignGram target w).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  have hfactor :
      (1 - s) • finiteDesignGram target w +
          s • Matrix.vecMulVec (target c) (star (target c)) =
        (1 - (s : ℂ)) •
          (finiteDesignGram target w +
            (s / (1 - s) : ℝ) •
              Matrix.vecMulVec (target c) (star (target c))) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      smul_eq_mul]
    field_simp
  have hlev :
      star (target c) ⬝ᵥ (finiteDesignGram target w)⁻¹.mulVec (target c) =
        finiteDesignLeverage target w c := rfl
  rw [finiteDesignGram_segment, hfactor, Matrix.det_smul,
    det_add_smul_vecMulVec_self_star _ hunit _ (s / (1 - s)), hlev,
    Fintype.card_fin]
  push_cast
  field_simp
  ring

theorem finiteDesignLeverage_le_finrank_of_maximal
    {C : Type*} [Fintype C] [DecidableEq C] {n : ℕ}
    (target : C → Fin (n + 1) → ℂ) {w : C → ℝ}
    (hw : w ∈ stdSimplex ℝ C)
    (hpd : (finiteDesignGram target w).PosDef)
    (hmax : ∀ q ∈ stdSimplex ℝ C,
      (finiteDesignGram target q).det.re ≤
        (finiteDesignGram target w).det.re)
    (c : C) :
    (finiteDesignLeverage target w c).re ≤ (n + 1 : ℝ) := by
  let M := finiteDesignGram target w
  let ell := finiteDesignLeverage target w c
  let d := M.det.re
  have hell_nonneg : 0 ≤ ell := finiteDesignLeverage_nonneg target hpd c
  have hell_re_nonneg : 0 ≤ ell.re := (RCLike.nonneg_iff.mp hell_nonneg).1
  have hell_im : ell.im = 0 := (RCLike.nonneg_iff.mp hell_nonneg).2
  have hell_eq : ell = (ell.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hell_im
  have hdet_pos : 0 < M.det := hpd.det_pos
  have hd_pos : 0 < d := (RCLike.pos_iff.mp hdet_pos).1
  have hdet_im : M.det.im = 0 := (RCLike.pos_iff.mp hdet_pos).2
  have hdet_eq : M.det = (d : ℂ) := by
    apply Complex.ext
    · simp [d]
    · simpa using hdet_im
  let g : ℝ → ℝ := fun s =>
    (finiteDesignGram target (finiteDesignSegment w c s)).det.re
  let p : ℝ → ℝ := fun s =>
    d * ((1 - s) ^ n * ((1 - s) + s * ell.re))
  have hgp : ∀ s : ℝ, s ≠ 1 → g s = p s := by
    intro s hs
    show (finiteDesignGram target (finiteDesignSegment w c s)).det.re =
      d * ((1 - s) ^ n * ((1 - s) + s * ell.re))
    rw [finiteDesignGram_segment_det target w c s hpd hs]
    show (M.det *
      ((1 - (s : ℂ)) ^ n * ((1 - (s : ℂ)) + (s : ℂ) * ell))).re = _
    rw [hdet_eq, hell_eq,
      show ((d : ℂ) * ((1 - (s : ℂ)) ^ n *
            ((1 - (s : ℂ)) + (s : ℂ) * (ell.re : ℂ)))) =
          ((d * ((1 - s) ^ n * ((1 - s) + s * ell.re)) : ℝ) : ℂ) by
        push_cast; ring]
    exact Complex.ofReal_re _
  have hpderiv : HasDerivAt p (d * (ell.re - (n + 1 : ℝ))) 0 := by
    have hlin : HasDerivAt (fun s : ℝ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have hpow : HasDerivAt (fun s : ℝ => (1 - s) ^ n) (-(n : ℝ)) 0 := by
      have h := hlin.pow n
      have he : (n : ℝ) * (1 - 0) ^ (n - 1) * (-1) = -(n : ℝ) := by norm_num
      exact he ▸ h
    have hid : HasDerivAt (fun s : ℝ => s * ell.re) ell.re 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const ell.re
    have hmul : HasDerivAt p
        (d * (-(n : ℝ) * ((1 - 0) + 0 * ell.re) +
          (1 - (0 : ℝ)) ^ n * (-1 + ell.re))) 0 :=
      HasDerivAt.const_mul d (hpow.mul (hlin.add hid))
    have hval :
        -(n : ℝ) * ((1 - 0) + 0 * ell.re) +
            (1 - (0 : ℝ)) ^ n * (-1 + ell.re) =
          ell.re - (n + 1 : ℝ) := by
      simp only [sub_zero, zero_mul, add_zero, mul_one, one_pow, one_mul]
      ring
    rw [hval] at hmul
    exact hmul
  have hgeq : g =ᶠ[nhds 0] p := by
    filter_upwards [eventually_ne_nhds (show (0 : ℝ) ≠ 1 by norm_num)] with s hs
    exact hgp s hs
  have hgderiv : HasDerivAt g (d * (ell.re - (n + 1 : ℝ))) 0 :=
    hpderiv.congr_of_eventuallyEq hgeq
  have hgmax : IsMaxOn g (Set.Icc (0 : ℝ) 1) 0 := by
    intro s hs
    change g s ≤ g 0
    have hsimp : finiteDesignSegment w c 0 = w := by
      ext j
      simp [finiteDesignSegment]
    simpa [g, hsimp] using
      hmax (finiteDesignSegment w c s)
        (finiteDesignSegment_mem_stdSimplex hw c hs)
  have htan : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      (show segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 by
        rw [segment_eq_Icc zero_le_one])
  have hderiv_nonpos := hgmax.localize.hasFDerivWithinAt_nonpos
    hgderiv.hasFDerivAt.hasFDerivWithinAt htan
  have hprod : d * (ell.re - (n + 1 : ℝ)) ≤ 0 := by
    simpa using hderiv_nonpos
  show ell.re ≤ (n + 1 : ℝ)
  nlinarith [hprod, hd_pos]

theorem norm_sum_weight_mul_mul_sq_le
    {C : Type*} [Fintype C] (w : C → ℝ) (a b : C → ℂ)
    (hw : ∀ c, 0 ≤ w c) :
    ‖∑ c, (w c : ℂ) * a c * b c‖ ^ 2 ≤
      (∑ c, w c * ‖a c‖ ^ 2) * (∑ c, w c * ‖b c‖ ^ 2) := by
  classical
  let A : C → ℝ := fun c => Real.sqrt (w c) * ‖a c‖
  let B : C → ℝ := fun c => Real.sqrt (w c) * ‖b c‖
  have hsqrt (c : C) : Real.sqrt (w c) * Real.sqrt (w c) = w c :=
    Real.mul_self_sqrt (hw c)
  have hAB : (∑ c, A c * B c) = ∑ c, w c * ‖a c‖ * ‖b c‖ := by
    apply Finset.sum_congr rfl
    intro c _
    dsimp [A, B]
    calc
      Real.sqrt (w c) * ‖a c‖ * (Real.sqrt (w c) * ‖b c‖) =
          (Real.sqrt (w c) * Real.sqrt (w c)) * ‖a c‖ * ‖b c‖ := by ring
      _ = w c * ‖a c‖ * ‖b c‖ := by rw [hsqrt c]
  have hA : (∑ c, A c ^ 2) = ∑ c, w c * ‖a c‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro c _
    dsimp [A]
    calc
      (Real.sqrt (w c) * ‖a c‖) ^ 2 =
          (Real.sqrt (w c) * Real.sqrt (w c)) * ‖a c‖ ^ 2 := by ring
      _ = w c * ‖a c‖ ^ 2 := by rw [hsqrt c]
  have hB : (∑ c, B c ^ 2) = ∑ c, w c * ‖b c‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro c _
    dsimp [B]
    calc
      (Real.sqrt (w c) * ‖b c‖) ^ 2 =
          (Real.sqrt (w c) * Real.sqrt (w c)) * ‖b c‖ ^ 2 := by ring
      _ = w c * ‖b c‖ ^ 2 := by rw [hsqrt c]
  have htri : ‖∑ c, (w c : ℂ) * a c * b c‖ ≤
      ∑ c, w c * ‖a c‖ * ‖b c‖ := by
    calc
      ‖∑ c, (w c : ℂ) * a c * b c‖ ≤
          ∑ c, ‖(w c : ℂ) * a c * b c‖ := norm_sum_le _ _
      _ = ∑ c, w c * ‖a c‖ * ‖b c‖ := by
        apply Finset.sum_congr rfl
        intro c _
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw c)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C) A B
  rw [hAB, hA, hB] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans hcs

theorem finiteComplexInner_sum_smul
    {C α : Type*} [Fintype C] [Fintype α]
    (u : α → ℂ) (a : C → ℂ) (v : C → α → ℂ) :
    finiteComplexInner u (∑ j, a j • v j) =
      ∑ j, a j * finiteComplexInner u (v j) := by
  classical
  simp only [finiteComplexInner, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun x _ => by ring

theorem norm_finiteComplexInner_comm
    {α : Type*} [Fintype α] (u v : α → ℂ) :
    ‖finiteComplexInner u v‖ = ‖finiteComplexInner v u‖ := by
  rw [finiteComplexInner_conj_symm u v]
  simp

theorem mulVec_nonsing_inv_mulVec
    {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α]
    (A : Matrix n n α) (v : n → α) (h : IsUnit A.det) :
    A.mulVec (A⁻¹.mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]

theorem finiteDesignGram_mulVec_expand
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) (w : C → ℝ) (u : Fin n → ℂ) :
    (finiteDesignGram target w).mulVec u =
      ∑ c, ((w c : ℂ) * finiteComplexInner (target c) u) • target c := by
  classical
  funext i
  simp only [finiteDesignGram, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Complex.real_smul, smul_eq_mul, Finset.sum_apply, Pi.smul_apply,
    finiteComplexInner, RCLike.star_def, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun j _ => by ring

theorem finiteDesignGram_quadratic_expand
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) (w : C → ℝ) (u : Fin n → ℂ) :
    star u ⬝ᵥ (finiteDesignGram target w).mulVec u =
      ((∑ c, w c * ‖finiteComplexInner u (target c)‖ ^ 2 : ℝ) : ℂ) := by
  classical
  rw [finiteDesignGram_mulVec_expand, dotProduct, Complex.ofReal_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
    RCLike.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hZ : finiteComplexInner u (target c) = ∑ i, conj (u i) * target c i := rfl
  have hterm :
      (∑ i, conj (u i) *
          ((w c : ℂ) * finiteComplexInner (target c) u * target c i)) =
        (w c : ℂ) * (finiteComplexInner (target c) u *
          finiteComplexInner u (target c)) := by
    rw [hZ, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hterm, finiteComplexInner_conj_symm (target c) u, Complex.ofReal_mul]
  congr 1
  rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]

theorem finiteDesignGram_reconstruct
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) {w : C → ℝ}
    (hpd : (finiteDesignGram target w).PosDef) (c : C) :
    target c = ∑ j,
      ((w j : ℂ) * finiteComplexInner (target j)
        ((finiteDesignGram target w)⁻¹.mulVec (target c))) • target j := by
  have hunit : IsUnit (finiteDesignGram target w).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [← finiteDesignGram_mulVec_expand]
  exact (mulVec_nonsing_inv_mulVec _ _ hunit).symm

theorem finiteDesignLeverage_eq_weighted_dual_energy
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) {w : C → ℝ}
    (hpd : (finiteDesignGram target w).PosDef) (c : C) :
    finiteDesignLeverage target w c =
      ((∑ j, w j * ‖finiteComplexInner (target j)
        ((finiteDesignGram target w)⁻¹.mulVec (target c))‖ ^ 2 : ℝ) : ℂ) := by
  classical
  have hunit : IsUnit (finiteDesignGram target w).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  have hrec := mulVec_nonsing_inv_mulVec (finiteDesignGram target w)
    (target c) hunit
  have hconj :
      star (target c) ⬝ᵥ (finiteDesignGram target w)⁻¹.mulVec (target c) =
        conj (star ((finiteDesignGram target w)⁻¹.mulVec (target c)) ⬝ᵥ
          (finiteDesignGram target w).mulVec
            ((finiteDesignGram target w)⁻¹.mulVec (target c))) := by
    rw [hrec, dotProduct, dotProduct, map_sum]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rw [finiteDesignLeverage, hconj, finiteDesignGram_quadratic_expand,
    Complex.conj_ofReal]
  simp_rw [norm_finiteComplexInner_comm]

theorem finiteDesign_matrixCauchySchwarz
    {C : Type*} [Fintype C] {n : ℕ}
    (target : C → Fin n → ℂ) {w : C → ℝ}
    (hw : ∀ c, 0 ≤ w c)
    (hpd : (finiteDesignGram target w).PosDef)
    (u : Fin n → ℂ) (c : C) :
    ‖finiteComplexInner u (target c)‖ ^ 2 ≤
      (finiteDesignLeverage target w c).re *
        ∑ j, w j * ‖finiteComplexInner u (target j)‖ ^ 2 := by
  classical
  have hinner : finiteComplexInner u (target c) =
      ∑ j, (w j : ℂ) * finiteComplexInner u (target j) *
        finiteComplexInner (target j)
          ((finiteDesignGram target w)⁻¹.mulVec (target c)) := by
    conv_lhs => rw [finiteDesignGram_reconstruct target hpd c]
    rw [finiteComplexInner_sum_smul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hcs := norm_sum_weight_mul_mul_sq_le w
    (fun j => finiteComplexInner u (target j))
    (fun j => finiteComplexInner (target j)
      ((finiteDesignGram target w)⁻¹.mulVec (target c))) hw
  rw [← hinner] at hcs
  rw [finiteDesignLeverage_eq_weighted_dual_energy target hpd c,
    Complex.ofReal_re]
  exact hcs.trans_eq (mul_comm _ _)

/-- A determinant-maximizing probability design exists on the actual finite
endpoint image, is nonsingular, and has leverage at most ambient dimension at
every occupied endpoint. -/
theorem exists_finiteOptimalDesign
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C] {n : ℕ}
    (target : C → Fin (n + 1) → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C,
      (finiteDesignGram target w).PosDef ∧
      ∀ c, (finiteDesignLeverage target w c).re ≤ (n + 1 : ℝ) := by
  obtain ⟨w, hw, hpd, hmax⟩ :=
    exists_finiteDesignGram_posDef_maximizer target hspan
  exact ⟨w, hw, hpd,
    finiteDesignLeverage_le_finrank_of_maximal target hw hpd hmax⟩

/-- **Sharp incidence-normalized endpoint design law.**  One probability
measure supported on actual occupied endpoints controls every endpoint probe
simultaneously with the exact ambient-dimension factor. -/
theorem exists_finiteOptimalDesign_pointwise
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C] {n : ℕ}
    (target : C → Fin (n + 1) → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    ∃ w ∈ stdSimplex ℝ C,
      ∀ (u : Fin (n + 1) → ℂ) (c : C),
        ‖finiteComplexInner u (target c)‖ ^ 2 ≤
          (n + 1 : ℝ) *
            ∑ j, w j * ‖finiteComplexInner u (target j)‖ ^ 2 := by
  obtain ⟨w, hw, hpd, hlev⟩ := exists_finiteOptimalDesign target hspan
  refine ⟨w, hw, ?_⟩
  intro u c
  let q : ℝ := ∑ j, w j * ‖finiteComplexInner u (target j)‖ ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun j _ ↦
    mul_nonneg (hw.1 j) (sq_nonneg _)
  calc
    ‖finiteComplexInner u (target c)‖ ^ 2 ≤
        (finiteDesignLeverage target w c).re * q :=
      finiteDesign_matrixCauchySchwarz target hw.1 hpd u c
    _ ≤ (n + 1 : ℝ) * q :=
      mul_le_mul_of_nonneg_right (hlev c) hq

/-- Endpoint coordinate vector is exactly the occupied-span coordinate map
evaluated on that endpoint. -/
theorem replicaTargetCoordinateVector_eq_coordinate
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ)
    (c : C) :
    replicaTargetCoordinateVector r target c =
      replicaTargetCoordinate r target (target c) := by
  funext i
  unfold replicaTargetCoordinateVector replicaTargetCoordinateEquiv
    replicaTargetCoordinate replicaSubspaceCoordinate
    replicaTargetVectorInSpan replicaTargetOrthonormalBasis
    replicaSubspaceOrthonormalBasis
  simp [OrthonormalBasis.repr_apply_apply]

/-- Occupied-span coordinates preserve the inner product against every actual
replica endpoint, including for source vectors outside the occupied span. -/
theorem finiteComplexInner_replicaTargetCoordinate_endpoint
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ)
    (ψ : α → ℂ) (c : C) :
    finiteComplexInner
        (replicaTargetCoordinate r target ψ)
        (replicaTargetCoordinate r target (target c)) =
      inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r (target c)) := by
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r (target c)
  have hv : v ∈ S := Submodule.subset_span (Set.mem_range_self c)
  let vS : S := ⟨v, hv⟩
  rw [finiteComplexInner]
  change (∑ i,
      star (replicaSubspaceCoordinate r S ψ i) *
        replicaSubspaceCoordinate r S (target c) i) = _
  rw [sum_star_replicaSubspaceCoordinate_mul_eq_inner_projection]
  have hvproj : S.orthogonalProjectionOnto v = vS :=
    S.orthogonalProjectionOnto_mem_subspace_eq_self vS
  rw [hvproj]
  exact S.inner_orthogonalProjectionOnto_eq_of_mem_right vS u

/-- A nonempty family of normalized endpoints has nonzero occupied replica
dimension at every replica order. -/
theorem replicaTargetSpan_finrank_pos_of_normalized
    {C α : Type*} [Nonempty C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    0 < Module.finrank ℂ (replicaTargetSpan r target) := by
  let c : C := Classical.choice (inferInstance : Nonempty C)
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨replicaTargetVectorInSpan r target c, ?_⟩
  intro hz
  have hval := congrArg (fun z : replicaTargetSpan r target ↦
    ‖(z : EuclideanSpace ℂ (Fin r → α))‖) hz
  have hnorm := norm_finitePureTensorPowerEuclidean_eq_one
    r (target c) (htarget c)
  simp [replicaTargetVectorInSpan, hnorm] at hval

/-- **Sharp occupied-endpoint replica design law.**  A single probability
design on actual endpoints controls complete replica capture with one factor
of occupied Hilbert number, independently of target-label cardinality. -/
theorem exists_replicaTarget_optimalDesign_pointwise
    {C α : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1) :
    ∃ w ∈ stdSimplex ℝ C,
      ∀ (ψ : α → ℂ) (c : C),
        finitePureStateFidelity ψ (target c) ^ r ≤
          (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ j, w j *
              finitePureStateFidelity ψ (target j) ^ r := by
  classical
  have hpos := replicaTargetSpan_finrank_pos_of_normalized r target htarget
  have hspan := span_replicaTargetCoordinateVector_eq_top r target
  have key : ∀ (m : ℕ) (T : C → Fin m → ℂ), 0 < m →
      Submodule.span ℂ (Set.range T) = ⊤ →
      ∃ w ∈ stdSimplex ℝ C, ∀ (u : Fin m → ℂ) (c : C),
        ‖finiteComplexInner u (T c)‖ ^ 2 ≤
          (m : ℝ) * ∑ j, w j * ‖finiteComplexInner u (T j)‖ ^ 2 := by
    rintro (_ | m) T hm hspanT
    · exact absurd hm (lt_irrefl 0)
    · simpa using exists_finiteOptimalDesign_pointwise T hspanT
  obtain ⟨w, hw, hdesign⟩ := key _
    (fun c ↦ replicaTargetCoordinateVector r target c) hpos hspan
  refine ⟨w, hw, ?_⟩
  intro ψ c
  have hbound := hdesign (replicaTargetCoordinate r target ψ) c
  simp_rw [replicaTargetCoordinateVector_eq_coordinate] at hbound
  simp_rw [finiteComplexInner_replicaTargetCoordinate_endpoint] at hbound
  simp_rw [← finitePureStateFidelity_pow_eq_replica_inner_norm_sq] at hbound
  exact hbound

/-- **Return-excised quenched incidence-normalized coarea law.**  One
probability design on the actual occupied endpoint image bounds the complete
capture event after return removal.  Integration stays on the original
restricted source measure, so every surviving fibre sheet retains its full
multiplicity. -/
theorem measure_completeTargetCapture_le_optimalDesignMoments
    {X C α : Type*} [MeasurableSpace X]
    [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ}
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : ∀ c, Integrable
      (fun x ↦ finitePureStateFidelity (state x) (target c) ^ r)
        (μ.restrict returnSetᶜ)) :
    ∃ w ∈ stdSimplex ℝ C,
      threshold ^ r *
          (μ.restrict returnSetᶜ).real {x | ∃ c,
            threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ c, w c * ∫ x,
            finitePureStateFidelity (state x) (target c) ^ r
              ∂(μ.restrict returnSetᶜ) ∧
      μ.real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
        μ.real returnSet +
          ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ c, w c * ∫ x,
              finitePureStateFidelity (state x) (target c) ^ r
                ∂(μ.restrict returnSetᶜ)) / threshold ^ r := by
  classical
  obtain ⟨w, hw, hpoint⟩ :=
    exists_replicaTarget_optimalDesign_pointwise r target htarget
  refine ⟨w, hw, ?_⟩
  let ν : Measure X := μ.restrict returnSetᶜ
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  let q : X → ℝ := fun x ↦
    (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
      ∑ c, w c * finitePureStateFidelity (state x) (target c) ^ r
  have hEQ : E ⊆ {x | threshold ^ r ≤ q x} := by
    intro x hx
    obtain ⟨c, hc⟩ := hx
    calc
      threshold ^ r ≤ finitePureStateFidelity (state x) (target c) ^ r :=
        pow_le_pow_left₀ hthreshold.le hc r
      _ ≤ q x := hpoint (state x) c
  have hintq : Integrable q ν := by
    dsimp [q, ν]
    apply Integrable.const_mul
    exact integrable_finsetSum Finset.univ fun c _ ↦
      (hint c).const_mul (w c)
  have hqnonneg : 0 ≤ᵐ[ν] q :=
    Filter.Eventually.of_forall fun x ↦ by
      dsimp [q]
      exact mul_nonneg (Nat.cast_nonneg _) <|
        Finset.sum_nonneg fun c _ ↦
          mul_nonneg (hw.1 c) (pow_nonneg (sq_nonneg _) r)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hintq (threshold ^ r)
  have hscaled : threshold ^ r * ν.real E ≤ ∫ x, q x ∂ν := by
    calc
      threshold ^ r * ν.real E ≤
          threshold ^ r * ν.real {x | threshold ^ r ≤ q x} := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono hEQ (by finiteness))
          (pow_nonneg hthreshold.le r)
      _ ≤ ∫ x, q x ∂ν := hmarkov
  have hqIntegral :
      (∫ x, q x ∂ν) =
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ c, w c * ∫ x,
            finitePureStateFidelity (state x) (target c) ^ r ∂ν := by
    dsimp [q]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ
      (fun c _ ↦ (hint c).const_mul (w c))]
    apply congrArg
    apply Finset.sum_congr rfl
    intro c _
    rw [integral_const_mul]
  have hscaled' :
      threshold ^ r * ν.real E ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ c, w c * ∫ x,
            finitePureStateFidelity (state x) (target c) ^ r ∂ν := by
    rwa [hqIntegral] at hscaled
  constructor
  · simpa [E, ν] using hscaled'
  · have hresidual :
        ν.real E ≤
          ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ c, w c * ∫ x,
              finitePureStateFidelity (state x) (target c) ^ r ∂ν) /
                threshold ^ r := by
      apply (le_div_iff₀' (pow_pos hthreshold r)).2
      simpa [mul_comm] using hscaled'
    have hcut := measureReal_capture_le_return_add_restrict_compl
      μ target state threshold returnSet hreturn
    exact hcut.trans (by
      simpa [E, ν] using add_le_add_left hresidual (μ.real returnSet))

/-- Uniform fixed-endpoint consequence.  The complete endpoint union costs
exactly one occupied-Hilbert-number factor, improving the maximal-volume
skeleton's quadratic factor. -/
theorem measure_completeTargetCapture_le_hilbert_mul_fixedMoment
    {X C α : Type*} [MeasurableSpace X]
    [Fintype C] [Nonempty C] [DecidableEq C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ}
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (fixedMoment : ℝ)
    (hint : ∀ c, Integrable
      (fun x ↦ finitePureStateFidelity (state x) (target c) ^ r)
        (μ.restrict returnSetᶜ))
    (hmoment : ∀ c,
      (∫ x, finitePureStateFidelity (state x) (target c) ^ r
        ∂(μ.restrict returnSetᶜ)) ≤ fixedMoment) :
    μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          fixedMoment) / threshold ^ r := by
  classical
  obtain ⟨w, hw, -, hcap⟩ :=
    measure_completeTargetCapture_le_optimalDesignMoments
      μ target state htarget threshold hthreshold returnSet hreturn hint
  have hweighted :
      (∑ c, w c * ∫ x,
        finitePureStateFidelity (state x) (target c) ^ r
          ∂(μ.restrict returnSetᶜ)) ≤ fixedMoment := by
    calc
      (∑ c, w c * ∫ x,
          finitePureStateFidelity (state x) (target c) ^ r
            ∂(μ.restrict returnSetᶜ)) ≤
          ∑ c, w c * fixedMoment := by
        exact Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (hmoment c) (hw.1 c)
      _ = fixedMoment := by rw [← Finset.sum_mul, hw.2, one_mul]
  have hscaled := mul_le_mul_of_nonneg_left hweighted
    (show 0 ≤ (Module.finrank ℂ
      (replicaTargetSpan r target) : ℝ) by positivity)
  have hdiv := (div_le_div_iff_of_pos_right
    (pow_pos hthreshold r)).2 hscaled
  exact hcap.trans (by linarith [hdiv])

/-- The dimension coefficient in the endpoint-design law is universally
sharp.  Already an orthonormal family of `n+1` endpoints forces every
probability design to pay at least `n+1`. -/
theorem finiteOptimalDesign_dimension_factor_sharp
    {n : ℕ} (w : Fin (n + 1) → ℝ)
    (hw : w ∈ stdSimplex ℝ (Fin (n + 1))) {K : ℝ}
    (hbound : ∀ (u : Fin (n + 1) → ℂ) (c : Fin (n + 1)),
      ‖finiteComplexInner u (fun i ↦ if i = c then 1 else 0)‖ ^ 2 ≤
        K * ∑ j, w j *
          ‖finiteComplexInner u (fun i ↦ if i = j then 1 else 0)‖ ^ 2) :
    (n + 1 : ℝ) ≤ K := by
  classical
  have hone (c : Fin (n + 1)) : 1 ≤ K * w c := by
    have hc := hbound (fun i ↦ if i = c then 1 else 0) c
    simpa [finiteComplexInner, apply_ite (fun z : ℂ => ‖z‖),
      Finset.sum_ite_eq'] using hc
  calc
    (n + 1 : ℝ) = ∑ _c : Fin (n + 1), (1 : ℝ) := by simp
    _ ≤ ∑ c, K * w c := Finset.sum_le_sum fun c _ ↦ hone c
    _ = K := by rw [← Finset.mul_sum, hw.2, mul_one]

end

end GaloisForLFunctions.HTGeometry
