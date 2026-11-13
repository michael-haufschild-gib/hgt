/-
Canonical rank induction adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.ReopenedCanonicalRows

/-!
# Canonical rank induction

The fixed-depth logarithmic rank `fixedDepthRank` drops by at least one for each retained child;
canonical rank mass and live scale bounds; two-passage height bounds of the reopened rows.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

/-- Each retained child drops this logarithmic rank by at least one. -/
def fixedDepthRank (Z K : ℝ) : ℕ := ⌈1000*Real.log K/Real.log Z⌉₊

theorem fixedDepthRank_initial (Z K : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hstart : K ≤ Z^3) : fixedDepthRank Z K ≤ 3000 := by
  have hz := Real.log_pos hZ
  have hl := Real.log_le_log hK hstart
  rw [Real.log_pow] at hl
  apply Nat.ceil_le.mpr
  change 1000*Real.log K/Real.log Z ≤ (3000:ℝ)
  apply (div_le_iff₀ hz).mpr
  norm_num at hl
  linarith

theorem fixedDepthRank_step (Z K K' : ℝ) (hZ : 1 < Z) (hK : 0 < K)
    (hK' : 1 ≤ K') (hstep : K' ≤ K/Z^((1:ℝ)/1000)) :
    fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K := by
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hz := Real.log_pos hZ
  have hk0 : 0 < K' := lt_of_lt_of_le zero_lt_one hK'
  have hl := Real.log_le_log hk0 hstep
  rw [Real.log_div hK.ne' (Real.rpow_pos_of_pos hz0 _).ne',Real.log_rpow hz0] at hl
  have ha : 0 ≤ 1000*Real.log K'/Real.log Z := by
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hK')) hz.le
  have hb : 1000*Real.log K'/Real.log Z+1 ≤ 1000*Real.log K/Real.log Z := by
    apply (le_div_iff₀ hz).mpr
    field_simp
    nlinarith
  have hn := Nat.ceil_mono hb
  rw [Nat.ceil_add_one ha] at hn
  exact hn

theorem fixedDepthRank_path (Z : ℝ) (hZ : 1 < Z) (K : ℕ → ℝ) (n : ℕ)
    (hK : ∀ i,i ≤ n → 1 ≤ K i) (hstart : K 0 ≤ Z^3)
    (hstep : ∀ i,i < n → K (i+1) ≤ K i/Z^((1:ℝ)/1000)) : n+1 ≤ 3001 := by
  have hiter : ∀ i,i ≤ n → fixedDepthRank Z (K i)+i ≤ fixedDepthRank Z (K 0) := by
    intro i
    induction i with
    | zero => simp
    | succ i hi =>
      intro hin
      have hip : i ≤ n := by omega
      have hil : i < n := by omega
      have hprev := hi hip
      have hs := fixedDepthRank_step Z (K i) (K (i+1)) hZ
        (lt_of_lt_of_le zero_lt_one (hK i hip)) (hK (i+1) hin) (hstep i hil)
      omega
  have ht := hiter n le_rfl
  have hb := fixedDepthRank_initial Z (K 0) hZ
    (lt_of_lt_of_le zero_lt_one (hK 0 (Nat.zero_le _))) hstart
  omega

theorem globalPooledDelta_ge (B F : ℝ) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (j : GlobalLogIndex) : B*F ≤ globalPooledDelta B F j := by
  have h0 := globalLogRep_ge_one j 0
  have h2 := globalLogRep_ge_one j 2
  have h3 := globalLogRep_ge_one j 3
  unfold globalPooledDelta
  calc
    B*F = B*F*1*1*1 := by ring
    _ ≤ _ := by gcongr

theorem globalPooledNaturalRow_pos (K B F : ℝ) (hK : 0 < K) (hB : 0 < B)
    (hF : 0 < F) (j : GlobalLogIndex) : 0 < globalPooledNaturalRow K B F j := by
  unfold globalPooledNaturalRow
  exact div_pos (mul_pos hK (globalLogRep_pos j 4))
    (mul_pos (sq_pos_of_pos (globalPooledDelta_pos B F hB hF j)) (sq_pos_of_pos hB))

theorem globalPooledNaturalRow_bound (K B F : ℝ) (hK : 0 < K) (hB : 0 < B)
    (hF : 0 < F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2) :
    globalPooledNaturalRow K B F j ≤ K/(globalPooledDelta B F j)^2 := by
  have hD := globalPooledDelta_pos B F hB hF j
  unfold globalPooledNaturalRow
  calc
    K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2) ≤
      K*B^2/((globalPooledDelta B F j)^2*B^2) := by gcongr
    _ = _ := by field_simp

theorem globalPooledRow_contraction (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) (hJ : globalLogRep j 4 ≤ B^2)
    (hretained : globalBinRadial ell (globalPooledRowScale K ell B F j) j ≤ globalPooledDelta B F j) :
    globalLogRep j 8*Real.exp 1 ≤ K/globalPooledDelta B F j := by
  have hD := globalPooledDelta_pos B F hB hF j
  have hN := globalPooledNaturalRow_pos K B F hK hB hF j
  have hn := globalPooledNaturalRow_bound K B F hK hB hF j hJ
  have hr := hretained
  rw [globalBinRadial,globalPooled_radial_ratio K ell B F hK hell hB hF] at hr
  have hr' : globalLogRep j 8*Real.exp 1 ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := by
    apply (div_le_iff₀ hN).mp
    simpa only [mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using hr
  calc
    _ ≤ globalPooledDelta B F j*globalPooledNaturalRow K B F j := hr'
    _ ≤ globalPooledDelta B F j*(K/(globalPooledDelta B F j)^2) := by gcongr
    _ = _ := by field_simp

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalActualBin_fixed_depth (Z K ell B F : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 0 < F)
    (hprogress : Z^((1:ℝ)/1000) ≤ B*F)
    (hstart : K ≤ Z^3) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hretained : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x) ≤ globalPooledDelta B F (globalScaleIndex p side x)) :
    let K' := globalLogRep (globalScaleIndex p side x) 8*Real.exp 1
    K' ≤ K/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z K'+1 ≤ fixedDepthRank Z K ∧
      fixedDepthRank Z K ≤ 3000 := by
  dsimp only
  have hrow := globalPooledRow_contraction K ell B F hK hell hB hF (globalScaleIndex p side x)
    (globalPooled_J_bound p hp B hB.le side x hk hb₁ hb₂) hretained
  have hD := hprogress.trans (globalPooledDelta_ge B F hB.le hF.le (globalScaleIndex p side x))
  have hz0 : 0 < Z := lt_trans zero_lt_one hZ
  have hsmall : globalLogRep (globalScaleIndex p side x) 8*Real.exp 1 ≤ K/Z^((1:ℝ)/1000) :=
    hrow.trans (div_le_div_of_nonneg_left hK.le (Real.rpow_pos_of_pos hz0 _) hD)
  have hchild : 1 ≤ globalLogRep (globalScaleIndex p side x) 8*Real.exp 1 :=
    one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one _ _) (Real.one_le_exp (by norm_num))
  exact ⟨hsmall,fixedDepthRank_step Z K _ hZ hK hchild hsmall,
    fixedDepthRank_initial Z K hZ hK hstart⟩
theorem fixedDepthRank_zero_iff (Z K : ℝ) (hZ : 1<Z) (hK : 0<K) :
    fixedDepthRank Z K=0 ↔ K≤1 := by
  rw [fixedDepthRank,Nat.ceil_eq_zero]
  constructor
  · intro h
    have hm := (div_le_iff₀ (Real.log_pos hZ)).mp h
    apply (Real.log_nonpos_iff hK.le).mp
    nlinarith
  · intro h
    apply (div_le_iff₀ (Real.log_pos hZ)).mpr
    have hm := (Real.log_nonpos_iff hK.le).mpr h
    nlinarith

theorem smallColumn_row_le_label (m : O) (hm : m≠0) (X F K : ℝ)
    (hX : X≤1) (hF : 0≤F) (hK : 0≤K)
    (hinv : K*‖ringComplex m‖^2≤X*F) : K≤F := by
  have hn := element_norm_ge_one m hm
  have h1 := mul_le_mul_of_nonneg_left hn hK
  have h2 := mul_le_mul_of_nonneg_right hX hF
  nlinarith

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

def canonicalRankMass (Z : ℝ) (r : ℕ) : ℝ :=
  Real.exp (3*((3000-r:ℕ):ℝ))*Z^2

theorem canonicalRankMass_initial (Z : ℝ) (r : ℕ) : Z^2≤canonicalRankMass Z r := by
  have he : 1≤Real.exp (3*((3000-r:ℕ):ℝ)) := Real.one_le_exp (by positivity)
  simpa only [one_mul,canonicalRankMass] using mul_le_mul_of_nonneg_right he (sq_nonneg Z)

theorem canonicalRankMass_step (Z : ℝ) (r s : ℕ) (hr : r≤3000) (hs : s+1≤r) :
    Real.exp 3*canonicalRankMass Z r≤canonicalRankMass Z s := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMass
  rw [←mul_assoc,←Real.exp_add]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg Z)

theorem canonicalRankMass_child (Z X F X' F' : ℝ) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) (hparent : X*F≤canonicalRankMass Z r)
    (hchild : X'*F'≤Real.exp 3*(X*F)) : X'*F'≤canonicalRankMass Z s :=
  hchild.trans ((mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le).trans
    (canonicalRankMass_step Z r s hr hs))

theorem canonicalRankMass_global (Z : ℝ) (hZ : Real.exp 9000≤Z) (r : ℕ) :
    canonicalRankMass Z r≤Z^3 := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  have he : Real.exp (3*((3000-r:ℕ):ℝ))≤Z :=
    (Real.exp_le_exp.mpr (by linarith)).trans hZ
  calc
    canonicalRankMass Z r ≤ Z*Z^2 := mul_le_mul_of_nonneg_right he (sq_nonneg Z)
    _ = Z^3 := by ring

theorem lowerCubeBin_transfer_mass (X B F : ℝ) (hB : B≠0) :
    (X/B^3)*(Real.exp 1*B)^3*F=Real.exp 3*(X*F) := by
  have he : (Real.exp 1)^3=Real.exp 3 := by
    rw [show (3:ℝ)=1+1+1 by norm_num,Real.exp_add,Real.exp_add]
    ring
  rw [mul_pow,←he]
  field_simp

theorem lowerCubeBin_energy_normalization (ell B F : ℝ) (hell : 0<ell) (hB : 0<B) :
    (ell*B^3)*((B*Real.sqrt ell)^2)⁻¹*
      (ell*(Real.exp 1*B)^2*F)*(ell*(Real.exp 1*B)^3*F)=
      Real.exp 5*((ell*B^3)*F)^2 := by
  have he : (Real.exp 1)^5=Real.exp 5 := by
    rw [show (5:ℝ)=1+1+1+1+1 by norm_num]
    simp only [Real.exp_add]
    ring
  rw [mul_pow,Real.sq_sqrt hell.le]
  simp only [mul_pow]
  rw [←he]
  field_simp

theorem canonical_live_scale_bounds (Z X F : ℝ) (r : ℕ)
    (hZ : Real.exp 9000≤Z) (hX : 1≤X) (hF : 1≤F)
    (hmass : X*F≤canonicalRankMass Z r) : X≤Z^3 ∧ F≤Z^3 := by
  have hm := hmass.trans (canonicalRankMass_global Z hZ r)
  constructor <;> nlinarith

theorem canonical_small_or_live (Z X F K : ℝ) (r : ℕ) (m : O)
    (hZ : Real.exp 9000≤Z) (_hX : 0<X) (hF : 1≤F) (hK : 0≤K) (hm : m≠0)
    (hmass : X*F≤canonicalRankMass Z r) (hinv : K*‖ringComplex m‖^2≤X*F) :
    K≤F ∨ (1<X ∧ X≤Z^3 ∧ F≤Z^3) := by
  by_cases hx : X≤1
  · exact Or.inl (smallColumn_row_le_label m hm X F K hx (by linarith) hK hinv)
  · have hl := lt_of_not_ge hx
    exact Or.inr ⟨hl,canonical_live_scale_bounds Z X F r hZ hl.le hF hmass⟩

def canonicalPoolCutoff (Bsupport Z : ℝ) : ℕ := ⌈Bsupport*Z^3⌉₊

theorem canonicalPoolCutoff_covers (Bsupport b Z X : ℝ)
    (hB : 0≤Bsupport) (hb : b≤Bsupport) (hX : 0≤X) (hXZ : X≤Z^3) :
    b*X≤(canonicalPoolCutoff Bsupport Z:ℝ) := by
  calc
    b*X ≤ Bsupport*X := mul_le_mul_of_nonneg_right hb hX
    _ ≤ Bsupport*Z^3 := mul_le_mul_of_nonneg_left hXZ hB
    _ ≤ _ := Nat.le_ceil _

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalBin_mask_bound (B F : ℝ) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    ‖ringComplex (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 ≤
      ‖ringComplex m‖^2*(Real.exp 1)^2*globalPooledDelta B F (globalScaleIndex p side x) := by
  let j := globalScaleIndex p side x
  have hb0 := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos B hB.le hb₁ hb₂).2.1
  change ‖ringComplex (globalFirstBadLabel p x.first)‖^2 ≤ B at hb0
  have he : ‖ringComplex (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 =
      ‖ringComplex (globalSecondMask p m x)‖^2 := by
    rw [ringComplex_norm_sq_eq_absNorm_span,ringComplex_norm_sq_eq_absNorm_span,globalSecondMask_span]
  rw [he]
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have ht0 := (primeProductNorm_pos p hp x.firstCommon).le
  have hr0 := (primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hj2 := (globalLogRep_pos j 2).le
  have hj3 := (globalLogRep_pos j 3).le
  have ha := globalLogRep_ge_one j 0
  change ‖ringComplex ((m*_*_)*∏ i∈x.firstCommon,p i)‖^2 ≤ _
  simp only [map_mul,norm_mul,mul_pow]
  change ‖ringComplex m‖^2*‖ringComplex (globalFirstBadLabel p x.first)‖^2*
    primeProductNorm p (x.source.sourceCommon\x.source.divisor)*primeProductNorm p x.firstCommon≤_
  calc
    _ ≤ ‖ringComplex m‖^2*B*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by gcongr
    _ ≤ ‖ringComplex m‖^2*(B*F*globalLogRep j 0)*(globalLogRep j 3*Real.exp 1)*(globalLogRep j 2*Real.exp 1) := by
      gcongr
      calc
        B = B*1*1 := by ring
        _ ≤ _ := by gcongr
    _ = _ := by unfold globalPooledDelta;ring

include hp in

theorem globalBin_invariant (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 1 ≤ F) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖ringComplex (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    (globalBinRadial ell (globalPooledRowScale K ell B F j) j/(Real.exp 1)^2)*
      (K*‖ringComplex m‖^2/((ell*B^3)*F)) := by
  dsimp only
  let j := globalScaleIndex p side x
  have hm := globalBin_mask_bound p hp B F hB hF side x hk m hb₁ hb₂
  have hcol := globalPooledColumnScale_pos ell hell j
  have hlab : 0 < globalPooledLabelScale j := zero_lt_one.trans_le (globalPooledLabelScale_ge_one j)
  have hk8 := globalLogRep_pos j 8
  have hF0 : 0 < F := zero_lt_one.trans_le hF
  calc
    _ ≤ (globalLogRep j 8*Real.exp 1)*
        (‖ringComplex m‖^2*(Real.exp 1)^2*globalPooledDelta B F j)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j) := by gcongr
    _ = _ := by
      have h (i : Fin 10) := (globalLogRep_pos j i).ne'
      have he : Real.exp 4=(Real.exp 1)^4 := by simp
      dsimp only [j] at h ⊢
      unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta globalPooledRowScale globalBinRadial
      rw [he]
      unfold globalPooledColumnScale
      field_simp [h]

include hp in
theorem globalBin_invariant_small_padding (Z η K ell B F : ℝ) (hZ : 1 < Z)
    (hK : 0 < K) (hell : 0 < ell) (hB : 0 < B) (hF : 1 ≤ F)
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (m : O)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B)
    (hpad : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x) ≤ Z^η) :
    let j := globalScaleIndex p side x
    (globalLogRep j 8*Real.exp 1)*‖ringComplex (fixedTripleMask m (globalSecondFixedTriple p x))‖^2 /
      (globalPooledColumnScale ell j*globalPooledLabelScale j) ≤
    Z^η*(K*‖ringComplex m‖^2/((ell*B^3)*F)) := by
  dsimp only
  apply (globalBin_invariant p hp K ell B F hK hell hB hF side x hk m hb₁ hb₂).trans
  have hz0 : 0 < Z := zero_lt_one.trans hZ
  have hpow : 0 ≤ Z^η := (Real.rpow_pos_of_pos hz0 η).le
  have he : 1 ≤ (Real.exp 1)^2 := one_le_pow₀ (Real.one_le_exp (by norm_num))
  have hr : globalBinRadial ell (globalPooledRowScale K ell B F (globalScaleIndex p side x))
      (globalScaleIndex p side x)/(Real.exp 1)^2 ≤ Z^η :=
    (div_le_iff₀ (sq_pos_of_pos (Real.exp_pos 1))).mpr (hpad.trans (le_mul_of_one_le_right hpow he))
  apply mul_le_mul_of_nonneg_right hr
  positivity

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem globalPooled_mass_le_parent (_K ell B F:ℝ) (hell:0<ell) (hB:0<B) (hF:0<F)
    (j:GlobalLogIndex) (hJ:globalLogRep j 4≤B^2) (hlarge:Real.exp 4≤B*F):
    globalPooledColumnScale ell j*globalPooledLabelScale j≤(ell*B^3)*F := by
  have hD:=globalPooledDelta_pos B F hB hF j
  have hM:0<(ell*B^3)*F:=by positivity
  rw [globalPooled_mass ell B F hB hF j]
  calc
    _ ≤ Real.exp 4*((ell*B^3)*F)*B^2/(globalPooledDelta B F j*B^2):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Real.exp 4*((ell*B^3)*F)/globalPooledDelta B F j:=by field_simp
    _ ≤ (ell*B^3)*F:=by
      apply (div_le_iff₀ hD).mpr
      have he:=hlarge.trans (globalPooledDelta_ge B F hB.le hF.le j)
      nlinarith

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in

theorem globalRetained_canonical_geometry
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal O×Ideal O×Ideal O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖ringComplex (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖ringComplex m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖ringComplex z.2‖^2≤Kchild) := by
  obtain ⟨x,hx,hqx⟩:=Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩:=Finset.mem_filter.mp hx
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hJ:globalLogRep j 4≤B^2:=by
    simpa only [hj] using globalPooled_J_bound p hp B hB.le side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
  have hD:Z^η≤globalPooledDelta B F j:=
    (Real.rpow_le_rpow_of_exponent_le hZ.le hη).trans
      (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
  have hr:globalLogRep j 8*Real.exp 1≤K/globalPooledDelta B F j:=
    globalPooledRow_contraction K ell B F hK hell hB hF0 j hJ (hretained.trans hD)
  have hKchild:1≤globalLogRep j 8*Real.exp 1:=one_le_mul_of_one_le_of_one_le
    (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hsmall:globalLogRep j 8*Real.exp 1≤Ksrc/Z^((1:ℝ)/1000):=by
    apply hr.trans
    calc
      _ ≤ K/Z^((1:ℝ)/1000):=div_le_div_of_nonneg_left hK.le
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
        (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
      _ ≤ _:=div_le_div_of_nonneg_right hKle (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hinv:=globalBin_invariant_small_padding p hp Z η K ell B F hZ hK hell hB hF side x
    (hk x hxs) m (hb₁ x hxs) (hb₂ x hxs) (by simpa only [hj] using hretained)
  simp only [hj,hqx] at hinv
  refine ⟨globalPooledColumnScale_pos ell hell j,globalPooledLabelScale_ge_one j,hKchild,
    globalPooled_mass_le_parent K ell B F hell hB hF0 j hJ hlarge,hsmall,
    fixedDepthRank_step Z Ksrc _ hZ hKsrc hKchild hsmall,
    fixedDepthRank_initial Z Ksrc hZ hKsrc hstart,hinv,?_⟩
  intro z hz
  have hb:=globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨globalArithmeticTargets_squarefree p source side q j z hz,
    globalArithmeticTargets_ne_zero p hp source side q j hk z hz,hb.2.1,hb.2.2⟩

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem canonicalProgress_large (Z : ℝ) (hZ : Real.exp 9000≤Z) :
    Real.exp 4≤Z^((1:ℝ)/1000) := by
  have hh := Real.rpow_le_rpow (Real.exp_pos 9000).le hZ (by norm_num : (0:ℝ)≤1/1000)
  rw [Real.rpow_def_of_pos (Real.exp_pos 9000), Real.log_exp] at hh
  norm_num at hh
  exact (Real.exp_le_exp.mpr (by norm_num : (4:ℝ)≤9)).trans hh

theorem paddedCanonicalRatio (K M R Z η : ℝ) (hM : 0<M) (hZ : 0<Z) :
    Z^η*((K/Z^η)*R/(Real.exp 3*M))=(K*R/M)/Real.exp 3 := by
  field_simp

def canonicalRankMargin (σ η : ℝ) (r : ℕ) : ℝ :=
  σ-η*((3000-r:ℕ):ℝ)

theorem canonicalRankMargin_lower (σ η : ℝ) (hη : 0≤η) (r : ℕ) :
    σ-3000*η≤canonicalRankMargin σ η r := by
  have hn : ((3000-r:ℕ):ℝ)≤3000 := by exact_mod_cast (Nat.sub_le 3000 r)
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRankMargin_step (σ η : ℝ) (hη : 0≤η) (r s : ℕ)
    (hr : r≤3000) (hs : s+1≤r) :
    canonicalRankMargin σ η s+η≤canonicalRankMargin σ η r := by
  have hn : 3000-r+1≤3000-s := by omega
  have hn' : ((3000-r:ℕ):ℝ)+1≤((3000-s:ℕ):ℝ) := by exact_mod_cast hn
  unfold canonicalRankMargin
  nlinarith

theorem canonicalRatio_exp_loss (K M R : ℝ) (hM : 0<M) :
    K*R/(Real.exp 3*M)=(K*R/M)/Real.exp 3 := by
  field_simp

theorem canonicalRankMargin_padding (Z σ η a : ℝ) (r s : ℕ)
    (hZ : 1<Z) (hη : 0≤η) (hr : r≤3000) (hs : s+1≤r)
    (ha : 0≤a) (hbound : a≤Z^(-canonicalRankMargin σ η r)) :
    Z^η*(a/Real.exp 3)≤Z^(-canonicalRankMargin σ η s) := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hmargin := canonicalRankMargin_step σ η hη r s hr hs
  calc
    Z^η*(a/Real.exp 3) ≤ Z^η*a :=
      mul_le_mul_of_nonneg_left (div_le_self ha (Real.one_le_exp (by norm_num)))
        (Real.rpow_nonneg hZ0.le _)
    _ ≤ Z^η*Z^(-canonicalRankMargin σ η r) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZ0.le _)
    _ = Z^(η-canonicalRankMargin σ η r) := by
      rw [sub_eq_add_neg,Real.rpow_add hZ0]
    _ ≤ Z^(-canonicalRankMargin σ η s) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
def canonicalPadding (ε C : ℝ) : ℝ :=
  min ((1:ℝ)/120040) (ε/6002)/(1+C)

theorem canonicalPadding_budget (ε C : ℝ) (hε : 0<ε) (hC : 0≤C) :
    0<canonicalPadding ε C ∧ canonicalPadding ε C≤(1:ℝ)/1000 ∧
    3000*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤(1:ℝ)/40 ∧
    3001*C*canonicalPadding ε C≤ε/2 ∧
    C*canonicalPadding ε C≤(1:ℝ)/1000 := by
  let a : ℝ := min ((1:ℝ)/120040) (ε/6002)
  have ha : 0<a := lt_min (by norm_num) (div_pos hε (by norm_num))
  have ha₁ : a≤(1:ℝ)/120040 := min_le_left _ _
  have ha₂ : a≤ε/6002 := min_le_right _ _
  have hd : 0<1+C := by linarith
  have heta : 0<canonicalPadding ε C := div_pos ha hd
  have heta₁ : canonicalPadding ε C≤a := div_le_self ha.le (by linarith)
  have hCeta : C*canonicalPadding ε C≤a := by
    change C*(a/(1+C))≤a
    rw [←mul_div_assoc]
    exact (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨heta,?_,?_,?_,?_,?_⟩ <;> nlinarith

theorem canonicalRankMargin_le (σ η : ℝ) (hη : 0≤η) (r : ℕ) :
    canonicalRankMargin σ η r≤σ := by
  unfold canonicalRankMargin
  have hn : (0:ℝ)≤((3000-r:ℕ):ℝ) := Nat.cast_nonneg _
  nlinarith

theorem canonicalRankMargin_reserved (η : ℝ) (hη : 0≤η)
    (hbudget : 3000*η≤(1:ℝ)/40) (r : ℕ) :
    (1:ℝ)/40≤canonicalRankMargin ((1:ℝ)/20) η r ∧
    canonicalRankMargin ((1:ℝ)/20) η r≤(1:ℝ)/20 := by
  constructor
  · exact (by linarith : (1:ℝ)/40≤(1:ℝ)/20-3000*η).trans
      (canonicalRankMargin_lower _ η hη r)
  · exact canonicalRankMargin_le _ η hη r

theorem canonicalRankMargin_initial_bound (Z η R M : ℝ) (r : ℕ)
    (hZ : 1≤Z) (hη : 0≤η) (hM : 0≤M)
    (hbound : R≤M*Z^(-((1:ℝ)/20))) :
    R≤M*Z^(-canonicalRankMargin ((1:ℝ)/20) η r) := by
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ hM
  exact Real.rpow_le_rpow_of_exponent_le hZ
    (neg_le_neg (canonicalRankMargin_le _ η hη r))

theorem canonicalRankMargin_final_bound (Z η R M : ℝ) (r : ℕ)
    (hZ : 1≤Z) (hη : 0≤η) (hM : 0≤M) (hbudget : 3000*η≤(1:ℝ)/40)
    (hbound : R≤M*Z^(-canonicalRankMargin ((1:ℝ)/20) η r)) :
    R≤M*Z^(-((1:ℝ)/40)) := by
  apply hbound.trans
  apply mul_le_mul_of_nonneg_left _ hM
  exact Real.rpow_le_rpow_of_exponent_le hZ
    (neg_le_neg (canonicalRankMargin_reserved η hη hbudget r).1)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem fixedTripleMask_ne_zero_of_bin (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j) (m : O) (hm : m≠0) :
    fixedTripleMask m q≠0 := by
  obtain ⟨x,hx,hqx⟩ := Finset.mem_image.mp hq
  have ht := globalSecondFixedTriple_nonzero p hp x
  rw [←hqx]
  unfold fixedTripleMask
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm
    (cubicIdealGenerator_ne_zero _ ht.1))
    (cubicIdealGenerator_ne_zero _ ht.2.1))
    (cubicIdealGenerator_ne_zero _ ht.2.2)

include hp in

theorem canonical_retained_scale_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖ringComplex m‖^2≤(X*F)*Z^(-σ))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale (K/Z^η) (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖ringComplex (fixedTripleMask m q)‖^2≤(X'*F')*Z^(-σ) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hKpad : 0<K/Z^η := div_pos hK0 (Real.rpow_pos_of_pos hZ0 _)
  have hKle : K/Z^η≤K := div_le_self hK0.le (Real.one_le_rpow hZ.le hη)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K (K/Z^η)
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hKpad hKle hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hratio' : globalLogRep j 8*Real.exp 1*‖ringComplex (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤Z^(-σ) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',paddedCanonicalRatio K (X*F)
      (‖ringComplex m‖^2) Z η (mul_pos hX hF0) hZ0] at hratio
    apply hratio.trans
    apply (div_le_self (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le)
      (Real.one_le_exp (by norm_num))).trans
    exact (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

include hp in

theorem canonical_retained_unpadded_closure
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (Z σ η X B F K : ℝ) (m : O)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hX : 0<X) (hB : 0<B) (hF : 1≤F) (hK : 1≤K) (hm : m≠0)
    (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hstart : K≤Z^3) (hmass : X*F≤canonicalRankMass Z (fixedDepthRank Z K))
    (hinv : K*‖ringComplex m‖^2≤
      (X*F)*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)))
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    0<X' ∧ 1≤F' ∧ 1≤K' ∧
      fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧ K'≤Z^3 ∧
      X'*F'≤canonicalRankMass Z (fixedDepthRank Z K') ∧
      K'*‖ringComplex (fixedTripleMask m q)‖^2≤
        (X'*F')*Z^(-canonicalRankMargin σ η (fixedDepthRank Z K')) ∧
      fixedTripleMask m q≠0 ∧
      (∀I∈globalCanonicalLabels p source side q j,
        I≠⊥ ∧ Squarefree I ∧ (Ideal.absNorm I:ℝ)≤F') := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hF0 : 0<F := zero_lt_one.trans_le hF
  have hBup : 0<Real.exp 1*B := mul_pos (Real.exp_pos _) hB
  have hell : 0<X/B^3 := div_pos hX (pow_pos hB 3)
  have hlarge : Real.exp 4≤(Real.exp 1*B)*F := (canonicalProgress_large Z hZbig).trans hprogress
  obtain ⟨hXc,hFc,hKc,hMc,hsmall,hrank,hrank0,hratio,hlabels⟩ :=
    globalRetained_canonical_geometry p hp source side q j hq Z η K K
      (X/B^3) (Real.exp 1*B) F m hZ hηsmall hK0 hK0 le_rfl hell hBup hF
      hprogress hlarge hstart hk hb₁ hb₂ hretained
  have hMc' : globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j≤Real.exp 3*(X*F) := by
    simpa only [lowerCubeBin_transfer_mass X B F hB.ne'] using hMc
  have hparent : K*‖ringComplex m‖^2/(X*F)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z K)) :=
    (div_le_iff₀ (mul_pos hX hF0)).mpr (by simpa only [mul_comm] using hinv)
  have hratio' : globalLogRep j 8*Real.exp 1*‖ringComplex (fixedTripleMask m q)‖^2/
      (globalPooledColumnScale (X/B^3) j*globalPooledLabelScale j)≤
      Z^(-canonicalRankMargin σ η (fixedDepthRank Z (globalLogRep j 8*Real.exp 1))) := by
    rw [lowerCubeBin_transfer_mass X B F hB.ne',canonicalRatio_exp_loss K (X*F)
      (‖ringComplex m‖^2) (mul_pos hX hF0)] at hratio
    exact hratio.trans (canonicalRankMargin_padding Z σ η _ _ _ hZ hη hrank0 hrank
      (div_nonneg (mul_nonneg hK0.le (sq_nonneg _)) (mul_pos hX hF0).le) hparent)
  refine ⟨hXc,hFc,hKc,hrank,?_,?_,?_,fixedTripleMask_ne_zero_of_bin p hp source side q j hq m hm,
    globalCanonicalLabels_bounds p hp source side q j hk⟩
  · exact hsmall.trans ((div_le_self hK0.le
      (Real.one_le_rpow hZ.le (by norm_num : (0:ℝ)≤1/1000))).trans hstart)
  · exact canonicalRankMass_child Z X F _ _ _ _ hrank0 hrank hmass hMc'
  · exact (div_le_iff₀ (mul_pos hXc (zero_lt_one.trans_le hFc))).mp hratio' |>.trans_eq (by ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap

variable {ι:Type*} [DecidableEq ι] (p:ι→O) (hp:∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

include hp in
theorem canonicalSourceCoefficient_frequencyTwist (Ψ : O →* ℂ) (m f : O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    canonicalSourceCoefficient p hg Ψ m f
      (fun U=>frequencyTwist g t (columnLog p X U)) S=
    kernelLogPhase t (-Real.log X)*canonicalSourceCoefficient p hg (normHeightTwist Ψ t) m f
      (fun U=>g (columnLog p X U)) S := by
  simp only [canonicalSourceCoefficient,JointLogSeparation.frequencyTwist_apply,
    kernelLogPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring
include hp in
theorem reopenedCanonicalRow_frequencyTwist (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : O →* ℂ) (m f z : O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    reopenedCanonicalRow p hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z=
      kernelLogPhase t (-Real.log X)*reopenedCanonicalRow p hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z := by
  unfold reopenedCanonicalRow
  simp_rw [canonicalSourceCoefficient_frequencyTwist p hp hg Ψ m f g X t hX,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro S hS
  ring

include hp in
theorem reopenedCanonicalRow_frequencyTwist_norm (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : O →* ℂ) (m f z : O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z‖=
      ‖reopenedCanonicalRow p hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist p hp hg pool Q β Ψ m f z g X t hX,
    norm_mul,kernelLogPhase_norm,one_mul]

include hp hcop in
theorem reopenedSource_frequencyTwist
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (hQ : ∀v∈Q,v.support⊆pool) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K X t : ℝ) (hK : 0<K) (hX : 0<X) :
    canonicalSourceTotal p hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      Ψ Ψ m m (frequencyTwist g t) (frequencyTwist g t) W K X=
    canonicalSourceTotal p hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g W K X := by
  rw [←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W K X hK,
    ←reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β
      (normHeightTwist Ψ t) m g W K X hK]
  apply Finset.sum_congr rfl
  intro I hI
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_frequencyTwist_norm p hp hg pool Q (β I) Ψ m _ z g X t hX]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap

theorem reopenedCanonicalRow_twoPassage_uniform_height
    (W g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0≤M) (hNv : 0≤Nv)
    (hgM : ∀t,g t≠0→|t|≤M) (hV : ∀t,V t≠0→|t|≤Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O) (Γ t Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M≤U → (∀u,‖Ψ u‖≤1) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      ‖(ell*B^2*F:ℂ)⁻¹*
        ((∑I∈labels,∑'z:O,W (‖ringComplex z‖^2/Ksrc)*
           (‖reopenedCanonicalRow p hg pool Q (β I) Ψ m
             (cubicIdealGenerator I)
             (fun S=>frequencyTwist g t (columnLog p ell S)) z‖^2:ℝ))-
         canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g W Ksrc ell-
         canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε K ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε K ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    canonicalSource_twoPassage_quantitative W g g V V M M Nv Nv hM hM hNv hNv
      hgM hgM hV hV hWin hWin ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m
    (frequencyTwist g t) W Ksrc ell hKsrc,
    reopenedSource_frequencyTwist p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell t hKsrc hell]
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  exact htransfer p hp hinj hcop hg hc hpr pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m (Γ^2) Ksrc K ell B F H U
    (sq_nonneg Γ) hKsrc hK hell hB hF hH hU hMU hMU hΨt hΨt
    (fun b hb C hC I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI)
    (reopenedCubeFamily_admissible Q)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1)
    (fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2) hsf hf

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels JointLogSeparation MeasureTheory
open scoped Classical SchwartzMap

theorem nonzeroRowFamily_le_center (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K scale B : ℝ) (zero tail : ℂ)
    (hK : 0<K) (hscale : 0<scale)
    (hcenter : ‖(scale:ℂ)⁻¹*((∑I∈labels,∑'z:O,rowMajorant (‖ringComplex z‖^2/K)*
      (‖P I z‖^2:ℝ))-zero-tail)‖ ≤ B) :
    (∑I∈labels,nonzeroRowMajorantSum (P I) K).re ≤ 
      ‖zero‖+‖tail‖+scale*B := by
  let total : ℂ := ∑I∈labels,∑'z:O,rowMajorant (‖ringComplex z‖^2/K)*(‖P I z‖^2:ℝ)
  have hnonzero : (∑I∈labels,nonzeroRowMajorantSum (P I) K).re ≤ total.re := by
    simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re,
      Complex.re_sum,Complex.ofReal_re]
    change (∑I∈labels,(∑'z:O,rowMajorant (‖ringComplex z‖^2/K)*(‖P I z‖^2:ℝ)).re)-
      ∑I∈labels,‖P I 0‖^2 ≤ _
    have hz : 0 ≤ ∑I∈labels,‖P I 0‖^2 := Finset.sum_nonneg (fun I hI=>sq_nonneg _)
    dsimp only [total]
    rw [Complex.re_sum]
    linarith
  have hc : ‖total-zero-tail‖ ≤ scale*B := by
    calc
      _ = scale*‖(scale:ℂ)⁻¹*(total-zero-tail)‖ := by
        rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
        field_simp
      _  ≤  _ := mul_le_mul_of_nonneg_left hcenter hscale.le
  apply hnonzero.trans
  calc
    total.re  ≤  ‖total‖ := Complex.re_le_norm _
    _ = ‖(total-zero-tail)+zero+tail‖ := by congr 1; ring
    _  ≤  ‖total-zero-tail‖+‖zero‖+‖tail‖ := norm_add₃_le
    _  ≤  _ := by linarith

theorem reopenedCanonicalRow_nonzero_twoPassage
    (g V : 𝓢(ℝ,ℂ)) (M Nv : ℝ) (hM : 0 ≤ M) (hNv : 0 ≤ Nv)
    (hgM : ∀t,g t≠0→|t| ≤ M) (hV : ∀t,V t≠0→|t| ≤ Nv)
    (hWin : ∀t,g t≠0→V t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0 ≤ Cfirst ∧ 0 ≤ C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0 ≤ C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t| ≤ M+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t| ≤ M+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O) (Γ t Ksrc Kcut ell B F H U:ℝ),
      0 ≤ Γ → 0<Ksrc → 0<Kcut → 0<ell → 1 ≤ B → 0<F → 0 ≤ H → 1 ≤ U →
      ell*Real.exp M ≤ U → (∀u,‖Ψ u‖ ≤ 1) →
      (∀I∈labels,∀v∈Q,‖β I v‖ ≤ Γ) → (∀v∈Q,v.support⊆pool) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2 ≤ B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ) ≤ F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (∑I∈labels,nonzeroRowMajorantSum
         (reopenedCanonicalRow p hg pool Q (β I) Ψ m
           (cubicIdealGenerator I)
           (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc).re ≤ 
      ‖canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖+
      ‖canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖+
      (ell*B^2*F)*(Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool bs)
          Ψt m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩ :=
    reopenedCanonicalRow_twoPassage_uniform_height rowMajorant g V M Nv hM hNv hgM hV hWin
      ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  dsimp only
  have ht := htransfer p hp hinj hcop hg hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F H U
    hΓ hKsrc hKcut hell hB hF hH hU hMU hΨ hβ hQ hQB hsf hf
  have hscale : 0<ell*B^2*F := mul_pos (mul_pos hell (sq_pos_of_pos (zero_lt_one.trans_le hB))) hF
  have hb := nonzeroRowFamily_le_center labels
    (fun I=>reopenedCanonicalRow p hg pool Q (β I) Ψ m
      (cubicIdealGenerator I)
      (fun S=>frequencyTwist g t (columnLog p ell S))) Ksrc (ell*B^2*F)
    ((Ksrc/Kcut)*Cfirst*(globalFirstRowCap Kcut ell B F)^deltaLoss*
      Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₁ C₁ Cd₁ Ct₁ (Γ^2) ε Kcut ell B F M H U A J N true)*
      Real.sqrt (globalFirstQuantitativeBudget p hg pool (canonicalSourceBlocks pool (reopenedCubeFamily Q))
        (normHeightTwist Ψ t) m windows₂ C₂ Cd₂ Ct₂ (Γ^2) ε Kcut ell B F M H U A J N false))
    (canonicalSourceZero p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc ell)
    (canonicalSourceTail p hp hg pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
      (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m g g rowMajorant Ksrc Kcut ell)
    hKsrc hscale (by simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using ht)
  exact hb.trans_eq (by ring)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

theorem reopenedCanonicalFirstErrors (g : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0→|t|≤M) (ε : ℝ) (hε : 0<ε) (A : ℕ) :
    ∃Czero Ctail : ℝ,0≤Czero ∧ 0≤Ctail ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (hpr:∀i,lambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O) (Γ t Ksrc Kcut ell B F lengthScale : ℝ),
      0≤Γ → 0<Ksrc → 0<Kcut → 0<ell → 1≤B → 1≤F → 1≤lengthScale → ell*Real.exp M≤lengthScale →
      (∀u,‖Ψ u‖≤1) → (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠⊥) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      let Ψt:=normHeightTwist Ψ t
      let bs:=reopenedCubeFamily Q
      let a:=reopenedPairCoefficient β
      (‖canonicalSourceZero p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc ell‖≤
        Czero*B^(1+ε)*ell*F*Γ^2*Ksrc) ∧
      (‖canonicalSourceTail p hp hg pool bs labels a Ψt Ψt m m g g rowMajorant Ksrc Kcut ell‖≤
        Ctail*B^(4+ε)*lengthScale^4*F*Γ^2*Ksrc*(1+lengthScale^3*B^4/Ksrc)^2/
          (1+(Ksrc/Kcut)/Real.exp (2*M))^A) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_uniform_canonicalFirstZero_bound ε hε
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_canonicalSourceTail_bound ε hε A
  let G : ℝ := SchwartzMap.seminorm ℝ 0 0 g
  have hG : 0≤G := apply_nonneg _ _
  have hgG : ∀x,‖g x‖≤G := fun x=>SchwartzMap.norm_le_seminorm ℝ g x
  have hgupper : ∀x,g x≠0→x≤M := fun x hx=>(le_abs_self x).trans (hgM x hx)
  refine ⟨Cz*Real.exp M*G^2*‖paperRadialFourier rowMajorant 0‖,
    Ct*G^2*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant,by positivity,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool Q labels β Ψ m Γ t Ksrc Kcut ell B F lengthScale
    hΓ hKsrc hKcut hell hB hF hL hML hΨ hβ hQB hI0 hIF
  dsimp only
  have hΨt : ∀u,‖normHeightTwist Ψ t u‖≤1 :=
    fun u=>(normHeightTwist_norm_le Ψ t u).trans (hΨ u)
  have hb₁ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).1
  have hb₂ := fun b hb=>(reopenedCubeFamily_cube_norms p Q B hQB b hb).2
  have ha : ∀b∈reopenedCubeFamily Q,∀D∈(pool\b.support).powerset,∀I∈labels,
      ‖reopenedPairCoefficient β b D I‖≤Γ^2 :=
    fun b hb D hD I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb D I hI
  constructor
  · have hz := hzero p hp hcop hg hinj hpr pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G ell Ksrc M B F (sq_nonneg Γ) hG hG hell hB hF
      hΨt hΨt (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper
    change ‖canonicalSourceZero p hp hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant Ksrc ell‖≤_ at hz
    rw [abs_of_pos hKsrc] at hz
    exact hz.trans_eq (by ring)
  · have ht := htail p hp hinj hcop hg hc hpr pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) (normHeightTwist Ψ t) (normHeightTwist Ψ t) m m
      g g rowMajorant (Γ^2) G G M M Ksrc Kcut ell B F lengthScale
      (sq_nonneg Γ) hG hG hKsrc hKcut hell hB hF hL hML hML hΨt hΨt
      (reopenedCubeFamily_admissible Q) hb₁ hb₂ hI0 hIF ha hgG hgG hgupper hgupper
    exact ht.trans_eq (by rw [show M+M=2*M by ring]; ring)


end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
