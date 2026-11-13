/-
Completed norm-height twists adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Mellin.JointLogSeparation

/-!
# Completed norm-height twists

A smooth proper extension of the logarithm from a positive interval and the norm-height twist
`normTwistedSource` transferred to the radial source. Fixed logarithmic cutoffs cost finite
derivative constants, and compact derivative bounds give linear Fourier bounds.
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

namespace FiniteRingSieve

variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]

noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

omit [DecidableEq R] in
private theorem sum_chars_zero {a : R} (ha : a ≠ 1) :
    (∑ χ : MulChar R ℂ, χ a) = 0 := by
  obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity R ℂ ha
  refine eq_zero_of_mul_eq_self_left hχ ?_
  simp only [Finset.mul_sum, ← MulChar.mul_apply]
  exact Fintype.sum_bijective _ (Group.mulLeft_bijective χ) _ _ fun χ' => rfl

theorem sum_chars (a : R) :
    (∑ χ : MulChar R ℂ, χ a) =
      if a = 1 then (Fintype.card Rˣ : ℂ) else 0 := by
  split_ifs with ha
  · subst a
    simp only [map_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have hc : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
      simpa only [Nat.card_eq_fintype_card] using
        MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ
    exact_mod_cast hc
  · exact sum_chars_zero ha

theorem unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by
  calc
    _ = ∑ χ : MulChar R ℂ, χ ((u⁻¹ * v : Rˣ) : R) := by
      apply Finset.sum_congr rfl
      intro χ _
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit,
        Units.val_mul, map_mul]
    _ = if ((u⁻¹ * v : Rˣ) : R) = 1 then (Fintype.card Rˣ : ℂ) else 0 :=
      sum_chars _
    _ = _ := by simp only [Units.val_eq_one, inv_mul_eq_one]


end FiniteRingSieve

open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap

namespace CompletedHeight

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open SchwartzPlanePoisson JointLogSeparation

def positiveCutoff (a b : ℝ) (ha : 0 < a) : ContDiffBump ((a+max a b)/2) where
  rIn := (max a b-a)/2+a/4
  rOut := (max a b-a)/2+a/2
  rIn_pos := by linarith [le_max_left a b]
  rIn_lt_rOut := by linarith

lemma positiveCutoff_one (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    positiveCutoff a b ha x=1 := by
  apply (positiveCutoff a b ha).one_of_mem_closedBall
  change dist x ((a+max a b)/2) ≤  (max a b-a)/2+a/4
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith [hx.1,hx.2,le_max_right a b]

lemma positiveCutoff_zero (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x < a/2) :
    positiveCutoff a b ha x=0 := by
  by_contra hn
  have hm : x∈Function.support (positiveCutoff a b ha) := hn
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  linarith [hm.1]

def logCorrection (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ :=
  positiveCutoff a b ha x*(Real.log x-x)

/-- A smooth proper extension of the logarithm from the fixed positive support interval. -/
def patchedLog (a b : ℝ) (ha : 0 < a) (x : ℝ) : ℝ := x+logCorrection a b ha x

lemma logCorrection_compact (a b : ℝ) (ha : 0 < a) :
    HasCompactSupport (logCorrection a b ha) := (positiveCutoff a b ha).hasCompactSupport.mul_right

lemma logCorrection_smooth (a b : ℝ) (ha : 0 < a) :
    ContDiff ℝ ∞ (logCorrection a b ha) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x=0
  · subst x
    have he : logCorrection a b ha =ᶠ[𝓝 (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds (by linarith : (0:ℝ)<a/2)] with y hy
      simp only [logCorrection,positiveCutoff_zero a b ha y hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (positiveCutoff a b ha).contDiff.contDiffAt.mul
      ((Real.contDiffAt_log.mpr hx).sub contDiffAt_id)

lemma patchedLog_temperate (a b : ℝ) (ha : 0 < a) :
    Function.HasTemperateGrowth (patchedLog a b ha) :=
  Function.HasTemperateGrowth.id'.add
    ((logCorrection_compact a b ha).hasTemperateGrowth (logCorrection_smooth a b ha))

lemma patchedLog_proper (a b : ℝ) (ha : 0 < a) :
    ∃k : ℕ, ∃C : ℝ, ∀x : ℝ, ‖x‖ ≤  C*(1+‖patchedLog a b ha x‖)^k := by
  obtain ⟨x₀,hx₀⟩ := (logCorrection_smooth a b ha).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (logCorrection_compact a b ha).norm
  refine ⟨1,‖logCorrection a b ha x₀‖+1,?_⟩
  intro x
  have ht : ‖x‖ ≤  ‖patchedLog a b ha x‖+‖logCorrection a b ha x‖ := by
    simpa only [patchedLog,add_sub_cancel_right] using
      norm_sub_le (patchedLog a b ha x) (logCorrection a b ha x)
  have hb := hx₀ x
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedLog a b ha x),norm_nonneg (logCorrection a b ha x₀)]

lemma patchedLog_eq_log (a b : ℝ) (ha : 0 < a) (x : ℝ) (hx : x∈Icc a b) :
    patchedLog a b ha x=Real.log x := by
  simp only [patchedLog,logCorrection,positiveCutoff_one a b ha x hx,one_mul]
  ring

def sourceTwistCLM (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) :
    𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  ((SchwartzMap.smulLeftCLM ℂ (W : ℝ→ ℂ)).restrictScalars ℝ).comp
    (SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha))

lemma sourceTwistCLM_apply (W g : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a) (x : ℝ) :
    sourceTwistCLM W a b ha g x = W x*g (patchedLog a b ha x) := by
  change (SchwartzMap.smulLeftCLM ℂ (W : ℝ→ ℂ)
    ((SchwartzMap.compCLM ℝ (patchedLog_temperate a b ha) (patchedLog_proper a b ha)) g)) x = _
  rw [SchwartzMap.smulLeftCLM_apply_apply W.hasTemperateGrowth]
  rfl

/-- A norm-height twist transferred from arithmetic coefficients to the radial source. -/
def normTwistedSource (W : ℝ→ ℂ) (t x : ℝ) : ℂ := kernelLogPhase t (Real.log x)*W x

lemma normTwistedSource_support (W : ℝ→ ℂ) (t : ℝ) :
    Function.support (normTwistedSource W t) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by simp only [normTwistedSource,hz,mul_zero])

theorem frequencyTwist_finite_bound (g : 𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤  C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  let c : ℕ×ℕ →  ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤ c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨n,C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤ C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤ n := Finset.le_sup hz
  have hh := frequencyTwist_seminorm_polynomial g t z.1 z.2
  exact hh.trans (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn)
    (by positivity) hC.le)

theorem normTwistedSource_schwartz (W : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support (W : ℝ→ ℂ) ⊆ Icc a b) :
    ∃ G : ℝ→ 𝓢(ℝ,ℂ), (∀t x,G t x=normTwistedSource W t x) ∧
      (∀S : Finset (ℕ×ℕ), ∃n : ℕ, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G t)≤ C*(1+‖t‖)^n) := by
  let M := |Real.log a|+|Real.log b|+1
  have hM : 0≤ M := by dsimp [M]; positivity
  obtain ⟨v,hvc,hvs,hvone,hvsupp,_⟩ := exists_complex_smooth_cutoff M hM
  let V : 𝓢(ℝ,ℂ) := hvc.toSchwartzMap hvs
  let G : ℝ→ 𝓢(ℝ,ℂ) := fun t => sourceTwistCLM W a b ha (frequencyTwist V t)
  refine ⟨G,?_,?_⟩
  · intro t x
    rw [show G t x=sourceTwistCLM W a b ha (frequencyTwist V t) x from rfl,
      sourceTwistCLM_apply,frequencyTwist_apply]
    by_cases hx : W x=0
    · simp only [normTwistedSource,hx,zero_mul,mul_zero]
    · have hxi := hs hx
      rw [patchedLog_eq_log a b ha x hxi]
      have hlog : |Real.log x|≤ M := by
        have hlo := Real.log_le_log ha hxi.1
        have hhi := Real.log_le_log (lt_of_lt_of_le ha hxi.1) hxi.2
        rw [abs_le]
        constructor <;> dsimp [M] <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),
          abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
      have hv : V (Real.log x)=1 := hvone _ hlog
      simp only [hv,mul_one,normTwistedSource]
      ring
  · intro S
    obtain ⟨s,C,hC,hcontrol⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
      (sourceTwistCLM W a b ha) S
    obtain ⟨n,D,hD,hbound⟩ := frequencyTwist_finite_bound V s
    refine ⟨n,C*D,mul_pos hC hD,?_⟩
    intro t
    exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end CompletedHeight

namespace CompletedHeight
open SchwartzPlanePoisson MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

def logRadius (a b : ℝ) : ℝ := |Real.log a| + |Real.log b| + 1

theorem logRadius_pos (a b : ℝ) : 0 < logRadius a b := by unfold logRadius; positivity

def logCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b
  rOut := logRadius a b + 1
  rIn_pos := logRadius_pos a b
  rIn_lt_rOut := by linarith

def logOuterCutoff (a b : ℝ) : ContDiffBump (0 : ℝ) where
  rIn := logRadius a b + 1
  rOut := logRadius a b + 2
  rIn_pos := by have := logRadius_pos a b; linarith
  rIn_lt_rOut := by linarith

def expCorrection (a b u : ℝ) : ℝ := logOuterCutoff a b u * (Real.exp u - u)
def patchedExp (a b u : ℝ) : ℝ := u + expCorrection a b u

theorem expCorrection_compact (a b : ℝ) : HasCompactSupport (expCorrection a b) :=
  (logOuterCutoff a b).hasCompactSupport.mul_right

theorem expCorrection_smooth (a b : ℝ) : ContDiff ℝ ∞ (expCorrection a b) :=
  (logOuterCutoff a b).contDiff.mul (Real.contDiff_exp.sub contDiff_id)

theorem patchedExp_temperate (a b : ℝ) : Function.HasTemperateGrowth (patchedExp a b) :=
  Function.HasTemperateGrowth.id'.add ((expCorrection_compact a b).hasTemperateGrowth
    (expCorrection_smooth a b))

theorem patchedExp_proper (a b : ℝ) :
    ∃ (k : ℕ) (C : ℝ), ∀ u : ℝ, ‖u‖ ≤  C * (1 + ‖patchedExp a b u‖) ^ k := by
  obtain ⟨u₀, hu₀⟩ := (expCorrection_smooth a b).continuous.norm.exists_forall_ge_of_hasCompactSupport
    (expCorrection_compact a b).norm
  refine ⟨1, ‖expCorrection a b u₀‖ + 1, ?_⟩
  intro u
  have htriangle : ‖u‖ ≤  ‖patchedExp a b u‖ + ‖expCorrection a b u‖ := by
    simpa only [patchedExp, add_sub_cancel_right] using
      norm_sub_le (patchedExp a b u) (expCorrection a b u)
  have hbound := hu₀ u
  simp only [pow_one]
  nlinarith [norm_nonneg (patchedExp a b u), norm_nonneg (expCorrection a b u₀)]

def logPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.smulLeftCLM ℂ (logCutoff a b)).comp
    (SchwartzMap.compCLM ℝ (patchedExp_temperate a b) (patchedExp_proper a b))

theorem logPullbackCLM_apply (a b : ℝ) (W : SchwartzMap ℝ ℂ) (u : ℝ) :
    logPullbackCLM a b W u = logCutoff a b u • W (patchedExp a b u) := by
  rw [logPullbackCLM, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply
    ((logCutoff a b).hasCompactSupport.hasTemperateGrowth (logCutoff a b).contDiff)]
  rfl

theorem logCutoff_eq_one_of_source (a b : ℝ) (ha : 0 < a) (u : ℝ)
    (hu : Real.exp u ∈ Set.Icc a b) : logCutoff a b u = 1 := by
  apply (logCutoff a b).one_of_mem_closedBall
  have hl := Real.log_le_log ha hu.1
  have hr := Real.log_le_log (Real.exp_pos u) hu.2
  simp only [Real.log_exp] at hl hr
  change dist u 0 ≤  logRadius a b
  rw [Real.dist_eq, sub_zero]
  apply abs_le.mpr
  constructor <;> dsimp [logRadius] <;>
    linarith [neg_abs_le (Real.log a), le_abs_self (Real.log b), abs_nonneg (Real.log a), abs_nonneg (Real.log b)]

theorem patchedExp_eq_exp_of_cutoff_ne_zero (a b u : ℝ) (hu : logCutoff a b u ≠ 0) :
    patchedExp a b u = Real.exp u := by
  have hmem : u ∈ Function.support (logCutoff a b) := hu
  rw [(logCutoff a b).support_eq] at hmem
  have heta : logOuterCutoff a b u = 1 := by
    apply (logOuterCutoff a b).one_of_mem_closedBall
    change dist u 0 ≤  logRadius a b + 1
    change dist u 0 < logRadius a b + 1 at hmem
    exact le_of_lt hmem
  simp [patchedExp, expCorrection, heta]

theorem logPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    logPullbackCLM a b W u = W (Real.exp u) := by
  rw [logPullbackCLM_apply]
  by_cases hW : W (Real.exp u) = 0
  · by_cases hcut : logCutoff a b u = 0
    · simp [hcut, hW]
    · rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u hcut, hW, smul_zero]
  · have hcut := logCutoff_eq_one_of_source a b ha u (hsupp hW)
    rw [patchedExp_eq_exp_of_cutoff_ne_zero a b u (by rw [hcut]; norm_num), hcut, one_smul]



theorem compact_family_deriv_sup_bound (F : ℝ →  ℝ →  ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ J, ∀ u : ℝ, ‖iteratedFDeriv ℝ j (F σ) u‖ ≤  C := by
  have hc := (section_iteratedDeriv_smooth F hF j).continuous.norm
  obtain ⟨M, hM⟩ := (hJ.prod hK).bddAbove_image hc.continuousOn
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro σ hσ u
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hu : u ∈ K
  · exact (hM (Set.mem_image_of_mem _ (show (σ, u) ∈ J ×ˢ K from ⟨hσ, hu⟩))).trans
      (by linarith [le_abs_self M])
  · have hs : Function.support (iteratedDeriv j (F σ)) ⊆ K :=
      (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset (F σ) j).trans
        (closure_minimal (hsupp σ) hK.isClosed))
    have hz : iteratedDeriv j (F σ) u = 0 := by by_contra hn; exact hu (hs hn)
    simp only [hz, norm_zero]
    positivity

theorem compact_family_mul_deriv_L1_source_bound (F : ℝ →  ℝ →  ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J,
      (∫ u : ℝ, ‖iteratedDeriv j (fun u => F σ u * W u) u‖) ≤ 
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose c hc hcb using fun i : Fin (j + 1) => compact_family_deriv_sup_bound F hF K hK hsupp J hJ i.val
  let D := (∑ i : Fin (j + 1), c i) + 1
  have hD : 0 < D := by
    have : 0 ≤  ∑ i : Fin (j + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hder (i : ℕ) (hi : i ≤  j) (σ : ℝ) (hσ : σ ∈ J) (u : ℝ) :
      ‖iteratedFDeriv ℝ i (F σ) u‖ ≤  D := by
    let k : Fin (j + 1) := ⟨i, by omega⟩
    have hsum : c k ≤  ∑ l : Fin (j + 1), c l :=
      Finset.single_le_sum (fun l _ => (hc l).le) (Finset.mem_univ k)
    exact (hcb k σ hσ u).trans (by dsimp [D]; linarith)
  let B : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D
  have hB : 0 ≤  B := by dsimp [B]; positivity
  refine ⟨(B + 1) * (volume.real K + 1), by positivity, ?_⟩
  intro W σ hσ
  let S : ℝ := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤  S := by dsimp [S]; positivity
  have hWder (k : ℕ) (hk : k ≤  j) (u : ℝ) : ‖iteratedFDeriv ℝ k W u‖ ≤  S := by
    have hle : schwartzSeminormFamily ℝ ℝ ℂ (0, k) ≤ 
        (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ) (by simp [hk])
    exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ W k u).trans (Seminorm.le_def.mp hle W)
  have hb (u : ℝ) : ‖iteratedDeriv j (fun u => F σ u * W u) u‖ ≤  (B + 1) * S := by
    rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hfσ : ContDiff ℝ ∞ (F σ) := hF.comp (contDiff_const.prodMk contDiff_id)
    apply (norm_iteratedFDeriv_mul_le hfσ (W.smooth ⊤) u (n := j)
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).trans
    calc
      _ ≤  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * D * S := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hder i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) σ hσ u) (by positivity))
          (hWder (j - i) (Nat.sub_le _ _) u) (norm_nonneg _) (by positivity)
      _ = B * S := by rw [← Finset.sum_mul]
      _ ≤  (B + 1) * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hmul : Function.support (fun u => F σ u * W u) ⊆ K := by
    intro u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : Function.support (iteratedDeriv j (fun u => F σ u * W u)) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hmul hK.isClosed))
  have hzero : ∀ u, u ∉ K →  ‖iteratedDeriv j (fun u => F σ u * W u) u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j (fun u => F σ u * W u) u = 0 := by by_contra hn; exact hu (hs hn)
    simp [hz]
  have hi := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => ‖iteratedDeriv j (fun u => F σ u * W u) u‖) hK.measure_lt_top
    (C := (B + 1) * S) (fun u _ => by simpa using hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun u => norm_nonneg _))] at hi
  calc
    _ ≤  ((B + 1) * S) * volume.real K := hi
    _ ≤  ((B + 1) * S) * (volume.real K + 1) := by gcongr; linarith
    _ = _ := by dsimp [S]; ring


end CompletedHeight

namespace CompletedHeight
open SchwartzPlanePoisson MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

theorem compact_family_mul_fourier_power_source_bound (F : ℝ →  ℝ →  ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ 
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_deriv_L1_source_bound F hF K hK hsupp J hJ j
  refine ⟨C / (2 * Real.pi) ^ j, by positivity, ?_⟩
  intro W σ hσ w
  have hFW : ContDiff ℝ ∞ (Function.uncurry (fun σ u => F σ u * W u)) :=
    hF.mul ((W.smooth ⊤).comp contDiff_snd)
  have hsupport : ∀ σ, Function.support (fun u => F σ u * W u) ⊆ K := by
    intro σ u hu
    exact hsupp σ (mul_ne_zero_iff.mp hu).1
  have hs : ContDiff ℝ ∞ (fun u => F σ u * W u) :=
    hFW.comp (contDiff_const.prodMk contDiff_id)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hs
    (fun k _ => compact_family_deriv_integrable (fun σ u => F σ u * W u) hFW K hK hsupport σ k)
    (by simp : (j : ℕ∞) ≤  ⊤)
  have hid : (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) =
      ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hn : ‖𝓕 (iteratedDeriv j (fun u => F σ u * W u)) w‖ ≤ 
      C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) (iteratedDeriv j (fun u => F σ u * W u)) w).trans
    exact hb W σ hσ
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  rw [← hid] at hn
  calc
    _ = (2 * Real.pi) ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := mul_comm _ _
    _ ≤  _ := hn

theorem compact_family_mul_fourier_weighted_source_bound (F : ℝ →  ℝ →  ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set ℝ) (hK : IsCompact K)
    (hsupp : ∀ σ, Function.support (F σ) ⊆ K) (J : Set ℝ) (hJ : IsCompact J)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : SchwartzMap ℝ ℂ, ∀ σ ∈ J, ∀ w : ℝ,
      (1 + |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤ 
        C * (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C₀, hC₀, h0⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ 0
  obtain ⟨Cj, hCj, hj⟩ := compact_family_mul_fourier_power_source_bound F hF K hK hsupp J hJ j
  refine ⟨2 ^ j * (C₀ + Cj), by positivity, ?_⟩
  intro W σ hσ w
  let S := (Finset.Iic (0, j)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hS : 0 ≤  S := by dsimp [S]; positivity
  have hsubset : Finset.Iic (0, 0) ⊆ Finset.Iic (0, j) := by
    intro p hp
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hp).trans (by simp))
  have hseminorm : (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤  S :=
    Seminorm.le_def.mp (Finset.sup_mono hsubset) W
  have hbase : ‖𝓕 (fun u => F σ u * W u) w‖ ≤  C₀ * S := by
    have hh : ‖𝓕 (fun u => F σ u * W u) w‖ ≤  C₀ * (Finset.Iic (0, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
      simpa using h0 W σ hσ w
    exact hh.trans (mul_le_mul_of_nonneg_left hseminorm hC₀.le)
  have hpower : |w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ ≤  Cj * S := hj W σ hσ w
  by_cases hw : |w| ≤  1
  · calc
      _ ≤  2 ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ ≤  2 ^ j * (C₀ * S) := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤  2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring
  · have hw' : 1 ≤  |w| := le_of_lt (lt_of_not_ge hw)
    calc
      _ ≤  (2 * |w|) ^ j * ‖𝓕 (fun u => F σ u * W u) w‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by linarith) j) (norm_nonneg _)
      _ = 2 ^ j * (|w| ^ j * ‖𝓕 (fun u => F σ u * W u) w‖) := by rw [mul_pow, mul_assoc]
      _ ≤  2 ^ j * (Cj * S) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤  2 ^ j * ((C₀ + Cj) * S) := by gcongr; linarith
      _ = _ := by dsimp [S]; ring

def negativeLogPullbackCLM (a b : ℝ) : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv).comp (logPullbackCLM a b)

theorem negativeLogPullbackCLM_eq_actual (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b) (u : ℝ) :
    negativeLogPullbackCLM a b W u = W (Real.exp (-u)) := by
  change logPullbackCLM a b W (-u) = _
  exact logPullbackCLM_eq_actual a b ha W hsupp (-u)

def logWeight (a b σ u : ℝ) : ℂ := (Real.exp (-σ * u) * logCutoff a b (-u) : ℝ)

theorem logWeight_smooth (a b : ℝ) : ContDiff ℝ ∞ (Function.uncurry (logWeight a b)) := by
  change ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((Real.exp (-p.1 * p.2) * logCutoff a b (-p.2) : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp
    ((Real.contDiff_exp.comp (contDiff_fst.neg.mul contDiff_snd)).mul
      ((logCutoff a b).contDiff.comp contDiff_snd.neg))

theorem logWeight_support (a b σ : ℝ) :
    Function.support (logWeight a b σ) ⊆ Metric.closedBall 0 (logRadius a b + 1) := by
  intro u hu
  have hc : logCutoff a b (-u) ≠ 0 := by
    intro hc
    exact hu (by simp [logWeight, hc])
  have hm : -u ∈ Function.support (logCutoff a b) := hc
  rw [(logCutoff a b).support_eq] at hm
  change dist (-u) 0 < logRadius a b + 1 at hm
  change dist u 0 ≤  logRadius a b + 1
  simpa only [dist_zero_right, norm_neg] using hm.le

theorem logWeight_mul_pullback (a b : ℝ) (ha : 0 < a) (W : SchwartzMap ℝ ℂ)
    (hsupp : Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b) (σ u : ℝ) :
    logWeight a b σ u * negativeLogPullbackCLM a b W u = mellinLogFamily W σ u := by
  rw [negativeLogPullbackCLM_eq_actual a b ha W hsupp]
  by_cases hW : W (Real.exp (-u)) = 0
  · simp [logWeight, mellinLogFamily, hW]
  · have hc := logCutoff_eq_one_of_source a b ha (-u) (hsupp hW)
    simp [logWeight, mellinLogFamily, hc]

theorem mellin_strip_source_bound (a b : ℝ) (ha : 0 < a) (lo hi : ℝ) (j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ σ ∈ Set.Icc lo hi, ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellin W ((σ : ℂ) + t * Complex.I)‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨C, hC, hb⟩ := compact_family_mul_fourier_weighted_source_bound
    (logWeight a b) (logWeight_smooth a b) (Metric.closedBall 0 (logRadius a b + 1))
    (isCompact_closedBall _ _) (logWeight_support a b) (Set.Icc lo hi) isCompact_Icc j
  obtain ⟨s, D, hD, hDbd⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
    (negativeLogPullbackCLM a b) (Finset.Iic (0, j))
  refine ⟨s, (1 + 2 * Real.pi) ^ j * C * D, by positivity, ?_⟩
  intro W hsupp σ hσ t
  have hfun : (fun u => logWeight a b σ u * negativeLogPullbackCLM a b W u) = mellinLogFamily W σ :=
    funext (logWeight_mul_pullback a b ha W hsupp σ)
  have hfour := hb (negativeLogPullbackCLM a b W) σ hσ (t / (2 * Real.pi))
  rw [hfun] at hfour
  have ht : |t| = (2 * Real.pi) * |t / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    field_simp
  have hbase : 1 + |t| ≤  (1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos, abs_nonneg (t / (2 * Real.pi))]
  rw [mellin_eq_logFamily_fourier]
  calc
    _ ≤  ((1 + 2 * Real.pi) * (1 + |t / (2 * Real.pi)|)) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1 + 2 * Real.pi) ^ j * ((1 + |t / (2 * Real.pi)|) ^ j *
        ‖𝓕 (mellinLogFamily W σ) (t / (2 * Real.pi))‖) := by rw [mul_pow, mul_assoc]
    _ ≤  (1 + 2 * Real.pi) ^ j * (C *
        (D * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) :=
      mul_le_mul_of_nonneg_left (hfour.trans (mul_le_mul_of_nonneg_left (hDbd W) hC.le)) (by positivity)
    _ = _ := by ring

theorem mellinData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        (1 + |t|) ^ j * ‖mellinData W ((σ : ℂ) + t * Complex.I)‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  let g : ℕ := 4 * A + 4
  obtain ⟨Cγ, hCγ, hγ⟩ := cubicReflectionGamma_strip_bound A
  obtain ⟨s, CV, hCV, hVb⟩ := mellin_strip_source_bound a b ha (-(A : ℝ)) (1 / 4) (g + j)
  refine ⟨s, Cγ * CV, mul_pos hCγ hCV, ?_⟩
  intro W hsupp σ hσ t
  have hσ' : -σ ∈ Set.Icc (-(A : ℝ)) (1 / 4) := by constructor <;> linarith [hσ.1, hσ.2]
  have hmb := hVb W hsupp (-σ) hσ' (-t)
  have heq : (-σ : ℝ) + (-t : ℝ) * Complex.I = -((σ : ℂ) + t * Complex.I) := by
    push_cast
    ring
  rw [heq, abs_neg] at hmb
  have hgb : ‖cubicReflectionGamma ((σ : ℂ) + t * Complex.I)‖ ≤  Cγ * (1 + |t|) ^ g := hγ σ hσ t
  rw [mellinData, norm_mul]
  calc
    _ = ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        ‖cubicReflectionGamma ((σ : ℂ) + t * Complex.I)‖ := by ring
    _ ≤  ((1 + |t|) ^ j * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) *
        (Cγ * (1 + |t|) ^ g) := mul_le_mul_of_nonneg_left hgb (by positivity)
    _ = Cγ * ((1 + |t|) ^ (g + j) * ‖mellin W (-((σ : ℂ) + t * Complex.I))‖) := by
      rw [pow_add]
      ring
    _ ≤  Cγ * (CV * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := mul_le_mul_of_nonneg_left hmb hCγ.le
    _ = _ := by ring

theorem mellinEulerData_strip_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ t : ℝ,
        ‖mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t ^ 2) := by
  obtain ⟨s, C, hC, hb⟩ := mellinData_strip_source_bound a b ha A (j + 2)
  refine ⟨s, ((A : ℝ) + 2) ^ j * C, by positivity, ?_⟩
  intro W hsupp σ hσ t
  apply weighted_two_to_cauchy (norm_nonneg _) t
  have hσabs : |σ| ≤  (A : ℝ) + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [hσ.1, hσ.2, (Nat.cast_nonneg A : (0 : ℝ) ≤  A)]
  have hz : ‖(σ : ℂ) + t * Complex.I‖ ≤  ((A : ℝ) + 2) * (1 + |t|) := by
    have hnorm := norm_add_le (σ : ℂ) ((t : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one] at hnorm
    nlinarith [abs_nonneg t, (Nat.cast_nonneg A : (0 : ℝ) ≤  A)]
  rw [mellinEulerData, norm_mul, norm_pow, norm_neg]
  calc
    _ ≤  (1 + |t|) ^ 2 * ((((A : ℝ) + 2) * (1 + |t|)) ^ j *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by gcongr
    _ = ((A : ℝ) + 2) ^ j * ((1 + |t|) ^ (j + 2) *
        ‖mellinData W ((σ : ℂ) + t * Complex.I)‖) := by rw [mul_pow, pow_add]; ring
    _ ≤  ((A : ℝ) + 2) ^ j * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) :=
      mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (by positivity)
    _ = _ := by ring

theorem mellinInv_euler_line_source_bound (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ), ∀ y : ℝ, 0 < y → 
        ‖mellinInv σ (mellinEulerData W j) y‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * y ^ (-σ) := by
  obtain ⟨s, C, hC, hb⟩ := mellinEulerData_strip_source_bound a b ha A j
  refine ⟨s, C / 2, by positivity, ?_⟩
  intro W hsupp σ hσ y hy
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hint : ‖∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * Complex.I)) *
        mellinEulerData W j ((σ : ℂ) + t * Complex.I)‖ ≤ 
      (y ^ (-σ) * (C * Q)) * Real.pi := by
    calc
      _ ≤  ∫ t : ℝ, (y ^ (-σ) * (C * Q)) * (1 + t ^ 2)⁻¹ := by
        apply norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul _)
        filter_upwards [] with t
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
        simpa only [div_eq_mul_inv, mul_assoc] using
          mul_le_mul_of_nonneg_left (hb W hsupp σ hσ t) (Real.rpow_nonneg hy.le (-σ))
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤  1 / (2 * Real.pi))]
  simp only [smul_eq_mul]
  calc
    _ ≤  (1 / (2 * Real.pi)) * ((y ^ (-σ) * (C * Q)) * Real.pi) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp [Q]; field_simp

theorem paperKernel_euler_source_power_decay (a b : ℝ) (ha : 0 < a) (A j : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ x : ℝ, 0 < x → 
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (1 / 4 : ℝ)) ∧
        (‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * x ^ (-(A : ℝ))) := by
  obtain ⟨s, C, hC, hb⟩ := mellinInv_euler_line_source_bound a b ha A j
  let B := max (paperScale ^ (1 / 4 : ℝ)) (paperScale ^ (-(A : ℝ)))
  have hB : 0 < B := lt_of_lt_of_le (Real.rpow_pos_of_pos paperScale_pos _) (le_max_left _ _)
  refine ⟨s, C * B, mul_pos hC hB, ?_⟩
  intro W hsupp x hx
  let Q := s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤  Q := by dsimp [Q]; positivity
  have hline (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ)) :
      ‖LocalLogFourier.eulerDeriv (paperKernel W) j x‖ ≤ 
        C * Q * (paperScale * x) ^ (-σ) := by
    have he : LocalLogFourier.eulerDeriv (paperKernel W) j x =
        paperKernelLogDerivative W j x := by
      simpa only [LocalLogFourier.eulerDeriv,Real.exp_zero,mul_one] using
        iteratedDeriv_paperKernel_exp W a b ha hsupp (W.smooth ⊤) x hx j 0
    rw [he,paperKernelLogDerivative]
    rw [mellinInv_euler_shift W a b ha hsupp (W.smooth ⊤) A j σ hσ _ (mul_pos paperScale_pos hx)]
    exact hb W hsupp σ hσ (paperScale * x) (mul_pos paperScale_pos hx)
  have hleft : -(1 / 4 : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · rfl
    · linarith [show (0 : ℝ) ≤  A from Nat.cast_nonneg A]
  have hright : (A : ℝ) ∈ Set.Icc (-(1 / 4 : ℝ)) (A : ℝ) := by
    constructor
    · linarith [show (0 : ℝ) ≤  A from Nat.cast_nonneg A]
    · rfl
  constructor
  · have hh := hline _ hleft
    rw [neg_neg, Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤  C * Q * (paperScale ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := hh
      _ = (C * paperScale ^ (1 / 4 : ℝ)) * Q * x ^ (1 / 4 : ℝ) := by ring
      _ ≤  (C * B) * Q * x ^ (1 / 4 : ℝ) := by
        gcongr
        exact le_max_left _ _
  · have hh := hline _ hright
    rw [Real.mul_rpow paperScale_pos.le hx.le] at hh
    calc
      _ ≤  C * Q * (paperScale ^ (-(A : ℝ)) * x ^ (-(A : ℝ))) := hh
      _ = (C * paperScale ^ (-(A : ℝ))) * Q * x ^ (-(A : ℝ)) := by ring
      _ ≤  (C * B) * Q * x ^ (-(A : ℝ)) := by
        gcongr
        exact le_max_right _ _

theorem paperKernel_euler_source_uniform_weighted_bound
    (a b : ℝ) (ha : 0 < a) (A K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ W : SchwartzMap ℝ ℂ, Function.support (W : ℝ →  ℂ) ⊆ Set.Icc a b → 
      ∀ i ≤  K, ∀ x : ℝ, 0 < x → 
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤ 
          C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  choose s c hc hb using fun i : Fin (K + 1) => paperKernel_euler_source_power_decay a b ha A i.val
  let S : Finset (ℕ × ℕ) := Finset.univ.biUnion s
  let D : ℝ := (∑ i : Fin (K + 1), c i) + 1
  have hD : 0 < D := by
    have hs : (0 : ℝ) ≤  ∑ i : Fin (K + 1), c i := Finset.sum_nonneg (fun i _ => (hc i).le)
    dsimp [D]
    linarith
  have hci (i : Fin (K + 1)) : c i ≤  D := by
    have hs : c i ≤  ∑ k : Fin (K + 1), c k :=
      Finset.single_le_sum (fun k _ => (hc k).le) (Finset.mem_univ i)
    dsimp [D]
    linarith
  refine ⟨S, 2 ^ A * (D + D), by positivity, ?_⟩
  intro W hsupp
  let Q := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hQ : 0 ≤  Q := by dsimp [Q]; positivity
  have hsource (i : Fin (K + 1)) : c i * (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤  D * Q := by
    have hsub : s i ⊆ S := Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hq : (s i).sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤  Q :=
      Seminorm.le_def.mp (Finset.sup_mono hsub) W
    exact mul_le_mul (hci i) hq (by positivity) hD.le
  have hsmall : ∀ i ≤  K, ∀ x : ℝ, 0 < x →  x ≤  1 → 
      ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤  D * Q := by
    intro i hi x hx hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hp : x ^ (1 / 4 : ℝ) ≤  1 := Real.rpow_le_one hx.le hx1 (by norm_num)
    calc
      _ ≤  (c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (1 / 4 : ℝ) := (hb k W hsupp x hx).1
      _ ≤  c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        simpa using mul_le_mul_of_nonneg_left hp (mul_nonneg (hc k).le (by positivity))
      _ ≤  D * Q := hsource k
  have hlarge : ∀ i ≤  K, ∀ x : ℝ, 1 ≤  x → 
      x ^ A * ‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ ≤  D * Q := by
    intro i hi x hx1
    have hx : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    let k : Fin (K + 1) := ⟨i, by omega⟩
    have hxpow : x ^ A ≠ 0 := pow_ne_zero A hx.ne'
    calc
      _ ≤  x ^ A * ((c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W) * x ^ (-(A : ℝ))) :=
        mul_le_mul_of_nonneg_left (hb k W hsupp x hx).2 (pow_nonneg hx.le A)
      _ = c k * (s k).sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
        rw [Real.rpow_neg hx.le, Real.rpow_natCast]
        field_simp
      _ ≤  D * Q := hsource k
  intro i hi x hx
  have hcoef : (2:ℝ)^A*(D*Q) ≤ (2^A*(D+D))*Q := by
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD.le) (by positivity)) hQ
  change _ ≤ (2^A*(D+D))*Q
  by_cases hx1 : x≤1
  · calc
      _ ≤ 2^A*‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith : 1+x≤2) A) (norm_nonneg _)
      _ ≤ 2^A*(D*Q) := mul_le_mul_of_nonneg_left (hsmall i hi x hx hx1) (by positivity)
      _ ≤ _ := hcoef
  · calc
      _ ≤ (2*x)^A*‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) (by linarith : 1+x≤2*x) A) (norm_nonneg _)
      _ = 2^A*(x^A*‖LocalLogFourier.eulerDeriv (paperKernel W) i x‖) := by rw [mul_pow,mul_assoc]
      _ ≤ 2^A*(D*Q) := mul_le_mul_of_nonneg_left (hlarge i hi x (by linarith)) (by positivity)
      _ ≤ _ := hcoef


end CompletedHeight

namespace CompletedHeight
open SchwartzPlanePoisson MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

/-- Multiplication by a fixed logarithmic cutoff costs a fixed finite derivative constant. -/
theorem localized_derivative_linear_bound
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ F : ℝ → ℝ → ℂ,
      (∀ R, 0 < R → ContDiff ℝ ∞ (F R)) → ∀ C : ℝ, 0 ≤ C →
      (∀ i ≤ j, ∀ R, 0 < R → ∀ u, |u| ≤ M →
        (1 + R)^N * ‖iteratedDeriv i (F R) u‖ ≤ C) →
      ∀ R, 0 < R → ∀ u,
        (1 + R)^N * ‖iteratedDeriv j (fun v => χ v * F R v) u‖ ≤ D*C := by
  have hχb (i : ℕ) : ∃ D : ℝ, 0 < D ∧ ∀ u ∈ Set.Icc (-M) M, ‖iteratedDeriv i χ u‖ ≤ D := by
    obtain ⟨D, hD⟩ := isCompact_Icc.bddAbove_image
      (hχ.continuous_iteratedDeriv i (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))).norm.continuousOn
    exact ⟨|D| + 1, by positivity, fun u hu =>
      (hD (Set.mem_image_of_mem _ hu)).trans (by linarith [le_abs_self D])⟩
  choose D hD hDb using hχb
  let B := ∑ i ∈ Finset.range (j + 1), ‖(j.choose i : ℂ)‖ * D i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (hD i).le)
  refine ⟨B + 1, by positivity, ?_⟩
  intro F hF C hC hCb R hR u
  by_cases hu : u ∈ Set.Icc (-M) M
  · have hprod := iteratedDeriv_mul (n := j) (x := u)
      (hχ.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
      ((hF R hR).of_le
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
    change (1 + R) ^ N * ‖iteratedDeriv j (χ * (fun v : ℝ => F R v)) u‖ ≤ _
    rw [hprod]
    calc
      _ ≤ (1 + R) ^ N * ∑ i ∈ Finset.range (j + 1),
          ‖(j.choose i : ℂ) * iteratedDeriv i χ u *
            iteratedDeriv (j - i) (fun v : ℝ => F R v) u‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ B * C := by
        rw [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_le_sum
        intro i hi
        have hDi := (hD i).le
        rw [norm_mul, norm_mul]
        calc
          _ = (‖(j.choose i : ℂ)‖ * ‖iteratedDeriv i χ u‖) *
              ((1 + R) ^ N * ‖iteratedDeriv (j - i) (fun v : ℝ => F R v) u‖) := by ring
          _ ≤ (‖(j.choose i : ℂ)‖ * D i) * C :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hDb i u hu) (norm_nonneg _))
              (hCb (j - i) (Nat.sub_le _ _) R hR u (abs_le.mpr hu)) (by positivity) (by positivity)
      _ ≤ (B + 1) * C := mul_le_mul_of_nonneg_right (by linarith) hC
  · have hsprod : Function.support (fun v : ℝ => χ v * F R v) ⊆ Set.Icc (-M) M := by
      intro v hv
      apply hχs
      intro hz
      exact hv (by simp only [hz, zero_mul])
    have hsd := (subset_tsupport (iteratedDeriv j (fun v : ℝ => χ v * F R v))).trans
      ((tsupport_iteratedDeriv_subset _ j).trans (closure_minimal hsprod isClosed_Icc))
    have hz : iteratedDeriv j (fun v : ℝ => χ v * F R v) u = 0 := by
      by_contra hn
      exact hu (hsd hn)
    rw [hz, norm_zero, mul_zero]
    positivity


/-- A compact derivative bound gives an explicit Fourier bound linear in its constant. -/
theorem compact_fourier_power_linear_bound
    (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F) (K : Set ℝ) (hK : IsCompact K)
    (hs : Function.support F ⊆ K) (P C : ℝ) (hP : 0 ≤ P) (hC : 0 ≤ C)
    (j : ℕ) (hb : ∀ u, P * ‖iteratedDeriv j F u‖ ≤ C) (t : ℝ) :
    P * (|t|^j * ‖𝓕 F t‖) ≤ C*(volume.real K+1)/(2*Real.pi)^j := by
  have hPR := hP
  have hcompact (n : ℕ) : HasCompactSupport (iteratedDeriv n F) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    exact (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ n).trans
      (closure_minimal hs hK.isClosed))
  have hi (n : ℕ) : Integrable (iteratedDeriv n F) :=
    (hF.continuous_iteratedDeriv n
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).integrable_of_hasCompactSupport (hcompact n)
  have hfour := Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hF
    (fun n _ => hi n) (by simp : (j : ℕ∞) ≤ ⊤)
  have hid : (2 * Real.pi) ^ j * (|t| ^ j * ‖𝓕 F t‖) =
      ‖𝓕 (iteratedDeriv j F) t‖ := by
    rw [hfour]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    ring
  have hsder : Function.support (iteratedDeriv j F) ⊆ K :=
    (subset_tsupport _).trans ((tsupport_iteratedDeriv_subset _ j).trans
      (closure_minimal hs hK.isClosed))
  have hzero : ∀ u, u ∉ K → P * ‖iteratedDeriv j F u‖ = 0 := by
    intro u hu
    have hz : iteratedDeriv j F u = 0 := by
      by_contra hn
      exact hu (hsder hn)
    rw [hz, norm_zero, mul_zero]
  have hI := norm_setIntegral_le_of_norm_le_const («μ» := volume)
    (f := fun u => P * ‖iteratedDeriv j F u‖) hK.measure_lt_top
    (C := C) (fun u _ => by rw [Real.norm_of_nonneg (by positivity)]; exact hb u)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    Real.norm_of_nonneg (integral_nonneg (fun _ => by positivity)), integral_const_mul] at hI
  have hFourier := mul_le_mul_of_nonneg_left
    (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ)
      (iteratedDeriv j F) t) hP
  apply (le_div_iff₀ (by positivity : 0 < (2 * Real.pi) ^ j)).mpr
  calc
    _ = P * ((2 * Real.pi) ^ j * (|t| ^ j * ‖𝓕 F t‖)) := by ring
    _ = P * ‖𝓕 (iteratedDeriv j F) t‖ := by rw [hid]
    _ ≤ C * volume.real K := hFourier.trans hI
    _ ≤ C * (volume.real K + 1) := mul_le_mul_of_nonneg_left (by linarith) hC


end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson
open scoped SchwartzMap
@[simp] lemma frequencyTwist_zero (g : 𝓢(ℝ,ℂ)) : frequencyTwist g 0=g := by
  ext x
  simp only [frequencyTwist_apply,kernelLogPhase,mul_zero,zero_mul,Complex.ofReal_zero,Complex.exp_zero,one_mul]
end JointLogSeparation

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
