import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.CauchyJumpDimension
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.GaussianProbeFlatLimit
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Short-time separation of Cauchy and Gaussian probe volumes

Subtracting multiples of the first row of an entrywise exponential
matrix leaves an n by n block vanishing at zero. Its derivative is the
double-centered exponent table. Thus n+1 distinct Cauchy rates open
to order n. The Gaussian weak-step limit opens to order n(n+1)/2.
-/

noncomputable section
open Finset Matrix Filter
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.ProbeVolume
open LogCauchy JumpGrid HilbertMetric.CauchyDephasing
variable {n : ℕ}

/-- Entrywise exponential evolution with generator table D. -/
def attenuation (D : Table n) (t : ℝ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i j => Real.exp (-t*D i j)

/-- Mixed difference of the exponent based at the first row and column. -/
def tangent (D : Table n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (D i.succ 0+D 0 j.succ-D 0 0)-D i.succ j.succ

private def block (D : Table n) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.exp (-t*D i.succ j.succ)-Real.exp (-t*(D i.succ 0+D 0 j.succ-D 0 0))

private theorem eliminate (D : Table n) (t : ℝ) :
    (attenuation D t).det=Real.exp (-t*D 0 0)*(block D t).det := by
  let A := attenuation D t
  let c := fun i => if i=0 then 0 else -Real.exp (-t*(D i 0-D 0 0))
  let B := Matrix.of fun i j => A i j+c i*A 0 j
  have prod (i j) : Real.exp (-t*(D i 0-D 0 0))*Real.exp (-t*D 0 j)=
      Real.exp (-t*(D i 0+D 0 j-D 0 0)) := by rw [← Real.exp_add]; congr 1; ring
  have he : B.det=A.det :=
    det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (fun _ _ => rfl)
  have off (i j) (hi : i≠0) : B i j=Real.exp (-t*D i j)-Real.exp (-t*(D i 0+D 0 j-D 0 0)) := by
    change Real.exp (-t*D i j)+(if i=0 then 0 else -Real.exp (-t*(D i 0-D 0 0)))*Real.exp (-t*D 0 j)=_
    rw [if_neg hi,neg_mul (Real.exp _) (Real.exp _),prod]
    exact (sub_eq_add_neg _ _).symm
  have hb : B.submatrix Fin.succ Fin.succ=block D t := by
    ext i j
    exact off i.succ j.succ (Fin.succ_ne_zero i)
  change A.det=_
  rw [← he,det_succ_column_zero,sum_eq_single 0]
  · simp only [Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero,hb]
    congr 1
    simp [B,c,A,attenuation]
  · intro i _ hi
    rw [off _ _ hi,add_sub_cancel_right,sub_self,mul_zero,zero_mul]
  · simp

private theorem tangent_limit (D : Table n) :
    Tendsto (fun t : ℝ => t⁻¹ • block D t) (𝓝[≠] 0) (𝓝 (tangent D)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let a := D i.succ j.succ
  let b := D i.succ 0+D 0 j.succ-D 0 0
  have diff (c : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-t*c)) (-c) 0 := by
    simpa only [Pi.neg_apply,id_eq,neg_zero,zero_mul,Real.exp_zero,one_mul,neg_one_mul] using
      ((hasDerivAt_id (0:ℝ)).neg.mul_const c).exp
  have h := ((diff a).sub (diff b)).tendsto_slope_zero
  simpa only [Pi.sub_apply,Matrix.smul_apply,smul_eq_mul,block,tangent,Matrix.of_apply,a,b,zero_add,neg_zero,zero_mul,
    Real.exp_zero,sub_self,sub_zero,neg_sub_neg] using h

/-- All real exponent tables have the same first possible volume coefficient,
including nonsymmetric tables with arbitrary diagonal entries. -/
theorem exponential_tangent (D : Table n) :
    Tendsto (fun t : ℝ => (attenuation D t).det/t^n) (𝓝[≠] 0) (𝓝 (tangent D).det) := by
  have hdet := (continuous_id.matrix_det.tendsto (tangent D)).comp (tangent_limit D)
  have hhead : Tendsto (fun t : ℝ => Real.exp (-t*D 0 0)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (-t*D 0 0)) := by fun_prop
    exact (hc.tendsto' 0 1 (by simp)).mono_left nhdsWithin_le_nhds
  have h := hhead.mul hdet
  rw [one_mul] at h
  apply h.congr' (Eventually.of_forall ?_)
  intro t
  change Real.exp (-t*D 0 0)*(t⁻¹ • block D t).det=_
  rw [eliminate,det_smul,Fintype.card_fin,inv_pow]
  ring

def cauchyDet (v : Nodes n) (t : ℝ) := (Matrix.of fun i j => (coherence (v i) (v j))^t).det

private theorem cauchy_attenuation (v : Nodes n) (t : ℝ) :
    (attenuation (logTable v) t).det=cauchyDet v t := by
  unfold cauchyDet attenuation
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.of_apply,logTable,cost,Real.rpow_def_of_pos (coherence_pos _ _),neg_mul_neg,mul_comm t]

/-- The finite Cauchy probe has strictly positive leading coefficient at
every distinct rate grid, including grids of one or two rates. -/
theorem cauchy_volume_limit (v : Nodes n) :
    0<(tangent (logTable v)).det ∧
    Tendsto (fun t : ℝ => cauchyDet v t/t^n) (𝓝[≠] 0) (𝓝 (tangent (logTable v)).det) := by
  have he : tangent (logTable v)=(4:ℝ)⁻¹ • anchored (logTable v) := by
    ext i j
    simp only [tangent,of_apply,logTable,cost,coherence_self,Real.log_one,neg_zero,sub_zero,
      anchored,Matrix.smul_apply,smul_eq_mul,coherence_symm (v i.succ) (v 0)]
    ring
  constructor
  · rw [he,det_smul,Fintype.card_fin]
    exact mul_pos (by positivity) (log_anchored_posDef v).det_pos
  · simpa only [cauchy_attenuation] using exponential_tangent (logTable v)

private theorem order_succ (n : ℕ) : GaussianVolume.order (n+1)=GaussianVolume.order n+n := by
  simp only [GaussianVolume.order,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]

/-- The ratio of the two actual volume observables has exact opening order
n(n−1)/2 on n+1 distinct ordered momenta. Its normalized limit is positive. -/
theorem gaussian_cauchy_volume_ratio (v : Fin (n+1) ↪o ℝ) :
    let r : Nodes n := ⟨v,v.injective⟩
    let c := GaussianVolume.coefficient v v/(tangent (logTable r)).det
    0<c ∧ Tendsto (fun t : ℝ => (GaussianVolume.determinant v v t/cauchyDet r t)/t^(GaussianVolume.order n))
      (𝓝[≠] 0) (𝓝 c) := by
  intro r c
  obtain ⟨hp,hg⟩ := GaussianVolume.gaussian_flat_limit v v
  obtain ⟨hq,hc⟩ := cauchy_volume_limit r
  refine ⟨div_pos hp hq, (hg.div hc hq.ne').congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin (s:=({0}:Set ℝ)ᶜ) (a:=0)] with t ht
  have ne : t≠0 := ht
  change (GaussianVolume.determinant v v t/t^(GaussianVolume.order (n+1)))/(cauchyDet r t/t^n)=_
  rw [order_succ,pow_add]
  by_cases z : cauchyDet r t=0
  · simp [z]
  · field_simp [ne,z]

/-- The signed Weil measurement after exponential attenuation of its entries. -/
def snapshot (D : Table n) (p : Fin (n+1) → {x : ℝ // 1≤x}) (t : ℝ) :=
  Matrix.of fun i j => (attenuation D t i j : ℂ)*probeGram (fun k => (p k).val) i j

/-- The Gaussian measurement is a single momentum jump. The Cauchy
measurement is the limit of the contrast-power jumps at any reference rate. -/
theorem snapshot_channels (v : Nodes n) (p : Fin (n+1) → {x : ℝ // 1≤x}) (t o : ℝ) :
    let W := probeGram (fun k => (p k).val)
    snapshot (gaussianTable v) p t=jumpEvolution t (fun _ : Fin 1 => (v : Fin (n+1) → ℝ)) W ∧
      Tendsto (fun N : ℕ => jumpEvolution t (fun k : Fin N => fun i => jump o k.val (v i)) W)
        atTop (𝓝 (snapshot (logTable v) p t)) := by
  intro W
  constructor
  · ext i j
    simp only [snapshot,attenuation,of_apply,gaussianTable,jumpEvolution,jointCost,Fin.sum_univ_one,W]
  · simpa only [snapshot,attenuation,of_apply,logTable,cost,neg_mul_neg,
      Real.rpow_def_of_pos (coherence_pos _ _),mul_comm t,W] using truncated_evolution v o t W

/-- Compare two recorded matrices entry by entry before taking their determinant. -/
def volumeBetween (later earlier : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :=
  (Matrix.of fun i j => (later i j/earlier i j).re).det

/-- Two measured Weil matrices determine the exact determinant at their time
lag. Neither the starting time nor the unattenuated matrix is needed. -/
theorem snapshot_volume (D : Table n) (p : Fin (n+1) → {x : ℝ // 1≤x}) (s t : ℝ) :
    volumeBetween (snapshot D p (s+t)) (snapshot D p s)=(attenuation D t).det := by
  unfold volumeBetween
  apply congrArg Matrix.det
  ext i j
  have factor : attenuation D (s+t) i j=attenuation D t i j*attenuation D s i j := by
    change Real.exp (_)=Real.exp (_)*Real.exp (_)
    rw [←Real.exp_add]
    congr 1
    ring
  have nz : snapshot D p s i j≠0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) (safe_probeGram_entry_ne_zero p i j)
  have entry : snapshot D p (s+t) i j/snapshot D p s i j=(attenuation D t i j : ℂ) := by
    apply (div_eq_iff nz).mpr
    simp only [snapshot,of_apply,factor,Complex.ofReal_mul,mul_assoc]
  change (snapshot D p (s+t) i j/snapshot D p s i j).re=attenuation D t i j
  simp only [entry,Complex.ofReal_re]

/-- The two volume exponents can be distinguished using pairs of observations
started at independently chosen times on independently chosen Weil probes. -/
theorem measured_volume_ratio (v : Fin (n+1) ↪o ℝ)
    (p q : Fin (n+1) → {x : ℝ // 1≤x}) (a b : ℝ) :
    let r : Nodes n := ⟨v,v.injective⟩
    let G := snapshot (gaussianTable r) p
    let C := snapshot (logTable r) q
    let c := GaussianVolume.coefficient v v/(tangent (logTable r)).det
    0<c ∧ Tendsto (fun h : ℝ => (volumeBetween (G (a+h)) (G a)/volumeBetween (C (b+h)) (C b))/
      h^(GaussianVolume.order n)) (𝓝[≠] 0) (𝓝 c) := by
  dsimp only
  simp only [snapshot_volume,cauchy_attenuation]
  exact gaussian_cauchy_volume_ratio v

#print axioms exponential_tangent
#print axioms cauchy_volume_limit
#print axioms gaussian_cauchy_volume_ratio
#print axioms snapshot_channels
#print axioms snapshot_volume
#print axioms measured_volume_ratio
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk.ProbeVolume
