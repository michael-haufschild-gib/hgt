import GaloisForLFunctions.HTGeometry.PolyatomicHilbertGeometry
import GaloisForLFunctions.HTGeometry.HalfLineExponentialGram

/-!
# Exact finite spectral separation of fractional collision-energy features

The Gamma weight from the auxiliary Laplace factorization never vanishes
on the positive half-line. Removing that common weight transfers every
finite linear relation to the corpus's Cauchy-Gram exponential system.
Consequently the fractional-energy Gram matrix is nonsingular exactly
when its squared-energy nodes are distinct, for every finite size and
every positive real shape. No lower separation bound is needed.
-/

open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The positive decay rate of one energy feature. -/
def collisionFeatureRate (e x : ℝ) : ℝ := Real.exp e / 2 + x ^ 2

theorem collisionFeatureRate_pos (e x : ℝ) : 0 < collisionFeatureRate e x := by
  unfold collisionFeatureRate
  positivity

/-- Native Cauchy-Gram exponential with the collision feature's decay rate. -/
def collisionUnweightedAtom (e x : ℝ) :=
  expFeature (collisionFeatureRate e x) (collisionFeatureRate_pos e x)

/-- The unweighted atom has its literal real-exponential representative. -/
theorem collisionUnweightedAtom_ae (e x : ℝ) :
    (collisionUnweightedAtom e x : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t => (Real.exp (-collisionFeatureRate e x * t) : ℂ)) := by
  have h := (halfLineLaplaceFeatureRaw_memLp
    (show 0 < (collisionFeatureRate e x : ℂ).re from collisionFeatureRate_pos e x)).coeFn_toLp
  filter_upwards [h] with t ht
  change (collisionUnweightedAtom e x : ℝ → ℂ) t =
    halfLineLaplaceFeatureRaw (collisionFeatureRate e x) t at ht
  rw [ht]
  simp only [halfLineLaplaceFeatureRaw, RCLike.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp]

/-- The common Gamma half-density factors out of every finite relation in the actual L² space. -/
theorem collisionLaplaceAtom_sum_weight {n : ℕ}
    (a e : ℝ) (x : Fin n → ℝ) (c : Fin n → ℂ) :
    (fun t => (∑ i, c i • collisionLaplaceAtom a e (x i)) t) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))]
      (fun t => ((t ^ ((Real.exp a - 1) / 2) : ℝ) : ℂ) *
        (∑ i, c i • collisionUnweightedAtom e (x i)) t) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => c i • collisionLaplaceAtom a e (x i)),
    Lp.coeFn_finsetSum Finset.univ (fun i => c i • collisionUnweightedAtom e (x i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (collisionLaplaceAtom a e (x i))),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (collisionUnweightedAtom e (x i))),
    ae_all_iff.mpr (fun i => collisionLaplaceAtom_ae a e (x i)),
    ae_all_iff.mpr (fun i => collisionUnweightedAtom_ae e (x i))]
    with t hsumW hsumU hsmulW hsmulU hW hU
  rw [hsumW, hsumU]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hsmulW hsmulU ⊢
  simp_rw [hsmulW, hsmulU, hW, hU]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [collisionLaplaceFeature, collisionFeatureRate, Complex.ofReal_mul]
  ring

/-- Complete classification of finite independence: only repeated squared energies cause loss. -/
theorem collisionLaplaceAtom_linearIndependent_iff {n : ℕ}
    (a e : ℝ) (x : Fin n → ℝ) :
    LinearIndependent ℂ (fun i => collisionLaplaceAtom a e (x i)) ↔
      Function.Injective (fun i => x i ^ 2) := by
  constructor
  · intro h i j hij
    exact h.injective ((collisionLaplaceAtom_eq_iff a e (x i) (x j)).mpr hij)
  · intro hinj
    have hrate : Function.Injective (fun i => collisionFeatureRate e (x i)) := by
      intro i j h
      apply hinj
      unfold collisionFeatureRate at h
      linarith
    have hbase := linearIndependent_expFeature
      (fun i => collisionFeatureRate e (x i))
      (fun i => collisionFeatureRate_pos e (x i)) hrate
    rw [Fintype.linearIndependent_iff] at hbase ⊢
    intro c hc i
    apply hbase c ?_ i
    change (∑ i, c i • collisionUnweightedAtom e (x i)) = 0
    apply Lp.ext
    filter_upwards [collisionLaplaceAtom_sum_weight a e x c,
      Lp.coeFn_zero ℂ 2 (volume.restrict (Ioi (0 : ℝ))),
      ae_restrict_mem measurableSet_Ioi] with t hweight hzero ht
    have hnonzero : ((t ^ ((Real.exp a - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos ht _))
    rw [hc, hzero] at hweight
    have hz := (mul_eq_zero.mp hweight.symm).resolve_left hnonzero
    exact hz.trans hzero.symm

/-- Every finite completed Gram matrix is invertible precisely at distinct squared energies. -/
theorem collisionLaplaceAtom_gram_det_ne_zero_iff {n : ℕ}
    (a e : ℝ) (x : Fin n → ℝ) :
    (Matrix.gram ℂ (fun i => collisionLaplaceAtom a e (x i))).det ≠ 0 ↔
      Function.Injective (fun i => x i ^ 2) := by
  rw [Matrix.det_gram_ne_zero_iff_linearIndependent,
    collisionLaplaceAtom_linearIndependent_iff]

end GaloisForLFunctions.HTGeometry
