import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourcePrincipalData

/-! The physical logarithmic source channel annihilates the entire original
principal half-square, including its mixed Weyl term. Actual Laplacians are used. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOpticalLogCusp
open D4BMJointSource D4BMGlobalAngularResponse D4BMAngularSeries D4BMModularCore
open D4BMHorizon
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Repeated actual hyperbolic angular Laplacians, without a supplied eigenvalue. -/
def laplacianJet : ℕ → Field → Field
  | 0,f => f
  | n+1,f => hyperbolicLaplacian (laplacianJet n f)

/-- The physical spin-two factor times the common logarithmic source polynomial. -/
def logarithmicChannel (q : XiZeroCopy) (f : Field) (z : Point) : ℂ :=
  let lam := (q.1:ℂ)*((q.1:ℂ)-1);
  -laplacianJet 4 f z+4*(2*lam+1)*laplacianJet 3 f z-
    4*(lam+1)*(4*lam+1)*laplacianJet 2 f z+8*lam*(4*lam+1)*laplacianJet 1 f z

private theorem positive_nhds (z : Point) (hz : 0 < z 1) :
    {w : Point | 0 < w 1} ∈ 𝓝 z :=
  (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz

private def principalJet (q : XiZeroCopy) (n : ℕ) (z : Point) : ℂ :=
  ∑ i : Fin 3, principalAmplitude q i*(principalExponent q i*(principalExponent q i-1))^n*
    (z 1:ℂ)^(principalExponent q i)

private theorem laplacian_sum {ι : Type*} (s : Finset ι) (f : ι → Point → ℂ)
    (z : Point) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hyperbolicLaplacian (fun x => ∑ i ∈ s, f i x) z = ∑ i ∈ s, hyperbolicLaplacian (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty,zero_mul] using
      (hyperbolicLaplacian_const_mul (f := fun _ : Point => (1:ℂ)) (z := z) contDiffAt_const (0:ℂ))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [hyperbolicLaplacian_add (hf i (Finset.mem_insert_self _ _))
      (ContDiffAt.sum (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem principalJet_next (q : XiZeroCopy) (n : ℕ) (z : Point) (hz : 0 < z 1) :
    hyperbolicLaplacian (principalJet q n) z = principalJet q (n+1) z := by
  have hp (i : Fin 3) : ContDiffAt ℝ 2 (fun x : Point => (x 1:ℂ)^(principalExponent q i)) z :=
    (height_cpow_contDiffOn (principalExponent q i) 2).contDiffAt (positive_nhds z hz)
  unfold principalJet
  rw [laplacian_sum _ _ z (fun i _ => contDiffAt_const.mul (hp i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hyperbolicLaplacian_const_mul (hp i),height_cpow_hyperbolicLaplacian _ z hz,pow_succ]
  ring

private theorem principal_laplacianJet (q : XiZeroCopy) (n : ℕ) (z : Point) (hz : 0 < z 1) :
    laplacianJet n (principalSquare q) z = principalJet q n z := by
  induction n generalizing z with
  | zero => simpa only [laplacianJet,principalJet,pow_zero,mul_one] using principalSquare_expansion q z hz
  | succ n ih =>
    have he : laplacianJet n (principalSquare q) =ᶠ[𝓝 z] principalJet q n := by
      filter_upwards [positive_nhds z hz] with w hw
      exact ih w hw
    change hyperbolicLaplacian (laplacianJet n (principalSquare q)) z=principalJet q (n+1) z
    rw [hyperbolicLaplacian_congr he,principalJet_next q n z hz]

/-- The logarithmic tail's physical angular channel removes all three literal
cusp-principal powers at every Xi occurrence, retaining the original Weyl coefficients. -/
theorem principalSquare_logarithmicChannel (q : XiZeroCopy) (z : UpperHalfPlane) :
    logarithmicChannel q (principalSquare q) (coordinates z)=0 := by
  unfold logarithmicChannel
  simp_rw [principal_laplacianJet q _ (coordinates z) z.im_pos]
  simp only [principalJet,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,principalExponent,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

end
end RHTower.D4BMOpticalLogCusp
