import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.GapGrid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import Mathlib.MeasureTheory.Integral.Prod

/-! # Gaussian mass retained by one-block spectral dilations -/
open Set MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section
variable {ι : Type*} [Fintype ι]
private abbrev law (ι : Type*) [Fintype ι] := Measure.pi fun _ : ι => gaussianReal 0 1

/-- If one of N contractions between one half and one carries each
sample in E to F, the standard Gaussian mass of F is at least
μ(E)/(N·2ᵈ). The scale may depend on the whole sample. -/
theorem gaussian_grid_cover {N : ℕ} (E F : Set (ι→ℝ)) (hF : MeasurableSet F)
    (hcover : ∀ x∈E, ∃ k : Fin N, scale k • x ∈ F) :
    (law ι).real E ≤ (N:ℝ)*2^(Fintype.card ι)*(law ι).real F := by
  let μ := law ι
  let S (k : Fin N) := (fun x : ι→ℝ => scale k • x) ⁻¹' F
  have hS (k : Fin N) : MeasurableSet (S k) :=
    hF.preimage (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i))
  have hm (k : Fin N) : μ.real (S k) ≤ (2:ℝ)^(Fintype.card ι)*μ.real F := by
    have hs := scale_mem k
    have hp : 0<scale k := (by norm_num : (0:ℝ)<1/2).trans_le hs.1
    have hd := PrescribedTimes.gaussian_dilation_comparison ((one_le_inv₀ hp).mpr hs.2) (S k) (hS k)
    have hback : (fun x : ι→ℝ => (scale k)⁻¹ • x) ⁻¹' S k=F := by
      ext x
      change scale k • ((scale k)⁻¹ • x)∈F ↔ x∈F
      rw [smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
    rw [hback] at hd
    have htwo : (scale k)⁻¹≤2 := (inv_le_comm₀ hp (by norm_num)).mpr
      (by simpa only [show (2:ℝ)⁻¹=1/2 by norm_num] using hs.1)
    exact hd.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (inv_nonneg.mpr hp.le) htwo _) measureReal_nonneg)
  have hsub : E ⊆ ⋃ k, S k := fun x hx => mem_iUnion.mpr (hcover x hx)
  calc μ.real E ≤ μ.real (⋃ k, S k) := measureReal_mono hsub
       _ ≤ ∑ k, μ.real (S k) := measureReal_iUnion_fintype_le _
       _ ≤ ∑ _ : Fin N, (2:ℝ)^(Fintype.card ι)*μ.real F := Finset.sum_le_sum (fun k _ => hm k)
       _ = _ := by rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc]

/-- Fixing the left block reduces the tensor-sum gap requirement to
a right-block Gaussian event. The only scaling law needed is the
homogeneity of the actual right energies. -/
theorem spectral_section_mass {I J : Type*} [Fintype I] [Fintype J]
    (a : I→ℝ) (b : (ι→ℝ)→J→ℝ) (hf : ∀ c : ℝ, 0<c → ∀ x j, b (c • x) j=c*b x j)
    (E : Set (ι→ℝ)) {g : ℝ} (hg : 0<g) (ha : ∀ i j, i≠j → g ≤ |a i-a j|)
    (hb : ∀ x∈E, ∀ i j, i≠j → g ≤ |b x i-b x j|) (hmeas : ∀ j, Measurable fun x => b x j) :
    let N := Fintype.card ((I×J)×(I×J))+1
    let F := {x : ι→ℝ | ∀ u v : I×J, u≠v →
      g/(8*(N:ℝ)) ≤ |(a u.1+b x u.2)-(a v.1+b x v.2)|}
    (law ι).real E ≤ (N:ℝ)*2^(Fintype.card ι)*(law ι).real F := by
  intro N F
  have hF : MeasurableSet F := by
    simp only [F,setOf_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ =>
      measurableSet_le measurable_const (((measurable_const.add (hmeas u.2)).sub
        (measurable_const.add (hmeas v.2))).abs)
  apply gaussian_grid_cover (N:=N) E F hF
  intro x hx
  obtain ⟨k,hk⟩ := exists_separated_scale a (b x) hg ha (hb x hx)
  have hp : 0<scale k := (by norm_num : (0:ℝ)<1/2).trans_le (scale_mem k).1
  exact ⟨k,fun u v huv => by simpa only [hf _ hp] using hk u v huv⟩

#print axioms spectral_section_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
