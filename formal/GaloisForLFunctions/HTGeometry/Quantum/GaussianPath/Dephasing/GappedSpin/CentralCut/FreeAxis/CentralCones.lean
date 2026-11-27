import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.QubitFrame

/-! # Distinguishing spin axes by the physical central field -/
open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
noncomputable section

theorem SpinFrame.entry_le (F : SpinFrame) (i j : Fin 3) : |F.R i j| ≤ 1 := by
  have he := congrFun (congrFun F.orthogonal j) j
  have hs : ∑ k, (F.R k j)^2 = 1 := by
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,←sq,Matrix.one_apply_eq] using he
  have h := single_le_sum (fun (k : Fin 3) _ => sq_nonneg (F.R k j)) (mem_univ i)
  rw [hs] at h
  exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa only [sq_abs,one_pow] using h)

/-- Two residuals in slope coordinates specify the narrow cone seen
from the central onsite field. -/
def SlopeCone (p q δ : ℝ) (v : Fin 3→ℝ) : Prop :=
  1/8 ≤ v 2 ∧ |v 0-p*v 2| ≤ 6*δ ∧ |v 1-q*v 2| ≤ 6*δ

theorem rotated_field_cone (F : SpinFrame) {p q δ : ℝ} (hp : |p|≤2) (hq : |q|≤2)
    (hcol : 1/3 ≤ F.R 2 2) (hx : F.R 0 2=p*F.R 2 2) (hy : F.R 1 2=q*F.R 2 2)
    (hδ : δ ≤ 1/3600) (w : Fin 3→ℝ) (hw : 1/2 ≤ w 2)
    (hu : |w 0| ≤ δ) (hv : |w 1| ≤ δ) : SlopeCone p q δ (F.R *ᵥ w) := by
  let v := F.R *ᵥ w
  have herr (i : Fin 3) : |v i-F.R i 2*w 2| ≤ 2*δ := by
    change |(∑ j, F.R i j*w j)-_| ≤ _
    rw [Fin.sum_univ_three,add_sub_cancel_right]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_mul]
    have h₀ := mul_le_mul (F.entry_le i 0) hu (abs_nonneg _) zero_le_one
    have h₁ := mul_le_mul (F.entry_le i 1) hv (abs_nonneg _) zero_le_one
    linarith only [h₀,h₁]
  have hs (i : Fin 3) (a : ℝ) (ha : |a|≤2) (hh : F.R i 2=a*F.R 2 2) :
      |v i-a*v 2| ≤ 6*δ := by
    have he : v i-a*v 2=(v i-F.R i 2*w 2)-a*(v 2-F.R 2 2*w 2) := by rw [hh]; ring
    rw [he]
    apply (show |(v i-F.R i 2*w 2)-a*(v 2-F.R 2 2*w 2)| ≤
      |v i-F.R i 2*w 2|+|a*(v 2-F.R 2 2*w 2)| by
      simpa only [sub_zero,zero_sub,abs_neg] using
        abs_sub_le (v i-F.R i 2*w 2) 0 (a*(v 2-F.R 2 2*w 2))).trans
    rw [abs_mul]
    have hb := mul_le_mul ha (herr 2) (abs_nonneg _) (by norm_num)
    linarith only [herr i,hb]
  refine ⟨?_,hs 0 p hp hx,hs 1 q hq hy⟩
  have hl := mul_le_mul hcol hw (by norm_num) ((by norm_num : (0:ℝ)≤1/3).trans hcol)
  have he := (abs_le.mp (herr 2)).1
  change 1/8 ≤ v 2
  linarith only [hl,he,hδ]

/-- If two cones contain one field, each slope differs by at most 96δ. -/
theorem common_cone_slopes {p q p' q' δ : ℝ} {v : Fin 3→ℝ}
    (h : SlopeCone p q δ v) (h' : SlopeCone p' q' δ v) :
    |p-p'| ≤ 96*δ ∧ |q-q'| ≤ 96*δ := by
  have bound {a b t : ℝ} (ha : |t-a*v 2|≤6*δ) (hb : |t-b*v 2|≤6*δ) :
      |a-b| ≤ 96*δ := by
    have hw : |(a-b)*v 2| ≤ 12*δ := by
      rw [show (a-b)*v 2=(t-b*v 2)-(t-a*v 2) by ring]
      have ht := abs_sub_le (t-b*v 2) 0 (t-a*v 2)
      rw [sub_zero,zero_sub,abs_neg] at ht
      exact ht.trans (by linarith only [ha,hb])
    rw [abs_mul,abs_of_nonneg ((by norm_num : (0:ℝ)≤1/8).trans h.1)] at hw
    have hz := mul_le_mul_of_nonneg_left h.1 (abs_nonneg (a-b))
    linarith only [hz,hw]
  exact ⟨bound h.2.1 h'.2.1,bound h.2.2 h'.2.2⟩

#print axioms common_cone_slopes
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
