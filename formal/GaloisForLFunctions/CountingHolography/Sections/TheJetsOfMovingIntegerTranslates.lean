import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm

/-!
# Regularized jets under moving integer dilations

Translating the packet by log d changes the resolution from r to dr.
The degree indices, their off-diagonal kernel and their logarithmic
counterterms agree exactly on the common support.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open AbsoluteGeometryOfSpecZ Finset Filter Topology Zeta23

private def jetOn (v : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  (∑ n ∈ S, ∑ m ∈ S.erase n, v m*v n*levyKernel m n)-
    ∑ n ∈ S, v n^2/n*Real.log ((n:ℝ)/(2*Real.pi))

private theorem jetOn_congr {S : Finset ℕ} {v w : ℕ → ℝ} (h : ∀ j ∈ S, v j=w j) :
    jetOn v S = jetOn w S := by
  unfold jetOn
  refine congrArg₂ (· - ·) (sum_congr rfl fun n hn => sum_congr rfl fun m hm => ?_)
    (sum_congr rfl fun n hn => ?_)
  · rw [h m (mem_of_mem_erase hm),h n hn]
  · rw [h n hn]

private theorem jetOn_restrict {S T : Finset ℕ} (v : ℕ → ℝ) (ht : T ⊆ S)
    (hz : ∀ j ∈ S, j ∉ T → v j=0) : jetOn v S=jetOn v T := by
  have hout : (∑ n ∈ S, ∑ m ∈ S.erase n, v m*v n*levyKernel m n)=
      ∑ n ∈ T, ∑ m ∈ S.erase n, v m*v n*levyKernel m n :=
    (sum_subset ht fun n hn hn' => sum_eq_zero fun m _ => by rw [hz n hn hn',mul_zero,zero_mul]).symm
  unfold jetOn
  rw [hout]
  refine congrArg₂ (· - ·) (sum_congr rfl fun n _ => (sum_subset (erase_subset_erase n ht) ?_).symm)
    (sum_subset ht fun n hn hn' => by simp only [hz n hn hn',zero_pow (by decide : 2 ≠ 0),zero_div,zero_mul]).symm
  intro m hm hm'
  rw [hz m (mem_of_mem_erase hm) (fun h => hm' (mem_erase.mpr ⟨(mem_erase.mp hm).1,h⟩)),zero_mul,zero_mul]

/-- An integer translate on the original window gives exactly the regularized
jet of the fixed packet at the dilated resolution, provided the window reaches
the packet's right support endpoint. -/
theorem degreeForm_log_dilate {f : ℝ → ℝ} {K d r L : ℕ}
    (hs : ∀ u, u ≤ 0 ∨ Real.log K ≤ u → f u=0) (hK : 0 < K) (hd : 0 < d) (hr : 0 < r)
    (hcover : K*d ≤ 1+L) :
    degreeForm (fun u => f (u-Real.log d)) L r = degreeForm f (3*K) (d*r) := by
  let R := d*r
  let S := Ioc r (r+L*r)
  let S' := Ioc R (R+3*K*R)
  let T := Ioc R (K*R)
  let v := degreeSample f R
  have hR : 0 < R := Nat.mul_pos hd hr
  have hR' : 0 < (R:ℝ) := Nat.cast_pos.mpr hR
  have hrR : r ≤ R := Nat.le_mul_of_pos_left r hd
  have hupper : K*R ≤ r+L*r := by
    simpa only [R,← Nat.mul_assoc,Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right r hcover
  have ht : T ⊆ S := fun j hj => mem_Ioc.mpr ⟨hrR.trans_lt (mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2.trans hupper⟩
  have ht' : T ⊆ S' := by
    have hh : K*R ≤ R+3*K*R := by
      rw [Nat.mul_assoc]; omega
    exact fun j hj => mem_Ioc.mpr ⟨(mem_Ioc.mp hj).1,(mem_Ioc.mp hj).2.trans hh⟩
  have outside {j : ℕ} (hj : 0 < j) (h : j ∉ T) : v j=0 := by
    change f (Real.log ((j:ℝ)/R)) = 0
    apply hs
    by_cases hlow : j ≤ R
    · exact Or.inl (Real.log_nonpos (div_nonneg (Nat.cast_nonneg _) hR'.le)
        ((div_le_one hR').mpr (by exact_mod_cast hlow)))
    · have hhi : K*R < j := lt_of_not_ge (fun hh => h (mem_Ioc.mpr ⟨lt_of_not_ge hlow,hh⟩))
      exact Or.inr (Real.log_le_log (Nat.cast_pos.mpr hK) ((le_div_iff₀ hR').mpr (by exact_mod_cast hhi.le)))
  have align {j : ℕ} (hj : 0 < j) : degreeSample (fun u => f (u-Real.log d)) r j=v j := by
    change f (Real.log ((j:ℝ)/r)-Real.log d)=f (Real.log ((j:ℝ)/(d*r:ℕ)))
    rw [← Real.log_div (div_pos (Nat.cast_pos.mpr hj) (Nat.cast_pos.mpr hr)).ne' (Nat.cast_pos.mpr hd : 0 < (d:ℝ)).ne',
      Nat.cast_mul,div_div,mul_comm (r:ℝ)]
  change jetOn (degreeSample (fun u => f (u-Real.log d)) r) S=jetOn v S'
  rw [jetOn_congr (fun j (hj : j ∈ S) => align (hr.trans (mem_Ioc.mp hj).1))]
  exact (jetOn_restrict v ht (fun _ hj => outside (hr.trans (mem_Ioc.mp hj).1))).trans
    (jetOn_restrict v ht' (fun _ hj => outside (hR.trans (mem_Ioc.mp hj).1))).symm

/-- The fixed-packet archimedean limit remains valid when both the integer
translate and the horizon move, as soon as the effective resolution tends to infinity. -/
theorem tendsto_degreeForm_moving_integer_dilate {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {K : ℕ} (hK : 0 < K)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u=0) (d r L : ℕ → ℕ)
    (h : ∀ᶠ n : ℕ in atTop, 0 < d n ∧ 0 < r n ∧ K*d n ≤ 1+L n)
    (hres : Tendsto (fun n => d n*r n) atTop atTop) :
    Tendsto (fun n => degreeForm (fun u => f (u-Real.log (d n))) (L n) (r n)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)-
        (_root_.RHTower.weilPoleTerm (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  apply ((tendsto_degreeForm hf hfc hK hs).comp hres).congr'
  filter_upwards [h] with n hn
  exact (degreeForm_log_dilate (fun u hu => hs u (hu.imp (fun h₀ => h₀.trans (Real.log_nonneg (by norm_num))) id))
    hK hn.1 hn.2.1 hn.2.2).symm

#print axioms degreeForm_log_dilate
#print axioms tendsto_degreeForm_moving_integer_dilate

end GaloisForLFunctions.CountingHolography.Sections
