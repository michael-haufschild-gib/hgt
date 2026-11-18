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

/-- For two degree indices separated by a factor of at least H², the
absolute jet kernel is at most 2/H times their product harmonic weight. -/
private theorem far_jet {m n : ℕ} (hm : 0 < m) {H : ℝ} (hH : 2 ≤ H)
    (hsep : H^2*m ≤ n) : |levyKernel m n| ≤ (2/H)/((m:ℝ)*n) := by
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have hH' : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have h₂ : 2*(m:ℝ) ≤ n := by
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hH 2
    linarith only [hsep,mul_le_mul_of_nonneg_right hsq hm'.le,hm']
  have hn : 0 < (n:ℝ) := by linarith only [h₂,hm']
  have hdiff : 0 < (n:ℝ)-m := by linarith only [h₂,hm']
  have hj : jetKernel m n ≤ 2/n := by
    unfold jetKernel
    rw [abs_of_nonpos (by linarith only [hdiff] : (m:ℝ)-n ≤ 0),neg_sub]
    have h₁ : 1/((n:ℝ)-m) ≤ 2/n := (div_le_div_iff₀ hdiff hn).mpr (by linarith only [h₂])
    have h₂' : 1/((m:ℝ)+n) ≤ 2/n := (div_le_div_iff₀ (add_pos hm' hn) hn).mpr (by linarith only [hm',hn])
    linarith only [h₁,h₂']
  have hs : H*(m:ℝ) ≤ Real.sqrt ((m:ℝ)*n) := by
    apply (Real.le_sqrt (mul_nonneg hH'.le hm'.le) (mul_nonneg hm'.le hn.le)).mpr
    linarith only [mul_le_mul_of_nonneg_left hsep hm'.le]
  have hk : 0 ≤ levyKernel m n := by unfold levyKernel jetKernel; positivity
  rw [abs_of_nonneg hk,levyKernel]
  calc jetKernel m n/Real.sqrt ((m:ℝ)*n) ≤ (2/(n:ℝ))/(H*m) :=
          div_le_div₀ (by positivity) hj (mul_pos hH' hm') hs
    _ = _ := by ring

/-- For two packets with separated sampled supports, their mixed regularized
jet is bounded by their harmonic sample masses times the inverse square
root of the separation factor. This estimate is independent of resolution. -/
theorem degreeForm_separated_mixed_bound (f g : ℝ → ℝ) {L r : ℕ} (hr : 0 < r)
    {H : ℝ} (hH : 2 ≤ H)
    (hsep : ∀ i ∈ Ioc r (r+L*r), ∀ j ∈ Ioc r (r+L*r),
      degreeSample f r i ≠ 0 → degreeSample g r j ≠ 0 → H^2*i ≤ j) :
    |degreeForm (fun u => f u+g u) L r-degreeForm f L r-degreeForm g L r| ≤
      (4/H)*(∑ i ∈ Ioc r (r+L*r), |degreeSample f r i| / i)*
        (∑ j ∈ Ioc r (r+L*r), |degreeSample g r j| / j) := by
  let S := Ioc r (r+L*r)
  let v := degreeSample f r
  let w := degreeSample g r
  let a := fun i : ℕ => |v i| / i
  let b := fun i : ℕ => |w i| / i
  have hH' : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hpos {i : ℕ} (hi : i ∈ S) : 0 < i := hr.trans (mem_Ioc.mp hi).1
  have overlap {i : ℕ} (hi : i ∈ S) : v i*w i=0 := by
    by_contra h
    obtain ⟨hv,hw⟩ := mul_ne_zero_iff.mp h
    have hs := hsep i hi i hi hv hw
    have hm : 0 < (i:ℝ) := Nat.cast_pos.mpr (hpos hi)
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hH 2
    linarith only [hs,mul_le_mul_of_nonneg_right hh hm.le,hm]
  have entry {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
      |v i*w j*levyKernel i j| ≤ (2/H)*(a i*b j) := by
    by_cases hv : v i=0
    · simp [a,hv]
    by_cases hw : w j=0
    · simp [b,hw]
    rw [abs_mul,abs_mul]
    exact (mul_le_mul_of_nonneg_left (far_jet (hpos hi) hH (hsep i hi j hj hv hw))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq (by dsimp only [a,b]; ring)
  let A := fun (s t : ℕ → ℝ) => ∑ n ∈ S, ∑ m ∈ S.erase n, s m*t n*levyKernel m n
  let C := fun (s : ℕ → ℝ) => ∑ n ∈ S, s n^2/n*Real.log ((n:ℝ)/(2*Real.pi))
  have hcounter : C (fun i => v i+w i)=C v+C w := by
    dsimp only [C]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    rw [add_sq,show 2*v i*w i=0 by rw [mul_assoc,overlap hi,mul_zero],add_zero,add_div,add_mul]
  have hexp : A (fun i => v i+w i) (fun i => v i+w i)=A v v+A v w+(A w v+A w w) := by
    simp only [A,add_mul,mul_add,sum_add_distrib]
    abel
  have hdiff : degreeForm (fun u => f u+g u) L r-degreeForm f L r-degreeForm g L r=A v w+A w v := by
    change (A (fun i => v i+w i) (fun i => v i+w i)-C (fun i => v i+w i))-(A v v-C v)-(A w w-C w)=_
    rw [hexp,hcounter]
    ring
  have mass (s t a' b' : ℕ → ℝ)
      (hb : ∀ i ∈ S, ∀ j ∈ S, |s i*t j*levyKernel i j| ≤ (2/H)*(a' i*b' j))
      (ha : ∀ i, 0 ≤ a' i) (hb' : ∀ i, 0 ≤ b' i) :
      |A s t| ≤ (2/H)*(∑ i ∈ S, a' i)*(∑ j ∈ S, b' j) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j ∈ S, ∑ i ∈ S, (2/H)*(a' i*b' j) := by
              refine sum_le_sum fun j hj => (abs_sum_le_sum_abs _ _).trans ?_
              exact (sum_le_sum fun i hi => hb i (mem_of_mem_erase hi) j hj).trans
                (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun i _ _ => mul_nonneg
                  (div_nonneg (by norm_num) hH'.le) (mul_nonneg (ha i) (hb' j))))
      _ = _ := by simp only [← mul_assoc,← sum_mul,← mul_sum]
  have ha (i) : 0 ≤ a i := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hb (i) : 0 ≤ b i := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  have hvw := mass v w a b (fun _ hi _ hj => entry hi hj) ha hb
  have hwv := mass w v b a (fun i hi j hj => by
    rw [mul_comm (w i),levyKernel_comm i j,mul_comm (b i)]
    exact entry hj hi) hb ha
  rw [hdiff]
  change |A v w+A w v| ≤ (4/H)*(∑ i ∈ S, a i)*(∑ i ∈ S, b i)
  exact (abs_add_le _ _).trans ((add_le_add hvw hwv).trans_eq (by ring))

#print axioms degreeForm_separated_mixed_bound
#print axioms degreeForm_log_dilate
#print axioms tendsto_degreeForm_moving_integer_dilate

end GaloisForLFunctions.CountingHolography.Sections
