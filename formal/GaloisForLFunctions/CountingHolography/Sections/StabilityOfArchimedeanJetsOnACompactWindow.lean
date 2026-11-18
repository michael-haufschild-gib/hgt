import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.ThePacketsOnTheDegreePointsCarryWeilsArchimedeanForm

/-!
# Uniform stability of the degree-point jets on a compact window

On bounded Lipschitz families, changing the packet uniformly in the
interior changes its regularized jet by a uniform amount at every
resolution. The singular jump density is compensated by one Lipschitz
increment. The two tails are bounded where the packets differ.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open AbsoluteGeometryOfSpecZ Filter Finset Topology Zeta23

private theorem weighted_window_bound {L r : ℕ} (hr : 0 < r) (f : ℕ → ℝ) {B : ℝ}
    (hf : ∀ j ∈ Ioc r (r+L*r), |f j| ≤ B) :
    |∑ j ∈ Ioc r (r+L*r), f j/j| ≤ (L:ℝ)*B := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ _j ∈ Ioc r (r+L*r), B/(r:ℝ) := by
            refine sum_le_sum fun j hj => ?_
            have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
            rw [abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)]
            exact div_le_div₀ ((abs_nonneg _).trans (hf j hj)) (hf j hj) hr'
              (by exact_mod_cast (mem_Ioc.mp hj).1.le)
    _ = _ := by
      simp only [sum_const,Nat.card_Ioc,Nat.add_sub_cancel_left,nsmul_eq_mul,Nat.cast_mul]
      field_simp [(Nat.cast_pos.mpr hr : 0 < (r:ℝ)).ne']

private theorem weighted_double_window_bound {L r : ℕ} (hr : 0 < r) (f : ℕ → ℕ → ℝ) {B : ℝ}
    (hf : ∀ i ∈ Ioc r (r+L*r), ∀ j ∈ Ioc r (r+L*r), |f i j| ≤ B) :
    |∑ i ∈ Ioc r (r+L*r), ∑ j ∈ Ioc r (r+L*r), f i j/((i:ℝ)*j)| ≤ (L:ℝ)*(L*B) := by
  have hre (i j : ℕ) : f i j/((i:ℝ)*j)=(f i j/j)/i := by ring
  simp_rw [hre,← sum_div]
  exact weighted_window_bound hr _ (fun i hi => weighted_window_bound hr _ (hf i hi))

private def jetRowPart (M r j : ℕ) := levyRow j-Real.log ((j:ℝ)/(2*Real.pi))-lowTail r j-highTail M j

/-- In the common interior the two removed tails are uniformly separated
from the singularity, even as the mesh is refined. -/
private theorem bounded_interior_rows : ∃ B : ℝ, 0 ≤ B ∧ ∀ {M r j : ℕ},
    0 < r → 3*r ≤ j → 3*j ≤ M → |jetRowPart M r j| ≤ B := by
  let Ω := _root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv
  obtain ⟨D,hD⟩ := tendsto_levyRow_sub_log.abs.bddAbove_range
  have h₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hΩ : 0 ≤ Ω (Real.log 3) := (_root_.RHTower.WeilLevyPoleGauss.archLevyAntideriv_pos h₃).le
  refine ⟨|D|+3*Ω (Real.log 3),by positivity,fun {M r j} hr hlow hhigh => ?_⟩
  have hj : 0 < j := by omega
  have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hlow' : (3:ℝ)*r ≤ j := by exact_mod_cast hlow
  have hhigh' : (3:ℝ)*j ≤ M := by exact_mod_cast hhigh
  have hlog₁ := Real.log_le_log (by norm_num : (0:ℝ)<3) ((le_div_iff₀ hr').mpr hlow')
  have hlog₂ := Real.log_le_log (by norm_num : (0:ℝ)<3) ((le_div_iff₀ hj').mpr hhigh')
  have hlog₃ : Real.log 3 ≤ Real.log j := Real.log_le_log (by norm_num) (by exact_mod_cast (show 3 ≤ j by omega))
  have hL := (lowTail_bounds hr hlow).2
  have hR := highTail_le (n := j) (M := M) hj (by omega)
  change highTail M j ≤ Ω (Real.log (((M+0:ℕ):ℝ)/j)) at hR
  rw [Nat.add_zero] at hR
  have hw : |levyRow j-Real.log ((j:ℝ)/(2*Real.pi))| ≤ |D| := (hD ⟨j,rfl⟩).trans (le_abs_self D)
  have hl₀ : 0 ≤ lowTail r j := sum_nonneg fun k _ => levyWeight_nonneg k j
  have hr₀ : 0 ≤ highTail M j := tsum_nonneg fun _ => levyWeight_nonneg _ _
  unfold jetRowPart
  rw [abs_le] at hw ⊢
  constructor <;> linarith only [hw.1,hw.2,hL,hR,hl₀,hr₀,hΩ,
    archLevyAntideriv_anti h₃ hlog₁,archLevyAntideriv_anti h₃ hlog₂,archLevyAntideriv_anti h₃ hlog₃]

private theorem jet_as_weighted_rows (f : ℝ → ℝ) (L : ℕ) {r : ℕ} (hr : 0 < r) :
    degreeForm f L r =
      (∑ j ∈ Ioc r (r+L*r), (degreeSample f r j^2*jetRowPart (r+L*r) r j)/j)-
      (∑ i ∈ Ioc r (r+L*r), ∑ j ∈ Ioc r (r+L*r),
        boxKernel f (Real.log ((i:ℝ)/r)) (Real.log ((j:ℝ)/r))/((i:ℝ)*j))/2 := by
  rw [degreeForm_eq f L hr,← sum_sub_distrib,← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  unfold jetRowPart
  ring

private theorem box_perturbation {f g : ℝ → ℝ} {A e T : ℝ}
    (he : 0 ≤ e) (hA : 0 ≤ A)
    (hf : ∀ u v, |f u-f v| ≤ A*|u-v|) (hg : ∀ u v, |g u-g v| ≤ A*|u-v|)
    (hd : ∀ u, |f u-g u| ≤ e) {u v : ℝ} (ht : |u-v| ≤ T) :
    |boxKernel f u v-boxKernel g u v| ≤ 2*A*e*Real.exp (T/2) := by
  let t := |u-v|
  rcases (abs_nonneg (u-v)).eq_or_lt with h | h
  · have huv := sub_eq_zero.mp (abs_eq_zero.mp h.symm)
    subst v
    rw [boxKernel_self,boxKernel_self,sub_self,abs_zero]
    positivity
  let w := _root_.RHTower.archLevyDensity t
  have hw : 0 ≤ w := (_root_.RHTower.archLevyDensity_pos h).le
  have h₁ : |(f u-f v)-(g u-g v)| ≤ 2*e := by
    rw [show (f u-f v)-(g u-g v)=(f u-g u)-(f v-g v) by ring]
    exact (abs_sub _ _).trans (by linarith only [hd u,hd v])
  have h₂ : |(f u-f v)+(g u-g v)| ≤ 2*A*t :=
    (abs_add_le _ _).trans (by dsimp only [t]; linarith only [hf u v,hg u v])
  have hs := mul_le_mul h₁ h₂ (abs_nonneg _) (mul_nonneg (by norm_num) he)
  have hh := mul_le_mul_of_nonneg_left hs hw
  have ht' : t*w ≤ Real.exp (T/2)/2 := (mul_archLevyDensity_le h).trans
    (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [ht])) (by norm_num))
  change |w*(f u-f v)^2-w*(g u-g v)^2| ≤ _
  rw [← mul_sub,sq_sub_sq,abs_mul,abs_of_nonneg hw,abs_mul]
  linarith only [hh,mul_le_mul_of_nonneg_left ht' (show 0 ≤ 4*A*e by positivity)]

/-- The original jets on a fixed window are uniformly stable in the
supremum distance on bounded Lipschitz packets agreeing at both ends. -/
theorem degreeForm_stable_on_compact_window (K : ℕ) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℝ → ℝ) {A e : ℝ}, 0 ≤ A → 0 ≤ e →
    (∀ u, |f u| ≤ A ∧ |g u| ≤ A ∧ |f u-g u| ≤ e) →
    (∀ u v, |f u-f v| ≤ A*|u-v| ∧ |g u-g v| ≤ A*|u-v|) →
    (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u=g u) →
    ∀ {r : ℕ}, 0 < r → |degreeForm f (3*K) r-degreeForm g (3*K) r| ≤ C*A*e := by
  obtain ⟨B,hB,hrow⟩ := bounded_interior_rows
  let L := 3*K
  let T := Real.log (1+(L:ℝ))
  refine ⟨2*L*B+(L:ℝ)^2*Real.exp (T/2),by positivity,fun f g {A e} hA he hval hlip hs {r} hr => ?_⟩
  let M := r+L*r
  let S := Ioc r M
  let u := fun j : ℕ => Real.log ((j:ℝ)/r)
  let W := fun j => jetRowPart M r j
  let X := fun j => (f (u j)^2-g (u j)^2)*W j
  let Y := fun i j => boxKernel f (u i) (u j)-boxKernel g (u i) (u j)
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hM : (M:ℝ)=(1+(L:ℝ))*r := by dsimp only [M]; push_cast; ring
  have hu {j : ℕ} (hj : j ∈ S) : 0 ≤ u j ∧ u j ≤ T := by
    have hlo : (r:ℝ) ≤ j := by exact_mod_cast (mem_Ioc.mp hj).1.le
    have hhi : (j:ℝ) ≤ M := by exact_mod_cast (mem_Ioc.mp hj).2
    rw [hM] at hhi
    exact ⟨Real.log_nonneg ((one_le_div hr').mpr hlo),Real.log_le_log (div_pos (hr'.trans_le hlo) hr')
      ((div_le_iff₀ hr').mpr hhi)⟩
  have hx {j : ℕ} (hj : j ∈ S) : |X j| ≤ (2*A*e)*B := by
    by_cases hz : f (u j)=g (u j)
    · simp only [X,hz,sub_self,zero_mul,abs_zero]; positivity
    have h₁ : Real.log 3 < u j := lt_of_not_ge (fun h => hz (hs _ (Or.inl h)))
    have h₂ : u j < Real.log K := lt_of_not_ge (fun h => hz (hs _ (Or.inr h)))
    have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr (hr.trans (mem_Ioc.mp hj).1)
    have hlo := (lt_div_iff₀ hr').mp ((Real.log_lt_log_iff (by norm_num) (div_pos hj' hr')).mp h₁)
    have hhi := (div_lt_iff₀ hr').mp ((Real.log_lt_log_iff (div_pos hj' hr') (Nat.cast_pos.mpr hK)).mp h₂)
    have hbound : 3*j ≤ M := by
      have hjK : j ≤ K*r := by exact_mod_cast hhi.le
      have h := Nat.mul_le_mul_left 3 hjK
      dsimp only [M,L]
      rw [← Nat.mul_assoc] at h
      omega
    have hw := hrow hr (by exact_mod_cast hlo.le) hbound
    have hv : |f (u j)+g (u j)| ≤ 2*A :=
      (abs_add_le _ _).trans (by linarith only [(hval (u j)).1,(hval (u j)).2.1])
    have hd := (hval (u j)).2.2
    have hsq : |f (u j)^2-g (u j)^2| ≤ 2*A*e := by
      rw [sq_sub_sq,abs_mul]
      exact mul_le_mul hv hd (abs_nonneg _) (by positivity)
    exact (abs_mul _ _).le.trans (mul_le_mul hsq hw (abs_nonneg _) (by positivity))
  have hy {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) : |Y i j| ≤ 2*A*e*Real.exp (T/2) :=
    box_perturbation he hA (fun u v => (hlip u v).1) (fun u v => (hlip u v).2)
      (fun u => (hval u).2.2) (abs_le.mpr ⟨by linarith only [(hu hi).1,(hu hj).2],
        by linarith only [(hu hi).2,(hu hj).1]⟩)
  have hX := weighted_window_bound (L := L) hr X (fun _ hj => hx hj)
  have hY := weighted_double_window_bound (L := L) hr Y (fun _ hi _ hj => hy hi hj)
  have hid : degreeForm f L r-degreeForm g L r =
      (∑ j ∈ S, X j/j)-(∑ i ∈ S, ∑ j ∈ S, Y i j/((i:ℝ)*j))/2 := by
    simp only [X,Y,W,u,S,M,sub_mul,sub_div,sum_sub_distrib,jet_as_weighted_rows _ _ hr,degreeSample]
    ring
  change |degreeForm f L r-degreeForm g L r| ≤ _
  rw [hid,abs_le]
  rw [abs_le] at hX hY
  constructor <;> linarith only [hX.1,hX.2,hY.1,hY.2]

/-- Uniform convergence on a bounded Lipschitz family preserves the continuous
archimedean value even when the packet and the resolution vary together. -/
theorem tendsto_degreeForm_varying_compact_packets {K : ℕ} (hK : 0 < K) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hs : ∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → f u=0)
    (g : ℕ → ℝ → ℝ) (r : ℕ → ℕ) (hr : Tendsto r atTop atTop) {A : ℝ} (hA : 0 ≤ A)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (h : ∀ᶠ n : ℕ in atTop, 0 ≤ e n ∧
      (∀ u, |g n u| ≤ A ∧ |f u| ≤ A ∧ |g n u-f u| ≤ e n) ∧
      (∀ u v, |g n u-g n v| ≤ A*|u-v| ∧ |f u-f v| ≤ A*|u-v|) ∧
      (∀ u, u ≤ Real.log 3 ∨ Real.log K ≤ u → g n u=f u)) :
    Tendsto (fun n => degreeForm (g n) (3*K) (r n)) atTop
      (𝓝 (-(_root_.RHTower.WeilOneSided.weilArchRe
        (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)-
        (_root_.RHTower.weilPoleTerm (EF.weilTest (packetTest f hf hfc).1 (packetTest f hf hfc).1)).re))) := by
  obtain ⟨C,_,hC⟩ := degreeForm_stable_on_compact_window K hK
  have hd : Tendsto (fun n => degreeForm (g n) (3*K) (r n)-degreeForm f (3*K) (r n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun n => C*A*e n) _ (by simpa only [mul_zero] using he.const_mul (C*A))
    filter_upwards [h,hr.eventually_ge_atTop 1] with n hn hn'
    rw [Real.norm_eq_abs]
    exact hC _ _ hA hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 hn'
  simpa only [sub_add_cancel,zero_add,Function.comp_apply] using
    hd.add ((tendsto_degreeForm hf hfc hK hs).comp hr)

#print axioms tendsto_degreeForm_varying_compact_packets
#print axioms degreeForm_stable_on_compact_window

end GaloisForLFunctions.CountingHolography.Sections
