import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrescribedDelays.AngularData.Packing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.SparseReadings.Dilation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.MesoscopicDelay

/-! # A physical observation price localized to a set of Gaussian directions -/

open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows LocalPatches.RampWindows.SparseReadings
open private isolated_visit from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.RampWindows.SparseReadings.Dilation
open private coordinate_card from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.MesoscopicDelay
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Selecting an angular subset does not alter the comparison factor
for the radial dilations. The numerator and denominator both refer to
the same angular subset. -/
private theorem angular_grid {k s m : ℕ} (P : Option ℕ) (D : Set (PrefixIndex (k+1) → ℝ))
    (hD : MeasurableSet D) (hdir : ∀ x (u : ℝ), 0<u → u • x ∈ D → x ∈ D)
    {g T w l H : ℝ} (hg : 0≤g) (hT : 0<T) (hspan : (m:ℝ)*g ≤ T)
    (hprice : (Fintype.card (PrefixIndex (k+1)):ℝ)*((m:ℝ)*g) ≤ T)
    (hw : 0≤w) (hl : l ≤ g/2-2*w) (hh : (m:ℝ)*g+2*w ≤ H) :
    let X := prefixPoint k
    (m:ℝ)*pathPauliDisorderLaw.real (X ⁻¹' ((visit (k+1) s P T w \ cheapLag (k+1) s l H) ∩ D)) ≤
      exp 1*pathPauliDisorderLaw.real (X ⁻¹' D) := by
  intro X
  let E := visit (k+1) s P T w
  let a := factor (m:=m) g T
  have hE : MeasurableSet E := measurable_visit ..
  have ha (i : Fin m) : 1≤a i := (factor_bounds hg hT hspan i).1
  have hp (i : Fin m) : (Fintype.card (PrefixIndex (k+1)):ℝ)*(a i-1) ≤ 1 := by
    change _*(1+(i.val:ℝ)*g/T-1) ≤ 1
    rw [add_sub_cancel_left,←mul_div_assoc,div_le_one hT]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (by exact_mod_cast i.isLt.le : (i.val:ℝ) ≤ m) hg) (Nat.cast_nonneg _)).trans hprice
  have hsub : X ⁻¹' ((E \ cheapLag (k+1) s l H) ∩ D) ⊆ X ⁻¹' (isolated a E ∩ D) := by
    rintro ω ⟨⟨hfit,hgood⟩,hd⟩
    exact ⟨isolated_visit P ω hg hT hspan hw hl hh hfit hgood,hd⟩
  apply (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Nat.cast_nonneg m)).trans
  have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
  change _*pathPauliDisorderLaw.real (prefixPoint k ⁻¹' _) ≤ _*pathPauliDisorderLaw.real (prefixPoint k ⁻¹' _)
  rw [hmp.measureReal_preimage ((measurable_isolated a hE).inter hD).nullMeasurableSet,
    hmp.measureReal_preimage hD.nullMeasurableSet]
  exact angular_isolated_mass a E D hE hD hdir ha hp

/-- Beyond cubic time the price per unit angular mass depends only on
the width and the forbidden lag horizon. It is uniform over the delay,
including when the candidate circuit varies throughout the window. -/
theorem angular_late_window (A δ : ℝ) (hA : 0<A) (hδ : 0<δ) :
    ∃ C>0, ∀ (k s : ℕ) (P : Option ℕ) (D : Set (PrefixIndex (k+1) → ℝ)), MeasurableSet D →
      (∀ x (u : ℝ), 0<u → u • x ∈ D → x ∈ D) →
      let K : ℝ := (k+3:ℕ)
      let Q := K^(65/64:ℝ)
      ∀ T ≥ K^3, ∀ w ≥ (0:ℝ), pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
        ((visit (k+1) s P T w \ cheapLag (k+1) s (A/K) (δ*Q)) ∩ D)) ≤
          (C*(1+w)/Q)*pathPauliDisorderLaw.real (prefixPoint k ⁻¹' D) := by
  let b := min (1/16:ℝ) (δ/2)
  let q := 2*A+4
  have hb : 0<b := lt_min (by norm_num) (half_pos hδ)
  have hq : 0<q := by dsimp only [q]; linarith only [hA]
  refine ⟨2*exp 1*q/b,by positivity,?_⟩
  intro k s P D hD hdir K Q T hT w hw
  let g := q*(1+w)
  let M := pathPauliDisorderLaw.real (prefixPoint k ⁻¹' D)
  let Z := prefixPoint k ⁻¹' ((visit (k+1) s P T w \ cheapLag (k+1) s (A/K) (δ*Q)) ∩ D)
  have hg : 0<g := mul_pos hq (by linarith only [hw])
  have hK : 1≤K := by change (1:ℝ)≤((k+3:ℕ):ℝ); exact_mod_cast (show 1≤k+3 by omega)
  have hk := zero_lt_one.trans_le hK
  have hQ : 0<Q := rpow_pos_of_pos hk _
  have hQ₂ : Q≤K^2 := (rpow_le_rpow_of_exponent_le hK (by norm_num : (65/64:ℝ)≤(2:ℕ))).trans_eq (rpow_natCast K 2)
  have hbQ : 0<b*Q := mul_pos hb hQ
  have he := Real.one_le_exp (by norm_num : (0:ℝ)≤1)
  have hrewrite : (2*exp 1*q/b)*(1+w)/Q=2*exp 1*g/(b*Q) := by dsimp only [g]; ring
  rw [hrewrite]
  change pathPauliDisorderLaw.real Z ≤ (2*exp 1*g/(b*Q))*M
  by_cases hbig : 2≤b*Q/g
  · let m := ⌊b*Q/g⌋₊
    have hmf : (m:ℝ) ≤ b*Q/g := Nat.floor_le (div_nonneg hbQ.le hg.le)
    have hm : 0<(m:ℝ) := Nat.cast_pos.mpr (Nat.floor_pos.mpr (le_trans (by norm_num) hbig))
    have hmg := (le_div_iff₀ hg).mp hmf
    have hKQ : K*Q ≤ T := (mul_le_mul_of_nonneg_left hQ₂ hk.le).trans ((by ring : K*K^2=K^3).le.trans hT)
    have hcap : 16*((m:ℝ)*g) ≤ Q := by
      have hb₁ : b ≤ 1/16 := min_le_left ..
      linarith only [hmg,mul_le_mul_of_nonneg_right hb₁ hQ.le]
    have hcost : (Fintype.card (PrefixIndex (k+1)):ℝ)*((m:ℝ)*g) ≤ T := calc
      _ ≤ (16*K)*((m:ℝ)*g) := mul_le_mul_of_nonneg_right (coordinate_card k) (mul_nonneg hm.le hg.le)
      _ = K*(16*((m:ℝ)*g)) := by ring
      _ ≤ T := (mul_le_mul_of_nonneg_left hcap hk.le).trans hKQ
    have hspan : (m:ℝ)*g ≤ T := by
      have hmg₀ := mul_nonneg hm.le hg.le
      have hQK := le_mul_of_one_le_left hQ.le hK
      linarith only [hcap,hQK,hKQ,hmg₀]
    have hδQ := mul_le_mul_of_nonneg_right (min_le_right (1/16:ℝ) (δ/2)) hQ.le
    have hgw : 2*w≤g := by dsimp only [g,q]; nlinarith only [hA,hw,mul_nonneg hA.le hw]
    have hwin : (m:ℝ)*g+2*w ≤ δ*Q := by
      have htwo := (le_div_iff₀ hg).mp hbig
      change b*Q ≤ δ/2*Q at hδQ
      linarith only [hmg,hδQ,htwo,hgw,hg]
    have hlo : A/K ≤ g/2-2*w := by
      dsimp only [g,q]
      nlinarith only [div_le_self hA.le hK,hA,mul_nonneg hA.le hw]
    have hmass := angular_grid (m:=m) (s:=s) P D hD hdir hg.le ((pow_pos hk 3).trans_le hT)
      hspan hcost hw hlo hwin
    have hnext : b*Q/g < (m:ℝ)+1 := Nat.lt_floor_add_one _
    have hfloor₁ := (div_lt_iff₀ hg).mp hnext
    have hm₁ : 1≤(m:ℝ) := by
      have hn : 1 ≤ m := Nat.floor_pos.mpr (le_trans (by norm_num) hbig)
      exact_mod_cast hn
    have hhalf : b*Q ≤ 2*g*(m:ℝ) := by linarith only [hfloor₁,mul_le_mul_of_nonneg_right hm₁ hg.le]
    have hprice : exp 1/(m:ℝ) ≤ 2*exp 1*g/(b*Q) := (div_le_div_iff₀ hm hbQ).mpr (by
      calc
        _ ≤ exp 1*(2*g*(m:ℝ)) := mul_le_mul_of_nonneg_left hhalf (exp_pos _).le
        _ = _ := by ring)
    apply le_trans _ (mul_le_mul_of_nonneg_right hprice (show 0≤M from measureReal_nonneg))
    rw [div_mul_eq_mul_div,le_div_iff₀ hm,mul_comm _ (m:ℝ)]
    exact hmass
  · have hf : b*Q < 2*g := (div_lt_iff₀ hg).mp (lt_of_not_ge hbig)
    have h₁ : 1 ≤ 2*exp 1*g/(b*Q) := (le_div_iff₀ hbQ).mpr (by
      linarith only [hf,mul_le_mul_of_nonneg_right he hg.le])
    have hsub : Z ⊆ prefixPoint k ⁻¹' D := fun _ hx => hx.2
    exact (measureReal_mono hsub).trans (le_mul_of_one_le_left measureReal_nonneg h₁)

#print axioms angular_late_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
