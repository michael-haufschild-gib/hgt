import GaloisForLFunctions.HTGeometry.DispersivePDE.TheGeometricThresholdForWeightedCriticalModes

/-!
# Rigidity at the weighted geometric threshold

For a positive synchronized state, the logarithmic distance of the
coupling from threshold is the weighted sum of the logarithmic excesses
of the individual self-interactions over the common product. Thus every
coordinate approaches the same normalized self-interaction. At zero mass
that limiting ray is the entire family of positive critical states.
-/

noncomputable section
open Finset Filter Topology
namespace HTGeometry.WeightedCriticalModes
variable {ι : Type*} [Fintype ι]

/-- At zero mass the only positive states have exactly critical
coupling and a common self-interaction at every coordinate. -/
theorem massless_states {w μ x : ι → ℝ} {r b : ℝ} (mass : ∑ i,w i=1)
    (hμ : ∀ i, 0<μ i) (hb : 0<b) :
    Synchronized w μ (fun _ => 0) r b x ↔
      b=geometricMean w μ ∧ ∃ c : ℝ, 0<c ∧ ∀ i, x i=c/μ i := by
  constructor
  · intro sol
    have pos : 0<geometricMean w x := Real.exp_pos _
    have site (i : ι) : μ i*x i=b*geometricMean w x := by simpa only [zero_mul,zero_add] using sol.2 i
    have eq := congrArg (geometricMean w) (funext site)
    rw [geometricMean_mul w hμ sol.1,geometricMean_const mass (mul_pos hb pos)] at eq
    exact ⟨(mul_right_cancel₀ pos.ne' eq).symm,b*geometricMean w x,mul_pos hb pos,
      fun i => (eq_div_iff (hμ i).ne').mpr ((mul_comm ..).trans (site i))⟩
  · rintro ⟨crit,c,hc,shape⟩
    have xp (i : ι) : 0<x i := (shape i).symm ▸ div_pos hc (hμ i)
    have site (i : ι) : μ i*x i=c := by rw [shape]; field_simp [(hμ i).ne']
    have eq := congrArg (geometricMean w) (funext site)
    rw [geometricMean_mul w hμ xp,geometricMean_const mass hc] at eq
    refine ⟨xp,fun i => ?_⟩
    rw [zero_mul,zero_add,crit,eq,site]

private def siteRatio (w μ x : ι → ℝ) (b : ℝ) (i : ι) : ℝ := μ i*x i/(b*geometricMean w x)

private theorem ratio_gt_one {w μ m x : ι → ℝ} {r b : ℝ} (hm : ∀ i, 0 < m i)
    (hb : 0<b) (sol : Synchronized w μ m r b x) (i : ι) : 1<siteRatio w μ x b i := by
  apply (one_lt_div (mul_pos hb (Real.exp_pos _))).mpr
  rw [sol.2 i]
  exact lt_add_of_pos_left _ (mul_pos (hm i) (Real.rpow_pos_of_pos (sol.1 i) r))

/-- Exact logarithmic distance to critical coupling, decomposed across
the individual mode excesses. -/
theorem logarithmic_mode_excess {w μ m x : ι → ℝ} {r b : ℝ} (mass : ∑ i,w i=1)
    (hμ : ∀ i, 0<μ i) (hb : 0<b) (sol : Synchronized w μ m r b x) :
    ∑ i,w i*Real.log (μ i*x i/(b*geometricMean w x))=Real.log (geometricMean w μ/b) := by
  have gx : 0<geometricMean w x := Real.exp_pos _
  have gu : 0<geometricMean w μ := Real.exp_pos _
  simp only [fun i => Real.log_div (mul_pos (hμ i) (sol.1 i)).ne' (mul_pos hb gx).ne',
    fun i => Real.log_mul (hμ i).ne' (sol.1 i).ne',mul_sub,mul_add]
  rw [sum_sub_distrib,sum_add_distrib,←sum_mul,mass,one_mul,Real.log_mul hb.ne' gx.ne',
    Real.log_div gu.ne' hb.ne']
  simp only [geometricMean,Real.log_exp]
  ring

/-- Each normalized self-interaction is squeezed between one and
the total coupling ratio raised to the reciprocal of its own weight. -/
theorem individual_mode_excess_bound {w μ m x : ι → ℝ} {r b : ℝ}
    (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1) (hμ : ∀ i, 0<μ i) (hm : ∀ i, 0 < m i)
    (hb : 0<b) (sol : Synchronized w μ m r b x) (i : ι) :
    1<μ i*x i/(b*geometricMean w x) ∧
      μ i*x i/(b*geometricMean w x)≤(geometricMean w μ/b)^(1/w i) := by
  have all := ratio_gt_one hm hb sol
  have pos : 0<siteRatio w μ x b i := zero_lt_one.trans (all i)
  have cap := single_le_sum (s:=univ) (f:=fun j => w j*Real.log (siteRatio w μ x b j))
    (fun j _ => mul_nonneg (hw j).le (Real.log_nonneg (all j).le)) (mem_univ i)
  rw [show (∑ j,w j*Real.log (siteRatio w μ x b j))=Real.log (geometricMean w μ/b) from
    logarithmic_mode_excess mass hμ hb sol] at cap
  have bound := (le_div_iff₀ (hw i)).mpr ((mul_comm ..).le.trans cap)
  have gp : 0<geometricMean w μ/b := div_pos (Real.exp_pos _) hb
  refine ⟨all i,?_⟩
  change siteRatio w μ x b i≤_
  rw [←Real.exp_log pos,Real.rpow_def_of_pos gp]
  apply Real.exp_le_exp.mpr
  simpa only [div_eq_mul_inv,one_mul] using bound

-- Multiplying a site's excess by the pressure power cancels the
-- unknown scale of the state. The two log bounds then have a common
-- limit at critical coupling.
private theorem scaled_site_log {w μ m x : ι → ℝ} {r b : ℝ}
    (hμ : ∀ i, 0<μ i) (hb : 0<b) (sol : Synchronized w μ m r b x) (i : ι) :
    let P := b*geometricMean w x
    let z := siteRatio w μ x b i
    let a := m i/(μ i)^r
    a*z^r/z ≤ P^(1-r)*Real.log z ∧ P^(1-r)*Real.log z ≤ a*z^r := by
  intro P z a
  have pp : 0<P := mul_pos hb (Real.exp_pos _)
  have zp : 0<z := div_pos (mul_pos (hμ i) (sol.1 i)) pp
  have inc : z-1=m i*(x i)^r/P := by
    change μ i*x i/P-1=_
    rw [sol.2 i]
    change (m i*(x i)^r+P)/P-1=_
    rw [add_div,div_self pp.ne',add_sub_cancel_right]
  have eq : P^(1-r)*(z-1)=a*z^r := by
    rw [inc,Real.rpow_sub pp,Real.rpow_one]
    change _=(m i/(μ i)^r)*(μ i*x i/P)^r
    rw [Real.div_rpow (mul_pos (hμ i) (sol.1 i)).le pp.le,Real.mul_rpow (hμ i).le (sol.1 i).le]
    field_simp [pp.ne',(Real.rpow_pos_of_pos pp r).ne',(Real.rpow_pos_of_pos (hμ i) r).ne']
  have low := Real.log_le_sub_one_of_pos (inv_pos.mpr zp)
  rw [Real.log_inv] at low
  have ps := (Real.rpow_pos_of_pos pp (1-r)).le
  constructor
  · rw [←eq,mul_div_assoc,sub_div,div_self zp.ne',one_div]
    exact mul_le_mul_of_nonneg_left (by linarith only [low]) ps
  · rw [←eq]
    exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos zp) ps

/-- The pressure P = b G(x) has a pole in P^(1−r). Its residue in
the logarithmic distance to threshold is the weighted sum of the
rescaled masses mᵢ/μᵢʳ. The positive state exists at every parameter
of the approaching family. -/
theorem critical_pressure_residue [Nonempty ι] {α : Type*} {F : Filter α}
    {w μ m : ι → ℝ} {r : ℝ} (hw : ∀ i, 0<w i) (mass : ∑ i,w i=1)
    (hμ : ∀ i, 0<μ i) (hm : ∀ i, 0 < m i) (hr : r<1)
    (b : α → ℝ) (hb : ∀ j, 0<b j ∧ b j<geometricMean w μ)
    (critical : Tendsto b F (𝓝 (geometricMean w μ))) :
    ∃ x : α → ι → ℝ, (∀ j, Synchronized w μ m r (b j) (x j)) ∧
      Tendsto (fun j => (b j*geometricMean w (x j))^(1-r)*Real.log (geometricMean w μ/b j))
        F (𝓝 (∑ i,w i*(m i/(μ i)^r))) := by
  choose x sol using fun j => ((weighted_synchronization_iff hw mass hμ hm hr (hb j).1).mpr (hb j).2).exists
  refine ⟨x,sol,?_⟩
  let z (j : α) (i : ι) := siteRatio w μ (x j) (b j) i
  let a (i : ι) := m i/(μ i)^r
  let P (j : α) := b j*geometricMean w (x j)
  have gp : 0<geometricMean w μ := Real.exp_pos _
  have ratio : Tendsto (fun j => geometricMean w μ/b j) F (𝓝 1) := by
    have lim := (tendsto_const_nhds (x:=geometricMean w μ)).div critical gp.ne'
    change Tendsto (fun j => geometricMean w μ/b j) F (𝓝 (geometricMean w μ/geometricMean w μ)) at lim
    rwa [div_self gp.ne'] at lim
  have zz (i : ι) : Tendsto (fun j => z j i) F (𝓝 1) := by
    have cap : Tendsto (fun j => (geometricMean w μ/b j)^(1/w i)) F (𝓝 1) := by
      simpa only [Real.one_rpow] using ratio.rpow_const (p:=1/w i) (.inl one_ne_zero)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cap
    · exact fun j => (ratio_gt_one hm (hb j).1 (sol j) i).le
    · exact fun j => (individual_mode_excess_bound hw mass hμ hm (hb j).1 (sol j) i).2
  have power (i : ι) : Tendsto (fun j => z j i^r) F (𝓝 1) := by
    simpa only [Real.one_rpow] using (zz i).rpow_const (p:=r) (.inl one_ne_zero)
  have lower : Tendsto (fun j => ∑ i,w i*(a i*z j i^r/z j i)) F (𝓝 (∑ i,w i*a i)) := by
    apply tendsto_finsetSum
    intro i _
    have lim := (((power i).const_mul (a i)).div (zz i) one_ne_zero).const_mul (w i)
    change Tendsto (fun j => w i*(a i*z j i^r/z j i)) F (𝓝 (w i*(a i*1/1))) at lim
    simpa only [mul_one,div_one] using lim
  have upper : Tendsto (fun j => ∑ i,w i*(a i*z j i^r)) F (𝓝 (∑ i,w i*a i)) := by
    apply tendsto_finsetSum
    intro i _
    simpa only [mul_one] using (((power i).const_mul (a i)).const_mul (w i))
  have mid (j : α) : P j^(1-r)*Real.log (geometricMean w μ/b j)=
      ∑ i,w i*(P j^(1-r)*Real.log (z j i)) := by
    rw [←logarithmic_mode_excess mass hμ (hb j).1 (sol j),mul_sum]
    exact sum_congr rfl fun i _ => mul_left_comm ..
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lower upper
  · intro j
    change _≤P j^(1-r)*Real.log (geometricMean w μ/b j)
    rw [mid]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (scaled_site_log hμ (hb j).1 (sol j) i).1 (hw i).le
  · intro j
    change P j^(1-r)*Real.log (geometricMean w μ/b j)≤_
    rw [mid]
    exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (scaled_site_log hμ (hb j).1 (sol j) i).2 (hw i).le

#print axioms critical_pressure_residue
#print axioms massless_states
#print axioms individual_mode_excess_bound
#print axioms logarithmic_mode_excess
end HTGeometry.WeightedCriticalModes
