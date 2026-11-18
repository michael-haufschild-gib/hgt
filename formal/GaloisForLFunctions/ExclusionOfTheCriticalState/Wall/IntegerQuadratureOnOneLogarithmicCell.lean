import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFirstAbsoluteMomentOfStateIncrements

/-!
# The unit-cell error for integer sampling of the confined profile

At integer n, comparison with the continuum only displaces the profile by at
most 1/n on the log axis. The little-o square-root translation modulus absorbs
the inverse-square-root weight at precisely the summatory logarithmic scale.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

/-- The critical weight at a positive real rather than at an integer. -/
def continuousIntegerAtom (Φ : ℝ → ℝ) (x t : ℝ) := (Real.sqrt x)⁻¹ * Φ (t-Real.log x)

/-- Error made by sampling one integer and integrating the same cell. -/
def integerCellDefect (Φ : ℝ → ℝ) (n : ℕ) (t : ℝ) :=
  ∫ x in Ioc (n:ℝ) (n+1), continuousIntegerAtom Φ n t - continuousIntegerAtom Φ x t

private theorem integerAtom_integrable {Φ : ℝ → ℝ} (hi : Integrable Φ) (x : ℝ) :
    Integrable (continuousIntegerAtom Φ x) := (hi.comp_sub_right (Real.log x)).const_mul _

private theorem integerAtom_norm_integral {Φ : ℝ → ℝ} (x : ℝ) :
    (∫ t : ℝ, ‖continuousIntegerAtom Φ x t‖) = (Real.sqrt x)⁻¹ * ∫ u, |Φ u| := by
  simp only [continuousIntegerAtom,norm_mul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [integral_const_mul,integral_sub_right_eq_self (fun u => |Φ u|)]

private theorem atomDiff_integrable_prod {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    {n : ℕ} (hn : 1 ≤ n) : Integrable (fun p : ℝ × ℝ => continuousIntegerAtom Φ n p.2 - continuousIntegerAtom Φ p.1 p.2)
      ((volume.restrict (Ioc (n:ℝ) (n+1))).prod volume) := by
  let f := fun x t : ℝ => continuousIntegerAtom Φ n t - continuousIntegerAtom Φ x t
  have hm : Measurable (Function.uncurry f) := by dsimp only [f,Function.uncurry,continuousIntegerAtom]; fun_prop
  refine (integrable_prod_iff hm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x =>
    (integerAtom_integrable hi _).sub (integerAtom_integrable hi _),?_⟩
  let A := ∫ u, |Φ u|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  refine (integrable_const (2*A)).mono' hm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hnx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hb {y : ℝ} (hy : 1 ≤ y) : (Real.sqrt y)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by simpa using Real.sqrt_le_sqrt hy)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  calc _ ≤ ∫ t : ℝ, ‖continuousIntegerAtom Φ n t‖ + ‖continuousIntegerAtom Φ x t‖ :=
           integral_mono ((integerAtom_integrable hi _).sub (integerAtom_integrable hi _)).norm
             ((integerAtom_integrable hi _).norm.add (integerAtom_integrable hi _).norm) (fun t => norm_sub_le ..)
    _ = (Real.sqrt n)⁻¹*A + (Real.sqrt x)⁻¹*A := by rw [integral_add (integerAtom_integrable hi _).norm (integerAtom_integrable hi _).norm,
             integerAtom_norm_integral,integerAtom_norm_integral]
    _ ≤ 2*A := by linarith only [mul_le_mul_of_nonneg_right (hb hnx) hA,mul_le_mul_of_nonneg_right (hb (hnx.trans hx.1.le)) hA]

/-- The integrated absolute error is bounded by integrating first over translations. -/
theorem integerCellDefect_L1_le {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (integerCellDefect Φ n) ∧ (∫ t, |integerCellDefect Φ n t|) ≤
      ∫ x in Ioc (n:ℝ) (n+1), ∫ t : ℝ, |continuousIntegerAtom Φ n t - continuousIntegerAtom Φ x t| := by
  have hp := atomDiff_integrable_prod hc hi hn
  refine ⟨hp.integral_prod_right,?_⟩
  rw [integral_integral_swap hp.norm]
  apply integral_mono hp.integral_prod_right.abs hp.norm.integral_prod_right
  exact fun t => abs_integral_le_integral_abs

private theorem inv_sqrt_cell {u x : ℝ} (hu : 0 < u) (hux : u ≤ x) (hx : x ≤ u+1) :
    (Real.sqrt u)⁻¹ - (Real.sqrt x)⁻¹ ≤ 1/(u*Real.sqrt u) := by
  have h1 := Real.sqrt_pos.2 hu
  have h2 := Real.sqrt_pos.2 (hu.trans_le hux)
  have h3 := Real.sqrt_le_sqrt hux
  have hprod : u ≤ Real.sqrt u*Real.sqrt x := by
    calc _ = Real.sqrt u*Real.sqrt u := (Real.mul_self_sqrt hu.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 h1.le
  have he : ((Real.sqrt u)⁻¹-(Real.sqrt x)⁻¹) * (u*Real.sqrt u) =
      (u/(Real.sqrt x*(Real.sqrt x+Real.sqrt u)))*(x-u) := by
    rw [show x-u = (Real.sqrt x-Real.sqrt u)*(Real.sqrt x+Real.sqrt u) by
      nlinarith only [Real.sq_sqrt hu.le,Real.sq_sqrt (hu.trans_le hux).le]]
    field_simp [h1.ne',h2.ne',(add_pos h2 h1).ne']
  rw [le_div_iff₀ (mul_pos hu h1),he]
  have hh : u/(Real.sqrt x*(Real.sqrt x+Real.sqrt u)) ≤ 1 := by
    rw [div_le_one (mul_pos h2 (add_pos h2 h1))]
    nlinarith only [Real.sq_sqrt (hu.trans_le hux).le,hprod,hux]
  simpa only [one_mul] using mul_le_mul hh (show x-u ≤ 1 by linarith only [hx]) (sub_nonneg.2 hux) zero_le_one

private theorem integrated_atom_diff {Φ : ℝ → ℝ} (hi : Integrable Φ) {u x : ℝ}
    (hu : 0 < u) (hux : u ≤ x) (hx : x ≤ u+1) :
    (∫ t, |continuousIntegerAtom Φ u t-continuousIntegerAtom Φ x t|) ≤
      (Real.sqrt u)⁻¹*(∫ t, |Φ t-Φ (t+(Real.log x-Real.log u))|) +
      (1/(u*Real.sqrt u))*(∫ t, |Φ t|) := by
  let h := Real.log x-Real.log u
  let a := (Real.sqrt u)⁻¹
  let b := (Real.sqrt x)⁻¹
  have ha : 0 ≤ a := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hab : 0 ≤ a-b := sub_nonneg.2 (inv_anti₀ (Real.sqrt_pos.2 hu) (Real.sqrt_le_sqrt hux))
  have hd : Integrable (fun s => |Φ s-Φ (s+h)|) := (hi.sub (hi.comp_add_right h)).abs
  have hf : Integrable (fun t => a*|Φ (t-Real.log x)-Φ (t-Real.log x+h)|) := (hd.comp_sub_right _).const_mul _
  have hg : Integrable (fun t => (a-b)*|Φ (t-Real.log x)|) := (hi.abs.comp_sub_right _).const_mul _
  calc _ ≤ ∫ t, a*|Φ (t-Real.log x)-Φ (t-Real.log x+h)| + (a-b)*|Φ (t-Real.log x)| := by
           apply integral_mono ((integerAtom_integrable hi _).sub (integerAtom_integrable hi _)).abs (hf.add hg)
           intro t
           have he : t-Real.log u = t-Real.log x+h := by dsimp only [h]; ring
           change |a*Φ (t-Real.log u)-b*Φ (t-Real.log x)| ≤ _
           rw [he,show a*Φ (t-Real.log x+h)-b*Φ (t-Real.log x) =
             a*(Φ (t-Real.log x+h)-Φ (t-Real.log x)) + (a-b)*Φ (t-Real.log x) by ring]
           exact (abs_add_le ..).trans_eq (by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hab,abs_sub_comm]; rfl)
    _ = a*(∫ t, |Φ t-Φ (t+h)|) + (a-b)*(∫ t, |Φ t|) := by
           rw [integral_add hf hg,integral_const_mul,integral_const_mul,
             integral_sub_right_eq_self (fun t => |Φ t-Φ (t+h)|),integral_sub_right_eq_self (fun t => |Φ t|)]
    _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right (inv_sqrt_cell hu hux hx) (integral_nonneg fun _ => abs_nonneg _)) _

/-- The absolute error of one integer cell, integrated over all translates,
is little-o of 1/n. -/
theorem tendsto_integerCellDefect_of_L1_modulus {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hm : Tendsto (fun h : ℝ => (∫ u, |Φ u-Φ (u+h)|)/Real.sqrt h) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun n : ℕ => (n:ℝ)*(∫ t, |integerCellDefect Φ n t|)) atTop (𝓝 0) := by
  let A := ∫ u, |Φ u|
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hninf : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hninf
  have hA0 : Tendsto (fun n : ℕ => A / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_const_nhds (x := A)).mul (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hninf))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε/2 := half_pos hε
  obtain ⟨r,hr,hs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hm.eventually_lt_const he)
  filter_upwards [eventually_ge_atTop (1:ℕ),hinv.eventually_lt_const hr,hA0.eventually_lt_const he] with n hn hnr hnA
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hsq := Real.sqrt_pos.2 hn'
  have H (x : ℝ) (hx : x ∈ Ioc (n:ℝ) (n+1)) : (∫ t, |continuousIntegerAtom Φ n t-continuousIntegerAtom Φ x t|) ≤
      (ε/2)/(n:ℝ) + 1/((n:ℝ)*Real.sqrt n)*A := by
    let h := Real.log x-Real.log n
    have hp : 0 < h := sub_pos.2 (Real.log_lt_log hn' hx.1)
    have hu : h ≤ (n:ℝ)⁻¹ := by
      rw [show h = Real.log (x/(n:ℝ)) from (Real.log_div (hn'.trans hx.1).ne' hn'.ne').symm]
      apply (Real.log_le_sub_one_of_pos (div_pos (hn'.trans hx.1) hn')).trans
      rw [sub_le_iff_le_add,div_le_iff₀ hn']
      rw [add_mul,inv_mul_cancel₀ hn'.ne',one_mul,add_comm]; exact hx.2
    have hsmall := hs (show h ∈ Ioo 0 r from ⟨hp,hu.trans_lt hnr⟩)
    change (∫ s, |Φ s-Φ (s+h)|)/Real.sqrt h < ε/2 at hsmall
    have hroot : Real.sqrt h ≤ (Real.sqrt n)⁻¹ := by simpa only [Real.sqrt_inv] using Real.sqrt_le_sqrt hu
    have hm' : (∫ s, |Φ s-Φ (s+h)|) ≤ (ε/2)*(Real.sqrt n)⁻¹ :=
      ((div_lt_iff₀ (Real.sqrt_pos.2 hp)).1 hsmall).le.trans (mul_le_mul_of_nonneg_left hroot he.le)
    apply (integrated_atom_diff hi hn' hx.1.le hx.2).trans
    apply add_le_add_left
    calc _ ≤ (Real.sqrt n)⁻¹*((ε/2)*(Real.sqrt n)⁻¹) := mul_le_mul_of_nonneg_left hm' (inv_nonneg.2 hsq.le)
      _ = _ := by
        rw [show (Real.sqrt n)⁻¹*(ε/2*(Real.sqrt n)⁻¹) = (ε/2)/((Real.sqrt n)^2) by ring,Real.sq_sqrt hn'.le]
  have hp := atomDiff_integrable_prod hc hi hn
  have hv := (integerCellDefect_L1_le hc hi hn).2.trans (setIntegral_mono_on
    hp.norm.integral_prod_left (by simp) measurableSet_Ioc H)
  have heq (b : ℝ) : (∫ _x in Ioc (n:ℝ) (n+1), b) = b := by simp
  rw [heq] at hv
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hn'.le (integral_nonneg fun _ => abs_nonneg _))]
  calc _ ≤ (n:ℝ)*((ε/2)/n+1/((n:ℝ)*Real.sqrt n)*A) := mul_le_mul_of_nonneg_left hv hn'.le
    _ = ε/2 + A/Real.sqrt n := by field_simp [hn'.ne',hsq.ne']
    _ < _ := by linarith only [hnA]

/-- The continuous critical state satisfies the unit-cell estimate. -/
theorem criticalState_integerCellDefect {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ (∀ u, 0 ≤ u → Φ u = 0) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ u, |Φ u| ≤ C*Real.exp (2*u)) ∧
      Tendsto (fun n : ℕ => (n:ℝ)*(∫ t, |integerCellDefect Φ n t|)) atTop (𝓝 0) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,hb,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine ⟨Φ,hΦ,heq,hs,hb,tendsto_integerCellDefect_of_L1_modulus hΦ (hF.2.1.congr heq) ?_⟩
  apply (criticalState_tendsto_L1_increment_div_sqrt hW ht hF).congr fun h => ?_
  congr 1
  apply integral_congr_ae
  filter_upwards [heq,(measurePreserving_add_right volume h).quasiMeasurePreserving.ae heq] with u h1 h2
  rw [h1,show F (u+h) = Φ (u+h) from h2]

#print axioms criticalState_integerCellDefect

end GaloisForLFunctions.ExclusionOfTheCriticalState
