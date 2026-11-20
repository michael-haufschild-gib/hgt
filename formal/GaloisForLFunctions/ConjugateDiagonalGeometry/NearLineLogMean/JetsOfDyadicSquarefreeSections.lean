import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheRegularPartOfSquarefreeSections
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn
import GaloisForLFunctions.RHTower.ZetaFisherVariance

/-!
# Multiplicity from dyadic squarefree sections

Two sharp cutoffs cancel the density pole, including its removable
value d log 2. The explicit error is locally uniform throughout the
right half-plane. Applying holomorphic convergence to the resulting
entire polynomials detects every order of a zeta zero by finite
logarithmically weighted sums.
-/
noncomputable section
open Finset Complex Filter MeasureTheory
open scoped Topology
open _root_.RHTower.Sieve (squarefreeDensity)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def powerMass (X : ℝ) (s : ℂ) := ∫ t in Set.Ioc 1 X,(t:ℂ)^(-s)

/-- Holomorphic limit of the dyadic differences, defined also at one. -/
def squarefreeDyadicLimit (s : ℂ) :=
  (squarefreeDensity:ℂ)*powerMass 2 s+(1-(2:ℂ)^(1-s))*squarefreeRegularPart s

private theorem mass_one {X : ℝ} (hx : 1≤X) : powerMass X 1=(Real.log X:ℂ) := by
  have hr : (∫ t in Set.Ioc 1 X,t⁻¹) = Real.log X := by
    rw [←intervalIntegral.integral_of_le hx,integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx),div_one]
  unfold powerMass
  simp_rw [Complex.cpow_neg_one,←Complex.ofReal_inv]
  rw [integral_complex_ofReal,hr]

theorem squarefreeDyadicLimit_one : squarefreeDyadicLimit 1=(squarefreeDensity:ℂ)*(Real.log 2:ℂ) := by
  simp only [squarefreeDyadicLimit,sub_self,Complex.cpow_zero,mul_zero,zero_mul,add_zero,mass_one (by norm_num : (1:ℝ)≤2)]

private theorem mass_dilation {X : ℝ} (hx : 1≤X) (s : ℂ) :
    powerMass (2*X) s=powerMass 2 s + (2:ℂ)^(1-s)*powerMass X s := by
  have hp := zero_lt_one.trans_le hx
  have h2x : 1≤2*X := by linarith
  by_cases he : s=1
  · subst s
    rw [mass_one h2x,mass_one (by norm_num),mass_one hx,sub_self,Complex.cpow_zero,one_mul,
      Real.log_mul (by norm_num : (2:ℝ)≠0) hp.ne',Complex.ofReal_add]
  have H (Y:ℝ) (hy:1≤Y) : powerMass Y s=((Y:ℂ)^(1-s)-1)/(1-s) := by
    rw [eq_div_iff (sub_ne_zero.mpr he.symm),mul_comm];exact (squarefree_density_primitive hy s).symm
  rw [H _ h2x,H _ (by norm_num),H _ hx,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) hp.le,
    Complex.ofReal_ofNat]
  ring

/-- Uniform dyadic error, regular across s = 1. -/
theorem squarefree_dyadic_error {X : ℝ} (hx : 1≤X) {s : ℂ} (hs : 1/2<s.re) :
    ‖dyadicSquarefreeDifference X s-squarefreeDyadicLimit s‖ ≤
       12*(1+‖s‖/(s.re-1/2))*X^(1/2-s.re) := by
  let q := (2:ℂ)^(1-s)
  let E := fun Y => squarefreeSection Y s-(squarefreeDensity:ℂ)*powerMass Y s-squarefreeRegularPart s
  have hE (Y : ℝ) (hy : 1≤Y) : ‖E Y‖ ≤ 4*(1+‖s‖/(s.re-1/2))*Y^(1/2-s.re) :=
    squarefree_section_regular_part_error hy hs
  have htwo : 1≤2*X := by linarith
  have heq : dyadicSquarefreeDifference X s-squarefreeDyadicLimit s=E (2*X)-q*E X := by
    simp only [dyadicSquarefreeDifference,squarefreeDyadicLimit,E,q,mass_dilation hx];ring
  have hq : ‖q‖≤2 := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (1-s)
    simp only [Complex.ofReal_ofNat,Complex.sub_re,Complex.one_re] at hh
    change ‖(2:ℂ)^(1-s)‖≤2
    rw [hh]
    conv_rhs => rw [←Real.rpow_one (2:ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hp : (2*X)^(1/2-s.re) ≤ X^(1/2-s.re) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) (by linarith) (sub_nonpos.mpr hs.le)
  have hn : 0≤4*(1+‖s‖/(s.re-1/2)) := by have := sub_pos.mpr hs;positivity
  have H := (hE _ htwo).trans (mul_le_mul_of_nonneg_left hp hn)
  rw [heq]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact (add_le_add H (mul_le_mul hq (hE _ hx) (norm_nonneg _) (by norm_num))).trans_eq (by ring)

private def halfPlane := {s : ℂ | 1/2<s.re}
private theorem halfPlane_open : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re

/-- Uniform convergence on compact subsets includes compact sets
crossing the abscissa of absolute convergence. -/
theorem squarefree_dyadic_locally_uniform :
    TendstoLocallyUniformlyOn (fun X : ℝ => dyadicSquarefreeDifference X) squarefreeDyadicLimit
      atTop {s : ℂ | 1/2<s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact halfPlane_open]
  intro K hsub hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases K.eq_empty_or_nonempty with rfl|hne
  · simp
  obtain ⟨lo,hlo,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨hi,hhi,hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
  have hc : 1/2<lo.re := hsub hlo
  let D := 12*(1+‖hi‖/(lo.re-1/2))
  have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hc)).const_mul D
  rw [mul_zero] at hh
  filter_upwards [hh.eventually_lt_const hε,eventually_ge_atTop (1:ℝ)] with X hX hx s hsk
  have hs : 1/2<s.re := hsub hsk
  have hsr := hmin hsk
  have hsn := hmax hsk
  rw [dist_comm,dist_eq_norm]
  apply (squarefree_dyadic_error hx hs).trans_lt
  apply lt_of_le_of_lt _ hX
  rw [neg_sub]
  apply mul_le_mul
  · dsimp only [D];gcongr
    · exact hsn
    · exact sub_pos.mpr hc
    · exact hsr
  · exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hsr])
  · exact Real.rpow_nonneg (zero_le_one.trans hx) _
  · dsimp only [D];have := sub_pos.mpr hc;positivity

private theorem entire_section (X : ℝ) : Differentiable ℂ (squarefreeSection X) := by
  rw [show squarefreeSection X=(fun s : ℂ => ∑ n∈Icc 1 ⌊X⌋₊,
    (n:ℂ)^(-s)*(((((ArithmeticFunction.moebius n:ℤ):ℝ)^2):ℝ):ℂ)) from funext (squarefreeSection_eq_positive X)]
  exact Differentiable.sum fun n hn s =>
    ((differentiableAt_id.neg).const_cpow (Or.inl (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (mem_Icc.mp hn).1)))).mul_const _

private theorem entire_dyadic (X : ℝ) : Differentiable ℂ (dyadicSquarefreeDifference X) := by
  apply (entire_section (2*X)).sub
  exact ((differentiable_const.sub differentiable_id).const_cpow (Or.inl (by norm_num : (2:ℂ)≠0))).mul (entire_section X)

/-- All arithmetic derivatives converge to the corresponding zeta
quotient derivatives, with the pole already removed before differentiating. -/
theorem squarefree_dyadic_jet (j : ℕ) :
    TendstoLocallyUniformlyOn (fun X : ℝ => iteratedDeriv j (dyadicSquarefreeDifference X))
      (iteratedDeriv j squarefreeDyadicLimit) atTop {s : ℂ | 1/2<s.re} :=
  GaloisForLFunctions.iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform halfPlane_open
    squarefree_dyadic_locally_uniform (.of_forall fun X => (entire_dyadic X).differentiableOn) j

/-- At every point in the open right strip, the dyadic limit vanishes
to exactly the multiplicity of the zeta zero there. -/
theorem squarefree_dyadic_order {s : ℂ} (hlo : 1/2<s.re) (hhi : s.re<1) :
    analyticOrderAt squarefreeDyadicLimit s=analyticOrderAt riemannZeta s := by
  let U := {z : ℂ | 1/2<z.re ∧ z.re<1}
  have ho : IsOpen U := halfPlane_open.inter (isOpen_lt Complex.continuous_re continuous_const)
  let f := fun z : ℂ => (1-(2:ℂ)^(1-z))/riemannZeta (2*z)
  have eq : squarefreeDyadicLimit =ᶠ[𝓝 s] f*riemannZeta := by
    filter_upwards [ho.mem_nhds (show s∈U from ⟨hlo,hhi⟩)] with z hz
    have he := tendsto_nhds_unique (squarefree_dyadic_locally_uniform.tendsto_at hz.1)
      (dyadic_squarefree_limit hz.1 hz.2)
    rw [he,Pi.mul_apply];dsimp only [f];ring
  have hz : riemannZeta (2*s)≠0 := riemannZeta_ne_zero_of_one_lt_re (by
    simp only [two_mul,Complex.add_re];linarith)
  have hs1 : s≠1 := by rintro rfl; norm_num at hhi
  have h2 : 2*s≠1 := by
    intro he;have hre := congrArg Complex.re he
    simp only [two_mul,Complex.add_re,Complex.one_re] at hre;linarith
  have hf : AnalyticAt ℂ f s := by
    apply AnalyticAt.div _ _ hz
    · apply AnalyticAt.sub analyticAt_const
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
      exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).cexp
    · exact (_root_.RHTower.analyticAt_riemannZeta h2).comp (analyticAt_const.mul analyticAt_id)
  have hq : (2:ℂ)^(1-s)≠1 := by
    have he := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<2) (1-s)
    simp only [Complex.ofReal_ofNat,Complex.sub_re,Complex.one_re] at he
    intro h
    rw [h,norm_one] at he
    exact (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) (sub_pos.mpr hhi)).ne he
  rw [analyticOrderAt_congr eq,analyticOrderAt_mul hf (_root_.RHTower.analyticAt_riemannZeta hs1),
    hf.analyticOrderAt_eq_zero.mpr (div_ne_zero (sub_ne_zero.mpr hq.symm) hz),zero_add]

/-- Multiplicity at least m is equivalent to decay of the first m
ordinary arithmetic derivatives along one common cofinal sequence. -/
theorem squarefree_jet_vanishing_iff {s : ℂ} (hlo : 1/2<s.re) (hhi : s.re<1) (m : ℕ) :
    (∃ X : ℕ → ℝ,Tendsto X atTop atTop ∧ ∀ j<m,Tendsto (fun n =>
      iteratedDeriv j (dyadicSquarefreeDifference (X n)) s) atTop (𝓝 0)) ↔
      (m:ℕ∞)≤analyticOrderAt riemannZeta s := by
  have hDiff := squarefree_dyadic_locally_uniform.differentiableOn
    (.of_forall fun X => (entire_dyadic X).differentiableOn) halfPlane_open
  have hA := hDiff.analyticOnNhd halfPlane_open s hlo
  rw [←squarefree_dyadic_order hlo hhi,natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA]
  constructor
  · rintro ⟨X,hX,h⟩ j hj
    exact tendsto_nhds_unique (((squarefree_dyadic_jet j).tendsto_at hlo).comp hX) (h j hj)
  · intro h
    refine ⟨fun n => (n:ℝ),tendsto_natCast_atTop_atTop,fun j hj => ?_⟩
    rw [←h j hj]
    exact ((squarefree_dyadic_jet j).tendsto_at hlo).comp tendsto_natCast_atTop_atTop

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
