import GaloisForLFunctions.CountingHolography.Sections.TheMellinKernelOfSquareConductorPrices
import GaloisForLFunctions.CountingHolography.Sections.TheSignedProductOverSquareConductors
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.FiniteOffLineLandau
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # One-sided bounds for the signed square prefix

The Mellin integral of the prefix gives the price series divided by its
argument. Landau continuation along the real axis forces the same zero
width from either sign. A zero on the unexplored side would give a
nonzero residue in the holomorphic half-plane.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Finset MeasureTheory Filter Topology _root_.RHTower SquareRootThreshold Complex

private abbrev Q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
private def P (N : ℕ) := ∑ n ∈ Icc 1 N, Real.log (Q n:ℝ)
private abbrev J (z : ℂ) := 2+2*z
private abbrev W := mellin squarePrimeWeight

private theorem prefix_log (N : ℕ) : P N = Real.log (squareGeneratorPrefix N:ℝ) := by
  have h : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  rw [P,h,squareGeneratorPrefix]
  push_cast
  symm
  apply Real.log_prod
  intro n _
  exact (show 0 < (Q n:ℝ) by exact_mod_cast
    (show 0 < Q n from prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _)).ne'

private theorem price_cubic : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 0 < n → |Real.log (Q n:ℝ)| ≤ K*(n:ℝ)^3 := by
  obtain ⟨C,hC,h⟩ := successorSquare_diagonal_log_at_width
  refine ⟨2*C,by positivity,fun n hn => ?_⟩
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hp := Real.rpow_le_rpow_of_exponent_le (by linarith only [hn'] : 1 ≤ (n:ℝ)+1)
    (show 2*zetaZeroWidth ≤ 1 by linarith only [zetaZeroWidth_le_half])
  rw [Real.rpow_one] at hp
  exact (h n hn).trans ((mul_le_mul_of_nonneg_left
    (hp.trans (by linarith only [hn'] : (n:ℝ)+1 ≤ 2*n)) (mul_nonneg hC (sq_nonneg _))).trans_eq (by ring))

private theorem absolute_prefix_quartic : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
    (∑ k ∈ Icc 1 N, ‖squareConductorPrice k‖) ≤ K*(N:ℝ)^4 := by
  obtain ⟨K,hK,h⟩ := price_cubic
  refine ⟨K,hK,fun N => ?_⟩
  have row (k : ℕ) (hk : k ∈ Icc 1 N) : ‖squareConductorPrice k‖ ≤ K*(N:ℝ)^3 := by
    rw [squareConductorPrice,Complex.norm_real,Real.norm_eq_abs]
    exact (h k (mem_Icc.mp hk).1).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg k) (by exact_mod_cast (mem_Icc.mp hk).2) _) hK)
  exact (sum_le_sum row).trans_eq (by simp only [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]; ring)

private def density (e u : ℝ) := Real.exp (-3*u/2)*(e*P ⌊Real.exp (u/2)⌋₊)

private theorem density_measurable (e : ℝ) : Measurable (density e) := by
  have hP : Measurable P := measurable_of_countable _
  unfold density
  fun_prop

/-- Exponential substitution in the Mellin integral of a step prefix. -/
private theorem density_laplace (e : ℝ) {v : ℂ} (hv : 1/2 < v.re) :
    (∫ u in Set.Ioi (0:ℝ), (density e u:ℂ)*Complex.exp (-v*(u:ℂ))) =
      (e:ℂ)*LSeries squareConductorPrice (3+2*v)/(v+3/2) := by
  let s := 3+2*v
  let g := fun x : ℝ => (P ⌊x⌋₊:ℂ)*(x:ℂ)^(-(s+1))
  have hs : 4 < s.re := by dsimp only [s]; simp; linarith only [hv]
  obtain ⟨K,hK,h⟩ := absolute_prefix_quartic
  have hO : (fun N => ∑ k ∈ Icc 1 N, ‖squareConductorPrice k‖) =O[atTop] (fun N : ℕ => (N:ℝ)^(4:ℝ)) := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards with N
    simpa only [Real.norm_of_nonneg (sum_nonneg fun _ _ => norm_nonneg _),Real.rpow_ofNat,
      Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg N) 4)] using h N
  have hD := LSeries_eq_mul_integral' squareConductorPrice (r := 4) (by norm_num) hs hO
  have hP (n : ℕ) : (∑ k ∈ Icc 1 n, squareConductorPrice k) = (P n:ℂ) := by
    simp only [P,Complex.ofReal_sum,squareConductorPrice]
  simp_rw [hP] at hD
  let x := fun u : ℝ => Real.exp (u/2)
  have hd (u : ℝ) : HasDerivAt x (x u/2) u := by
    simpa only [x,id_eq,one_mul,div_eq_mul_inv] using
      (((hasDerivAt_id u).div_const (2:ℝ)).exp)
  have him : x '' (Set.Ioi 0) = Set.Ioi 1 := by
    ext t; constructor
    · rintro ⟨u,hu,rfl⟩
      exact Real.one_lt_exp_iff.mpr (half_pos hu)
    · intro ht
      change 1 < t at ht
      exact ⟨2*Real.log t,mul_pos two_pos (Real.log_pos ht),by simp [x,Real.exp_log (zero_lt_one.trans ht)]⟩
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (hd u).hasDerivWithinAt)
    (fun u _ t _ he => by have hh := Real.exp_injective he; linarith : Set.InjOn x (Set.Ioi 0)) g
  rw [him] at hi
  have hsub : (∫ u in Set.Ioi (0:ℝ), (density e u:ℂ)*Complex.exp (-v*(u:ℂ))) =
      (2*(e:ℂ))*(∫ t in Set.Ioi (1:ℝ), g t) := by
    rw [hi,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp only
    rw [abs_of_pos (show 0 < x u / 2 from half_pos (Real.exp_pos _)),Complex.real_smul]
    have hx : ((x u:ℝ):ℂ)^(-(s+1)) = Complex.exp ((u/2:ℝ)*(-(s+1))) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp]
    simp only [density,g,hx,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
    dsimp only [x,s]
    push_cast
    have h1 : Complex.exp (↑u / 2) * Complex.exp (↑u / 2 * -(3 + 2 * v + 1)) =
        Complex.exp (-3 * ↑u / 2) * Complex.exp (-v * ↑u) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (-((e:ℂ) * (P ⌊Real.exp (u / 2)⌋₊ : ℂ))) * h1
  change LSeries squareConductorPrice s = s*(∫ t in Set.Ioi (1:ℝ), g t) at hD
  have hn : v+3/2 ≠ 0 := fun he => by have h := congrArg Complex.re he; simp at h; linarith only [h,hv]
  rw [hsub,show 3+2*v=s from rfl,hD,eq_div_iff hn]
  dsimp only [s]; ring

private theorem density_growth {e C b u : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ 3+2*b)
    (hp : ∀ N : ℕ, e*P N ≤ C*(N:ℝ)^(3+2*b)) :
    density e u ≤ C*Real.exp (b*u) := by
  let x := Real.exp (u/2)
  have hx := Real.exp_pos (u/2)
  have hN := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx.le) hb
  have h := (hp ⌊x⌋₊).trans (mul_le_mul_of_nonneg_left hN hC)
  refine (mul_le_mul_of_nonneg_left h (Real.exp_pos (-3*u/2)).le).trans_eq ?_
  rw [Real.rpow_def_of_pos hx,Real.log_exp,mul_left_comm,← Real.exp_add]
  congr 2; ring

private theorem extension_of_prefix_bound {a e C : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2)
    (he : |e|=1) (hC : 0 ≤ C) (hp : ∀ N : ℕ, e*P N ≤ C*(N:ℝ)^(3+2*a)) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {z : ℂ | 1/2+a < z.re} ∧
      ∀ z : ℂ, 1 < z.re → H z = squareConductorContinuation (J z) := by
  obtain ⟨K,hK,habs⟩ := absolute_prefix_quartic
  have hraw (N : ℕ) : |P N| ≤ K*(N:ℝ)^4 := by
    apply (abs_sum_le_sum_abs _ _).trans
    simpa only [squareConductorPrice,Complex.norm_real,Real.norm_eq_abs] using habs N
  have hK' (u : ℝ) (_ : 0 < u) : |density e u| ≤ K*Real.exp (u/2) := by
    have hh (d : ℝ) (hd : |d|=1) (N : ℕ) : d*P N ≤ K*(N:ℝ)^(3+2*(1/2:ℝ)) := by
      have h := le_abs_self (d*P N)
      rw [abs_mul,hd,one_mul] at h
      simpa only [show (3:ℝ)+2*(1/2)=4 by norm_num,Real.rpow_ofNat] using h.trans (hraw N)
    rw [abs_le]
    have h₁ := density_growth (u := u) hK (by norm_num) (hh e he)
    have h₂ := density_growth (u := u) hK (by norm_num) (hh (-e) (by simpa only [abs_neg] using he))
    have he' : density (-e) u = -density e u := by unfold density; ring
    rw [he'] at h₂
    rw [show (1/2:ℝ)*u=u/2 by ring] at h₁ h₂
    constructor <;> linarith only [h₁,h₂]
  let Λ := fun v : ℂ => (e:ℂ)*squarePriceRegularContinuation (3+2*v)/(v+3/2)
  have hΛ (t : ℝ) (ht : a < t) : AnalyticAt ℂ Λ (t:ℂ) := by
    have hh : AnalyticAt ℂ squarePriceRegularContinuation (3+2*(t:ℂ)) := by
      simpa only [Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_ofNat] using
        analyticAt_squarePriceRegularContinuation_real (t := 3+2*t) (by linarith only [ha,ht])
    have hz : (t:ℂ)+3/2 ≠ 0 := by
      intro h; have h' := congrArg Complex.re h; simp at h'; linarith only [ha,ht,h']
    exact (analyticAt_const.mul (hh.comp (f := fun v : ℂ => 3+2*v) (x := (t:ℂ)) (by fun_prop))).div
      (analyticAt_id.add analyticAt_const) hz
  have hright (v : ℂ) (hv : 1/2 < v.re) :
      squarePriceRegularContinuation (3+2*v) = squareConductorContinuation (3+2*v) := by
    let z := (3+2*v)/2-1
    have hz : 1 < z.re := by dsimp only [z]; simp; linarith only [hv]
    have hz₁ : z ≠ 1 := fun h => hz.ne' (by rw [h]; rfl)
    apply squarePriceRegularContinuation_eq hz₁
    rw [zetaResidueUnit,Function.update_of_ne hz₁]
    exact mul_ne_zero (sub_ne_zero.mpr hz₁) (riemannZeta_ne_zero_of_one_lt_re hz)
  obtain ⟨F,hF,hFright⟩ := exists_differentiable_extension_of_le_exp (density_measurable e)
    hK' ha ha' (fun u _ => density_growth hC (by linarith only [ha]) hp) hΛ (fun v hv => by
      rw [density_laplace e hv]
      dsimp only [Λ]
      rw [hright v hv]
      have hh : 4 < (3+2*v).re := by simp; linarith only [hv]
      rw [LSeries_squareConductorPrice hh,squareConductorContinuation])
  let H := fun z : ℂ => ((z+1)*(e:ℂ))*F (z-1/2)
  have hU : IsOpen {z : ℂ | 1/2+a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  refine ⟨H,?_,?_⟩
  · apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    have h : a < (z-1/2).re := by change 1/2+a < z.re at hz; simp; linarith only [hz]
    exact ((((differentiableAt_id.add_const _).mul_const _).mul
      ((hF _ h).comp z (differentiableAt_id.sub_const _)))).differentiableWithinAt
  · intro z hz
    have h : 1/2 < (z-1/2).re := by simp; linarith only [hz]
    have hz' : z+1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith only [hz,hh]
    have he₂ : (e:ℂ)*(e:ℂ)=1 := by
      have h : e*e=1 := by nlinarith only [sq_abs e,congrArg (fun x : ℝ => x^2) he]
      exact_mod_cast h
    dsimp only [H]
    rw [hFright _ h]
    dsimp only [Λ]
    rw [hright _ h,show 3+2*(z-1/2)=J z by ring,show z-1/2+3/2=z+1 by ring]
    field_simp [hz']; linear_combination (squareConductorContinuation (J z))*he₂

private theorem cleared_price_iff {z h : ℂ} (hz : z ≠ 1) (hu : zetaResidueUnit z ≠ 0) :
    h = squareConductorContinuation (J z) ↔
      (z-1)*zetaResidueUnit z*(h-squareConductorAnalyticRemainder (J z)) =
      W z*(zetaResidueUnit z-(z-1)*deriv zetaResidueUnit z) := by
  have ht : J z/2-1=z := by ring
  have hd : -deriv riemannZeta z/riemannZeta z =
      (z-1)⁻¹-deriv zetaResidueUnit z/zetaResidueUnit z := by
    rw [neg_div,← logDeriv_apply,logDeriv_zeta_eq hz hu,logDeriv_apply]; ring
  rw [squareConductorContinuation,ht,hd]
  field_simp [sub_ne_zero.mpr hz,hu]
  constructor <;> intro he <;> linear_combination he

private theorem width_of_price_extension {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) (H : ℂ → ℂ)
    (hH : AnalyticOnNhd ℂ H {z : ℂ | 1/2+a < z.re})
    (hagree : ∀ z : ℂ, 1 < z.re → H z = squareConductorContinuation (J z)) : zetaZeroWidth ≤ a := by
  apply (zetaZeroWidth_le_iff_suzukiZetaZeroFreeRightOf ha).mpr
  intro ρ hρ hρ₁ hζ
  let U := {z : ℂ | 1/2+a < z.re}
  let L := fun z : ℂ => (z-1)*zetaResidueUnit z*(H z-squareConductorAnalyticRemainder (J z))
  let R := fun z : ℂ => W z*(zetaResidueUnit z-(z-1)*deriv zetaResidueUnit z)
  have hL : AnalyticOnNhd ℂ L U := by
    intro z hz
    have h3 : 3 < (J z).re := by change 1/2+a < z.re at hz; simp [J]; linarith only [ha,hz]
    exact (((analyticAt_id.sub analyticAt_const).mul (analyticAt_zetaResidueUnit z)).mul
      ((hH z hz).sub ((analytic_squareConductorAnalyticRemainder _ h3).comp
        (f := J) (show AnalyticAt ℂ J z from (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 2+2*z) z)))))
  have hR : AnalyticOnNhd ℂ R U := by
    intro z _
    have hW := (differentiable_mellin_squarePrimeWeight.differentiableOn.analyticOnNhd isOpen_univ) z (Set.mem_univ _)
    exact hW.mul ((analyticAt_zetaResidueUnit z).sub ((analyticAt_id.sub analyticAt_const).mul
      (analyticAt_zetaResidueUnit z).deriv))
  have h2 : (2:ℂ) ∈ U := by change 1/2+a < (2:ℂ).re; norm_num; linarith only [ha']
  have hEq : Set.EqOn L R U := hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt (1/2+a)).isPreconnected h2 (by
      filter_upwards [(Complex.continuous_re.continuousAt (x := (2:ℂ))).eventually
        (lt_mem_nhds (by norm_num : (1:ℝ)<(2:ℂ).re))] with z hz
      have hz₁ : z ≠ 1 := fun he => hz.ne' (by rw [he]; rfl)
      have hu : zetaResidueUnit z ≠ 0 := by
        rw [zetaResidueUnit,Function.update_of_ne hz₁]
        exact mul_ne_zero (sub_ne_zero.mpr hz₁) (riemannZeta_ne_zero_of_one_lt_re hz)
      exact (cleared_price_iff hz₁ hu).mp (hagree z hz))
  have hρ' : ρ.re < 1 := by
    by_contra! h
    exact riemannZeta_ne_zero_of_one_le_re h hζ
  have h₀ := analyticAt_riemannZeta_primeShiftResidueClosability hρ₁
  obtain ⟨g,hg,hg₀,hfac⟩ := h₀.analyticOrderAt_ne_top.mp (analyticOrderAt_riemannZeta_ne_top hρ₁)
  have hnear : H =ᶠ[𝓝[≠] ρ] fun z => squareConductorContinuation (J z) := by
    have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [self_mem_nhdsWithin (a := ρ) (s := {ρ}ᶜ),nhdsWithin_le_nhds (hU.mem_nhds hρ),
      nhdsWithin_le_nhds hfac,nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg₀),
      nhdsWithin_le_nhds (eventually_ne_nhds hρ₁)] with z hne hz hfact hgz hz₁
    have hζ' : riemannZeta z ≠ 0 := by
      rw [hfact,smul_eq_mul]; exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hne)) hgz
    have hu : zetaResidueUnit z ≠ 0 := by
      rw [zetaResidueUnit,Function.update_of_ne hz₁]; exact mul_ne_zero (sub_ne_zero.mpr hz₁) hζ'
    exact (cleared_price_iff hz₁ hu).mpr (hEq hz)
  obtain ⟨hne,hres⟩ := squareConductorContinuation_zero_residue hζ (by linarith only [hρ,ha]) hρ'
  have hJ : Tendsto J (𝓝[≠] ρ) (𝓝[≠] J ρ) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(show Continuous J from (by fun_prop : Continuous fun z : ℂ => 2+2*z)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin (a := ρ) (s := {ρ}ᶜ)] with z hz
    intro h
    apply hz
    change 2+2*z=2+2*ρ at h
    exact Set.mem_singleton_iff.mpr (by linear_combination h/2)
  have hlim : Tendsto (fun z => (J z-J ρ)*H z) (𝓝[≠] ρ)
      (𝓝 (-2*(zetaMultiplicity ρ:ℂ)*W ρ)) :=
    (hres.comp hJ).congr' (hnear.mono fun z he => by dsimp only [Function.comp_apply]; rw [he])
  have ht : Tendsto (fun z => J z-J ρ) (𝓝[≠] ρ) (𝓝 0) := by
    exact (tendsto_sub_self_punctured_zero (J ρ)).comp hJ
  have hzero := ht.mul ((hH ρ hρ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  exact hne ((tendsto_nhds_unique hlim hzero).trans (zero_mul _))

/-- Either one-sided power bound for the log prefix recovers the zeta zero width. -/
theorem zetaZeroWidth_le_iff_one_sided_square_prefix {a e : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) (he : |e|=1) :
    zetaZeroWidth ≤ a ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      e*Real.log (squareGeneratorPrefix N:ℝ) ≤ C*(N:ℝ)^(3+2*a) := by
  constructor
  · intro hw
    obtain ⟨C,hC,h⟩ := (zetaZeroWidth_le_iff_square_generator_prefix ha ha').mp hw
    refine ⟨C,hC,fun N => (le_abs_self _).trans ?_⟩
    rw [abs_mul,he,one_mul]; exact h N
  · rintro ⟨C,hC,h⟩
    obtain ⟨H,hH,hagree⟩ := extension_of_prefix_bound ha ha' he hC (fun N => (prefix_log N) ▸ h N)
    exact width_of_price_extension ha ha' H hH hagree

end GaloisForLFunctions.CountingHolography.Sections
