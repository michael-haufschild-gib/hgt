import GaloisForLFunctions.RHTower.ChiRamanujanCubicRegularSource
import GaloisForLFunctions.RHTower.ZetaStripPolynomialBound
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Global analytic control of the actual BAG residue factors

Unconditional polynomial-width zero-free disks for the pole-removed zeta factor,
uniform over the closed damping strip. Cauchy estimates control every derivative
of the factor and its reciprocal. These are actual arithmetic inputs for the
noncompact cubic boundary; no source growth or RH premise is assumed.
-/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace RHTower.BAGTrace

/-- Actual zero-freeness and reciprocal control on a polynomial-width region
crossing the critical plane, not an assumed reciprocal bound. -/
theorem exists_zeta_polynomial_zeroFree_region :
    ∃ a ∈ Ioc (0 : ℝ) (1/2), ∃ C > 0, ∀ σ t : ℝ, 3 < |t| →
      1-a/(1+|t|)^9 ≤ σ →
      riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I) ≠ 0 ∧
      ‖(riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I))⁻¹‖ ≤ C*(1+|t|)^9 := by
  obtain ⟨A,hA,C₀,hC₀,hInv⟩ := ZetaInvBnd
  obtain ⟨B,hB,hZero⟩ := ZetaZeroFree
  have hApos : 0 < A := hA.1
  let a := min A B
  let C := C₀+Real.exp (22/4)*(1+1/A)
  have ha : 0 < a := lt_min hA.1 hB.1
  have haA : a ≤ A := min_le_left _ _
  have haB : a ≤ B := min_le_right _ _
  have hrest : 0 < Real.exp (22/4)*(1+1/A) := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨a,⟨ha,haA.trans hA.2⟩,C,hC,?_⟩
  intro σ t ht hσ
  let L := Real.log |t|
  let T := 1+|t|
  have hL1 : 1 < L := logt_gt_one ht.le
  have hL : 0 < L := lt_trans zero_lt_one hL1
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hLT : L ≤ T := by
    have h := Real.log_le_sub_one_of_pos (show 0 < |t| by linarith)
    dsimp [L,T]
    linarith
  have hLT9 : L^9 ≤ T^9 := pow_le_pow_left₀ hL.le hLT 9
  have hlower (D : ℝ) (haD : a ≤ D) : 1-D/L^9 ≤ σ := by
    have hd : a/T^9 ≤ D/L^9 := div_le_div₀ (ha.le.trans haD) haD (pow_pos hL 9) hLT9
    change 1-a/T^9 ≤ σ at hσ
    linarith
  constructor
  · by_cases hσ1 : 1 ≤ σ
    · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1)
    · exact hZero σ t ht ⟨hlower B haB,lt_of_not_ge hσ1⟩
  · by_cases hright : σ < 1+A/L^9
    · have hi := hInv σ t ht ⟨hlower A haA,hright⟩
      have hp : L^7 ≤ T^9 := (pow_le_pow_left₀ hL.le hLT 7).trans
        (pow_le_pow_right₀ hT1 (by norm_num : 7 ≤ 9))
      have hi' : ‖(riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I))⁻¹‖ ≤ C₀*L^7 := by
        simpa only [norm_inv,one_div,Real.rpow_ofNat] using hi
      exact hi'.trans ((mul_le_mul_of_nonneg_left hp hC₀.le).trans
        (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hT.le 9)))
    · have hwidth : 0 < A/L^9 := div_pos hA.1 (pow_pos hL 9)
      have hs : 1 < σ := by linarith [le_of_not_gt hright]
      have hquot : A/L^9 ≤ σ-1 := by linarith [le_of_not_gt hright]
      have hinv : 1/(σ-1) ≤ T^9/A := by
        apply (div_le_div_iff₀ (sub_pos.mpr hs) hA.1).mpr
        have hq := (div_le_iff₀ (pow_pos hL 9)).mp hquot
        have hmul := mul_le_mul_of_nonneg_left hLT9 (sub_pos.mpr hs).le
        nlinarith
      have hm := Sieve.norm_LSeries_moebius_le_uniform (σ := σ) (t := t) hs
      rw [Sieve.LSeries_moebius_eq_inv (by simpa using hs)] at hm
      have hfactor : 1+T^9/A ≤ (1+1/A)*T^9 := by
        have hp : 1 ≤ T^9 := one_le_pow₀ hT1
        calc
          1+T^9/A ≤ T^9+T^9/A := add_le_add hp (le_refl _)
          _ = (1+1/A)*T^9 := by ring
      calc
        _ ≤ Real.exp (22/4)*(1+1/(σ-1)) := hm
        _ ≤ Real.exp (22/4)*(1+T^9/A) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hinv) (Real.exp_pos _).le
        _ ≤ Real.exp (22/4)*(1+1/A)*T^9 := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfactor (Real.exp_pos (22/4)).le
        _ ≤ C*T^9 := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hT.le 9)

private theorem near_vertical_coordinates {σ t r : ℝ} {z : ℂ}
    (hz : z ∈ closedBall ((σ : ℂ)+(t : ℂ)*Complex.I) r) :
    |z.re-σ| ≤ r ∧ |z.im-t| ≤ r := by
  have hn : ‖z-((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ r := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  constructor
  · simpa using (Complex.abs_re_le_norm (z-((σ : ℂ)+(t : ℂ)*Complex.I))).trans hn
  · simpa using (Complex.abs_im_le_norm (z-((σ : ℂ)+(t : ℂ)*Complex.I))).trans hn

/-- Polynomially shrinking zero-free disks with simultaneous bounds for the actual
pole-removed zeta factor and its reciprocal, uniform through sigma=1. -/
theorem exists_residue_polynomial_disks :
    ∃ c ∈ Ioc (0 : ℝ) 1, ∃ M > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ, 5 ≤ |t| →
      ∀ z ∈ closedBall ((σ : ℂ)+(t : ℂ)*Complex.I) (c/(1+|t|)^9),
        zetaResidueFactor z ≠ 0 ∧
        ‖zetaResidueFactor z‖ ≤ M*(1+|t|)^9 ∧
        ‖(zetaResidueFactor z)⁻¹‖ ≤ M*(1+|t|)^9 := by
  obtain ⟨a,ha,C,hC,hregion⟩ := exists_zeta_polynomial_zeroFree_region
  let c := a/(2 : ℝ)^9
  let M := 30+C*(2 : ℝ)^9
  have hc : 0 < c := div_pos ha.1 (by positivity)
  have hc1 : c ≤ 1 := by dsimp [c]; norm_num; linarith [ha.2]
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨c,⟨hc,hc1⟩,M,hM,?_⟩
  intro σ hσ t ht z hz
  let T := 1+|t|
  let r := c/T^9
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hr1 : r ≤ 1 := (div_le_self hc.le (one_le_pow₀ hT1)).trans hc1
  have hcoord := near_vertical_coordinates hz
  change |z.re-σ| ≤ r ∧ |z.im-t| ≤ r at hcoord
  have himUpper : |z.im| ≤ |t|+1 := by
    calc
      |z.im| = |(z.im-t)+t| := by congr 1; ring
      _ ≤ |z.im-t|+|t| := by simpa only [Real.norm_eq_abs] using norm_add_le (z.im-t) t
      _ ≤ |t|+1 := by linarith [hcoord.2]
  have himLower : 3 < |z.im| := by
    have hb : |t| ≤ |z.im-t|+|z.im| := by
      calc
        |t| = |(t-z.im)+z.im| := by congr 1; ring
        _ ≤ |t-z.im|+|z.im| := by simpa only [Real.norm_eq_abs] using norm_add_le (t-z.im) z.im
        _ = |z.im-t|+|z.im| := by rw [abs_sub_comm t z.im]
    linarith [hcoord.2]
  have hZ : 0 < 1+|z.im| := by positivity
  have hZT : 1+|z.im| ≤ 2*T := by dsimp [T]; linarith [abs_nonneg t]
  have hpow : (1+|z.im|)^9 ≤ (2*T)^9 := pow_le_pow_left₀ hZ.le hZT 9
  have hrad : r=a/(2*T)^9 := by simp only [r,c,div_div,mul_pow]
  have hrwidth : r ≤ a/(1+|z.im|)^9 := by
    rw [hrad]
    exact div_le_div₀ ha.1.le (le_refl a) (pow_pos hZ 9) hpow
  have hre : 1-a/(1+|z.im|)^9 ≤ z.re := by
    have hl := (abs_le.mp hcoord.1).1
    linarith [hσ.1]
  have hreg := hregion z.re z.im himLower hre
  have hzeta : riemannZeta z ≠ 0 := by
    simpa only [Complex.re_add_im] using hreg.1
  have hinvZ : ‖(riemannZeta z)⁻¹‖ ≤ C*(1+|z.im|)^9 := by
    simpa only [Complex.re_add_im] using hreg.2
  have hzne : z ≠ 1 := by intro he; norm_num [he] at himLower
  have hFne : zetaResidueFactor z ≠ 0 := by
    rw [zetaResidueFactor_of_ne hzne]
    exact mul_ne_zero (sub_ne_zero.mpr hzne) hzeta
  have hre0 : 0 ≤ z.re := by linarith [(abs_le.mp hcoord.1).1,hσ.1]
  have hre3 : z.re ≤ 3 := by linarith [(abs_le.mp hcoord.1).2,hσ.2]
  have hreQuarter : 1/4 ≤ z.re := by
    have hcHalf : c ≤ 1/2 := by dsimp [c]; norm_num; linarith [ha.2]
    have hrHalf : r ≤ 1/2 := (div_le_self hc.le (one_le_pow₀ hT1)).trans hcHalf
    linarith [(abs_le.mp hcoord.1).1,hσ.1]
  have hzm : ‖z-1‖ ≤ 3*T := by
    have hh := Complex.norm_le_abs_re_add_abs_im (z-1)
    have hreAbs : |z.re-1| ≤ 2 := abs_le.mpr ⟨by linarith,by linarith⟩
    simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at hh
    dsimp [T]
    linarith
  have hzupper : ‖riemannZeta z‖ ≤ 10*T := by
    have h := RHTower.norm_riemannZeta_le_quarter hreQuarter (by linarith : 2 ≤ |z.im|)
    dsimp [T]
    linarith
  have hFupper : ‖zetaResidueFactor z‖ ≤ 30*T^9 := by
    rw [zetaResidueFactor_of_ne hzne,norm_mul]
    have hh := mul_le_mul hzm hzupper (norm_nonneg _) (by positivity : 0 ≤ 3*T)
    have hp : T^2 ≤ T^9 := pow_le_pow_right₀ hT1 (by norm_num)
    nlinarith
  have hnormLower : 1 ≤ ‖z-1‖ := by
    have h := Complex.abs_im_le_norm (z-1)
    simp only [Complex.sub_im,Complex.one_im,sub_zero] at h
    linarith
  have hFinv : ‖(zetaResidueFactor z)⁻¹‖ ≤ (C*(2 : ℝ)^9)*T^9 := by
    calc
      _ = ‖(riemannZeta z)⁻¹‖/‖z-1‖ := by
        simp only [zetaResidueFactor_of_ne hzne,mul_inv_rev,norm_mul,norm_inv,div_eq_mul_inv]
      _ ≤ ‖(riemannZeta z)⁻¹‖ := div_le_self (norm_nonneg _) hnormLower
      _ ≤ C*(1+|z.im|)^9 := hinvZ
      _ ≤ C*(2*T)^9 := mul_le_mul_of_nonneg_left hpow hC.le
      _ = _ := by rw [mul_pow]; ring
  refine ⟨hFne,hFupper.trans ?_,hFinv.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (pow_nonneg hT.le 9)
    dsimp [M]
    linarith [mul_pos hC (by positivity : 0 < (2 : ℝ)^9)]
  · apply mul_le_mul_of_nonneg_right _ (pow_nonneg hT.le 9)
    dsimp [M]
    linarith

/-- Uniform polynomial zero-free disks at every height, including the regularized pole.
This supplies actual complex neighborhoods for the subsequent multivariable source estimates. -/
theorem exists_residue_global_polynomial_disks :
    ∃ c ∈ Ioc (0 : ℝ) 1, ∃ M > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ,
      ∀ z ∈ closedBall ((σ : ℂ)+(t : ℂ)*Complex.I) (c/(1+|t|)^9),
        zetaResidueFactor z ≠ 0 ∧
        ‖zetaResidueFactor z‖ ≤ M*(1+|t|)^9 ∧
        ‖(zetaResidueFactor z)⁻¹‖ ≤ M*(1+|t|)^9 := by
  obtain ⟨c₀,hc₀,M₀,hM₀,hhigh⟩ := exists_residue_polynomial_disks
  let center : ℝ × ℝ → ℂ := fun w => (w.1 : ℂ)+(w.2 : ℂ)*Complex.I
  have hcenter : Continuous center := by dsimp [center]; fun_prop
  let K := center '' Icc (1,-5) (2,5)
  have hK : IsCompact K := isCompact_Icc.image hcenter
  have hopen : IsOpen {z : ℂ | zetaResidueFactor z ≠ 0} :=
    isOpen_ne_fun differentiable_zetaResidueFactor.continuous continuous_const
  have hKU : K ⊆ {z : ℂ | zetaResidueFactor z ≠ 0} := by
    rintro z ⟨w,hw,rfl⟩
    apply zetaResidueFactor_ne_zero_closed
    simpa [center] using hw.1.1
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open hopen hKU
  have hI : ContinuousOn (fun z => (zetaResidueFactor z)⁻¹) (cthickening δ K) := by
    intro z hz
    exact ((differentiable_zetaResidueFactor z).inv (hδU hz)).continuousAt.continuousWithinAt
  have hpair : ContinuousOn (fun z => (zetaResidueFactor z,(zetaResidueFactor z)⁻¹))
      (cthickening δ K) := differentiable_zetaResidueFactor.continuous.continuousOn.prodMk hI
  obtain ⟨B,hB⟩ := hK.cthickening.exists_bound_of_continuousOn hpair
  let c := min c₀ δ
  let M := M₀+|B|+1
  have hc : 0 < c := lt_min hc₀.1 hδ
  have hcC : c ≤ c₀ := min_le_left _ _
  have hcδ : c ≤ δ := min_le_right _ _
  have hM : 0 < M := by dsimp [M]; positivity
  have hMhigh : M₀ ≤ M := by dsimp [M]; linarith [abs_nonneg B]
  have hMlow : B ≤ M := by dsimp [M]; linarith [le_abs_self B]
  refine ⟨c,⟨hc,hcC.trans hc₀.2⟩,M,hM,?_⟩
  intro σ hσ t z hz
  have hT1 : 1 ≤ 1+|t| := by linarith [abs_nonneg t]
  have hT : 0 < (1+|t|)^9 := by positivity
  by_cases ht : 5 ≤ |t|
  · have hrad : c/(1+|t|)^9 ≤ c₀/(1+|t|)^9 := div_le_div_of_nonneg_right hcC hT.le
    have h := hhigh σ hσ t ht z (closedBall_subset_closedBall hrad hz)
    have he := mul_le_mul_of_nonneg_right hMhigh hT.le
    exact ⟨h.1,h.2.1.trans he,h.2.2.trans he⟩
  · have hsmall : |t| ≤ 5 := (lt_of_not_ge ht).le
    have hsK : ((σ : ℂ)+(t : ℂ)*Complex.I) ∈ K :=
      ⟨(σ,t),⟨⟨hσ.1,(abs_le.mp hsmall).1⟩,⟨hσ.2,(abs_le.mp hsmall).2⟩⟩,rfl⟩
    have hrad : c/(1+|t|)^9 ≤ δ := (div_le_self hc.le (one_le_pow₀ hT1)).trans hcδ
    have hzK := closedBall_subset_cthickening hsK δ (closedBall_subset_closedBall hrad hz)
    have hb := hB z hzK
    have he : B ≤ M*(1+|t|)^9 := hMlow.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hT1 (n := 9)) hM.le)
    exact ⟨hδU hzK,((norm_fst_le _).trans hb).trans he,((norm_snd_le _).trans hb).trans he⟩

/-- All derivatives have polynomial growth uniformly through the critical plane. -/
theorem exists_residue_derivative_polynomial_bounds (n : ℕ) :
    ∃ C > 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ t : ℝ,
      ‖iteratedDeriv n zetaResidueFactor ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤ C*(1+|t|)^(9*(n+1)) ∧
      ‖iteratedDeriv n (fun z => (zetaResidueFactor z)⁻¹) ((σ : ℂ)+(t : ℂ)*Complex.I)‖ ≤
        C*(1+|t|)^(9*(n+1)) := by
  obtain ⟨c,hc,M,hM,hdisks⟩ := exists_residue_global_polynomial_disks
  let C := (n.factorial : ℝ)*M/c^n
  have hc0 : 0 < c := hc.1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro σ hσ t
  let s : ℂ := (σ : ℂ)+(t : ℂ)*Complex.I
  let T := 1+|t|
  let r := c/T^9
  have hT : 0 < T := by dsimp [T]; positivity
  have hr : 0 < r := div_pos hc0 (pow_pos hT 9)
  have hdInv : DifferentiableOn ℂ (fun z => (zetaResidueFactor z)⁻¹) (closedBall s r) := by
    intro z hz
    exact ((differentiable_zetaResidueFactor z).inv (hdisks σ hσ t z hz).1).differentiableWithinAt
  have hF := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    differentiable_zetaResidueFactor.diffContOnCl
    (fun z hz => (hdisks σ hσ t z (sphere_subset_closedBall hz)).2.1)
  have hI := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hdInv.diffContOnCl_ball (subset_refl _))
    (fun z hz => (hdisks σ hσ t z (sphere_subset_closedBall hz)).2.2)
  have he : (n.factorial : ℝ)*(M*T^9)/r^n=C*T^(9*(n+1)) := by
    simp only [r,C,div_pow,show 9*(n+1)=9+9*n by omega,pow_add,pow_mul]
    field_simp
  exact ⟨hF.trans_eq he,hI.trans_eq he⟩

end RHTower.BAGTrace
