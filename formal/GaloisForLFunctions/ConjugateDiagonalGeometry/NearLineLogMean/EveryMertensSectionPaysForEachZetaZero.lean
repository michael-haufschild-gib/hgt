import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoBoundsForTheMertensDirichletSection
import GaloisForLFunctions.ArithmeticProduction.TheMollifiedZetaFunctionIsBandLimited
import GaloisForLFunctions.HTGeometry.PhragmenLindelofPower

/-!
# Every finite Möbius section pays for each zeta zero

Multiply the pole-cleared mollified error by a power of the cutoff whose
exponent varies across a strip. Abel summation controls the left edge.
On the right the vanishing convolution head pays for the growing power.
Evaluation at a zero then gives a lower bound for every cutoff.
-/

noncomputable section
open Complex Filter Finset
open _root_.RHTower
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def scale (N : ℕ) (r d : ℝ) (s : ℂ) :=
  Complex.exp (((Real.log N : ℝ) : ℂ) * (r : ℂ) * (s - (d : ℂ)))

private theorem norm_scale {N : ℕ} (hN : 1 ≤ N) (r d : ℝ) (s : ℂ) :
    ‖scale N r d s‖ = (N:ℝ) ^ (r * (s.re-d)) := by
  rw [scale,Complex.norm_exp,Real.rpow_def_of_pos (Nat.cast_pos.mpr hN)]
  congr 1
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.sub_re,zero_mul,mul_zero,sub_zero,add_zero]
  ring

private def errorSection (N : ℕ) (s : ℂ) :=
  zetaEntire s * edPoly mobCoeff (Icc 1 N) s - (s-1)

private theorem differentiable_error (N : ℕ) : Differentiable ℂ (errorSection N) :=
  (differentiable_zetaEntire.mul (differentiable_edPoly mobCoeff
    (fun _ hn => (mem_Icc.mp hn).1))).sub (differentiable_id.sub (differentiable_const _))

private theorem vertical_linear_bound {R : ℝ} {s : ℂ} (hs : 0 ≤ s.re) (hR : s.re ≤ R) :
    1 + ‖s‖ ≤ (R+1)*(1+|s.im|) := by
  have ht := Complex.norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg hs] at ht
  linarith only [ht,hR,mul_nonneg (hs.trans hR) (abs_nonneg s.im)]

private theorem edge_power {d : ℝ} {s : ℂ} (hd : 0 ≤ d) (hs : d ≤ s.re) (m : ℕ) :
    (1+|s.im|)^m ≤ 2^m * ‖s-((-1:ℝ):ℂ)‖^m := by
  have hr := Complex.re_le_norm (s-((-1:ℝ):ℂ))
  have hi := Complex.abs_im_le_norm (s-((-1:ℝ):ℂ))
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hr hi
  rw [←mul_pow]
  exact pow_le_pow_left₀ (by positivity) (by linarith only [hr,hi,hd,hs]) m

/-- A zero gives a power lower bound at every cutoff. Taking the right
edge farther away makes the interpolation slope arbitrarily close to one. -/
theorem mertens_cost_at_a_zero {ρ : ℂ} (hz : riemannZeta ρ = 0)
    {d r : ℝ} (hd : 0<d) (hdρ : d < ρ.re) (hr : 0 < r) (hr1 : r<1) :
    ∃ A : ℝ, 0<A ∧ ∀ {N : ℕ}, 1≤N →
      (N:ℝ)^(r*(ρ.re-d)) ≤ A*(1+mertensAbelCost N) := by
  let R := 3+3/(1-r)
  have h1r : 0<1-r := sub_pos.mpr hr1
  have hR : 3 ≤ R := le_add_of_nonneg_right (div_nonneg (by norm_num) h1r.le)
  have hρR := (re_le_zetaZeroAbscissa hz).trans zetaZeroAbscissa_le_one
  have hdR : d < R := by linarith only [hdρ,hρR,hR]
  have hRe : r*(R-d)+(3-R) ≤ 0 := by
    have hdiv := div_mul_cancel₀ (3:ℝ) h1r.ne'
    dsimp only [R]
    linarith only [hdiv,mul_nonneg hr.le hd.le,h1r]
  obtain ⟨C,k,hC,hζ⟩ := ArithmeticProduction.exists_norm_zetaEntire_le (by linarith only [hR] : 1≤R)
  obtain ⟨D,hD,hfar⟩ := far_right_mertens_error
  let L := (R+1)*(C+D+1)
  have hR0 : 0 ≤ R+1 := by linarith only [hR]
  have hL : 0 < L := mul_pos (by linarith only [hR]) (by linarith only [hC,hD])
  have hne : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hz
  have hdist := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  let S := 2^(k+1)*‖ρ-((-1:ℝ):ℂ)‖^(k+1)
  refine ⟨1+L*S/‖ρ-1‖,by dsimp only [S]; positivity,fun {N} hN => ?_⟩
  let B := 1+mertensAbelCost N
  have hcost : 0 ≤ mertensAbelCost N :=
    add_nonneg (norm_nonneg _) (mertens_abel_mass_nonneg N)
  have hB : 1 ≤ B := le_add_of_nonneg_right hcost
  have hB0 := zero_le_one.trans hB
  have hbase := (Nat.one_le_cast (α:=ℝ)).mpr hN
  let F := fun s => scale N r d s * errorSection N s
  have hF : Differentiable ℂ F := by
    apply Differentiable.mul _ (differentiable_error N)
    unfold scale
    fun_prop
  have absErr (s : ℂ) (hds : d ≤ s.re) (hsR : s.re ≤ R) :
      ‖errorSection N s‖ ≤ L*B*(1+|s.im|)^(k+1) := by
    let t := 1+|s.im|
    have t1 : 1≤t := le_add_of_nonneg_right (abs_nonneg _)
    have t0 := zero_le_one.trans t1
    have hk := one_le_pow₀ t1 (n:=k)
    have H := vertical_linear_bound (hd.le.trans hds) hsR
    have h1 : ‖s-1‖ ≤ (R+1)*t :=
      (norm_sub_le _ _).trans (by rw [norm_one,add_comm]; exact H)
    have hpoly : ‖edPoly mobCoeff (Icc 1 N) s‖ ≤ (R+1)*t*B :=
      (norm_mertens_section_from_abel_cost hN (hd.trans_le hds)).trans
        (mul_le_mul H (le_add_of_nonneg_left zero_le_one) hcost (mul_nonneg hR0 t0))
    have hZ := hζ s (by linarith only [hd,hds]) hsR
    have hp : ‖zetaEntire s‖ * ‖edPoly mobCoeff (Icc 1 N) s‖ ≤ (C*t^k)*((R+1)*t*B) :=
      mul_le_mul hZ hpoly (norm_nonneg _) (mul_nonneg hC (pow_nonneg t0 _))
    have hh : (R+1)*t ≤ (R+1)*t*(t^k*B) :=
      le_mul_of_one_le_right (mul_nonneg hR0 t0) (one_le_mul_of_one_le_of_one_le hk hB)
    have hL' : (C+1)*(R+1) ≤ L := by
      dsimp only [L]
      nlinarith only [mul_nonneg hR0 hD]
    calc ‖errorSection N s‖ ≤ ‖zetaEntire s * edPoly mobCoeff (Icc 1 N) s‖+‖s-1‖ := norm_sub_le _ _
         _ ≤ (C+1)*(R+1)*(B*t^(k+1)) := by
           rw [norm_mul,pow_succ]
           linarith only [hp,h1,hh]
         _ ≤ _ := by
           change _ ≤ L*B*t^(k+1)
           rw [mul_assoc L]
           exact mul_le_mul_of_nonneg_right hL' (mul_nonneg hB0 (pow_nonneg t0 _))
  have right (s : ℂ) (hs : s.re=R) : ‖F s‖ ≤ L*B*(1+|s.im|)^(k+1) := by
    have hs1 : s ≠ 1 := by
      intro hh
      rw [hh,Complex.one_re] at hs
      linarith only [hR,hs]
    have herr : errorSection N s = (s-1)*mobMollifiedError N s := by
      rw [errorSection,zetaEntire_eq hs1,mobMollifiedError]; ring
    have hf := hfar hN (hR.trans hs.ge : 3 ≤ s.re)
    have ht : 1 ≤ 1+|s.im| := le_add_of_nonneg_right (abs_nonneg _)
    have hm := vertical_linear_bound (by linarith only [hR,hs] : 0 ≤ s.re) hs.le
    have he : ‖s-1‖ ≤ (R+1)*(1+|s.im|) := (norm_sub_le _ _).trans (by rw [norm_one,add_comm]; exact hm)
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hbase hRe
    have hfac : D*(R+1) ≤ L*B :=
      (by dsimp only [L]; nlinarith only [hR0,mul_nonneg hR0 hC] : D*(R+1) ≤ L).trans
        (le_mul_of_one_le_right hL.le hB)
    change ‖scale N r d s * errorSection N s‖ ≤ _
    rw [norm_mul,norm_scale hN,herr,norm_mul,hs]
    rw [hs] at hf
    calc _ ≤ (N:ℝ)^(r*(R-d))*(((R+1)*(1+|s.im|))*(D*(N:ℝ)^(3-R))) := by
           gcongr
         _ = ((N:ℝ)^(r*(R-d))*(N:ℝ)^(3-R))*(D*(R+1)*(1+|s.im|)) := by ring
         _ ≤ D*(R+1)*(1+|s.im|) := by
           rw [←Real.rpow_add (Nat.cast_pos.mpr hN)]
           exact mul_le_of_le_one_left (by positivity) hpow
         _ ≤ _ := mul_le_mul hfac (by simpa using pow_le_pow_right₀ ht (Nat.succ_le_succ (Nat.zero_le k)) ) (by positivity) (mul_nonneg hL.le hB0)
  have edges (s : ℂ) (hs : d ≤ s.re) (hh : ‖F s‖ ≤ L*B*(1+|s.im|)^(k+1)) :
      ‖F s‖ ≤ L*B*2^(k+1)*‖s-((-1:ℝ):ℂ)‖^((k+1:ℕ):ℝ) := by
    rw [Real.rpow_natCast,mul_assoc (L*B)]
    exact hh.trans (mul_le_mul_of_nonneg_left (edge_power hd.le hs _) (mul_nonneg hL.le hB0))
  have hPL := HTGeometry.norm_le_mul_rpow_of_vertical_strip (F:=F) (c₀ := -1) (A:=d) (B:=R)
    (ν:=((k+1:ℕ):ℝ)) (N:=((k+1:ℕ):ℝ)) hdR (by positivity) (by linarith only [hd]) hF
    (C:=(N:ℝ)^(r*(R-d))*(L*B)) (by positivity) (by positivity)
    (fun s hs hs' => by
      change ‖scale N r d s * errorSection N s‖ ≤ _
      rw [norm_mul,norm_scale hN,Real.rpow_natCast,mul_assoc]
      exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hbase (by linarith only [mul_le_mul_of_nonneg_left hs' hr.le]))
        (absErr s hs hs') (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (fun s hs => edges s hs.ge (by
      change ‖scale N r d s * errorSection N s‖ ≤ _
      rw [norm_mul,norm_scale hN,hs,sub_self,mul_zero,Real.rpow_zero,one_mul]
      exact absErr s hs.ge (hs.le.trans hdR.le)))
    (fun s hs => edges s (hdR.le.trans hs.ge) (right s hs)) ρ hdρ.le (by linarith only [hρR,hR])
  change ‖scale N r d ρ * errorSection N ρ‖ ≤ _ at hPL
  rw [norm_mul,norm_scale hN,errorSection,zetaEntire_eq hne,hz,mul_zero,zero_mul,zero_sub,norm_neg,
    max_self,Real.rpow_natCast] at hPL
  have hq : (N:ℝ)^(r*(ρ.re-d)) ≤ (L*S/‖ρ-1‖)*B := by
    have hh := (le_div_iff₀ hdist).mpr hPL
    exact hh.trans_eq (by dsimp only [S]; ring)
  exact hq.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hB0)

/-- Every strictly subcritical power is exceeded at every sufficiently
large cutoff by the absolute Abel cost. -/
theorem eventually_large_mertens_abel_cost {b : ℝ} (hb : 0 ≤ b)
    (h : b < zetaZeroAbscissa) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C*(N:ℝ)^b < mertensAbelCost N := by
  obtain ⟨ρ,hz,hbρ⟩ := exists_zetaZero_lt_re h
  let d := (ρ.re-b)/2
  have hd : 0<d := by dsimp only [d]; linarith only [hbρ]
  have hgap : b < ρ.re-d := by dsimp only [d]; linarith only [hbρ]
  have hp := hb.trans_lt hgap
  obtain ⟨r,hr,hr1⟩ := exists_between ((div_lt_one hp).mpr hgap)
  have hr0 := (div_nonneg hb hp.le).trans_lt hr
  have he := (div_lt_iff₀ hp).mp hr
  obtain ⟨A,hA,hh⟩ := mertens_cost_at_a_zero hz hd (by linarith only [hp]) hr0 hr1
  have ht := (tendsto_rpow_atTop (sub_pos.mpr he)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 1, ht.eventually_gt_atTop (A*(1+|C|))] with N hN hlarge
  have hn := (Nat.one_le_cast (α:=ℝ)).mpr hN
  have hw := Real.one_le_rpow hn hb
  have hmul := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos (zero_lt_one.trans_le hn) b)
  change _ < (N:ℝ)^b * (N:ℝ)^(r*(ρ.re-d)-b) at hmul
  rw [←Real.rpow_add (zero_lt_one.trans_le hn),show b+(r*(ρ.re-d)-b)=r*(ρ.re-d) by ring] at hmul
  by_contra! hsmall
  have hCA := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (Nat.cast_nonneg N) b)
  linarith only [hmul,hh hN,mul_le_mul_of_nonneg_left hw hA.le,
    mul_le_mul_of_nonneg_left (hsmall.trans hCA) hA.le]

#print axioms mertens_cost_at_a_zero
#print axioms eventually_large_mertens_abel_cost
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
