import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerBoundaryPositivity
import GaloisForLFunctions.RHTower.ZeroFreeRegionFromFour
import GaloisForLFunctions.RHTower.XiHorizontalSlopeNearOne

/-! A classical zero-free region follows from the positive coefficients of
the actual Mayer boundary slope. Only the pole and zero-resolvent estimates
for the zeta logarithmic derivative enter the analytic bounds. -/

open Complex Set ArithmeticFunction
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerBoundaryPositivity
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryZeroFree

private theorem real_logDeriv_nonpos {u : ℝ} (hu : 1 < u) :
    (logDeriv riemannZeta (u : ℂ)).re ≤ 0 := by
  have h := _root_.RHTower.DeBruijn.re_neg_logDeriv_riemannZeta_real_eq_tsum hu
  rw [_root_.RHTower.Sieve.neg_div_re_eq_neg_logDeriv_re] at h
  have hn : 0 ≤ ∑' n : ℕ, vonMangoldt n/(n : ℝ)^u :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) u)
  linarith only [h,hn]

private theorem norm_shift_logDeriv_le {σ t : ℝ} (hσ : 1 < σ) :
    ‖logDeriv riemannZeta ((σ : ℂ)+(t : ℂ)*I+1)‖ ≤ 3 := by
  have hp : 0 < σ := zero_lt_one.trans hσ
  have h := _root_.RHTower.DeBruijn.norm_logDeriv_riemannZeta_le_inv_sub_one_add_two
    (σ := σ+1) (by linarith only [hσ]) t
  have he : ((σ+1 : ℝ) : ℂ)+(t : ℂ)*I=(σ : ℂ)+(t : ℂ)*I+1 := by push_cast; ring
  rw [he,add_sub_cancel_right] at h
  have hi : 1/σ ≤ 1 := (div_le_iff₀ hp).mpr (by linarith only [hσ])
  linarith only [h,hi]

/-- The source slope has the same real pole bound, since its correction is nonpositive. -/
theorem boundarySlope_real_le {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (boundarySlope (σ : ℂ)).re ≤ 1/(σ-1)+1 := by
  rw [boundarySlope_eq (by simpa using hσ),Complex.add_re,Complex.neg_re]
  have h := _root_.RHTower.neg_re_logDeriv_riemannZeta_real_le hσ hσ2
  rw [_root_.RHTower.Sieve.neg_div_re_eq_neg_logDeriv_re] at h
  have hshift := real_logDeriv_nonpos (u := σ+1) (by linarith only [hσ])
  rw [Complex.ofReal_add,Complex.ofReal_one] at hshift
  linarith only [h,hshift]

/-- A uniform bound for the denominator correction transfers the vertical Landau bound. -/
theorem boundarySlope_vertical_le {σ t : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ t) :
    (boundarySlope ((σ : ℂ)+(t : ℂ)*I)).re ≤ Real.log t/2+7/2 := by
  rw [boundarySlope_eq (by simpa using hσ),Complex.add_re,Complex.neg_re]
  have h := _root_.RHTower.neg_re_logDeriv_riemannZeta_le_half hσ hσ2 ht
  have hshift := (Complex.re_le_norm _).trans (norm_shift_logDeriv_le (t := t) hσ)
  linarith only [h,hshift]

/-- Retaining one actual zeta zero in the source slope gives its reciprocal distance. -/
theorem boundarySlope_zero_le {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (q : _root_.RHTower.XiZeroCopy) (hγ : 4 ≤ (q.1 : ℂ).im) :
    (boundarySlope ((σ : ℂ)+((q.1 : ℂ).im : ℂ)*I)).re ≤
      Real.log (q.1 : ℂ).im/2+7/2-1/(σ-(q.1 : ℂ).re) := by
  have hβ := _root_.RHTower.xiZeroCopy_re_lt_one q
  have hp : 0 < σ-(q.1 : ℂ).re := by linarith only [hσ,hβ]
  have h := _root_.RHTower.neg_re_logDeriv_riemannZeta_le_half_sub hσ hσ2 hγ q
  have he : Complex.normSq (((σ : ℂ)+((q.1 : ℂ).im : ℂ)*I)-(q.1 : ℂ))=
      (σ-(q.1 : ℂ).re)^2 := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im]
    ring
  have hd : (σ-(q.1 : ℂ).re)/(σ-(q.1 : ℂ).re)^2=1/(σ-(q.1 : ℂ).re) := by
    field_simp [hp.ne']
  rw [he,hd] at h
  rw [boundarySlope_eq (by simpa using hσ),Complex.add_re,Complex.neg_re]
  have hshift := (Complex.re_le_norm _).trans
    (norm_shift_logDeriv_le (t := (q.1 : ℂ).im) hσ)
  linarith only [h,hshift]

/-- The de la Vallee Poussin inequality obtained from actual transfer-boundary positivity. -/
theorem source_dlvp {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (q : _root_.RHTower.XiZeroCopy) (hγ : 4 ≤ (q.1 : ℂ).im) :
    4/(σ-(q.1 : ℂ).re) ≤ 3/(σ-1)+(5/2)*Real.log (q.1 : ℂ).im+41/2+Real.log 2/2 := by
  have hp : 0 < (q.1 : ℂ).im := by linarith only [hγ]
  have hpos := three_four_one (t := (q.1 : ℂ).im) hσ
  have hr := boundarySlope_real_le hσ hσ2
  have hm := boundarySlope_zero_le hσ hσ2 q hγ
  have hd := boundarySlope_vertical_le (t := 2*(q.1 : ℂ).im) hσ hσ2 (by linarith only [hγ])
  have hc : ((2*(q.1 : ℂ).im : ℝ) : ℂ)=(2*(q.1 : ℂ).im : ℂ) := by push_cast; rfl
  rw [hc] at hd
  rw [Real.log_mul (by norm_num) hp.ne'] at hd
  rw [show (4 : ℝ)/(σ-(q.1 : ℂ).re)=4*(1/(σ-(q.1 : ℂ).re)) by ring,
    show (3 : ℝ)/(σ-1)=3*(1/(σ-1)) by ring]
  linarith only [hpos,hr,hm,hd]

private theorem log_height_ge_one {t : ℝ} (ht : 4 ≤ t) : 1 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) ht
  have he : Real.log 4=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [he] at h
  linarith only [h,Real.log_two_gt_d9]

/-- An explicit logarithmic zero-free strip, proved using the actual boundary slope. -/
theorem xiZero_re_le {q : _root_.RHTower.XiZeroCopy} (hq : 4 ≤ (q.1 : ℂ).im) :
    (q.1 : ℂ).re ≤ 1-1/(1000*Real.log (q.1 : ℂ).im) := by
  let L : ℝ := Real.log (q.1 : ℂ).im
  have hL : 1 ≤ L := log_height_ge_one hq
  have hLp : 0 < L := zero_lt_one.trans_le hL
  let σ : ℝ := 1+1/(100*L)
  have hdpos : 0 < 1/(100*L) := by positivity
  have hσ : 1 < σ := by dsimp [σ]; linarith only [hdpos]
  have hdle : 1/(100*L) ≤ 1/100 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hL])
  have hσ2 : σ ≤ 2 := by dsimp [σ]; linarith only [hdle]
  have hβ := _root_.RHTower.xiZeroCopy_re_lt_one q
  have hδ : 0 < σ-(q.1 : ℂ).re := by linarith only [hσ,hβ]
  have hmain := source_dlvp hσ hσ2 q hq
  have hpole : 3/(σ-1)=300*L := by dsimp [σ]; field_simp [hLp.ne']; ring
  rw [hpole] at hmain
  change 4/(σ-(q.1 : ℂ).re) ≤ 300*L+(5/2)*L+41/2+Real.log 2/2 at hmain
  have hmain' : 4/(σ-(q.1 : ℂ).re) ≤ 325*L := by
    linarith only [hmain,hL,Real.log_two_lt_d9]
  have hprod : 4 ≤ (325*L)*(σ-(q.1 : ℂ).re) := (div_le_iff₀ hδ).mp hmain'
  by_contra hc
  have hb : 1-1/(1000*L) < (q.1 : ℂ).re := not_le.mp hc
  have he : 1/(100*L)+1/(1000*L)=(11/1000)/L := by field_simp; ring
  have hsmall : σ-(q.1 : ℂ).re < (11/1000)/L := by
    rw [← he]
    dsimp [σ]
    linarith only [hb]
  have hsmall' := (lt_div_iff₀ hLp).mp hsmall
  nlinarith only [hprod,hsmall']

/-- The classical strip follows for zeta itself, with either sign of the ordinate. -/
theorem zeta_ne_zero {β γ : ℝ} (hγ : 4 ≤ |γ|)
    (hβ : 1-1/(1000*Real.log |γ|) < β) :
    riemannZeta ((β : ℂ)+(γ : ℂ)*I) ≠ 0 := by
  intro hz
  let s : ℂ := (β : ℂ)+(γ : ℂ)*I
  have hsre : s.re=β := by simp [s]
  have hsim : s.im=γ := by simp [s]
  have hL := log_height_ge_one hγ
  have hsmall : 1/(1000*Real.log |γ|) ≤ 1/1000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hL])
  have hβ0 : 0 < β := by linarith only [hβ,hsmall]
  have hs1 : s ≠ 1 := by
    intro he
    have hg : γ=0 := by rw [← hsim,he]; simp
    rw [hg] at hγ
    norm_num at hγ
  have hx : _root_.RHTower.xi s=0 :=
    (_root_.RHTower.xi_eq_zero_iff (by rw [hsre]; exact hβ0) hs1).mpr hz
  let ρ : _root_.RHTower.XiDivisorSupport := ⟨s,_root_.RHTower.mem_xi_divisor_support_of_eq_zero hx⟩
  have hp := _root_.RHTower.xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor _root_.RHTower.xi Set.univ) (ρ : ℂ)) := by omega
  let q : _root_.RHTower.XiZeroCopy := ⟨ρ,⟨0,hn⟩⟩
  have hq : (q.1 : ℂ)=s := rfl
  rcases le_or_gt 0 γ with hg | hg
  · have hg4 : 4 ≤ γ := by rwa [abs_of_nonneg hg] at hγ
    have h := xiZero_re_le (q := q) (by rw [hq,hsim]; exact hg4)
    rw [hq,hsre,hsim] at h
    rw [abs_of_nonneg hg] at hβ
    linarith only [h,hβ]
  · have hg4 : 4 ≤ -γ := by rwa [abs_of_neg hg] at hγ
    have hc : ((_root_.RHTower.xiZeroCopyConjEquiv q).1 : ℂ)=(starRingEnd ℂ) (q.1 : ℂ) := rfl
    have h := xiZero_re_le (q := _root_.RHTower.xiZeroCopyConjEquiv q)
      (by rw [hc,hq,Complex.conj_im,hsim]; exact hg4)
    rw [hc,hq,Complex.conj_re,Complex.conj_im,hsre,hsim] at h
    rw [abs_of_neg hg] at hβ
    linarith only [h,hβ]

/-- The actual scattering inverse has no pole in the resulting part of the strip. -/
theorem positiveBoundary_order_zero {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1)
    (ht : 4 ≤ |w.im|) (hr : 1-1/(1000*Real.log |w.im|) < w.re) :
    meromorphicOrderAt MayerBoundaryResolvent.positiveBoundary w=0 := by
  have hz : riemannZeta w ≠ 0 := by
    simpa only [Complex.re_add_im] using (zeta_ne_zero ht hr)
  have hw1 : w ≠ 1 := by intro he; norm_num [he] at h1
  have ha := GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta hw1
  rw [MayerBoundaryResolvent.positiveBoundary_order h0 h1,
    analyticOrderNatAt,ha.analyticOrderAt_eq_zero.mpr hz]
  norm_num

#print axioms positiveBoundary_order_zero

#print axioms boundarySlope_real_le
#print axioms boundarySlope_vertical_le
#print axioms boundarySlope_zero_le
#print axioms source_dlvp
#print axioms xiZero_re_le
#print axioms zeta_ne_zero
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundaryZeroFree
