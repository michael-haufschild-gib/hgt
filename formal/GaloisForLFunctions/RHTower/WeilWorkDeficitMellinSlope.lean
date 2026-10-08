import GaloisForLFunctions.RHTower.WeilWorkDeficitMellinAmplitude
import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog

/-!
# First derivative of the actual demodulated Mellin transform

The exact Gamma product supplies its derivative on `Re(s)=4`. The leading
digamma phase cancels at the amplitude saddle, giving a common scaled
Gaussian bound in the bulk. Higher derivatives and global tails remain
separate obligations; no spectral-deficit conclusion is asserted here.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open RHTower.WeilWorkDeficitAmplitude RHTower.WeilWorkDeficitMellin RHTower.WeilWorkDeficitPrimeKernel
noncomputable section
namespace RHTower.WeilWorkDeficitSlope

private def symbol (k : ℕ) (s : ℂ) : ℂ :=
  (-1:ℂ)^k * (s-1/2)^(2*k) * s^2 * (s-1)^2 *
    (Real.pi:ℂ)^(-s) * (Complex.Gamma (s/2))^2 / 4

/-- Exact derivative multiplier after removal of the saddle's linear phase. -/
def slope (k : ℕ) (T t : ℝ) : ℂ :=
  I * ((2*k:ℂ)/(7/2+(t:ℂ)*I) + 2/(4+(t:ℂ)*I) + 2/(3+(t:ℂ)*I) +
    Complex.digamma (2+(t:ℂ)*I/2) - (Real.log Real.pi:ℂ) - (Real.log (T/(2*Real.pi)):ℂ))

/-- Literal product-kernel Mellin integral with its saddle's linear phase removed. -/
def demodulatedMellin (k : ℕ) (t : ℝ) : ℂ :=
  (∫ x in Ioi (0:ℝ), (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ)) *
    Complex.exp (-I*(t:ℂ)*(Real.log (saddleHeight k/(2*Real.pi)):ℂ))

private theorem height_four (k : ℕ) : 4 ≤ saddleHeight k := by
  unfold saddleHeight
  rw [le_div_iff₀ (by positivity : (0:ℝ)<Real.pi/2)]
  nlinarith [Real.pi_lt_d2, (Nat.cast_nonneg k : (0:ℝ)≤k)]

private theorem height_eq (k : ℕ) : (Real.pi/2)*saddleHeight k = 2*(k:ℝ)+7 := by
  unfold saddleHeight
  field_simp

private theorem height_norm (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ ‖(σ:ℂ)+(t:ℂ)*I‖ := by
  simpa [abs_of_nonneg ht] using Complex.abs_im_le_norm ((σ:ℂ)+(t:ℂ)*I)

private theorem near_inverse (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖I/((σ:ℂ)+(t:ℂ)*I)-(1/t:ℝ)‖ ≤ |σ|/t^2 := by
  have hz : (σ:ℂ)+(t:ℂ)*I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hid : I/((σ:ℂ)+(t:ℂ)*I)-(1/t:ℝ) =
      -(σ:ℂ)/((t:ℂ)*((σ:ℂ)+(t:ℂ)*I)) := by
    push_cast
    rw [div_sub_div _ _ hz htC]
    congr 1 <;> ring
  rw [hid, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos ht)
  nlinarith [height_norm σ ht.le]

private theorem log_ratio {T t : ℝ} (hT : 0 < T) (ht : T/2 ≤ t) :
    |Real.log (t/T)| ≤ 2*|t-T|/T := by
  have ht0 : 0 < t := by linarith
  have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 hT)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hT ht0)
  rw [Real.log_div hT.ne' ht0.ne', Real.log_div ht0.ne' hT.ne'] at *
  rw [abs_le]
  constructor
  · have hle : T/t-1 ≤ 2*|t-T|/T := by
      rw [div_sub_one ht0.ne', div_le_div_iff₀ ht0 hT]
      have h := neg_le_abs (t-T)
      have ha := abs_nonneg (t-T)
      nlinarith
    linarith
  · have hle : t/T-1 ≤ 2*|t-T|/T := by
      rw [div_sub_one hT.ne', div_le_div_iff₀ hT hT]
      nlinarith [le_abs_self (t-T), abs_nonneg (t-T)]
    linarith

private theorem slope_decomp (k : ℕ) {T t : ℝ} (hT : 0 < T) (ht : 0 < t) :
    slope k T t =
      ((2*(k:ℝ)/t-Real.pi/2:ℝ):ℂ) + I*(Real.log (t/T):ℂ) +
      ((2*k:ℂ)*(I/(7/2+(t:ℂ)*I)-(1/t:ℝ)) +
        2*I/(4+(t:ℂ)*I)+2*I/(3+(t:ℂ)*I) +
        I*(Complex.digamma (2+(t:ℂ)*I/2)-vertLog (t/2))) := by
  have hl : Real.log (t/2) - Real.log Real.pi - Real.log (T/(2*Real.pi)) =
      Real.log (t/T) := by
    rw [Real.log_div ht.ne' (by norm_num),
      Real.log_div hT.ne' (by positivity), Real.log_mul (by norm_num) Real.pi_pos.ne',
      Real.log_div ht.ne' hT.ne']
    ring
  unfold slope vertLog
  rw [← hl]
  push_cast
  ring_nf
  simp [Complex.I_sq]

private theorem slope_error (k : ℕ) {T t D : ℝ} (hT : 0 < T) (ht : 2 ≤ t)
    (hpsi : ‖Complex.digamma (2+(t:ℂ)*I/2)-vertLog (t/2)‖ ≤ 2*D/t)
    (hk : (k:ℝ) ≤ Real.pi/2*t) :
    ‖slope k T t‖ ≤ |2*(k:ℝ)/t-Real.pi/2| + |Real.log (t/T)| +
      (7*Real.pi/2+4+2*D)/t := by
  have ht0 : 0 < t := by linarith
  have hi : ‖I/(7/2+(t:ℂ)*I)-(1/t:ℝ)‖ ≤ (7/2)/t^2 := by
    convert near_inverse (7/2) ht0 using 1 <;> norm_num
  have hterm : ‖(2*k:ℂ)*(I/(7/2+(t:ℂ)*I)-(1/t:ℝ))‖ ≤ (7*Real.pi/2)/t := by
    rw [norm_mul]
    have hc : ‖(2*k:ℂ)‖ = 2*(k:ℝ) := by norm_num [norm_mul]
    rw [hc]
    calc _ ≤ (2*(k:ℝ)) * ((7/2)/t^2) := mul_le_mul_of_nonneg_left hi (by positivity)
         _ ≤ (7*Real.pi/2)/t := by
           rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos ht0) ht0]
           nlinarith [mul_le_mul_of_nonneg_right hk ht0.le]
  have hrat (σ : ℝ) : ‖2*I/((σ:ℂ)+(t:ℂ)*I)‖ ≤ 2/t := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one]
    norm_num only [Complex.norm_ofNat]
    exact div_le_div_of_nonneg_left (by norm_num) ht0 (height_norm σ ht0.le)
  rw [slope_decomp k hT ht0]
  calc _ ≤ ‖((2*(k:ℝ)/t-Real.pi/2:ℝ):ℂ)‖ + ‖I*(Real.log (t/T):ℂ)‖ +
      (‖(2*k:ℂ)*(I/(7/2+(t:ℂ)*I)-(1/t:ℝ))‖ +
        ‖2*I/(4+(t:ℂ)*I)‖+‖2*I/(3+(t:ℂ)*I)‖ +
        ‖I*(Complex.digamma (2+(t:ℂ)*I/2)-vertLog (t/2))‖) := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _)
            ((norm_add_le _ _).trans (add_le_add
              ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)))
       _ ≤ |2*(k:ℝ)/t-Real.pi/2| + |Real.log (t/T)| +
        ((7*Real.pi/2)/t + 2/t + 2/t + 2*D/t) := by
          simpa only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
            Real.norm_eq_abs, Complex.ofReal_ofNat] using
            add_le_add (le_refl (‖((2*(k:ℝ)/t-Real.pi/2:ℝ):ℂ)‖ + ‖I*(Real.log (t/T):ℂ)‖))
              (add_le_add (add_le_add (add_le_add hterm (hrat 4)) (hrat 3))
                (by simpa only [norm_mul, Complex.norm_I, one_mul] using hpsi))
       _ = _ := by ring

private theorem scaled_slope : ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (t : ℝ),
    saddleHeight k/2 ≤ t → t ≤ 2*saddleHeight k →
      Real.sqrt (saddleHeight k)*‖slope k (saddleHeight k) t‖ ≤
        C*(1+|t-saddleHeight k|/Real.sqrt (saddleHeight k)) := by
  obtain ⟨D,hD,hpsi⟩ := exists_uniform_bound_digamma_sub_vertLog (M:=2) (by norm_num)
  let R : ℝ := 7*Real.pi/2+11+2*D
  let C : ℝ := Real.pi+2+2*R
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun k t ht ht2 => ?_⟩
  have hT4 := height_four k
  have hT : 0 < saddleHeight k := by linarith
  have ht2' : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hh := height_eq k
  have hk : (k:ℝ) ≤ Real.pi/2*t := by nlinarith [Real.pi_pos]
  have hps : ‖Complex.digamma (2+(t:ℂ)*I/2)-vertLog (t/2)‖ ≤ 2*D/t := by
    convert hpsi 2 (t/2) (by norm_num) le_rfl (by linarith) using 1 <;> push_cast <;> ring
  have hs := slope_error k hT ht2' hps hk
  have hmain : |2*(k:ℝ)/t-Real.pi/2| ≤ (Real.pi/2)*|t-saddleHeight k|/t+7/t := by
    have he : 2*(k:ℝ)/t-Real.pi/2 =
        (Real.pi/2)*(saddleHeight k-t)/t-7/t := by
      field_simp
      nlinarith
    rw [he]
    have hn := abs_sub ((Real.pi/2)*(saddleHeight k-t)/t) (7/t)
    simpa [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos ht0, abs_sub_comm] using hn
  have hb : ‖slope k (saddleHeight k) t‖ ≤
      (Real.pi+2)*|t-saddleHeight k|/saddleHeight k+R/t := by
    have hm : (Real.pi/2)*|t-saddleHeight k|/t ≤
        Real.pi*|t-saddleHeight k|/saddleHeight k := by
      rw [div_le_div_iff₀ ht0 hT]
      nlinarith [mul_nonneg (by nlinarith [Real.pi_pos] : 0 ≤ Real.pi*(2*t-saddleHeight k))
        (abs_nonneg (t-saddleHeight k))]
    have hl := log_ratio hT ht
    calc _ ≤ ((Real.pi/2)*|t-saddleHeight k|/t+7/t) +
          (2*|t-saddleHeight k|/saddleHeight k) + (7*Real.pi/2+4+2*D)/t :=
            hs.trans (add_le_add (add_le_add hmain hl) le_rfl)
         _ ≤ (Real.pi*|t-saddleHeight k|/saddleHeight k+7/t) +
          (2*|t-saddleHeight k|/saddleHeight k) + (7*Real.pi/2+4+2*D)/t := by
            linarith only [hm]
         _ = _ := by dsimp [R]; ring
  have hsq := Real.sq_sqrt hT.le
  have hsqrt : 0 < Real.sqrt (saddleHeight k) := Real.sqrt_pos.2 hT
  have hsqrt1 : 1 ≤ Real.sqrt (saddleHeight k) := by nlinarith
  have htbound : Real.sqrt (saddleHeight k)/t ≤ 2 := by
    rw [div_le_iff₀ ht0]
    nlinarith
  calc _ ≤ Real.sqrt (saddleHeight k) *
        ((Real.pi+2)*|t-saddleHeight k|/saddleHeight k+R/t) :=
          mul_le_mul_of_nonneg_left hb hsqrt.le
       _ = (Real.pi+2)*(|t-saddleHeight k|/Real.sqrt (saddleHeight k)) +
          R*(Real.sqrt (saddleHeight k)/t) := by
            field_simp
            rw [hsq]
       _ ≤ (Real.pi+2)*(|t-saddleHeight k|/Real.sqrt (saddleHeight k)) + 2*R := by
         nlinarith [mul_le_mul_of_nonneg_left htbound hR]
       _ ≤ C*(1+|t-saddleHeight k|/Real.sqrt (saddleHeight k)) := by
         dsimp [C]
         have hx := mul_nonneg hR (div_nonneg (abs_nonneg (t-saddleHeight k)) hsqrt.le)
         nlinarith only [hx, Real.pi_pos]

private theorem pow_deriv {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hn : f t ≠ 0) (n : ℕ) :
    HasDerivAt (fun t => f t ^ n) (f t ^ n * ((n:ℂ)*f'/f t)) t := by
  apply (hf.pow n).congr_deriv
  cases n with
  | zero => simp
  | succ n => simp only [Nat.succ_sub_one, pow_succ]; field_simp [hn]

private theorem symbol_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => symbol k (4+(t:ℂ)*I))
      (symbol k (4+(t:ℂ)*I) *
        (I*((2*k:ℂ)/(7/2+(t:ℂ)*I)+2/(4+(t:ℂ)*I)+2/(3+(t:ℂ)*I)+
          Complex.digamma (2+(t:ℂ)*I/2)-(Real.log Real.pi:ℂ)))) t := by
  let s : ℂ := 4+(t:ℂ)*I
  have hs : s.re = 4 := by simp [s]
  have hn (c : ℝ) (hc : c ≠ 4) : s-(c:ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hs] at this
    exact hc (by linarith)
  have hpath : HasDerivAt (fun t : ℝ => 4+(t:ℂ)*I) I t := by
    simpa using ((Complex.hasDerivAt_ofReal t).mul_const I).const_add 4
  have hg0 : ∀ m : ℕ, s/2 ≠ -(m:ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp [hs] at this
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hg : HasDerivAt Complex.Gamma
      (Complex.Gamma (s/2)*Complex.digamma (s/2)) (s/2) := by
    apply (Complex.differentiableAt_Gamma (s/2) hg0).hasDerivAt.congr_deriv
    rw [Complex.digamma_def, logDeriv_apply]
    field_simp [Complex.Gamma_ne_zero hg0]
  have hhalf := hg.comp t (hpath.div_const 2)
  have hpow := pow_deriv (hpath.sub_const (1/2))
    (by simpa using hn (1/2) (by norm_num)) (2*k)
  have hsq := pow_deriv hpath (by simpa using hn 0 (by norm_num)) 2
  have hsq1 := pow_deriv (hpath.sub_const 1) (hn 1 (by norm_num)) 2
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hpder : HasDerivAt (fun t : ℝ => (Real.pi:ℂ)^(-(4+(t:ℂ)*I)))
      ((Real.pi:ℂ)^(-s) * (-I*(Real.log Real.pi:ℂ))) t := by
    simp_rw [Complex.cpow_def_of_ne_zero hp, ← Complex.ofReal_log Real.pi_pos.le]
    apply (hpath.neg.const_mul (Real.log Real.pi:ℂ)).cexp.congr_deriv
    dsimp [s]
    ring
  have hall := (((((hpow.const_mul ((-1:ℂ)^k)).mul hsq).mul hsq1).mul hpder).mul
    (hhalf.pow 2)).div_const 4
  apply hall.congr_deriv
  dsimp [symbol, s]
  have hdelta : (4:ℂ)+(t:ℂ)*I-1/2 = 7/2+(t:ℂ)*I := by ring
  have hminus : (4:ℂ)+(t:ℂ)*I-1 = 3+(t:ℂ)*I := by ring
  have hhalf' : ((4:ℂ)+(t:ℂ)*I)/2 = 2+(t:ℂ)*I/2 := by ring
  simp only [hdelta,hminus,hhalf',Nat.cast_mul,Nat.cast_ofNat]
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub]
  ring

/-- Exact differentiation of the literal Mellin integral, with no assumed symbol identity. -/
theorem hasDerivAt_demodulatedMellin (k : ℕ) (t : ℝ) :
    HasDerivAt (demodulatedMellin k)
      (demodulatedMellin k t * slope k (saddleHeight k) t) t := by
  have heq : demodulatedMellin k = fun t : ℝ => symbol k (4+(t:ℂ)*I) *
      Complex.exp (-I*(t:ℂ)*(Real.log (saddleHeight k/(2*Real.pi)):ℂ)) := by
    funext t
    unfold demodulatedMellin
    rw [productKernel_mellin k (by simp : 0 < ((4:ℂ)+(t:ℂ)*I).re)]
    rfl
  have hex := (((Complex.hasDerivAt_ofReal t).const_mul (-I)).mul_const
    (Real.log (saddleHeight k/(2*Real.pi)):ℂ)).cexp
  rw [heq]
  apply ((symbol_deriv k t).mul hex).congr_deriv
  unfold slope
  ring

/-- One scaled first-derivative Gaussian bound, uniform in every order `k`. -/
theorem exists_demodulatedMellin_deriv_bulk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (t : ℝ), saddleHeight k/2 ≤ t → t ≤ 2*saddleHeight k →
      Real.sqrt (saddleHeight k)*‖deriv (demodulatedMellin k) t‖ ≤
        C*saddleMass k*(1+|t-saddleHeight k|/Real.sqrt (saddleHeight k)) *
          Real.exp (-(Real.pi/2)*(t-saddleHeight k)^2/(9*saddleHeight k)) := by
  obtain ⟨A,hA,hamp⟩ := exists_productKernel_mellin_bulk_bound
  obtain ⟨C,hC,hslope⟩ := scaled_slope
  refine ⟨A*C,mul_pos hA hC,fun k t ht ht2 => ?_⟩
  have hn : ‖demodulatedMellin k t‖ =
      ‖∫ x in Ioi (0:ℝ), (x:ℂ)^((4+(t:ℂ)*I)-1)*(productKernel k x:ℂ)‖ := by
    simp [demodulatedMellin, Complex.norm_exp]
  rw [(hasDerivAt_demodulatedMellin k t).deriv, norm_mul]
  calc _ = ‖demodulatedMellin k t‖ *
      (Real.sqrt (saddleHeight k)*‖slope k (saddleHeight k) t‖) := by ring
       _ ≤ (A*saddleMass k*Real.exp (-(Real.pi/2)*(t-saddleHeight k)^2/(9*saddleHeight k)))*
          (C*(1+|t-saddleHeight k|/Real.sqrt (saddleHeight k))) :=
            mul_le_mul (by simpa only [hn] using hamp k t ht ht2) (hslope k t ht ht2)
              (by positivity) (by
                have hh : 0 ≤ saddleHeight k := le_trans (by norm_num) (height_four k)
                unfold saddleMass
                positivity)
       _ = _ := by ring

end RHTower.WeilWorkDeficitSlope
