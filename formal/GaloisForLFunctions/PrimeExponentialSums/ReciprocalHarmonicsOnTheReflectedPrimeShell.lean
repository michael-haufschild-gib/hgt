import GaloisForLFunctions.PrimeExponentialSums.ReciprocalVaughanOnPowerRanges
import GaloisForLFunctions.PrimeExponentialSums.FiniteHarmonicsOfThePrimeSawtooth
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# Low reciprocal harmonics on the reflected prime shell

At target power t the block extends to the two-branch exponent a(t).
The harmonic cutoff is x^(2(a-t)). The lower end of the reciprocal
frequency interval controls the inverse-frequency term in Vaughan's estimate.
-/

noncomputable section
open Filter Finset ArithmeticFunction RHTower.Sieve
namespace GaloisForLFunctions.PrimeExponentialSums

/-- Uniform Mangoldt estimate on all partial dyadic blocks in the shell.
The frequency interval includes the first x^(2(a-t)) harmonics of each
of the three reflected endpoints. -/
theorem reflected_shell_reciprocal_harmonics {t ε : ℝ} (ht : 1/2 ≤ t) (ht1 : t < 1)
    (he : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ {A B : ℕ} {S : ℝ}, A ≤ B → B ≤ 2*A →
      x^t ≤ A → (A:ℝ) ≤ x^(reflectedPrimeShellExponent t) →
      x ≤ S → S ≤ 8*Real.pi*x^(1+2*(reflectedPrimeShellExponent t-t)) →
      ‖∑ j ∈ Ico A B,(vonMangoldt j : ℂ)*Complex.exp (((S/(j:ℝ):ℝ):ℂ)*Complex.I)‖ ≤
        x^(t+ε) := by
  let a := reflectedPrimeShellExponent t
  let b := 2*(a-t)
  let u := 1/2+5*a/2-3*t
  let v := 2*(a-t)
  obtain ⟨hta,ha,hu,hv,huv,hcur,hexp⟩ := reflected_prime_shell_exponents ht ht1
  change t < a at hta
  change a < 1 at ha
  change 0 < u at hu
  change 0 < v at hv
  change u+v < t at huv
  change 1+b+3*(u+v) < 4*t at hcur
  change reciprocalVaughanExponent a 1 (1+b) u v (u+v) ≤ t at hexp
  let η := min ((t-u-v)/4) (min ((4*t-1-b-3*(u+v))/8) (min ((1-a)/2) (ε/5)))
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (by linarith only [huv]) (lt_min (by linarith only [hcur])
      (lt_min (by linarith only [ha]) (by linarith only [he])))
  have hη1 : η ≤ (t-u-v)/4 := min_le_left _ _
  have hη2 : η ≤ (4*t-1-b-3*(u+v))/8 := (min_le_right _ _).trans (min_le_left _ _)
  have hη3 : η ≤ (1-a)/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη4 : η ≤ ε/5 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hpert : reciprocalVaughanExponent (a+η) 1 (1+b+η) u v (u+v+2*η) ≤ t+2*η := by
    simp only [reciprocalVaughanExponent,max_le_iff] at hexp ⊢
    obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hexp
    repeat' apply And.intro
    all_goals linarith only [h₁,h₂,h₃,h₄,h₅,hη]
  obtain ⟨D,hD,henv⟩ := reciprocal_vaughan_envelope
  have hlarge : ∀ᶠ x : ℝ in atTop, max ((10:ℝ)^27) (8*Real.pi) ≤ x^η := by
    simpa only [pow_zero,mul_one] using eventually_const_mul_one_add_log_pow_le_rpow hη
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<10^27) (le_max_left _ _)) 0
  have hlog := eventually_const_mul_one_add_log_pow_le_rpow hη (show 0<5*D by positivity) 4
  filter_upwards [eventually_ge_atTop (1:ℝ),hlarge,hlog] with x hx hconst hlog
  intro A B S hAB hd hAlow hAhi hSlo hShi
  let P (z : ℝ) := x^z
  have hx0 := zero_lt_one.trans_le hx
  have pos (z : ℝ) : 0 < P z := Real.rpow_pos_of_pos hx0 _
  have mono {z w : ℝ} (h : z ≤ w) : P z ≤ P w := Real.rpow_le_rpow_of_exponent_le hx h
  have mult (z w : ℝ) : P z*P w=P (z+w) := (Real.rpow_add hx0 _ _).symm
  have one : P 1=x := Real.rpow_one _
  have hbig := (le_max_left _ _).trans hconst
  have hpi := (le_max_right _ _).trans hconst
  have htwo : 2 < P η := (by norm_num : (2:ℝ)<10^27).trans_le hbig
  have twice (z : ℝ) : 2*P z ≤ P (z+η) := by
    calc _ ≤ P η*P z := mul_le_mul_of_nonneg_right htwo.le (pos z).le
         _ = _ := by rw [mult,add_comm]
  have upper (z : ℝ) (hz : 0 ≤ z) : (⌈P z⌉₊:ℝ) < P (z+η) := by
    have hh := Real.one_le_rpow hx hz
    apply (Nat.ceil_lt_add_one (pos z).le).trans_le
    exact (show P z+1 ≤ 2*P z by dsimp only [P]; linarith only [hh]).trans (twice z)
  let U := ⌈P u⌉₊
  let V := ⌈P v⌉₊
  have hU : (U:ℝ) < P (u+η) := upper u hu.le
  have hV : (V:ℝ) < P (v+η) := upper v hv.le
  have hUV : ((U*V:ℕ):ℝ) ≤ P (u+v+2*η) := by
    rw [Nat.cast_mul,show u+v+2*η=(u+η)+(v+η) by ring,←mult]
    exact mul_le_mul hU.le hV.le (Nat.cast_nonneg _) (pos _).le
  have hA1 : 1 ≤ A := by
    exact_mod_cast (Real.one_le_rpow hx (by linarith only [ht] : 0 ≤ t)).trans hAlow
  have hB : (B:ℝ) ≤ P (a+η) := by
    have hb : (B:ℝ) ≤ 2*(A:ℝ) := by exact_mod_cast hd
    exact hb.trans ((mul_le_mul_of_nonneg_left hAhi (by norm_num)).trans (twice a))
  have hS : S ≤ P (1+b+η) := by
    change S ≤ 8*Real.pi*P (1+b) at hShi
    calc S ≤ P η*P (1+b) := hShi.trans (mul_le_mul_of_nonneg_right hpi (pos _).le)
         _ = _ := by rw [mult,add_comm η]
  have hSm : 0 < S := hx0.trans_le hSlo
  have huA : U < A := by
    exact_mod_cast hU.trans_le ((mono (by linarith only [hη1,hη,hv] : u+η ≤ t)).trans hAlow)
  have huvA : U*V ≤ A := by
    exact_mod_cast hUV.trans ((mono (by linarith only [hη1,hη] : u+v+2*η ≤ t)).trans hAlow)
  have hcurve : S*((U*V:ℕ):ℝ)^3 ≤ 72*Real.pi*(A:ℝ)^4 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (U*V)) hUV 3
    have pp (z : ℝ) (k : ℕ) : (P z)^k=P (z*k) := by
      change (x^z)^k=x^(z*(k:ℝ))
      rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le]
    rw [pp] at hh
    have hr := mul_le_mul hS hh (by positivity) (pos _).le
    rw [mult] at hr
    have hl := pow_le_pow_left₀ (pos t).le hAlow 4
    rw [pp] at hl
    apply hr.trans ((mono ?_).trans (hl.trans ?_))
    · push_cast; linarith only [hη2,hη]
    · exact le_mul_of_one_le_left (by positivity) (by linarith only [Real.pi_gt_three])
  have hscale : (10:ℝ)^27*A ≤ S := by
    calc _ ≤ P η*P a := mul_le_mul hbig hAhi (Nat.cast_nonneg _) (pos _).le
         _ ≤ P 1 := by rw [mult]; exact mono (by linarith only [hη3,ha])
         _ ≤ S := one.le.trans hSlo
  have henv' := henv hSm hA1 hAB hd ((Nat.one_le_ceil_iff).mpr (pos u))
    ((Nat.one_le_ceil_iff).mpr (pos v)) huA huvA hcurve hscale
  have hacc := reciprocal_vaughan_power_account hD.le hx hAB hB (one.le.trans hSlo) hS
    (show P u ≤ (U:ℝ) from Nat.le_ceil _) (show P v ≤ (V:ℝ) from Nat.le_ceil _) hUV
  have hBx : (B:ℝ) ≤ x := hB.trans ((mono (by linarith only [hη3,ha] : a+η ≤ 1)).trans_eq one)
  have hLB := Real.log_le_log (by exact_mod_cast hA1.trans hAB : (0:ℝ)<B) hBx
  have hLB0 := Real.log_natCast_nonneg B
  have hlogs : 5*D*(1+Real.log B)^4 ≤ P η :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hLB0]) (add_le_add_right hLB 1) 4)
      (show 0 ≤ 5*D by positivity)).trans hlog
  apply henv'.trans (hacc.trans ?_)
  calc _ ≤ P η*P (t+2*η) := mul_le_mul hlogs (mono hpert) (pos _).le (pos _).le
       _ ≤ _ := by rw [mult]; exact mono (by linarith only [hη4,hη])

#print axioms reflected_shell_reciprocal_harmonics

private theorem real_weight_fourier_neg (s : Finset ℕ) (y w : ℕ → ℝ) (h : ℤ) :
    (∑ j ∈ s,(w j:ℂ)*fourier (-h) (y j : UnitAddCircle)) =
      star (∑ j ∈ s,(w j:ℂ)*fourier h (y j : UnitAddCircle)) := by
  simp only [fourier_neg,star_sum,star_mul]
  exact sum_congr rfl fun j _ => by simp [mul_comm]

/-- The finite harmonic estimate applies to the actual Mangoldt measure,
including reciprocity phases lying on a jump of the fractional part. -/
theorem reflected_shell_mangoldt_saw {t ε : ℝ} (ht : 1/2 ≤ t) (ht1 : t < 1)
    (he : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ {A B : ℕ} {k : ℝ}, A ≤ B → B ≤ 2*A →
      x^t ≤ A → (A:ℝ) ≤ x^(reflectedPrimeShellExponent t) → 2 ≤ k → k ≤ 4 →
      |∑ j ∈ Ico A B,vonMangoldt j*(Int.fract (k*x/j)-1/2)| ≤ x^(t+ε) := by
  let a := reflectedPrimeShellExponent t
  let b := 2*(a-t)
  obtain ⟨hta,ha,_⟩ := reflected_prime_shell_exponents ht ht1
  change t < a at hta
  change a < 1 at ha
  have hb : 0 < b := by dsimp only [b]; linarith only [hta]
  have hb1 : b ≤ 1 := by dsimp only [b]; linarith only [ha,ht]
  obtain ⟨C,hC,hsaw⟩ := sawtooth_from_finite_harmonics
  have he3 : 0 < ε/3 := by linarith only [he]
  have hlog := eventually_const_mul_one_add_log_pow_le_rpow he3 (show 0<43*(C+1) by linarith only [hC]) 1
  have htwo : ∀ᶠ x : ℝ in atTop, 2 ≤ x^b := by
    simpa only [pow_zero,mul_one] using eventually_const_mul_one_add_log_pow_le_rpow hb
      (by norm_num : (0:ℝ)<2) 0
  filter_upwards [eventually_ge_atTop (1:ℝ),reflected_shell_reciprocal_harmonics ht ht1 he3,
    htwo,hlog] with x hx hfreq htwo hlog
  intro A B k hAB hd hAl hAu hk hk'
  let P (z : ℝ) := x^z
  let H := ⌊P b⌋₊
  let δ := P (t-a)
  have hx0 := zero_lt_one.trans_le hx
  have pos (z : ℝ) : 0 < P z := Real.rpow_pos_of_pos hx0 _
  have mult (z w : ℝ) : P z*P w=P (z+w) := (Real.rpow_add hx0 _ _).symm
  have mono {z w : ℝ} (h : z ≤ w) : P z ≤ P w := Real.rpow_le_rpow_of_exponent_le hx h
  have hHle : (H:ℝ) ≤ P b := Nat.floor_le (pos b).le
  have hHup : P b < (H:ℝ)+1 := Nat.lt_floor_add_one _
  have hHh : P b/2 ≤ H := by change 2 ≤ P b at htwo; linarith only [htwo,hHup]
  have hH0 : 0 < H := by exact_mod_cast (half_pos (pos b)).trans_le hHh
  have hxH : (H:ℝ) ≤ x := hHle.trans ((mono hb1).trans_eq (Real.rpow_one x))
  have hHlog := Real.log_le_log (Nat.cast_pos.mpr hH0) hxH
  have heA : 1 ≤ A := by exact_mod_cast (Real.one_le_rpow hx (by linarith only [ht] : 0 ≤ t)).trans hAl
  have hmass : (∑ j ∈ Ico A B,vonMangoldt j) ≤ 14*P a := by
    calc _ ≤ ∑ j ∈ Icc 1 B,vonMangoldt j := by
               apply sum_le_sum_of_subset_of_nonneg
               · exact fun j hj => mem_Icc.mpr ⟨heA.trans (mem_Ico.mp hj).1,(mem_Ico.mp hj).2.le⟩
               · exact fun _ _ _ => vonMangoldt_nonneg
         _ ≤ 7*B := _root_.RHTower.chebyshevPsi_le_seven B
         _ ≤ _ := by
               have h : (B:ℝ) ≤ 2*(A:ℝ) := by exact_mod_cast hd
               change (A:ℝ) ≤ P a at hAu
               linarith only [h,hAu]
  let G (h : ℤ) := ∑ j ∈ Ico A B,(vonMangoldt j:ℂ)*fourier h ((k*x/(j:ℝ):ℝ) : UnitAddCircle)
  have hpos {h : ℤ} (hh : 0 < h) (hhH : h.natAbs ≤ H) : ‖G h‖ ≤ P (t+ε/3) := by
    have hhr : (1:ℝ) ≤ h := by exact_mod_cast hh
    have hcast : (h:ℝ)=(h.natAbs:ℝ) := by
      rw [Nat.cast_natAbs,Int.cast_abs,abs_of_nonneg (Int.cast_nonneg.mpr hh.le)]
    have hhup : (h:ℝ) ≤ P b := hcast.le.trans ((Nat.cast_le.mpr hhH).trans hHle)
    let S := 2*Real.pi*h*k*x
    have hcoef : 1 ≤ 2*Real.pi*h*k := by
      calc (1:ℝ) ≤ (2*Real.pi)*1*2 := by linarith only [Real.pi_gt_three]
           _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hhr (by positivity)) hk
             (by norm_num) (mul_nonneg (by positivity) (by linarith only [hhr]))
    have hlo : x ≤ S := le_mul_of_one_le_left hx0.le hcoef
    have hhi : S ≤ 8*Real.pi*x^(1+2*(reflectedPrimeShellExponent t-t)) := by
      have hθ := mul_le_mul (mul_le_mul_of_nonneg_left hhup (by positivity : 0 ≤ 2*Real.pi))
        hk' (by linarith only [hk] : 0 ≤ k) (mul_nonneg (by positivity) (pos b).le)
      apply (mul_le_mul_of_nonneg_right hθ hx0.le).trans_eq
      change 2*Real.pi*P b*4*x=8*Real.pi*P (1+b)
      rw [←mult,show P 1=x from Real.rpow_one x]; ring
    have hz := hfreq hAB hd hAl hAu hlo hhi
    have phase (j : ℕ) : fourier h ((k*x/(j:ℝ):ℝ) : UnitAddCircle)=
        Complex.exp (((S/(j:ℝ):ℝ):ℂ)*Complex.I) := by
      rw [fourier_coe_apply]
      congr 1
      dsimp only [S]; push_cast; ring
    simpa only [G, phase] using hz
  have hboth (h : ℤ) (hh : h ≠ 0) (hhH : h.natAbs ≤ H) : ‖G h‖ ≤ P (t+ε/3) := by
    rcases lt_or_gt_of_ne hh with hneg | hpos'
    · have hflip : G h=star (G (-h)) := by
        simpa only [G,neg_neg] using real_weight_fourier_neg (Ico A B)
          (fun j : ℕ => k*x/j) (fun j => vonMangoldt j) (-h)
      rw [hflip,norm_star]
      exact hpos (neg_pos.mpr hneg) (by simpa only [Int.natAbs_neg] using hhH)
    · exact hpos hpos' hhH
  have hbound := hsaw (Ico A B) (fun j : ℕ => k*x/j) (fun j => vonMangoldt j)
    (fun _ => vonMangoldt_nonneg) hH0 (pos (t-a)) (pos (t+ε/3)).le hmass hboth
  have hprec : δ*(14*P a)=14*P t := by
    dsimp only [δ]; rw [mul_left_comm,mult,sub_add_cancel]
  have hprod : P t*δ*P b=P a := by
    dsimp only [δ]; rw [mult,mult]; congr 1; dsimp only [b]; ring
  have htail : 14*P a/δ/H ≤ 28*P t := by
    rw [div_le_iff₀ (Nat.cast_pos.mpr hH0),div_le_iff₀ (pos (t-a))]
    calc 14*P a = 28*P t*(P b/2)*δ := by rw [←hprod]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_left hHh (by positivity)) (pos _).le
  have hpm : P t ≤ P (t+ε/3) := mono (by linarith only [he3])
  have hz := Real.log_nonneg hx
  have haz : P t ≤ (1+Real.log x)*P (t+ε/3) := hpm.trans
    (le_mul_of_one_le_left (pos _).le (by linarith only [hz]))
  have hmix := mul_le_mul_of_nonneg_left (add_le_add_right hHlog 1) (pos (t+ε/3)).le
  have hprice : δ*(14*P a)+P (t+ε/3)*(1+Real.log H)+(14*P a)/δ/H ≤
      43*((1+Real.log x)*P (t+ε/3)) := by
    rw [hprec]
    linarith only [hmix,htail,haz]
  have htotal : C*(δ*(14*P a)+P (t+ε/3)*(1+Real.log H)+(14*P a)/δ/H) ≤ P (t+ε) := by
    apply (mul_le_mul_of_nonneg_left hprice hC).trans
    calc _ ≤ (43*(C+1)*(1+Real.log x))*P (t+ε/3) := by
               have hh := mul_nonneg (by linarith only [hz] : 0 ≤ 1+Real.log x) (pos (t+ε/3)).le
               linarith only [hh]
         _ ≤ P (ε/3)*P (t+ε/3) := mul_le_mul_of_nonneg_right (by simpa only [pow_one] using hlog) (pos _).le
         _ ≤ _ := by rw [mult]; exact mono (by linarith only [he])
  have hfinal := hbound.trans htotal
  simpa only [HTGeometry.SmoothedSawtooth.saw,←Complex.ofReal_mul,←Complex.ofReal_sum,
    Complex.norm_real,Real.norm_eq_abs] using hfinal

#print axioms reflected_shell_mangoldt_saw

end GaloisForLFunctions.PrimeExponentialSums
