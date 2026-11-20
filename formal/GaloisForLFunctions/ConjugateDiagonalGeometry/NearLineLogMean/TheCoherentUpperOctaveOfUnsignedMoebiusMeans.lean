import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheEndpointScalesOfTheSmoothedMoebiusTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Coherence of the unsigned upper octave of the Möbius section

After removal of the Möbius signs, every frequency in (K,2K] lies
within log 2 of the carrier. A fixed interval of positive heights sees
at least a constant fraction of the total amplitude. This gives a
squarefree witness for the length threshold of the Dirichlet mean bound.
-/

noncomputable section
open Filter Topology MeasureTheory Finset ArithmeticFunction
open _root_.RHTower.Sieve
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private def mass (n : ℕ) := ((moebius n:ℤ):ℝ)^2/n
private def w (m n : ℕ) := mass n*logTailScale m n
private theorem mass_nonneg (n : ℕ) : 0 ≤ mass n := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

private def phase (x : ℝ) := Complex.exp ((x:ℂ)*Complex.I)
private theorem norm_phase (x : ℝ) : ‖phase x‖=1 := Complex.norm_exp_ofReal_mul_I x
private theorem phase_add (x y : ℝ) : phase (x+y)=phase x*phase y := by
  simp only [phase,Complex.ofReal_add,add_mul,Complex.exp_add]

/-- The critical squarefree amplitudes on (K,2K] after replacing each
Möbius coefficient by its absolute value. -/
def unsignedDyadicMoebius (m K : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ioc K (2*K), (w m n:ℂ)*phase (-t*Real.log n)

/-- The coefficients coincide term by term with the absolute critical
coefficients of the logarithmically filtered Möbius polynomial. -/
theorem unsignedDyadicMoebius_formula (m : ℕ) {K : ℕ} (hK : 2 ≤ K) (t : ℝ) :
    unsignedDyadicMoebius m K t = ∑ n ∈ Ioc K (2*K),
      (((((moebius n:ℤ):ℝ)^2*(n:ℝ)^(-(1/2:ℝ))*(Real.log 2/Real.log n)^m):ℝ):ℂ)*
        Complex.exp (((-t*Real.log n:ℝ):ℂ)*Complex.I) := by
  apply sum_congr rfl
  intro n hn
  have hkn := (mem_Ioc.mp hn).1
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 := (zero_lt_one.trans hn1).ne'
  have hw : w m n = ((moebius n:ℤ):ℝ)^2*(n:ℝ)^(-(1/2:ℝ))*(Real.log 2/Real.log n)^m := by
    rw [w,mass,logTailScale_eq_weight m hn1]
    field_simp
  exact congrArg (fun x : ℝ => (x:ℂ)*phase (-t*Real.log n)) hw

/-- The squarefree harmonic mass of one multiplicative octave. -/
def octaveHarmonicMass (K : ℕ) := harmonicMoebiusDiagonal (2*K:ℕ)-harmonicMoebiusDiagonal K

private theorem octave_sum (K : ℕ) : octaveHarmonicMass K = ∑ n ∈ Ioc K (2*K), mass n := by
  have hi : Icc 1 (2*K) \ Icc 1 K = Ioc K (2*K) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hs : Icc 1 K ⊆ Icc 1 (2*K) := fun _ hn => mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
    (mem_Icc.mp hn).2.trans (by omega)⟩
  simp only [octaveHarmonicMass,harmonicMoebiusDiagonal,Nat.floor_natCast,←hi,sum_sdiff_eq_sub hs,mass]

theorem octaveHarmonicMass_limit :
    Tendsto octaveHarmonicMass atTop (𝓝 (squarefreeDensity*Real.log 2)) := by
  let E (x : ℝ) := harmonicMoebiusDiagonal x-squarefreeDensity*Real.log x-squarefreeHarmonicConstant
  have hE : Tendsto E atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
      (by simpa only [mul_zero] using (tendsto_rpow_neg_atTop (show (0:ℝ)<1/2 by norm_num)).const_mul 12)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact (Real.norm_eq_abs _).le.trans (squarefree_harmonic_finite_part hx)
  have hn := tendsto_natCast_atTop_atTop (R:=ℝ)
  have h2 := hE.comp (hn.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have h := (h2.sub (hE.comp hn)).add (tendsto_const_nhds (x:=squarefreeDensity*Real.log 2))
  simp only [sub_zero,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
  have hk0 : (0:ℝ)<k := Nat.cast_pos.mpr hk
  dsimp only [Function.comp_apply,E,octaveHarmonicMass]
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hk0.ne']
  ring

private theorem top_scale_le {K n : ℕ} (hK : 2 ≤ K) (hn : n ∈ Ioc K (2*K)) (m : ℕ) :
    logTailScale m (2*K:ℕ)/2 ≤ logTailScale m n := by
  have hk := (mem_Ioc.mp hn).1
  have hN := (mem_Ioc.mp hn).2
  have hn2 : (1:ℝ)<n := by exact_mod_cast (show 1 < n by omega)
  have htop : (1:ℝ)<(2*K:ℕ) := by exact_mod_cast (show 1 < 2*K by omega)
  have hmono := Real.log_le_log (zero_lt_one.trans hn2) (Nat.cast_le.mpr hN)
  have h := pow_le_pow_left₀ (div_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)) (Real.log_pos htop).le)
    (div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (Real.log_pos hn2) hmono) (2*m)
  have hnN : ((2*K:ℕ):ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast (show 2*K ≤ 2*n by omega)
  have hprod := mul_le_mul hnN h (pow_nonneg (div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_pos htop).le) _) (by positivity)
  have he := logTailScale_sq m htop
  have he' := logTailScale_sq m hn2
  apply (sq_le_sq₀ (div_nonneg (Real.exp_pos _).le zero_le_two) (Real.exp_pos _).le).mp
  change (logTailScale m (2*K:ℕ)/2)^2 ≤ (logTailScale m n)^2
  linarith only [hprod,he,he',sq_nonneg (logTailScale m n)]

private def edge : ℝ := 1/Real.log 2
private theorem edge_gt_one : 1 < edge := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num)
  exact (one_lt_div (Real.log_pos (by norm_num))).mpr (by linarith only [h])

private theorem unsigned_octave_norm_floor (m : ℕ) {K : ℕ} (hK : 2 ≤ K) {t : ℝ} (ht : t ∈ Set.Icc 1 edge) :
    octaveHarmonicMass K*logTailScale m (2*K:ℕ)/4 ≤ ‖unsignedDyadicMoebius m K t‖ := by
  let L := Real.log (2*K:ℕ)
  have hr : phase (t*L)*unsignedDyadicMoebius m K t =
      ∑ n ∈ Ioc K (2*K), (w m n:ℂ)*phase (t*(L-Real.log n)) := by
    rw [unsignedDyadicMoebius,mul_sum]
    apply sum_congr rfl
    intro n _
    rw [show t*(L-Real.log n)=t*L+(-t*Real.log n) by ring,phase_add]
    ring
  have h (n : ℕ) (hn : n ∈ Ioc K (2*K)) :
      mass n*(logTailScale m (2*K:ℕ)/4) ≤ ((w m n:ℂ)*phase (t*(L-Real.log n))).re := by
    have hk0 : (0:ℝ)<K := Nat.cast_pos.mpr (by omega)
    have hkn := (mem_Ioc.mp hn).1
    have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr (by omega)
    have hlo := Real.log_le_log hn0 (Nat.cast_le.mpr (mem_Ioc.mp hn).2)
    have hhi := Real.log_le_log hk0 (Nat.cast_le.mpr hkn.le)
    have htop : L=Real.log 2+Real.log K := by
      simp only [L,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hk0.ne']
    have hphase : t*(L-Real.log n) ≤ 1 := by
      calc _ ≤ edge*Real.log 2 := mul_le_mul ht.2 (by linarith only [htop,hhi]) (sub_nonneg.mpr hlo) (zero_lt_one.trans edge_gt_one).le
        _ = 1 := div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1:ℝ)<2)).ne'
    have hp0 := mul_nonneg (zero_le_one.trans ht.1) (sub_nonneg.mpr hlo)
    have hc := Real.one_sub_sq_div_two_le_cos (x:=t*(L-Real.log n))
    have hs := pow_le_pow_left₀ hp0 hphase 2
    have hv : 1/2 ≤ Real.cos (t*(L-Real.log n)) := by linarith only [hs,hc]
    have scale := top_scale_le hK hn m
    have hmul := mul_le_mul scale hv (show (0:ℝ) ≤ 1/2 by norm_num) (Real.exp_pos _).le
    rw [Complex.re_ofReal_mul,phase,Complex.exp_ofReal_mul_I_re,w]
    have H := mul_le_mul_of_nonneg_left hmul (mass_nonneg n)
    linarith only [H]
  have hh := sum_le_sum h
  rw [←sum_mul,←octave_sum,←Complex.re_sum,←hr] at hh
  have he := hh.trans (Complex.re_le_norm _)
  rw [norm_mul,norm_phase,one_mul] at he
  linarith only [he]

/-- A fixed interval of positive heights forces squared energy at least
a constant times the square of the high-frequency endpoint scale. -/
theorem unsigned_dyadic_window_energy (m : ℕ) {K : ℕ} (hK : 2 ≤ K) {T : ℝ} (hT : 1/Real.log 2 ≤ T) :
    (1/Real.log 2-1)*(octaveHarmonicMass K*logTailScale m (2*K:ℕ)/4)^2 ≤
      ∫ t in (1:ℝ)..T, ‖unsignedDyadicMoebius m K t‖^2 := by
  have h0 : 0 ≤ octaveHarmonicMass K := by rw [octave_sum]; exact sum_nonneg fun n _ => mass_nonneg n
  let b := octaveHarmonicMass K*logTailScale m (2*K:ℕ)/4
  have hb : 0 ≤ b := div_nonneg (mul_nonneg h0 (Real.exp_pos _).le) (by norm_num)
  have hcont : Continuous (fun t : ℝ => ‖unsignedDyadicMoebius m K t‖^2) := by
    unfold unsignedDyadicMoebius phase
    fun_prop
  have hm := intervalIntegral.integral_mono_on (μ:=volume) edge_gt_one.le
    (f:=fun _ => b^2) (g:=fun t => ‖unsignedDyadicMoebius m K t‖^2)
    intervalIntegrable_const (hcont.intervalIntegrable _ _)
    (fun t ht => pow_le_pow_left₀ hb (unsigned_octave_norm_floor m hK ht) 2)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hm
  exact hm.trans (intervalIntegral.integral_mono_interval le_rfl edge_gt_one.le hT
    (.of_forall fun _ => sq_nonneg _) (hcont.intervalIntegrable _ _))

/-- Above the length threshold, the unsigned dyadic polynomial has
divergent normalized energy. Any improvement for the original row
in this range must distinguish its signs. -/
theorem unsigned_dyadic_mean_diverges {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 < γ)
    (hgap : γ < 1-2*α) :
    let N := fun K : ℕ => 2*K
    Tendsto (fun K : ℕ => (∫ t in (1:ℝ)..(1+((N K:ℝ)^γ)),
      ‖unsignedDyadicMoebius (cutoffLogarithmicOrder α (N K)) K t‖^2)/((N K:ℝ)^γ)) atTop atTop := by
  intro N
  let β := (α+(1-γ)/2)/2
  have hb : α < β := by dsimp only [β]; linarith only [hgap]
  have hp : 0 < 1-2*β-γ := by dsimp only [β]; linarith only [hgap]
  have hN : Tendsto N atTop atTop := tendsto_atTop_mono (f:=id) (fun _ => by dsimp only [id,N]; omega) tendsto_id
  have hR := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hN
  have ht := (tendsto_rpow_atTop hγ).comp hR
  have hαN := ((cutoff_penalty_fraction hα).comp hN).eventually_le_const hb
  let d := squarefreeDensity*Real.log 2/2
  have hδ : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < d := half_pos (mul_pos hδ hL)
  have hmass := octaveHarmonicMass_limit.eventually_const_le
    (show d < squarefreeDensity*Real.log 2 from half_lt_self (mul_pos hδ hL))
  let c := (edge-1)*(d/4)^2
  have hc : 0 < c := mul_pos (sub_pos.mpr edge_gt_one) (sq_pos_of_pos (div_pos hd (by norm_num)))
  have hlarge := ((tendsto_rpow_atTop hp).comp hR).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ hlarge
  filter_upwards [eventually_ge_atTop (2:ℕ),hαN,ht.eventually_ge_atTop edge,hmass] with K hK hupper hT hM
  let x : ℝ := N K
  let m := cutoffLogarithmicOrder α (N K)
  have hx : (1:ℝ)<x := by dsimp only [x,N]; exact_mod_cast (show 1 < 2*K by omega)
  have hx0 := zero_lt_one.trans hx
  have hy := Real.log_pos hx
  have hpaid : logTailPenalty m x ≤ β*Real.log x := (div_le_iff₀ hy).mp hupper
  have hs : x^(1-2*β) ≤ (logTailScale m x)^2 := by
    rw [logTailScale,←Real.exp_nat_mul,Real.rpow_def_of_pos hx0,Real.exp_le_exp]
    push_cast
    linarith only [hpaid]
  have hms := pow_le_pow_left₀ hd.le hM 2
  have hDS := mul_le_mul hms hs (Real.rpow_nonneg hx0.le _) (sq_nonneg _)
  have hfloor := unsigned_dyadic_window_energy m hK (T:=1+x^γ)
    (hT.trans (le_add_of_nonneg_left zero_le_one))
  have hden := Real.rpow_pos_of_pos hx0 γ
  apply (le_div_iff₀ hden).mpr
  change c*x^(1-2*β-γ)*x^γ ≤ _
  rw [mul_assoc,←Real.rpow_add hx0,sub_add_cancel]
  apply le_trans _ hfloor
  change (edge-1)*(d/4)^2*x^(1-2*β) ≤ (edge-1)*(octaveHarmonicMass K*logTailScale m x/4)^2
  have hm := mul_le_mul_of_nonneg_left hDS (div_nonneg (sub_pos.mpr edge_gt_one).le (by norm_num : (0:ℝ) ≤ 16))
  linarith only [hm]

#print axioms unsignedDyadicMoebius_formula
#print axioms unsigned_dyadic_mean_diverges
#print axioms octaveHarmonicMass_limit
#print axioms unsigned_dyadic_window_energy

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
