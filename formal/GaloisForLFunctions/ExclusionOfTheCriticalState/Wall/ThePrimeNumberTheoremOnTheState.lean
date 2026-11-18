import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.DilatingTheOrdinaryPrimeMeasure
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProperPrimePowersInThePrimeWave
import GaloisForLFunctions.HTGeometry.ReflectionIntegral

/-!
# The prime number theorem on the physical state

The continuous state profile supplies a fixed test of the rescaled ordinary-prime
measure. At prime powers of exponent one and two its integral is respectively the
polar charge and half the zero-frequency charge.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private def primeDilationTest (Φ : ℝ → ℝ) (k u : ℝ) : ℝ :=
  Real.exp (-(k/2)*Real.log (max 1 u))*Φ (-k*Real.log (max 1 u))

private theorem continuous_primeDilationTest {Φ : ℝ → ℝ} (hc : Continuous Φ) (k : ℝ) :
    Continuous (primeDilationTest Φ k) := by
  have hl : Continuous fun u : ℝ => Real.log (max 1 u) :=
    (continuous_const.max continuous_id).log fun u => (lt_of_lt_of_le zero_lt_one (le_max_left 1 u)).ne'
  exact ((hl.const_mul _).rexp).mul (hc.comp (hl.const_mul _))

private theorem primeDilationTest_of_pos {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {k u : ℝ} (hk : 0 ≤ k) (hu : 0 < u) :
    primeDilationTest Φ k u = Real.exp (-(k/2)*Real.log u)*Φ (-k*Real.log u) := by
  rcases le_or_gt 1 u with h | h
  · simp only [primeDilationTest,max_eq_right h]
  · have hl := Real.log_nonpos hu.le h.le
    have hz := hs (-k*Real.log u) (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hk) hl)
    simp only [primeDilationTest,max_eq_left h.le,Real.log_one,mul_zero,hs 0 le_rfl,hz]

private theorem primeDilationTest_bound {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {k : ℝ} (hk : 1 ≤ k) (u : ℝ) :
    |primeDilationTest Φ k u| ≤ (2*C)/(1+u^2) := by
  rcases le_or_gt u 1 with hu | hu
  · simp only [primeDilationTest,max_eq_left hu,Real.log_one,mul_zero,hs 0 le_rfl,mul_zero,abs_zero]
    positivity
  · have hu0 := zero_lt_one.trans hu
    have hl := Real.log_nonneg hu.le
    rw [primeDilationTest_of_pos hs (zero_le_one.trans hk) hu0,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hraw := mul_le_mul_of_nonneg_left (hb (-k*Real.log u))
      (Real.exp_pos (-(k/2)*Real.log u)).le
    have hpow : Real.exp (-(2*Real.log u)) = (u^2)⁻¹ := by
      rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log hu0,sq]
    have hexp : Real.exp (-(k/2)*Real.log u+2*(-k*Real.log u)) ≤ (u^2)⁻¹ := by
      rw [← hpow,Real.exp_le_exp]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hk) hl,hl]
    calc _ ≤ C*Real.exp (-(k/2)*Real.log u+2*(-k*Real.log u)) := by
             rw [Real.exp_add]; exact hraw.trans_eq (by ring)
      _ ≤ C*(u^2)⁻¹ := mul_le_mul_of_nonneg_left hexp hC
      _ ≤ _ := by
        rw [← div_eq_mul_inv,div_le_div_iff₀ (sq_pos_of_pos hu0) (by positivity)]
        have hu2 : 1 ≤ u^2 := one_le_pow₀ hu.le
        nlinarith only [mul_nonneg hC (sub_nonneg.mpr hu2)]

private theorem real_laplace_eq_integral (F : ℝ → ℝ) (b : ℝ) :
    (negativeHalfLineLaplace (cx F) (b:ℂ)).re = ∫ u : ℝ, Real.exp (b*u)*F u := by
  have he : negativeHalfLineLaplace (cx F) (b:ℂ) = ((∫ u : ℝ, Real.exp (b*u)*F u : ℝ):ℂ) := by
    rw [negativeHalfLineLaplace,← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun u => by
      simp only [cx,Complex.ofReal_mul,Complex.ofReal_exp])
  exact congrArg Complex.re he

private theorem integral_primeDilationTest {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {k : ℝ} (hk : 0 < k) :
    ∫ y in Ici (0:ℝ), primeDilationTest Φ k y =
      k⁻¹*(negativeHalfLineLaplace (cx Φ) ((1/2-k⁻¹:ℝ):ℂ)).re := by
  let f := fun u : ℝ => Real.exp ((1/2-k⁻¹)*u)*Φ u
  rw [integral_Ici_eq_integral_Ioi,HTGeometry.integral_Ioi_comp_exp,real_laplace_eq_integral]
  calc _ = ∫ r : ℝ, f (-k*r) := by
         apply integral_congr_ae (Eventually.of_forall fun r => ?_)
         rw [primeDilationTest_of_pos hs hk.le (Real.exp_pos r),Real.log_exp,
           ← mul_assoc,← Real.exp_add]
         have he : r + -(k/2)*r = (1/2-k⁻¹)*(-k*r) := by
           field_simp [hk.ne']; ring
         simp only [he,f]
    _ = _ := by
         simpa only [inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hk),smul_eq_mul,f] using
           (Measure.integral_comp_mul_left f (-k))

/-- The signed layer at exponent `k`, with weight `(log p) p^(-k/2)` and delay `k log p`. -/
def primePowerLayer (Φ : ℝ → ℝ) (k t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, Real.log (p:ℕ)*Real.exp (-(k/2)*Real.log (p:ℕ))*Φ (t-k*Real.log (p:ℕ))

private theorem prime_test_eq_layer {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {k : ℝ} (hk : 0 < k) (t : ℝ) :
    (∑' p : Nat.Primes, Real.log (p:ℕ)*primeDilationTest Φ k ((p:ℕ)/Real.exp (t/k))) /
      Real.exp (t/k) = Real.exp ((1/2-k⁻¹)*t)*primePowerLayer Φ k t := by
  rw [primePowerLayer,← tsum_mul_left,← tsum_div_const]
  apply tsum_congr
  intro p
  have hp : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.property.pos
  have hX := Real.exp_pos (t/k)
  rw [primeDilationTest_of_pos hs hk.le (div_pos hp hX),Real.log_div hp.ne' hX.ne',Real.log_exp]
  have ha : -k*(Real.log (p:ℕ)-t/k) = t-k*Real.log (p:ℕ) := by field_simp [hk.ne']; ring
  rw [ha, div_eq_iff hX.ne']
  have he : Real.exp (-(k/2)*(Real.log (p:ℕ)-t/k)) =
      Real.exp ((1/2-k⁻¹)*t)*Real.exp (-(k/2)*Real.log (p:ℕ))*Real.exp (t/k) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    field_simp [hk.ne']; ring
  rw [he]; ring

/-- On logarithmic Chebyshev mass coordinates, the square layer is an exact integral
of translates. Each interval in the mass coordinate contributes its prime's logarithm. -/
theorem primeSquareLayer_eq_bin_integral {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {t : ℝ} (ht : 0 ≤ t) :
    primePowerLayer Φ 2 t = ∫ r : ℝ,
      let p := primeBinReading 1 (Real.exp r)
      Real.exp r/p*Φ (t-2*Real.log p) := by
  let Ψ := fun u : ℝ => Φ (t+u)
  have hΨ : Continuous Ψ := hc.comp (continuous_const.add continuous_id)
  have hsΨ (u : ℝ) (hu : 0 ≤ u) : Ψ u=0 := hs _ (add_nonneg ht hu)
  have hbΨ (u : ℝ) : |Ψ u| ≤ (C*Real.exp (2*t))*Real.exp (2*u) := by
    simpa only [Ψ,mul_add,Real.exp_add,mul_assoc] using hb (t+u)
  have hCΨ : 0 ≤ C*Real.exp (2*t) := mul_nonneg hC (Real.exp_pos _).le
  have hI := integral_primeBinReading_eq (continuous_primeDilationTest hΨ 2).measurable
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCΨ)
    (fun u _ => primeDilationTest_bound hsΨ hCΨ hbΨ (by norm_num : (1:ℝ) ≤ 2) u)
    (x := 1) zero_lt_one
  rw [integral_Ici_eq_integral_Ioi,HTGeometry.integral_Ioi_comp_exp] at hI
  simp only [div_one] at hI
  have hP := prime_test_eq_layer hsΨ (by norm_num : (0:ℝ) < 2) 0
  simp only [zero_div,Real.exp_zero,div_one,mul_zero,one_mul] at hP
  have hp : primePowerLayer Φ 2 t = primePowerLayer Ψ 2 0 := by
    simp only [primePowerLayer,Ψ,zero_sub,sub_eq_add_neg]
  rw [hp,← hP,← hI]
  apply integral_congr_ae (Eventually.of_forall fun r => ?_)
  let p := primeBinReading 1 (Real.exp r)
  have hp0 := primeBinReading_one_pos (Real.exp r)
  change Real.exp r*primeDilationTest Ψ 2 p = Real.exp r/p*Φ (t-2*Real.log p)
  rw [primeDilationTest_of_pos hsΨ (by norm_num : (0:ℝ) ≤ 2) hp0]
  norm_num only [div_self (by norm_num : (2:ℝ) ≠ 0),neg_one_mul,Real.exp_neg,
    Real.exp_log (show 0 < p from hp0)]
  simp only [Ψ,neg_mul,sub_eq_add_neg,div_eq_mul_inv,mul_assoc]

/-- A fixed prime-power layer samples the Laplace integral of any continuous confined profile. -/
theorem tendsto_primePowerLayer_of_confinement {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (fun t : ℝ => Real.exp ((1/2-k⁻¹)*t)*primePowerLayer Φ k t)
      atTop (𝓝 (k⁻¹*(negativeHalfLineLaplace (cx Φ) ((1/2-k⁻¹:ℝ):ℂ)).re)) := by
  have hk0 := zero_lt_one.trans_le hk
  have hP := tendsto_dilated_ordinary_prime_sum (continuous_primeDilationTest hΦ k)
    (mul_nonneg (by norm_num) hC) (fun u _ => primeDilationTest_bound hs hC hb hk u)
  rw [integral_primeDilationTest hs hk0] at hP
  have hscale : Tendsto (fun t : ℝ => Real.exp (t/k)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hk0)
  exact (hP.comp hscale).congr fun t => prime_test_eq_layer hs hk0 t

/-- For each fixed exponent at least one, the prime number theorem gives the
leading signed layer in terms of a single real Laplace value of the state. -/
theorem criticalState_primePowerLayer_asymptotic {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ ∀ k : ℝ, 1 ≤ k →
      Tendsto (fun t : ℝ => Real.exp ((1/2-k⁻¹)*t)*primePowerLayer Φ k t)
        atTop (𝓝 (k⁻¹*(negativeHalfLineLaplace (cx F) ((1/2-k⁻¹:ℝ):ℂ)).re)) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine ⟨Φ,hΦ,heq,fun k hk => ?_⟩
  have he : negativeHalfLineLaplace (cx Φ) ((1/2-k⁻¹:ℝ):ℂ) =
      negativeHalfLineLaplace (cx F) ((1/2-k⁻¹:ℝ):ℂ) := by
    apply integral_congr_ae
    filter_upwards [heq] with u hu
    simp only [cx,hu]
  rw [← he]
  exact tendsto_primePowerLayer_of_confinement hΦ hs hC hb hk

/-- In the first two layers the polar term comes from ordinary primes and
the constant term from prime squares. Both limits use the same representative. -/
theorem criticalState_ordinary_and_square_prime_limits {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      Tendsto (fun t : ℝ => Real.exp (-(t/2))*primePowerLayer Φ 1 t) atTop
        (𝓝 (negativeHalfLineLaplace (cx F) (-(1/2))).re) ∧
      Tendsto (primePowerLayer Φ 2) atTop (𝓝 ((negativeHalfLineLaplace (cx F) 0).re/2)) := by
  obtain ⟨Φ,hΦ,heq,h⟩ := criticalState_primePowerLayer_asymptotic hW ht hF
  refine ⟨Φ,hΦ,heq,?_,?_⟩
  · have h1 := h 1 le_rfl
    rw [show 1/2-(1:ℝ)⁻¹ = -(1/2) by norm_num] at h1
    have hx (t : ℝ) : -(1/2)*t = -(t/2) := by ring
    have hz : ((-(1/2):ℝ):ℂ) = -(1/2) := by norm_num
    simpa only [hx,hz,inv_one,one_mul] using h1
  · have h2 := h 2 (by norm_num)
    rw [show 1/2-(2:ℝ)⁻¹ = 0 by norm_num] at h2
    simpa only [zero_mul,Real.exp_zero,one_mul,Complex.ofReal_zero,div_eq_inv_mul] using h2

/-- The prime-power indices of exponent at least three. -/
abbrev cubeOrHigherIndex (j : Nat.Primes × ℕ) : ℕ := (j.1 : ℕ)^(j.2+3)

/-- The total variation of all layers above the squares decays exponentially,
at every rate below one sixth. Only prime powers past the observation time contribute. -/
theorem cubeOrHigherWave_absolute_exp_bound {g : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → g u=0)
    {C : ℝ} (hb : ∀ u, |g u| ≤ C) {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1/6) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ,
      let a := fun j => vonMangoldtAtom (cubeOrHigherIndex j)*g (t-Real.log (cubeOrHigherIndex j))
      (Summable fun j => |a j|) ∧ (∑' j, |a j|) ≤ M*Real.exp (-b*t) := by
  let w := fun j : Nat.Primes × ℕ => |vonMangoldtAtom (cubeOrHigherIndex j)|*
    Real.exp (b*Real.log (cubeOrHigherIndex j))
  have hw : Summable w := by
    have hre : (1:ℝ)/3 < ((1:ℂ)/2-(b:ℂ)).re := by
      rw [Complex.sub_re,Complex.ofReal_re,show ((1:ℂ)/2).re=(1:ℝ)/2 by norm_num]
      linarith only [hb1]
    refine (summable_xiPrimeLogHigherValuationThreePlus_term hre).norm.congr fun j => ?_
    rw [← vonMangoldtAtom_mul_cexp_eq_term (b:ℂ),norm_mul,Complex.norm_real,Real.norm_eq_abs,
      norm_cexp_mul_ofReal,Complex.ofReal_re]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hb 0)
  refine ⟨(∑' j, w j)*C,mul_nonneg (tsum_nonneg fun j => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hC,
    fun t => ?_⟩
  let a := fun j => vonMangoldtAtom (cubeOrHigherIndex j)*g (t-Real.log (cubeOrHigherIndex j))
  have ha (j) : |a j| ≤ w j*C*Real.exp (-b*t) := by
    let l := Real.log (cubeOrHigherIndex j)
    have hg : |g (t-l)| ≤ C*Real.exp (b*(l-t)) := by
      by_cases ht : l ≤ t
      · rw [hs _ (sub_nonneg.mpr ht),abs_zero]; positivity
      · exact (hb _).trans (le_mul_of_one_le_right hC (Real.one_le_exp (mul_nonneg hb0 (sub_nonneg.mpr (le_of_not_ge ht)))))
    change |vonMangoldtAtom (cubeOrHigherIndex j)*g (t-l)| ≤
      (|vonMangoldtAtom (cubeOrHigherIndex j)|*Real.exp (b*l))*C*Real.exp (-b*t)
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left hg (abs_nonneg _)).trans_eq
    rw [mul_sub,Real.exp_sub,neg_mul,Real.exp_neg]
    ring
  have hmajor := (hw.mul_right C).mul_right (Real.exp (-b*t))
  have habs := Summable.of_nonneg_of_le (fun j => abs_nonneg (a j)) ha hmajor
  refine ⟨habs,(habs.tsum_le_tsum ha hmajor).trans_eq ?_⟩
  rw [tsum_mul_right,tsum_mul_right]

/-- The exponential absolute bound removes cubic and higher powers at late times. -/
private theorem tendsto_cubeOrHigherWave {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {C : ℝ} (hΦ : ∀ u, |Φ u| ≤ C) :
    Tendsto (fun t : ℝ => ∑' j, vonMangoldtAtom (cubeOrHigherIndex j)*
      Φ (t-Real.log (cubeOrHigherIndex j))) atTop (𝓝 0) := by
  obtain ⟨M,_,h⟩ := cubeOrHigherWave_absolute_exp_bound hs hΦ (b := 1/12) (by norm_num) (by norm_num)
  have h0 := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
    (by norm_num : -(1/12:ℝ)<0))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (by simpa only [mul_zero] using h0.const_mul M)
  intro t
  have ha := (h t).1
  simp only [← Real.norm_eq_abs] at ha
  exact (norm_tsum_le_tsum_norm ha).trans (by simpa only [Real.norm_eq_abs] using (h t).2)

private theorem square_term_eq (Φ : ℝ → ℝ) (t : ℝ) (p : Nat.Primes) :
    vonMangoldtAtom ((p:ℕ)^2)*Φ (t-Real.log (((p:ℕ)^2:ℕ):ℝ)) =
      Real.log (p:ℕ)*Real.exp (-(2/2)*Real.log (p:ℕ))*Φ (t-2*Real.log (p:ℕ)) := by
  have hp : 0 < ((p:ℕ):ℝ) := by exact_mod_cast p.property.pos
  have hh : 2 ≤ (p:ℕ)^2 := p.property.two_le.trans (Nat.le_self_pow (by decide) (p:ℕ))
  rw [vonMangoldtAtom,if_pos hh,ArithmeticFunction.vonMangoldt_apply_pow (by decide),
    ArithmeticFunction.vonMangoldt_apply_prime p.property,Nat.cast_pow,Real.sqrt_sq hp.le,Real.log_pow]
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (2:ℝ) ≠ 0),neg_one_mul,
    Real.exp_neg,Real.exp_log hp,div_eq_mul_inv]

/-- Separating exponent two in the absolutely convergent proper-power row. -/
theorem square_add_higher_eq_properPower {Φ : ℝ → ℝ} {t : ℝ}
    (habs : Summable fun j : Nat.Primes × ℕ =>
      vonMangoldtAtom (properPrimePowerIndex j)*|Φ (t-Real.log (properPrimePowerIndex j))|)
    : primePowerLayer Φ 2 t+(∑' j, vonMangoldtAtom (cubeOrHigherIndex j)*Φ (t-Real.log (cubeOrHigherIndex j))) =
      ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*Φ (t-Real.log (properPrimePowerIndex j)) := by
  let f := fun j : Nat.Primes × ℕ => vonMangoldtAtom (properPrimePowerIndex j)*
    Φ (t-Real.log (properPrimePowerIndex j))
  have hf : Summable f := by
    apply Summable.of_norm
    refine habs.congr fun j => ?_
    have hn : 0 ≤ vonMangoldtAtom (properPrimePowerIndex j) := by
      unfold vonMangoldtAtom
      split_ifs <;> first | exact le_rfl | exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    simp only [f,Real.norm_eq_abs,abs_mul,abs_of_nonneg hn]
  have hshift : Summable fun j : Nat.Primes × ℕ => f (j.1,j.2+1) := by
    apply hf.comp_injective (i := fun j : Nat.Primes × ℕ => (j.1,j.2+1))
    rintro ⟨p,i⟩ ⟨q,j⟩ he
    simpa only [Prod.mk.injEq,Nat.add_right_cancel_iff] using he
  have hhead : Summable (fun p : Nat.Primes => f (p,0)) :=
    hf.comp_injective (i := fun p : Nat.Primes => (p,0)) (fun _ _ h => congrArg Prod.fst h)
  have hsplit (p : Nat.Primes) : (∑' j, f (p,j)) = f (p,0)+∑' j, f (p,j+1) :=
    (hf.comp_injective (i := fun n : ℕ => (p,n)) (fun _ _ h => congrArg Prod.snd h)).tsum_eq_zero_add
  have hsq : primePowerLayer Φ 2 t = ∑' p : Nat.Primes, f (p,0) :=
    tsum_congr fun p => (square_term_eq Φ t p).symm
  change primePowerLayer Φ 2 t + (∑' j : Nat.Primes × ℕ, f (j.1,j.2+1)) = ∑' j, f j
  rw [hsq,hf.tsum_prod,hshift.tsum_prod]
  simp_rw [hsplit]
  rw [hhead.tsum_add hshift.prod]

private theorem tendsto_properPowerWave_of_square {Φ : ℝ → ℝ} {C L : ℝ}
    (hs : ∀ u, 0 ≤ u → Φ u=0) (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    (h2 : Tendsto (primePowerLayer Φ 2) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*
      Φ (t-Real.log (properPrimePowerIndex j))) atTop (𝓝 L) := by
  have hb' (u : ℝ) : |Φ u| ≤ C := by
    rcases le_or_gt 0 u with hu | hu
    · simpa only [hs u hu,abs_zero] using hC
    · exact (hb u).trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith only [hu])))
  have hboth := h2.add (tendsto_cubeOrHigherWave hs hb')
  rw [add_zero] at hboth
  obtain ⟨_,_,habs⟩ := properPowerWave_absolute_envelope (by norm_num : (0:ℝ)<2) hC hb
  exact hboth.congr fun t => square_add_higher_eq_properPower (habs t).1

/-- After summing over all proper prime powers, the same half-charge remains.
The limit is for the unheated signed wave of the continuous representative. -/
theorem criticalState_tendsto_properPowerWave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      Tendsto (fun t : ℝ => ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*
        Φ (t-Real.log (properPrimePowerIndex j))) atTop (𝓝 ((negativeHalfLineLaplace (cx F) 0).re/2)) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨Ψ,hΨ,heqΨ,_,h2⟩ := criticalState_ordinary_and_square_prime_limits hW ht hF
  have hΨΦ : Ψ = Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heqΨ.symm.trans heq)
  subst Ψ
  exact ⟨Φ,hΦ,heq,tendsto_properPowerWave_of_square hs hC hb h2⟩

/-- All proper powers sample half the integral of every continuous test dominated
by the absolute state profile. The terms of exponent at least three vanish together. -/
theorem criticalState_tendsto_dominated_properPowerWave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ g : ℝ → ℝ, Continuous g → (∀ u, |g u| ≤ |Φ u|) →
        Tendsto (fun t : ℝ => ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*
          g (t-Real.log (properPrimePowerIndex j))) atTop (𝓝 ((∫ u, g u)/2)) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine ⟨Φ,hΦ,heq,fun g hg hdom => ?_⟩
  have hsg (u : ℝ) (hu : 0 ≤ u) : g u=0 := by
    have h := hdom u
    rwa [hs u hu,abs_zero,abs_nonpos_iff] at h
  have hbg (u : ℝ) : |g u| ≤ C*Real.exp (2*u) := (hdom u).trans (hb u)
  have h2 := tendsto_primePowerLayer_of_confinement hg hsg hC hbg (k := 2) (by norm_num)
  rw [show 1/2-(2:ℝ)⁻¹ = 0 by norm_num] at h2
  simp only [zero_mul,Real.exp_zero,one_mul,real_laplace_eq_integral] at h2
  exact tendsto_properPowerWave_of_square hsg hC hbg (by simpa only [div_eq_inv_mul] using h2)

/-- The total variation of the proper-power wave tends to half the absolute mass of the state. -/
theorem criticalState_tendsto_absolute_properPowerWave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      Tendsto (fun t : ℝ => ∑' j, vonMangoldtAtom (properPrimePowerIndex j)*
        |Φ (t-Real.log (properPrimePowerIndex j))|) atTop (𝓝 ((∫ u, |Φ u|)/2)) := by
  obtain ⟨Φ,hΦ,he,h⟩ := criticalState_tendsto_dominated_properPowerWave hW ht hF
  exact ⟨Φ,hΦ,he,h (fun u => |Φ u|) hΦ.abs (fun u => (abs_abs (Φ u)).le)⟩

#print axioms criticalState_tendsto_dominated_properPowerWave
#print axioms criticalState_tendsto_absolute_properPowerWave
#print axioms criticalState_tendsto_properPowerWave

#print axioms criticalState_ordinary_and_square_prime_limits
#print axioms criticalState_primePowerLayer_asymptotic

end GaloisForLFunctions.ExclusionOfTheCriticalState
