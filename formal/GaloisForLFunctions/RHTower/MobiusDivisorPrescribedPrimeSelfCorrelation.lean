import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanUniformRenewal
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GaloisForLFunctions.RHTower.MobiusDivisorPrimePairRatioProfile
import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedClockBlock

/-!
# Uniform prescribed-prime self-correlation and direct debt reduction

A positive inverse-cube moment survives every finite prime core with one
uniform lower bound. Completing the square against the sum of the head and
its delayed copy turns that moment into a core-uniform positive pairing gap.
The exact renewal identity then gives a negative self-correlation increment
at every prescribed prime, retaining the full squarefree Euler density.

A prime pair near that prescribed ratio consequently reduces the original
relative debt in the full logarithmic finite clock energy. No preliminary
prime insertion or assumed source sign enters this construction. The eventual
cutoff threshold still depends on the core and selected pair; cumulative
payment, absolute energy control and exhaustive continuation are not asserted.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private lemma pair_zero_integrable (P : Finset ℕ) {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3) (Ioi 0) := by
  apply (integrable_mobiusDivisorDilationMean_kernel P hY).of_forall_sdiff_eq_zero measurableSet_Ioi
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma pair_zero_integral (P : Finset ℕ) (Y : ℝ) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3)=mobiusDivisorDilationMean P Y := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma pair_scale (P : Finset ℕ) {A B : ℝ} (hB : 0 < B) (x : ℝ) :
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^3 =
      B^3*(mobiusDivisorContinuousHead P ((A/B)*(B*x))*
        mobiusDivisorContinuousHead P (B*x)/(B*x)^3) := by
  rw [show A/B*(B*x)=A*x by field_simp]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma pair_integrable (P : Finset ℕ) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) (Ioi 1) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff _ 0 hB).mpr
    (by simpa using pair_zero_integrable P (div_pos hA hB))
  have hi' : IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) (Ioi 0) := by
    apply IntegrableOn.congr_fun (hi.const_mul (B^3)) _ measurableSet_Ioi
    intro x _
    exact (pair_scale P hB x).symm
  exact hi'.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))

private lemma pair_integral (P : Finset ℕ) {A B : ℝ}
    (hA : 0 < A) (hA1 : A ≤ 1) (hB : 0 < B) :
    (∫x in Ioi (1:ℝ),mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) = B^2*mobiusDivisorDilationMean P (A/B) := by
  have he : (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) =
      ∫x in Ioi (1:ℝ),mobiusDivisorContinuousHead P (A*x)*
        mobiusDivisorContinuousHead P (B*x)/x^3 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
    intro x hx
    have hx1 : x ≤ 1 := le_of_not_gt hx.2
    have hh : A*x ≤ 1 := (mul_le_mul_of_nonneg_left hx1 hA.le).trans (by simpa using hA1)
    simp [mobiusDivisorContinuousHead_eq_zero P hh]
  rw [← he]
  simp_rw [pair_scale P hB]
  rw [integral_const_mul,integral_comp_mul_left_Ioi
    (fun u => mobiusDivisorContinuousHead P ((A/B)*u)*mobiusDivisorContinuousHead P u/u^3)
    0 hB,mul_zero,smul_eq_mul,pair_zero_integral]
  field_simp

private lemma moment_scale (P : Finset ℕ) {A : ℝ} (hA : 0 < A) (x : ℝ) :
    mobiusDivisorContinuousHead P (x/A)/x^3 =
      (A^3)⁻¹*(mobiusDivisorContinuousHead P (A⁻¹*x)/(A⁻¹*x)^3) := by
  rw [show x/A=A⁻¹*x by ring]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma moment_scaled_integrable (P : Finset ℕ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun x => mobiusDivisorContinuousHead P (x/A)/x^3) (Ioi 1) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff _ 0 (inv_pos.mpr hA)).mpr
    (by simpa using integrable_mobiusDivisorContinuousHead_moment P)
  have hi' : IntegrableOn (fun x => mobiusDivisorContinuousHead P (x/A)/x^3) (Ioi 0) := by
    apply (hi.const_mul ((A^3)⁻¹)).congr
    filter_upwards with x
    exact (moment_scale P hA x).symm
  exact hi'.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))

private lemma moment_scaled_integral (P : Finset ℕ) {A : ℝ} (hA : 1 ≤ A) :
    (∫x in Ioi (1:ℝ),mobiusDivisorContinuousHead P (x/A)/x^3) =
      (A^2)⁻¹*(∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P x/x^3) := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have he : (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (x/A)/x^3) =
      ∫x in Ioi (1:ℝ),mobiusDivisorContinuousHead P (x/A)/x^3 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
    intro x hx
    have hh : x/A ≤ 1 := (div_le_one hA0).mpr ((le_of_not_gt hx.2).trans hA)
    simp [mobiusDivisorContinuousHead_eq_zero P hh]
  rw [← he]
  simp_rw [moment_scale P hA0]
  rw [integral_const_mul,integral_comp_mul_left_Ioi
    (fun x => mobiusDivisorContinuousHead P x/x^3) 0 (inv_pos.mpr hA0),
    mul_zero,inv_inv,smul_eq_mul]
  field_simp

private lemma cube_weight_eq : (fun x : ℝ => x^(-3:ℝ)) = fun x => 1/x^(3:ℕ) := by
  funext x
  rw [show (-3:ℝ) = -((3:ℕ):ℝ) by norm_num, Real.rpow_neg_natCast]
  rw [one_div, zpow_neg, zpow_natCast]

private lemma cube_weight_integrable : IntegrableOn (fun x : ℝ => 1/x^3) (Ioi 1) := by
  rw [← cube_weight_eq]
  exact integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) zero_lt_one

private lemma cube_weight_integral : (∫x in Ioi (1:ℝ),(1:ℝ)/x^3) = 1/2 := by
  rw [← cube_weight_eq,integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) zero_lt_one]
  norm_num

/-- One positive source constant bounds the paired head plus every delayed copy,
uniformly over the complete finite processed prime core. -/
theorem exists_mobiusDivisorDilationMean_uniform_plus_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Finset ℕ, (∀ p ∈ P,p.Prime) → ∀ A : ℝ, 1 ≤ A →
      c ≤ mobiusDivisorDilationMean P 1 + mobiusDivisorDilationMean P A/A := by
  let m : ℝ := Real.exp (-2*∑' n : ℕ,(n:ℝ)^(-3/2:ℝ))*
    (∫x in Ioi (0:ℝ),divisorContinuousUnitHead x/x^3)
  have hm : 0 < m := mul_pos (Real.exp_pos _) integral_divisorContinuousUnitHead_moment_pos
  refine ⟨m^2,pow_pos hm 2,?_⟩
  intro P hP A hA
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAi : 0 < A⁻¹ := inv_pos.mpr hA0
  have hAi1 : A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hA
  let g : ℝ → ℝ := fun x => mobiusDivisorContinuousHead P x+A*mobiusDivisorContinuousHead P (x/A)
  have hi0 := pair_integrable P zero_lt_one zero_lt_one
  have hi1 := pair_integrable P zero_lt_one hAi
  have hi2 := pair_integrable P hAi hAi
  simp only [one_mul,← div_eq_mul_inv,mul_comm A⁻¹] at hi0 hi1 hi2
  have hiM := (integrable_mobiusDivisorContinuousHead_moment P).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  have hig : IntegrableOn (fun x => g x/x^3) (Ioi 1) := by
    apply (hiM.add ((moment_scaled_integrable P hA0).const_mul A)).congr
    filter_upwards with x
    dsimp [g]
    ring
  have hig2 : IntegrableOn (fun x => (g x)^2/x^3) (Ioi 1) := by
    apply ((hi0.add (hi1.const_mul (2*A))).add (hi2.const_mul (A^2))).congr
    filter_upwards with x
    dsimp [g]
    ring
  have hg2 : (∫x in Ioi (1:ℝ),(g x)^2/x^3) =
      2*(mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P A/A) := by
    have he (x : ℝ) : (g x)^2/x^3 =
        (mobiusDivisorContinuousHead P x*mobiusDivisorContinuousHead P x/x^3+
        (2*A)*(mobiusDivisorContinuousHead P x*mobiusDivisorContinuousHead P (x/A)/x^3))+
        A^2*(mobiusDivisorContinuousHead P (x/A)*mobiusDivisorContinuousHead P (x/A)/x^3) := by
      dsimp [g]
      ring
    simp_rw [he]
    have hadd := integral_add (hi0.add (hi1.const_mul (2*A))) (hi2.const_mul (A^2))
    simp only [Pi.add_apply] at hadd
    rw [hadd,integral_add hi0 (hi1.const_mul _),integral_const_mul,integral_const_mul]
    have h0 := pair_integral P zero_lt_one le_rfl zero_lt_one
    have h1 := pair_integral P zero_lt_one le_rfl hAi
    have h2 := pair_integral P hAi hAi1 hAi
    simp only [one_mul,one_pow,one_div,inv_inv,div_self hAi.ne',
      mul_comm A⁻¹,← div_eq_mul_inv] at h0 h1 h2
    rw [h0,h1,h2]
    field_simp
    ring
  have hmg : m ≤ ∫x in Ioi (1:ℝ),g x/x^3 := by
    have he (x : ℝ) : g x/x^3 = mobiusDivisorContinuousHead P x/x^3+
        A*(mobiusDivisorContinuousHead P (x/A)/x^3) := by dsimp [g]; ring
    simp_rw [he]
    rw [integral_add hiM ((moment_scaled_integrable P hA0).const_mul A),integral_const_mul,
      integral_mobiusDivisorContinuousHead_moment_Ioi_one,moment_scaled_integral P hA]
    have hb := integral_mobiusDivisorContinuousHead_moment_uniform_lower P hP
    change m ≤ _ at hb
    have hn : 0 ≤ A*((A^2)⁻¹*(∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P x/x^3)) :=
      mul_nonneg hA0.le (mul_nonneg (by positivity) (hm.le.trans hb))
    linarith only [hb,hn]
  have hineq : 4*m*(∫x in Ioi (1:ℝ),g x/x^3)-2*m^2 ≤
      ∫x in Ioi (1:ℝ),(g x)^2/x^3 := by
    have hi := (hig.const_mul (4*m)).sub (cube_weight_integrable.const_mul (4*m^2))
    have h := integral_mono_ae hi hig2 ?_
    · simp only [Pi.sub_apply] at h
      rw [integral_sub (hig.const_mul _) (cube_weight_integrable.const_mul _),
        integral_const_mul,integral_const_mul,cube_weight_integral] at h
      linarith only [h]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x^3 := pow_pos (lt_trans zero_lt_one hx) 3
      have hs : 4*m*g x-4*m^2 ≤ (g x)^2 := by nlinarith only [sq_nonneg (g x-2*m)]
      have hh := div_le_div_of_nonneg_right hs hx0.le
      dsimp only [Pi.sub_apply]
      convert hh using 1
      ring
  rw [hg2] at hineq
  nlinarith only [hineq,mul_le_mul_of_nonneg_left hmg hm.le]

/-- Processing any prescribed prime drops its own density-weighted dilation
correlation by one core-independent source margin. The exact squarefree
Euler density and prime scaling are retained. -/
theorem exists_mobiusDivisor_uniform_prescribed_prime_correlation_drop :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Finset ℕ, (∀ q ∈ P,q.Prime) →
      ∀ p : ℕ, p.Prime → p ∉ P →
        c*(Sieve.squarefreeDensity*∏q∈P,(q:ℝ)/(q+1))*
            ((p:ℝ)*Real.sqrt p/(p+1)) ≤
          (Sieve.squarefreeDensity*∏q∈P,(q:ℝ)/(q+1))*mobiusDivisorDilationMean P p-
            (Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
              mobiusDivisorDilationMean (insert p P) p := by
  obtain ⟨c,hc,hgap⟩ := exists_mobiusDivisorDilationMean_uniform_plus_gap
  refine ⟨c,hc,?_⟩
  intro P hP p hp hpP
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (1:ℝ) ≤ (p:ℝ)^2 := by nlinarith only [hp1]
  have h := hgap P hP ((p:ℝ)^2) hp2
  let ρ : ℝ := Sieve.squarefreeDensity*∏q∈P,(q:ℝ)/(q+1)
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    apply mul_nonneg
    · rw [Sieve.squarefreeDensity_eq]
      positivity
    · exact prod_nonneg (fun q hq => div_nonneg (Nat.cast_nonneg q) (by positivity))
  have hf : 0 ≤ ρ*((p:ℝ)*Real.sqrt p/(p+1)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right h hf
  have he : (Sieve.squarefreeDensity*∏q∈P,(q:ℝ)/(q+1))*mobiusDivisorDilationMean P p-
      (Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
        mobiusDivisorDilationMean (insert p P) p =
      (mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P ((p:ℝ)^2)/(p:ℝ)^2)*
        (ρ*((p:ℝ)*Real.sqrt p/(p+1))) := by
    rw [prod_insert hpP,mobiusDivisorDilationMean_insert P hP hp hpP hp0,
      div_self hp0.ne']
    dsimp [ρ]
    rw [← pow_two]
    field_simp
    ring
  rw [he]
  simpa only [ρ,mul_assoc] using hscaled


private def selfDebtDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏p∈P,(p:ℝ)/(p+1)

private def selfDebtEnergy (P : Finset ℕ) : ℝ :=
  ∑' n,mobiusDivisorFixedCoreBlockMass P n

private lemma ratio_weight_lower {p q U : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hU : 1 ≤ U) (hqU : q ≤ U*p) : 1/U^2 ≤ (p/q)*Real.sqrt (p/q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have ha : 0 < p/q := div_pos hp hq
  have hb : p/q ≤ 1 := (div_le_one hq).mpr hpq
  have hl : 1/U ≤ p/q := by
    rw [div_le_div_iff₀ hU0 hq]
    simpa [mul_comm] using hqU
  have hs : p/q ≤ Real.sqrt (p/q) := by
    nlinarith [Real.sq_sqrt ha.le,Real.sqrt_nonneg (p/q)]
  calc
    _ = (1/U)*(1/U) := by ring
    _ ≤ (p/q)*(p/q) := mul_le_mul hl hl (by positivity) ha.le
    _ ≤ _ := mul_le_mul_of_nonneg_left hs ha.le

private lemma relative_window_release (P R : Finset ℕ)
    (hP : P.Nonempty) (hR : R.Nonempty)
    (hPprime : ∀r∈P,r.Prime) (hRprime : ∀r∈R,r.Prime)
    (L U k : ℝ) (hL : 1≤L) (hLU : L<U) (hk : 0<k)
    (hW : ∀Y : ℝ,L≤Y → Y≤U →
      selfDebtDensity R*mobiusDivisorDilationMean R Y-
        selfDebtDensity P*mobiusDivisorDilationMean P Y ≤ -k) :
    ∃c T : ℝ,0<c ∧ ∀p q : ℕ,p.Prime → q.Prime →
      p∉P → q∉P → p∉R → q∉R → p<q → T≤(p:ℝ) →
      L*(p:ℝ)≤q → (q:ℝ)≤U*(p:ℝ) →
      c/(p:ℝ) ≤ (selfDebtEnergy R-selfDebtEnergy P)-
        (selfDebtEnergy (insert q (insert p R))-selfDebtEnergy (insert q (insert p P))) := by
  obtain ⟨CP,hCP,hprofileP⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile P hP hPprime
  obtain ⟨CR,hCR,hprofileR⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile R hR hRprime
  let C := CP+CR
  have hC : 0≤C := add_nonneg hCP hCR
  let c := k/(2*U^2)
  have hU : 0<U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,(C/c+1)^2,hc,?_⟩
  intro p q hp hq hpP hqP hpR hqR hpq hpT hlo hhi
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpq0 : (p:ℝ)≤q := by exact_mod_cast hpq.le
  have hratio := hW ((q:ℝ)/p) ((le_div_iff₀ hp0).mpr hlo) ((div_le_iff₀ hp0).mpr hhi)
  let τ := ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)
  have hτ : 0≤τ := by dsimp [τ]; positivity
  have hτlo : 1/U^2≤τ := ratio_weight_lower hp0 hpq0 (hL.trans hLU.le) hhi
  have herrorP := (abs_le.mp (hprofileP p q hp hq hpP hqP hpq.ne' hpq.le)).1
  have herrorR := (abs_le.mp (hprofileR p q hp hq hpR hqR hpq.ne' hpq.le)).2
  have hsmall : C/Real.sqrt p<c := by
    have hroot := Real.sqrt_le_sqrt hpT
    rw [Real.sqrt_sq (by positivity : 0≤C/c+1)] at hroot
    have hm := mul_le_mul_of_nonneg_left hroot hc.le
    have he : c*(C/c+1)=C+c := by field_simp
    rw [he] at hm
    exact (div_lt_iff₀ (Real.sqrt_pos.mpr hp0)).mpr (by linarith)
  have hmain : 2*τ*(selfDebtDensity R*mobiusDivisorDilationMean R ((q:ℝ)/p)-
      selfDebtDensity P*mobiusDivisorDilationMean P ((q:ℝ)/p)) ≤ -4*c := by
    have hm := mul_le_mul_of_nonneg_left hratio (show 0≤2*τ by positivity)
    have hl := mul_le_mul_of_nonneg_left hτlo (show 0≤2*k by positivity)
    have he : 4*c=2*k*(1/U^2) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  have hadd : CP/Real.sqrt p+CR/Real.sqrt p=C/Real.sqrt p := by dsimp [C]; ring
  change -(CP/Real.sqrt p) ≤ (p:ℝ)*(selfDebtEnergy (insert q (insert p P))-selfDebtEnergy P)-
    2*selfDebtDensity P*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*mobiusDivisorDilationMean P ((q:ℝ)/p) at herrorP
  change (p:ℝ)*(selfDebtEnergy (insert q (insert p R))-selfDebtEnergy R)-
    2*selfDebtDensity R*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*mobiusDivisorDilationMean R ((q:ℝ)/p) ≤
    CR/Real.sqrt p at herrorR
  apply (div_le_iff₀ hp0).mpr
  dsimp [τ] at hmain
  nlinarith only [herrorP,herrorR,hmain,hsmall,hc,hadd]

/-- Two fresh actual primes directly reduce the full prescribed-prime relative
clock debt on a common cutoff tail. No preliminary core change, sign premise,
or debt premise is used. The onset still depends on the chosen primes. -/
theorem exists_mobiusDivisorDirectPrescribedDebtReduction :
    ∀ P : Finset ℕ, P.Nonempty → (∀ r ∈ P,r.Prime) →
      ∀ r : ℕ, r.Prime → r ∉ P → ∀ B : ℕ,
        ∃ p q : ℕ, B < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
          p ∉ insert r P ∧ q ∉ insert p (insert r P) ∧
          ∃ d : ℝ, 0 < d ∧ ∀ᶠ M : ℕ in atTop,
            d*(M:ℝ)^2*(1+Real.log M) ≤
              (mobiusDivisorFiniteClockEnergy 1 M (insert r P)-
                mobiusDivisorFiniteClockEnergy 1 M P)-
              (mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P)))-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P))) := by
  classical
  intro P hP hprime r hr hrP B
  let R := insert r P
  have hR : R.Nonempty := ⟨r,mem_insert_self r P⟩
  have hRprime : ∀ s ∈ R,s.Prime := by simpa [R] using And.intro hr hprime
  have hr0 : (0:ℝ) < r := by exact_mod_cast hr.pos
  have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr.one_lt.le
  have hρ : 0 < selfDebtDensity P := by
    apply mul_pos
    · rw [Sieve.squarefreeDensity_eq]
      positivity
    · exact prod_pos (fun s hs => div_pos (by exact_mod_cast (hprime s hs).pos) (by positivity))
  obtain ⟨c,hc,hdrop⟩ := exists_mobiusDivisor_uniform_prescribed_prime_correlation_drop
  let k := c*selfDebtDensity P*((r:ℝ)*Real.sqrt r/(r+1))/2
  have hk : 0 < k := by dsimp [k]; positivity
  let D := fun Y : ℝ => selfDebtDensity R*mobiusDivisorDilationMean R Y-
    selfDebtDensity P*mobiusDivisorDilationMean P Y
  have hDr : D r < -k := by
    have h := hdrop P hprime r hr hrP
    change c*selfDebtDensity P*((r:ℝ)*Real.sqrt r/(r+1)) ≤
      selfDebtDensity P*mobiusDivisorDilationMean P r-selfDebtDensity R*mobiusDivisorDilationMean R r at h
    dsimp [D,k] at *
    linarith only [h,hk]
  have hcont : ContinuousAt D r :=
    (((continuousOn_mobiusDivisorDilationMean R hR hRprime).continuousAt (Ioi_mem_nhds hr0)).const_mul _).sub
      (((continuousOn_mobiusDivisorDilationMean P hP hprime).continuousAt (Ioi_mem_nhds hr0)).const_mul _)
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp
    (hcont.eventually (eventually_lt_nhds hDr))
  let U := (r:ℝ)+ε/2
  have hU : (r:ℝ) < U := by dsimp [U]; linarith
  have hband : ∀ Y : ℝ,(r:ℝ) ≤ Y → Y ≤ U →
      selfDebtDensity R*mobiusDivisorDilationMean R Y-
        selfDebtDensity P*mobiusDivisorDilationMean P Y ≤ -k := by
    intro Y hlo hhi
    have hd : dist Y (r:ℝ) < ε := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
      dsimp [U] at hhi
      linarith
    exact (hεprop hd).le
  obtain ⟨a,T,ha,hrelease⟩ := relative_window_release P R hP hR hprime hRprime
    r U k hr1 hU hk hband
  have hwidth : 0 < (U-r)/(r:ℝ) := div_pos (sub_pos.mpr hU) hr0
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between hwidth)
  let N := max (B+1) (max (P.sup id+1) (max (r+1) (⌈max T (Z/(r:ℝ))⌉₊+1)))
  obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes N
  have hBp : B < p := lt_of_lt_of_le (Nat.lt_succ_self B) ((le_max_left _ _).trans hNp)
  have hSup : P.sup id < p := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hNp))
  have hrp : r < p := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNp)))
  have hceil : ⌈max T (Z/(r:ℝ))⌉₊ ≤ p := (Nat.le_succ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNp)))
  have ht : max T (Z/(r:ℝ)) ≤ (p:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpT : T ≤ (p:ℝ) := (le_max_left _ _).trans ht
  have hZp : Z ≤ (r:ℝ)*p := by
    have h := (div_le_iff₀ hr0).mp ((le_max_right _ _).trans ht)
    simpa [mul_comm] using h
  obtain ⟨q,hq,hqlo,hqhi⟩ := hZ ((r:ℝ)*p) hZp
  have hfactor : (1+(U-r)/(r:ℝ))*((r:ℝ)*p)=U*p := by field_simp; ring
  rw [hfactor] at hqhi
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpqR : (p:ℝ) < q :=
    (by nlinarith only [hr1,hp0] : (p:ℝ) ≤ (r:ℝ)*p).trans_lt hqlo
  have hpq : p < q := by exact_mod_cast hpqR
  have hpP : p ∉ P := fun hpP => (not_le_of_gt hSup) (Finset.le_sup (f:=id) hpP)
  have hqP : q ∉ P := fun hqP => (not_le_of_gt (hSup.trans hpq)) (Finset.le_sup (f:=id) hqP)
  have hpR : p ∉ R := by simp [R,hrp.ne',hpP]
  have hqR : q ∉ R := by simp [R,(hrp.trans hpq).ne',hqP]
  have hqfresh : q ∉ insert p (insert r P) := by simpa [R,hpq.ne'] using hqR
  have hg := hrelease p q hp hq hpP hqP hpR hqR hpq hpT hqlo.le hqhi.le
  let d := a/(2*(p:ℝ))
  have hd : 0 < d := by dsimp [d]; positivity
  have htwo : 2*d=a/(p:ℝ) := by dsimp [d]; ring
  have hnewP : ∀ s ∈ insert q (insert p P),s.Prime := by simpa using And.intro hq (And.intro hp hprime)
  have hnewR : ∀ s ∈ insert q (insert p R),s.Prime := by simpa using And.intro hq (And.intro hp hRprime)
  have hlim := ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log R hRprime).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime)).sub
      ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewR).sub
        (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewP))
  have hstrict : d < (selfDebtEnergy R-selfDebtEnergy P)-
      (selfDebtEnergy (insert q (insert p R))-selfDebtEnergy (insert q (insert p P))) := by
    rw [← htwo] at hg
    linarith only [hg,hd]
  refine ⟨p,q,hBp,hpq,hp,hq,hpR,hqfresh,d,hd,?_⟩
  have he := hlim.eventually (eventually_gt_nhds hstrict)
  filter_upwards [he,eventually_ge_atTop (1:ℕ)] with M hM hM1
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hden : 0 < (M:ℝ)^2*(1+Real.log M) := by positivity
  simp only [← sub_div] at hM
  have h := (le_div_iff₀ hden).mp hM.le
  simpa only [R,mul_assoc] using h

end RHTower
