import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedPrimeSelfCorrelation

/-!
# Quantitative prescribed-prime clock payment

The square of three literal delayed heads gives a Gram inequality. Combined
with the exact prime renewal law, it forces quadratic feedback from the
actual omitted-prime debt, retaining both squarefree Euler products.

For current coefficient energy K and positive omitted-prime debt delta,
actual fresh helper primes p < q pay at least
`min(delta, delta^2/K)/(128*r*p)` times the full logarithmic clock weight.
One common eventual cutoff tail carries the absolute old-core payment,
twice that payment for the prescribed-prime core, and the relative payment.
Both baselines precede all helpers. The nonpositive-debt alternative concerns
the limiting coefficient, not finite-clock payment.

This is a local quantitative producer. The ratio aperture, helper threshold
and finite-counting onset still depend on the core. Cumulative repayment,
control across changing cutoffs and paid exhaustive continuation remain open.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private lemma kernel_zero_integrable (P : Finset ℕ) {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3) (Ioi 0) := by
  apply (integrable_mobiusDivisorDilationMean_kernel P hY).of_forall_sdiff_eq_zero measurableSet_Ioi
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma kernel_zero_integral (P : Finset ℕ) (Y : ℝ) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^3)=mobiusDivisorDilationMean P Y := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma pair_scale (P : Finset ℕ) {A B : ℝ} (hB : 0<B) (x : ℝ) :
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^3 =
      B^3*(mobiusDivisorContinuousHead P ((A/B)*(B*x))*
        mobiusDivisorContinuousHead P (B*x)/(B*x)^3) := by
  rw [show A/B*(B*x)=A*x by field_simp]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma pair_integrable (P : Finset ℕ) {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3) (Ioi 0) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff _ 0 hB).mpr
    (by simpa using kernel_zero_integrable P (div_pos hA hB))
  apply IntegrableOn.congr_fun (hi.const_mul (B^3)) _ measurableSet_Ioi
  intro x _
  exact (pair_scale P hB x).symm

private lemma pair_integral (P : Finset ℕ) {A B : ℝ} (hB : 0<B) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^3)=B^2*mobiusDivisorDilationMean P (A/B) := by
  simp_rw [pair_scale P hB]
  rw [integral_const_mul,integral_comp_mul_left_Ioi
    (fun u => mobiusDivisorContinuousHead P ((A/B)*u)*mobiusDivisorContinuousHead P u/u^3) 0 hB,mul_zero,
    smul_eq_mul,kernel_zero_integral]
  field_simp

private lemma three_shift_quadratic_nonneg (P : Finset ℕ) {A : ℝ}
    (hA : 0 < A) (u v w : ℝ) :
    0 ≤ mobiusDivisorDilationMean P 1*(u^2+v^2+w^2)+
      2*(mobiusDivisorDilationMean P A/A)*(u*v+v*w)+
      2*(mobiusDivisorDilationMean P (A^2)/A^2)*u*w := by
  let J := fun a b x : ℝ =>
    mobiusDivisorContinuousHead P (a*x)*mobiusDivisorContinuousHead P (b*x)/x^3
  let f := fun x : ℝ => u*mobiusDivisorContinuousHead P x+
    v*A*mobiusDivisorContinuousHead P (A⁻¹*x)+
    w*A^2*mobiusDivisorContinuousHead P ((A^2)⁻¹*x)
  have hA2 : 0 < A^2 := pow_pos hA 2
  have hAi : 0 < A⁻¹ := inv_pos.mpr hA
  have hA2i : 0 < (A^2)⁻¹ := inv_pos.mpr hA2
  have h0 : IntegrableOn (fun x => u^2*J 1 1 x) (Ioi 0) :=
    (pair_integrable P zero_lt_one zero_lt_one).const_mul _
  have h1 : IntegrableOn (fun x => (2*u*v*A)*J 1 A⁻¹ x) (Ioi 0) :=
    (pair_integrable P zero_lt_one hAi).const_mul _
  have h2 : IntegrableOn (fun x => (2*u*w*A^2)*J 1 (A^2)⁻¹ x) (Ioi 0) :=
    (pair_integrable P zero_lt_one hA2i).const_mul _
  have h3 : IntegrableOn (fun x => (v^2*A^2)*J A⁻¹ A⁻¹ x) (Ioi 0) :=
    (pair_integrable P hAi hAi).const_mul _
  have h4 : IntegrableOn (fun x => (2*v*w*A^3)*J A⁻¹ (A^2)⁻¹ x) (Ioi 0) :=
    (pair_integrable P hAi hA2i).const_mul _
  have h5 : IntegrableOn (fun x => (w^2*A^4)*J (A^2)⁻¹ (A^2)⁻¹ x) (Ioi 0) :=
    (pair_integrable P hA2i hA2i).const_mul _
  have hexp (x : ℝ) : (f x)^2/x^3 =
      ((((u^2*J 1 1 x+(2*u*v*A)*J 1 A⁻¹ x)+
        (2*u*w*A^2)*J 1 (A^2)⁻¹ x)+(v^2*A^2)*J A⁻¹ A⁻¹ x)+
        (2*v*w*A^3)*J A⁻¹ (A^2)⁻¹ x)+(w^2*A^4)*J (A^2)⁻¹ (A^2)⁻¹ x := by
    dsimp [f,J]
    simp only [one_mul]
    ring
  have hn : 0 ≤ ∫x in Ioi (0:ℝ),(f x)^2/x^3 := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact div_nonneg (sq_nonneg _) (pow_nonneg hx.le _)
  simp_rw [hexp] at hn
  have ha5 := integral_add ((((h0.add h1).add h2).add h3).add h4) h5
  have ha4 := integral_add (((h0.add h1).add h2).add h3) h4
  have ha3 := integral_add ((h0.add h1).add h2) h3
  have ha2 := integral_add (h0.add h1) h2
  have ha1 := integral_add h0 h1
  simp only [Pi.add_apply] at ha5 ha4 ha3 ha2 ha1
  rw [ha5,ha4,ha3,ha2,ha1] at hn
  simp only [integral_const_mul,J] at hn
  rw [pair_integral P zero_lt_one,pair_integral P hAi,
    pair_integral P hA2i,pair_integral P hAi,
    pair_integral P hA2i,pair_integral P hA2i] at hn
  simp only [one_div,inv_inv,div_self (ne_of_gt hAi),
    div_self (ne_of_gt hA2i),div_self (by norm_num : (1:ℝ)≠0),
    one_pow,one_mul] at hn
  have he : A⁻¹/(A^2)⁻¹=A := by field_simp
  rw [he] at hn
  convert hn using 1
  field_simp
  ring

/-- The literal three-delay Gram inequality, uniformly in the finite core. -/
theorem mobiusDivisorDilationMean_three_shift_gram
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) {A : ℝ} (hA : 0 < A) :
    2*(mobiusDivisorDilationMean P A/A)^2 ≤
      mobiusDivisorDilationMean P 1*
        (mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P (A^2)/A^2) := by
  let K := mobiusDivisorDilationMean P 1
  let z := mobiusDivisorDilationMean P A/A
  let t := mobiusDivisorDilationMean P (A^2)/A^2
  have hK : 0 < K := mobiusDivisorDilationMean_one_pos P hP
  have hq := three_shift_quadratic_nonneg P hA K (-2*z) K
  change 0 ≤ K*(K^2+(-2*z)^2+K^2)+2*z*(K*(-2*z)+(-2*z)*K)+2*t*K*K at hq
  change 2*z^2 ≤ K*(K+t)
  by_contra hn
  have hm := mul_pos hK (sub_pos.mpr (lt_of_not_ge hn))
  nlinarith only [hq,hm]

private def debtDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1)
private def debtEnergy (P : Finset ℕ) : ℝ := ∑'n,mobiusDivisorFixedCoreBlockMass P n

private lemma density_positive (P : Finset ℕ) (hP : ∀r∈P,r.Prime) : 0<debtDensity P := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]; positivity
  · exact prod_pos (fun r hr => div_pos (by exact_mod_cast (hP r hr).pos) (by positivity))

private lemma energy_diagonal (P : Finset ℕ) (hP : ∀r∈P,r.Prime) :
    debtEnergy P=debtDensity P*mobiusDivisorDilationMean P 1 := by
  have h1 : 1∉P := fun h => Nat.not_prime_one (hP 1 h)
  have hprim (n : ℕ) (t : ℝ) : mobiusDivisorPrimeCorrelationPrimitive P 1 n t=
      2*mobiusDivisorHeadBlockPrimitive P n t := by
    simp [mobiusDivisorPrimeCorrelationPrimitive,mobiusDivisorHeadBlockPrimitive]
    ring
  have hm (n : ℕ) : mobiusDivisorPrimeCorrelationMass P 1 n=
      mobiusDivisorFixedCoreBlockMass P n := by
    simp only [mobiusDivisorPrimeCorrelationMass,mobiusDivisorFixedCoreBlockMass,hprim]
    split_ifs
    · rfl
    · rw [prod_insert h1]
      ring
  have h := hasSum_mobiusDivisorPrimeCorrelationMass_integral P hP (by omega : 0<1)
  rw [show mobiusDivisorPrimeCorrelationMass P 1=mobiusDivisorFixedCoreBlockMass P from funext hm] at h
  rw [integral_mobiusDivisorPrimeCorrelationKernel_eq_dilationMean P (by omega : 0<1),
    prod_insert h1] at h
  have he := h.tsum_eq
  convert he using 1 <;> norm_num [debtEnergy,debtDensity]
  ring

private lemma debt_formula (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {r : ℕ} (hr : r.Prime) (hrP : r∉P) :
    debtEnergy (insert r P)-debtEnergy P =
      -2*debtDensity P*Real.sqrt r/((r:ℝ)*(r+1))*mobiusDivisorDilationMean P r := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr.pos
  have he := mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hP hr hrP
  rw [show -(3/2:ℝ)=1/2-2 by norm_num,
    Real.rpow_sub hr0,← Real.sqrt_eq_rpow,Real.rpow_two,prod_insert hrP] at he
  dsimp [debtEnergy,debtDensity]
  have halg : 2*(Sieve.squarefreeDensity*((r:ℝ)/(r+1)*∏p∈P,(p:ℝ)/(p+1)))*
      (Real.sqrt r/(r:ℝ)^2)*mobiusDivisorDilationMean P r =
      2*(Sieve.squarefreeDensity*∏p∈P,(p:ℝ)/(p+1))*Real.sqrt r/((r:ℝ)*(r+1))*
        mobiusDivisorDilationMean P r := by field_simp
  rw [halg] at he
  calc
    _ = -((∑'n,mobiusDivisorFixedCoreBlockMass P n)-
      ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n) := by ring
    _ = _ := by rw [he]; ring

private lemma feedback_identity (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    {r : ℕ} (hr : r.Prime) (hrP : r∉P) :
    debtDensity P*mobiusDivisorDilationMean P r-
      debtDensity (insert r P)*mobiusDivisorDilationMean (insert r P) r =
      (mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P ((r:ℝ)^2)/(r:ℝ)^2)*
        (debtDensity P*((r:ℝ)*Real.sqrt r/(r+1))) := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr.pos
  dsimp [debtDensity]
  rw [prod_insert hrP,mobiusDivisorDilationMean_insert P hP hr hrP hr0,
    div_self hr0.ne',← pow_two]
  field_simp
  ring

/-- The actual omitted-prime debt forces quadratic feedback. Both Euler
products are retained; the bound is expressed in current energy and debt. -/
theorem mobiusDivisor_prescribed_debt_quadratic_feedback
    (P : Finset ℕ) (hP : ∀p∈P,p.Prime) {r : ℕ} (hr : r.Prime) (hrP : r∉P) :
    Real.sqrt r*((r:ℝ)+1)*
        ((∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n)-
          (∑'n,mobiusDivisorFixedCoreBlockMass P n))^2 ≤
      2*(∑'n,mobiusDivisorFixedCoreBlockMass P n)*
        ((Sieve.squarefreeDensity*∏p∈P,(p:ℝ)/(p+1))*mobiusDivisorDilationMean P r-
          (Sieve.squarefreeDensity*∏p∈insert r P,(p:ℝ)/(p+1))*
            mobiusDivisorDilationMean (insert r P) r) := by
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr.pos
  have hρ := density_positive P hP
  have hg := mobiusDivisorDilationMean_three_shift_gram P hP hr0
  have hn := mul_nonneg
    (show 0≤2*(debtDensity P)^2*(r:ℝ)*Real.sqrt r/(r+1) by positivity)
    (sub_nonneg.mpr hg)
  change Real.sqrt r*((r:ℝ)+1)*(debtEnergy (insert r P)-debtEnergy P)^2 ≤
    2*debtEnergy P*(debtDensity P*mobiusDivisorDilationMean P r-
      debtDensity (insert r P)*mobiusDivisorDilationMean (insert r P) r)
  rw [debt_formula P hP hr hrP,energy_diagonal P hP,feedback_identity P hP hr hrP]
  have he : 2*(debtDensity P*mobiusDivisorDilationMean P 1)*
        ((mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P ((r:ℝ)^2)/(r:ℝ)^2)*
          (debtDensity P*((r:ℝ)*Real.sqrt r/(r+1))))-
      Real.sqrt r*((r:ℝ)+1)*
        (-2*debtDensity P*Real.sqrt r/((r:ℝ)*(r+1))*mobiusDivisorDilationMean P r)^2 =
      (2*(debtDensity P)^2*(r:ℝ)*Real.sqrt r/(r+1))*
        (mobiusDivisorDilationMean P 1*
          (mobiusDivisorDilationMean P 1+mobiusDivisorDilationMean P ((r:ℝ)^2)/(r:ℝ)^2)-
            2*(mobiusDivisorDilationMean P r/(r:ℝ))^2) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt hr0.le]
  exact sub_nonneg.mp (he.symm ▸ hn)

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
      debtDensity R*mobiusDivisorDilationMean R Y-
        debtDensity P*mobiusDivisorDilationMean P Y ≤ -k) :
    ∃ T : ℝ, ∀p q : ℕ,p.Prime → q.Prime →
      p∉P → q∉P → p∉R → q∉R → p<q → T≤(p:ℝ) →
      L*(p:ℝ)≤q → (q:ℝ)≤U*(p:ℝ) →
      (k/(2*U^2))/(p:ℝ) ≤ (debtEnergy R-debtEnergy P)-
        (debtEnergy (insert q (insert p R))-debtEnergy (insert q (insert p P))) := by
  obtain ⟨CP,hCP,hprofileP⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile P hP hPprime
  obtain ⟨CR,hCR,hprofileR⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile R hR hRprime
  let C := CP+CR
  have hC : 0≤C := add_nonneg hCP hCR
  let c := k/(2*U^2)
  have hU : 0<U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨(C/c+1)^2,?_⟩
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
  have hmain : 2*τ*(debtDensity R*mobiusDivisorDilationMean R ((q:ℝ)/p)-
      debtDensity P*mobiusDivisorDilationMean P ((q:ℝ)/p)) ≤ -4*c := by
    have hm := mul_le_mul_of_nonneg_left hratio (show 0≤2*τ by positivity)
    have hl := mul_le_mul_of_nonneg_left hτlo (show 0≤2*k by positivity)
    have he : 4*c=2*k*(1/U^2) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  have hadd : CP/Real.sqrt p+CR/Real.sqrt p=C/Real.sqrt p := by dsimp [C]; ring
  change -(CP/Real.sqrt p) ≤ (p:ℝ)*(debtEnergy (insert q (insert p P))-debtEnergy P)-
    2*debtDensity P*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*mobiusDivisorDilationMean P ((q:ℝ)/p) at herrorP
  change (p:ℝ)*(debtEnergy (insert q (insert p R))-debtEnergy R)-
    2*debtDensity R*((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)*mobiusDivisorDilationMean R ((q:ℝ)/p) ≤
    CR/Real.sqrt p at herrorR
  apply (div_le_iff₀ hp0).mpr
  dsimp [τ] at hmain
  nlinarith only [herrorP,herrorR,hmain,hsmall,hc,hadd]

private lemma negative_window_release (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀ r ∈ P,r.Prime)
    (L U k : ℝ) (hL : 1 ≤ L) (hLU : L < U) (hk : 0 < k)
    (hW : ∀ Y : ℝ,L ≤ Y → Y ≤ U → debtDensity P*mobiusDivisorDilationMean P Y ≤ -k) :
    ∃ T : ℝ, ∀ p q : ℕ,p.Prime → q.Prime → p ∉ P → q ∉ P → p < q →
      T ≤ (p:ℝ) → L*(p:ℝ) ≤ q → (q:ℝ) ≤ U*(p:ℝ) →
      (k/(2*U^2))/(p:ℝ) ≤ (∑' n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
  obtain ⟨C,hC,hprofile⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile P hP hprime
  let c := k/(2*U^2)
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(C/c+1)^2,?_⟩
  intro p q hp hq hpP hqP hpq hpT hlo hhi
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpqR : (p:ℝ) ≤ q := by exact_mod_cast hpq.le
  have hratio := hW ((q:ℝ)/p) ((le_div_iff₀ hpR).mpr hlo) ((div_le_iff₀ hpR).mpr hhi)
  let τ := ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτlo : 1/U^2 ≤ τ := ratio_weight_lower hpR hpqR (hL.trans hLU.le) hhi
  have herror := (abs_le.mp (hprofile p q hp hq hpP hqP hpq.ne' hpq.le)).2
  have hsmall : C/Real.sqrt p < c := by
    have hroot := Real.sqrt_le_sqrt hpT
    rw [Real.sqrt_sq (by positivity : 0 ≤ C/c+1)] at hroot
    have hm := mul_le_mul_of_nonneg_left hroot hc.le
    have he : c*(C/c+1)=C+c := by field_simp
    rw [he] at hm
    exact (div_lt_iff₀ (Real.sqrt_pos.mpr hpR)).mpr (by linarith)
  have hmain : 2*τ*(debtDensity P*mobiusDivisorDilationMean P ((q:ℝ)/p)) ≤ -4*c := by
    have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*τ by positivity)
    have hl := mul_le_mul_of_nonneg_left hτlo (show 0 ≤ 2*k by positivity)
    have he : 4*c = 2*k*(1/U^2) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  apply (div_le_iff₀ hpR).mpr
  have herror' : (p:ℝ)*((∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
    ∑' n,mobiusDivisorFixedCoreBlockMass P n)-
    2*τ*(debtDensity P*mobiusDivisorDilationMean P ((q:ℝ)/p)) ≤ C/Real.sqrt p := by
    simpa only [debtDensity,τ,mul_assoc,mul_left_comm,mul_comm] using herror
  nlinarith only [herror',hmain,hsmall,hc]

/-- A source-dependent payment: the positive debt and current energy fix the
coefficient; only the actual prescribed and helper primes enter its scale. -/
def mobiusDivisorPrescribedDebtPairPayment (P : Finset ℕ) (r p : ℕ) : ℝ :=
  let K := ∑'n,mobiusDivisorFixedCoreBlockMass P n
  let δ := (∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n)-K
  min δ (δ^2/K)/(128*(r:ℝ)*p)

/-- Actual fresh helpers pay an explicit amount of both absolute clock energy
and the relative omitted-prime debt, on one common full logarithmic cutoff tail.
No sign, payment, or availability premise is assumed. -/
theorem exists_mobiusDivisorQuantitativePrescribedDebtPayment :
    ∀ P : Finset ℕ, P.Nonempty → (∀ r ∈ P,r.Prime) →
      ∀ r : ℕ, r.Prime → r ∉ P →
        (∑' n,mobiusDivisorFixedCoreBlockMass (insert r P) n) ≤
          (∑' n,mobiusDivisorFixedCoreBlockMass P n) ∨
        ∀ B : ℕ, ∃ p q : ℕ, B < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
          p ∉ insert r P ∧ q ∉ insert p (insert r P) ∧
          0 < mobiusDivisorPrescribedDebtPairPayment P r p ∧
          ∀ᶠ M : ℕ in atTop,
            mobiusDivisorPrescribedDebtPairPayment P r p*(M:ℝ)^2*(1+Real.log M) ≤
              mobiusDivisorFiniteClockEnergy 1 M P-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P)) ∧
            2*mobiusDivisorPrescribedDebtPairPayment P r p*(M:ℝ)^2*(1+Real.log M) ≤
              mobiusDivisorFiniteClockEnergy 1 M (insert r P)-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P))) ∧
            mobiusDivisorPrescribedDebtPairPayment P r p*(M:ℝ)^2*(1+Real.log M) ≤
              (mobiusDivisorFiniteClockEnergy 1 M (insert r P)-
                mobiusDivisorFiniteClockEnergy 1 M P)-
              (mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P)))-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P))) := by
  classical
  intro P hP hprime r hr hrP
  by_cases hpaid : debtEnergy (insert r P) ≤ debtEnergy P
  · exact Or.inl hpaid
  right
  intro B
  let R := insert r P
  let K := debtEnergy P
  let δ := debtEnergy R-debtEnergy P
  let b := min δ (δ^2/K)
  let k := (r:ℝ)*b/8
  have hR : R.Nonempty := ⟨r,mem_insert_self r P⟩
  have hRprime : ∀s∈R,s.Prime := by simpa [R] using And.intro hr hprime
  have hr0 : (0:ℝ)<r := by exact_mod_cast hr.pos
  have hr1 : (1:ℝ)≤r := by exact_mod_cast hr.one_lt.le
  have hρ := density_positive P hprime
  have hK : 0<K := by
    dsimp [K]
    rw [energy_diagonal P hprime]
    exact mul_pos hρ (mobiusDivisorDilationMean_one_pos P hprime)
  have hδ : 0<δ := sub_pos.mpr (lt_of_not_ge hpaid)
  have hb : 0<b := lt_min hδ (div_pos (pow_pos hδ 2) hK)
  have hk : 0<k := by dsimp [k]; positivity
  have hs1 : 1≤Real.sqrt (r:ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hr1
  have hc : (r:ℝ)≤Real.sqrt r*((r:ℝ)+1) := by nlinarith only [hr0,hs1]
  have hδc : δ*(Real.sqrt r*((r:ℝ)+1)) =
      -2*(debtDensity P*mobiusDivisorDilationMean P r) := by
    dsimp [δ,R]
    rw [debt_formula P hprime hr hrP]
    have hs := Real.sq_sqrt hr0.le
    field_simp
    rw [hs]
  have hDrP : debtDensity P*mobiusDivisorDilationMean P r < -k := by
    have h1 := mul_le_mul_of_nonneg_left (min_le_left δ (δ^2/K)) hr0.le
    have h2 := mul_le_mul_of_nonneg_left hc hδ.le
    change (r:ℝ)*b≤(r:ℝ)*δ at h1
    dsimp [k] at hk ⊢
    nlinarith only [h1,h2,hδc,hk]
  let D := fun Y : ℝ => debtDensity R*mobiusDivisorDilationMean R Y-
    debtDensity P*mobiusDivisorDilationMean P Y
  have hDr : D r < -k := by
    have hf := mobiusDivisor_prescribed_debt_quadratic_feedback P hprime hr hrP
    have hf' : Real.sqrt r*((r:ℝ)+1)*δ^2 ≤ 2*K*(-D r) := by
      simpa only [δ,K,R,debtEnergy,debtDensity,D,neg_sub] using hf
    have hb2 : b*K≤δ^2 := (le_div_iff₀ hK).mp (min_le_right δ (δ^2/K))
    have h1 := mul_le_mul_of_nonneg_left hb2 hr0.le
    have h2 := mul_le_mul_of_nonneg_right hc (sq_nonneg δ)
    have hKG : K*((r:ℝ)*b) ≤ K*(2*(-D r)) := by nlinarith only [hf',h1,h2]
    have hG : (r:ℝ)*b≤2*(-D r) := by
      by_contra h
      have hm := mul_pos hK (sub_pos.mpr (lt_of_not_ge h))
      nlinarith only [hKG,hm]
    dsimp [k] at hk ⊢
    linarith only [hG,hk]
  have hcontP : ContinuousAt (fun Y => debtDensity P*mobiusDivisorDilationMean P Y) r :=
    ((continuousOn_mobiusDivisorDilationMean P hP hprime).continuousAt (Ioi_mem_nhds hr0)).const_mul _
  have hcont : ContinuousAt D r :=
    (((continuousOn_mobiusDivisorDilationMean R hR hRprime).continuousAt (Ioi_mem_nhds hr0)).const_mul _).sub hcontP
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp
    ((hcontP.eventually (eventually_lt_nhds hDrP)).and
      (hcont.eventually (eventually_lt_nhds hDr)))
  let U := (r:ℝ)+min ε (r:ℝ)/2
  have hmin : 0 < min ε (r:ℝ) := lt_min hε hr0
  have hU : (r:ℝ)<U := by dsimp [U]; linarith only [hmin]
  have hUbound : U≤2*(r:ℝ) := by dsimp [U]; linarith only [min_le_right ε (r:ℝ),hr0]
  have hband : ∀Y : ℝ,(r:ℝ)≤Y → Y≤U →
      debtDensity P*mobiusDivisorDilationMean P Y≤-k ∧ D Y≤-k := by
    intro Y hlo hhi
    have hd : dist Y (r:ℝ)<ε := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
      dsimp [U] at hhi
      linarith only [hhi,min_le_left ε (r:ℝ),hε]
    exact ⟨(hεprop hd).1.le,(hεprop hd).2.le⟩
  obtain ⟨TP,hreleaseP⟩ := negative_window_release P hP hprime
    r U k hr1 hU hk (fun Y hlo hhi => (hband Y hlo hhi).1)
  obtain ⟨T,hrelease⟩ := relative_window_release P R hP hR hprime hRprime
    r U k hr1 hU hk (fun Y hlo hhi => (hband Y hlo hhi).2)

  have hwidth : 0 < (U-r)/(r:ℝ) := div_pos (sub_pos.mpr hU) hr0
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between hwidth)
  let N := max (B+1) (max (P.sup id+1) (max (r+1) (⌈max (max T TP) (Z/(r:ℝ))⌉₊+1)))
  obtain ⟨p,hNp,hp⟩ := Nat.exists_infinite_primes N
  have hBp : B < p := lt_of_lt_of_le (Nat.lt_succ_self B) ((le_max_left _ _).trans hNp)
  have hSup : P.sup id < p := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hNp))
  have hrp : r < p := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNp)))
  have hceil : ⌈max (max T TP) (Z/(r:ℝ))⌉₊ ≤ p := (Nat.le_succ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hNp)))
  have ht : max (max T TP) (Z/(r:ℝ)) ≤ (p:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpTT : max T TP ≤ (p:ℝ) := (le_max_left _ _).trans ht
  have hpT : T ≤ (p:ℝ) := (le_max_left _ _).trans hpTT
  have hpTP : TP ≤ (p:ℝ) := (le_max_right _ _).trans hpTT
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
  have hgP := hreleaseP p q hp hq hpP hqP hpq hpTP hqlo.le hqhi.le

  let d := mobiusDivisorPrescribedDebtPairPayment P r p
  have hddef : d=b/(128*(r:ℝ)*p) := rfl
  have hd : 0<d := by rw [hddef]; positivity
  have hU0 : 0<U := hr0.trans hU
  have hcoef : b/(64*(r:ℝ))≤k/(2*U^2) := by
    apply (div_le_div_iff₀ (by positivity : 0<64*(r:ℝ)) (by positivity : 0<2*U^2)).mpr
    have hsq : U^2≤4*(r:ℝ)^2 := by nlinarith only [hUbound,hU0,hr0]
    have hm := mul_le_mul_of_nonneg_left hsq hb.le
    dsimp [k]
    nlinarith only [hm]
  have hdgain : 2*d≤(k/(2*U^2))/(p:ℝ) := by
    calc
      2*d = (b/(64*(r:ℝ)))/(p:ℝ) := by rw [hddef]; ring
      _ ≤ _ := div_le_div_of_nonneg_right hcoef hp0.le

  have hnewP : ∀ s ∈ insert q (insert p P),s.Prime := by simpa using And.intro hq (And.intro hp hprime)
  have hnewR : ∀ s ∈ insert q (insert p R),s.Prime := by simpa using And.intro hq (And.intro hp hRprime)
  have hlim := ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log R hRprime).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime)).sub
      ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewR).sub
        (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewP))
  have hlimP := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewP)
  have hstrict : d < (debtEnergy R-debtEnergy P)-
      (debtEnergy (insert q (insert p R))-debtEnergy (insert q (insert p P))) := by
    linarith only [hg,hdgain,hd]
  have hstrictP : d < (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
      (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n) := by
    linarith only [hgP,hdgain,hd]
  refine ⟨p,q,hBp,hpq,hp,hq,hpR,hqfresh,hd,?_⟩
  have he := hlim.eventually (eventually_gt_nhds hstrict)
  have heP := hlimP.eventually (eventually_gt_nhds hstrictP)
  filter_upwards [he,heP,eventually_ge_atTop (1:ℕ)] with M hM hMP hM1
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hden : 0 < (M:ℝ)^2*(1+Real.log M) := by positivity
  simp only [← sub_div] at hM hMP
  have hrel := (le_div_iff₀ hden).mp hM.le
  have habs := (le_div_iff₀ hden).mp hMP.le
  have hrel' : d*(M:ℝ)^2*(1+Real.log M) ≤
      (mobiusDivisorFiniteClockEnergy 1 M (insert r P)-mobiusDivisorFiniteClockEnergy 1 M P)-
        (mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P)))-
          mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P))) := by
    simpa only [R,mul_assoc] using hrel
  have habs' : d*(M:ℝ)^2*(1+Real.log M) ≤ mobiusDivisorFiniteClockEnergy 1 M P-
      mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P)) := by
    simpa only [mul_assoc] using habs
  exact ⟨habs',by linarith only [habs',hrel'],hrel'⟩

end RHTower
