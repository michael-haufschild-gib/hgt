import GaloisForLFunctions.RHTower.MobiusDivisorPrimePairRatioProfile

/-!
# Actual prime pairs with ordered reserves for prescribed-prime debt

The exact diagonal energy identifies the relative source sign. A common
fresh insertion reverses that sign on a prime-ratio interval. Actual primes
in this interval release strictly more energy after the prescribed prime
than before it, so their pair decreases the complete inherited debt.
All three preparation prefixes have arbitrarily small all-cutoff cost.

The theorem produces local debt reduction after preparation. Payment of the
entire debt and an exhaustive prime history remain separate open problems.
-/

noncomputable section
open Finset Set Filter Topology
namespace RHTower

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

private lemma inserted_density (P : Finset ℕ) {a : ℕ} (ha : a∉P) :
    debtDensity (insert a P)=(a:ℝ)/(a+1)*debtDensity P := by
  simp only [debtDensity,prod_insert ha]
  ring

private lemma relative_negative_band (P R : Finset ℕ)
    (hP : P.Nonempty) (hR : R.Nonempty)
    (hPprime : ∀r∈P,r.Prime) (hRprime : ∀r∈R,r.Prime)
    (hdebt : debtEnergy P < debtEnergy R) :
    ∃η c T : ℝ,0<η ∧ 0<c ∧ ∀a : ℕ,a.Prime → a∉P → a∉R → T≤(a:ℝ) →
      ∀Y : ℝ,(a:ℝ)≤Y → Y≤(1+η)*(a:ℝ) →
        debtDensity (insert a R)*mobiusDivisorDilationMean (insert a R) Y-
          debtDensity (insert a P)*mobiusDivisorDilationMean (insert a P) Y ≤
            -c*Real.sqrt a := by
  let D : ℝ→ℝ := fun Y => debtDensity R*mobiusDivisorDilationMean R Y-
    debtDensity P*mobiusDivisorDilationMean P Y
  have hD : 0<D 1 := by
    dsimp [D]
    rw [← energy_diagonal P hPprime,← energy_diagonal R hRprime]
    linarith
  have hcP := (continuousOn_mobiusDivisorDilationMean P hP hPprime).continuousAt
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  have hcR := (continuousOn_mobiusDivisorDilationMean R hR hRprime).continuousAt
    (Ioi_mem_nhds (by norm_num : (0:ℝ)<1))
  have hc : ContinuousAt D 1 := (hcR.const_mul _).sub (hcP.const_mul _)
  have he := hc.eventually (eventually_gt_nhds (show D 1/2<D 1 by linarith))
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp he
  obtain ⟨CP,hCP,hboundP⟩ := exists_bound_mobiusDivisorDilationMean_insert_ratio P hP hPprime
  obtain ⟨CR,hCR,hboundR⟩ := exists_bound_mobiusDivisorDilationMean_insert_ratio R hR hRprime
  have hρP := density_positive P hPprime
  have hρR := density_positive R hRprime
  let C := debtDensity R*CR+debtDensity P*CP
  let c := D 1/8
  have hC : 0≤C := by dsimp [C]; positivity
  have hc0 : 0<c := by dsimp [c]; positivity
  refine ⟨ε/2,c,(C/(2*c)+1)^2,by positivity,hc0,?_⟩
  intro a ha haP haR haT Y hlo hhi
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha.pos
  have ha1 : (1:ℝ)≤a := by exact_mod_cast ha.one_lt.le
  have hY1 := ha1.trans hlo
  have hzlo : 1≤Y/(a:ℝ) := (le_div_iff₀ ha0).mpr (by simpa using hlo)
  have hzhi : Y/(a:ℝ)≤1+ε/2 := (div_le_iff₀ ha0).mpr hhi
  have hd := hεprop (show dist (Y/(a:ℝ)) 1<ε by
    rw [Real.dist_eq,abs_of_nonneg (by linarith : 0≤Y/(a:ℝ)-1)]
    linarith)
  have hroot := Real.sqrt_le_sqrt haT
  rw [Real.sqrt_sq (by positivity : 0≤C/(2*c)+1)] at hroot
  have hmargin : C<2*c*Real.sqrt a := by
    have hh := mul_le_mul_of_nonneg_left hroot (show 0≤2*c by positivity)
    have hh' : 2*c*(C/(2*c)+1)=C+2*c := by field_simp
    rw [hh'] at hh
    linarith
  have hRP := mul_le_mul_of_nonneg_left (abs_le.mp (hboundR a ha haR Y hY1)).2 hρR.le
  have hPP := mul_le_mul_of_nonneg_left (abs_le.mp (hboundP a ha haP Y hY1)).1 hρP.le
  have hd' := mul_le_mul_of_nonneg_left hd.le (Real.sqrt_nonneg (a:ℝ))
  have hraw : debtDensity R*mobiusDivisorDilationMean (insert a R) Y-
      debtDensity P*mobiusDivisorDilationMean (insert a P) Y ≤ -2*c*Real.sqrt a := by
    dsimp [C,D,c] at *
    nlinarith only [hRP,hPP,hd',hmargin]
  have hf : (1/2:ℝ)≤(a:ℝ)/(a+1) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<a+1)).mpr
    linarith
  have hm := mul_le_mul_of_nonneg_left hraw (show 0≤(a:ℝ)/(a+1) by positivity)
  have hl := mul_le_mul_of_nonneg_right hf (show 0≤2*c*Real.sqrt a by positivity)
  rw [inserted_density R haR,inserted_density P haP]
  nlinarith only [hm,hl]

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

private lemma negative_window_release (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀ r ∈ P,r.Prime)
    (L U k : ℝ) (hL : 1 ≤ L) (hLU : L < U) (hk : 0 < k)
    (hW : ∀ Y : ℝ,L ≤ Y → Y ≤ U → mobiusDivisorDilationMean P Y ≤ -k) :
    ∃ c T : ℝ,0 < c ∧ ∀ p q : ℕ,p.Prime → q.Prime → p ∉ P → q ∉ P → p < q →
      T ≤ (p:ℝ) → L*(p:ℝ) ≤ q → (q:ℝ) ≤ U*(p:ℝ) →
      c/(p:ℝ) ≤ (∑' n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
  obtain ⟨C,hC,hprofile⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile P hP hprime
  let ρ := Sieve.squarefreeDensity*∏ r ∈ P,(r:ℝ)/(r+1)
  have hρ : 0 < ρ := by
    apply mul_pos
    · rw [Sieve.squarefreeDensity_eq]; positivity
    · exact prod_pos (fun r hr => div_pos (by exact_mod_cast (hprime r hr).pos) (by positivity))
  let c := ρ*k/(2*U^2)
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,(C/c+1)^2,hc,?_⟩
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
  have hmain : 2*ρ*τ*mobiusDivisorDilationMean P ((q:ℝ)/p) ≤ -4*c := by
    have hm := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2*ρ*τ by positivity)
    have hl := mul_le_mul_of_nonneg_left hτlo (show 0 ≤ 2*ρ*k by positivity)
    have he : 4*c = 2*ρ*k*(1/U^2) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  apply (div_le_iff₀ hpR).mpr
  have herror' : (p:ℝ)*((∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
    ∑' n,mobiusDivisorFixedCoreBlockMass P n)-
    2*ρ*τ*mobiusDivisorDilationMean P ((q:ℝ)/p) ≤ C/Real.sqrt p := by
    simpa only [ρ,τ,mul_assoc] using herror
  nlinarith only [herror',hmain,hsmall,hc]


private lemma relative_window_release (P R : Finset ℕ)
    (hP : P.Nonempty) (hR : R.Nonempty)
    (hPprime : ∀r∈P,r.Prime) (hRprime : ∀r∈R,r.Prime)
    (L U k : ℝ) (hL : 1≤L) (hLU : L<U) (hk : 0<k)
    (hW : ∀Y : ℝ,L≤Y → Y≤U →
      debtDensity R*mobiusDivisorDilationMean R Y-
        debtDensity P*mobiusDivisorDilationMean P Y ≤ -k) :
    ∃c T : ℝ,0<c ∧ ∀p q : ℕ,p.Prime → q.Prime →
      p∉P → q∉P → p∉R → q∉R → p<q → T≤(p:ℝ) →
      L*(p:ℝ)≤q → (q:ℝ)≤U*(p:ℝ) →
      c/(p:ℝ) ≤ (debtEnergy R-debtEnergy P)-
        (debtEnergy (insert q (insert p R))-debtEnergy (insert q (insert p P))) := by
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

private lemma sample_vanish (P : Finset ℕ) {M r : ℕ} (hr : 0<r) (hMr : M≤r) :
    mobiusDivisorInterpolatedFibre M r P ∅=0 := by
  have h0 : mobiusDivisorSelectionFibre 0 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  have h1 : mobiusDivisorSelectionFibre 1 P ∅=0 := by
    simp [mobiusDivisorSelectionFibre, mobiusDivisorSelectionIndices, subsetLabelFibre]
  rcases hMr.eq_or_lt with rfl | hlt
  · have hw : divisorPrimeClipWeight M M=0 := by simp [divisorPrimeClipWeight, Nat.div_self hr]
    simp [mobiusDivisorInterpolatedFibre, Nat.div_self hr, hw, h1]
  · simp [mobiusDivisorInterpolatedFibre, Nat.div_eq_of_lt hlt, h0, h1]

private lemma common_prime_cost (P : Finset ℕ) (hP : ∀ q ∈ P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (M : ℕ) :
    mobiusDivisorSelectionEnergy M (insert p P) ≤ mobiusDivisorSelectionEnergy M P+
      (2*((3/5:ℝ)*2^(P.card-1))^2/(p:ℝ))*(M:ℝ)^2 := by
  let S := fixedCoreSquarefreeIndices (insert p P) M
  have he : mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P)=
      ∑ r ∈ S,mobiusDivisorPrimeCorrelationTerm P p M r := by
    rw [mobiusDivisorSelectionEnergy_prime_release_eq_correlation P hp hpP M]
    simp only [S,mobiusDivisorPrimeCorrelationTerm,mul_sum,mul_assoc]
  have hfilter : (∑ r ∈ S,|mobiusDivisorPrimeCorrelationTerm P p M r|)=
      ∑ r ∈ S.filter (fun r => p ≤ M/r),|mobiusDivisorPrimeCorrelationTerm P p M r| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro r hr hnot
    have hr0 : 0 < r := (mem_Icc.mp (mem_filter.mp hr).1).1
    have hlt : M < p*r := by
      have hh : ¬p ≤ M/r := fun h => hnot (mem_filter.mpr ⟨hr,h⟩)
      have hh' : ¬p*r ≤ M := fun h => hh ((Nat.le_div_iff_mul_le hr0).mpr h)
      omega
    rw [mobiusDivisorPrimeCorrelationTerm,
      sample_vanish P (Nat.mul_pos hp.pos hr0) hlt.le,mul_zero,abs_zero]
  have hb := mobiusDivisorPrimeCorrelation_absolute_tail_le P hP hp hpP M hp.pos
  have ha : |mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P)| ≤
      (2*((3/5:ℝ)*2^(P.card-1))^2/(p:ℝ))*(M:ℝ)^2 := by
    rw [he]
    exact (abs_sum_le_sum_abs _ _).trans (by rw [hfilter]; exact hb)
  have hn := neg_le_abs (mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M (insert p P))
  linarith only [ha,hn]

private lemma uniform_insertion_threshold (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℕ,∀ P : Finset ℕ,P.card ≤ K → (∀ r ∈ P,r.Prime) →
      ∀ p : ℕ,p.Prime → p ∉ P → A ≤ p → ∀ M : ℕ,
      mobiusDivisorSelectionEnergy M (insert p P) ≤ mobiusDivisorSelectionEnergy M P+ε*(M:ℝ)^2 := by
  let C : ℝ := 2*((3/5:ℝ)*2^K)^2
  obtain ⟨A,hA⟩ := exists_nat_gt (C/ε)
  refine ⟨A,fun P hPK hP p hp hpP hAp M => ?_⟩
  have hcoeff : 2*((3/5:ℝ)*2^(P.card-1))^2 ≤ C := by
    dsimp [C]
    gcongr
    · norm_num
    · omega
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hbound : C/ε < (p:ℝ) := hA.trans_le (by exact_mod_cast hAp)
  have hsmall : C/(p:ℝ) ≤ ε := by
    apply (div_le_iff₀ hp0).mpr
    have h := (div_lt_iff₀ hε).mp hbound
    linarith
  have h := common_prime_cost P hP hp hpP M
  have hc := (div_le_div_of_nonneg_right hcoeff hp0.le).trans hsmall
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (M:ℝ))
  linarith only [h,hm]


private lemma tail_gain (P R : Finset ℕ) (hP : ∀r∈P,r.Prime) (hR : ∀r∈R,r.Prime)
    {c : ℝ} (hc : 0<c) (hE : 2*c≤debtEnergy P-debtEnergy R) :
    ∀ᶠM : ℕ in atTop,c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M P-mobiusDivisorSelectionEnergy M R := by
  have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq P hP).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq R hR)
  have hlt : c<debtEnergy P-debtEnergy R := by linarith
  have he := ht.eventually (eventually_gt_nhds hlt)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
  have hMR : (0:ℝ)<M := by exact_mod_cast hM0
  simp only [← sub_div] at hM
  exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

private lemma tail_relative_gain (P R S T : Finset ℕ)
    (hP : ∀r∈P,r.Prime) (hR : ∀r∈R,r.Prime)
    (hS : ∀r∈S,r.Prime) (hT : ∀r∈T,r.Prime)
    {c : ℝ} (hc : 0<c) (hE : 2*c≤(debtEnergy R-debtEnergy P)-(debtEnergy T-debtEnergy S)) :
    ∀ᶠM : ℕ in atTop,c*(M:ℝ)^2 ≤
      (mobiusDivisorSelectionEnergy M R-mobiusDivisorSelectionEnergy M P)-
      (mobiusDivisorSelectionEnergy M T-mobiusDivisorSelectionEnergy M S) := by
  have ht := ((tendsto_mobiusDivisorSelectionEnergy_div_sq R hR).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq P hP)).sub
    ((tendsto_mobiusDivisorSelectionEnergy_div_sq T hT).sub
      (tendsto_mobiusDivisorSelectionEnergy_div_sq S hS))
  have hlt : c<(debtEnergy R-debtEnergy P)-(debtEnergy T-debtEnergy S) := by linarith
  have he := ht.eventually (eventually_gt_nhds hlt)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
  have hMR : (0:ℝ)<M := by exact_mod_cast hM0
  simp only [← sub_div] at hM
  exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

/-- Every prescribed-prime coefficient debt is already nonpositive or admits
actual, arbitrarily distant preparations and reserve pairs with strictly larger
release after that prime. Every preparation prefix has an arbitrarily small
all-cutoff energy cost in both states. The ordered reserves strictly decrease
the actual prescribed-prime debt on one common eventual cutoff tail. -/
theorem exists_mobiusDivisorPrescribedDebtReserveProducer :
    ∀ P : Finset ℕ,P.Nonempty → (∀r∈P,r.Prime) → ∀ r : ℕ,r.Prime → r∉P →
      (∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n) ≤
        (∑'n,mobiusDivisorFixedCoreBlockMass P n) ∨
      ∀ ε : ℝ,0<ε → ∀ B : ℕ,∃ a : ℕ,B<a ∧ a.Prime ∧ a∉insert r P ∧
        ∀ H : ℕ,∃ p q : ℕ,H≤p ∧ a<p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
          p∉insert a (insert r P) ∧ q∉insert p (insert a (insert r P)) ∧
          (∀ M : ℕ,∀ S ∈ ({P,insert r P} : Finset (Finset ℕ)),
            mobiusDivisorSelectionEnergy M (insert a S) ≤ mobiusDivisorSelectionEnergy M S+ε*(M:ℝ)^2 ∧
            mobiusDivisorSelectionEnergy M (insert p (insert a S)) ≤ mobiusDivisorSelectionEnergy M S+ε*(M:ℝ)^2 ∧
            mobiusDivisorSelectionEnergy M (insert q (insert p (insert a S))) ≤ mobiusDivisorSelectionEnergy M S+ε*(M:ℝ)^2) ∧
          ∃ c : ℝ,0<c ∧ ∀ᶠ M : ℕ in atTop,
            c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert a P)-
              mobiusDivisorSelectionEnergy M (insert q (insert p (insert a P))) ∧
            c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert a (insert r P))-
              mobiusDivisorSelectionEnergy M (insert q (insert p (insert a (insert r P)))) ∧
            c*(M:ℝ)^2 ≤
              (mobiusDivisorSelectionEnergy M (insert a (insert r P))-
                mobiusDivisorSelectionEnergy M (insert a P))-
              (mobiusDivisorSelectionEnergy M (insert q (insert p (insert a (insert r P))))-
                mobiusDivisorSelectionEnergy M (insert q (insert p (insert a P)))) := by
  classical
  intro P hP hprime r hr hrP
  by_cases hdebt : debtEnergy (insert r P)≤debtEnergy P
  · exact Or.inl hdebt
  right
  intro ε hε B
  let R := insert r P
  have hRprime : ∀t∈R,t.Prime := by simpa [R] using And.intro hr hprime
  have hR : R.Nonempty := insert_nonempty _ _
  obtain ⟨η₀,c₀,T₀,hη₀,hc₀,hband₀⟩ := exists_mobiusDivisorDilationMean_insert_negative_band P hP hprime
  obtain ⟨η₁,c₁,T₁,hη₁,hc₁,hband₁⟩ := relative_negative_band P R hP hR hprime hRprime (lt_of_not_ge hdebt)
  let η := min η₀ η₁
  have hη : 0<η := lt_min hη₀ hη₁
  obtain ⟨A,hcost⟩ := uniform_insertion_threshold (R.card+2) (ε/3) (by positivity)
  obtain ⟨a,haBound,ha⟩ := Nat.exists_infinite_primes (B+R.sup id+A+⌈max T₀ T₁⌉₊+1)
  have hBa : B<a := by omega
  have hAa : A≤a := by omega
  have hasup : R.sup id<a := by omega
  have haT : max T₀ T₁≤(a:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈max T₀ T₁⌉₊≤a by omega))
  have haR : a∉R := by
    intro h
    have hh : a≤R.sup id := Finset.le_sup (f:=id) h
    omega
  have haP : a∉P := fun h => haR (mem_insert_of_mem h)
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha.pos
  have ha1 : (1:ℝ)≤a := by exact_mod_cast ha.one_lt.le
  have hPa : ∀t∈insert a P,t.Prime := by simpa using And.intro ha hprime
  have hRa : ∀t∈insert a R,t.Prime := by simpa using And.intro ha hRprime
  let U := (1+η)*(a:ℝ)
  have haU : (a:ℝ)<U := by dsimp [U]; nlinarith only [mul_pos hη ha0]
  have hU₀ : U≤(1+η₀)*(a:ℝ) := by
    dsimp [U,η]
    exact mul_le_mul_of_nonneg_right (by linarith only [min_le_left η₀ η₁]) ha0.le
  have hU₁ : U≤(1+η₁)*(a:ℝ) := by
    dsimp [U,η]
    exact mul_le_mul_of_nonneg_right (by linarith only [min_le_right η₀ η₁]) ha0.le
  obtain ⟨d₀,V₀,hd₀,hrelease₀⟩ := negative_window_release (insert a P) (insert_nonempty _ _) hPa
    a U (c₀*Real.sqrt a) ha1 haU (mul_pos hc₀ (Real.sqrt_pos.mpr ha0)) (by
      intro Y hlo hhi
      have h := hband₀ a ha haP ((le_max_left _ _).trans haT) Y hlo (hhi.trans hU₀)
      simpa only [neg_mul] using h)
  obtain ⟨d₁,V₁,hd₁,hrelease₁⟩ := relative_window_release (insert a P) (insert a R)
    (insert_nonempty _ _) (insert_nonempty _ _) hPa hRa
    a U (c₁*Real.sqrt a) ha1 haU (mul_pos hc₁ (Real.sqrt_pos.mpr ha0)) (by
      intro Y hlo hhi
      have h := hband₁ a ha haP haR ((le_max_right _ _).trans haT) Y hlo (hhi.trans hU₁)
      simpa only [neg_mul] using h)
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between hη)
  refine ⟨a,hBa,ha,haR,?_⟩
  intro H
  obtain ⟨p,hpBound,hp⟩ := Nat.exists_infinite_primes (H+a+⌈max V₀ (max V₁ Z)⌉₊+1)
  have hHp : H≤p := by omega
  have hap : a<p := by omega
  have hpV : max V₀ (max V₁ Z)≤(p:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast (show ⌈max V₀ (max V₁ Z)⌉₊≤p by omega))
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpa : (p:ℝ)≤(a:ℝ)*(p:ℝ) := by simpa using mul_le_mul_of_nonneg_right ha1 hp0.le
  have hZp : Z≤(p:ℝ) := (le_max_right V₁ Z).trans ((le_max_right _ _).trans hpV)
  obtain ⟨q,hq,hqlo,hqhi⟩ := hZ ((a:ℝ)*(p:ℝ)) (hZp.trans hpa)
  have hpq : p<q := by exact_mod_cast hpa.trans_lt hqlo
  have hqhi' : (q:ℝ)≤U*(p:ℝ) := by dsimp [U]; nlinarith only [hqhi.le]
  have hpRa : p∉insert a R := by
    intro h
    rcases mem_insert.mp h with h | h
    · omega
    · have hh : p≤R.sup id := Finset.le_sup (f:=id) h; omega
  have hqRap : q∉insert p (insert a R) := by
    intro h
    rcases mem_insert.mp h with h | h
    · omega
    rcases mem_insert.mp h with h | h
    · omega
    · have hh : q≤R.sup id := Finset.le_sup (f:=id) h; omega
  have hsub : insert a P⊆insert a R := by
    intro t ht
    rcases mem_insert.mp ht with rfl | ht
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_insert_of_mem ht)
  have hpPa : p∉insert a P := fun h => hpRa (hsub h)
  have hqRa : q∉insert a R := fun h => hqRap (mem_insert_of_mem h)
  have hqPa : q∉insert a P := fun h => hqRa (hsub h)
  have hcoeff₀ := hrelease₀ p q hp hq hpPa hqPa hpq ((le_max_left _ _).trans hpV) hqlo.le hqhi'
  have hcoeff₁ := hrelease₁ p q hp hq hpPa hqPa hpRa hqRa hpq
    ((le_max_left V₁ Z).trans ((le_max_right _ _).trans hpV)) hqlo.le hqhi'
  let c := min d₀ d₁/(2*(p:ℝ))
  have hc : 0<c := div_pos (lt_min hd₀ hd₁) (by positivity)
  have hc₀ : 2*c≤d₀/(p:ℝ) := by
    calc
      _ = min d₀ d₁/(p:ℝ) := by dsimp [c]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (min_le_left _ _) hp0.le
  have hc₁ : 2*c≤d₁/(p:ℝ) := by
    calc
      _ = min d₀ d₁/(p:ℝ) := by dsimp [c]; ring
      _ ≤ _ := div_le_div_of_nonneg_right (min_le_right _ _) hp0.le
  refine ⟨p,q,hHp,hap,hpq,hp,hq,hpRa,hqRap,?_,c,hc,?_⟩
  · intro M S hS
    have hSR : S⊆R := by
      rcases mem_insert.mp hS with rfl | hS
      · exact subset_insert _ _
      · have he : S=R := mem_singleton.mp hS
        subst S
        exact Finset.Subset.rfl
    have hSprime : ∀t∈S,t.Prime := fun t ht => hRprime t (hSR ht)
    have haS : a∉S := fun h => haR (hSR h)
    have hSa : insert a S⊆insert a R := insert_subset_insert a hSR
    have hpSa : p∉insert a S := fun h => hpRa (hSa h)
    have hSap : insert p (insert a S)⊆insert p (insert a R) := insert_subset_insert p hSa
    have hqSap : q∉insert p (insert a S) := fun h => hqRap (hSap h)
    have hSaprime : ∀t∈insert a S,t.Prime := by simpa using And.intro ha hSprime
    have hSapprime : ∀t∈insert p (insert a S),t.Prime := by simpa using And.intro hp hSaprime
    have hcard := Finset.card_le_card hSR
    have hcarda := card_insert_le a S
    have hcardp := card_insert_le p (insert a S)
    have h₀ := hcost S (by omega) hSprime a ha haS hAa M
    have h₁ := hcost (insert a S) (by omega) hSaprime p hp hpSa (hAa.trans hap.le) M
    have h₂ := hcost (insert p (insert a S)) (by omega) hSapprime q hq hqSap
      (hAa.trans (hap.le.trans hpq.le)) M
    have hm := mul_nonneg hε.le (sq_nonneg (M:ℝ))
    constructor
    · nlinarith only [h₀,hm]
    constructor <;> nlinarith only [h₀,h₁,h₂,hm]
  · have hPap : ∀t∈insert p (insert a P),t.Prime := by simpa using And.intro hp hPa
    have hRap : ∀t∈insert p (insert a R),t.Prime := by simpa using And.intro hp hRa
    have hPapq : ∀t∈insert q (insert p (insert a P)),t.Prime := by simpa using And.intro hq hPap
    have hRapq : ∀t∈insert q (insert p (insert a R)),t.Prime := by simpa using And.intro hq hRap
    have htail₀ := tail_gain _ _ hPa hPapq hc (hc₀.trans hcoeff₀)
    have htail₁ := tail_relative_gain _ _ _ _ hPa hRa hPapq hRapq hc (hc₁.trans hcoeff₁)
    filter_upwards [htail₀,htail₁] with M hM₀ hM₁
    refine ⟨hM₀,?_,hM₁⟩
    have hm := mul_nonneg hc.le (sq_nonneg (M:ℝ))
    change c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert a R)-
      mobiusDivisorSelectionEnergy M (insert q (insert p (insert a R)))
    linarith only [hM₀,hM₁,hm]

end RHTower
