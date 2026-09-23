import GaloisForLFunctions.RHTower.MobiusDivisorPrescribedPrimeSelfCorrelation

/-!
# Direct simultaneous descent of prescribed-prime clock debt

A positive prescribed-prime coefficient debt fixes the sign of the actual
head pairing at that prime's ratio. The uniform self-correlation drop then
supplies a common interval where both the absolute and relative pairings
have the payment sign. Two actual fresh primes in this interval decrease
both absolute energies and the relative debt, measured before either helper.

The full logarithmic finite clock weight is retained on one common eventual
tail. The alternative is stated in terms of the limiting coefficient, not
finite-clock payment. This local construction does not prove cumulative
repayment, bounded intermediate energies, or exhaustive continuation.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private def selfDebtDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏p∈P,(p:ℝ)/(p+1)

private def selfDebtEnergy (P : Finset ℕ) : ℝ :=
  ∑' n,mobiusDivisorFixedCoreBlockMass P n

private lemma ratio_weight_lower {p q U : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hU : 1 ≤ U) (hqU : q ≤ U*p) : 1/U^(2 : ℕ) ≤ (p/q)*Real.sqrt (p/q) := by
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
  let c := k/(2*U^(2 : ℕ))
  have hU : 0<U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,(C/c+1)^(2 : ℕ),hc,?_⟩
  intro p q hp hq hpP hqP hpR hqR hpq hpT hlo hhi
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpq0 : (p:ℝ)≤q := by exact_mod_cast hpq.le
  have hratio := hW ((q:ℝ)/p) ((le_div_iff₀ hp0).mpr hlo) ((div_le_iff₀ hp0).mpr hhi)
  let τ := ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)
  have hτ : 0≤τ := by dsimp [τ]; positivity
  have hτlo : 1/U^(2 : ℕ)≤τ := ratio_weight_lower hp0 hpq0 (hL.trans hLU.le) hhi
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
    have he : 4*c=2*k*(1/U^(2 : ℕ)) := by dsimp [c]; ring
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
  let c := ρ*k/(2*U^(2 : ℕ))
  have hU : 0 < U := lt_of_lt_of_le zero_lt_one (hL.trans hLU.le)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,(C/c+1)^(2 : ℕ),hc,?_⟩
  intro p q hp hq hpP hqP hpq hpT hlo hhi
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpqR : (p:ℝ) ≤ q := by exact_mod_cast hpq.le
  have hratio := hW ((q:ℝ)/p) ((le_div_iff₀ hpR).mpr hlo) ((div_le_iff₀ hpR).mpr hhi)
  let τ := ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)
  have hτ : 0 ≤ τ := by dsimp [τ]; positivity
  have hτlo : 1/U^(2 : ℕ) ≤ τ := ratio_weight_lower hpR hpqR (hL.trans hLU.le) hhi
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
    have he : 4*c = 2*ρ*k*(1/U^(2 : ℕ)) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  apply (div_le_iff₀ hpR).mpr
  have herror' : (p:ℝ)*((∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
    ∑' n,mobiusDivisorFixedCoreBlockMass P n)-
    2*ρ*τ*mobiusDivisorDilationMean P ((q:ℝ)/p) ≤ C/Real.sqrt p := by
    simpa only [ρ,τ,mul_assoc] using herror
  nlinarith only [herror',hmain,hsmall,hc]

/-- Every positive prescribed-prime coefficient debt admits two fresh actual
helpers which lower both absolute full logarithmic clock energies and reduce
the debt on one common cutoff tail. The baseline precedes both helpers. -/
theorem exists_mobiusDivisorDirectPrescribedDebtDescent :
    ∀ P : Finset ℕ, P.Nonempty → (∀ r ∈ P,r.Prime) →
      ∀ r : ℕ, r.Prime → r ∉ P →
        (∑' n,mobiusDivisorFixedCoreBlockMass (insert r P) n) ≤
          (∑' n,mobiusDivisorFixedCoreBlockMass P n) ∨
        ∀ B : ℕ, ∃ p q : ℕ, B < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
          p ∉ insert r P ∧ q ∉ insert p (insert r P) ∧
          ∃ d : ℝ, 0 < d ∧ ∀ᶠ M : ℕ in atTop,
            d*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
              mobiusDivisorFiniteClockEnergy 1 M P-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P)) ∧
            2*d*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
              mobiusDivisorFiniteClockEnergy 1 M (insert r P)-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P))) ∧
            d*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
              (mobiusDivisorFiniteClockEnergy 1 M (insert r P)-
                mobiusDivisorFiniteClockEnergy 1 M P)-
              (mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P)))-
                mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P))) := by
  classical
  intro P hP hprime r hr hrP
  by_cases hpaid : selfDebtEnergy (insert r P) ≤ selfDebtEnergy P
  · exact Or.inl hpaid
  right
  intro B
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
  have hρR : 0 < selfDebtDensity R := by
    apply mul_pos
    · rw [Sieve.squarefreeDensity_eq]
      positivity
    · exact prod_pos (fun s hs => div_pos (by exact_mod_cast (hRprime s hs).pos) (by positivity))
  have hneg : mobiusDivisorDilationMean P r < 0 := by
    have he := mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hprime hr hrP
    have hd : selfDebtEnergy P-selfDebtEnergy R < 0 := sub_neg.mpr (lt_of_not_ge hpaid)
    change selfDebtEnergy P-selfDebtEnergy R =
      2*selfDebtDensity R*(r:ℝ)^(-(3/2:ℝ))*mobiusDivisorDilationMean P r at he
    have hfac : 0 < 2*selfDebtDensity R*(r:ℝ)^(-(3/2:ℝ)) := by positivity
    by_contra hn
    have hprod := mul_nonneg hfac.le (le_of_not_gt hn)
    linarith only [he,hd,hprod]
  let kP := -mobiusDivisorDilationMean P r/2
  have hkP : 0 < kP := by dsimp [kP]; linarith only [hneg]
  have hDrP : mobiusDivisorDilationMean P r < -kP := by dsimp [kP]; linarith only [hneg]
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
  have hcontP : ContinuousAt (mobiusDivisorDilationMean P) r :=
    (continuousOn_mobiusDivisorDilationMean P hP hprime).continuousAt (Ioi_mem_nhds hr0)
  have hcont : ContinuousAt D r :=
    (((continuousOn_mobiusDivisorDilationMean R hR hRprime).continuousAt (Ioi_mem_nhds hr0)).const_mul _).sub
      (hcontP.const_mul _)
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp
    ((hcontP.eventually (eventually_lt_nhds hDrP)).and
      (hcont.eventually (eventually_lt_nhds hDr)))
  let U := (r:ℝ)+ε/2
  have hU : (r:ℝ) < U := by dsimp [U]; linarith
  have hband : ∀ Y : ℝ,(r:ℝ) ≤ Y → Y ≤ U →
      mobiusDivisorDilationMean P Y ≤ -kP ∧
      selfDebtDensity R*mobiusDivisorDilationMean R Y-
        selfDebtDensity P*mobiusDivisorDilationMean P Y ≤ -k := by
    intro Y hlo hhi
    have hd : dist Y (r:ℝ) < ε := by
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hlo)]
      dsimp [U] at hhi
      linarith
    exact ⟨(hεprop hd).1.le,(hεprop hd).2.le⟩
  obtain ⟨aP,TP,haP,hreleaseP⟩ := negative_window_release P hP hprime
    r U kP hr1 hU hkP (fun Y hlo hhi => (hband Y hlo hhi).1)
  obtain ⟨a,T,ha,hrelease⟩ := relative_window_release P R hP hR hprime hRprime
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
  let d := min a aP/(2*(p:ℝ))
  have hd : 0 < d := by dsimp [d]; exact div_pos (lt_min ha haP) (by positivity)
  have htwo : 2*d=min a aP/(p:ℝ) := by dsimp [d]; ring
  have hdA : 2*d ≤ a/(p:ℝ) := by rw [htwo]; exact div_le_div_of_nonneg_right (min_le_left _ _) hp0.le
  have hdP : 2*d ≤ aP/(p:ℝ) := by rw [htwo]; exact div_le_div_of_nonneg_right (min_le_right _ _) hp0.le
  have hnewP : ∀ s ∈ insert q (insert p P),s.Prime := by simpa using And.intro hq (And.intro hp hprime)
  have hnewR : ∀ s ∈ insert q (insert p R),s.Prime := by simpa using And.intro hq (And.intro hp hRprime)
  have hlim := ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log R hRprime).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime)).sub
      ((tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewR).sub
        (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewP))
  have hlimP := (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log P hprime).sub
    (tendsto_mobiusDivisorFiniteClockEnergy_div_sq_log _ hnewP)
  have hstrict : d < (selfDebtEnergy R-selfDebtEnergy P)-
      (selfDebtEnergy (insert q (insert p R))-selfDebtEnergy (insert q (insert p P))) := by
    linarith only [hg,hdA,hd]
  have hstrictP : d < (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
      (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n) := by
    linarith only [hgP,hdP,hd]
  refine ⟨p,q,hBp,hpq,hp,hq,hpR,hqfresh,d,hd,?_⟩
  have he := hlim.eventually (eventually_gt_nhds hstrict)
  have heP := hlimP.eventually (eventually_gt_nhds hstrictP)
  filter_upwards [he,heP,eventually_ge_atTop (1:ℕ)] with M hM hMP hM1
  have hMR : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 ≤ Real.log (M:ℝ) := Real.log_nonneg (by exact_mod_cast hM1)
  have hden : 0 < (M:ℝ)^(2 : ℕ)*(1+Real.log M) := by positivity
  simp only [← sub_div] at hM hMP
  have hrel := (le_div_iff₀ hden).mp hM.le
  have habs := (le_div_iff₀ hden).mp hMP.le
  have hrel' : d*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤
      (mobiusDivisorFiniteClockEnergy 1 M (insert r P)-mobiusDivisorFiniteClockEnergy 1 M P)-
        (mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p (insert r P)))-
          mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P))) := by
    simpa only [R,mul_assoc] using hrel
  have habs' : d*(M:ℝ)^(2 : ℕ)*(1+Real.log M) ≤ mobiusDivisorFiniteClockEnergy 1 M P-
      mobiusDivisorFiniteClockEnergy 1 M (insert q (insert p P)) := by
    simpa only [mul_assoc] using habs
  exact ⟨habs',by linarith only [habs',hrel'],hrel'⟩

end RHTower
