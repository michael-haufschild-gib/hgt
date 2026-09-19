import GaloisForLFunctions.RHTower.MobiusDivisorPrimePairRatioProfile

/-!
# Common actual reserve pairs across a finite collection of source states

A common fresh prime creates overlapping negative correlation bands in every
nonempty core of a finite prime field. Actual prime pairs in that band release
energy simultaneously in all those states. Preparation and intermediate
insertions cost an arbitrarily small quadratic allowance at every cutoff.
No exhaustive history or payment of an existing prescribed-prime debt is asserted.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma common_negative_band (F : Finset (Finset ℕ))
    (hF : ∀ P ∈ F,P.Nonempty ∧ ∀ r ∈ P,r.Prime) :
    ∃ η c T : ℝ, 0 < η ∧ 0 < c ∧ ∀ a : ℕ,a.Prime →
      (∀ P ∈ F,a ∉ P) → T ≤ (a:ℝ) → ∀ Y : ℝ,
      (a:ℝ) ≤ Y → Y ≤ (1+η)*(a:ℝ) → ∀ P ∈ F,
        mobiusDivisorDilationMean (insert a P) Y ≤ -c*Real.sqrt a := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1,1,0,by norm_num,by norm_num,by simp⟩
  | @insert P F hPF ih =>
    obtain ⟨η₀,c₀,T₀,hη₀,hc₀,h₀⟩ := ih (fun Q hQ => hF Q (mem_insert_of_mem hQ))
    obtain ⟨η₁,c₁,T₁,hη₁,hc₁,h₁⟩ := exists_mobiusDivisorDilationMean_insert_negative_band
      P (hF P (mem_insert_self _ _)).1 (hF P (mem_insert_self _ _)).2
    refine ⟨min η₀ η₁,min c₀ c₁,max T₀ T₁,lt_min hη₀ hη₁,lt_min hc₀ hc₁,?_⟩
    intro a ha haF haT Y hYlo hYhi Q hQ
    rcases mem_insert.mp hQ with hQP | hQ
    · subst Q
      have h := h₁ a ha (haF P (mem_insert_self _ _)) ((le_max_right _ _).trans haT)
        Y hYlo (hYhi.trans (mul_le_mul_of_nonneg_right
          (by linarith only [min_le_right η₀ η₁]) (Nat.cast_nonneg a)))
      have hc := mul_le_mul_of_nonneg_right (min_le_right c₀ c₁) (Real.sqrt_nonneg (a:ℝ))
      linarith only [h,hc]
    · have h := h₀ a ha (fun Q hQ => haF Q (mem_insert_of_mem hQ))
        ((le_max_left _ _).trans haT) Y hYlo
        (hYhi.trans (mul_le_mul_of_nonneg_right (by linarith only [min_le_left η₀ η₁])
          (Nat.cast_nonneg a))) Q hQ
      have hc := mul_le_mul_of_nonneg_right (min_le_left c₀ c₁) (Real.sqrt_nonneg (a:ℝ))
      linarith only [h,hc]

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

private lemma common_pair_release (F : Finset (Finset ℕ))
    (hF : ∀ P ∈ F,P.Nonempty ∧ ∀ r ∈ P,r.Prime)
    (L U k : ℝ) (hL : 1 ≤ L) (hLU : L < U) (hk : 0 < k)
    (hW : ∀ P ∈ F,∀ Y : ℝ,L ≤ Y → Y ≤ U → mobiusDivisorDilationMean P Y ≤ -k) :
    ∃ c T : ℝ,0 < c ∧ ∀ p q : ℕ,p.Prime → q.Prime →
      (∀ P ∈ F,p ∉ P ∧ q ∉ P) → p < q →
      T ≤ (p:ℝ) → L*(p:ℝ) ≤ q → (q:ℝ) ≤ U*(p:ℝ) → ∀ P ∈ F,
      c/(p:ℝ) ≤ (∑' n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
  induction F using Finset.induction_on with
  | empty => exact ⟨1,0,by norm_num,by simp⟩
  | @insert P F hPF ih =>
    obtain ⟨c₀,T₀,hc₀,h₀⟩ := ih (fun Q hQ => hF Q (mem_insert_of_mem hQ))
      (fun Q hQ => hW Q (mem_insert_of_mem hQ))
    obtain ⟨c₁,T₁,hc₁,h₁⟩ := negative_window_release P (hF P (mem_insert_self _ _)).1
      (hF P (mem_insert_self _ _)).2 L U k hL hLU hk (hW P (mem_insert_self _ _))
    refine ⟨min c₀ c₁,max T₀ T₁,lt_min hc₀ hc₁,?_⟩
    intro p q hp hq hfree hpq hpT hlo hhi Q hQ
    have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
    rcases mem_insert.mp hQ with hQP | hQ
    · subst Q
      exact (div_le_div_of_nonneg_right (min_le_right c₀ c₁) hp0).trans
        (h₁ p q hp hq (hfree P (mem_insert_self _ _)).1 (hfree P (mem_insert_self _ _)).2
          hpq ((le_max_right _ _).trans hpT) hlo hhi)
    · exact (div_le_div_of_nonneg_right (min_le_left c₀ c₁) hp0).trans
        (h₀ p q hp hq (fun Q hQ => hfree Q (mem_insert_of_mem hQ)) hpq
          ((le_max_left _ _).trans hpT) hlo hhi Q hQ)

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

/-- A common actual prime preparation and arbitrarily large actual reserve pairs
work across all nonempty cores in any finite prime field. Every physical prefix
has arbitrarily small all-cutoff cost; the final pair releases positive eventual
quadratic energy in every prepared core, with no parity or source-sign premise. -/
theorem exists_mobiusDivisorCommonReserveProducer :
    ∀ N : ℕ,∀ ε : ℝ,0 < ε → ∃ a : ℕ,N < a ∧ a.Prime ∧
      ∀ B : ℕ,∃ p q : ℕ,B ≤ p ∧ a < p ∧ p < q ∧ p.Prime ∧ q.Prime ∧
        (∀ M : ℕ,∀ P : Finset ℕ,P ⊆ mobiusDivisorSelectionPrimes N →
          mobiusDivisorSelectionEnergy M (insert a P) ≤ mobiusDivisorSelectionEnergy M P+ε*(M:ℝ)^2 ∧
          mobiusDivisorSelectionEnergy M (insert p (insert a P)) ≤ mobiusDivisorSelectionEnergy M P+ε*(M:ℝ)^2 ∧
          mobiusDivisorSelectionEnergy M (insert q (insert p (insert a P))) ≤ mobiusDivisorSelectionEnergy M P+ε*(M:ℝ)^2) ∧
        ∃ c : ℝ,0 < c ∧ ∀ᶠ M : ℕ in atTop,∀ P : Finset ℕ,
          P ⊆ mobiusDivisorSelectionPrimes N → P.Nonempty →
          c*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert a P)-
            mobiusDivisorSelectionEnergy M (insert q (insert p (insert a P))) := by
  classical
  intro N ε hε
  let S := mobiusDivisorSelectionPrimes N
  let F := S.powerset.filter (fun P => P.Nonempty)
  have hFP (P : Finset ℕ) (hP : P ∈ F) : P ⊆ S ∧ P.Nonempty := by
    obtain ⟨hsub,hne⟩ := mem_filter.mp hP
    exact ⟨mem_powerset.mp hsub,hne⟩
  have hprime (P : Finset ℕ) (hP : P ⊆ S) : ∀ r ∈ P,r.Prime := by
    intro r hr
    exact (mem_filter.mp (hP hr)).2
  have hsmall (P : Finset ℕ) (hP : P ⊆ S) : ∀ r ∈ P,r < N := by
    intro r hr
    exact mem_range.mp (mem_filter.mp (hP hr)).1
  obtain ⟨η,c₀,T,hη,hc₀,hband⟩ := common_negative_band F
    (fun P hP => ⟨(hFP P hP).2,hprime P (hFP P hP).1⟩)
  obtain ⟨A,hcost⟩ := uniform_insertion_threshold (S.card+2) (ε/3) (by positivity)
  obtain ⟨a,haBound,ha⟩ := Nat.exists_infinite_primes (max (N+1) (max A ⌈T⌉₊))
  have hNa : N < a := by have := (le_max_left _ _).trans haBound; omega
  have hAa : A ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans haBound)
  have haT : T ≤ (a:ℝ) := (Nat.le_ceil T).trans
    (by exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans haBound)))
  have haR : (0:ℝ) < a := by exact_mod_cast ha.pos
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast ha.one_lt.le
  have haP (P : Finset ℕ) (hP : P ⊆ S) : a ∉ P := by
    intro h
    have := hsmall P hP a h
    omega
  let G := F.image (fun P => insert a P)
  have hG : ∀ Q ∈ G,Q.Nonempty ∧ ∀ r ∈ Q,r.Prime := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := mem_image.mp hQ
    exact ⟨insert_nonempty _ _,by simpa using And.intro ha (hprime P (hFP P hP).1)⟩
  let U : ℝ := (1+η)*(a:ℝ)
  have haU : (a:ℝ) < U := by dsimp [U]; nlinarith only [mul_pos hη haR]
  have hW : ∀ Q ∈ G,∀ Y : ℝ,(a:ℝ) ≤ Y → Y ≤ U →
      mobiusDivisorDilationMean Q Y ≤ -(c₀*Real.sqrt a) := by
    intro Q hQ Y hlo hhi
    obtain ⟨P,hP,rfl⟩ := mem_image.mp hQ
    have h := hband a ha (fun P hP => haP P (hFP P hP).1) haT Y hlo hhi P hP
    simpa only [neg_mul] using h
  obtain ⟨d,V,hd,hrelease⟩ := common_pair_release G hG a U (c₀*Real.sqrt a)
    ha1 haU (mul_pos hc₀ (Real.sqrt_pos.mpr haR)) hW
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between hη)
  refine ⟨a,hNa,ha,?_⟩
  intro B
  obtain ⟨p,hpBound,hp⟩ := Nat.exists_infinite_primes
    (max B (max (a+1) (max A ⌈max V Z⌉₊)))
  have hBp : B ≤ p := (le_max_left _ _).trans hpBound
  have hap : a < p := by
    have := (le_max_left _ _).trans ((le_max_right _ _).trans hpBound)
    omega
  have hAp : A ≤ p := hAa.trans hap.le
  have hpVZ : max V Z ≤ (p:ℝ) := (Nat.le_ceil _).trans
    (by exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hpBound))))
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpa : (p:ℝ) ≤ (a:ℝ)*(p:ℝ) := by
    simpa using mul_le_mul_of_nonneg_right ha1 hpR.le
  obtain ⟨q,hq,hqlo,hqhi⟩ := hZ ((a:ℝ)*(p:ℝ)) (((le_max_right _ _).trans hpVZ).trans hpa)
  have hpq : p < q := by exact_mod_cast hpa.trans_lt hqlo
  have hqhi' : (q:ℝ) ≤ U*(p:ℝ) := by dsimp [U]; nlinarith only [hqhi.le]
  have hfree (P : Finset ℕ) (hP : P ⊆ S) : p ∉ insert a P ∧ q ∉ insert p (insert a P) := by
    constructor
    · intro h
      rcases mem_insert.mp h with h | h
      · omega
      · have := hsmall P hP p h; omega
    · intro h
      rcases mem_insert.mp h with h | h
      · omega
      rcases mem_insert.mp h with h | h
      · omega
      · have := hsmall P hP q h; omega
  have hfreeG : ∀ Q ∈ G,p ∉ Q ∧ q ∉ Q := by
    intro Q hQ
    obtain ⟨P,hP,rfl⟩ := mem_image.mp hQ
    have hh := hfree P (hFP P hP).1
    exact ⟨hh.1,fun h => hh.2 (mem_insert_of_mem h)⟩
  have hcoeff := hrelease p q hp hq hfreeG hpq ((le_max_left _ _).trans hpVZ) hqlo.le hqhi'
  refine ⟨p,q,hBp,hap,hpq,hp,hq,?_,d/(2*(p:ℝ)),by positivity,?_⟩
  · intro M P hP
    have hPS : P ⊆ S := hP
    have hcard : P.card ≤ S.card := card_le_card hPS
    have hPa : ∀ r ∈ insert a P,r.Prime := by simpa using And.intro ha (hprime P hPS)
    have hPp : ∀ r ∈ insert p (insert a P),r.Prime := by simpa using And.intro hp hPa
    have hcarda : (insert a P).card = P.card+1 := card_insert_of_notMem (haP P hPS)
    have hcardp : (insert p (insert a P)).card = P.card+2 := by
      rw [card_insert_of_notMem (hfree P hPS).1,hcarda]
    have h₀ := hcost P (by omega) (hprime P hPS) a ha (haP P hPS) hAa M
    have h₁ := hcost (insert a P) (by omega) hPa p hp (hfree P hPS).1 hAp M
    have h₂ := hcost (insert p (insert a P)) (by omega) hPp q hq (hfree P hPS).2
      (hAp.trans hpq.le) M
    have hm := mul_nonneg hε.le (sq_nonneg (M:ℝ))
    constructor
    · nlinarith only [h₀,hm]
    constructor <;> nlinarith only [h₀,h₁,h₂,hm]
  · have hevent : ∀ P ∈ F,∀ᶠ M : ℕ in atTop,
        d/(2*(p:ℝ))*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert a P)-
          mobiusDivisorSelectionEnergy M (insert q (insert p (insert a P))) := by
      intro P hP
      have hPS := (hFP P hP).1
      have hPa : ∀ r ∈ insert a P,r.Prime := by simpa using And.intro ha (hprime P hPS)
      have hPp : ∀ r ∈ insert p (insert a P),r.Prime := by simpa using And.intro hp hPa
      have hPq : ∀ r ∈ insert q (insert p (insert a P)),r.Prime := by simpa using And.intro hq hPp
      have hcoef := hcoeff (insert a P) (mem_image.mpr ⟨P,hP,rfl⟩)
      have hstrict : d/(2*(p:ℝ)) < (∑' n,mobiusDivisorFixedCoreBlockMass (insert a P) n)-
          ∑' n,mobiusDivisorFixedCoreBlockMass (insert q (insert p (insert a P))) n := by
        apply lt_of_lt_of_le _ hcoef
        have he : d/(2*(p:ℝ)) = (d/2)/(p:ℝ) := by ring
        rw [he]
        exact div_lt_div_of_pos_right (by linarith) hpR
      have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq (insert a P) hPa).sub
        (tendsto_mobiusDivisorSelectionEnergy_div_sq _ hPq)
      have he := ht.eventually (eventually_gt_nhds hstrict)
      filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
      have hMR : (0:ℝ) < M := by exact_mod_cast hM0
      simp only [← sub_div] at hM
      exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le
    have hall := (Filter.eventually_all_finset F).mpr hevent
    filter_upwards [hall] with M hM P hP hn
    exact hM P (mem_filter.mpr ⟨mem_powerset.mpr hP,hn⟩)

end RHTower
