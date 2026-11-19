import GaloisForLFunctions.RestrictedFactorizationCalculus.EveryEmptyOrderedFibre
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeMassInDeficientRows
import GaloisForLFunctions.RHTower.Sieve.SquarefreeHarmonic
import GaloisForLFunctions.RHTower.SecondMoment
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory

/-!
# A positive proportion of the block crosses empty ordered fibres

Each small negative cofactor supplies a prime-sized family of ordered pairs
which its original fibre cannot match. Summing the reciprocal-cofactor
weights gives a logarithm. Removing the two largest primes recovers the
cofactor and prevents any overlap when the families are added.
-/

noncomputable section

open Finset Filter RHTower ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem negative_harmonic (N : ℕ) :
    2 * ∑ c ∈ negParity (Icc 1 N), 1/(c:ℝ) =
      (∑ c ∈ (Icc 1 N).filter Squarefree, 1/(c:ℝ)) -
        (∑ c ∈ Icc 1 N, (μ c:ℝ)/c) := by
  rw [negParity, sum_filter, sum_filter, mul_sum,
    ← sum_sub_distrib]
  refine sum_congr rfl fun c _ => ?_
  by_cases hs : Squarefree c
  · rcases moebius_eq_one_or_neg_one_of_squarefree hs with h | h <;> simp [h,hs]
    ring
  · simp [moebius_eq_zero_of_not_squarefree hs,hs]

/-- Harmonic mass of the negative squarefree cofactors up to a sharp real cutoff. -/
private theorem eventually_negative_harmonic :
    ∀ᶠ s : ℝ in atTop, Real.log s / 8 ≤ ∑ c ∈ negParity (Icc 1 ⌊s⌋₊), 1/(c:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 4] with s hs hl
  let N := ⌊s⌋₊
  have hN : 1 ≤ N := (Nat.one_le_floor_iff _).2 (by linarith)
  have hm := (le_abs_self _).trans (abs_sum_moebius_div_le_one N hN)
  have hf := (harmonic_Icc_ge_log N).trans (Sieve.sum_inv_le_two_mul_sum_inv_squarefree N)
  have hlN := Real.log_le_log (by linarith only [hs] : 0 < s) (Nat.lt_floor_add_one s).le
  have hid := negative_harmonic N
  change Real.log s/8 ≤ ∑ c ∈ negParity (Icc 1 N), 1/(c:ℝ)
  linarith only [hl,hm,hf,hlN,hid]

/-- Twelfth-root coordinate of an actual cofactor row. -/
def quotientRoot (X c : ℕ) := ((X:ℝ)/c)^(1/12:ℝ)

theorem quotientRoot_pow (X c : ℕ) : quotientRoot X c ^ 12 = (X:ℝ)/c := by
  rw [quotientRoot,← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
  norm_num

/-- Cofactors contributing a positive proportion through the deficient exponent band. -/
def smallNegativeCofactors (X : ℕ) := negParity (Icc 1 ⌊(X:ℝ)^(1/24:ℝ)⌋₊)

/-- The explicit disjoint family of deficient negative endpoints. -/
def deficientFamily (X : ℕ) := (smallNegativeCofactors X).biUnion (fun c =>
  (deficientProducts (quotientRoot X c)).image (c*·))

private def exhausted (X : ℕ) :=
  (negParity (Ioc X (2*X))).filter (fun n => fibrePos X (evenPrefixCofactor n) = ∅)

/-- The explicit family built from small negative cofactors already occupies
a positive proportion of the octave, and every member lies in an empty fibre. -/
theorem eventually_linear_deficient_family :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)/49920 ≤ ((deficientFamily X).card:ℝ) ∧
      deficientFamily X ⊆ (negParity (Ioc X (2*X))).filter
        (fun n => fibrePos X (evenPrefixCofactor n) = ∅) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp eventually_deficientProducts_lower
  obtain ⟨H,hH⟩ := eventually_atTop.mp eventually_negative_harmonic
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^(1/24:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlim.eventually_ge_atTop (max 2 (max T H))] with X hX hs
  let s := (X:ℝ)^(1/24:ℝ)
  let C := negParity (Icc 1 ⌊s⌋₊)
  let W := fun c => deficientProducts (quotientRoot X c)
  have hs2 : 2 ≤ s := (le_max_left _ _).trans hs
  have hs0 : 0 < s := by linarith only [hs2]
  have hs1 : 1 ≤ s := by linarith only [hs2]
  have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXL := Real.log_pos (by exact_mod_cast (by omega : 1 < X) : (1:ℝ) < X)
  have hs24 : s^24 = X := by
    rw [show s = (X:ℝ)^(1/24:ℝ) from rfl,← Real.rpow_natCast,← Real.rpow_mul hX0.le]
    norm_num
  have hlog : Real.log X = 24*Real.log s := by rw [← hs24,Real.log_pow]; norm_num
  -- Even the smallest quotient root exceeds the entire cofactor cutoff.
  have hgeom {c : ℕ} (hc : c ∈ C) : 0 < c ∧ (c:ℝ) ≤ s ∧ s ≤ quotientRoot X c ∧
      quotientRoot X c ≤ X := by
    obtain ⟨hcs,_⟩ := mem_filter.mp hc
    obtain ⟨hc1,hcup⟩ := mem_Icc.mp hcs
    have hc0 : (0:ℝ) < c := by exact_mod_cast hc1
    have hc' := (Nat.cast_le.mpr hcup).trans (Nat.floor_le hs0.le)
    have ht0 : 0 ≤ quotientRoot X c := Real.rpow_nonneg (by positivity) _
    have ht : s ≤ quotientRoot X c := by
      apply (pow_le_pow_iff_left₀ hs0.le ht0 (by decide : 12 ≠ 0)).1
      rw [quotientRoot_pow,le_div_iff₀ hc0,← hs24]
      calc s^12*(c:ℝ) ≤ s^12*s := mul_le_mul_of_nonneg_left hc' (by positivity)
           _ = s^13 := by ring
           _ ≤ s^24 := pow_le_pow_right₀ hs1 (by decide)
    have ht1 : 1 ≤ quotientRoot X c := hs1.trans ht
    have ht12 : quotientRoot X c ≤ quotientRoot X c^12 := by
      simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 12)
    rw [quotientRoot_pow] at ht12
    exact ⟨hc1,hc',ht,ht12.trans (div_le_self hX0.le (by exact_mod_cast hc1))⟩
  -- The same ordered factorization proves emptiness and decodes the cofactor.
  have hinfo {c w : ℕ} (hc : c ∈ C) (hw : w ∈ W c) :
      c*w ∈ exhausted X ∧ stem (stem (c*w)) = c := by
    obtain ⟨hc1,hcs,hst,_⟩ := hgeom hc
    have hcμ := (mem_filter.mp hc).2
    let t := quotientRoot X c
    have ht2 := hs2.trans hst
    have ht1 : 1 ≤ t := hs1.trans hst
    have ht0 : 0 < t := hs0.trans_le hst
    have ht12 : t^12 = (X:ℝ)/c := quotientRoot_pow X c
    obtain ⟨q,r,hq,hr,hqr,hql,_,rfl,hw1,hw2⟩ := deficientProducts_factors ht2 hw
    have hqt : t ≤ t^4 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 4)
    have htq : t < (q:ℝ) := by
      change 2*t^4 < (q:ℝ) at hql
      linarith only [hql,hqt,pow_nonneg ht0.le 4]
    have hcq : c < q := Nat.cast_lt.mp ((hcs.trans hst).trans_lt htq)
    have htop : ∀ d ∈ c.primeFactors, d < q := fun d hd =>
      (Nat.le_of_dvd hc1 (Nat.dvd_of_mem_primeFactors hd)).trans_lt hcq
    have hbelow := below_pair hc1.ne' hq hqr htop
    have hcqn := Nat.mul_ne_zero hc1.ne' hq.ne_zero
    have hc0 : (0:ℝ) < c := by exact_mod_cast hc1
    rw [ht12] at hw1 hw2
    have hnI : c*(q*r) ∈ Ioc X (2*X) := by
      apply mem_Ioc.mpr
      constructor
      · rw [div_lt_iff₀ hc0] at hw1
        exact_mod_cast (by simpa only [mul_comm (c:ℝ)] using hw1 :
          (X:ℝ) < (c:ℝ)*(q*r:ℕ))
      · rw [← mul_div_assoc,le_div_iff₀ hc0] at hw2
        exact_mod_cast (by simpa only [mul_comm (c:ℝ)] using hw2 :
          (c:ℝ)*(q*r:ℕ) ≤ 2*X)
    have hnμ : μ (c*(q*r)) = -1 := by
      rw [← mul_assoc,mu_append hcqn hr hbelow,mu_append hc1.ne' hq htop,hcμ]; decide
    have hstem : stem (c*(q*r)) = c*q := by rw [← mul_assoc,stem_mul_of_largest hcqn hr hbelow]
    refine ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨hnI,hnμ⟩,?_⟩,
      by rw [hstem,stem_mul_of_largest hc1.ne' hq htop]⟩
    rw [ordered_cofactor_of_negative hnμ,hstem]
    apply fibrePos_eq_empty_of_primeFactor_sq_ge (by omega)
      (Nat.mem_primeFactors.mpr ⟨hq,dvd_mul_left q c,hcqn⟩)
    have hq3 := pow_le_pow_left₀ (by positivity : 0 ≤ 2*t^4) hql.le 3
    have hbig : 2*t^12 ≤ (q:ℝ)^3 := by nlinarith only [hq3,pow_nonneg ht0.le 12]
    rw [ht12,← mul_div_assoc,div_le_iff₀ hc0] at hbig
    exact_mod_cast (hbig.trans_eq (by ring : (q:ℝ)^3*c = (c:ℝ)*q*q^2))
  let D := C.biUnion fun c => (W c).image (c*·)
  have hsub : D ⊆ exhausted X := by
    intro n hn
    obtain ⟨c,hc,hm⟩ := mem_biUnion.mp hn
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hm
    exact (hinfo hc hw).1
  have hcard : D.card = ∑ c ∈ C,(W c).card := by
    dsimp only [D]
    rw [card_biUnion]
    · exact sum_congr rfl fun c hc => card_image_of_injOn (fun _ _ _ _ h =>
        Nat.eq_of_mul_eq_mul_left (hgeom hc).1 h)
    · intro c hc d hd hne
      apply disjoint_left.mpr
      intro n hn hn'
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hn
      obtain ⟨v,hv,he⟩ := mem_image.mp hn'
      exact hne ((hinfo hc hw).2.symm.trans ((congrArg (fun n => stem (stem n)) he.symm).trans
        (hinfo hd hv).2))
  have hrow (c : ℕ) (hc : c ∈ C) : (X:ℝ)/(260*Real.log X)*(1/c) ≤ ((W c).card:ℝ) := by
    obtain ⟨hc1,_,hst,htX⟩ := hgeom hc
    have hc0 : (0:ℝ) < c := by exact_mod_cast hc1
    have ht0 := hs0.trans_le hst
    have hlt : 0 < Real.log (quotientRoot X c) := Real.log_pos (by linarith only [hs2,hst])
    have hl := Real.log_le_log ht0 htX
    apply le_trans _ (hT _ ((le_max_left _ _).trans ((le_max_right _ _).trans (hs.trans hst))))
    rw [quotientRoot_pow,div_mul_div_comm,mul_one,div_div]
    apply div_le_div_of_nonneg_left hX0.le (by positivity)
    simpa only [mul_comm (c:ℝ),mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ) ≤ 260)) hc0.le
  -- The reciprocal-cofactor sum supplies the logarithm lost in each prime row.
  have hsum := hH s ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
  refine ⟨?_,hsub⟩
  change (X:ℝ)/49920 ≤ (D.card:ℝ)
  rw [hcard,Nat.cast_sum]
  calc (X:ℝ)/49920 = (X:ℝ)/(260*Real.log X)*(Real.log s/8) := by
          have hne := (Real.log_pos (by linarith only [hs2] : 1 < s)).ne'
          rw [hlog]
          field_simp [hne]
          ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hsum (by positivity :
            0 ≤ (X:ℝ)/(260*Real.log X))).trans (by rw [mul_sum]; exact sum_le_sum hrow)

/-- A linear number of negatives have no positive neighbour in their original fibre. -/
theorem eventually_linear_empty_fibre_debt :
    ∀ᶠ X : ℕ in atTop, (X:ℝ)/49920 ≤ (((negParity (Ioc X (2*X))).filter
      (fun n => fibrePos X (evenPrefixCofactor n) = ∅)).card:ℝ) := by
  filter_upwards [eventually_linear_deficient_family] with X h
  exact h.1.trans (by exact_mod_cast card_le_card h.2)

/-- Every ordered matching loses a positive proportion of the block to empty
fibres. One cross-fibre matching covers all those negative vertices and
retains every previously covered positive vertex. -/
theorem eventually_linear_cross_fibre_transport :
    ∀ᶠ X : ℕ in atTop, ∀ A : OppositeParityMatching OrderedExchange (Ioc X (2*X)),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        A.sources ⊆ M.sources ∧ (X:ℝ)/49920 ≤ ((M.targets \ A.targets).card:ℝ) := by
  filter_upwards [eventually_every_empty_fibre_covered,eventually_linear_empty_fibre_debt] with X hx hd
  intro A
  obtain ⟨M,hA,hcov⟩ := hx A
  refine ⟨M,hA,hd.trans ?_⟩
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  refine mem_sdiff.mpr ⟨hcov hn,?_⟩
  intro ht
  obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
  have hh : m ∈ fibrePos X (evenPrefixCofactor (A.partner m)) :=
    mem_filter.mpr ⟨A.sources_subset hm,(A.adj m hm).2⟩
  rw [(mem_filter.mp hn).2] at hh
  exact notMem_empty _ hh

#print axioms eventually_linear_deficient_family
#print axioms eventually_linear_empty_fibre_debt
#print axioms eventually_linear_cross_fibre_transport

end GaloisForLFunctions.RestrictedFactorizationCalculus
