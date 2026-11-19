import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheOrderOfAbsoluteMertensMass
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.HowManyMertensPrefixesReachASubcriticalPower
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.PowerMassOfAnExceptionalSet
import GaloisForLFunctions.RHTower.MobiusMertensAbsoluteMomentExponentLaw

/-!
# The lower counting order of Mertens excursions

An exceptional set with m members can carry only O(mᵃ) reciprocal
Mertens mass if |M(k)| is bounded by kᵃ and a ≤ 1. A sparse set
would contradict the lower bound furnished at every cutoff by a zeta
zero. The conclusion applies also at and below square-root scale.
-/

noncomputable section
open Filter Finset
open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem reciprocal_mass_of_set {a C : ℝ} (ha : 0<a) (ha1 : a≤1) (hC : 0≤C)
    (S : Finset ℕ) (hs : ∀ k ∈ S, 1≤k)
    (hM : ∀ k ∈ S, ‖mobiusMertensPartialSum k‖ ≤ C*((k:ℝ)+1)^a) :
    (∑ k ∈ S, ‖mobiusMertensPartialSum k‖/(k:ℝ)) ≤ (C*2^a*(1+1/a))*((S.card:ℝ)+1)^a := by
  have hrow (k : ℕ) (hk : k∈S) :
      ‖mobiusMertensPartialSum k‖/(k:ℝ) ≤ (C*2^a)*(k:ℝ)^(a-1) := by
    have h1 := (Nat.one_le_cast (α:=ℝ)).mpr (hs k hk)
    have kp := zero_lt_one.trans_le h1
    have h := Real.rpow_le_rpow (by positivity : 0≤(k:ℝ)+1)
      (by linarith only [h1] : (k:ℝ)+1 ≤ 2*k) ha.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) kp.le] at h
    rw [Real.rpow_sub kp,Real.rpow_one]
    exact (div_le_div_of_nonneg_right ((hM k hk).trans (mul_le_mul_of_nonneg_left h hC)) kp.le).trans_eq (by ring)
  have hsum := sum_le_sum hrow
  rw [←mul_sum] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_left (packed_power ha ha1 S hs)
    (mul_nonneg hC (by positivity))).trans_eq (by ring))

/-- A small exceptional population bounds the entire reciprocal mass
at that same cutoff. The two powers measure the threshold and the
largest admissible size of its exceptional members. -/
theorem mertens_abel_mass_two_population {a b C A : ℝ} (hb : 0<b) (hb1 : b≤1)
    (ha : 0<a) (ha1 : a≤1) (hC : 0≤C) (hA : 0≤A)
    (hM : ∀ k : ℕ, ‖mobiusMertensPartialSum k‖ ≤ A*((k:ℝ)+1)^a) :
    ∃ B : ℝ, 0≤B ∧ ∀ N, mertensAbelMass N ≤ B*(((N:ℝ)+1)^b+
      (((mertensExcursions b C N).card:ℝ)+1)^a) := by
  classical
  let P := C*2^b*(1+1/b)
  let Q := A*2^a*(1+1/a)
  have hP : 0≤P := by dsimp only [P]; positivity
  have hQ : 0≤Q := by dsimp only [Q]; positivity
  refine ⟨P+Q,add_nonneg hP hQ,fun N => ?_⟩
  let S := Icc 1 N
  let E := mertensExcursions b C N
  let T := S ∩ E
  have ht : T ⊆ S := inter_subset_left
  have gp := reciprocal_mass_of_set hb hb1 hC (S \ T)
    (fun _ hk => (mem_Icc.mp (mem_sdiff.mp hk).1).1) (fun k hk => by
      obtain ⟨hks,hkt⟩ := mem_sdiff.mp hk
      rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
      exact le_of_not_gt fun h => hkt (mem_inter.mpr ⟨hks,mem_filter.mpr
        ⟨mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hks).2),h⟩⟩))
  have ep := reciprocal_mass_of_set ha ha1 hA T (fun k hk => (mem_Icc.mp (ht hk)).1) (fun k _ => hM k)
  have hc : (S \ T).card ≤ N := by
    simpa [S,Nat.card_Icc] using (card_le_card (sdiff_subset : S \ T ⊆ S))
  have he : T.card ≤ E.card := card_le_card inter_subset_right
  have hg := Real.rpow_le_rpow (by positivity : 0≤((S \ T).card:ℝ)+1)
    (add_le_add_right (Nat.cast_le.mpr hc) 1) hb.le
  have hi := Real.rpow_le_rpow (by positivity : 0≤(T.card:ℝ)+1)
    (add_le_add_right (Nat.cast_le.mpr he) 1) ha.le
  rw [mertens_abel_mass_eq]
  change (∑ k ∈ S, _) ≤ (P+Q)*(((N:ℝ)+1)^b+((E.card:ℝ)+1)^a)
  rw [←sum_sdiff ht]
  change _ ≤ P*_ at gp
  change _ ≤ Q*_ at ep
  linarith only [gp,ep,mul_le_mul_of_nonneg_left hg hP,mul_le_mul_of_nonneg_left hi hQ,
    mul_nonneg hP (Real.rpow_nonneg (by positivity : 0≤(E.card:ℝ)+1) a),
    mul_nonneg hQ (Real.rpow_nonneg (by positivity : 0≤(N:ℝ)+1) b)]

private theorem upper_envelope {d : ℝ} (hd : 0<d) (hd1 : d<1) :
    ∃ a : ℝ, 0<a ∧ a≤1 ∧ d*a<zetaZeroAbscissa ∧
      ∃ A : ℝ, 0≤A ∧ ∀ k : ℕ, ‖mobiusMertensPartialSum k‖ ≤ A*((k:ℝ)+1)^a := by
  have hθ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  by_cases hθ1 : zetaZeroAbscissa < 1
  · have hdθ := (lt_div_iff₀ hd).mpr (mul_lt_of_lt_one_right hθ hd1)
    obtain ⟨a,ha,ha'⟩ := exists_between (lt_min hθ1 hdθ)
    obtain ⟨A,hA,h⟩ := mobiusMertens_subpower_zetaZeroAbscissa (a-zetaZeroAbscissa) (sub_pos.mpr ha)
    rw [show zetaZeroAbscissa+(a-zetaZeroAbscissa)=a by ring] at h
    have hda := (lt_div_iff₀ hd).mp (ha'.trans_le (min_le_right _ _))
    exact ⟨a,hθ.trans ha,(ha'.trans_le (min_le_left _ _)).le,by linarith only [hda],A,hA,h⟩
  · have he := le_antisymm zetaZeroAbscissa_le_one (le_of_not_gt hθ1)
    refine ⟨1,zero_lt_one,le_rfl,by rwa [mul_one,he],1,zero_le_one,fun k => ?_⟩
    simpa only [Real.rpow_one,one_mul] using norm_mobiusMertensPartialSum_le k

/-- Every sufficiently large cutoff contains more than K(N+1)^d
prefixes exceeding C(k+1)^b, for every b < Θ and d < 1. -/
theorem all_cutoffs_many_mertens_excursions {b d : ℝ} (hb : b<zetaZeroAbscissa)
    (hd : d<1) (C K : ℝ) :
    ∀ᶠ N : ℕ in atTop, K*((N:ℝ)+1)^d < ((mertensExcursions b C N).card:ℝ) := by
  have hθ := (by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa
  obtain ⟨t,ht,htθ⟩ := exists_between (max_lt hθ hb)
  obtain ⟨v,hv,hv1⟩ := exists_between (max_lt zero_lt_one hd)
  have ht0 := (le_max_left 0 b).trans_lt ht
  have hv0 := (le_max_left 0 d).trans_lt hv
  obtain ⟨a,ha,ha1,hva,A,hA,hM⟩ := upper_envelope hv0 hv1
  obtain ⟨B,hB,hpop⟩ := mertens_abel_mass_two_population ht0 (htθ.le.trans zetaZeroAbscissa_le_one)
    ha ha1 (abs_nonneg C) hA hM
  let e := max t (v*a)
  have he := max_lt htθ hva
  have he0 := ht0.le.trans (le_max_left t (v*a))
  filter_upwards [eventually_large_mertens_abel_mass he0 he (B*(1+(|K|+1)^a))] with N hlarge
  let X := (N:ℝ)+1
  have hX : 1≤X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have xp := zero_lt_one.trans_le hX
  let E := mertensExcursions t |C| N
  have hs : E ⊆ mertensExcursions b C N := by
    intro k hk
    obtain ⟨hkn,hk'⟩ := mem_filter.mp hk
    refine mem_filter.mpr ⟨hkn,lt_of_le_of_lt ?_ hk'⟩
    exact mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_left (Nat.cast_nonneg k)) ((le_max_right 0 b).trans ht.le))
      (Real.rpow_nonneg (by positivity) _) (abs_nonneg C)
  by_contra! hsmall
  have hm := (Nat.cast_le (α:=ℝ)).mpr (card_le_card hs)
  have htiny : (E.card:ℝ) ≤ |K|*X^v := (hm.trans hsmall).trans (mul_le_mul (le_abs_self K)
    (Real.rpow_le_rpow_of_exponent_le hX ((le_max_right 0 d).trans hv.le)) (Real.rpow_nonneg xp.le _) (abs_nonneg K))
  have hcount : (E.card:ℝ)+1 ≤ (|K|+1)*X^v := by linarith only [htiny,Real.one_le_rpow hX hv0.le]
  have hpow := Real.rpow_le_rpow (by positivity : 0≤(E.card:ℝ)+1) hcount ha.le
  rw [Real.mul_rpow (by positivity : 0≤|K|+1) (Real.rpow_nonneg xp.le _),←Real.rpow_mul xp.le] at hpow
  have hsc := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (le_max_right t (v*a)))
    (Real.rpow_nonneg (by positivity : 0≤|K|+1) a)
  have both : X^t+((E.card:ℝ)+1)^a ≤ (1+(|K|+1)^a)*X^e := by
    linarith only [hpow,hsc,Real.rpow_le_rpow_of_exponent_le hX (le_max_left t (v*a))]
  have hup := (hpop N).trans (mul_le_mul_of_nonneg_left both hB)
  change B*(1+(|K|+1)^a)*X^e < _ at hlarge
  linarith only [hlarge,hup]

#print axioms mertens_abel_mass_two_population
#print axioms all_cutoffs_many_mertens_excursions
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
