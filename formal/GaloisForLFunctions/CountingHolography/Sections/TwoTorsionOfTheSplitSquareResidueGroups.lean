import GaloisForLFunctions.CountingHolography.Sections.PrimeFactorMultiplicityOfTheSquareGenerator
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Two-torsion when each prime occurrence contributes a unit group

Every odd factor contributes one independent involution. Removing the
factors at two changes the signed factor count on a square conductor by
at most a quadratic term. Its positive leading asymptotic survives.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction ArithmeticWeightTheory
open _root_.RHTower _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

/-- Independent prime-field unit groups for all prime occurrences. -/
abbrev splitResidueUnits (m : ℕ) :=
  (p : ↥m.primeFactors) → Fin (m.factorization p.val) → (ZMod p.val)ˣ

/-- Number of odd factors, counted with multiplicity. -/
def oddFactorCount (m : ℕ) := ∑ p ∈ m.primeFactors, if p = 2 then 0 else m.factorization p

private theorem oddFactorCount_add_two (m : ℕ) : oddFactorCount m + m.factorization 2 = cardFactors m := by
  have htwo : (∑ p ∈ m.primeFactors, if p = 2 then m.factorization p else 0) = m.factorization 2 := by
    by_cases h : 2 ∈ m.primeFactors
    · simp [h]
    · have hz : m.factorization 2 = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using h)
      simp [h,hz]
  rw [oddFactorCount,← htwo,← sum_add_distrib,cardFactors_eq_sum_factorization,Finsupp.sum,Nat.support_factorization]
  exact sum_congr rfl fun p _ => by by_cases h : p = 2 <;> simp [h]

private theorem involutions_mod_prime {p : ℕ} (hp : p.Prime) :
    Nat.card (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).ker = if p = 2 then 1 else 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [IsCyclic.card_powMonoidHom_ker,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp]
  split_ifs with h
  · norm_num [h]
  · obtain ⟨k,hk⟩ := hp.odd_of_ne_two h
    apply Nat.gcd_eq_right.mpr
    exact ⟨k,by omega⟩

/-- A split residue group has exactly two to the odd factor count involutions,
including the identity. -/
theorem card_splitResidueUnits_two_torsion (m : ℕ) :
    Nat.card (powMonoidHom 2 : splitResidueUnits m →* splitResidueUnits m).ker = 2^(oddFactorCount m) := by
  classical
  let B := fun p : ↥m.primeFactors => (powMonoidHom 2 : (ZMod p.val)ˣ →* (ZMod p.val)ˣ).ker
  let A := (powMonoidHom 2 : splitResidueUnits m →* splitResidueUnits m).ker
  let e : A ≃ ((p : ↥m.primeFactors) → Fin (m.factorization p.val) → B p) := {
    toFun := fun a p j => ⟨a.val p j,congrFun (congrFun a.property p) j⟩
    invFun := fun b => ⟨fun p j => (b p j).val,funext fun p => funext fun j => (b p j).property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_pi]
  simp only [Nat.card_fun,Nat.card_eq_fintype_card (α := Fin _),Fintype.card_fin]
  have h (p : ↥m.primeFactors) : Nat.card (B p)^(m.factorization p.val) =
      2^(if p.val=2 then 0 else m.factorization p.val) := by
    rw [show Nat.card (B p)=_ from involutions_mod_prime (Nat.prime_of_mem_primeFactors p.property)]
    split_ifs <;> simp
  simp_rw [h]
  rw [← pow_sum,oddFactorCount]
  congr 1
  exact sum_attach _ _

private abbrev q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
private abbrev T (n : ℕ) := Real.log ((n:ℝ)^2)

/-- The exceptional factor at two has only quadratic valuation. -/
theorem square_exponent_at_two : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    |(deningerRatExp (q n) 2:ℝ)| ≤ C*(n:ℝ)^2 := by
  obtain ⟨D,hD,hrow⟩ := diagonal_prime_exponent_profile_error
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨D/Real.log 2,div_nonneg hD hlog.le,?_⟩
  have ht := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [eventually_gt_atTop 0,ht.eventually_gt_atTop (Real.log 2+8)] with n hn ht
  let S := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
  change Real.log 2+8 < T n at ht
  have hl₄ : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h₁ := splineAutoCorr_zero_outside (x := Real.log 2-T n)
    (by linarith only [ht,neg_abs_le (Real.log 2-T n)])
  have h₂ := splineAutoCorr_zero_outside (x := Real.log 2-T n-Real.log 4)
    (by linarith only [ht,hl₄,neg_abs_le (Real.log 2-T n-Real.log 4)])
  have hz : diagonalPrimeProfile n 2 = 0 := by simp [diagonalPrimeProfile,squareLogProfile,T] at h₁ h₂ ⊢; simp [h₁,h₂]
  by_cases hmem : 2 ∈ S
  · have he := (single_le_sum (f := fun p => |(deningerRatExp (q n) p:ℝ)-diagonalPrimeProfile n p|*vonMangoldt p)
        (fun p _ => mul_nonneg (abs_nonneg _) vonMangoldt_nonneg) hmem).trans (hrow hn)
    rw [hz,sub_zero,vonMangoldt_apply_prime Nat.prime_two,Nat.cast_ofNat] at he
    exact ((le_div_iff₀ hlog).mpr he).trans_eq (by ring)
  · have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) 2
    change deningerRatExp (q n) 2 = if 2 ∈ S then _ else 0 at he
    rw [if_neg hmem] at he
    rw [he,Int.cast_zero,abs_zero]; positivity

/-- The signed odd-factor count has the same positive cubic-over-log-squared
asymptotic as the signed count over all primes. -/
theorem tendsto_square_generator_two_torsion_rank_difference :
    Tendsto (fun n : ℕ => T n^2*((oddFactorCount (q n).num.natAbs:ℝ)-oddFactorCount (q n).den)/(n:ℝ)^3)
      atTop (𝓝 (4*Real.log 4*squareAutocorrelationMass)) := by
  obtain ⟨C,hC,h⟩ := square_exponent_at_two
  have hlog := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul 2
  have ht : Tendsto (fun n : ℕ => T n/(n:ℝ)^(1/2:ℝ)) atTop (𝓝 0) := by
    simpa only [T,Real.log_pow,Nat.cast_ofNat,mul_div_assoc,mul_zero,Function.comp_apply] using hlog
  have he : Tendsto (fun n : ℕ => T n^2*(deningerRatExp (q n) 2:ℝ)/(n:ℝ)^3) atTop (𝓝 0) := by
    have hh := (ht.pow 2).const_mul C
    simp only [zero_pow two_ne_zero,mul_zero] at hh
    apply squeeze_zero_norm' _ hh
    filter_upwards [h,eventually_gt_atTop 0] with n hₙ hn
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    rw [Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_pos (pow_pos hn' 3)]
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hₙ (sq_nonneg _)) (pow_nonneg hn'.le _)).trans_eq ?_
    rw [div_pow,← Real.sqrt_eq_rpow,Real.sq_sqrt hn'.le]; field_simp
  have hz := tendsto_square_generator_prime_multiplicity.sub he
  rw [sub_zero] at hz
  refine hz.congr fun n => ?_
  have hu := congrArg (fun a : ℕ => (a:ℝ)) (oddFactorCount_add_two (q n).num.natAbs)
  have hv := congrArg (fun a : ℕ => (a:ℝ)) (oddFactorCount_add_two (q n).den)
  simp only [Nat.cast_add] at hu hv
  simp only [deningerRatExp_apply,Int.cast_sub,Int.cast_natCast]
  change T n^2*((cardFactors _:ℝ)-cardFactors _)/(n:ℝ)^3 - _ = _
  rw [← hu,← hv]; ring

private theorem two_torsion_le_kernel_mul {G H : Type*} [CommGroup G] [CommGroup H]
    [Finite G] [Finite H] (f : G →* H) :
    Nat.card (powMonoidHom 2 : G →* G).ker ≤
      Nat.card f.ker * Nat.card (powMonoidHom 2 : H →* H).ker := by
  let A := (powMonoidHom 2 : G →* G).ker
  let B := (powMonoidHom 2 : H →* H).ker
  let g : A →* B := {
    toFun := fun x => ⟨f x.val,by
      change (f x.val)^2 = 1
      rw [← map_pow,show x.val^2=1 from x.property,map_one]⟩
    map_one' := Subtype.ext f.map_one
    map_mul' := fun a b => Subtype.ext (f.map_mul _ _) }
  let i : g.ker → f.ker := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hi : Function.Injective i := fun _ _ h => Subtype.ext (Subtype.ext (congrArg Subtype.val h))
  have hk := Nat.card_le_card_of_injective i hi
  have hr := Nat.card_le_card_of_injective (fun x : g.range => (x.val:B)) Subtype.val_injective
  have he := g.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  exact he.symm.trans_le (Nat.mul_le_mul hk hr)

/-- The two-torsion rank deficit is a lower bound on the logarithmic kernel
size of every homomorphism between the split residue groups. -/
theorem splitResidueUnits_kernel_lower (u v : ℕ) (f : splitResidueUnits u →* splitResidueUnits v) :
    ((oddFactorCount u:ℝ)-oddFactorCount v)*Real.log 2 ≤ Real.log (Nat.card f.ker) := by
  letI (p : ↥u.primeFactors) : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  letI (p : ↥v.primeFactors) : NeZero p.val := ⟨(Nat.prime_of_mem_primeFactors p.property).ne_zero⟩
  have h := two_torsion_le_kernel_mul f
  rw [card_splitResidueUnits_two_torsion,card_splitResidueUnits_two_torsion] at h
  have he : (2:ℝ)^oddFactorCount u ≤ (Nat.card f.ker:ℝ)*2^oddFactorCount v := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) he
  rw [Real.log_mul (Nat.cast_pos.mpr Nat.card_pos).ne' (by positivity),Real.log_pow,Real.log_pow] at hl
  linarith only [hl]

/-- Even an arbitrarily large fixed quadratic log allowance eventually fails
for every map from the split numerator group to the split denominator group. -/
theorem square_split_units_kernel_exceeds_quadratic (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ f : splitResidueUnits (q n).num.natAbs →* splitResidueUnits (q n).den,
        C*(n:ℝ)^2 < Real.log (Nat.card f.ker) := by
  let c := 4*Real.log 4*squareAutocorrelationMass
  have hc : 0 < c := mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) squareAutocorrelationMass_pos
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have ht := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop).const_mul 2
  have hsmall : Tendsto (fun n : ℕ => T n / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [T,Real.log_pow,Nat.cast_ofNat,mul_div_assoc,mul_zero,Function.comp_apply,Real.sqrt_eq_rpow] using ht
  have hs := (hsmall.pow 2).const_mul (C/Real.log 2)
  simp only [zero_pow two_ne_zero,mul_zero] at hs
  filter_upwards [eventually_gt_atTop 1,hs.eventually (gt_mem_nhds (half_pos hc)),
    tendsto_square_generator_two_torsion_rank_difference.eventually (lt_mem_nhds (show c/2 < c by linarith only [hc]))]
    with n hn h₁ h₂
  intro f
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0 < T n := Real.log_pos (one_lt_pow₀ (by exact_mod_cast hn : (1:ℝ)<n) two_ne_zero)
  have hcmp := h₁.trans h₂
  rw [div_pow,Real.sq_sqrt hn'.le] at hcmp
  have hbig := (lt_div_iff₀ (pow_pos hn' 3)).mp hcmp
  have he : C/Real.log 2*(T n^2/(n:ℝ))*(n:ℝ)^3 =
      (C*(n:ℝ)^2/Real.log 2)*T n^2 := by field_simp; ring
  rw [he,mul_comm (T n^2)] at hbig
  have h := (div_lt_iff₀ hlog).mp ((mul_lt_mul_iff_left₀ (sq_pos_of_pos hl)).mp hbig)
  exact h.trans_le (splitResidueUnits_kernel_lower _ _ f)

end GaloisForLFunctions.CountingHolography.Sections
