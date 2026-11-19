import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheQDeformationOfTheHorizonPeriod
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples
import GaloisForLFunctions.RHTower.CausalMobiusThetaPhysicalSource
import Mathlib.NumberTheory.Primorial

/-!
# A signed divisibility average of the primitive cofactors

Sampling on multiples of d with coefficient M(⌊V/d⌋) retains total weight
one. Its coprimality reading for v is the truncated divisor sum of μ. All
proper cofactors through V vanish. The first surviving octave reads −μ(v).
-/

noncomputable section
open Finset ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
open RHTower (truncMoebiusDivisorSum truncMoebiusDivisorSum_eq_sum_divisors_filter)
open scoped ArithmeticFunction.Moebius
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem multiples_mertens_weight {V e : ℕ} (he : 0 < e) :
    (∑ d ∈ (Icc 1 V).filter (fun d => e ∣ d),mertens (V/d)) = if e ≤ V then 1 else 0 := by
  rw [_root_.RHTower.Sieve.sum_filter_dvd_eq_sum_scaled he]
  simp only [←Nat.div_div_eq_div_mul]
  by_cases h : e ≤ V
  · rw [if_pos h]
    exact sum_mertens_floor_eq_one ((Nat.le_div_iff_mul_le he).mpr (by simpa only [one_mul] using h))
  · rw [if_neg h,Nat.div_eq_of_lt (lt_of_not_ge h)]
    simp

/-- A cofactor reads exactly its truncated Möbius divisor sum under the
same normalized weights at every sieve level. -/
theorem signed_coprime_cofactor_projection (V : ℕ) {v : ℕ} (hv : 0 < v) :
    (∑ d ∈ (Icc 1 V).filter (v.Coprime ·),mertens (V/d)) = truncMoebiusDivisorSum V v := by
  rw [sum_filter]
  calc _ = ∑ d ∈ Icc 1 V,(if v.Coprime d then (1:ℝ) else 0)*mertens (V/d) := by
             exact sum_congr rfl fun d _ => by split_ifs <;> simp
       _ = ∑ e ∈ v.divisors,(μ e:ℝ)*∑ d ∈ (Icc 1 V).filter (fun d => e ∣ d),mertens (V/d) := by
             simp only [reflected_coprime_indicator hv,sum_mul,sum_filter,mul_sum]
             rw [sum_comm]
             apply sum_congr rfl
             intro e _
             exact sum_congr rfl fun d _ => by split_ifs <;> simp
       _ = _ := by
             rw [truncMoebiusDivisorSum_eq_sum_divisors_filter _ hv.ne',sum_filter]
             apply sum_congr rfl
             intro e he
             rw [multiples_mertens_weight (Nat.pos_of_mem_divisors he)]
             split_ifs <;> simp

#print axioms signed_coprime_cofactor_projection

/-- Every proper cofactor up to V vanishes identically in the projected sum. -/
theorem projected_proper_cofactor_zero {V v : ℕ} (hv : 1 < v) (hV : v ≤ V) :
    (∑ d ∈ (Icc 1 V).filter (v.Coprime ·),mertens (V/d))=0 := by
  rw [signed_coprime_cofactor_projection _ (by omega),_root_.RHTower.truncMoebiusDivisorSum_of_le hv.le hV,if_neg hv.ne']

/-- The moving lower cofactor boundary transfers the entire first octave
onto the signed Möbius function of the actual cofactor. -/
theorem first_projected_cofactor_octave {V v : ℕ} (hv : 1 < v) (hlo : V < v) (hhi : v ≤ 2*V) :
    (∑ d ∈ (Icc 1 V).filter (v.Coprime ·),mertens (V/d)) = -(μ v:ℝ) := by
  rw [signed_coprime_cofactor_projection _ (by omega),
    truncMoebiusDivisorSum_eq_sum_divisors_filter _ (by omega)]
  have hlast : v.divisors.filter (fun e => ¬e ≤ V)={v} := by
    ext e
    simp only [mem_filter,mem_singleton]
    constructor
    · rintro ⟨he,heV⟩
      by_contra h
      obtain ⟨j,hj⟩ := Nat.dvd_of_mem_divisors he
      have hj2 : 2 ≤ j := by
        have hj0 : j ≠ 0 := by rintro rfl; rw [mul_zero] at hj; omega
        have hj1 : j ≠ 1 := by rintro rfl; exact h (by simpa only [mul_one] using hj.symm)
        omega
      have h2 := Nat.mul_le_mul_left e hj2
      rw [←hj] at h2
      omega
    · rintro rfl
      exact ⟨Nat.mem_divisors.mpr ⟨dvd_refl _,by omega⟩,not_le.mpr hlo⟩
  have hs := sum_filter_add_sum_filter_not v.divisors (· ≤ V) (fun e => (μ e:ℝ))
  rw [hlast,sum_singleton,_root_.RHTower.Sieve.sum_divisors_moebius_real,if_neg hv.ne'] at hs
  linarith only [hs]

#print axioms projected_proper_cofactor_zero
#print axioms first_projected_cofactor_octave

/-- A prime above the level disappears from every divisor test in the
truncated row. If the other factor is within the level, only a unit
partner survives. -/
theorem projected_weight_at_large_prime {V p u : ℕ} (hp : p.Prime) (hVp : V < p)
    (hu : 1 ≤ u) (huV : u ≤ V) :
    truncMoebiusDivisorSum V (u*p) = if u=1 then 1 else 0 := by
  have hs : (Icc 1 V).filter (fun e => e ∣ u*p)=(Icc 1 V).filter (fun e => e ∣ u) := by
    apply filter_congr
    intro e he
    obtain ⟨he0,heV⟩ := mem_Icc.mp he
    have hc : p.Coprime e := hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt he0 (heV.trans_lt hVp))
    exact hc.symm.dvd_mul_right
  calc _ = truncMoebiusDivisorSum V u := by unfold _root_.RHTower.truncMoebiusDivisorSum; rw [hs]
       _ = _ := _root_.RHTower.truncMoebiusDivisorSum_of_le hu huV

/-- Up to the square of the cutoff every surviving cofactor carrying a
larger prime is that prime itself, with exact coefficient one. -/
theorem surviving_cofactor_with_large_prime {V v p : ℕ} (hv : 1 ≤ v) (hsq : v ≤ V^2)
    (hp : p.Prime) (hVp : V < p) (hdiv : p ∣ v) :
    truncMoebiusDivisorSum V v = if v=p then 1 else 0 := by
  let u := v/p
  have hmul : u*p=v := Nat.div_mul_cancel hdiv
  have hu : 1 ≤ u := Nat.div_pos (Nat.le_of_dvd hv hdiv) hp.pos
  have huV : u ≤ V := by
    by_contra! h
    have hbad := Nat.mul_lt_mul_of_lt_of_lt h hVp
    rw [hmul,←pow_two] at hbad
    exact (not_lt_of_ge hsq) hbad
  have eq1 : u=1 ↔ v=p := by
    constructor
    · intro h; simpa only [h,one_mul] using hmul.symm
    · rintro rfl; exact Nat.div_self hp.pos
  rw [←hmul,projected_weight_at_large_prime hp hVp hu huV,hmul]
  simp only [eq1]

#print axioms surviving_cofactor_with_large_prime

/-- Total variation and its first divisibility moment, for use on short
intervals whose number of multiples depends on d. -/
theorem cofactor_projection_weight_cost (V : ℕ) :
    (∑ d ∈ Icc 1 V,|mertens (V/d)|) ≤ V*(1+Real.log V) ∧
      (∑ d ∈ Icc 1 V,(d:ℝ)*|mertens (V/d)|) ≤ (V:ℝ)^2 := by
  have hM (j : ℕ) : |mertens j| ≤ j := by
    apply (abs_sum_le_sum_abs (fun i => (μ i:ℝ)) (Icc 1 j)).trans
    calc _ ≤ ∑ _ ∈ Icc 1 j,(1:ℝ) := by
               apply sum_le_sum
               intro i _
               exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=i)
         _ = j := by simp [Nat.card_Icc]
  have hd (d : ℕ) : |mertens (V/d)| ≤ (V:ℝ)/d := (hM _).trans Nat.cast_div_le
  constructor
  · apply (sum_le_sum (s:=Icc 1 V) (fun d _ => hd d)).trans
    calc _ = (V:ℝ)*∑ d ∈ Icc 1 V,1/(d:ℝ) := by rw [mul_sum]; simp only [mul_one_div]
         _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log V) (Nat.cast_nonneg _)
  · calc _ ≤ ∑ _ ∈ Icc 1 V,(V:ℝ) := by
               apply sum_le_sum
               intro d h
               have hd0 := (Nat.cast_pos (α:=ℝ)).mpr (mem_Icc.mp h).1
               exact (mul_le_mul_of_nonneg_left (hd d) hd0.le).trans_eq (mul_div_cancel₀ _ hd0.ne')
         _ = _ := by simp [Nat.card_Icc,pow_two]

#print axioms cofactor_projection_weight_cost

/-- Primitive frequency among the multiples d k in a consecutive
window of L quotient indices. -/
def sampledCofactorFrequency (v d a L : ℕ) : ℝ :=
  (∑ k ∈ Ioc a (a+L),if v.Coprime (d*k) then (1:ℝ) else 0)/L

private theorem primitive_window_error {v : ℕ} (hv : 0 < v) (a L : ℕ) :
    |(∑ k ∈ Ioc a (a+L),if v.Coprime k then (1:ℝ) else 0) -
      (v.totient:ℝ)/v*L| ≤ squarefreeDivisorMass v := by
  let I := Ioc a (a+L)
  have count : (∑ k ∈ I,if v.Coprime k then (1:ℝ) else 0) =
      ∑ e ∈ v.divisors,(μ e:ℝ)*((I.filter (fun k => e ∣ k)).card:ℝ) := by
    simp only [reflected_coprime_indicator hv]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
  change |(∑ k ∈ I,_)-_| ≤ _
  rw [count,←_root_.RHTower.Sieve.sum_moebius_div_divisors_eq_totient_div hv,sum_mul,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro e he
  have hh := _root_.RHTower.Sieve.abs_card_filter_dvd_Ioc_sub_lt e a (a+L) (Nat.pos_of_mem_divisors he) (by omega)
  rw [Nat.cast_add,add_sub_cancel_left] at hh
  rw [show (μ e:ℝ)*((I.filter (fun k => e ∣ k)).card:ℝ)-(μ e:ℝ)/e*L =
    (μ e:ℝ)*(((I.filter (fun k => e ∣ k)).card:ℝ)-(L:ℝ)/e) by ring,abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hh.le

/-- The finite quotient-window frequency has its true coprime density
with one endpoint error per squarefree divisor, at every starting point. -/
theorem sampled_cofactor_frequency_error {v L : ℕ} (hv : 0 < v) (hL : 0 < L) (d a : ℕ) :
    |sampledCofactorFrequency v d a L-(if v.Coprime d then (v.totient:ℝ)/v else 0)| ≤
      squarefreeDivisorMass v/L := by
  by_cases hc : v.Coprime d
  · have eqn (k : ℕ) : v.Coprime (d*k) ↔ v.Coprime k :=
      Nat.coprime_mul_iff_right.trans (and_iff_right hc)
    rw [if_pos hc]
    simp only [sampledCofactorFrequency,eqn]
    have hL' := (Nat.cast_pos (α:=ℝ)).mpr hL
    rw [show (∑ k ∈ Ioc a (a+L),if v.Coprime k then (1:ℝ) else 0)/L-(v.totient:ℝ)/v =
      ((∑ k ∈ Ioc a (a+L),if v.Coprime k then (1:ℝ) else 0)-(v.totient:ℝ)/v*L)/L by
        rw [sub_div,mul_div_cancel_right₀ _ hL'.ne'],abs_div,abs_of_pos hL']
    exact div_le_div_of_nonneg_right (primitive_window_error hv a L) hL'.le
  · have hnone (k : ℕ) : ¬v.Coprime (d*k) := fun h => hc (Nat.coprime_mul_iff_right.mp h).1
    rw [if_neg hc]
    simp only [sampledCofactorFrequency,if_neg (hnone _),sum_const_zero,zero_div,sub_self,abs_zero]
    exact div_nonneg (sum_nonneg fun _ _ => abs_nonneg _) (Nat.cast_nonneg _)

/-- The signed multiple-frequency average gives the projected cofactor
density even for windows of different lengths and arbitrary starting points. -/
theorem signed_window_cofactor_density (V : ℕ) {v : ℕ} (hv : 0 < v) (a L : ℕ → ℕ)
    (hL : ∀ d ∈ Icc 1 V,0 < L d) :
    |(∑ d ∈ Icc 1 V,mertens (V/d)*sampledCofactorFrequency v d (a d) (L d))-
      (v.totient:ℝ)/v*truncMoebiusDivisorSum V v| ≤
      squarefreeDivisorMass v*∑ d ∈ Icc 1 V,|mertens (V/d)|/(L d:ℝ) := by
  rw [←signed_coprime_cofactor_projection _ hv,sum_filter,mul_sum,←sum_sub_distrib,mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  let M := mertens (V/d)
  let ρ := (v.totient:ℝ)/v
  let f := sampledCofactorFrequency v d (a d) (L d)
  have eqn : M*f-ρ*(if v.Coprime d then M else 0) = M*(f-(if v.Coprime d then ρ else 0)) := by
    split_ifs <;> ring
  rw [eqn,abs_mul]
  exact (mul_le_mul_of_nonneg_left (sampled_cofactor_frequency_error hv (hL d hd) d (a d))
    (abs_nonneg M)).trans_eq (by ring)

#print axioms signed_window_cofactor_density

/-- Every normalized signed sample which removes all prime cofactors up
to V pays at least log(V#) in total log modulus. -/
theorem signed_sampling_primorial_cost (V : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hpos : ∀ m ∈ S,0 < m) (hw : ∑ m ∈ S,w m=1)
    (hremove : ∀ p ∈ Nat.primesLE V,(∑ m ∈ S.filter (p.Coprime ·),w m)=0) :
    Real.log (primorial V) ≤ ∑ m ∈ S,|w m| * Real.log m := by
  let P := Nat.primesLE V
  have hdiv (p : ℕ) (hp : p ∈ P) : (∑ m ∈ S.filter (fun m => p ∣ m),w m)=1 := by
    have h := sum_filter_add_sum_filter_not S (p.Coprime ·) w
    rw [hremove p hp,zero_add,hw] at h
    simpa only [(Nat.prime_of_mem_primesLE hp).coprime_iff_not_dvd,not_not] using h
  have hlocal (m : ℕ) (hm : m ∈ S) :
      (∑ p ∈ P.filter (fun p => p ∣ m),Real.log p) ≤ Real.log m := by
    let F := P.filter (fun p => p ∣ m)
    have hsub : F ⊆ m.primeFactors := fun p hp => Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primesLE (mem_filter.mp hp).1,(mem_filter.mp hp).2,(hpos m hm).ne'⟩
    have hd := (prod_dvd_prod_of_subset F m.primeFactors id hsub).trans (Nat.prod_primeFactors_dvd m)
    have hp (p : ℕ) (h : p ∈ F) : 0 < p := (Nat.prime_of_mem_primeFactors (hsub h)).pos
    have hP : 0 < ∏ p ∈ F,p := prod_pos hp
    have h := Real.log_le_log (Nat.cast_pos.mpr hP) ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_of_dvd (hpos m hm) hd))
    rwa [Nat.cast_prod,Real.log_prod (fun p h => Nat.cast_ne_zero.mpr (hp p h).ne')] at h
  have hθ : Real.log (primorial V)=∑ p ∈ P,Real.log p := by
    rw [primorial_eq_prod_primesLE,Nat.cast_prod,Real.log_prod]
    intro p hp
    exact Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primesLE hp).ne_zero
  rw [hθ]
  calc _ = ∑ p ∈ P,∑ m ∈ S,if p ∣ m then w m*Real.log p else 0 := by
             apply sum_congr rfl
             intro p hp
             rw [←sum_filter,←sum_mul,hdiv p hp,one_mul]
       _ = ∑ m ∈ S,w m*∑ p ∈ P.filter (fun p => p ∣ m),Real.log p := by
             rw [sum_comm]
             apply sum_congr rfl
             intro m _
             rw [mul_sum,sum_filter]
       _ ≤ _ := by
             apply sum_le_sum
             intro m hm
             exact mul_le_mul (le_abs_self _) (hlocal m hm) (sum_nonneg fun p _ => Real.log_natCast_nonneg p) (abs_nonneg _)

#print axioms signed_sampling_primorial_cost

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
