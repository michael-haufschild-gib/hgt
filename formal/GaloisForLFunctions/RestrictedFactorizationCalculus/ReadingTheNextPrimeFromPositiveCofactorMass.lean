import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTwoPrimeBoundariesOfPolynomialCofactorBands
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# Reading the next prime from positive cofactor mass

On the square cofactor band the positive signal is a single prime interval.
A power bound for its endpoint errors is uniform under independent proper
prime-power edits. Inverting the reciprocal endpoint and rounding recovers
the first allowed prime from the signal alone.
-/
noncomputable section
open Finset Filter ArithmeticFunction _root_.RHTower.CoprimeMobius
open GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem nonprime_cost {s : ℝ} (hs : 1/2 < s) (hu : s ≤ 1) (X : ℕ) :
    (∑ q ∈ (Icc 1 X).filter (fun q => ¬q.Prime), vonMangoldt q) ≤
      (36/(s-1/2))*(X:ℝ)^s := by
  have sp : 0 < s := (by norm_num : (0:ℝ) < 1/2).trans hs
  have paid := _root_.RHTower.sum_nonprime_vonMangoldt_rpow_le (sub_pos.mpr hs)
    (by linarith only [hu] : s-1/2 ≤ 1) X
  rw [show 1/2+(s-1/2)=s by ring] at paid
  have point (q : ℕ) (hq : q ∈ (Icc 1 X).filter (fun q => ¬q.Prime)) :
      vonMangoldt q ≤ vonMangoldt q*(q:ℝ)^(-s)*(X:ℝ)^s := by
    obtain ⟨lo,hi⟩ := mem_Icc.mp (mem_filter.mp hq).1
    have qr := (Nat.cast_pos (α:=ℝ)).mpr lo
    have hle := Real.rpow_le_rpow qr.le (Nat.cast_le.mpr hi) sp.le
    rw [Real.rpow_neg qr.le,← div_eq_mul_inv]
    calc vonMangoldt q = (vonMangoldt q/(q:ℝ)^s)*(q:ℝ)^s :=
           (div_mul_cancel₀ _ (Real.rpow_pos_of_pos qr s).ne').symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hle (div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg qr.le _))
  apply (sum_le_sum point).trans
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right paid (Real.rpow_nonneg (Nat.cast_nonneg X) s)

/-- The power error in a prime interval past a wall is uniform in its lower
endpoint and in the individual edits at every proper prime power. -/
theorem prime_interval_power_cost_above_the_abscissa {s : ℝ} (hs : _root_.RHTower.zetaZeroAbscissa < s)
    (hu : s ≤ 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y K X : ℕ, 1 ≤ K → y ≤ K → K ≤ X →
    ∀ a : ArithmeticFunction ℝ, (∀ n,|a n| ≤ vonMangoldt n) →
    (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |(∑ n ∈ Ioc K X,a n)-((X:ℝ)-K)| ≤ C*(X:ℝ)^s := by
  obtain ⟨B,hB,psi⟩ := _root_.RHTower.exists_psiRemainder_le_rpow_zetaZeroAbscissa
    (s-_root_.RHTower.zetaZeroAbscissa) (sub_pos.mpr hs)
  rw [add_sub_cancel_left] at psi
  have sh := _root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hs
  have sp := (by norm_num : (0:ℝ) < 1/2).trans sh
  let D := 36/(s-1/2)
  have hd : 0 ≤ D := div_nonneg (by norm_num) (sub_pos.mpr sh).le
  refine ⟨2*(B+D),by positivity,?_⟩
  intro y K X hK hy hX a dom same
  let I := Ioc K X
  let f := fun n => a n-vonMangoldt n
  have point (q : ℕ) (hq : q ∈ I) :
      |f q| ≤ if ¬q.Prime then 2*vonMangoldt q else 0 := by
    by_cases hp : q.Prime
    · have free : IsFree (RoughReading.banned y) q :=
        (isFree_prime _ hp).mpr (not_le.mpr (hy.trans_lt (mem_Ioc.mp hq).1))
      simp only [f,same q hp,roughMangoldtWeight,roughRestriction_apply,if_pos free,
        sub_self,abs_zero,hp,not_true_eq_false,if_false,le_rfl]
    · rw [if_pos hp]
      exact (abs_sub ..).trans (by rw [abs_of_nonneg (vonMangoldt_nonneg (n:=q)),two_mul]; exact add_le_add_right (dom q) _)
  have sub : I.filter (fun q => ¬q.Prime) ⊆ (Icc 1 X).filter (fun q => ¬q.Prime) := by
    intro q h
    obtain ⟨hi,hp⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(Nat.zero_le K).trans_lt (mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2⟩,hp⟩
  have cost := (abs_sum_le_sum_abs I f).trans (sum_le_sum point)
  rw [←sum_filter,←mul_sum] at cost
  have subcost := (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => vonMangoldt_nonneg)).trans (nonprime_cost sh hu X)
  have diff : |(∑ q ∈ I,a q)-(∑ q ∈ I,vonMangoldt q)| ≤ 2*(D*(X:ℝ)^s) := by
    rw [←sum_sub_distrib]
    exact cost.trans (mul_le_mul_of_nonneg_left subcost (by norm_num))
  have sets : Icc 1 X \ Icc 1 K = I := by ext q; simp only [I,mem_sdiff,mem_Icc,mem_Ioc]; omega
  have psiDiff : (∑ q ∈ I,vonMangoldt q) = _root_.RHTower.chebyshevPsi X-_root_.RHTower.chebyshevPsi K := by
    rw [←sets,sum_sdiff_eq_sub (Icc_subset_Icc_right hX)]; rfl
  rw [psiDiff] at diff
  have small := (psi K hK).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hX) sp.le) hB)
  have large := psi X (hK.trans hX)
  unfold _root_.RHTower.psiRemainder at small large
  apply abs_le.mpr
  constructor <;> linarith only [(abs_le.mp diff).1,(abs_le.mp diff).2,(abs_le.mp small).1,
    (abs_le.mp small).2,(abs_le.mp large).1,(abs_le.mp large).2]

/-- Read an integral reciprocal endpoint by rounding to the nearest integer. -/
def decodePositiveCofactorMass (X : ℕ) (M : ℝ) := ⌊(X:ℝ)/((X:ℝ)-M)+1/2⌋₊

private theorem recover_reciprocal {p X : ℕ} {M E : ℝ} (hp : 0 < p) (he : 0 ≤ E)
    (reading : |M-((X:ℝ)-(X:ℝ)/p)| ≤ E) (enough : 4*(p:ℝ)^2*E < X) :
    decodePositiveCofactorMass X M = p := by
  let d := (X:ℝ)-M
  have pp : 0 < (p:ℝ) := Nat.cast_pos.mpr hp
  have p1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have ep := mul_nonneg he pp.le
  have ep2 := le_mul_of_one_le_right ep p1
  have err : |(X:ℝ)-d*p| ≤ E*p := by
    have eq : (X:ℝ)-d*p = (M-((X:ℝ)-(X:ℝ)/p))*p := by
      dsimp only [d]; field_simp [pp.ne'] <;> ring
    rw [eq,abs_mul,abs_of_pos pp]
    exact mul_le_mul_of_nonneg_right reading pp.le
  have gap : 2*(E*p) < d := by
    apply (mul_lt_mul_iff_left₀ pp).mp
    nlinarith only [enough,(abs_le.mp err).2,ep2]
  have dp : 0 < d := (mul_nonneg (by norm_num) ep).trans_lt gap
  have he' : |(X:ℝ)/d-p| < 1/2 := by
    rw [div_sub' _ _ dp.ne',abs_div,abs_of_pos dp,div_lt_iff₀ dp]
    have eq : (X:ℝ)-(p:ℝ)*d = (X:ℝ)-d*p := by ring
    rw [eq]
    linarith only [err,gap]
  apply (Nat.floor_eq_iff (show 0 ≤ (X:ℝ)/d+1/2 by positivity)).mpr
  constructor <;> linarith only [(abs_lt.mp he').1,(abs_lt.mp he').2]

/-- Every growing wall y ≤ X^α with 2α+Θ < 1 can be decoded from the
positive mass at the square cofactor cutoff, even with all proper powers edited. -/
theorem next_prime_from_positive_band_mass {α : ℝ} (ha : 0 ≤ α)
    (room : 2*α+_root_.RHTower.zetaZeroAbscissa < 1) (b : ℕ → ℕ)
    (grow : Tendsto b atTop atTop) (small : ∀ᶠ X : ℕ in atTop, (b X:ℝ) ≤ (X:ℝ)^α) :
    ∀ᶠ X : ℕ in atTop, ∀ a : ArithmeticFunction ℝ, (∀ n,|a n| ≤ vonMangoldt n) →
      (∀ p,p.Prime → a p=roughMangoldtWeight (b X) p) →
      decodePositiveCofactorMass X (positivePrimeBandMass a (b X) X ((b X)^2)) =
        nextRoughPrime (b X) := by
  let s := (_root_.RHTower.zetaZeroAbscissa+(1-2*α))/2
  let η := 1-(2*α+s)
  have hs : _root_.RHTower.zetaZeroAbscissa < s := by dsimp only [s]; linarith only [room]
  have hu : s ≤ 1 := by dsimp only [s]; linarith only [room,ha]
  have hη : 0 < η := by dsimp only [η,s]; linarith only [room]
  have sp := (by norm_num : (0:ℝ) < 1/2).trans (_root_.RHTower.half_le_zetaZeroAbscissa.trans_lt hs)
  obtain ⟨C,hC,cap⟩ := prime_interval_power_cost_above_the_abscissa hs hu
  have Xgrow := (tendsto_rpow_atTop hη).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [small,grow.eventually_ge_atTop 4,grow (positive_band_is_an_exact_prime_cut 2),
    Xgrow.eventually_gt_atTop (16*(C+1)),eventually_ge_atTop 1] with X hy hy4 exactBand price hx
  intro a dom same
  let y := b X
  let p := nextRoughPrime y
  have yp : 0 < y := by change 4 ≤ y at hy4;omega
  have px := nextPrime_prime (((y+1:ℕ):ℝ))
  have pp : 0 < p := px.pos
  have yp' : y < p := by
    have h := GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff.le_nextPrime (((y+1:ℕ):ℝ))
    exact_mod_cast h
  obtain ⟨P,hP,hyp,hi⟩ := Nat.exists_prime_lt_and_le_two_mul y yp.ne'
  have pbound : p ≤ 2*y := (GaloisForLFunctions.ArithmeticPositiveDuality.RationalPrimeOneOff.nextPrime_le
    hP (show (((y+1:ℕ):ℝ)) ≤ P by exact_mod_cast hyp)).trans hi
  have py2 : p ≤ y^2 := pbound.trans (by simpa only [pow_two] using Nat.mul_le_mul_right y (show 2 ≤ y by omega))
  have xp : 0 < (X:ℝ) := Nat.cast_pos.mpr hx
  have X1 : (1:ℝ) ≤ X := by exact_mod_cast hx
  have xsp : 1 ≤ (X:ℝ)^s := Real.one_le_rpow X1 sp.le
  have pr := (Nat.cast_pos (α:=ℝ)).mpr pp
  have pq : (p:ℝ) ≤ 2*(X:ℝ)^α := (show (p:ℝ) ≤ 2*y by exact_mod_cast pbound).trans
    (mul_le_mul_of_nonneg_left hy (by norm_num))
  have hsq := pow_le_pow_left₀ pr.le pq 2
  have collapse : ((X:ℝ)^α)^2=(X:ℝ)^(2*α) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul xp.le]; congr 1; push_cast; ring
  rw [mul_pow,collapse] at hsq
  let E := (C+1)*(X:ℝ)^s
  have e1 : 1 ≤ E := one_le_mul_of_one_le_of_one_le (by linarith only [hC]) xsp
  have budget : 4*(p:ℝ)^2*E < X := by
    have scaled := mul_lt_mul_of_pos_right (show 16*(C+1)<(X:ℝ)^η from price) (Real.rpow_pos_of_pos xp (2*α+s))
    rw [←Real.rpow_add xp,show η+(2*α+s)=1 by dsimp only [η];ring,Real.rpow_one] at scaled
    apply lt_of_le_of_lt _ scaled
    rw [Real.rpow_add xp]
    dsimp only [E]
    calc _ ≤ 4*(2^2*(X:ℝ)^(2*α))*((C+1)*(X:ℝ)^s) :=
             mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (mul_nonneg (by linarith only [hC]) (Real.rpow_nonneg xp.le _))
         _ = _ := by ring
  have room' : p*p ≤ X := by
    have stay := le_mul_of_one_le_right (sq_nonneg (p:ℝ)) e1
    have big1 := le_mul_of_one_le_left (mul_nonneg (sq_nonneg (p:ℝ)) (zero_le_one.trans e1)) (by norm_num : (1:ℝ) ≤ 4)
    have le : (p:ℝ)^2 ≤ X := stay.trans (big1.trans (by linarith only [budget]))
    exact_mod_cast (by simpa only [pow_two] using le : (p:ℝ)*p ≤ X)
  have pK : p ≤ X/p := (Nat.le_div_iff_mul_le pp).mpr room'
  have hband := exactBand (y^2) X (pow_pos yp _) le_rfl a
  rw [min_eq_right py2] at hband
  have h := cap y (X/p) X (pp.trans_le pK) (yp'.le.trans pK) (Nat.div_le_self ..) a dom same
  have lower := (Nat.cast_le (α:=ℝ)).mpr (Nat.div_mul_le_self X p)
  have upper := (Nat.cast_lt (α:=ℝ)).mpr ((Nat.div_lt_iff_lt_mul pp).mp (Nat.lt_succ_self (X/p)))
  push_cast at lower upper
  have hl := (le_div_iff₀ pr).mpr lower
  have hh : (X:ℝ)/p < ((X/p:ℕ):ℝ)+1 := (div_lt_iff₀ pr).mpr (by linarith only [upper])
  rw [hband]
  apply recover_reciprocal pp (zero_le_one.trans e1) _ budget
  apply abs_le.mpr
  constructor <;> dsimp only [E] <;> linarith only [(abs_le.mp h).1,(abs_le.mp h).2,hl,hh,xsp]

end GaloisForLFunctions.RestrictedFactorizationCalculus
