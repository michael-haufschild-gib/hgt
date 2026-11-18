import Mathlib.Analysis.Complex.ExponentialBounds
import GaloisForLFunctions.BiScaleUncertainty.InteriorOfBoxSplines
import GaloisForLFunctions.CountingHolography.Sections.ReducedOrdinaryPrimeProducts
import GaloisForLFunctions.CountingHolography.Sections.SmallMultiplicitiesOnSquareConductors
import GaloisForLFunctions.RHTower.XiMassShellPrimeMass
import GaloisForLFunctions.RHTower.Sieve.PrimePairShiftSum

/-!
# A prime window in the denominator at every multiplicity

Near the far end of the longest lag the two positive graphs have no
mutual contacts and the negative graph has no self-contact. One fixed
lower degree has strictly negative contact with the upper graph at every
resolution. Every ordinary prime of the window enters the denominator.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticFunction
open BiScaleUncertainty.ChebyshevGauge

private def threeAtoms (s t x : ℝ) :=
  cubicSpline x+2*cubicSpline (x-s)-cubicSpline (x-t)

private theorem packet_square {n : ℕ} (hn : 0 < n) (u : ℝ) :
    packet (successorSquareTriple n) u =
      threeAtoms (Real.log ((n:ℝ)^2)) (Real.log (((2*n+1:ℕ):ℝ)^2)) (u-(Real.log 3+5)) := by
  let F := fun d : ℝ => cubicSpline (u-(Real.log 3+5)-Real.log d)
  change (∑ i, (successorSquareTriple n i:ℝ)*F ((i:ℝ)+1)) = _
  rw [show (∑ i, (successorSquareTriple n i:ℝ)*F ((i:ℝ)+1)) =
    ∑ i : Fin ((2*n+1)^2+1), F ((i:ℝ)+1)*(successorSquareTriple n i:ℝ) from
      sum_congr rfl fun i _ => mul_comm _ _]
  rw [sum_successorSquareTriple hn F]
  simp only [F,threeAtoms,Real.log_one,sub_zero]

private theorem separated (x d e l : ℝ) (h : 8+e-d < l) :
    cubicSpline (x-d)*cubicSpline (x+l-e)=0 := by
  by_cases hx : cubicSpline (x-d)=0
  · rw [hx,zero_mul]
  have hb : |x-d| ≤ 4 := le_of_not_gt fun h => hx (cubicSpline_eq_zero h)
  have hz : 4 < x+l-e := by linarith only [(abs_le.mp hb).1,h]
  rw [cubicSpline_eq_zero (hz.trans_le (le_abs_self _)),mul_zero]

/-- Beyond the diameter of the two positive graphs only opposite signs
can meet. Keep the lower-to-upper contact as a strictness witness. -/
private theorem long_product (x s t l : ℝ) (hs : 0 ≤ s) (hl : 8+s < l) :
    threeAtoms s t x*threeAtoms s t (x+l) ≤ - (cubicSpline x*cubicSpline (x+l-t)) := by
  let P := fun u : ℝ => cubicSpline u+2*cubicSpline (u-s)
  have self : P x*P (x+l)=0 := by
    have h₁ := separated x 0 0 l (by linarith only [hs,hl])
    have h₂ := separated x 0 s l (by linarith only [hl])
    have h₃ := separated x s 0 l (by linarith only [hs,hl])
    have h₄ := separated x s s l (by linarith only [hs,hl])
    simp only [sub_zero] at h₁ h₂ h₃
    unfold P
    linarith only [h₁,h₂,h₃,h₄]
  have h₅ := separated x t t l (by linarith only [hs,hl])
  have h₆ := mul_nonneg (cubicSpline_nonneg (x-s)) (cubicSpline_nonneg (x+l-t))
  have hp : 0 ≤ P (x+l) := add_nonneg (cubicSpline_nonneg _) (mul_nonneg (by norm_num) (cubicSpline_nonneg _))
  have h₇ := mul_nonneg (cubicSpline_nonneg (x-t)) hp
  change (P x-cubicSpline (x-t))*(P (x+l)-cubicSpline (x+l-t)) ≤ _
  calc _ = P x*P (x+l) + cubicSpline (x-t)*cubicSpline (x+l-t) -
              P x*cubicSpline (x+l-t)-cubicSpline (x-t)*P (x+l) := by ring
    _ ≤ _ := by rw [self,h₅]; dsimp only [P] at *; linarith only [h₆,h₇]

/-- Exponential of the full upper support lag. -/
def successorSquareWindowScale (n : ℕ) := Real.exp 8*(((2*n+1 : ℕ):ℝ)^2)

private theorem log_window {n k : ℕ} (hn : 0 < n)
    (hlo : successorSquareWindowScale n/3 < k) (hhi : (k:ℝ) ≤ successorSquareWindowScale n/2) :
    8+Real.log ((n:ℝ)^2) < Real.log k ∧
    |Real.log 4-5| < 4 ∧
    |Real.log 4-5+Real.log k-Real.log (((2*n+1 : ℕ):ℝ)^2)| < 4 := by
  let p := (n:ℝ)^2
  let b := (((2*n+1:ℕ):ℝ)^2)
  have hp : 0 < p := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  have hb : 0 < b := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.succ_pos _))
  have hsep : 3*p < b := by dsimp only [p,b]; push_cast; nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
  have hlog := Real.log_lt_log (mul_pos (by norm_num) hp) hsep
  rw [Real.log_mul (by norm_num) hp.ne'] at hlog
  change Real.exp 8*b/3 < k at hlo
  change (k:ℝ) ≤ Real.exp 8*b/2 at hhi
  have hk := (div_pos (mul_pos (Real.exp_pos _) hb) (by norm_num)).trans hlo
  have hl := Real.log_lt_log (div_pos (mul_pos (Real.exp_pos _) hb) (by norm_num)) hlo
  have hu := Real.log_le_log hk hhi
  simp only [Real.log_div (mul_pos (Real.exp_pos _) hb).ne' (by norm_num : (3:ℝ) ≠ 0),
    Real.log_div (mul_pos (Real.exp_pos _) hb).ne' (by norm_num : (2:ℝ) ≠ 0),
    Real.log_mul (Real.exp_pos _).ne' hb.ne',Real.log_exp] at hl hu
  have h4 : 1 < Real.log 4 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr
    (Real.exp_one_lt_d9.trans (by norm_num))
  have h4' := Real.log_le_sub_one_of_pos (by norm_num : 0 < (4:ℝ))
  have h34 := Real.log_le_log (by norm_num : 0 < (3:ℝ)) (by norm_num : (3:ℝ) ≤ 4)
  have h2 : Real.log 2 < 1 := (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    (lt_trans (by norm_num) Real.exp_one_gt_d9)
  have h42 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  exact ⟨by linarith only [hlog,hl],abs_lt.mpr ⟨by linarith only [h4],by linarith only [h4']⟩,
    abs_lt.mpr ⟨by linarith only [hl,h34],by linarith only [hu,h42,h2]⟩⟩

/-- Each lag of this interval has a strictly negative unrounded row
at every positive resolution whose mesh includes the degree 12r. -/
theorem successorSquare_negative_window {n k L r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hL : 11 ≤ L) (hlo : successorSquareWindowScale n/3 < k) (hhi : (k:ℝ) ≤ successorSquareWindowScale n/2) :
    contactMultiplicity (packet (successorSquareTriple n)) L r k < 0 := by
  obtain ⟨hsep,hlow,hhigh⟩ := log_window hn hlo hhi
  let s := Real.log ((n:ℝ)^2)
  let t := Real.log (((2*n+1:ℕ):ℝ)^2)
  let l := Real.log k
  let z := fun j : ℕ => Real.log ((j:ℝ)/r)-(Real.log 3+5)
  let f := packet (successorSquareTriple n)
  have hkr : 0 < (k:ℝ) := (show 0 < successorSquareWindowScale n/3 by unfold successorSquareWindowScale; positivity).trans hlo
  have hrr : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hs : 0 ≤ s := Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hn : (1:ℝ) ≤ n))
  have hrow (j : ℕ) (hj : 0 < j) :
      degreeSample f r j*degreeSample f r (j*k)/j ≤ -(cubicSpline (z j)*cubicSpline (z j+l-t))/j := by
    unfold degreeSample f
    rw [packet_square hn,packet_square hn,Nat.cast_mul,mul_div_right_comm (j:ℝ) k r,
      Real.log_mul (div_pos (Nat.cast_pos.mpr hj) hrr).ne' hkr.ne',
      show Real.log ((j:ℝ)/r)+Real.log k-(Real.log 3+5)=z j+l by dsimp only [z,l]; ring]
    exact div_le_div_of_nonneg_right (long_product (z j) s t l hs hsep) (Nat.cast_nonneg _)
  have hz : z (12*r) = Real.log 4-5 := by
    unfold z
    rw [Nat.cast_mul,mul_div_cancel_right₀ _ hrr.ne']
    norm_num only [Nat.cast_ofNat]
    rw [show (12:ℝ)=4*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hJ : 12*r ∈ Ioc r (r+L*r) := mem_Ioc.mpr
    ⟨by omega,by have he := Nat.mul_le_mul_right r hL; omega⟩
  have hJ' : 0 < 12*r := Nat.mul_pos (by decide) hr
  have hstrict := mul_pos (cubicSpline_pos_of_abs_lt_four hlow) (cubicSpline_pos_of_abs_lt_four hhigh)
  unfold contactMultiplicity
  apply mul_neg_of_pos_of_neg (div_pos (by norm_num) (Real.sqrt_pos.mpr hkr))
  refine sum_neg' (fun j hj => (hrow j (hr.trans (mem_Ioc.mp hj).1)).trans
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (cubicSpline_nonneg _) (cubicSpline_nonneg _)))
      (Nat.cast_nonneg _))) ⟨12*r,hJ,?_⟩
  refine (hrow _ hJ').trans_lt ?_
  rw [hz]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hstrict) (Nat.cast_pos.mpr hJ')

theorem successorSquareWindowScale_bounds (n : ℕ) :
    (n:ℝ)^2 ≤ successorSquareWindowScale n ∧ 9 ≤ successorSquareWindowScale n ∧
    successorSquareWindowScale n ≤ windowEnd ((2*n+1)^2+1) := by
  let b := (((2*n+1 : ℕ):ℝ)^2)
  let N := (2*n+1)^2+1
  have hb : 1 ≤ b := one_le_pow₀ (by exact_mod_cast Nat.succ_pos (2*n))
  have hE : 9 ≤ Real.exp 8 := by linarith only [Real.add_one_le_exp (8:ℝ)]
  have hn : (n:ℝ)^2 ≤ b := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
  have h₁ : b ≤ Real.exp 8*b := le_mul_of_one_le_left (zero_le_one.trans hb) (by linarith only [hE])
  refine ⟨hn.trans h₁,hE.trans (le_mul_of_one_le_right (Real.exp_pos _).le hb),?_⟩
  have hN : b ≤ (N:ℝ)+1 := by dsimp only [b,N]; push_cast; linarith
  have he := Real.exp_le_exp.mpr (show (8:ℝ) ≤ Real.log 3+10 by linarith only [Real.log_nonneg (by norm_num : (1:ℝ)≤3)])
  change Real.exp 8*b ≤ (⌈Real.exp (Real.log 3+5+Real.log ((N:ℝ)+1)+5)⌉₊ : ℝ)
  refine (mul_le_mul he hN (zero_le_one.trans hb) (Real.exp_pos _).le).trans (le_trans (le_of_eq ?_) (Nat.le_ceil _))
  rw [show Real.log 3+5+Real.log ((N:ℝ)+1)+5 = (Real.log 3+10)+Real.log ((N:ℝ)+1) by ring,
    Real.exp_add (Real.log 3+10) (Real.log ((N:ℝ)+1)),Real.exp_log (by positivity : 0 < (N:ℝ)+1)]

/-- The ordinary primes in the separated upper contact interval. -/
def successorSquareWindowPrimes (n : ℕ) :=
  (Ioc ⌊successorSquareWindowScale n/3⌋₊ ⌊successorSquareWindowScale n/2⌋₊).filter Nat.Prime

/-- Every proportional interval eventually contains at least half its
length in prime logarithmic mass. -/
theorem proportional_prime_mass {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    ∀ᶠ x : ℝ in atTop, (v-u)/2*x ≤
      ∑ p ∈ (Ioc ⌊u*x⌋₊ ⌊v*x⌋₊).filter Nat.Prime, Real.log p := by
  let ε := (v-u)/(2*(u+v))
  have hv := hu.trans huv
  have hε : 0 < ε := div_pos (sub_pos.mpr huv) (by positivity)
  have he : ε*(u+v)=(v-u)/2 := by unfold ε; field_simp
  have h := _root_.RHTower.chebyshevTheta_eventually_relative hε
  filter_upwards [(tendsto_id.const_mul_atTop hu).eventually h,
    (tendsto_id.const_mul_atTop hv).eventually h,eventually_ge_atTop (0:ℝ)] with x hl ht hx
  change |Chebyshev.theta (u*x)-u*x| ≤ ε*(u*x) at hl
  change |Chebyshev.theta (v*x)-v*x| ≤ ε*(v*x) at ht
  rw [← _root_.RHTower.chebyshevTheta_sub_eq_shellSum
    (Nat.floor_mono (mul_le_mul_of_nonneg_right huv.le hx))]
  linarith only [(abs_le.mp hl).2,(abs_le.mp ht).1,congrArg (fun y : ℝ => y*x) he]

private theorem denominator_window_mass :
    ∀ᶠ n : ℕ in atTop, successorSquareWindowScale n/12 ≤ ∑ k ∈ successorSquareWindowPrimes n, Real.log k := by
  have hn := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hW : Tendsto successorSquareWindowScale atTop atTop :=
    tendsto_atTop_mono (fun n => (successorSquareWindowScale_bounds n).1) hn
  have hm := proportional_prime_mass (u := (1:ℝ)/3) (v := (1:ℝ)/2) (by norm_num) (by norm_num)
  filter_upwards [hW.eventually hm] with n h
  simpa only [successorSquareWindowPrimes,one_div_mul_eq_div,show ((1:ℝ)/2-1/3)/2 = 1/12 by norm_num] using h

/-- The product of all ordinary primes of the window divides the
denominator in lowest terms, even at multiplicity one. -/
theorem successorSquare_window_product_dvd {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∏ k ∈ successorSquareWindowPrimes n, k) ∣ (ordinaryPrimeGenerator (m • successorSquareTriple n)).den := by
  let d := successorSquareTriple n
  let a := m • d
  let W := successorSquareWindowScale n
  let L := 3*windowEnd ((2*n+1)^2+1)
  let S := (Icc 2 L).filter Nat.Prime
  let x := contactMultiplicity (packet a) L (resolution a)
  have hW := successorSquareWindowScale_bounds n
  have hlarge : 9 ≤ (windowEnd ((2*n+1)^2+1) : ℝ) := hW.2.1.trans hW.2.2
  have hL : 11 ≤ L := by
    have hnat : 9 ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast hlarge
    dsimp only [L]
    omega
  have hr : 0 < resolution a := hm.trans_le (successorSquare_resolution_ge n m)
  have hmem {k : ℕ} (hk : k ∈ successorSquareWindowPrimes n) : k.Prime ∧ W/3 < k ∧ (k:ℝ) ≤ W/2 := by
    obtain ⟨hi,hp⟩ := mem_filter.mp hk
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hi
    exact ⟨hp,(Nat.floor_lt (by linarith only [hW.2.1] : 0 ≤ W/3)).mp hl,
      (Nat.cast_le.mpr hu).trans (Nat.floor_le (by linarith only [hW.2.1] : 0 ≤ W/2))⟩
  have hs : successorSquareWindowPrimes n ⊆ S := by
    intro k hk
    obtain ⟨hp,_,hu⟩ := hmem hk
    have he : (k:ℝ) ≤ windowEnd ((2*n+1)^2+1) := by linarith only [hu,hW.2.1,hW.2.2]
    have hnat : k ≤ windowEnd ((2*n+1)^2+1) := by exact_mod_cast he
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,by dsimp only [L]; omega⟩,hp⟩
  apply (_root_.RHTower.Sieve.prod_dvd_iff_forall_dvd (fun k hk => (hmem hk).1) _).mpr
  intro k hk
  obtain ⟨hp,hl,hu⟩ := hmem hk
  letI : Fact k.Prime := ⟨hp⟩
  have hneg : x k < 0 := by
    unfold x a
    rw [packet_smul,contactMultiplicity_scale]
    exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Nat.cast_pos.mpr hm))
      (successorSquare_negative_window hn hr hL hl hu)
  by_contra hnot
  have he := (HTGeometry.Arithmetic.nonneg_val_iff_not_dvd_den k (ordinaryPrimeGenerator a)).mpr hnot
  rw [← _root_.RHTower.deningerRatExp_apply_of_prime hp,ordinaryPrimeGenerator_exponent,if_pos (hs hk)] at he
  have hnon : (0:ℝ) ≤ (⌊x k⌋:ℤ) := by exact_mod_cast he
  exact hneg.not_ge (hnon.trans (Int.floor_le _))

/-- At every positive multiplicity the log contribution of ordinary primes
in the reduced denominator grows at least quadratically in the conductor parameter. -/
theorem successorSquare_denominator_lower : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m →
    (n:ℝ)^2/12 ≤ Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n)).den := by
  filter_upwards [denominator_window_mass,eventually_ge_atTop 1] with n hmass hn
  intro m hm
  let q := ordinaryPrimeGenerator (m • successorSquareTriple n)
  have hk (k : ℕ) (hk : k ∈ successorSquareWindowPrimes n) : 0 < k := (mem_filter.mp hk).2.pos
  have hprod : 0 < ∏ k ∈ successorSquareWindowPrimes n, k := prod_pos hk
  have hq : (∏ k ∈ successorSquareWindowPrimes n, k) ≤ q.den :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero q.den_nz) (successorSquare_window_product_dvd hn hm)
  have hh := Real.log_le_log (Nat.cast_pos.mpr hprod : (0:ℝ) < _) (Nat.cast_le.mpr hq)
  rw [Nat.cast_prod,Real.log_prod (fun k h => (Nat.cast_pos.mpr (hk k h) : (0:ℝ) < _).ne')] at hh
  exact (div_le_div_of_nonneg_right (successorSquareWindowScale_bounds n).1 (by norm_num : (0:ℝ) ≤ 12)).trans
    (hmass.trans hh)

/-- On the square-root multiplicity range the denominator forces exponential
decay of the actual rational generator, uniformly in the multiplicity. -/
theorem small_multiplicity_exponential_decay : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m → C*(m:ℝ)^2 ≤ n →
      Real.log (ordinaryPrimeGenerator (m • successorSquareTriple n) : ℝ) ≤ -(n:ℝ)^2/24 := by
  obtain ⟨C,hC,B,hB,h⟩ := small_multiplicity_ordinary_modulus
  refine ⟨max C 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  filter_upwards [successorSquare_denominator_lower,eventually_ge_atTop ⌈24*Real.log B⌉₊,
    eventually_ge_atTop 1] with n hden hn hn1
  intro m hm hmn
  have hmC := (mul_le_mul_of_nonneg_right (le_max_left C 1) (sq_nonneg (m:ℝ))).trans hmn
  have hmn' := (mul_le_mul_of_nonneg_right (le_max_right C 1) (sq_nonneg (m:ℝ))).trans hmn
  rw [one_mul] at hmn'
  have hfit := h hn1 hmC
  have hpos : 0 < ordinaryPrimeModulus (m • successorSquareTriple n) :=
    prod_pos fun k _ => pow_pos (contactBase_pos k) _
  have hup := Real.log_le_log (Nat.cast_pos.mpr hpos : (0:ℝ) < _) (Nat.cast_le.mpr hfit)
  rw [Nat.cast_pow,Real.log_pow,Nat.cast_pow] at hup
  have hl : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast hB : (1:ℝ) ≤ B)
  have hh : 24*Real.log B ≤ (n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hd := hden m hm
  rw [log_ordinaryPrimeGenerator_den] at hd
  linarith only [hd,hup,mul_le_mul_of_nonneg_right hmn' hl,
    mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α := ℝ) n)]

#print axioms successorSquare_negative_window
#print axioms successorSquare_window_product_dvd
#print axioms successorSquare_denominator_lower
#print axioms small_multiplicity_exponential_decay

end GaloisForLFunctions.CountingHolography.Sections
