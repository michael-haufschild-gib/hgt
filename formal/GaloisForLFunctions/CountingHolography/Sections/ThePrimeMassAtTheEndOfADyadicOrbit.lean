import GaloisForLFunctions.CountingHolography.Sections.FinitePlaceCostOfTheStirlingRemainder
import GaloisForLFunctions.CountingHolography.Sections.TheLogarithmicMomentOfTheSquarePrimeProfile

/-! # The escaping prime mass on a dyadic orbit of square conductors

The logarithmic valuations are a difference of two positive prime profiles
at successive squares, up to a quadratically bounded absolute error.
In the dyadic sum with weights eight to the minus depth this error is
absolutely summable in both indices. The end profile has a nonzero
limiting mass although it vanishes eventually at every fixed prime.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology MeasureTheory ArithmeticCastelnuovoSeveri ArithmeticFunction
open ArithmeticWeightTheory _root_.RHTower _root_.RHTower.WeilDeletion BiScaleUncertainty.ChebyshevGauge

private def weight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
private def S (n : ℕ) := ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1))
private def q (n : ℕ) := ordinaryPrimeGenerator (n • successorSquareTriple n)
private def price (n k : ℕ) := (deningerRatExp (q n) k:ℝ)*weight k

/-- Positive moving endpoint, with the logarithmic prime weight included. -/
def squarePrimeEndpoint (n k : ℕ) : ℝ :=
  (4*(n:ℝ)^2/Real.sqrt k)*splineAutoCorr (Real.log k-Real.log ((n:ℝ)^2))*weight k

private def err (n k : ℕ) := price n k-(squarePrimeEndpoint n k-squarePrimeEndpoint (2*n) k/8)

private theorem endpoint_zero {n k : ℕ} (hn : 0 < n) (hk : k ∉ S n) :
    price n k=0 ∧ squarePrimeEndpoint n k=0 ∧ squarePrimeEndpoint (2*n) k=0 := by
  by_cases hp : k.Prime
  · have hcut : 3*windowEnd ((2*n+1)^2+1) < k :=
      lt_of_not_ge fun h => hk (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,h⟩,hp⟩)
    have hkL : (windowEnd ((2*n+1)^2+1):ℝ) < k := by
      exact_mod_cast (by omega : windowEnd ((2*n+1)^2+1) < k)
    have hb := (successorSquareWindowScale_bounds n).2.2.trans_lt hkL
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hp.pos
    have hhigh : 0 < ((2*n:ℕ):ℝ) := by positivity
    have hsq : (((2*n:ℕ):ℝ))^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hhigh.le (by exact_mod_cast Nat.le_succ (2*n)) 2
    have hlow : (n:ℝ)^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hn'.le (by exact_mod_cast (by omega : n ≤ 2*n+1)) 2
    have hz {x : ℝ} (hx : 0 < x) (h : x^2 ≤ (((2*n+1:ℕ):ℝ))^2) : splineAutoCorr (Real.log k-Real.log (x^2))=0 := by
      apply splineAutoCorr_zero_outside
      apply lt_of_lt_of_le _ (le_abs_self _)
      rw [← Real.log_div hk'.ne' (sq_pos_of_pos hx).ne',Real.lt_log_iff_exp_lt (div_pos hk' (sq_pos_of_pos hx)),lt_div_iff₀ (sq_pos_of_pos hx)]
      have he := (mul_le_mul_of_nonneg_left h (Real.exp_pos 8).le)
      exact he.trans_lt hb
    have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
    change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
    simp only [price,he,if_neg hk,Int.cast_zero,zero_mul,squarePrimeEndpoint,hz hn' hlow,hz hhigh hsq,mul_zero,and_self]
  · simp [price,squarePrimeEndpoint,weight,hp]

private theorem error_row {n k : ℕ} (hn : 0 < n) :
    err n k=((deningerRatExp (q n) k:ℝ)-diagonalPrimeProfile n k)*weight k := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have he : Real.log (((2*n:ℕ):ℝ)^2)=Real.log ((n:ℝ)^2)+Real.log 4 := by
    push_cast
    rw [mul_pow,Real.log_mul (by norm_num) (sq_pos_of_pos hn').ne']
    norm_num
    ring
  simp only [err,price,squarePrimeEndpoint,diagonalPrimeProfile,squareLogProfile,he,
    show Real.log k-(Real.log ((n:ℝ)^2)+Real.log 4)=Real.log k-Real.log ((n:ℝ)^2)-Real.log 4 by ring,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem error_summable {n : ℕ} (hn : 0 < n) : Summable (fun k => |err n k|) :=
  summable_of_ne_finset_zero (s := S n) fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃]

private theorem error_budget : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n → (∑' k, |err n k|) ≤ C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hE⟩ := diagonal_prime_exponent_profile_error
  refine ⟨C,hC,fun {n} hn => ?_⟩
  rw [tsum_eq_sum (s := S n) (fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃])]
  apply le_trans (le_of_eq (sum_congr rfl fun k hk => ?_)) (hE hn)
  have hp := (mem_filter.mp hk).2
  rw [error_row hn,abs_mul,weight,if_pos hp,abs_of_nonneg (Real.log_natCast_nonneg _),vonMangoldt_apply_prime hp]
  rfl

private theorem price_sum (n : ℕ) (hn : 0 < n) : (∑' k, price n k)=Real.log (q n:ℝ) := by
  rw [tsum_eq_sum (s := S n) (fun _ hk => (endpoint_zero hn hk).1),q,log_ordinaryPrimeGenerator]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
  change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
  rw [price,he,if_pos hk,weight,if_pos hp,vonMangoldt_apply_prime hp]

private theorem endpoint_summable {n : ℕ} (hn : 0 < n) : Summable (squarePrimeEndpoint n) :=
  summable_of_ne_finset_zero (s := S n) fun _ hk => (endpoint_zero hn hk).2.1

/-- The positive endpoint has cubic mass with an explicit leading coefficient. -/
theorem tendsto_squarePrimeEndpoint_mass :
    Tendsto (fun n : ℕ => (∑' k, squarePrimeEndpoint n k)/(n:ℝ)^3) atTop (𝓝 (4*squareAutocorrelationMass)) := by
  have hK : HasCompactSupport splineAutoCorr := by
    rw [show splineAutoCorr=upow 1 7 from funext splineAutoCorr_eq_eight_boxes]
    exact hasCompactSupport_upow 1 7
  have h := ((tendsto_ordinary_prime_log_test continuous_splineAutoCorr hK).comp
    ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)).const_mul 4
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hsub : (∑' p : Nat.Primes, squarePrimeEndpoint n p.val)=∑' k, squarePrimeEndpoint n k :=
    tsum_subtype_eq_of_support_subset fun k hk hp => hk (by simp [squarePrimeEndpoint,weight,hp])
  rw [← hsub]
  let L := fun p : Nat.Primes => Real.log (p:ℕ)*(splineAutoCorr (Real.log ((p:ℕ)/(n:ℝ)^2))/Real.sqrt ((p:ℕ)/(n:ℝ)^2))
  have he (p : Nat.Primes) : squarePrimeEndpoint n p.val = (4*(n:ℝ))*L p := by
    have hp : 0 < ((p:ℕ):ℝ) := Nat.cast_pos.mpr p.property.pos
    simp only [squarePrimeEndpoint,weight,if_pos p.property,L,Real.log_div hp.ne' (sq_pos_of_pos hn').ne',
      Real.sqrt_div hp.le,Real.sqrt_sq hn'.le]
    field_simp [hn'.ne',(Real.sqrt_pos.mpr hp).ne'] <;> ring
  simp_rw [he]
  rw [tsum_mul_left]
  change 4*((∑' p, L p)/(n:ℝ)^2)=_
  field_simp

private def orbit (n j : ℕ) := 2^j*n
private def factor (j : ℕ) : ℝ := (1/8)^j
private def row (n j k : ℕ) := factor j*price (orbit n j) k
private def tail (n j k : ℕ) := factor j*squarePrimeEndpoint (orbit n j) k
private def remainder (n : ℕ) (i : ℕ × ℕ) := factor i.1*err (orbit n i.1) i.2

private theorem orbit_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < orbit n j :=
  Nat.mul_pos (pow_pos (by decide : 0 < 2) j) hn

private theorem orbit_infty {n : ℕ} (hn : 0 < n) : Tendsto (orbit n) atTop atTop := by
  refine tendsto_atTop_mono (f := fun j : ℕ => 2^j) (fun j => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ)))
  exact Nat.le_mul_of_pos_right _ hn

private theorem row_split (n j k : ℕ) :
    row n j k=tail n j k-tail n (j+1) k+remainder n (j,k) := by
  simp only [row,tail,remainder,factor,orbit,err,pow_succ]
  rw [show (2:ℕ)^j*2*n=2*(2^j*n) by ring]
  ring

private def geometricError (n : ℕ) (r : ℝ) (i : ℕ × ℕ) := r^i.1*err (orbit n i.1) i.2

private theorem summable_geometricError {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) (hr₄ : r*4 < 1) :
    Summable (geometricError n r) := by
  obtain ⟨C,hC,hE⟩ := error_budget
  have hf (j : ℕ) : 0 ≤ r^j := pow_nonneg hr _
  have habs (j k : ℕ) : |geometricError n r (j,k)|=r^j*|err (orbit n j) k| := by
    rw [geometricError,abs_mul,abs_of_nonneg (hf j)]
  apply Summable.of_norm
  simp only [Real.norm_eq_abs]
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro j
    simp_rw [habs]
    exact (error_summable (orbit_pos hn j)).mul_left _
  · let D := C*(n:ℝ)^2
    have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (by norm_num : (0:ℝ) ≤ 4)) hr₄).mul_right D
    apply Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => abs_nonneg _) _ hgeo
    intro j
    simp_rw [habs]
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left (hE (orbit_pos hn j)) (hf j)).trans_eq ?_
    dsimp only [orbit,D]
    push_cast
    rw [mul_pow,← pow_mul,Nat.mul_comm j 2,pow_mul]
    calc _ = (r^j*((2:ℝ)^2)^j)*(C*(n:ℝ)^2) := by ring
      _ = _ := by rw [← mul_pow]; norm_num

private theorem summable_remainder {n : ℕ} (hn : 0 < n) : Summable (remainder n) :=
  summable_geometricError hn (by norm_num : (0:ℝ) ≤ 1/8) (by norm_num)

private theorem tail_eventually_zero {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, tail n j k=0 := by
  have ht := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp (orbit_infty hn)))
  filter_upwards [ht.eventually_gt_atTop (Real.log k+8)] with j hj
  change Real.log k+8 < Real.log ((orbit n j:ℝ)^2) at hj
  have hz := splineAutoCorr_zero_outside (x := Real.log k-Real.log ((orbit n j:ℝ)^2))
    (by linarith only [hj,neg_abs_le (Real.log k-Real.log ((orbit n j:ℝ)^2))])
  simp [tail,squarePrimeEndpoint,hz]

private theorem orbit_column_sum {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (∑' j, row n j k)=squarePrimeEndpoint n k+∑' j, remainder n (j,k) := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (tail_eventually_zero hn k)
  have ht : Summable (fun j => tail n j k) := summable_of_ne_finset_zero (s := range J)
    fun j hj => hJ j (le_of_not_gt (fun hh => hj (mem_range.mpr hh)))
  have ht' : Summable (fun j => tail n (j+1) k) := summable_of_ne_finset_zero (s := range J)
    fun j hj => hJ _ (by have := not_lt.mp (mt mem_range.mpr hj); omega)
  have hR := (summable_remainder hn).prod_symm.prod_factor k
  simp_rw [row_split]
  rw [(ht.sub ht').tsum_add hR,ht.tsum_sub ht']
  have hs := ht.tsum_eq_zero_add
  change (∑' j, tail n j k)=tail n 0 k+∑' j, tail n (j+1) k at hs
  rw [hs]
  simp [tail,factor,orbit]

private theorem tail_mass_limit {n : ℕ} (hn : 0 < n) :
    Tendsto (fun j => ∑' k, tail n j k) atTop (𝓝 (4*(n:ℝ)^3*squareAutocorrelationMass)) := by
  have h := (tendsto_squarePrimeEndpoint_mass.comp (orbit_infty hn)).const_mul ((n:ℝ)^3)
  rw [show (n:ℝ)^3*(4*squareAutocorrelationMass)=4*(n:ℝ)^3*squareAutocorrelationMass by ring] at h
  apply h.congr fun j => ?_
  simp only [tail,tsum_mul_left]
  change (n:ℝ)^3*((∑' k, squarePrimeEndpoint (orbit n j) k)/(orbit n j:ℝ)^3)=_
  have he : (orbit n j:ℝ)^3=(8:ℝ)^j*(n:ℝ)^3 := by
    simp only [orbit,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,← pow_mul]
    rw [Nat.mul_comm j 3,pow_mul]
    norm_num
  have hn' : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [he]
  dsimp only [factor]
  rw [one_div,inv_pow]
  field_simp

/-- Summing first along each fixed prime and then over the primes exceeds
the limit in conductor order by exactly four times the positive cubic mass. -/
theorem dyadic_square_prime_mass_escape {n : ℕ} (hn : 0 < n) :
    Tendsto (fun K : ℕ =>
      (∑' p : ℕ, ∑' j : ℕ, (1/8:ℝ)^j*
        (deningerRatExp (ordinaryPrimeGenerator ((2^j*n) • successorSquareTriple (2^j*n))) p:ℝ)*
        (if p.Prime then Real.log p else 0)) -
      ∑ j ∈ range K, (1/8:ℝ)^j*Real.log
        (ordinaryPrimeGenerator ((2^j*n) • successorSquareTriple (2^j*n)):ℝ))
      atTop (𝓝 (4*(n:ℝ)^3*squareAutocorrelationMass)) := by
  have hR := summable_remainder hn
  have hcols : (∑' p, ∑' j, row n j p)=(∑' p, squarePrimeEndpoint n p)+∑' j, ∑' p, remainder n (j,p) := by
    simp_rw [orbit_column_sum hn]
    rw [(endpoint_summable hn).tsum_add hR.prod_symm.prod,hR.tsum_comm]
  have hsum (j : ℕ) : factor j*Real.log (q (orbit n j):ℝ)=
      (∑' p, tail n j p)-(∑' p, tail n (j+1) p)+∑' p, remainder n (j,p) := by
    rw [← price_sum _ (orbit_pos hn _),← tsum_mul_left]
    change (∑' p, row n j p)=_
    have ht (i : ℕ) : Summable (tail n i) := (endpoint_summable (orbit_pos hn i)).mul_left _
    simp_rw [row_split]
    rw [((ht j).sub (ht (j+1))).tsum_add (hR.prod_factor j),(ht j).tsum_sub (ht (j+1))]
  have hRlim := hR.prod.hasSum.tendsto_sum_nat
  have h := (tail_mass_limit hn).add ((tendsto_const_nhds
    (x := ∑' j, ∑' p, remainder n (j,p))).sub hRlim)
  rw [sub_self,add_zero] at h
  apply h.congr fun K => ?_
  simp only [mul_assoc]
  change _ = (∑' p, ∑' j, row n j p)-∑ j ∈ range K, factor j*Real.log (q (orbit n j):ℝ)
  simp_rw [hsum]
  rw [hcols,sum_add_distrib,sum_range_sub']
  simp only [tail,factor,orbit,pow_zero,one_mul]
  ring

/-- The two-index family of actual logarithmic valuations cannot be
summed unconditionally. Its failure at weight one eighth occurs on every
positive dyadic orbit, including orbits with bounded signed prices. -/
theorem not_summable_dyadic_square_log_valuations {n : ℕ} (hn : 0 < n) :
    ¬ Summable (fun i : ℕ × ℕ => (1/8:ℝ)^i.1 *
      ((deningerRatExp (ordinaryPrimeGenerator ((2^i.1*n) • successorSquareTriple (2^i.1*n))) i.2:ℝ)*
        (if i.2.Prime then Real.log i.2 else 0))) := by
  intro h
  change Summable (Function.uncurry (row n)) at h
  have hprice (j : ℕ) : (∑' p, row n j p)=factor j*Real.log (q (orbit n j):ℝ) := by
    simp only [row,tsum_mul_left,price_sum _ (orbit_pos hn j)]
  have hzero := ((tendsto_const_nhds (x := ∑' j, ∑' p, row n j p)).sub h.prod.hasSum.tendsto_sum_nat)
  rw [sub_self] at hzero
  have he := dyadic_square_prime_mass_escape hn
  simp only [mul_assoc] at he
  change Tendsto (fun K => (∑' p, ∑' j, row n j p)-
    ∑ j ∈ range K, factor j*Real.log (q (orbit n j):ℝ)) atTop _ at he
  simp_rw [← hprice] at he
  rw [h.tsum_comm] at he
  have hp : 0 < 4*(n:ℝ)^3*squareAutocorrelationMass :=
    mul_pos (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 3)) squareAutocorrelationMass_pos
  exact hp.ne' (tendsto_nhds_unique he hzero)

private theorem abs_row_sum {n : ℕ} (hn : 0 < n) :
    (∑' k, |price n k|)=Real.log (q n).num.natAbs+Real.log (q n).den := by
  rw [tsum_eq_sum (s := S n) (fun k hk => by rw [(endpoint_zero hn hk).1,abs_zero]),
    ← ordinary_absolute_prime_mass (n • successorSquareTriple n)]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  rw [price,abs_mul,weight,if_pos hp,abs_of_nonneg (Real.log_natCast_nonneg k),vonMangoldt_apply_prime hp]

/-- One eighth is exactly the radius of absolute convergence of the
prime-by-prime dyadic series, on every positive starting conductor. -/
theorem summable_dyadic_square_log_valuations_iff {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    Summable (fun i : ℕ × ℕ => r^i.1*((deningerRatExp (q (orbit n i.1)) i.2:ℝ)*weight i.2)) ↔ r < 1/8 := by
  change Summable (fun i : ℕ × ℕ => r^i.1*price (orbit n i.1) i.2) ↔ _
  constructor
  · intro h
    by_contra he
    apply not_summable_dyadic_square_log_valuations hn
    apply Summable.of_abs
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun i => ?_) h.abs
    change |(1/8:ℝ)^i.1*price (orbit n i.1) i.2| ≤ |r^i.1*price (orbit n i.1) i.2|
    rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) _),abs_of_nonneg (pow_nonneg hr _)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (le_of_not_gt he) _) (abs_nonneg _)
  · intro hsmall
    obtain ⟨B,hB,hsize⟩ := successorSquare_products_upper
    have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (by norm_num : (0:ℝ) ≤ 8))
      (show r*8 < 1 by linarith only [hsmall])).mul_right (3*B*(n:ℝ)^3)
    apply Summable.of_abs
    simp only [abs_mul,abs_of_nonneg (pow_nonneg hr _)]
    apply (summable_prod_of_nonneg (fun i => mul_nonneg (pow_nonneg hr i.1) (abs_nonneg _))).mpr
    constructor
    · intro j
      exact (summable_of_ne_finset_zero (s := S (orbit n j)) (fun k hk => by
        rw [(endpoint_zero (orbit_pos hn j) hk).1,abs_zero])).mul_left _
    · refine Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => mul_nonneg (pow_nonneg hr j) (abs_nonneg _))
        (fun j => ?_) hgeo
      let m := orbit n j
      have hm : 0 < m := orbit_pos hn j
      have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
      obtain ⟨hu,hv⟩ := hsize (m := m) hm
      have hsub := mul_le_mul_of_nonneg_right hm' (sq_nonneg (m:ℝ))
      have htot : Real.log (q m).num.natAbs+Real.log (q m).den ≤ 3*B*(m:ℝ)^3 := by
        change Real.log (q m).num.natAbs ≤ B*m*(m:ℝ)^2 at hu
        change Real.log (q m).den ≤ B*((m:ℝ)*(m:ℝ)^2+m^2) at hv
        linarith only [hu,hv,mul_le_mul_of_nonneg_left hsub hB]
      rw [tsum_mul_left,abs_row_sum (orbit_pos hn j)]
      refine (mul_le_mul_of_nonneg_left htot (pow_nonneg hr j)).trans_eq ?_
      dsimp only [m,orbit]
      push_cast
      rw [mul_pow (2:ℝ)^j,← pow_mul,Nat.mul_comm j 3,pow_mul]
      change r^j*(3*B*(8^j*(n:ℝ)^3))=_
      rw [mul_pow r 8 j]; ring

private theorem endpoint_nonneg (n k : ℕ) : 0 ≤ squarePrimeEndpoint n k := by
  have hw : 0 ≤ weight k := by
    unfold weight; split_ifs <;> first | exact Real.log_natCast_nonneg _ | rfl
  exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _))
    (splineAutoCorr_nonneg _)) hw

/-- Product of the first K prices on a doubling orbit with integer powers
eight to the remaining depth. -/
def dyadicSquareProduct (n : ℕ) : ℕ → ℚ
  | 0 => 1
  | K+1 => dyadicSquareProduct n K ^ 8 * q (2^K*n)

private theorem orbit_price_pos (n : ℕ) : 0 < q n := by
  unfold q ordinaryPrimeGenerator
  exact prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k) : (0:ℚ) < _) _

private theorem dyadic_product_pos (n K : ℕ) : 0 < dyadicSquareProduct n K := by
  induction K with
  | zero => exact zero_lt_one
  | succ K ih => exact mul_pos (pow_pos ih 8) (orbit_price_pos _)

private theorem dyadic_product_row (n K k : ℕ) :
    8*factor K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k =
      ∑ j ∈ range K, row n j k := by
  induction K with
  | zero => simp [dyadicSquareProduct]
  | succ K ih =>
    rw [sum_range_succ,← ih,dyadicSquareProduct,deningerRatExp_mul
      (pow_ne_zero 8 (dyadic_product_pos _ _).ne') (orbit_price_pos _).ne',deningerRatExp_pow (dyadic_product_pos _ _).ne']
    simp only [Finsupp.add_apply,Finsupp.smul_apply,nsmul_eq_mul,Int.cast_add,Int.cast_mul,Int.cast_ofNat]
    dsimp only [factor,row,price,orbit]
    rw [pow_succ]; ring

private theorem finite_dyadic_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ), (∑ k ∈ P, |∑ j ∈ range K, remainder n (j,k)|) ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hE⟩ := error_budget
  refine ⟨C,hC,fun {n} hn P K => ?_⟩
  let D := C*(n:ℝ)^2
  have hd : 0 ≤ D := mul_nonneg hC (sq_nonneg _)
  have hgeo := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)).mul_right D
  calc _ ≤ ∑ k ∈ P, ∑ j ∈ range K, |remainder n (j,k)| :=
            sum_le_sum fun k _ => abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ range K, ∑ k ∈ P, |remainder n (j,k)| := sum_comm
    _ ≤ ∑ j ∈ range K, (1/2:ℝ)^j*D := sum_le_sum fun j _ => by
      have hfac : 0 ≤ factor j := pow_nonneg (by norm_num) _
      simp only [remainder,abs_mul,abs_of_nonneg hfac,← mul_sum]
      have hsum := (error_summable (orbit_pos hn j)).sum_le_tsum P (fun _ _ => abs_nonneg _)
      refine (mul_le_mul_of_nonneg_left (hsum.trans (hE (orbit_pos hn j))) hfac).trans_eq ?_
      dsimp only [orbit,factor,D]
      push_cast
      rw [mul_pow,← pow_mul,Nat.mul_comm j 2,pow_mul]
      calc _ = ((1/8:ℝ)^j*(2^2:ℝ)^j)*(C*(n:ℝ)^2) := by ring
        _ = _ := by rw [← mul_pow]; norm_num
    _ ≤ _ := (hgeo.summable.sum_le_tsum _ (fun j _ => mul_nonneg (pow_nonneg (by norm_num) _) hd)).trans_eq
      (by rw [hgeo.tsum_eq]; dsimp only [D]; ring)

/-- The two endpoint profiles recover the normalized integer product up
to a uniform quadratic error in total absolute logarithmic weight. -/
theorem dyadic_square_product_endpoints : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ),
      ∑ k ∈ P, |8*(1/8:ℝ)^K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k -
        (squarePrimeEndpoint n k - (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k)| ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := finite_dyadic_error
  refine ⟨C,hC,fun {n} hn P K => ?_⟩
  refine le_trans (le_of_eq (sum_congr rfl fun k _ => ?_)) (h hn P K)
  rw [← show factor K=(1/8:ℝ)^K from rfl,dyadic_product_row]
  simp_rw [row_split]
  rw [sum_add_distrib,sum_range_sub']
  simp [tail,factor,orbit]

/-- Once the two support intervals are disjoint, the positive and negative
parts of the product recover the two endpoint masses separately. -/
theorem dyadic_square_product_separated_endpoints : ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
    ∀ (P : Finset ℕ) (K : ℕ), 16 < 2*K*Real.log 2 →
    let v := fun k => 8*(1/8:ℝ)^K*(deningerRatExp (dyadicSquareProduct n K) k:ℝ)*weight k
    (∑ k ∈ P, |max (v k) 0 - squarePrimeEndpoint n k|) ≤ 2*C*(n:ℝ)^2 ∧
    (∑ k ∈ P, |max (-v k) 0 - (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k|) ≤ 2*C*(n:ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := dyadic_square_product_endpoints
  refine ⟨C,hC,fun {n} hn P K hK => ?_⟩
  let x := squarePrimeEndpoint n
  let y := fun k => (1/8:ℝ)^K*squarePrimeEndpoint (2^K*n) k
  have hzero (k : ℕ) : x k = 0 ∨ y k = 0 := by
    let t := Real.log k-Real.log ((n:ℝ)^2)
    by_cases ht : 8 < |t|
    · left; change 4*(n:ℝ)^2/Real.sqrt k*splineAutoCorr t*weight k=0
      rw [splineAutoCorr_zero_outside ht,mul_zero,zero_mul]
    · right
      have hl : Real.log (((2^K*n:ℕ):ℝ)^2) = 2*K*Real.log 2 + Real.log ((n:ℝ)^2) := by
        rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_pow,Real.log_mul
          (by positivity) (sq_pos_of_pos (Nat.cast_pos.mpr hn)).ne',Real.log_pow,Real.log_pow]
        push_cast; ring
      have hz : 8 < |Real.log k-Real.log (((2^K*n:ℕ):ℝ)^2)| := by
        rw [hl]
        have ht' := (le_abs_self t).trans (le_of_not_gt ht)
        dsimp only [t] at ht'
        linarith only [ht',hK,neg_abs_le (Real.log k-(2*K*Real.log 2+Real.log ((n:ℝ)^2)))]
      simp [y,squarePrimeEndpoint,splineAutoCorr_zero_outside hz]
  have hj (k : ℕ) : max (x k-y k) 0 = x k ∧ max (-(x k-y k)) 0 = y k := by
    have hx : 0 ≤ x k := endpoint_nonneg _ _
    have hy : 0 ≤ y k := mul_nonneg (pow_nonneg (by norm_num) _) (endpoint_nonneg _ _)
    rcases hzero k with hz | hz <;> simp [hz,max_eq_left hx,max_eq_left hy,
      max_eq_right (neg_nonpos.mpr hx),max_eq_right (neg_nonpos.mpr hy)]
  constructor
  · refine (sum_le_sum fun k _ => ?_).trans (h hn P K)
    rw [← (hj k).1]
    exact abs_max_sub_max_le_abs _ _ _
  · refine (sum_le_sum fun k _ => ?_).trans (h hn P K)
    rw [← (hj k).2]
    exact (abs_max_sub_max_le_abs _ _ _).trans_eq (by rw [neg_sub_neg,abs_sub_comm])

private theorem endpoint_column_finite {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, squarePrimeEndpoint (orbit n j) k = 0 := by
  filter_upwards [tail_eventually_zero hn k] with j hj
  exact (mul_eq_zero.mp hj).resolve_left (pow_ne_zero j (by norm_num : (1/8:ℝ) ≠ 0))

/-- Above one eighth, the actual sum in prime order tends to positive
infinity as long as the accumulated quadratic row error is summable. -/
theorem dyadic_square_supercritical_prime_order {n : ℕ} (hn : 0 < n) {r : ℝ}
    (hr : 1/8 < r) (hr₄ : r*4 < 1) :
    Tendsto (fun K : ℕ => ∑ k ∈ range K, ∑' j : ℕ, r^j *
      ((deningerRatExp (q (2^j*n)) k : ℝ)*weight k)) atTop atTop := by
  have hr₀ : 0 ≤ r := le_trans (by norm_num) hr.le
  let B := fun j k => squarePrimeEndpoint (orbit n j) k
  let Q := fun i : ℕ × ℕ => r^i.1 * B (i.1+1) i.2
  let E := geometricError n r
  have hE : Summable E := summable_geometricError hn hr₀ hr₄
  have hQ₀ (i : ℕ × ℕ) : 0 ≤ Q i := mul_nonneg (pow_nonneg hr₀ _) (endpoint_nonneg _ _)
  have hBsum (k d : ℕ) : Summable (fun j : ℕ => r^j * B (j+d) k) := by
    obtain ⟨J,hJ⟩ := eventually_atTop.mp (endpoint_column_finite hn k)
    exact summable_of_ne_finset_zero (s := range J) fun j hj => by
      have h : J ≤ j := not_lt.mp (mt mem_range.mpr hj)
      rw [show B (j+d) k=0 from hJ _ (by omega),mul_zero]
  have hcolumn (k : ℕ) : (∑' j : ℕ, r^j * price (orbit n j) k) =
      (r-1/8)*(∑' j : ℕ, Q (j,k)) + (squarePrimeEndpoint n k + ∑' j : ℕ, E (j,k)) := by
    let A := fun j : ℕ => r^j * B j k
    have hA : Summable A := by simpa only [Nat.add_zero] using hBsum k 0
    have hQ : Summable (fun j => Q (j,k)) := hBsum k 1
    have he (j : ℕ) : r^j*price (orbit n j) k = A j-(1/8)*Q (j,k)+E (j,k) := by
      dsimp only [A,Q,E,B,geometricError,err,orbit]
      rw [show 2^(j+1)*n=2*(2^j*n) by ring]
      ring
    simp_rw [he]
    rw [(hA.sub (hQ.mul_left _)).tsum_add (hE.prod_symm.prod_factor k),hA.tsum_sub (hQ.mul_left _),
      tsum_mul_left,hA.tsum_eq_zero_add]
    have htail : ∀ j, A (j+1)=r*Q (j,k) := fun j => by dsimp only [A,Q]; rw [pow_succ]; ring
    simp_rw [htail]
    rw [tsum_mul_left]
    simp only [A,B,orbit,pow_zero,one_mul]
    ring
  have hbad : ¬Summable (fun k : ℕ => ∑' j : ℕ, Q (j,k)) := by
    intro ha
    have hdouble : Summable (fun i : ℕ × ℕ => Q (i.2,i.1)) :=
      (summable_prod_of_nonneg (fun i => hQ₀ (i.2,i.1))).mpr ⟨fun k => hBsum k 1,ha⟩
    have hrows : Tendsto (fun j : ℕ => ∑' k, Q (j,k)) atTop (𝓝 0) := hdouble.prod_symm.prod.tendsto_atTop_zero
    have htail : Tendsto (fun j : ℕ => ∑' k, tail n (j+1) k) atTop (𝓝 0) := by
      refine squeeze_zero (fun j => tsum_nonneg fun k => mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/8) _) (endpoint_nonneg _ _)) (fun j => ?_) hrows
      simp only [tail,factor,Q,B,tsum_mul_left]
      have he : (1/8:ℝ)^(j+1) ≤ r^j := (pow_le_pow_right_of_le_one (by norm_num) (by norm_num)
        (Nat.le_succ j)).trans (pow_le_pow_left₀ (by norm_num) hr.le _)
      exact mul_le_mul_of_nonneg_right he (tsum_nonneg fun k => endpoint_nonneg _ k)
    have hlim := (tail_mass_limit hn).comp (tendsto_add_atTop_nat 1)
    have hpos : 0 < 4*(n:ℝ)^3*squareAutocorrelationMass := by
      exact mul_pos (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) _)) squareAutocorrelationMass_pos
    exact hpos.ne (tendsto_nhds_unique htail hlim)
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => tsum_nonneg fun j => hQ₀ (j,k))).mp hbad
  have hrest := ((endpoint_summable hn).add hE.prod_symm.prod).hasSum.tendsto_sum_nat
  have hmain := hdiv.const_mul_atTop (sub_pos.mpr hr)
  have h := hmain.atTop_add hrest
  refine h.congr fun K => ?_
  change (r-1/8)*(∑ k ∈ range K, ∑' j, Q (j,k))+
    (∑ k ∈ range K, (squarePrimeEndpoint n k + ∑' j, E (j,k)))=_
  rw [mul_sum,← sum_add_distrib]
  exact sum_congr rfl fun k _ => (hcolumn k).symm

/-- In conductor order the signed price is absolutely summable below
the threshold determined by the zero width. -/
theorem dyadic_square_conductor_order {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r)
    (hwidth : r*2^(2+2*SquareRootThreshold.zetaZeroWidth:ℝ) < 1) :
    Summable (fun j : ℕ => r^j*Real.log (q (2^j*n):ℝ)) := by
  obtain ⟨C,hC,h⟩ := successorSquare_diagonal_log_at_width
  let b := 2*SquareRootThreshold.zetaZeroWidth
  have hb : 0 ≤ b := mul_nonneg two_pos.le SquareRootThreshold.zetaZeroWidth_nonneg
  let A := C*(n:ℝ)^2*(2*(n:ℝ))^b
  have hgeo := (summable_geometric_of_lt_one (mul_nonneg hr (Real.rpow_nonneg (by norm_num) _)) hwidth).mul_right A
  apply Summable.of_norm_bounded hgeo
  intro j
  let m := orbit n j
  have hm := orbit_pos hn j
  have hm₁ : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (m:ℝ)+1) (by linarith only [hm₁] : (m:ℝ)+1 ≤ 2*m) hb
  have hbound := (h m hm).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hC (sq_nonneg _)))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hr _)]
  refine (mul_le_mul_of_nonneg_left hbound (pow_nonneg hr j)).trans_eq ?_
  dsimp only [m,orbit,A]
  push_cast
  rw [show 2*((2:ℝ)^j*n)=2^j*(2*n) by ring,Real.mul_rpow (by positivity) (by positivity),
    mul_pow (2:ℝ)^j,← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2),
    show (j:ℝ)*b=b*j by ring,Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,
    Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_two,mul_pow r,mul_pow (2^2:ℝ)]
  ring

end GaloisForLFunctions.CountingHolography.Sections
