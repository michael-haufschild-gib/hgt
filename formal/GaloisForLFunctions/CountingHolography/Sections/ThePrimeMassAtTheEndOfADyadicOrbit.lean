import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
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

private theorem endpoint_zero {n k : ℕ} (hn : 0<n) (hk : k ∉ S n) :
    price n k=0 ∧ squarePrimeEndpoint n k=0 ∧ squarePrimeEndpoint (2*n) k=0 := by
  by_cases hp : k.Prime
  · have hcut : 3*windowEnd ((2*n+1)^2+1)<k :=
      lt_of_not_ge fun h => hk (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,h⟩,hp⟩)
    have hkL : (windowEnd ((2*n+1)^2+1):ℝ)<k := by
      exact_mod_cast (by omega : windowEnd ((2*n+1)^2+1)<k)
    have hb := (successorSquareWindowScale_bounds n).2.2.trans_lt hkL
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hk' : 0 < (k:ℝ) := Nat.cast_pos.mpr hp.pos
    have hhigh : 0<((2*n:ℕ):ℝ) := by positivity
    have hsq : (((2*n:ℕ):ℝ))^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hhigh.le (by exact_mod_cast Nat.le_succ (2*n)) 2
    have hlow : (n:ℝ)^2 ≤ (((2*n+1:ℕ):ℝ))^2 :=
      pow_le_pow_left₀ hn'.le (by exact_mod_cast (by omega : n≤2*n+1)) 2
    have hz {x : ℝ} (hx : 0<x) (h : x^2≤(((2*n+1:ℕ):ℝ))^2) : splineAutoCorr (Real.log k-Real.log (x^2))=0 := by
      apply splineAutoCorr_zero_outside
      apply lt_of_lt_of_le _ (le_abs_self _)
      rw [← Real.log_div hk'.ne' (sq_pos_of_pos hx).ne',Real.lt_log_iff_exp_lt (div_pos hk' (sq_pos_of_pos hx)),lt_div_iff₀ (sq_pos_of_pos hx)]
      have he := (mul_le_mul_of_nonneg_left h (Real.exp_pos 8).le)
      exact he.trans_lt hb
    have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
    change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
    simp only [price,he,if_neg hk,Int.cast_zero,zero_mul,squarePrimeEndpoint,hz hn' hlow,hz hhigh hsq,mul_zero,and_self]
  · simp [price,squarePrimeEndpoint,weight,hp]

private theorem error_row {n k : ℕ} (hn : 0<n) :
    err n k=((deningerRatExp (q n) k:ℝ)-diagonalPrimeProfile n k)*weight k := by
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have he : Real.log (((2*n:ℕ):ℝ)^2)=Real.log ((n:ℝ)^2)+Real.log 4 := by
    push_cast
    rw [mul_pow,Real.log_mul (by norm_num) (sq_pos_of_pos hn').ne']
    norm_num
    ring
  simp only [err,price,squarePrimeEndpoint,diagonalPrimeProfile,squareLogProfile,he,
    show Real.log k-(Real.log ((n:ℝ)^2)+Real.log 4)=Real.log k-Real.log ((n:ℝ)^2)-Real.log 4 by ring,
    Nat.cast_mul,Nat.cast_ofNat]
  ring

private theorem error_summable {n : ℕ} (hn : 0<n) : Summable (fun k => |err n k|) :=
  summable_of_ne_finset_zero (s := S n) fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃]

private theorem error_budget : ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n → (∑' k, |err n k|)≤C*(n:ℝ)^2 := by
  obtain ⟨C,hC,hE⟩ := diagonal_prime_exponent_profile_error
  refine ⟨C,hC,fun {n} hn => ?_⟩
  rw [tsum_eq_sum (s := S n) (fun k hk => by
    obtain ⟨h₁,h₂,h₃⟩ := endpoint_zero hn hk
    simp [err,h₁,h₂,h₃])]
  apply le_trans (le_of_eq (sum_congr rfl fun k hk => ?_)) (hE hn)
  have hp := (mem_filter.mp hk).2
  rw [error_row hn,abs_mul,weight,if_pos hp,abs_of_nonneg (Real.log_natCast_nonneg _),vonMangoldt_apply_prime hp]
  rfl

private theorem price_sum (n : ℕ) (hn : 0<n) : (∑' k, price n k)=Real.log (q n:ℝ) := by
  rw [tsum_eq_sum (s := S n) (fun _ hk => (endpoint_zero hn hk).1),q,log_ordinaryPrimeGenerator]
  refine sum_congr rfl fun k hk => ?_
  have hp := (mem_filter.mp hk).2
  have he := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) k
  change deningerRatExp (q n) k=if k ∈ S n then _ else 0 at he
  rw [price,he,if_pos hk,weight,if_pos hp,vonMangoldt_apply_prime hp]

private theorem endpoint_summable {n : ℕ} (hn : 0<n) : Summable (squarePrimeEndpoint n) :=
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
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hsub : (∑' p : Nat.Primes, squarePrimeEndpoint n p.val)=∑' k, squarePrimeEndpoint n k :=
    tsum_subtype_eq_of_support_subset fun k hk hp => hk (by simp [squarePrimeEndpoint,weight,hp])
  rw [← hsub]
  let L := fun p : Nat.Primes => Real.log (p:ℕ)*(splineAutoCorr (Real.log ((p:ℕ)/(n:ℝ)^2))/Real.sqrt ((p:ℕ)/(n:ℝ)^2))
  have he (p : Nat.Primes) : squarePrimeEndpoint n p.val = (4*(n:ℝ))*L p := by
    have hp : 0<((p:ℕ):ℝ) := Nat.cast_pos.mpr p.property.pos
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

private theorem orbit_pos {n : ℕ} (hn : 0<n) (j : ℕ) : 0<orbit n j :=
  Nat.mul_pos (pow_pos (by decide : 0<2) j) hn

private theorem orbit_infty {n : ℕ} (hn : 0<n) : Tendsto (orbit n) atTop atTop := by
  refine tendsto_atTop_mono (f := fun j : ℕ => 2^j) (fun j => ?_) (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1<(2:ℕ)))
  exact Nat.le_mul_of_pos_right _ hn

private theorem row_split (n j k : ℕ) :
    row n j k=tail n j k-tail n (j+1) k+remainder n (j,k) := by
  simp only [row,tail,remainder,factor,orbit,err,pow_succ]
  rw [show (2:ℕ)^j*2*n=2*(2^j*n) by ring]
  ring

private theorem summable_remainder {n : ℕ} (hn : 0<n) : Summable (remainder n) := by
  obtain ⟨C,hC,hE⟩ := error_budget
  have hf (j : ℕ) : 0≤factor j := pow_nonneg (by norm_num) _
  have habs (j k : ℕ) : |remainder n (j,k)|=factor j*|err (orbit n j) k| := by
    rw [remainder,abs_mul,abs_of_nonneg (hf j)]
  apply Summable.of_norm
  simp only [Real.norm_eq_abs]
  apply (summable_prod_of_nonneg (fun _ => abs_nonneg _)).mpr
  constructor
  · intro j
    simp_rw [habs]
    exact (error_summable (orbit_pos hn j)).mul_left _
  · let D := C*(n:ℝ)^2
    have hgeo := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1)).mul_right D
    apply Summable.of_nonneg_of_le (fun j => tsum_nonneg fun k => abs_nonneg _) _ hgeo
    intro j
    simp_rw [habs]
    rw [tsum_mul_left]
    refine (mul_le_mul_of_nonneg_left (hE (orbit_pos hn j)) (hf j)).trans_eq ?_
    dsimp only [factor,orbit,D]
    push_cast
    rw [mul_pow,← pow_mul,Nat.mul_comm j 2,pow_mul]
    calc _ = ((1/8:ℝ)^j*((2:ℝ)^2)^j)*(C*(n:ℝ)^2) := by ring
      _ = _ := by rw [← mul_pow]; norm_num

private theorem tail_eventually_zero {n : ℕ} (hn : 0<n) (k : ℕ) :
    ∀ᶠ j : ℕ in atTop, tail n j k=0 := by
  have ht := Real.tendsto_log_atTop.comp ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp
    (tendsto_natCast_atTop_atTop.comp (orbit_infty hn)))
  filter_upwards [ht.eventually_gt_atTop (Real.log k+8)] with j hj
  change Real.log k+8<Real.log ((orbit n j:ℝ)^2) at hj
  have hz := splineAutoCorr_zero_outside (x := Real.log k-Real.log ((orbit n j:ℝ)^2))
    (by linarith only [hj,neg_abs_le (Real.log k-Real.log ((orbit n j:ℝ)^2))])
  simp [tail,squarePrimeEndpoint,hz]

private theorem orbit_column_sum {n : ℕ} (hn : 0<n) (k : ℕ) :
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

private theorem tail_mass_limit {n : ℕ} (hn : 0<n) :
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
theorem dyadic_square_prime_mass_escape {n : ℕ} (hn : 0<n) :
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
theorem not_summable_dyadic_square_log_valuations {n : ℕ} (hn : 0<n) :
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
  have hp : 0<4*(n:ℝ)^3*squareAutocorrelationMass :=
    mul_pos (mul_pos (by norm_num) (pow_pos (Nat.cast_pos.mpr hn) 3)) squareAutocorrelationMass_pos
  exact hp.ne' (tendsto_nhds_unique he hzero)

#print axioms tendsto_squarePrimeEndpoint_mass
#print axioms dyadic_square_prime_mass_escape
#print axioms not_summable_dyadic_square_log_valuations

end GaloisForLFunctions.CountingHolography.Sections
