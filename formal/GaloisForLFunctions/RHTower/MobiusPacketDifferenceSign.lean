import GaloisForLFunctions.RHTower.MobiusRenewalEnergySign
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Signed differences of the literal Möbius packets

For `b_N(r,k) = sum_{n=1}^N mu(n)/(n+1)^r * ((n-1)/(n+1))^k`, high finite
differences recover the opposite coefficients at one and two with geometric errors uniform
in the integer cutoff. Consequently neither global sign gives complete monotonicity.

The same packets satisfy an exact adjacent-exponent recurrence. The shifted arithmetic moment
is strictly positive immediately above exponent two and strictly negative immediately above
exponent one. Thus the first packet square increases eventually in cutoff near exponent one.
These source sign laws do not bound the complete weighted sum of packet squares.
-/

open Filter Topology Finset
open scoped BigOperators
noncomputable section
namespace RHTower.MobiusPacketDifference

def node (n : ℕ) : ℝ := (n : ℝ) / ((n : ℝ) + 2)
def weight (r : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 2) ^ (-r)
def coefficient (r : ℝ) (n : ℕ) : ℝ :=
  shiftedMobiusRealCoefficient n * weight r n
def packet (N : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ range N, coefficient r n * node n ^ k
def difference : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, k => f k
  | j+1, f, k => difference j f k - difference j f (k+1)
def majorant (n : ℕ) : ℝ := 4 / ((n : ℝ) + 2) ^ 2
def budget : ℝ := ∑' n : ℕ, majorant n
def unitDetector (N : ℕ) (r : ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ range N, coefficient r n * majorant n * (2 / ((n : ℝ)+2)) ^ h
def primeDetector (N : ℕ) (r : ℝ) (h : ℕ) : ℝ :=
  ∑ n ∈ range N,
    (coefficient r n * majorant n * node n) * (3 / ((n : ℝ)+2)) ^ h

private theorem node_nonneg (n : ℕ) : 0 ≤ node n := by unfold node; positivity
private theorem node_le_one (n : ℕ) : node n ≤ 1 := by
  unfold node
  apply (div_le_one (by positivity : (0:ℝ)<(n:ℝ)+2)).2
  linarith
private theorem one_sub_node (n : ℕ) : 1 - node n = 2 / ((n : ℝ)+2) := by
  unfold node
  field_simp
  ring
private theorem weight_nonneg (r : ℝ) (n : ℕ) : 0 ≤ weight r n := by
  unfold weight
  positivity
private theorem weight_le_one {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : weight r n ≤ 1 := by
  unfold weight
  calc
    ((n:ℝ)+2)^(-r) ≤ (1:ℝ)^(-r) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by linarith [show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n]) (by linarith)
    _ = 1 := Real.one_rpow _
private theorem abs_coefficient_le_one {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    |coefficient r n| ≤ 1 := by
  have hm : |shiftedMobiusRealCoefficient n| ≤ 1 := by
    unfold shiftedMobiusRealCoefficient
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n+1)
  rw [coefficient, abs_mul, abs_of_nonneg (weight_nonneg r n)]
  calc
    |shiftedMobiusRealCoefficient n| * weight r n ≤ 1 * weight r n :=
      mul_le_mul_of_nonneg_right hm (weight_nonneg r n)
    _ ≤ 1 := by simpa using weight_le_one hr n
private theorem majorant_nonneg (n : ℕ) : 0 ≤ majorant n := by
  unfold majorant
  positivity
private theorem majorant_summable : Summable majorant := by
  have hs := ((Real.summable_one_div_nat_add_rpow 2 2).mpr (by norm_num : (1:ℝ)<2)).mul_left 4
  change Summable (fun n : ℕ => 4 / ((n:ℝ)+2)^2)
  simpa only [Real.rpow_two, sq_abs, one_div, div_eq_mul_inv, one_mul] using! hs

theorem budget_nonneg : 0 ≤ budget := tsum_nonneg majorant_nonneg

private theorem finite_atom_error_bound
    (c q : ℕ → ℝ) (a N h : ℕ) (theta : ℝ) (hN : a < N)
    (htheta : 0 ≤ theta) (hqa : q a = 1)
    (hterm : ∀ n, n ≠ a → |c n * q n ^ h| ≤ theta ^ h * majorant n) :
    |(∑ n ∈ range N, c n * q n ^ h) - c a| ≤ theta ^ h * budget := by
  have ha : a ∈ range N := mem_range.mpr hN
  have heq : (∑ n ∈ range N, c n * q n ^ h) - c a =
      ∑ n ∈ (range N).erase a, c n * q n ^ h := by
    have hs := sum_erase_add (range N) (fun n => c n * q n ^ h) ha
    rw [hqa, one_pow, mul_one] at hs
    linarith
  rw [heq]
  calc
    |∑ n ∈ (range N).erase a, c n * q n ^ h| ≤
        ∑ n ∈ (range N).erase a, |c n * q n ^ h| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ (range N).erase a, theta ^ h * majorant n :=
      sum_le_sum fun n hn => hterm n (ne_of_mem_erase hn)
    _ = theta ^ h * ∑ n ∈ (range N).erase a, majorant n := by rw [mul_sum]
    _ ≤ theta ^ h * budget := mul_le_mul_of_nonneg_left
      (majorant_summable.sum_le_tsum _ (fun n _ => majorant_nonneg n))
      (pow_nonneg htheta h)

private theorem coefficient_majorant_bound {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    |coefficient r n * majorant n| ≤ majorant n := by
  rw [abs_mul, abs_of_nonneg (majorant_nonneg n)]
  simpa using mul_le_mul_of_nonneg_right (abs_coefficient_le_one hr n) (majorant_nonneg n)

theorem unitDetector_error (N : ℕ) (hN : 1 ≤ N) {r : ℝ} (hr : 0 ≤ r) (h : ℕ) :
    |unitDetector N r h - 2 ^ (-r)| ≤ (2/3 : ℝ)^h * budget := by
  have he := finite_atom_error_bound
    (fun n => coefficient r n * majorant n) (fun n => 2 / ((n:ℝ)+2))
    0 N h (2/3) (by omega) (by norm_num) (by norm_num) ?_
  · have h0 : coefficient r 0 * majorant 0 = 2 ^ (-r) := by
      norm_num [coefficient, weight, majorant, shiftedMobiusRealCoefficient]
    change |unitDetector N r h - coefficient r 0 * majorant 0| ≤ _ at he
    rw [h0] at he
    exact he
  · intro n hn
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have hq : 2 / ((n:ℝ)+2) ≤ (2/3:ℝ) := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).2
      linarith
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℝ)≤2/((n:ℝ)+2))]
    calc
      |coefficient r n * majorant n| * (2/((n:ℝ)+2))^h ≤
          majorant n * (2/3:ℝ)^h :=
        mul_le_mul (coefficient_majorant_bound hr n)
          (pow_le_pow_left₀ (by positivity) hq h) (by positivity) (majorant_nonneg n)
      _ = _ := mul_comm _ _

theorem primeDetector_error (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr : 0 ≤ r) (h : ℕ) :
    |primeDetector N r h + (4/27:ℝ) * 3 ^ (-r)| ≤ (3/4:ℝ)^h * budget := by
  have he := finite_atom_error_bound
    (fun n => coefficient r n * majorant n * node n) (fun n => 3 / ((n:ℝ)+2))
    1 N h (3/4) (by omega) (by norm_num) (by norm_num) ?_
  · have hm : shiftedMobiusRealCoefficient 1 = -1 := by
      have hp := ArithmeticFunction.moebius_apply_prime Nat.prime_two
      unfold shiftedMobiusRealCoefficient
      norm_num
      exact_mod_cast hp
    have h1 : coefficient r 1 * majorant 1 * node 1 = -(4/27:ℝ)*3^(-r) := by
      norm_num [coefficient, weight, majorant, node, hm]
      ring
    change |primeDetector N r h - coefficient r 1 * majorant 1 * node 1| ≤ _ at he
    rw [h1, neg_mul, sub_neg_eq_add] at he
    exact he
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp only [node, Nat.cast_zero, zero_div, mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (majorant_nonneg 0)
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    have hq : 3 / ((n:ℝ)+2) ≤ (3/4:ℝ) := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).2
      linarith
    have hc : |coefficient r n * majorant n * node n| ≤ majorant n := by
      rw [abs_mul, abs_of_nonneg (node_nonneg n)]
      simpa using mul_le_mul (coefficient_majorant_bound hr n) (node_le_one n)
        (node_nonneg n) (majorant_nonneg n)
    rw [abs_mul, abs_pow, abs_of_nonneg (by positivity : (0:ℝ)≤3/((n:ℝ)+2))]
    calc
      |coefficient r n * majorant n * node n| * (3/((n:ℝ)+2))^h ≤
          majorant n * (3/4:ℝ)^h :=
        mul_le_mul hc (pow_le_pow_left₀ (by positivity) hq h)
          (by positivity) (majorant_nonneg n)
      _ = _ := mul_comm _ _

theorem difference_packet (N : ℕ) (r : ℝ) (j k : ℕ) :
    difference j (packet N r) k =
      ∑ n ∈ range N, coefficient r n * node n ^ k * (2 / ((n:ℝ)+2)) ^ j := by
  induction j generalizing k with
  | zero => simp [difference, packet]
  | succ j ih =>
    simp only [difference, ih]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    rw [pow_succ, pow_succ, ← one_sub_node]
    ring

theorem unitDetector_eq_difference (N : ℕ) (r : ℝ) (h : ℕ) :
    unitDetector N r h = difference (h+2) (packet N r) 0 := by
  rw [difference_packet, unitDetector]
  apply sum_congr rfl
  intro n hn
  simp only [pow_zero, mul_one, pow_add, div_pow, majorant]
  norm_num
  ring

theorem primeDetector_eq_difference (N : ℕ) (r : ℝ) (h : ℕ) :
    primeDetector N r h = (3/2:ℝ)^h * difference (h+2) (packet N r) 1 := by
  rw [difference_packet, primeDetector, mul_sum]
  apply sum_congr rfl
  intro n hn
  have he : 3 / ((n:ℝ)+2) = (3/2:ℝ) * (2/((n:ℝ)+2)) := by ring
  rw [he, mul_pow, pow_add, pow_one]
  simp only [majorant, div_pow]
  norm_num
  ring

theorem eventually_opposite_detector_signs {r : ℝ} (hr : 0 ≤ r) :
    ∀ᶠ h : ℕ in atTop, ∀ N : ℕ, 2 ≤ N →
      0 < unitDetector N r h ∧ primeDetector N r h < 0 := by
  have h2 : Tendsto (fun h : ℕ => (2/3:ℝ)^h * budget) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (2/3:ℝ)<1)).mul_const budget
  have h3 : Tendsto (fun h : ℕ => (3/4:ℝ)^h * budget) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3/4:ℝ)<1)).mul_const budget
  have hp2 : (0:ℝ) < 2^(-r) := Real.rpow_pos_of_pos (by norm_num) _
  have hp3 : (0:ℝ) < (4/27:ℝ)*3^(-r) := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hp2), h3.eventually (gt_mem_nhds hp3)] with h hh2 hh3
  intro N hN
  have hu := (abs_le.mp (unitDetector_error N (by omega) hr h)).1
  have hp := (abs_le.mp (primeDetector_error N hN hr h)).2
  constructor <;> linarith

theorem no_completely_monotone_orientation (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    ¬ ((∀ j k : ℕ, 0 ≤ difference j (packet N r) k) ∨
      (∀ j k : ℕ, difference j (packet N r) k ≤ 0)) := by
  obtain ⟨h, hh⟩ := (eventually_opposite_detector_signs hr).exists
  obtain ⟨hu,hp⟩ := hh N hN
  rw [unitDetector_eq_difference] at hu
  rw [primeDetector_eq_difference] at hp
  have hp' : difference (h+2) (packet N r) 1 < 0 := by
    by_contra he
    have hn := mul_nonneg (by positivity : (0:ℝ)≤(3/2:ℝ)^h) (le_of_not_gt he)
    linarith
  rintro (hpos | hneg)
  · exact (not_lt_of_ge (hpos (h+2) 1)) hp'
  · exact (not_lt_of_ge (hneg (h+2) 0)) hu

end RHTower.MobiusPacketDifference

namespace RHTower.MobiusRenewalEnergy

def primeCorrection (r : ℝ) : ℝ :=
  2 * (difference r 1 + difference r 2 + difference r 4) + difference r 3

private theorem correction_continuous : Continuous primeCorrection := by
  have hw (n : ℕ) : Continuous (fun r : ℝ => weight r n) := by
    unfold weight
    exact (Real.continuous_const_rpow (by positivity : (n:ℝ)+1 ≠ 0)).comp continuous_neg
  have hd (n : ℕ) : Continuous (fun r : ℝ => difference r n) := (hw n).sub (hw (n+1))
  exact continuous_const.mul (((hd 1).add (hd 2)).add (hd 4)) |>.add (hd 3)

/-- The negative prime coefficients and first squareful coefficient improve the full shifted
moment lower bound without discarding any later integer. -/
theorem shiftedMoment_lower_primeCorrection (N : ℕ) (hN : 5 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    originalMoment N r - 1 + primeCorrection r ≤ shiftedMoment N r := by
  have hd (n : ℕ) : 0 ≤ difference r n := by
    unfold difference weight
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  have hmu (n : ℕ) : shiftedMobiusRealCoefficient n ≤ 1 := by
    unfold shiftedMobiusRealCoefficient
    exact_mod_cast (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n+1))).2
  have hterm (n : ℕ) : 0 ≤ (1-shiftedMobiusRealCoefficient n)*difference r n :=
    mul_nonneg (by linarith [hmu n]) (hd n)
  have hs : ({1,2,3,4} : Finset ℕ) ⊆ range N := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> simp only [mem_range] <;> omega
  have hsum := sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => hterm n)
  have h2 : shiftedMobiusRealCoefficient 1 = -1 := by
    have hp := ArithmeticFunction.moebius_apply_prime Nat.prime_two
    unfold shiftedMobiusRealCoefficient
    norm_num
    exact_mod_cast hp
  have h3 : shiftedMobiusRealCoefficient 2 = -1 := by
    have hp := ArithmeticFunction.moebius_apply_prime Nat.prime_three
    unfold shiftedMobiusRealCoefficient
    norm_num
    exact_mod_cast hp
  have h5 : shiftedMobiusRealCoefficient 4 = -1 := by
    have hp := ArithmeticFunction.moebius_apply_prime Nat.prime_five
    unfold shiftedMobiusRealCoefficient
    norm_num
    exact_mod_cast hp
  have h4 : shiftedMobiusRealCoefficient 3 = 0 := by
    have hp := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by omega : 2 ≠ 0)
    norm_num [shiftedMobiusRealCoefficient] at hp ⊢
    exact hp
  simp only [sum_insert (by simp : (1 : ℕ) ∉ ({2,3,4} : Finset ℕ)),
    sum_insert (by simp : (2 : ℕ) ∉ ({3,4} : Finset ℕ)),
    sum_insert (by simp : (3 : ℕ) ∉ ({4} : Finset ℕ)),
    sum_singleton, h2, h3, h4, h5] at hsum
  have htall : ∀ M : ℕ, ∑ n ∈ range M, difference r n = 1-weight r M := by
    intro M
    induction M with
    | zero => simp [weight]
    | succ M ih => rw [Finset.sum_range_succ, ih, difference]; ring
  have ht := htall N
  have heq : (∑ n ∈ range N, (1-shiftedMobiusRealCoefficient n)*difference r n) =
      1-weight r N-(originalMoment N r-shiftedMoment N r) := by
    simp_rw [sub_mul, one_mul, sum_sub_distrib]
    rw [ht]
    simp only [originalMoment, shiftedMoment, difference, mul_sub, sum_sub_distrib]
  rw [heq] at hsum
  have hw : 0 ≤ weight r N := by unfold weight; positivity
  unfold primeCorrection
  linarith

private theorem invZeta_two_real_gt : (3/5:ℝ) < (Sieve.invZeta (2:ℂ)).re := by
  have heq : (Sieve.invZeta (2:ℂ)).re = 6 / Real.pi^2 := by
    rw [Sieve.invZeta_eq_inv (by norm_num : (2:ℂ)≠1), riemannZeta_two]
    have hc : (((Real.pi:ℂ)^2/6)⁻¹) = ((6/Real.pi^2:ℝ):ℂ) := by
      push_cast
      rw [inv_div]
    simpa only [Complex.ofReal_re] using congrArg Complex.re hc
  rw [heq]
  have hp : Real.pi^2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d4]
  apply (lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
  linarith

/-- The shifted arithmetic moment is uniformly separated from zero positively at every
sufficiently long cutoff throughout a right neighborhood of exponent two. -/
theorem eventually_shiftedMoment_positive_near_two :
    ∃ ε > 0, ∀ r : ℝ, 2 < r → r < 2+ε →
      ∀ᶠ N : ℕ in atTop, (1/200:ℝ) < shiftedMoment N r := by
  let g : ℝ → ℝ := fun r => (Sieve.invZeta (r:ℂ)).re - 1 + primeCorrection r
  have hc : ContinuousAt g 2 := by
    have hi : ContinuousAt (fun r : ℝ => (Sieve.invZeta (r:ℂ)).re) 2 :=
      Complex.continuous_re.continuousAt.comp
        ((Sieve.differentiableAt_invZeta_of_zeta_ne_zero
          (by norm_num : (2:ℂ)≠1)
          (riemannZeta_ne_zero_of_one_lt_re (by norm_num : (1:ℝ)<(2:ℂ).re))).continuousAt.comp
            (f := fun r : ℝ => (r:ℂ)) (x := (2:ℝ)) Complex.continuous_ofReal.continuousAt)
    exact (hi.sub continuousAt_const).add correction_continuous.continuousAt
  have hg : (1/100:ℝ) < g 2 := by
    have hi := invZeta_two_real_gt
    norm_num [g, primeCorrection, difference, weight, Real.rpow_neg, Real.rpow_two]
    linarith
  have hn : ∀ᶠ r in nhds (2:ℝ), (1/100:ℝ) < g r :=
    hc.eventually (eventually_gt_nhds hg)
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp hn
  refine ⟨ε,hε,fun r hr hrε => ?_⟩
  have hgr : (1/100:ℝ) < g r := he (by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0<r-2)]
    linarith)
  have ht : Tendsto (fun N => originalMoment N r-1+primeCorrection r) atTop (nhds (g r)) :=
    ((tendsto_originalMoment (by linarith : 1<r)).sub_const 1).add_const _
  have hN := ht.eventually (eventually_gt_nhds (show (1/200:ℝ)<g r by linarith))
  filter_upwards [hN,eventually_ge_atTop 5] with N hbound hfive
  exact hbound.trans_le (shiftedMoment_lower_primeCorrection N hfive (by linarith))

end RHTower.MobiusRenewalEnergy

namespace RHTower.MobiusPacketDifference

theorem packet_zero_eq_shiftedMoment (N : ℕ) (r : ℝ) :
    packet N r 0 = MobiusRenewalEnergy.shiftedMoment N r := by
  simp only [packet, coefficient, weight, pow_zero, mul_one,
    MobiusRenewalEnergy.shiftedMoment, MobiusRenewalEnergy.weight]
  apply sum_congr rfl
  intro n hn
  congr 2
  push_cast
  ring

theorem packet_succ_eq_adjacent_orders (N : ℕ) (r : ℝ) (k : ℕ) :
    packet N r (k+1) = packet N r k - 2*packet N (r+1) k := by
  simp only [packet, pow_succ, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  have hw : weight (r+1) n = weight r n * ((n:ℝ)+2)⁻¹ := by
    unfold weight
    rw [show -(r+1)=-r+(-1) by ring, Real.rpow_add (by positivity), Real.rpow_neg_one]
  have hq := one_sub_node n
  unfold coefficient
  rw [hw]
  rw [div_eq_mul_inv] at hq
  have hnode : node n = 1 - 2 * ((n:ℝ)+2)⁻¹ := by linarith
  rw [hnode]
  ring

theorem packet_one_eq_adjacent_orders (N : ℕ) (r : ℝ) :
    packet N r 1 = packet N r 0 - 2*packet N (r+1) 0 :=
  packet_succ_eq_adjacent_orders N r 0

/-- Packet squares increase at their very first step for actual Möbius prefixes near the
critical exponent. The cutoffs remain ordinary integer cutoffs. -/
theorem eventually_first_packet_square_increases :
    ∃ ε > 0, ∀ r : ℝ, 1<r → r<1+ε →
      ∀ᶠ N : ℕ in atTop, packet N r 0 ^ 2 < packet N r 1 ^ 2 := by
  obtain ⟨ε₁,hε₁,hneg⟩ := MobiusRenewalEnergy.eventually_shiftedMoment_negative
  obtain ⟨ε₂,hε₂,hpos⟩ := MobiusRenewalEnergy.eventually_shiftedMoment_positive_near_two
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r hr hrε => ?_⟩
  have hn := hneg r hr (by linarith [min_le_left ε₁ ε₂])
  have hp := hpos (r+1) (by linarith) (by linarith [min_le_right ε₁ ε₂])
  filter_upwards [hn,hp] with N hn hp
  have hn' : packet N r 0 < 0 := by rw [packet_zero_eq_shiftedMoment]; linarith
  have hp' : 0 < packet N (r+1) 0 := by rw [packet_zero_eq_shiftedMoment]; linarith
  rw [packet_one_eq_adjacent_orders]
  nlinarith [sq_pos_of_pos hp', mul_neg_of_neg_of_pos hn' hp']

end RHTower.MobiusPacketDifference
