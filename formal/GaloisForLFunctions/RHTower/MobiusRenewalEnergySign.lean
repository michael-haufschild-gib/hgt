import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift
import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall

/-!
# Signed first-atom moments of finite Möbius renewal

For the literal integer section `F_N(x) = sum_{n=1}^N mu(n) exp(-n*x)`, define
`U_N(r) = sum_{n=1}^N mu(n)/(n+1)^r`. The nonnegative reciprocal-power differences,
together with `mu(1)=1` and `mu(4)=0`, give an explicit positive gap between the
ordinary and shifted moments. The ordinary moment converges to the regular
reciprocal of zeta, which vanishes at one. Hence `U_N(r) < -1/80` eventually in
integer cutoff throughout a nonempty interval immediately above one.

The complete weighted pairing of `F_N` with `exp(-x)-F_N` is exactly
`Gamma(r)*U_N(r)-E_N(r)`, and is eventually strictly negative on that interval.
These are source sign laws; they give no uniform upper bound for `E_N`.
-/

open Filter Topology Finset
open scoped BigOperators
noncomputable section
namespace RHTower
namespace MobiusRenewalEnergy

def weight (r : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-r)
def difference (r : ℝ) (n : ℕ) : ℝ := weight r n - weight r (n+1)
def originalMoment (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ range N, shiftedMobiusRealCoefficient n * weight r n
def shiftedMoment (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ range N, shiftedMobiusRealCoefficient n * weight r (n+1)

private theorem coefficient_lower (n : ℕ) : -1 ≤ shiftedMobiusRealCoefficient n := by
  have h := (abs_le.mp (ArithmeticFunction.abs_moebius_le_one (n := n+1))).1
  unfold shiftedMobiusRealCoefficient
  exact_mod_cast h

private theorem coefficient_zero : shiftedMobiusRealCoefficient 0 = 1 := by
  simp [shiftedMobiusRealCoefficient]

private theorem coefficient_three : shiftedMobiusRealCoefficient 3 = 0 := by
  have h := ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by decide : 2 ≠ 0)
  norm_num [shiftedMobiusRealCoefficient] at h ⊢
  exact h

private theorem difference_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) :
    0 ≤ difference r n := by
  unfold difference weight
  apply sub_nonneg.mpr
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

private theorem sum_difference (N : ℕ) (r : ℝ) :
    ∑ n ∈ range N, difference r n = 1 - weight r N := by
  induction N with
  | zero => simp [weight]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, difference]
    ring

/-- The first nonsquarefree coefficient leaves a strictly positive telescoping defect. -/
theorem difference_moment_lower (N : ℕ) (hN : 4 ≤ N) {r : ℝ} (hr : 1 ≤ r) :
    difference r 3 ≤ originalMoment N r - shiftedMoment N r := by
  have hpos (n : ℕ) : 0 ≤ (1 + shiftedMobiusRealCoefficient n) * difference r n :=
    mul_nonneg (by linarith [coefficient_lower n]) (difference_nonneg (by linarith) n)
  have hsubset : ({0,3} : Finset ℕ) ⊆ range N := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> simp only [mem_range] <;> omega
  have hsum := sum_le_sum_of_subset_of_nonneg hsubset
    (fun n _ _ => hpos n)
  simp only [sum_insert (by decide : (0 : ℕ) ∉ ({3} : Finset ℕ)),
    sum_singleton, coefficient_zero, coefficient_three] at hsum
  have hid : (∑ n ∈ range N, (1 + shiftedMobiusRealCoefficient n) * difference r n) =
      (1 - weight r N) + (originalMoment N r - shiftedMoment N r) := by
    simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
    rw [sum_difference]
    simp only [originalMoment, shiftedMoment, difference, mul_sub, Finset.sum_sub_distrib]
  rw [hid] at hsum
  have hw : weight r 1 ≤ (1/2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -r ≤ -1 by linarith)
    simpa [weight, Real.rpow_neg_one, show (1 : ℝ)+1=2 by ring] using h
  have hd : difference r 0 = 1 - weight r 1 := by simp [difference, weight]
  have hn : 0 ≤ weight r N := Real.rpow_nonneg (by positivity) _
  rw [hd] at hsum
  linarith

private theorem summable_original {r : ℝ} (hr : 1 < r) :
    Summable (fun n => shiftedMobiusRealCoefficient n * weight r n) := by
  have hw : Summable (weight r) := by
    simpa only [weight, Nat.cast_add, Nat.cast_one] using!
      (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by linarith : -r < -1))
  apply Summable.of_norm_bounded hw
  intro n
  have hmu : ‖shiftedMobiusRealCoefficient n‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    unfold shiftedMobiusRealCoefficient
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n+1))
  have hw0 : 0 ≤ weight r n := Real.rpow_nonneg (by positivity) _
  rw [norm_mul, Real.norm_of_nonneg hw0]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hmu hw0

private theorem tsum_original {r : ℝ} (hr : 1 < r) :
    (∑' n, shiftedMobiusRealCoefficient n * weight r n) =
      (Sieve.invZeta (r : ℂ)).re := by
  let f : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ) * (n : ℝ)^(-r)
  have heq (n : ℕ) : f (n+1) = shiftedMobiusRealCoefficient n * weight r n := by
    simp [f, shiftedMobiusRealCoefficient, weight]
  have hs : Summable (fun n => f (n+1)) := by
    simpa only [heq] using summable_original hr
  have hshift : (∑' n, f n) = ∑' n, shiftedMobiusRealCoefficient n * weight r n := by
    rw [tsum_eq_zero_add' hs]
    rw [show f 0 = 0 by simp [f], zero_add]
    exact tsum_congr heq
  have hcast : (fun n => (f n : ℂ)) =
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) * (n : ℂ)^(-(r : ℂ))) := by
    funext n
    simp only [f, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
      Complex.ofReal_neg]
  have h := Sieve.tsum_moebius_cpow_eq_invZeta (s := (r : ℂ)) (by simpa using hr)
  rw [← hcast, ← Complex.ofReal_tsum, hshift] at h
  exact congrArg Complex.re h

theorem tendsto_originalMoment {r : ℝ} (hr : 1 < r) :
    Tendsto (fun N => originalMoment N r) atTop (nhds (Sieve.invZeta (r : ℂ)).re) := by
  have h := (summable_original hr).hasSum.tendsto_sum_nat
  rwa [tsum_original hr] at h

/-- The literal shifted source moment is negative throughout a nonempty right neighborhood
of the zeta pole, at every sufficiently large integer cutoff. -/
theorem eventually_shiftedMoment_negative :
    ∃ ε > 0, ∀ r : ℝ, 1 < r → r < 1+ε →
      ∀ᶠ N : ℕ in atTop, shiftedMoment N r < -(1/80 : ℝ) := by
  let g : ℝ → ℝ := fun r => (Sieve.invZeta (r : ℂ)).re - difference r 3
  have hc : ContinuousAt g 1 := by
    have hi : ContinuousAt (fun r : ℝ => (Sieve.invZeta (r : ℂ)).re) 1 :=
      Complex.continuous_re.continuousAt.comp
        (Sieve.differentiableAt_invZeta_one.continuousAt.comp
          (f := fun r : ℝ => (r : ℂ)) (x := (1 : ℝ)) Complex.continuous_ofReal.continuousAt)
    have hd : ContinuousAt (fun r => difference r 3) 1 := by
      unfold difference weight
      exact ((Real.continuous_const_rpow (by positivity : (3 : ℝ)+1 ≠ 0)).comp
        continuous_neg).continuousAt.sub
          (((Real.continuous_const_rpow (by positivity : ((3+1:ℕ) : ℝ)+1 ≠ 0)).comp
            continuous_neg).continuousAt)
    exact hi.sub hd
  have hg : g 1 < -(1/40 : ℝ) := by
    norm_num [g, difference, weight, Sieve.invZeta_one, Real.rpow_neg_one]
  have hnear : ∀ᶠ r in nhds (1 : ℝ), g r < -(1/40 : ℝ) :=
    hc.eventually (eventually_lt_nhds hg)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ε, hε, fun r hr hrε => ?_⟩
  have hgr : g r < -(1/40 : ℝ) := he (by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < r-1)]
    linarith)
  have ht : Tendsto (fun N => originalMoment N r - difference r 3) atTop (nhds (g r)) :=
    (tendsto_originalMoment hr).sub_const _
  have hN := ht.eventually (eventually_lt_nhds (show g r < -(1/80 : ℝ) by linarith))
  filter_upwards [hN, eventually_ge_atTop 4] with N hbound hfour
  have hd := difference_moment_lower N hfour hr.le
  linarith

open Set MeasureTheory

private def atom (r : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x^(r-1) * Real.exp (-(((n : ℝ)+2)*x))

private theorem atom_integrable {r : ℝ} (hr : 0 < r) (n : ℕ) :
    IntegrableOn (atom r n) (Ioi 0) := by
  simpa only [atom, Real.rpow_one, neg_mul] using!
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := r-1) (b := (n : ℝ)+2)
      (by linarith) (by norm_num) (by positivity))

private theorem atom_integral {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), atom r n x) = Real.Gamma r * weight r (n+1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := r-1) (b := (n : ℝ)+2)
    (by norm_num) (by linarith) (by positivity)
  have he : r-1+1 = r := by ring
  have h' : (∫ x in Ioi (0 : ℝ), x^(r-1) * Real.exp (-((n : ℝ)+2)*x)) =
      ((n : ℝ)+2)^(-r) * Real.Gamma r := by
    simpa only [Real.rpow_one, he, div_one, mul_one] using h
  calc
    _ = ((n : ℝ)+2)^(-r) * Real.Gamma r := by
      simpa only [atom, neg_mul] using! h'
    _ = _ := by
      have hb : ((n+1 : ℕ) : ℝ)+1 = (n : ℝ)+2 := by push_cast; ring
      rw [weight, hb]
      ring

private theorem moment_density (N : ℕ) (r x : ℝ) :
    x^(r-1) * finiteMobiusLaplacePencil N x * Real.exp (-x) =
      ∑ n ∈ range N, shiftedMobiusRealCoefficient n * atom r n x := by
  unfold finiteMobiusLaplacePencil finiteRealLaplacePencil
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  have he : Real.exp (-((n+1 : ℕ) : ℝ)*x) * Real.exp (-x) =
      Real.exp (-(((n : ℝ)+2)*x)) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = shiftedMobiusRealCoefficient n *
        (x^(r-1) * (Real.exp (-((n+1 : ℕ) : ℝ)*x) * Real.exp (-x))) := by ring
    _ = _ := by rw [he]; rfl

private theorem moment_integrable (N : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => x^(r-1) * finiteMobiusLaplacePencil N x * Real.exp (-x))
      (Ioi 0) := by
  simp_rw [moment_density]
  exact integrable_finsetSum _ (fun n _ => (atom_integrable hr n).const_mul _)

/-- Exact moment against the first source atom, retaining the full integer section. -/
theorem moment_integral (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (∫ x in Ioi (0 : ℝ), x^(r-1) * finiteMobiusLaplacePencil N x * Real.exp (-x)) =
      Real.Gamma r * shiftedMoment N r := by
  simp_rw [moment_density]
  rw [integral_finsetSum _ (fun n _ => (atom_integrable hr n).const_mul _)]
  simp_rw [integral_const_mul, atom_integral hr]
  rw [shiftedMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Pairing of the original finite source with its complete renewal complement. -/
def renewalPairing (N : ℕ) (r : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), x^(r-1) * finiteMobiusLaplacePencil N x *
    (Real.exp (-x) - finiteMobiusLaplacePencil N x)

theorem renewalPairing_eq (N : ℕ) {r : ℝ} (hr : 0 < r) :
    renewalPairing N r = Real.Gamma r * shiftedMoment N r - finiteMobiusGammaHankelEnergy N r := by
  have he (x : ℝ) : x^(r-1) * finiteMobiusLaplacePencil N x *
      (Real.exp (-x) - finiteMobiusLaplacePencil N x) =
      x^(r-1) * finiteMobiusLaplacePencil N x * Real.exp (-x) -
        x^(r-1) * finiteMobiusLaplacePencil N x ^ 2 := by ring
  simp only [renewalPairing, he]
  have hsquare : IntegrableOn (fun x : ℝ => x^(r-1) * finiteMobiusLaplacePencil N x ^ 2)
      (Ioi 0) := integrableOn_finiteRealLaplacePencil_sq shiftedMobiusRealCoefficient N hr
  rw [integral_sub (moment_integrable N hr) hsquare,
    moment_integral N hr, integral_finiteMobiusLaplacePencil_sq N hr]

/-- The complete renewal feedback is eventually strictly negative on a nonempty
interval of energy orders immediately above one. -/
theorem eventually_renewalPairing_negative :
    ∃ ε > 0, ∀ r : ℝ, 1 < r → r < 1+ε →
      ∀ᶠ N : ℕ in atTop, renewalPairing N r < -(Real.Gamma r / 80) := by
  obtain ⟨ε,hε,hm⟩ := eventually_shiftedMoment_negative
  refine ⟨ε,hε,fun r hr hre => ?_⟩
  filter_upwards [hm r hr hre] with N hN
  have hr0 : 0 < r := by linarith
  have hg := Real.Gamma_pos_of_pos hr0
  have hmul := mul_lt_mul_of_pos_left hN hg
  have hE := finiteMobiusGammaHankelEnergy_nonneg N hr0
  rw [renewalPairing_eq N hr0]
  linarith

end MobiusRenewalEnergy
end RHTower
