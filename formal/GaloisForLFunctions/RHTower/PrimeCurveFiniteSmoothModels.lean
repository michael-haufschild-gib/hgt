import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Finite smoothness models of the actual prime curve

For every finite order `k`, an explicit real function on `ell²(primes)` is `C^k`
on a fixed ball about zero and agrees with `log |zeta(sigma)|` on the actual
prime curve `(p^(-sigma))_p` for every real `sigma > 1`.

The construction retains the finite Euler head `p <= 2^k`. Its remaining tail
is a series of one-sided real powers of the coordinate at the prime 2. Every
tail exponent exceeds `k`; all tail jets through order `k` vanish at zero.
Uniform derivative bounds are proved from a summable exponential majorant.

`exists_finiteSmoothGerm` is the unconditional existence result. The models
depend on `k`; this file supplies no common smooth or holomorphic germ and no
Kummer continuation or zero-free half-strip certificate. The complementary
smooth-germ obstruction and sharp derivative-norm claim are separate work.
-/

open Filter Set Topology

namespace RHTower.PrimeCurveModel

noncomputable def positivePower (a x : ℝ) : ℝ := (max x 0) ^ a

theorem positivePower_of_pos {a x : ℝ} (hx : 0 < x) :
    positivePower a x = x ^ a := by
  simp [positivePower, max_eq_left hx.le]

theorem positivePower_of_nonpos {a x : ℝ} (ha : 0 < a) (hx : x ≤ 0) :
    positivePower a x = 0 := by
  simp [positivePower, max_eq_right hx, Real.zero_rpow ha.ne']

theorem continuous_positivePower {a : ℝ} (ha : 0 ≤ a) :
    Continuous (positivePower a) :=
  (Real.continuous_rpow_const ha).comp (continuous_id.max continuous_const)

theorem hasDerivAt_positivePower {a x : ℝ} (ha : 1 < a) :
    HasDerivAt (positivePower a) (a * positivePower (a - 1) x) x := by
  have hne : ∀ y : ℝ, y ≠ 0 →
      HasDerivAt (positivePower a) (a * positivePower (a - 1) y) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hy | hy
    · have heq : positivePower a =ᶠ[𝓝 y] (fun _ => 0) := by
        filter_upwards [eventually_lt_nhds hy] with z hz
        exact positivePower_of_nonpos (by linarith) hz.le
      simpa [positivePower_of_nonpos (by linarith : 0 < a - 1) hy.le]
        using (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq heq
    · have heq : positivePower a =ᶠ[𝓝 y] (fun z => z ^ a) := by
        filter_upwards [eventually_gt_nhds hy] with z hz
        exact positivePower_of_pos hz
      simpa [positivePower_of_pos hy] using
        (Real.hasDerivAt_rpow_const (Or.inl hy.ne')).congr_of_eventuallyEq heq
  by_cases hx : x = 0
  · subst x
    exact hasDerivAt_of_hasDerivAt_of_ne hne
      (continuous_positivePower (by linarith)).continuousAt
      (continuous_const.mul (continuous_positivePower (by linarith))).continuousAt
  · exact hne x hx

theorem contDiffOn_of_jets {s : Set ℝ} {k : ℕ} (F : ℕ → ℝ → ℝ)
    (hs : IsOpen s)
    (hc : ∀ j ≤ k, ContinuousOn (F j) s)
    (hd : ∀ j < k, ∀ x ∈ s, HasDerivAt (F j) (F (j + 1) x) x) :
    ContDiffOn ℝ k (F 0) s := by
  induction k generalizing F with
  | zero => exact contDiffOn_zero.mpr (hc 0 le_rfl)
  | succ k ih =>
    rw [Nat.cast_add_one, contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hd 0 (Nat.zero_lt_succ k) x hx).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    have hshift : ContDiffOn ℝ k (F 1) s :=
      ih (fun j => F (j + 1)) (fun j hj => hc (j + 1) (Nat.succ_le_succ hj))
        (fun j hj x hx => hd (j + 1) (Nat.succ_lt_succ hj) x hx)
    exact hshift.congr (fun x hx => (hd 0 (Nat.zero_lt_succ k) x hx).deriv)

theorem contDiffOn_tsum_of_jets {ι : Type*} {s : Set ℝ} {k : ℕ}
    (F : ℕ → ι → ℝ → ℝ) (u : ℕ → ι → ℝ)
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hc : ∀ j ≤ k, ∀ i, ContinuousOn (F j i) s)
    (hu : ∀ j ≤ k, Summable (u j))
    (hb : ∀ j ≤ k, ∀ i x, x ∈ s → ‖F j i x‖ ≤ u j i)
    (hd : ∀ j < k, ∀ i x, x ∈ s → HasDerivAt (F j i) (F (j + 1) i x) x) :
    ContDiffOn ℝ k (fun x => ∑' i, F 0 i x) s := by
  apply contDiffOn_of_jets (fun j x => ∑' i, F j i x) hs
  · intro j hj
    exact continuousOn_tsum (hc j hj) (hu j hj) (hb j hj)
  · intro j hj x hx
    exact hasDerivAt_tsum_of_isPreconnected (hu (j + 1) hj) hs hconn
      (hd j hj) (hb (j + 1) hj) hx
      (.of_norm_bounded (hu j hj.le) (fun i => hb j hj.le i x hx)) hx

noncomputable def powerJetCoefficient (a : ℝ) (j : ℕ) : ℝ :=
  ∏ l ∈ Finset.range j, (a - l)

noncomputable def positivePowerJet (a : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  powerJetCoefficient a j * positivePower (a - j) x

@[simp] theorem powerJetCoefficient_zero (a : ℝ) : powerJetCoefficient a 0 = 1 := by
  simp [powerJetCoefficient]

theorem powerJetCoefficient_succ (a : ℝ) (j : ℕ) :
    powerJetCoefficient a (j + 1) = powerJetCoefficient a j * (a - j) := by
  exact Finset.prod_range_succ _ _

@[simp] theorem positivePowerJet_zero (a x : ℝ) :
    positivePowerJet a 0 x = positivePower a x := by
  simp [positivePowerJet]

theorem hasDerivAt_positivePowerJet {a : ℝ} {j : ℕ} (ha : (j : ℝ) + 1 < a) (x : ℝ) :
    HasDerivAt (positivePowerJet a j) (positivePowerJet a (j + 1) x) x := by
  unfold positivePowerJet
  have h := (hasDerivAt_positivePower (a := a - j) (x := x) (by linarith)).const_mul
    (powerJetCoefficient a j)
  simpa only [powerJetCoefficient_succ, Nat.cast_add, Nat.cast_one,
    sub_add_eq_sub_sub, mul_assoc] using h

theorem positivePowerJet_at_zero {a : ℝ} {j : ℕ} (ha : (j : ℝ) < a) :
    positivePowerJet a j 0 = 0 := by
  rw [positivePowerJet, positivePower_of_nonpos (by linarith : 0 < a - j) le_rfl, mul_zero]

theorem powerJetCoefficient_nonneg {a : ℝ} {j : ℕ} (ha : (j : ℝ) ≤ a) :
    0 ≤ powerJetCoefficient a j := by
  apply Finset.prod_nonneg
  intro l hl
  have hlj : (l : ℝ) < j := by exact_mod_cast Finset.mem_range.mp hl
  linarith

theorem powerJetCoefficient_le {a : ℝ} {j : ℕ} (ha : (j : ℝ) ≤ a) :
    powerJetCoefficient a j ≤ a ^ j := by
  have hprod : (∏ l ∈ Finset.range j, (a - l)) ≤ ∏ _l ∈ Finset.range j, a := by
    apply Finset.prod_le_prod
    · intro l hl
      have hlj : (l : ℝ) < j := by exact_mod_cast Finset.mem_range.mp hl
      linarith
    · intro l _
      exact sub_le_self _ (Nat.cast_nonneg l)
  simpa [powerJetCoefficient] using hprod

theorem norm_positivePowerJet_le {a ε x : ℝ} {j : ℕ}
    (ha : (j : ℝ) ≤ a) (hε : 0 ≤ ε) (hx : x ≤ ε) :
    ‖positivePowerJet a j x‖ ≤ a ^ j * ε ^ (a - j) := by
  rw [positivePowerJet, positivePower, norm_mul, Real.norm_of_nonneg (powerJetCoefficient_nonneg ha),
    Real.norm_of_nonneg (Real.rpow_nonneg (le_max_right x 0) _)]
  exact mul_le_mul (powerJetCoefficient_le ha)
    (Real.rpow_le_rpow (le_max_right x 0) (max_le hx hε) (sub_nonneg.mpr ha))
    (Real.rpow_nonneg (le_max_right x 0) _) (pow_nonneg ((Nat.cast_nonneg j).trans ha) _)

theorem contDiffOn_positivePowerSeries {ι : Type*} {k : ℕ} {ε : ℝ}
    (c a : ι → ℝ) (hε : 0 < ε) (ha : ∀ i, (k : ℝ) < a i)
    (hu : ∀ j ≤ k, Summable (fun i => ‖c i‖ * (a i) ^ j * ε ^ (a i - j))) :
    ContDiffOn ℝ k (fun x => ∑' i, c i * positivePower (a i) x) (Ioo (-ε) ε) := by
  let F : ℕ → ι → ℝ → ℝ := fun j i x => c i * positivePowerJet (a i) j x
  let u : ℕ → ι → ℝ := fun j i => ‖c i‖ * (a i) ^ j * ε ^ (a i - j)
  have hja : ∀ j ≤ k, ∀ i, (j : ℝ) < a i := by
    intro j hj i
    exact lt_of_le_of_lt (by exact_mod_cast hj) (ha i)
  have hc : ∀ j ≤ k, ∀ i, ContinuousOn (F j i) (Ioo (-ε) ε) := by
    intro j hj i
    exact (continuous_const.mul (continuous_const.mul
      (continuous_positivePower (by linarith [hja j hj i])))).continuousOn
  have hb : ∀ j ≤ k, ∀ i x, x ∈ Ioo (-ε) ε → ‖F j i x‖ ≤ u j i := by
    intro j hj i x hx
    simpa only [F, u, norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (norm_positivePowerJet_le (hja j hj i).le hε.le hx.2.le)
        (norm_nonneg (c i))
  have hd : ∀ j < k, ∀ i x, x ∈ Ioo (-ε) ε →
      HasDerivAt (F j i) (F (j + 1) i x) x := by
    intro j hj i x _
    have h : (j : ℝ) + 1 < a i := by
      exact_mod_cast hja (j + 1) hj i
    exact (hasDerivAt_positivePowerJet h x).const_mul (c i)
  simpa only [F, positivePowerJet_zero] using
    contDiffOn_tsum_of_jets F u isOpen_Ioo isPreconnected_Ioo hc hu hb hd

theorem iteratedDeriv_eq_of_jets {s : Set ℝ} {k : ℕ} (F : ℕ → ℝ → ℝ)
    (hs : IsOpen s)
    (hd : ∀ j < k, ∀ x ∈ s, HasDerivAt (F j) (F (j + 1) x) x) :
    ∀ j ≤ k, ∀ x ∈ s, iteratedDeriv j (F 0) x = F j x := by
  intro j hj
  induction j with
  | zero => simp
  | succ j ih =>
    intro x hx
    have heq : iteratedDeriv j (F 0) =ᶠ[𝓝 x] F j := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact ih (Nat.le_of_succ_le hj) y hy
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (hd j hj x hx).deriv

theorem power_jet_bound_by_exponential {a β : ℝ} (ha : 0 ≤ a) (j : ℕ) :
    a ^ j * (Real.exp (-(β + 1))) ^ (a - j) ≤
      (j.factorial : ℝ) * Real.exp ((β + 1) * j) * Real.exp (-β * a) := by
  have hp : a ^ j ≤ Real.exp a * (j.factorial : ℝ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < j.factorial)).mp
      (Real.pow_div_factorial_le_exp a ha j)
  calc
    a ^ j * (Real.exp (-(β + 1))) ^ (a - j)
        ≤ (Real.exp a * (j.factorial : ℝ)) *
          (Real.exp (-(β + 1))) ^ (a - j) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (Real.exp_pos _).le _)
    _ = (j.factorial : ℝ) * Real.exp (a + (-(β + 1)) * (a - j)) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, Real.exp_add]
      ring
    _ = (j.factorial : ℝ) * Real.exp ((β + 1) * j + -β * a) := by
      congr 2
      ring
    _ = _ := by rw [Real.exp_add]; ring

theorem summable_positivePower_jet_weight {ι : Type*} {β : ℝ}
    (c a : ι → ℝ) (hai : ∀ i, 0 ≤ a i)
    (hs : Summable (fun i => ‖c i‖ * Real.exp (-β * a i))) (j : ℕ) :
    Summable (fun i => ‖c i‖ * (a i) ^ j * (Real.exp (-(β + 1))) ^ (a i - j)) := by
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (hai i) j))
      (Real.rpow_nonneg (Real.exp_pos _).le _))
    (fun i => ?_)
    (hs.mul_left ((j.factorial : ℝ) * Real.exp ((β + 1) * j)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left (power_jet_bound_by_exponential (β := β) (hai i) j) (norm_nonneg (c i))

theorem contDiffOn_positivePowerSeries_of_exponential {ι : Type*} {k : ℕ} {β : ℝ}
    (c a : ι → ℝ) (ha : ∀ i, (k : ℝ) < a i)
    (hs : Summable (fun i => ‖c i‖ * Real.exp (-β * a i))) :
    ContDiffOn ℝ k (fun x => ∑' i, c i * positivePower (a i) x)
      (Ioo (-Real.exp (-(β + 1))) (Real.exp (-(β + 1)))) := by
  apply contDiffOn_positivePowerSeries c a (Real.exp_pos _) ha
  exact fun j _ => summable_positivePower_jet_weight c a
    (fun i => (Nat.cast_nonneg k).trans (ha i).le) hs j

theorem iteratedDeriv_positivePowerSeries_zero {ι : Type*} {k : ℕ} {ε : ℝ}
    (c a : ι → ℝ) (hε : 0 < ε) (ha : ∀ i, (k : ℝ) < a i)
    (hu : ∀ j ≤ k, Summable (fun i => ‖c i‖ * (a i) ^ j * ε ^ (a i - j)))
    {j : ℕ} (hj : j ≤ k) :
    iteratedDeriv j (fun x => ∑' i, c i * positivePower (a i) x) 0 = 0 := by
  let F : ℕ → ℝ → ℝ := fun l x => ∑' i, c i * positivePowerJet (a i) l x
  have hla : ∀ l ≤ k, ∀ i, (l : ℝ) < a i := by
    intro l hl i
    exact lt_of_le_of_lt (by exact_mod_cast hl) (ha i)
  have hz : ∀ l ≤ k, ∀ i, c i * positivePowerJet (a i) l 0 = 0 := by
    intro l hl i
    rw [positivePowerJet_at_zero (hla l hl i), mul_zero]
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hd : ∀ l < k, ∀ x ∈ Ioo (-ε) ε, HasDerivAt (F l) (F (l + 1) x) x := by
    intro l hl x hx
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun i y => c i * positivePowerJet (a i) l y)
      (g' := fun i y => c i * positivePowerJet (a i) (l + 1) y)
      (hu (l + 1) hl) isOpen_Ioo
      isPreconnected_Ioo ?_ ?_ h0 ?_ hx
    · intro i y _
      have hal : (l : ℝ) + 1 < a i := by exact_mod_cast hla (l + 1) hl i
      exact (hasDerivAt_positivePowerJet hal y).const_mul (c i)
    · intro i y hy
      simpa only [norm_mul, mul_assoc] using
        mul_le_mul_of_nonneg_left
          (norm_positivePowerJet_le (hla (l + 1) hl i).le hε.le hy.2.le) (norm_nonneg (c i))
    · simp only [hz l hl.le]
      exact summable_zero
  have h := iteratedDeriv_eq_of_jets F isOpen_Ioo hd j hj 0 h0
  simpa only [F, positivePowerJet_zero, hz j hj, tsum_zero] using h

abbrev TailPrime (k : ℕ) := {p : ℕ // Nat.Prime p ∧ 2 ^ k < p}

noncomputable def primeTailExponent {k : ℕ} (i : TailPrime k × ℕ) : ℝ :=
  (i.2 + 1 : ℕ) * Real.log (i.1.val : ℝ) / Real.log 2

noncomputable def primeTailCoefficient {k : ℕ} (i : TailPrime k × ℕ) : ℝ :=
  ((i.2 + 1 : ℕ) : ℝ)⁻¹

noncomputable def primeTail (k : ℕ) (t : ℝ) : ℝ :=
  ∑' i : TailPrime k × ℕ, primeTailCoefficient i * positivePower (primeTailExponent i) t

theorem primeTailExponent_gt {k : ℕ} (i : TailPrime k × ℕ) :
    (k : ℝ) < primeTailExponent i := by
  have hp : 0 < (i.1.val : ℝ) := by exact_mod_cast i.1.property.1.pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (k : ℝ) * Real.log 2 < Real.log (i.1.val : ℝ) := by
    have h := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)
      (by exact_mod_cast i.1.property.2 : (2 : ℝ) ^ k < i.1.val)
    simpa only [Real.log_pow] using h
  have hbase : (k : ℝ) < Real.log (i.1.val : ℝ) / Real.log 2 :=
    (lt_div_iff₀ hlog2).mpr hlog
  have hnonneg : 0 ≤ Real.log (i.1.val : ℝ) / Real.log 2 :=
    (Nat.cast_nonneg k).trans hbase.le
  have hr : (1 : ℝ) ≤ (i.2 + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.2)
  exact hbase.trans_le (by
    unfold primeTailExponent
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left hnonneg hr)

theorem exponential_primeTail_weight {k : ℕ} (i : TailPrime k × ℕ) :
    Real.exp (-(2 * Real.log 2) * primeTailExponent i) =
      (((i.1.val : ℝ) ^ 2)⁻¹) ^ (i.2 + 1) := by
  have hp : 0 < (i.1.val : ℝ) := by exact_mod_cast i.1.property.1.pos
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hexp : Real.exp (-(2 : ℝ) * Real.log (i.1.val : ℝ)) =
      ((i.1.val : ℝ) ^ 2)⁻¹ := by
    rw [neg_mul, Real.exp_neg]
    congr 1
    simpa only [Real.exp_log hp, Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (i.1.val : ℝ)) 2
  rw [← hexp, ← Real.exp_nat_mul]
  congr 1
  unfold primeTailExponent
  field_simp

theorem summable_primeTail_exponential_weight (k : ℕ) :
    Summable (fun i : TailPrime k × ℕ =>
      ‖primeTailCoefficient i‖ * Real.exp (-(2 * Real.log 2) * primeTailExponent i)) := by
  have hs : Summable (fun p : TailPrime k => ((p.val : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < (2 : ℕ))).subtype _
  have hg : Summable (fun r : ℕ => (1 / 4 : ℝ) ^ r) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hprod := hs.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)
  apply Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hprod
  rw [exponential_primeTail_weight]
  have hp : (2 : ℝ) ≤ i.1.val := by exact_mod_cast i.1.property.1.two_le
  have hq : ((i.1.val : ℝ) ^ 2)⁻¹ ≤ (1 / 4 : ℝ) := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
      (by nlinarith : (4 : ℝ) ≤ (i.1.val : ℝ) ^ 2)
  have hc : ‖primeTailCoefficient i‖ ≤ 1 := by
    unfold primeTailCoefficient
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.2) : (1 : ℝ) ≤ (i.2 + 1 : ℕ))
  calc
    ‖primeTailCoefficient i‖ * (((i.1.val : ℝ) ^ 2)⁻¹) ^ (i.2 + 1)
        ≤ (((i.1.val : ℝ) ^ 2)⁻¹) ^ (i.2 + 1) :=
      mul_le_of_le_one_left (by positivity) hc
    _ = ((i.1.val : ℝ) ^ 2)⁻¹ * (((i.1.val : ℝ) ^ 2)⁻¹) ^ i.2 := by rw [pow_succ']
    _ ≤ ((i.1.val : ℝ) ^ 2)⁻¹ * (1 / 4 : ℝ) ^ i.2 := by
      gcongr

theorem contDiffOn_primeTail (k : ℕ) :
    ContDiffOn ℝ k (primeTail k)
      (Ioo (-Real.exp (-(2 * Real.log 2 + 1))) (Real.exp (-(2 * Real.log 2 + 1)))) :=
  contDiffOn_positivePowerSeries_of_exponential primeTailCoefficient primeTailExponent
    primeTailExponent_gt (summable_primeTail_exponential_weight k)

theorem iteratedDeriv_primeTail_zero (k : ℕ) {j : ℕ} (hj : j ≤ k) :
    iteratedDeriv j (primeTail k) 0 = 0 := by
  apply iteratedDeriv_positivePowerSeries_zero primeTailCoefficient primeTailExponent
    (Real.exp_pos (-(2 * Real.log 2 + 1))) primeTailExponent_gt
      (fun l _ => summable_positivePower_jet_weight primeTailCoefficient primeTailExponent
        (fun i => (Nat.cast_nonneg k).trans (primeTailExponent_gt i).le)
          (summable_primeTail_exponential_weight k) l) hj

theorem primeTail_nonpos (k : ℕ) {t : ℝ} (ht : t ≤ 0) : primeTail k t = 0 := by
  have hz : ∀ i : TailPrime k × ℕ,
      primeTailCoefficient i * positivePower (primeTailExponent i) t = 0 := by
    intro i
    rw [positivePower_of_nonpos
      (lt_of_le_of_lt (Nat.cast_nonneg k) (primeTailExponent_gt i)) ht, mul_zero]
  simp only [primeTail, hz, tsum_zero]

theorem primeTail_on_euler_curve (k : ℕ) (σ : ℝ) :
    primeTail k ((2 : ℝ) ^ (-σ)) =
      ∑' i : TailPrime k × ℕ,
        ((i.2 + 1 : ℕ) : ℝ)⁻¹ * (i.1.val : ℝ) ^ (-σ * (i.2 + 1 : ℕ)) := by
  apply tsum_congr
  intro i
  congr 1
  rw [positivePower_of_pos (Real.rpow_pos_of_pos (by norm_num) _),
    Real.rpow_def_of_pos (Real.rpow_pos_of_pos (by norm_num) _), Real.log_rpow (by norm_num),
    Real.rpow_def_of_pos (by exact_mod_cast i.1.property.1.pos)]
  congr 1
  unfold primeTailExponent
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp

abbrev PrimeHilbert := lp (fun _ : Nat.Primes => ℝ) 2

theorem primeCurve_memℓp {σ : ℝ} (hσ : 1 / 2 < σ) :
    Memℓp (fun p : Nat.Primes => (p.val : ℝ) ^ (-σ)) 2 := by
  have hs : Summable (fun p : Nat.Primes => (p.val : ℝ) ^ (-σ * 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -σ * 2 < -1)).subtype _
  apply memℓp_gen
  convert hs using 1
  funext p
  simp only [ENNReal.toReal_ofNat]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.val) _),
    ← Real.rpow_mul (Nat.cast_nonneg p.val)]

noncomputable def primeCurve (σ : ℝ) (hσ : 1 / 2 < σ) : PrimeHilbert :=
  ⟨fun p => (p.val : ℝ) ^ (-σ), primeCurve_memℓp hσ⟩

@[simp] theorem primeCurve_apply (σ : ℝ) (hσ : 1 / 2 < σ) (p : Nat.Primes) :
    primeCurve σ hσ p = (p.val : ℝ) ^ (-σ) := rfl

noncomputable def lowPrimeLog (k : ℕ) (x : PrimeHilbert) : ℝ :=
  ∑ n ∈ Finset.range (2 ^ k + 1), if hn : Nat.Prime n then
    -Real.log (1 - x ⟨n, hn⟩) else 0

noncomputable def finiteSmoothModel (k : ℕ) (x : PrimeHilbert) : ℝ :=
  lowPrimeLog k x + primeTail k (x ⟨2, Nat.prime_two⟩)

theorem contDiffAt_finiteSmoothModel (k : ℕ) :
    ContDiffAt ℝ k (finiteSmoothModel k) 0 := by
  have hcoord (p : Nat.Primes) : ContDiffAt ℝ k (fun x : PrimeHilbert => x p) 0 :=
    (lp.evalCLM ℝ (fun _ : Nat.Primes => ℝ) 2 p).contDiff.contDiffAt
  have hlow : ContDiffAt ℝ k (lowPrimeLog k) 0 := by
    apply ContDiffAt.sum
    intro n _
    by_cases hn : Nat.Prime n
    · simp only [dif_pos hn]
      exact ((contDiffAt_const.sub (hcoord ⟨n, hn⟩)).log (by
        change (1 : ℝ) - 0 ≠ 0
        norm_num)).neg
    · simp only [dif_neg hn]
      exact contDiffAt_const
  have ht : ContDiffAt ℝ k (primeTail k) 0 :=
    (contDiffOn_primeTail k).contDiffAt (isOpen_Ioo.mem_nhds
      ⟨neg_neg_of_pos (Real.exp_pos _), Real.exp_pos _⟩)
  have htail : ContDiffAt ℝ k (fun x : PrimeHilbert => primeTail k (x ⟨2, Nat.prime_two⟩)) 0 := by
    apply ContDiffAt.fun_comp 0 _ (hcoord ⟨2, Nat.prime_two⟩)
    change ContDiffAt ℝ k (primeTail k) 0
    exact ht
  exact hlow.add htail

theorem finiteSmoothModel_on_euler_curve (k : ℕ) (σ : ℝ) (hσ : 1 / 2 < σ) :
    finiteSmoothModel k (primeCurve σ hσ) =
      (∑ n ∈ Finset.range (2 ^ k + 1), if Nat.Prime n then
        -Real.log (1 - (n : ℝ) ^ (-σ)) else 0) +
      ∑' i : TailPrime k × ℕ,
        ((i.2 + 1 : ℕ) : ℝ)⁻¹ * (i.1.val : ℝ) ^ (-σ * (i.2 + 1 : ℕ)) := by
  unfold finiteSmoothModel lowPrimeLog
  simp only [primeCurve_apply, Nat.cast_ofNat, primeTail_on_euler_curve, dite_eq_ite]

theorem summable_neg_log_one_sub {ι : Type*} {f : ι → ℝ} (hf : Summable f) :
    Summable (fun i => -Real.log (1 - f i)) := by
  have hg : DifferentiableAt ℝ (fun x : ℝ => -Real.log (1 - x)) 0 := by
    exact ((differentiableAt_const (1 : ℝ)).sub differentiableAt_id).log (by norm_num) |>.neg
  have hO : (fun x : ℝ => -Real.log (1 - x)) =O[𝓝 0] id := by
    simpa only [sub_zero, Real.log_one, neg_zero] using! hg.isBigO_sub
  exact hO.comp_summable hf

theorem primePower_log_hasSum {p : ℕ} (hp : Nat.Prime p) {σ : ℝ} (hσ : 0 < σ) :
    HasSum (fun r : ℕ => ((r + 1 : ℕ) : ℝ)⁻¹ * (p : ℝ) ^ (-σ * (r + 1 : ℕ)))
      (-Real.log (1 - (p : ℝ) ^ (-σ))) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (p : ℝ) ^ (-σ)) (by
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hσ))
  convert h using 1
  funext r
  rw [Real.rpow_mul_natCast (Nat.cast_nonneg p), div_eq_mul_inv]
  push_cast
  ring

theorem primeTail_on_euler_curve_eq_log_tail (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    primeTail k ((2 : ℝ) ^ (-σ)) =
      ∑' p : TailPrime k, -Real.log (1 - (p.val : ℝ) ^ (-σ)) := by
  have hp := fun p : TailPrime k => primePower_log_hasSum p.property.1 (by linarith : 0 < σ)
  have hsumlog : Summable (fun p : TailPrime k => -Real.log (1 - (p.val : ℝ) ^ (-σ))) :=
    summable_neg_log_one_sub
      ((Real.summable_nat_rpow.mpr (by linarith : -σ < -1)).subtype _)
  have hs : Summable (fun i : TailPrime k × ℕ =>
      ((i.2 + 1 : ℕ) : ℝ)⁻¹ * (i.1.val : ℝ) ^ (-σ * (i.2 + 1 : ℕ))) := by
    apply (summable_prod_of_nonneg (fun i => by positivity)).mpr
    refine ⟨fun p => (hp p).summable, ?_⟩
    simpa only [(hp _).tsum_eq] using hsumlog
  rw [primeTail_on_euler_curve, hs.tsum_prod]
  exact tsum_congr (fun p => (hp p).tsum_eq)

noncomputable def realEulerLog (σ : ℝ) : ℝ :=
  ∑' n : ℕ, if Nat.Prime n then -Real.log (1 - (n : ℝ) ^ (-σ)) else 0

theorem finiteSmoothModel_eq_eulerLog (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    finiteSmoothModel k (primeCurve σ (by linarith)) = realEulerLog σ := by
  have hs : Summable (fun n : ℕ =>
      if Nat.Prime n then -Real.log (1 - (n : ℝ) ^ (-σ)) else 0) := by
    have h := (summable_neg_log_one_sub
      (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))).indicator {n : ℕ | Nat.Prime n}
    convert! h using 1
    funext n
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have htail : (∑' p : TailPrime k, -Real.log (1 - (p.val : ℝ) ^ (-σ))) =
      ∑' n : {n : ℕ // n ∉ Finset.range (2 ^ k + 1)},
        if Nat.Prime n.val then -Real.log (1 - (n.val : ℝ) ^ (-σ)) else 0 := by
    erw [tsum_subtype {n : ℕ | Nat.Prime n ∧ 2 ^ k < n}
      (fun n => -Real.log (1 - (n : ℝ) ^ (-σ))),
      tsum_subtype {n : ℕ | n ∉ Finset.range (2 ^ k + 1)}
        (fun n => if Nat.Prime n then -Real.log (1 - (n : ℝ) ^ (-σ)) else 0)]
    apply tsum_congr
    intro n
    by_cases hp : Nat.Prime n
    · have hn : ¬n < 2 ^ k + 1 ↔ 2 ^ k < n := by omega
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.mem_range, hp, true_and, if_true, hn]
    · simp [Set.indicator_apply, hp]
  unfold finiteSmoothModel lowPrimeLog realEulerLog
  simp only [primeCurve_apply, Nat.cast_ofNat, dite_eq_ite]
  rw [primeTail_on_euler_curve_eq_log_tail k hσ, htail]
  exact hs.sum_add_tsum_subtype_compl (Finset.range (2 ^ k + 1))

theorem realEulerLog_eq_primeLog (σ : ℝ) :
    realEulerLog σ = ∑' p : Nat.Primes, -Real.log (1 - (p.val : ℝ) ^ (-σ)) := by
  simpa only [realEulerLog, Set.indicator] using!
    (tsum_subtype {n : ℕ | Nat.Prime n} (fun n => -Real.log (1 - (n : ℝ) ^ (-σ)))).symm

theorem realEulerLog_eq_log_norm_zeta {σ : ℝ} (hσ : 1 < σ) :
    realEulerLog σ = Real.log ‖riemannZeta (σ : ℂ)‖ := by
  have hb : (realEulerLog σ : ℂ) =
      ∑' p : Nat.Primes, -Complex.log (1 - (p.val : ℂ) ^ (-(σ : ℂ))) := by
    rw [realEulerLog_eq_primeLog, Complex.ofReal_tsum]
    apply tsum_congr
    intro p
    have hp : 0 ≤ 1 - (p.val : ℝ) ^ (-σ) := by
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.property.one_lt : (1 : ℝ) < p.val) (by linarith : -σ < 0)
      linarith
    rw [Complex.ofReal_neg, Complex.ofReal_log hp, Complex.ofReal_sub, Complex.ofReal_one,
      Complex.ofReal_cpow (Nat.cast_nonneg p.val)]
    simp only [Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [← riemannZeta_eulerProduct_exp_log (by simpa using hσ), ← hb,
    Complex.norm_exp, Complex.ofReal_re, Real.log_exp]

theorem finiteSmoothModel_eq_log_norm_zeta (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    finiteSmoothModel k (primeCurve σ (by linarith)) = Real.log ‖riemannZeta (σ : ℂ)‖ := by
  rw [finiteSmoothModel_eq_eulerLog k hσ, realEulerLog_eq_log_norm_zeta hσ]

theorem exists_finiteSmoothModel (k : ℕ) :
    ∃ G : PrimeHilbert → ℝ, ContDiffAt ℝ k G 0 ∧
      ∀ σ : ℝ, ∀ hσ : 1 < σ,
        G (primeCurve σ (by linarith)) = Real.log ‖riemannZeta (σ : ℂ)‖ :=
  ⟨finiteSmoothModel k, contDiffAt_finiteSmoothModel k,
    fun _ hσ => finiteSmoothModel_eq_log_norm_zeta k hσ⟩

noncomputable def modelRadius : ℝ := min (Real.exp (-(2 * Real.log 2 + 1))) 1

theorem modelRadius_pos : 0 < modelRadius := lt_min (Real.exp_pos _) zero_lt_one

theorem contDiffOn_finiteSmoothModel (k : ℕ) :
    ContDiffOn ℝ k (finiteSmoothModel k) (Metric.ball 0 modelRadius) := by
  have hcoord (p : Nat.Primes) :
      ContDiffOn ℝ k (fun x : PrimeHilbert => x p) (Metric.ball 0 modelRadius) :=
    (lp.evalCLM ℝ (fun _ : Nat.Primes => ℝ) 2 p).contDiff.contDiffOn
  have hbound (x : PrimeHilbert) (hx : x ∈ Metric.ball 0 modelRadius) (p : Nat.Primes) :
      |x p| < modelRadius := by
    have hx' : ‖x‖ < modelRadius := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact (lp.norm_apply_le_norm (by norm_num) x p).trans_lt hx'
  have hlow : ContDiffOn ℝ k (lowPrimeLog k) (Metric.ball 0 modelRadius) := by
    apply ContDiffOn.sum
    intro n _
    by_cases hn : Nat.Prime n
    · simp only [dif_pos hn]
      apply ContDiffOn.neg
      apply (contDiffOn_const.sub (hcoord ⟨n, hn⟩)).log
      intro x hx
      have hlt := (le_abs_self (x ⟨n, hn⟩)).trans_lt (hbound x hx ⟨n, hn⟩)
      have hr : modelRadius ≤ 1 := min_le_right _ _
      linarith
    · simp only [dif_neg hn]
      exact contDiffOn_const
  have ht : ContDiffOn ℝ k (fun x : PrimeHilbert => primeTail k (x ⟨2, Nat.prime_two⟩))
      (Metric.ball 0 modelRadius) := by
    exact (contDiffOn_primeTail k).comp (hcoord ⟨2, Nat.prime_two⟩) (fun x hx =>
      abs_lt.mp ((hbound x hx ⟨2, Nat.prime_two⟩).trans_le (min_le_left _ _)))
  exact hlow.add ht

theorem exists_finiteSmoothGerm (k : ℕ) :
    ∃ G : PrimeHilbert → ℝ, ∃ ε : ℝ, 0 < ε ∧
      ContDiffOn ℝ k G (Metric.ball 0 ε) ∧
      ∀ σ : ℝ, ∀ hσ : 1 < σ,
        G (primeCurve σ (by linarith)) = Real.log ‖riemannZeta (σ : ℂ)‖ :=
  ⟨finiteSmoothModel k, modelRadius, modelRadius_pos, contDiffOn_finiteSmoothModel k,
    fun _ hσ => finiteSmoothModel_eq_log_norm_zeta k hσ⟩

end RHTower.PrimeCurveModel
