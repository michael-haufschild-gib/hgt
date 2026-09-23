import GaloisForLFunctions.RHTower.PrimeArchThetaAtomMoments

/-!
# Dominant first-atom control for theta-cusp moments

The positive theta-cusp source is uniformly dominated by its first integer atom.  The exact
polynomial comparison gives a relative weight

`2 n^(4 : ℕ) exp (-π (n^(2 : ℕ) - 1))`

for the `n`th atom.  An elementary geometric estimate proves that the complete `n ≥ 2` tail has
total relative weight at most `8 / 2997`.  Consequently every even raw moment of the full source
is trapped between the first-atom moment and `3005 / 2997` times that moment.

The final declarations transfer two explicit first-atom inequalities to the already formalized
linear-polynomial prime--Gamma Hankel criterion.  No numerical approximation, zero-location
assumption, or Riemann-hypothesis assumption enters the tail bound.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

theorem thetaCuspSourceTerm_le_first
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n ≤
      (2 * (n : ℝ) ^ (4 : ℕ) *
        Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1))) *
          thetaCuspSourceTerm x 1 := by
  let u : ℝ := Real.exp x
  have hu : 1 ≤ u := by
    dsimp [u]
    simpa using Real.exp_le_exp.mpr hx
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnSq : 1 ≤ (n : ℝ) ^ (2 : ℕ) := by nlinarith
  have huSq : 1 ≤ u ^ (2 : ℕ) := by nlinarith [sq_nonneg u]
  have hprod : 0 ≤ ((n : ℝ) ^ (2 : ℕ) - 1) * (u ^ (2 : ℕ) - 1) :=
    mul_nonneg (sub_nonneg.mpr hnSq) (sub_nonneg.mpr huSq)
  have hexponent :
      -Real.pi * ((n : ℝ) * u) ^ (2 : ℕ) ≤
        -Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) + (-Real.pi * u ^ (2 : ℕ)) := by
    nlinarith [Real.pi_pos]
  have hgauss :
      Real.exp (-Real.pi * ((n : ℝ) * u) ^ (2 : ℕ)) ≤
        Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1)) *
          Real.exp (-Real.pi * u ^ (2 : ℕ)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hexponent
  have hpoly_u :
      0 ≤ 2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ)) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ (2 : ℕ) - 3 := by
      nlinarith [Real.pi_gt_three]
    rw [show 2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ) =
      u ^ (2 : ℕ) * (2 * Real.pi * u ^ (2 : ℕ) - 3) by ring]
    positivity
  have hpoly_nu :
      0 ≤ 2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ (4 : ℕ) -
          3 * ((n : ℝ) * u) ^ (2 : ℕ)) := by
    have hnu : 1 ≤ (n : ℝ) * u := by nlinarith [Real.exp_pos x]
    have hnuSq : 1 ≤ ((n : ℝ) * u) ^ (2 : ℕ) := by nlinarith
    have hcore : 0 ≤ 2 * Real.pi * ((n : ℝ) * u) ^ (2 : ℕ) - 3 := by
      nlinarith [Real.pi_gt_three]
    rw [show 2 * Real.pi * ((n : ℝ) * u) ^ (4 : ℕ) -
        3 * ((n : ℝ) * u) ^ (2 : ℕ) =
      ((n : ℝ) * u) ^ (2 : ℕ) *
        (2 * Real.pi * ((n : ℝ) * u) ^ (2 : ℕ) - 3) by ring]
    positivity
  have hpolyUpper :
      2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * u) ^ (4 : ℕ) -
            3 * ((n : ℝ) * u) ^ (2 : ℕ)) ≤
        2 * (n : ℝ) ^ (4 : ℕ) *
          (2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ))) := by
    have hcore : 0 ≤ 2 * Real.pi * u ^ (2 : ℕ) - 6 := by
      nlinarith [Real.pi_gt_three]
    have hbracket :
        0 ≤ (n : ℝ) ^ (2 : ℕ) * (2 * Real.pi * u ^ (2 : ℕ) - 6) + 3 := by
      positivity
    have hid :
        2 * (n : ℝ) ^ (4 : ℕ) *
              (2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ))) -
            2 * Real.pi *
              (2 * Real.pi * ((n : ℝ) * u) ^ (4 : ℕ) -
                3 * ((n : ℝ) * u) ^ (2 : ℕ)) =
          2 * Real.pi * (n : ℝ) ^ (2 : ℕ) * u ^ (2 : ℕ) *
            ((n : ℝ) ^ (2 : ℕ) * (2 * Real.pi * u ^ (2 : ℕ) - 6) + 3) := by
      ring
    apply sub_nonneg.mp
    rw [hid]
    positivity
  unfold thetaCuspSourceTerm thetaCuspSeed
  simp only [Nat.cast_one, one_mul]
  change Real.exp (x / 2) *
      (2 * Real.pi *
        (2 * Real.pi * ((n : ℝ) * u) ^ (4 : ℕ) -
          3 * ((n : ℝ) * u) ^ (2 : ℕ)) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ (2 : ℕ))) ≤ _
  change _ ≤ (2 * (n : ℝ) ^ (4 : ℕ) *
      Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1))) *
        (Real.exp (x / 2) *
          (2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ)) *
            Real.exp (-Real.pi * u ^ (2 : ℕ))))
  calc
    _ ≤ Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ (4 : ℕ) *
          (2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ)))) *
            Real.exp (-Real.pi * ((n : ℝ) * u) ^ (2 : ℕ))) := by
      gcongr
    _ ≤ Real.exp (x / 2) *
        ((2 * (n : ℝ) ^ (4 : ℕ) *
          (2 * Real.pi * (2 * Real.pi * u ^ (4 : ℕ) - 3 * u ^ (2 : ℕ)))) *
            (Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1)) *
              Real.exp (-Real.pi * u ^ (2 : ℕ)))) := by
      gcongr
    _ = _ := by ring

/-- The universal Gaussian weight controlling the `n`th source atom by the first. -/
def thetaCuspSourceAtomDominationWeight (n : ℕ) : ℝ :=
  2 * (n : ℝ) ^ (4 : ℕ) * Real.exp (-Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1))

theorem thetaCuspSourceAtomDominationWeight_nonneg (n : ℕ) :
    0 ≤ thetaCuspSourceAtomDominationWeight n := by
  unfold thetaCuspSourceAtomDominationWeight
  positivity

theorem summable_thetaCuspSourceAtomDominationWeight :
    Summable thetaCuspSourceAtomDominationWeight := by
  have hs := (summable_pow_mul_exp_neg_nat_sq 4 Real.pi_pos).mul_left
    (2 * Real.exp Real.pi)
  refine hs.congr (fun n => ?_)
  unfold thetaCuspSourceAtomDominationWeight
  rw [show -Real.pi * ((n : ℝ) ^ (2 : ℕ) - 1) =
    Real.pi + (-Real.pi * (n : ℝ) ^ (2 : ℕ)) by ring, Real.exp_add]
  ring

/-- The total relative higher-atom weight. -/
def thetaCuspHigherAtomDominationWeight : ℝ :=
  ∑' k : ℕ, thetaCuspSourceAtomDominationWeight (k + 2)

theorem thetaCuspHigherAtomDominationWeight_nonneg :
    0 ≤ thetaCuspHigherAtomDominationWeight := by
  unfold thetaCuspHigherAtomDominationWeight
  exact tsum_nonneg fun _ => thetaCuspSourceAtomDominationWeight_nonneg _

theorem thetaCuspFullSource_sub_first_le
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 ≤
      thetaCuspHigherAtomDominationWeight * thetaCuspSourceTerm x 1 := by
  have hs := summable_thetaCuspSourceTerm x
  have htail : Summable (fun k : ℕ => thetaCuspSourceTerm x (k + 2)) :=
    hs.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hweight : Summable
      (fun k : ℕ => thetaCuspSourceAtomDominationWeight (k + 2)) :=
    summable_thetaCuspSourceAtomDominationWeight.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hweighted : Summable (fun k : ℕ =>
      thetaCuspSourceAtomDominationWeight (k + 2) *
        thetaCuspSourceTerm x 1) := hweight.mul_right _
  have hhead :
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
        thetaCuspSourceTerm x 1 := by
    calc
      (∑ n ∈ Finset.range 2, thetaCuspSourceTerm x n) =
          thetaCuspSourceTerm x 0 + thetaCuspSourceTerm x 1 := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      _ = thetaCuspSourceTerm x 1 := by
        simp [thetaCuspSourceTerm, thetaCuspSeed]
  calc
    thetaCuspFullSource x - thetaCuspSourceTerm x 1 =
        ∑' k : ℕ, thetaCuspSourceTerm x (k + 2) := by
      rw [thetaCuspFullSource, ← hs.sum_add_tsum_nat_add 2, hhead]
      ring
    _ ≤ ∑' k : ℕ,
        thetaCuspSourceAtomDominationWeight (k + 2) *
          thetaCuspSourceTerm x 1 := by
      exact Summable.tsum_le_tsum (fun k => by
        exact thetaCuspSourceTerm_le_first
          (n := k + 2) (by omega) hx)
        htail hweighted
    _ = thetaCuspHigherAtomDominationWeight *
        thetaCuspSourceTerm x 1 := by
      rw [thetaCuspHigherAtomDominationWeight]
      exact Summable.tsum_mul_right _ hweight

theorem integrableOn_pow_mul_thetaCuspSourceTerm
    (j n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * j) * thetaCuspSourceTerm x n)
      (Ioi 0) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x n
  let g : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspFullSource x
  have hg : Integrable g mu := integrableOn_thetaCuspRawMoment (2 * j)
  apply Integrable.mono hg
  · exact ((by
      dsimp [f]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous f)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
    · have hterm : thetaCuspSourceTerm x n ≤ thetaCuspFullSource x := by
        rw [thetaCuspFullSource]
        exact (summable_thetaCuspSourceTerm x).le_tsum n
          (fun k _ => thetaCuspSourceTerm_nonneg_of_pos hx k)
      exact mul_le_mul_of_nonneg_left hterm (pow_nonneg hx.le _)
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspFullSource_pos_of_pos hx).le
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspSourceTerm_nonneg_of_pos hx n)

theorem thetaCuspHigherAtomRawEvenMoment_le_first
    (j : ℕ) :
    thetaCuspHigherAtomRawEvenMoment j ≤
      thetaCuspHigherAtomDominationWeight *
        thetaCuspAtomRawEvenMoment j 1 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspFullSource x
  let g : ℝ → ℝ := fun x => x ^ (2 * j) * thetaCuspSourceTerm x 1
  have hf : Integrable f mu := integrableOn_thetaCuspRawMoment (2 * j)
  have hg : Integrable g mu := integrableOn_pow_mul_thetaCuspSourceTerm j 1
  have hleft : Integrable (fun x => x ^ (2 * j) *
      (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) mu := by
    convert hf.sub hg using 1
    funext x
    dsimp [f, g]
    ring
  rw [thetaCuspHigherAtomRawEvenMoment, thetaCuspRawEvenMoment,
    thetaCuspAtomRawEvenMoment]
  change 2 * ∫ x, f x ∂mu - 2 * ∫ x, g x ∂mu ≤
    thetaCuspHigherAtomDominationWeight * (2 * ∫ x, g x ∂mu)
  rw [← mul_sub, ← integral_sub hf hg]
  rw [show (fun x => f x - g x) =
      (fun x => x ^ (2 * j) *
        (thetaCuspFullSource x - thetaCuspSourceTerm x 1)) by
    funext x
    dsimp [f, g]
    ring]
  rw [show thetaCuspHigherAtomDominationWeight *
      (2 * ∫ x, g x ∂mu) =
        2 * (thetaCuspHigherAtomDominationWeight *
          ∫ x, g x ∂mu) by ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← integral_const_mul]
  apply integral_mono_ae
  · exact hleft
  · exact hg.const_mul thetaCuspHigherAtomDominationWeight
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    calc
      x ^ (2 * j) *
          (thetaCuspFullSource x - thetaCuspSourceTerm x 1) ≤
        x ^ (2 * j) *
          (thetaCuspHigherAtomDominationWeight *
            thetaCuspSourceTerm x 1) :=
        mul_le_mul_of_nonneg_left
          (thetaCuspFullSource_sub_first_le hx.le)
          (pow_nonneg hx.le _)
      _ = thetaCuspHigherAtomDominationWeight * g x := by
        dsimp [g]
        ring

theorem thetaCusp_twelve_thousand_lt_exp_three_pi :
    (12000 : ℝ) < Real.exp (3 * Real.pi) := by
  have he1 : (1359 / 500 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h ⊢
    linarith
  have he9 : (1359 / 500 : ℝ) ^ (9 : ℕ) < Real.exp 9 := by
    rw [show (9 : ℝ) = (9 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  have hefrac0 := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 21 / 50 by norm_num) 3
  have hefrac :
      (1 + (21 : ℝ) / 50 + ((21 : ℝ) / 50) ^ (2 : ℕ) / 2) ≤
        Real.exp ((21 : ℝ) / 50) := by
    norm_num [Finset.sum_range_succ] at hefrac0 ⊢
    exact hefrac0
  calc
    (12000 : ℝ) < (1359 / 500 : ℝ) ^ (9 : ℕ) *
        (1 + (21 : ℝ) / 50 + ((21 : ℝ) / 50) ^ (2 : ℕ) / 2) := by norm_num
    _ < Real.exp 9 * Real.exp ((21 : ℝ) / 50) := by
      exact (mul_lt_mul_of_pos_right he9 (by norm_num)).trans_le
        (mul_le_mul_of_nonneg_left hefrac (Real.exp_pos 9).le)
    _ = Real.exp ((471 : ℝ) / 50) := by
      rw [← Real.exp_add]
      congr 1
      norm_num
    _ < Real.exp (3 * Real.pi) := by
      exact Real.exp_lt_exp.mpr (by nlinarith [Real.pi_gt_d2])

theorem thetaCusp_exp_neg_three_pi_lt :
    Real.exp (-3 * Real.pi) < (1 : ℝ) / 12000 := by
  rw [show -3 * Real.pi = -(3 * Real.pi) by ring, Real.exp_neg]
  simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num)
    thetaCusp_twelve_thousand_lt_exp_three_pi

theorem thetaCusp_sixteen_thousand_lt_exp_five_pi :
    (16000 : ℝ) < Real.exp (5 * Real.pi) := by
  have he15 : (16000 : ℝ) < Real.exp 15 := by
    have he1two : (2 : ℝ) < Real.exp 1 := by
      have h := Real.exp_one_gt_d9
      norm_num at h ⊢
      linarith
    calc
      (16000 : ℝ) < 2 ^ (15 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (15 : ℕ) := by
        exact pow_lt_pow_left₀ he1two (by norm_num) (by norm_num)
      _ = Real.exp 15 := by
        rw [show (15 : ℝ) = (15 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
  exact he15.trans (Real.exp_lt_exp.mpr (by nlinarith [Real.pi_gt_three]))

theorem thetaCusp_sixteen_mul_exp_neg_five_pi_lt :
    16 * Real.exp (-5 * Real.pi) < (1 : ℝ) / 1000 := by
  have hneg : Real.exp (-5 * Real.pi) < (1 : ℝ) / 16000 := by
    rw [show -5 * Real.pi = -(5 * Real.pi) by ring, Real.exp_neg]
    simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num)
      thetaCusp_sixteen_thousand_lt_exp_five_pi
  nlinarith

theorem thetaCusp_nat_add_two_le_two_pow_succ (k : ℕ) :
    k + 2 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) by ring]
      omega

theorem thetaCuspSourceAtomDominationWeight_add_two_le_geometric
    (k : ℕ) :
    thetaCuspSourceAtomDominationWeight (k + 2) ≤
      (1 / 375 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by
  have hnat := thetaCusp_nat_add_two_le_two_pow_succ k
  have hcast : ((k + 2 : ℕ) : ℝ) ≤ (2 ^ (k + 1) : ℕ) := by
    exact_mod_cast hnat
  have hpow : (((k + 2 : ℕ) : ℝ) ^ (4 : ℕ)) ≤
      16 * (16 : ℝ) ^ k := by
    calc
      (((k + 2 : ℕ) : ℝ) ^ (4 : ℕ)) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) ^ (4 : ℕ) := by
        gcongr
      _ = 16 * (16 : ℝ) ^ k := by
        push_cast
        calc
          ((2 : ℝ) ^ (k + 1)) ^ (4 : ℕ) =
              (2 : ℝ) ^ ((k + 1) * 4) := by rw [pow_mul]
          _ = (2 : ℝ) ^ (4 * (k + 1)) := by rw [Nat.mul_comm]
          _ = ((2 : ℝ) ^ (4 : ℕ)) ^ (k + 1) := by rw [pow_mul]
          _ = 16 * 16 ^ k := by rw [pow_succ']; norm_num
  have hsquare :
      (3 : ℝ) + 5 * k ≤ ((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) - 1 := by
    rcases k with _ | k
    · norm_num
    · push_cast
      nlinarith [sq_nonneg (k : ℝ)]
  have hexponent :
      -Real.pi * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) - 1) ≤
        -3 * Real.pi + (k : ℕ) * (-5 * Real.pi) := by
    nlinarith [Real.pi_pos]
  have hexp :
      Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) - 1)) ≤
        Real.exp (-3 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k := by
    calc
      _ ≤ Real.exp (-3 * Real.pi + (k : ℕ) * (-5 * Real.pi)) :=
        Real.exp_le_exp.mpr hexponent
      _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]
  have ha : Real.exp (-3 * Real.pi) ≤ (1 : ℝ) / 12000 :=
    thetaCusp_exp_neg_three_pi_lt.le
  have hr : 16 * Real.exp (-5 * Real.pi) ≤ (1 : ℝ) / 1000 :=
    thetaCusp_sixteen_mul_exp_neg_five_pi_lt.le
  unfold thetaCuspSourceAtomDominationWeight
  calc
    2 * (((k + 2 : ℕ) : ℝ) ^ (4 : ℕ)) *
        Real.exp (-Real.pi * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) - 1)) ≤
      2 * (16 * (16 : ℝ) ^ k) *
        (Real.exp (-3 * Real.pi) * (Real.exp (-5 * Real.pi)) ^ k) := by
      gcongr
    _ = 32 * Real.exp (-3 * Real.pi) *
        (16 * Real.exp (-5 * Real.pi)) ^ k := by ring
    _ ≤ 32 * ((1 : ℝ) / 12000) * ((1 / 1000 : ℝ) ^ k) := by
      gcongr
    _ = (1 / 375 : ℝ) * ((1 / 1000 : ℝ) ^ k) := by ring

theorem thetaCuspHigherAtomDominationWeight_le_geometric_rational :
    thetaCuspHigherAtomDominationWeight ≤ (8 : ℝ) / 2997 := by
  have hweight : Summable
      (fun k : ℕ => thetaCuspSourceAtomDominationWeight (k + 2)) :=
    summable_thetaCuspSourceAtomDominationWeight.comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hgeo : Summable (fun k : ℕ =>
      (1 / 375 : ℝ) * ((1 / 1000 : ℝ) ^ k)) :=
    (summable_geometric_of_norm_lt_one (by norm_num :
      ‖(1 / 1000 : ℝ)‖ < 1)).mul_left _
  calc
    thetaCuspHigherAtomDominationWeight =
        ∑' k : ℕ, thetaCuspSourceAtomDominationWeight (k + 2) := rfl
    _ ≤ ∑' k : ℕ, (1 / 375 : ℝ) * ((1 / 1000 : ℝ) ^ k) :=
      Summable.tsum_le_tsum
        thetaCuspSourceAtomDominationWeight_add_two_le_geometric
        hweight hgeo
    _ = (1 / 375 : ℝ) * (1 - (1 / 1000 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    _ = (8 : ℝ) / 2997 := by norm_num

theorem thetaCuspHigherAtomDominationWeight_le_one_div_three_hundred_seventy_four :
    thetaCuspHigherAtomDominationWeight ≤ (1 : ℝ) / 374 :=
  thetaCuspHigherAtomDominationWeight_le_geometric_rational.trans (by norm_num)

theorem thetaCuspHigherAtomDominationWeight_le_one_div_three_hundred :
    thetaCuspHigherAtomDominationWeight ≤ (1 : ℝ) / 300 :=
  thetaCuspHigherAtomDominationWeight_le_one_div_three_hundred_seventy_four.trans
    (by norm_num)

theorem thetaCuspRawEvenMoment_le_first_atom_factor (j : ℕ) :
    thetaCuspRawEvenMoment j ≤
      (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment j 1 := by
  rw [thetaCuspRawEvenMoment_eq_one_add_higher]
  calc
    thetaCuspAtomRawEvenMoment j 1 + thetaCuspHigherAtomRawEvenMoment j ≤
        thetaCuspAtomRawEvenMoment j 1 +
          thetaCuspHigherAtomDominationWeight *
            thetaCuspAtomRawEvenMoment j 1 :=
      add_le_add (le_refl _) (thetaCuspHigherAtomRawEvenMoment_le_first j)
    _ ≤ thetaCuspAtomRawEvenMoment j 1 +
        ((8 : ℝ) / 2997) * thetaCuspAtomRawEvenMoment j 1 := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_right
          thetaCuspHigherAtomDominationWeight_le_geometric_rational
          (thetaCuspAtomRawEvenMoment_nonneg j 1))
    _ = (3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment j 1 := by ring

theorem thetaCuspUpperAdjacentRatioSeparation_of_first_atom
    (hfirst :
      14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1) :
    ThetaCuspUpperAdjacentRatioSeparation := by
  rw [ThetaCuspUpperAdjacentRatioSeparation]
  have hm2 := thetaCuspRawEvenMoment_le_first_atom_factor 2
  have hm1 := thetaCuspAtomRawEvenMoment_one_le_raw 1
  have hm3 := thetaCuspAtomRawEvenMoment_one_le_raw 3
  have hm2non := thetaCuspRawEvenMoment_nonneg 2
  have hm1non := thetaCuspRawEvenMoment_nonneg 1
  have hm3non := thetaCuspRawEvenMoment_nonneg 3
  have hab2non := thetaCuspAtomRawEvenMoment_nonneg 2 1
  have hab1non := thetaCuspAtomRawEvenMoment_nonneg 1 1
  have hab3non := thetaCuspAtomRawEvenMoment_nonneg 3 1
  calc
    14 * thetaCuspRawEvenMoment 2 ^ (2 : ℕ) ≤
        14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) := by
      gcongr
    _ ≤ 9 * thetaCuspAtomRawEvenMoment 1 1 *
        thetaCuspAtomRawEvenMoment 3 1 := hfirst
    _ ≤ 9 * thetaCuspRawEvenMoment 1 * thetaCuspRawEvenMoment 3 := by
      gcongr

theorem thetaCuspRelaxedFourthMomentConcentration_of_first_atom
    (hfirst :
      16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ThetaCuspRelaxedFourthMomentConcentration := by
  rw [ThetaCuspRelaxedFourthMomentConcentration]
  have hm0 := thetaCuspRawEvenMoment_le_first_atom_factor 0
  have hm2 := thetaCuspRawEvenMoment_le_first_atom_factor 2
  have hm1 := thetaCuspAtomRawEvenMoment_one_le_raw 1
  have hm0non := thetaCuspRawEvenMoment_nonneg 0
  have hm2non := thetaCuspRawEvenMoment_nonneg 2
  have hab0non := thetaCuspAtomRawEvenMoment_nonneg 0 1
  have hab1non := thetaCuspAtomRawEvenMoment_nonneg 1 1
  have hab2non := thetaCuspAtomRawEvenMoment_nonneg 2 1
  calc
    16 * thetaCuspRawEvenMoment 0 * thetaCuspRawEvenMoment 2 ≤
        16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) := by
      gcongr
    _ ≤ 45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ) := hfirst
    _ ≤ 45 * thetaCuspRawEvenMoment 1 ^ (2 : ℕ) := by
      gcongr

theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom
    (hupper :
      14 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ^ (2 : ℕ) ≤
        9 * thetaCuspAtomRawEvenMoment 1 1 *
          thetaCuspAtomRawEvenMoment 3 1)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 0 1) *
          ((3005 / 2997 : ℝ) * thetaCuspAtomRawEvenMoment 2 1) ≤
        45 * thetaCuspAtomRawEvenMoment 1 1 ^ (2 : ℕ)) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re :=
  forall_primeArchSourceTraceHankel_linear_nonneg_of_ratioSplit
    (thetaCuspUpperAdjacentRatioSeparation_of_first_atom hupper)
    (thetaCuspRelaxedFourthMomentConcentration_of_first_atom hrelaxed)

end

end RHTower
