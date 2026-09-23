import GaloisForLFunctions.RHTower.Sieve.DampedCorrBound
import GaloisForLFunctions.RHTower.Sieve.RouteTContourRateBounds
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Prime-mass bounds for the damped Euler correction

The correction is bounded between the exponential of its prime mass and the
exponential of five times that mass. These comparisons give sufficient and
necessary budgets for preserving an exponential saving.

For all primes up to `N`, a finite Euler product gives the lower bound
`N ^ (1 - c)`. Along the Route T contour, the correction therefore overwhelms
the displayed stretched-exponential saving. This concerns the majorant, not
an estimate from below for the damped sum itself.
-/

open Filter Topology Finset

namespace RHTower.Sieve

private theorem correction_factor_mass_bounds {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 3 / 4) :
    Real.exp x ≤ (1+x)/(1-x) ∧ (1+x)/(1-x) ≤ Real.exp (5*x) := by
  have hd : 0 < 1-x := by linarith
  have hlow : 1-x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hexp : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  constructor
  · rw [le_div_iff₀ hd]
    have hmul := mul_le_mul_of_nonneg_left hlow (Real.exp_pos x).le
    nlinarith
  · have hnum : 1+x ≤ Real.exp x := by
      have := Real.add_one_le_exp x
      linarith
    have hden : 1/(1-x) ≤ Real.exp (4*x) := by
      rw [div_le_iff₀ hd]
      have := Real.add_one_le_exp (4*x)
      have hmul := mul_le_mul_of_nonneg_right this hd.le
      nlinarith
    calc (1+x)/(1-x) = (1+x)*(1/(1-x)) := by ring
      _ ≤ Real.exp x * Real.exp (4*x) :=
        mul_le_mul hnum hden (by positivity) (Real.exp_pos x).le
      _ = Real.exp (5*x) := by rw [← Real.exp_add]; congr 1; ring

/-- The Euler correction has exponential size in the sum of its local masses. -/
theorem dampedCorrBound_mass_bounds {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {c : ℝ} (hc : 1/2 ≤ c) :
    Real.exp (∑ p ∈ P, (p : ℝ)^(-c)) ≤ dampedCorrBound P c ∧
      dampedCorrBound P c ≤ Real.exp (5 * ∑ p ∈ P, (p : ℝ)^(-c)) := by
  have hfactor (p : ℕ) (hp : p ∈ P) :
      Real.exp ((p : ℝ)^(-c)) ≤ (1+(p : ℝ)^(-c))/(1-(p : ℝ)^(-c)) ∧
      (1+(p : ℝ)^(-c))/(1-(p : ℝ)^(-c)) ≤ Real.exp (5*(p : ℝ)^(-c)) := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hP p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hx : 0 < (p : ℝ)^(-c) := Real.rpow_pos_of_pos hp0 _
    have hsq : ((p : ℝ)^(-c))^(2 : ℕ) ≤ 1/2 := by
      rw [← Real.rpow_two, ← Real.rpow_mul hp0.le]
      calc (p : ℝ)^(-c*2) ≤ (p : ℝ)^(-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1/(p : ℝ) := by rw [Real.rpow_neg_one]; ring
        _ ≤ 1/2 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    exact correction_factor_mass_bounds hx.le (by nlinarith)
  constructor
  · rw [Real.exp_sum, dampedCorrBound]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le)
      (fun p hp => (hfactor p hp).1)
  · rw [dampedCorrBound, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact (Real.exp_pos _).le.trans (hfactor p hp).1
    · intro p hp
      exact (hfactor p hp).2


/-- The all-prime correction dominates the sum of the first `N` reciprocal powers. -/
theorem nat_rpow_le_dampedCorrBound_primesLE (N : ℕ) (hN : 1 ≤ N)
    {c : ℝ} (hc : 1/2 ≤ c) :
    (N : ℝ)^(1-c) ≤ dampedCorrBound (Nat.primesLE N) c := by
  classical
  let f : ℕ →* ℝ :=
    { toFun := fun n => (n : ℝ)^(-c)
      map_one' := by simp
      map_mul' := by
        intro a b
        simp only [Nat.cast_mul]
        exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b) }
  have hf (p : ℕ) (hp : p.Prime) : ‖f p‖ < 1 := by
    dsimp [f]
    rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have he := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := f) (fun {p} hp => hf p hp) (N+1)
  have hi := hasSum_subtype_iff_indicator.mp he.2
  have hsum : (∑ n ∈ Finset.Icc 1 N, (n : ℝ)^(-c)) ≤
      ∏ p ∈ (N+1).primesBelow, (1-f p)⁻¹ := by
    calc (∑ n ∈ Finset.Icc 1 N, (n : ℝ)^(-c)) =
        ∑ n ∈ Finset.Icc 1 N, ((N+1).smoothNumbers : Set ℕ).indicator f n := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnI := Finset.mem_Icc.mp hn
          have hs : n ∈ (N+1).smoothNumbers :=
            Nat.mem_smoothNumbers_iff_forall_le.mpr ⟨by omega, fun p hp _ _ => by omega⟩
          rw [Set.indicator_of_mem hs]
          rfl
      _ ≤ _ := sum_le_hasSum (Finset.Icc 1 N)
        (fun n _ => Set.indicator_nonneg (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _) n) hi
  have hprod : (∏ p ∈ (N+1).primesBelow, (1-f p)⁻¹) ≤
      dampedCorrBound (Nat.primesLE N) c := by
    rw [Nat.primesBelow_eq_primesLE_sub_one]
    simp only [Nat.add_sub_cancel]
    unfold dampedCorrBound
    apply Finset.prod_le_prod
    · intro p hp
      have hlt := rpow_neg_lt_one (Nat.prime_of_mem_primesLE hp).two_le hc
      dsimp [f]
      positivity
    · intro p hp
      have hlt := rpow_neg_lt_one (Nat.prime_of_mem_primesLE hp).two_le hc
      have hpos := Real.rpow_nonneg (Nat.cast_nonneg p) (-c)
      dsimp [f]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    (N : ℝ)^(1-c) = (N : ℝ)*(N : ℝ)^(-c) := by
      rw [sub_eq_add_neg, Real.rpow_add hN0, Real.rpow_one]
    _ = ∑ _n ∈ Finset.Icc 1 N, (N : ℝ)^(-c) := by simp
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (n : ℝ)^(-c) := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn1)
        (by exact_mod_cast hnN) (by linarith)
    _ ≤ dampedCorrBound (Nat.primesLE N) c := hsum.trans hprod


/-- A budget of five times the prime mass suffices to preserve a saving. -/
theorem dampedCorrBound_saving_of_mass_budget {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {c v r : ℝ} (hc : 1/2 ≤ c)
    (hbudget : 5 * ∑ p ∈ P, (p : ℝ)^(-c) ≤ v-r) :
    dampedCorrBound P c * Real.exp (-v) ≤ Real.exp (-r) := by
  calc
    dampedCorrBound P c * Real.exp (-v) ≤
        Real.exp (5 * ∑ p ∈ P, (p : ℝ)^(-c)) * Real.exp (-v) :=
      mul_le_mul_of_nonneg_right (dampedCorrBound_mass_bounds hP hc).2 (Real.exp_pos _).le
    _ = Real.exp (5 * ∑ p ∈ P, (p : ℝ)^(-c) - v) := by
      rw [← Real.exp_add]; congr 1
    _ ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)

/-- Preserving a saving requires a budget at least as large as the prime mass. -/
theorem mass_budget_of_dampedCorrBound_saving {P : Finset ℕ}
    (hP : ∀ p ∈ P, 2 ≤ p) {c v r : ℝ} (hc : 1/2 ≤ c)
    (hsaving : dampedCorrBound P c * Real.exp (-v) ≤ Real.exp (-r)) :
    (∑ p ∈ P, (p : ℝ)^(-c)) ≤ v-r := by
  have he : Real.exp ((∑ p ∈ P, (p : ℝ)^(-c))-v) ≤ Real.exp (-r) := by
    calc
      Real.exp ((∑ p ∈ P, (p : ℝ)^(-c))-v) =
          Real.exp (∑ p ∈ P, (p : ℝ)^(-c)) * Real.exp (-v) := by
        rw [← Real.exp_add]; congr 1
      _ ≤ dampedCorrBound P c * Real.exp (-v) :=
        mul_le_mul_of_nonneg_right (dampedCorrBound_mass_bounds hP hc).1 (Real.exp_pos _).le
      _ ≤ Real.exp (-r) := hsaving
  have h := Real.exp_le_exp.mp he
  linarith

/-- The all-prime correction overwhelms the contour saving uniformly in frequency. -/
theorem eventually_dampedCorrBound_primesLE_contour_saving_lower
    (A δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ τ : ℝ, |τ| ≤ N →
      Real.exp (9 * (Real.log (N : ℝ))^((1 : ℝ)/20)) ≤
        dampedCorrBound (Nat.primesLE N) (routeTContourLeft A δ (|τ|+N)) *
          Real.exp (-((Real.log (N : ℝ))^((1 : ℝ)/20))) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hdata := hnat.eventually (eventually_routeT_contour_rate_data A δ hδ)
  have hbase := hnat.eventually_ge_atTop routeTInverseBaseHeight
  filter_upwards [hdata, hbase, eventually_ge_atTop 1] with N hN hb hN1
  intro τ hτ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hshift := (hN (|τ|+N) (by linarith [abs_nonneg τ]) (by linarith)).1
  have hbound := nat_rpow_le_dampedCorrBound_primesLE N hN1
    (routeTContourLeft_ge_half A δ (|τ|+N))
  have he : (N : ℝ)^(1-routeTContourLeft A δ (|τ|+N)) =
      Real.exp (routeTContourShift A δ (|τ|+N) * Real.log N) := by
    rw [Real.rpow_def_of_pos hN0, routeTContourLeft]
    congr 1
    ring
  rw [he] at hbound
  calc
    Real.exp (9 * (Real.log (N : ℝ))^((1 : ℝ)/20)) ≤
        Real.exp (routeTContourShift A δ (|τ|+N) * Real.log N -
          (Real.log (N : ℝ))^((1 : ℝ)/20)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (routeTContourShift A δ (|τ|+N) * Real.log N) *
        Real.exp (-((Real.log (N : ℝ))^((1 : ℝ)/20))) := by
      rw [← Real.exp_add]; congr 1
    _ ≤ _ := mul_le_mul_of_nonneg_right hbound (Real.exp_pos _).le

/-- At zero frequency, the all-prime correction times the saving tends to infinity. -/
theorem tendsto_dampedCorrBound_primesLE_contour_saving_atTop
    (A δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ =>
      dampedCorrBound (Nat.primesLE N) (routeTContourLeft A δ N) *
        Real.exp (-((Real.log (N : ℝ))^((1 : ℝ)/20)))) atTop atTop := by
  have hroot : Tendsto (fun N : ℕ => (Real.log (N : ℝ))^((1 : ℝ)/20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hmul : Tendsto (fun N : ℕ => 9*(Real.log (N : ℝ))^((1 : ℝ)/20)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ)<9)).mpr hroot
  apply tendsto_atTop_mono' atTop _ (Real.tendsto_exp_atTop.comp hmul)
  filter_upwards [eventually_dampedCorrBound_primesLE_contour_saving_lower A δ hδ] with N hN
  simpa using hN 0 (by simp : |(0 : ℝ)| ≤ (N : ℝ))

end RHTower.Sieve
