import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryMovingSupportRigidity
import GaloisForLFunctions.RHTower.AdelicIntertwinerType
import GaloisForLFunctions.RHTower.PrimeSquareDeformedReflectionType
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open scoped BigOperators ComplexOrder
open Filter Set Topology

namespace RHTower

noncomputable section

private theorem exponentialChordFactor_eq_exp_sinh
    {y : ℝ} (hy : 0 < y) :
    exponentialChordFactor y =
      Real.exp (-(y / 2)) * (Real.sinh (y / 2) / (y / 2)) := by
  rw [exponentialChordFactor, if_neg hy.ne']
  have hexp :
      1 - Real.exp (-y) =
        2 * Real.exp (-(y / 2)) * Real.sinh (y / 2) := by
    rw [Real.sinh_eq]
    calc
      1 - Real.exp (-y) =
          Real.exp (-(y / 2)) * Real.exp (y / 2) -
            Real.exp (-(y / 2)) * Real.exp (-(y / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        simp
        ring
      _ = 2 * Real.exp (-(y / 2)) *
          ((Real.exp (y / 2) - Real.exp (-(y / 2))) / 2) := by ring
  rw [hexp]
  field_simp [hy.ne']

theorem exp_neg_half_le_exponentialChordFactor
    {y : ℝ} (hy : 0 ≤ y) :
    Real.exp (-(y / 2)) ≤ exponentialChordFactor y := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [exponentialChordFactor]
  rw [exponentialChordFactor_eq_exp_sinh hy]
  have hhalf : 0 ≤ y / 2 := by positivity
  have hsinh : y / 2 ≤ Real.sinh (y / 2) :=
    Real.self_le_sinh_iff.mpr hhalf
  have hdiv : 1 ≤ Real.sinh (y / 2) / (y / 2) := by
    rw [le_div_iff₀ (by positivity)]
    simpa using hsinh
  simpa using mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le

theorem exponentialChordFactor_le_exp_neg_half_add_sq_eighth
    {y : ℝ} (hy : 0 ≤ y) :
    exponentialChordFactor y ≤ Real.exp (-(y / 2) + y ^ (2 : ℕ) / 8) := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [exponentialChordFactor]
  rw [exponentialChordFactor_eq_exp_sinh hy]
  have hhalf : 0 ≤ y / 2 := by positivity
  have hsinh : Real.sinh (y / 2) ≤ (y / 2) * Real.cosh (y / 2) :=
    sinh_le_mul_cosh hhalf
  have hdiv : Real.sinh (y / 2) / (y / 2) ≤ Real.cosh (y / 2) := by
    rw [div_le_iff₀ (by positivity)]
    simpa [mul_comm] using hsinh
  have hcosh : Real.cosh (y / 2) ≤ Real.exp (y ^ (2 : ℕ) / 8) := by
    calc
      Real.cosh (y / 2) ≤ Real.exp ((y / 2) ^ (2 : ℕ) / 2) :=
        Real.cosh_le_exp_half_sq (y / 2)
      _ = Real.exp (y ^ (2 : ℕ) / 8) := by ring_nf
  calc
    Real.exp (-(y / 2)) * (Real.sinh (y / 2) / (y / 2)) ≤
        Real.exp (-(y / 2)) * Real.exp (y ^ (2 : ℕ) / 8) :=
      mul_le_mul_of_nonneg_left (hdiv.trans hcosh) (Real.exp_pos _).le
    _ = Real.exp (-(y / 2) + y ^ (2 : ℕ) / 8) := by rw [Real.exp_add]

theorem prod_exponentialChordFactor_mem_diffuseBounds
    {α : Type*} [DecidableEq α]
    (s : Finset α) (y : α → ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i) :
    Real.exp (-(∑ i ∈ s, y i) / 2) ≤
        ∏ i ∈ s, exponentialChordFactor (y i) ∧
      (∏ i ∈ s, exponentialChordFactor (y i)) ≤
        Real.exp (-(∑ i ∈ s, y i) / 2 +
          (∑ i ∈ s, (y i) ^ (2 : ℕ)) / 8) := by
  constructor
  · calc
      Real.exp (-(∑ i ∈ s, y i) / 2) =
          ∏ i ∈ s, Real.exp (-(y i / 2)) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [div_eq_mul_inv, neg_mul, Finset.sum_neg_distrib,
          Finset.sum_mul]
      _ ≤ ∏ i ∈ s, exponentialChordFactor (y i) := by
        exact Finset.prod_le_prod
          (fun i hi => (Real.exp_pos _).le)
          (fun i hi => exp_neg_half_le_exponentialChordFactor (hy i hi))
  · calc
      (∏ i ∈ s, exponentialChordFactor (y i)) ≤
          ∏ i ∈ s, Real.exp (-(y i / 2) + (y i) ^ (2 : ℕ) / 8) := by
        exact Finset.prod_le_prod
          (fun i hi => exponentialChordFactor_nonneg (hy i hi))
          (fun i hi =>
            exponentialChordFactor_le_exp_neg_half_add_sq_eighth (hy i hi))
      _ = Real.exp (-(∑ i ∈ s, y i) / 2 +
          (∑ i ∈ s, (y i) ^ (2 : ℕ)) / 8) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.sum_add_distrib, div_eq_mul_inv, neg_mul,
          Finset.sum_neg_distrib, Finset.sum_mul]

private theorem one_sub_sum_le_prod_one_sub
    {α : Type*} [DecidableEq α] (s : Finset α) (a : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have h0' : ∀ j ∈ s, 0 ≤ a j :=
        fun j hj => h0 j (Finset.mem_insert_of_mem hj)
      have h1' : ∀ j ∈ s, a j ≤ 1 :=
        fun j hj => h1 j (Finset.mem_insert_of_mem hj)
      have hai0 : 0 ≤ a i := h0 i (Finset.mem_insert_self i s)
      have hai1 : a i ≤ 1 := h1 i (Finset.mem_insert_self i s)
      have hsum0 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h0'
      have hprod0 : 0 ≤ ∏ j ∈ s, (1 - a j) :=
        Finset.prod_nonneg fun j hj => by linarith [h1' j hj]
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      rcases le_or_gt (1 - ∑ j ∈ s, a j) 0 with hneg | hpos
      · have : 0 ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
          mul_nonneg (by linarith) hprod0
        linarith
      · have hmul := mul_le_mul_of_nonneg_left (ih h0' h1')
          (by linarith : 0 ≤ 1 - a i)
        nlinarith [mul_nonneg hai0 hsum0]

theorem gammaSewnContractionProd_mem_diffuseBounds
    {x : ℝ} (hx : 0 < x) (P : Finset Nat.Primes) :
    1 - 3 * ∑ p ∈ P, (x * Real.log (p : ℝ)) ^ (2 : ℕ) ≤
        ∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p ∧
      (∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p) ≤ 1 := by
  let c : Nat.Primes → ℝ := fun p =>
    gammaSewnMobiusValuationContractionMultiplier x p
  let a : Nat.Primes → ℝ := fun p => 1 - c p
  have hc0 (p : Nat.Primes) : 0 ≤ c p :=
    (gammaSewnMobiusValuationContractionMultiplier_pos x p).le
  have hc1 (p : Nat.Primes) : c p ≤ 1 :=
    (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le
  have ha0 : ∀ p ∈ P, 0 ≤ a p := fun p hp => by
    dsimp only [a]
    linarith [hc1 p]
  have ha1 : ∀ p ∈ P, a p ≤ 1 := fun p hp => by
    dsimp only [a]
    linarith [hc0 p]
  constructor
  · have hprod := one_sub_sum_le_prod_one_sub P a ha0 ha1
    have hloss :
        (∑ p ∈ P, a p) ≤
          3 * ∑ p ∈ P, (x * Real.log (p : ℝ)) ^ (2 : ℕ) := by
      calc
        (∑ p ∈ P, a p) ≤
            ∑ p ∈ P, 3 * (x * Real.log (p : ℝ)) ^ (2 : ℕ) := by
          exact Finset.sum_le_sum fun p hp => by
            simpa only [a, c] using
              one_sub_gammaSewnMobiusValuationContractionMultiplier_le_three_mul_sq
                hx p
        _ = 3 * ∑ p ∈ P, (x * Real.log (p : ℝ)) ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
    apply (by linarith :
      1 - 3 * ∑ p ∈ P, (x * Real.log (p : ℝ)) ^ (2 : ℕ) ≤
        1 - ∑ p ∈ P, a p).trans
    apply hprod.trans_eq
    apply Finset.prod_congr rfl
    intro p hp
    dsimp only [a, c]
    ring
  · calc
      (∏ p ∈ P, gammaSewnMobiusValuationContractionMultiplier x p) ≤
          ∏ p ∈ P, (1 : ℝ) := by
        exact Finset.prod_le_prod
          (fun p hp => hc0 p)
          (fun p hp => hc1 p)
      _ = 1 := by simp

theorem tendsto_prod_exponentialChordFactor_diffuse
    (aperture : ℕ → ℝ) (P : ℕ → Finset Nat.Primes)
    (hpos : ∀ N, 0 < aperture N) {τ : ℝ}
    (htotal : Tendsto
      (fun N => aperture N * ∑ p ∈ P N, Real.log (p : ℝ))
      atTop (𝓝 τ))
    (hsq : Tendsto
      (fun N => ∑ p ∈ P N, (aperture N * Real.log (p : ℝ)) ^ (2 : ℕ))
      atTop (𝓝 0)) :
    Tendsto
      (fun N => ∏ p ∈ P N,
        exponentialChordFactor (aperture N * Real.log (p : ℝ)))
      atTop (𝓝 (Real.exp (-(τ / 2)))) := by
  let X : ℕ → ℝ := fun N =>
    aperture N * ∑ p ∈ P N, Real.log (p : ℝ)
  let Q : ℕ → ℝ := fun N =>
    ∑ p ∈ P N, (aperture N * Real.log (p : ℝ)) ^ (2 : ℕ)
  have hbounds : ∀ N,
      Real.exp (-(X N) / 2) ≤
          ∏ p ∈ P N,
            exponentialChordFactor (aperture N * Real.log (p : ℝ)) ∧
        (∏ p ∈ P N,
            exponentialChordFactor (aperture N * Real.log (p : ℝ))) ≤
          Real.exp (-(X N) / 2 + Q N / 8) := by
    intro N
    have h := prod_exponentialChordFactor_mem_diffuseBounds
      (P N) (fun p => aperture N * Real.log (p : ℝ))
      (fun p hp => (mul_pos (hpos N)
        (Real.log_pos (by exact_mod_cast p.2.one_lt))).le)
    simpa only [X, Q, Finset.mul_sum] using h
  have hX : Tendsto X atTop (𝓝 τ) := by simpa only [X] using htotal
  have hQ : Tendsto Q atTop (𝓝 0) := by simpa only [Q] using hsq
  have hlower : Tendsto (fun N => Real.exp (-(X N) / 2))
      atTop (𝓝 (Real.exp (-(τ / 2)))) := by
    simpa only [neg_div] using (((hX.neg.div_const 2).rexp))
  have hupper : Tendsto (fun N => Real.exp (-(X N) / 2 + Q N / 8))
      atTop (𝓝 (Real.exp (-(τ / 2)))) := by
    simpa only [neg_div, zero_div, add_zero] using
      (((hX.neg.div_const 2).add (hQ.div_const 8)).rexp)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower hupper (fun N => (hbounds N).1) (fun N => (hbounds N).2)

theorem tendsto_prod_gammaSewnContraction_diffuse
    (aperture : ℕ → ℝ) (P : ℕ → Finset Nat.Primes)
    (hpos : ∀ N, 0 < aperture N)
    (hsq : Tendsto
      (fun N => ∑ p ∈ P N, (aperture N * Real.log (p : ℝ)) ^ (2 : ℕ))
      atTop (𝓝 0)) :
    Tendsto
      (fun N => ∏ p ∈ P N,
        gammaSewnMobiusValuationContractionMultiplier (aperture N) p)
      atTop (𝓝 1) := by
  let Q : ℕ → ℝ := fun N =>
    ∑ p ∈ P N, (aperture N * Real.log (p : ℝ)) ^ (2 : ℕ)
  have hQ : Tendsto Q atTop (𝓝 0) := by simpa only [Q] using hsq
  have hlower : Tendsto (fun N => 1 - 3 * Q N) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hQ) using 1
    all_goals ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds
    (fun N => (gammaSewnContractionProd_mem_diffuseBounds (hpos N) (P N)).1)
    (fun N => (gammaSewnContractionProd_mem_diffuseBounds (hpos N) (P N)).2)

theorem tendsto_gammaSewnSynchronizedRecoveryRatio_diffuse
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (aperture : ℕ → ℝ) (P : ℕ → Finset Nat.Primes)
    (hpos : ∀ N, 0 < aperture N) {τ : ℝ} (hτ : 0 < τ)
    (hP : ∀ᶠ N in atTop, (P N).Nonempty)
    (htotal : Tendsto
      (fun N => aperture N * ∑ p ∈ P N, Real.log (p : ℝ))
      atTop (𝓝 τ))
    (hsq : Tendsto
      (fun N => ∑ p ∈ P N, (aperture N * Real.log (p : ℝ)) ^ (2 : ℕ))
      atTop (𝓝 0)) :
    Tendsto
      (fun N => gammaSewnSynchronizedRecoveryRatio nu (aperture N) (P N))
      atTop
      (𝓝 (Real.exp (-(τ / 2)) / exponentialChordFactor τ)) := by
  let X : ℕ → ℝ := fun N =>
    aperture N * ∑ p ∈ P N, Real.log (p : ℝ)
  have hX : Tendsto X atTop (𝓝 τ) := by simpa only [X] using htotal
  have hcontract := tendsto_prod_gammaSewnContraction_diffuse
    aperture P hpos hsq
  have hchord := tendsto_prod_exponentialChordFactor_diffuse
    aperture P hpos htotal hsq
  have hnum :
      Tendsto
        (fun N => ∏ p ∈ P N,
          (gammaSewnMobiusValuationContractionMultiplier (aperture N) p *
            exponentialChordFactor (aperture N * Real.log (p : ℝ))))
        atTop (𝓝 (Real.exp (-(τ / 2)))) := by
    simpa only [Finset.prod_mul_distrib, one_mul] using hcontract.mul hchord
  have hrawDen :
      Tendsto (fun N => (1 - Real.exp (-(X N))) / X N)
        atTop (𝓝 ((1 - Real.exp (-τ)) / τ)) := by
    have hcont : ContinuousAt (fun z : ℝ => (1 - Real.exp (-z)) / z) τ := by
      have hnum : ContinuousAt (fun z : ℝ => 1 - Real.exp (-z)) τ := by
        fun_prop
      exact hnum.div continuousAt_id hτ.ne'
    exact hcont.tendsto.comp hX
  have hXpos : ∀ᶠ N in atTop, 0 < X N :=
    hX.eventually (Ioi_mem_nhds hτ)
  have hdenRaw :
      Tendsto (fun N => exponentialChordFactor (X N))
        atTop (𝓝 ((1 - Real.exp (-τ)) / τ)) := by
    apply hrawDen.congr'
    filter_upwards [hXpos] with N hXN
    simp [exponentialChordFactor, hXN.ne']
  have hlimit :
      (1 - Real.exp (-τ)) / τ = exponentialChordFactor τ := by
    simp [exponentialChordFactor, hτ.ne']
  rw [hlimit] at hdenRaw
  have hquot := hnum.div hdenRaw
    (exponentialChordFactor_pos hτ.le).ne'
  apply hquot.congr'
  filter_upwards [hP] with N hPN
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient
    nu hnu (hpos N) hPN]
  rfl

theorem diffuseRecoveryLimit_eq_sinhRatio
    {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (-(τ / 2)) / exponentialChordFactor τ =
      τ / (2 * Real.sinh (τ / 2)) := by
  rw [exponentialChordFactor_eq_exp_sinh hτ]
  have hhalf : 0 < τ / 2 := by positivity
  have hsinh : 0 < Real.sinh (τ / 2) := Real.sinh_pos_iff.mpr hhalf
  field_simp [Real.exp_ne_zero, hτ.ne', hsinh.ne']

theorem diffuseRecoveryLimit_pos_lt_one
    {τ : ℝ} (hτ : 0 < τ) :
    0 < τ / (2 * Real.sinh (τ / 2)) ∧
      τ / (2 * Real.sinh (τ / 2)) < 1 := by
  have hhalf : 0 < τ / 2 := by positivity
  have hsinh0 : 0 < Real.sinh (τ / 2) := Real.sinh_pos_iff.mpr hhalf
  have hsinh : τ / 2 < Real.sinh (τ / 2) :=
    Real.self_lt_sinh_iff.mpr hhalf
  constructor
  · positivity
  · rw [div_lt_one (by positivity : 0 < 2 * Real.sinh (τ / 2))]
    linarith

def gammaSewnDiffusePrimeAperture (τ : ℝ) (N : ℕ) : ℝ :=
  τ / ((N : ℝ) + 1)

private theorem sum_primesBelowSubtype_log_eq (N : ℕ) :
    (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
      Real.log (p : ℝ)) =
      ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) := by
  classical
  rw [GaloisForLFunctions.primesBelowSubtype]
  rw [Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.attach_eq_univ]
  exact Finset.sum_attach (Nat.primesBelow N)
    (fun p : ℕ => Real.log (p : ℝ))

theorem gammaSewnDiffusePrimeAperture_pos
    {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    0 < gammaSewnDiffusePrimeAperture τ N := by
  unfold gammaSewnDiffusePrimeAperture
  positivity

theorem eventually_primesBelowSubtype_nonempty :
    ∀ᶠ N : ℕ in atTop,
      (GaloisForLFunctions.primesBelowSubtype N).Nonempty := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact ⟨⟨2, Nat.prime_two⟩,
    mem_primesBelowSubtype_iff.mpr (show (2 : ℕ) < N by omega)⟩

private theorem tendsto_natCast_div_natCast_add_one :
    Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) + 1))
      atTop (𝓝 1) := by
  simpa using (tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1 : ℝ))

private theorem tendsto_primesBelow_log_div_natCast_add_one :
    Tendsto
      (fun N : ℕ =>
        (∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) /
          ((N : ℝ) + 1))
      atTop (𝓝 1) := by
  have hprod := tendsto_sum_primesBelow_log_div.mul
    tendsto_natCast_div_natCast_add_one
  have hprod' :
      Tendsto
        (fun N : ℕ =>
          ((∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ)) / (N : ℝ)) *
            ((N : ℝ) / ((N : ℝ) + 1)))
        atTop (𝓝 1) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNs : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hN0, hNs]

private theorem tendsto_log_natCast_div_natCast_add_one_zero :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / ((N : ℝ) + 1))
      atTop (𝓝 0) := by
  have hlogReal : Tendsto (fun x : ℝ => Real.log x / x)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogNat : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      hlogReal.comp tendsto_natCast_atTop_atTop
  have hprod := hlogNat.mul tendsto_natCast_div_natCast_add_one
  have hprod' :
      Tendsto
        (fun N : ℕ => (Real.log (N : ℝ) / (N : ℝ)) *
          ((N : ℝ) / ((N : ℝ) + 1)))
        atTop (𝓝 0) := by simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNs : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hN0, hNs]

theorem tendsto_gammaSewnDiffusePrimeAperture_totalPhase
    (τ : ℝ) :
    Tendsto
      (fun N => gammaSewnDiffusePrimeAperture τ N *
        ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ))
      atTop (𝓝 τ) := by
  have hmass :
      Tendsto
        (fun N : ℕ =>
          (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
              Real.log (p : ℝ)) / ((N : ℝ) + 1))
        atTop (𝓝 1) := by
    apply tendsto_primesBelow_log_div_natCast_add_one.congr'
    exact Filter.Eventually.of_forall fun N => by
      exact congrArg (fun z : ℝ => z / ((N : ℝ) + 1))
        (sum_primesBelowSubtype_log_eq N).symm
  have h :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ)).mul hmass
  have h' :
      Tendsto
        (fun N : ℕ => τ *
          ((∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
              Real.log (p : ℝ)) / ((N : ℝ) + 1)))
        atTop (𝓝 τ) := by simpa using h
  apply h'.congr'
  exact Filter.Eventually.of_forall fun N => by
    unfold gammaSewnDiffusePrimeAperture
    have hden : (N : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]

private theorem sum_primesBelowSubtype_log_sq_le (N : ℕ) :
    (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
      Real.log (p : ℝ) ^ (2 : ℕ)) ≤
      Real.log (N : ℝ) *
        ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ) := by
  calc
    (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
        Real.log (p : ℝ) ^ (2 : ℕ)) ≤
        ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (N : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
      have hpN : (p : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (mem_primesBelowSubtype_iff.mp hp).le
      have hlog0 : 0 ≤ Real.log (p : ℝ) :=
        (Real.log_pos (by exact_mod_cast p.2.one_lt)).le
      have hlogle : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
        Real.log_le_log hp0 hpN
      nlinarith
    _ = Real.log (N : ℝ) *
        ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ) := by
      rw [Finset.mul_sum]

theorem gammaSewnDiffusePrimeAperture_quadraticPhase_le
    (τ : ℝ) (N : ℕ) :
    (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
      (gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)) ^ (2 : ℕ)) ≤
      τ ^ (2 : ℕ) * (Real.log (N : ℝ) / ((N : ℝ) + 1)) *
        ((∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
            Real.log (p : ℝ)) / ((N : ℝ) + 1)) := by
  let L : ℝ := ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
    Real.log (p : ℝ)
  let a : ℝ := gammaSewnDiffusePrimeAperture τ N
  have hrewrite :
      (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
        (a * Real.log (p : ℝ)) ^ (2 : ℕ)) =
        a ^ (2 : ℕ) * ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ) ^ (2 : ℕ) := by
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
  rw [hrewrite]
  calc
    a ^ (2 : ℕ) * ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ) ^ (2 : ℕ) ≤
        a ^ (2 : ℕ) * (Real.log (N : ℝ) * L) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [L] using sum_primesBelowSubtype_log_sq_le N)
        (sq_nonneg a)
    _ = τ ^ (2 : ℕ) * (Real.log (N : ℝ) / ((N : ℝ) + 1)) *
        (L / ((N : ℝ) + 1)) := by
      dsimp only [a, L, gammaSewnDiffusePrimeAperture]
      have hden : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hden]

theorem tendsto_gammaSewnDiffusePrimeAperture_quadraticPhase_zero
    (τ : ℝ) :
    Tendsto
      (fun N => ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
        (gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)) ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hmass :
      Tendsto
        (fun N : ℕ =>
          (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
              Real.log (p : ℝ)) / ((N : ℝ) + 1))
        atTop (𝓝 1) := by
    apply tendsto_primesBelow_log_div_natCast_add_one.congr'
    exact Filter.Eventually.of_forall fun N =>
      congrArg (fun z : ℝ => z / ((N : ℝ) + 1))
        (sum_primesBelowSubtype_log_eq N).symm
  have hupper :
      Tendsto
        (fun N : ℕ => τ ^ (2 : ℕ) *
          (Real.log (N : ℝ) / ((N : ℝ) + 1)) *
          ((∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
              Real.log (p : ℝ)) / ((N : ℝ) + 1)))
        atTop (𝓝 0) := by
    convert
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => τ ^ (2 : ℕ))
          atTop (𝓝 (τ ^ (2 : ℕ)))).mul
        (tendsto_log_natCast_div_natCast_add_one_zero.mul hmass)) using 1
    all_goals ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper
    (fun N => Finset.sum_nonneg fun p hp => sq_nonneg _)
    (fun N => gammaSewnDiffusePrimeAperture_quadraticPhase_le τ N)

theorem tendsto_gammaSewnDiffusePrimeAperture_zero
    (τ : ℝ) :
    Tendsto (gammaSewnDiffusePrimeAperture τ) atTop (𝓝 0) := by
  have hden : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  change Tendsto (fun N : ℕ => τ / ((N : ℝ) + 1)) atTop (𝓝 0)
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => τ)
    atTop (𝓝 τ)).div_atTop hden

theorem tendsto_gammaSewnDiffusePrimeAperture_localChord_one
    {τ : ℝ} (hτ : 0 < τ) (p : Nat.Primes) :
    Tendsto
      (fun N =>
        gammaSewnMobiusValuationContractionMultiplier
            (gammaSewnDiffusePrimeAperture τ N) p *
          exponentialChordFactor
            (gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)))
      atTop (𝓝 1) := by
  let y : ℕ → ℝ := fun N =>
    gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)
  have hy : Tendsto y atTop (𝓝 0) := by
    simpa only [y, zero_mul] using
      (tendsto_gammaSewnDiffusePrimeAperture_zero τ).mul_const
        (Real.log (p : ℝ))
  have hlower : Tendsto (fun N => 1 - y N - 3 * (y N) ^ (2 : ℕ))
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub hy).sub
      (tendsto_const_nhds.mul (hy.pow 2)) using 1
    all_goals ring
  have hbounds : ∀ N,
      1 - y N - 3 * (y N) ^ (2 : ℕ) ≤
          gammaSewnMobiusValuationContractionMultiplier
              (gammaSewnDiffusePrimeAperture τ N) p *
            exponentialChordFactor (y N) ∧
        gammaSewnMobiusValuationContractionMultiplier
              (gammaSewnDiffusePrimeAperture τ N) p *
            exponentialChordFactor (y N) ≤ 1 := by
    intro N
    have hapos := gammaSewnDiffusePrimeAperture_pos hτ N
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hlocal :=
      one_sub_gammaSewnLocalChord_le_totalPhase_add_three_mul_sq hapos p
    have hc0 :=
      (gammaSewnMobiusValuationContractionMultiplier_pos
        (gammaSewnDiffusePrimeAperture τ N) p).le
    have hc1 :=
      (gammaSewnMobiusValuationContractionMultiplier_lt_one hapos p).le
    have hf0 := exponentialChordFactor_nonneg (mul_pos hapos hlog).le
    have hf1 := exponentialChordFactor_le_one (mul_pos hapos hlog).le
    constructor
    · dsimp only [y]
      linarith
    · exact (mul_le_mul hc1 hf1 hf0 zero_le_one).trans_eq (one_mul 1)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlower tendsto_const_nhds (fun N => (hbounds N).1) (fun N => (hbounds N).2)

theorem tendsto_gammaSewnSynchronizedRecoveryRatio_diffuse_primesBelow
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto
      (fun N => gammaSewnSynchronizedRecoveryRatio nu
        (gammaSewnDiffusePrimeAperture τ N)
        (GaloisForLFunctions.primesBelowSubtype N))
      atTop (𝓝 (τ / (2 * Real.sinh (τ / 2)))) := by
  have h := tendsto_gammaSewnSynchronizedRecoveryRatio_diffuse
    nu hnu (gammaSewnDiffusePrimeAperture τ)
    GaloisForLFunctions.primesBelowSubtype
    (gammaSewnDiffusePrimeAperture_pos hτ) hτ
    eventually_primesBelowSubtype_nonempty
    (tendsto_gammaSewnDiffusePrimeAperture_totalPhase τ)
    (tendsto_gammaSewnDiffusePrimeAperture_quadraticPhase_zero τ)
  rw [diffuseRecoveryLimit_eq_sinhRatio hτ] at h
  exact h

/-- Canonical diffuse prime recovery is locally coefficient-faithful while retaining a strictly
nontrivial collective contraction. -/
theorem gammaSewnDiffusePrimeRecovery_localFaithful_collectivelyDamped
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) :
    (∀ p : Nat.Primes,
      Tendsto
        (fun N =>
          gammaSewnMobiusValuationContractionMultiplier
              (gammaSewnDiffusePrimeAperture τ N) p *
            exponentialChordFactor
              (gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)))
        atTop (𝓝 1)) ∧
      Tendsto
        (fun N => gammaSewnSynchronizedRecoveryRatio nu
          (gammaSewnDiffusePrimeAperture τ N)
          (GaloisForLFunctions.primesBelowSubtype N))
        atTop (𝓝 (τ / (2 * Real.sinh (τ / 2)))) ∧
      0 < τ / (2 * Real.sinh (τ / 2)) ∧
        τ / (2 * Real.sinh (τ / 2)) < 1 := by
  exact ⟨tendsto_gammaSewnDiffusePrimeAperture_localChord_one hτ,
    tendsto_gammaSewnSynchronizedRecoveryRatio_diffuse_primesBelow nu hnu hτ,
    diffuseRecoveryLimit_pos_lt_one hτ⟩

/-- Remove squarefree parity from the canonical moving-support recovery amplitude. -/
def gammaSewnDiffusePrimeOrientedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (τ : ℝ) (N : ℕ) : ℂ :=
  ((((-1 : ℝ) ^
      (GaloisForLFunctions.primesBelowSubtype N).card : ℝ) : ℂ)) *
    gammaSewnSynchronizedSignedRecoveryAmplitude nu
      (gammaSewnDiffusePrimeAperture τ N)
      (GaloisForLFunctions.primesBelowSubtype N)

theorem gammaSewnDiffusePrimeOrientedRecoveryAmplitude_eq_sqrt
    (nu : Nat.Primes → ℝ) (τ : ℝ) (N : ℕ) :
    gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ N =
      (Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu
        (gammaSewnDiffusePrimeAperture τ N)
        (GaloisForLFunctions.primesBelowSubtype N)) : ℝ) := by
  rw [gammaSewnDiffusePrimeOrientedRecoveryAmplitude,
    gammaSewnSynchronizedSignedRecoveryAmplitude]
  push_cast
  rw [← mul_assoc]
  rw [← pow_add, show
    (GaloisForLFunctions.primesBelowSubtype N).card +
      (GaloisForLFunctions.primesBelowSubtype N).card =
        2 * (GaloisForLFunctions.primesBelowSubtype N).card by omega,
    pow_mul]
  norm_num

theorem tendsto_gammaSewnDiffusePrimeOrientedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ)
      atTop
      (𝓝 ((Real.sqrt (τ / (2 * Real.sinh (τ / 2))) : ℝ) : ℂ)) := by
  have hratio :=
    tendsto_gammaSewnSynchronizedRecoveryRatio_diffuse_primesBelow nu hnu hτ
  have hsqrt :
      Tendsto
        (fun N => Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu
          (gammaSewnDiffusePrimeAperture τ N)
          (GaloisForLFunctions.primesBelowSubtype N)))
        atTop (𝓝 (Real.sqrt (τ / (2 * Real.sinh (τ / 2))))) := by
    simpa only [Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  apply hsqrt.ofReal.congr'
  exact Filter.Eventually.of_forall fun N =>
    (gammaSewnDiffusePrimeOrientedRecoveryAmplitude_eq_sqrt nu τ N).symm

/-- Universal positive scalar that restores the literal Ward coefficient after diffuse damping. -/
def gammaSewnDiffusePrimeWardNormalizer (τ : ℝ) : ℝ :=
  (Real.sqrt (τ / (2 * Real.sinh (τ / 2))))⁻¹

/-- Coefficient-restored moving-support amplitude.  It is uniformly bounded, though no longer a
contraction at finite cutoff. -/
def gammaSewnDiffusePrimeNormalizedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (τ : ℝ) (N : ℕ) : ℂ :=
  (gammaSewnDiffusePrimeWardNormalizer τ : ℂ) *
    gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ N

theorem tendsto_gammaSewnDiffusePrimeNormalizedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (gammaSewnDiffusePrimeNormalizedRecoveryAmplitude nu τ)
      atTop (𝓝 1) := by
  have hq := diffuseRecoveryLimit_pos_lt_one hτ
  have hsqrt : 0 < Real.sqrt (τ / (2 * Real.sinh (τ / 2))) :=
    Real.sqrt_pos.2 hq.1
  have h :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (gammaSewnDiffusePrimeWardNormalizer τ : ℂ))
      atTop (𝓝 (gammaSewnDiffusePrimeWardNormalizer τ : ℂ))).mul
      (tendsto_gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu hnu hτ)
  change Tendsto
    (fun N => (gammaSewnDiffusePrimeWardNormalizer τ : ℂ) *
      gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ N)
    atTop (nhds (1 : ℂ))
  have hlimit :
      (gammaSewnDiffusePrimeWardNormalizer τ : ℂ) *
          ((Real.sqrt (τ / (2 * Real.sinh (τ / 2))) : ℝ) : ℂ) = 1 := by
    rw [gammaSewnDiffusePrimeWardNormalizer, ← Complex.ofReal_mul]
    norm_num [hsqrt.ne']
  simpa only [hlimit] using h

theorem norm_gammaSewnDiffusePrimeNormalizedRecoveryAmplitude_le
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    ‖gammaSewnDiffusePrimeNormalizedRecoveryAmplitude nu τ N‖ ≤
      gammaSewnDiffusePrimeWardNormalizer τ := by
  have hq := diffuseRecoveryLimit_pos_lt_one hτ
  have hsqrt : 0 < Real.sqrt (τ / (2 * Real.sinh (τ / 2))) :=
    Real.sqrt_pos.2 hq.1
  have horiented :
      ‖gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ N‖ ≤ 1 := by
    rw [gammaSewnDiffusePrimeOrientedRecoveryAmplitude, norm_mul]
    simpa using norm_gammaSewnSynchronizedSignedRecoveryAmplitude_le_one
      nu hnu (gammaSewnDiffusePrimeAperture_pos hτ N)
      (GaloisForLFunctions.primesBelowSubtype N)
  have hnormalizer_nonneg : 0 ≤ gammaSewnDiffusePrimeWardNormalizer τ := by
    unfold gammaSewnDiffusePrimeWardNormalizer
    positivity
  have hnorm_normalizer :
      ‖(gammaSewnDiffusePrimeWardNormalizer τ : ℂ)‖ =
        gammaSewnDiffusePrimeWardNormalizer τ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hnormalizer_nonneg]
  rw [gammaSewnDiffusePrimeNormalizedRecoveryAmplitude, norm_mul,
    hnorm_normalizer]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left horiented hnormalizer_nonneg

theorem tendsto_xiWardAnchoredSourceTransportV_diffusePrimeSlope
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ}
    (hz : XiC z ≠ 0) (hz0 : z ≠ 0) :
    Tendsto
      (fun N =>
        xiWardAnchoredSourceTransportV z
            (gammaSewnDiffusePrimeAperture τ N : ℂ) /
          (gammaSewnDiffusePrimeAperture τ N : ℂ))
      atTop (𝓝 (logDeriv XiC z)) := by
  have hap0 := tendsto_gammaSewnDiffusePrimeAperture_zero τ
  have hapRight :
      Tendsto (gammaSewnDiffusePrimeAperture τ) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hap0, Filter.Eventually.of_forall
      (gammaSewnDiffusePrimeAperture_pos hτ)⟩
  have hsource := hasDerivAt_xiWardAnchoredSourceTransportV_zero hz hz0
  have hjetRight := hasDerivAt_tendsto_real_slope_zero_right hsource
  have hcomp := hjetRight.comp hapRight
  change Tendsto
    (fun N =>
      (xiWardAnchoredSourceTransportV z
          (gammaSewnDiffusePrimeAperture τ N : ℂ) -
        xiWardAnchoredSourceTransportV z 0) /
          (gammaSewnDiffusePrimeAperture τ N : ℂ))
    atTop (nhds (logDeriv XiC z)) at hcomp
  simpa only [xiWardAnchoredSourceTransportV_zero_value hz,
    sub_zero] using hcomp

/-- Without the universal scalar normalization, the exact Ward tangent survives only with the
strict diffuse damping factor.  This is the precise coefficient/order tradeoff. -/
theorem tendsto_gammaSewnDiffusePrimeOriented_xiWardAnchoredSourceTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ}
    (hz : XiC z ≠ 0) (hz0 : z ≠ 0) :
    Tendsto
      (fun N =>
        gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu τ N *
          (xiWardAnchoredSourceTransportV z
            (gammaSewnDiffusePrimeAperture τ N : ℂ) /
              (gammaSewnDiffusePrimeAperture τ N : ℂ)))
      atTop
      (𝓝 (((Real.sqrt (τ / (2 * Real.sinh (τ / 2))) : ℝ) : ℂ) *
        logDeriv XiC z)) := by
  exact (tendsto_gammaSewnDiffusePrimeOrientedRecoveryAmplitude nu hnu hτ).mul
    (tendsto_xiWardAnchoredSourceTransportV_diffusePrimeSlope hτ hz hz0)

theorem tendsto_gammaSewnDiffusePrimeNormalized_xiWardAnchoredSourceTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) {z : ℂ}
    (hz : XiC z ≠ 0) (hz0 : z ≠ 0) :
    Tendsto
      (fun N =>
        gammaSewnDiffusePrimeNormalizedRecoveryAmplitude nu τ N *
          (xiWardAnchoredSourceTransportV z
            (gammaSewnDiffusePrimeAperture τ N : ℂ) /
              (gammaSewnDiffusePrimeAperture τ N : ℂ)))
      atTop (𝓝 (logDeriv XiC z)) := by
  simpa using
    (tendsto_gammaSewnDiffusePrimeNormalizedRecoveryAmplitude nu hnu hτ).mul
      (tendsto_xiWardAnchoredSourceTransportV_diffusePrimeSlope hτ hz hz0)

theorem gammaSewnDiffusePrimeRecoveredXiWardNormalized_nonexpansive
    {n : ℕ} (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {τ : ℝ} (hτ : 0 < τ) (N : ℕ) {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re) :
    (rightHalfPlanePickDefect w
      (gammaSewnSynchronizedRecoveredXiWardNormalizedMultiplier nu
        (gammaSewnDiffusePrimeAperture τ N)
        (GaloisForLFunctions.primesBelowSubtype N) w)).PosSemidef :=
  gammaSewnSynchronizedRecoveredXiWardNormalized_nonexpansive
    nu hnu (GaloisForLFunctions.primesBelowSubtype N) hw
    (gammaSewnDiffusePrimeAperture_pos hτ N)

end
end RHTower
