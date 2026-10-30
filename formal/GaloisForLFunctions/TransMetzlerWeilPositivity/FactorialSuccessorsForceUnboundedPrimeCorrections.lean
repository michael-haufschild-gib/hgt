import GaloisForLFunctions.TransMetzlerWeilPositivity.FixedOverlapHasLogarithmicDivisorRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNonRatioMatrixIsTheActualPrimeCorrection
import GaloisForLFunctions.RHTower.Sieve.PrimeLogSqLower
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Above touching, the actual prime correction is unbounded

At horizon `N=2Y!-1`, every prime `p≤Y` supplies the successor edge
`p · 2(Y!/p)=N+1`. These edges have the same profile correlation, and their
squared prime weights sum to `∑ (log p)²/p`. This sum diverges. For every
fixed overlap greater than one, one unit coordinate therefore has unbounded
image under the actual normalized non-ratio prime matrix along these horizons.
Combined with the uniform touching estimate, this classifies eventual
boundedness of that operator exactly. It makes no claim about the sign of
the complete Weil matrix, whose archimedean terms remain present.
-/

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory Filter Topology Matrix

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open ArithmeticLorentzianGeometry ArithmeticElectrostatics ArithmeticEffectivityTheory
  SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- Horizon immediately before a common multiple of all primes through `Y`. -/
def factorialSuccessorHorizon (Y : ℕ) : ℕ := 2 * Y.factorial - 1

theorem factorialSuccessorHorizon_ge (Y : ℕ) : Y ≤ factorialSuccessorHorizon Y := by
  have hfac := Nat.factorial_pos Y
  have hself := Nat.self_le_factorial Y
  dsimp only [factorialSuccessorHorizon]
  omega

theorem factorialSuccessorHorizon_pos (Y : ℕ) : 1 ≤ factorialSuccessorHorizon Y := by
  have hfac := Nat.factorial_pos Y
  dsimp only [factorialSuccessorHorizon]
  omega

private theorem factorial_prime_product {Y p : ℕ} (hp : p ∈ Nat.primesLE Y) :
    p * (2 * (Y.factorial / p)) = factorialSuccessorHorizon Y + 1 := by
  have hprime := Nat.prime_of_mem_primesLE hp
  have hdvd := Nat.dvd_factorial hprime.pos (Nat.mem_primesLE.mp hp).1
  have hfac := Nat.factorial_pos Y
  calc
    _ = 2 * ((Y.factorial / p) * p) := by ring
    _ = 2 * Y.factorial := by rw [Nat.div_mul_cancel hdvd]
    _ = _ := by dsimp only [factorialSuccessorHorizon]; omega

private theorem factorial_prime_index_ge_two {Y p : ℕ} (hp : p ∈ Nat.primesLE Y) :
    2 ≤ 2 * (Y.factorial / p) := by
  have hprime := Nat.prime_of_mem_primesLE hp
  have hdvd := Nat.dvd_factorial hprime.pos (Nat.mem_primesLE.mp hp).1
  have hdiv := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos Y) hdvd) hprime.pos
  omega

private theorem factorial_prime_index_le {Y p : ℕ} (hp : p ∈ Nat.primesLE Y) :
    2 * (Y.factorial / p) ≤ factorialSuccessorHorizon Y := by
  have hprod := factorial_prime_product hp
  have hp2 := (Nat.prime_of_mem_primesLE hp).two_le
  have hn2 := factorial_prime_index_ge_two hp
  nlinarith only [hprod, hp2, hn2]

/-- Last coordinate of the factorial successor horizon. -/
def factorialSuccessorLast (Y : ℕ) : PrimeHorizonIndex (factorialSuccessorHorizon Y) :=
  ⟨factorialSuccessorHorizon Y, mem_Icc.mpr ⟨factorialSuccessorHorizon_pos Y, le_rfl⟩⟩

private def factorialPrimeCoordinate (Y : ℕ) (p : ↥(Nat.primesLE Y)) :
    PrimeHorizonIndex (factorialSuccessorHorizon Y) :=
  ⟨2 * (Y.factorial / p.val), mem_Icc.mpr
    ⟨by have h := factorial_prime_index_ge_two p.property; omega,
      factorial_prime_index_le p.property⟩⟩

private theorem factorialPrimeCoordinate_injective (Y : ℕ) :
    Function.Injective (factorialPrimeCoordinate Y) := by
  intro p q h
  apply Subtype.ext
  have hij := congrArg Subtype.val h
  change 2 * (Y.factorial / p.val) = 2 * (Y.factorial / q.val) at hij
  have hp : p.val * (2 * (Y.factorial / q.val)) = factorialSuccessorHorizon Y + 1 := by
    rw [← hij]
    exact factorial_prime_product p.property
  have hq := factorial_prime_product q.property
  have hn : 0 < 2 * (Y.factorial / q.val) := by
    have h := factorial_prime_index_ge_two q.property
    omega
  exact Nat.eq_of_mul_eq_mul_right hn (hp.trans hq.symm)

/-- Common correlation coefficient of all edges to the successor product. -/
def plateauSuccessorCorrelation (c : ℝ) (N : ℕ) : ℝ :=
  bumpCorr transMetzlerProfile (firstExteriorOverlap N / c) /
    (∫ u, transMetzlerProfile u ^ 2)

theorem plateauSuccessorCorrelation_nonneg (c : ℝ) (N : ℕ) :
    0 ≤ plateauSuccessorCorrelation c N := by
  apply div_nonneg _ integral_transMetzlerProfile_sq_pos.le
  exact integral_nonneg fun u =>
    mul_nonneg (transMetzlerProfile_nonneg u) (transMetzlerProfile_nonneg _)

private theorem successor_indices_nondividing {N p n : ℕ}
    (hp : 2 ≤ p) (hn : 2 ≤ n) (hprod : p * n = N + 1) :
    ¬ N ∣ n ∧ ¬ n ∣ N := by
  have hnN : n < N := by nlinarith only [hp, hn, hprod]
  constructor
  · intro h
    exact (not_le_of_gt hnN) (Nat.le_of_dvd (by omega) h)
  · intro h
    have hnext : n ∣ N + 1 := by rw [← hprod]; exact dvd_mul_left n p
    have hone : n ∣ 1 := by
      simpa only [Nat.add_sub_cancel_left] using Nat.dvd_sub hnext h
    have := Nat.dvd_one.mp hone
    omega

private theorem integral_atom_sub_log_eq_bumpCorr (g : ℝ → ℝ) (m n p : ℕ) :
    (∫ u, atom g m u * atom g n (u - Real.log p)) =
      bumpCorr g (Real.log p - (Real.log m - Real.log n)) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun u => g (u - Real.log m) * g (u - Real.log p - Real.log n))
    (Real.log p + Real.log n)
  change (∫ u, g (u - Real.log m) * g (u - Real.log p - Real.log n)) = _
  rw [← h]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    rw [show u + (Real.log p + Real.log n) - Real.log p - Real.log n = u by ring,
      show u + (Real.log p + Real.log n) - Real.log m =
        u + (Real.log p - (Real.log m - Real.log n)) by ring]
    exact mul_comm _ _

private theorem primePair_ge_one_shift {g : ℝ → ℝ} {w : ℝ}
    (hg0 : ∀ u, 0 ≤ g u) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) {N m n p : ℕ} (hm : m ∈ Icc 1 N) (hn : n ∈ Icc 1 N)
    (hp : 1 ≤ p) (hpN : p ≤ N) :
    vonMangoldtAtom p * bumpCorr g (Real.log p - (Real.log m - Real.log n)) ≤
      primePair (atom g m) (atom g n) := by
  let R := Real.log N + w + 1
  have hpR : p ∈ range (lagRange R) := by
    by_contra hpR
    have hlarge := two_mul_lt_abs_log_of_lagRange_le
      (show lagRange R ≤ p by simpa only [mem_range, not_lt] using hpR)
    rw [abs_of_nonneg (Real.log_natCast_nonneg p)] at hlarge
    have hlog := Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast hp)
      (show (p : ℝ) ≤ N by exact_mod_cast hpN)
    dsimp only [R] at hlarge
    linarith only [hlarge, hlog, Real.log_natCast_nonneg N, hw]
  have hplus (k : ℕ) : 0 ≤ ∫ u, atom g m u * atom g n (u + Real.log k) :=
    integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  have hminus (k : ℕ) : 0 ≤ ∫ u, atom g m u * atom g n (u - Real.log k) :=
    integral_nonneg fun u => mul_nonneg (hg0 _) (hg0 _)
  rw [primePair_eq_sum_of_supportedIn (supportedIn_atom hsupp hw hm)
    (supportedIn_atom hsupp hw hn), ← integral_atom_sub_log_eq_bumpCorr]
  apply (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hplus p))
    (_root_.RHTower.vonMangoldtAtom_nonneg' p)).trans
  exact single_le_sum
    (fun k _ => mul_nonneg (_root_.RHTower.vonMangoldtAtom_nonneg' k)
      (add_nonneg (hminus k) (hplus k))) hpR

/-- A genuine successor prime term survives subtraction of the exact-ratio kernel. -/
theorem fullWeilNonRatioMatrix_successor_entry_ge {c : ℝ} (hc : 0 < c)
    {N p : ℕ} (i j : PrimeHorizonIndex N) (hi : i.val = N)
    (hp : p.Prime) (hj : 2 ≤ j.val) (hprod : p * j.val = N + 1) :
    plateauSuccessorCorrelation c N * (Real.log p / Real.sqrt p) ≤
      fullWeilNonRatioMatrix transMetzlerProfile c N i j := by
  have hN : 1 ≤ N := by simpa only [hi] using (mem_Icc.mp i.property).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hj0 : (0 : ℝ) < j.val := by exact_mod_cast (show 0 < j.val by omega)
  have hpN : p ≤ N := by nlinarith only [hp.two_le, hj, hprod]
  have hnon := successor_indices_nondividing hp.two_le hj hprod
  have hkernel : weilPrimeKernel i j = 0 := by
    change weilPrimeKernel i.val j.val = 0
    rw [hi]
    simp only [weilPrimeKernel, hnon.1, hnon.2, false_and, if_false]
  have hw : 0 < c / N := div_pos hc hN0
  obtain ⟨_, hgsupp, _⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw
  have hM := integral_transMetzlerProfile_sq_pos
  have hmass : 0 < ∫ u, atomDilate transMetzlerProfile (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hterm := primePair_ge_one_shift
    (g := atomDilate transMetzlerProfile (c / N)) (N := N) (m := i.val) (n := j.val) (p := p)
    (fun u => transMetzlerProfile_nonneg (u / (c / N))) hgsupp hw.le i.property j.property
    hp.one_lt.le hpN
  have hprodR : (p : ℝ) * j.val = (N + 1 : ℕ) := by exact_mod_cast hprod
  have hlog : Real.log p + Real.log j.val = Real.log (N + 1 : ℕ) := by
    rw [← Real.log_mul hp0.ne' hj0.ne', hprodR]
  have hlag : Real.log p - (Real.log i.val - Real.log j.val) =
      Real.log (N + 1 : ℕ) - Real.log N := by rw [hi]; linarith only [hlog]
  have hlagw : (Real.log (N + 1 : ℕ) - Real.log N) / (c / N) =
      firstExteriorOverlap N / c := by
    unfold firstExteriorOverlap
    field_simp [hc.ne', hN0.ne']
  rw [fullWeilNonRatioMatrix_apply, hkernel, sub_zero]
  calc
    _ = (vonMangoldtAtom p * bumpCorr (atomDilate transMetzlerProfile (c / N))
        (Real.log p - (Real.log i.val - Real.log j.val))) /
          (∫ u, atomDilate transMetzlerProfile (c / N) u ^ 2) := by
      rw [hlag, bumpCorr_atomDilate hw, integral_atomDilate_sq hw, hlagw,
        vonMangoldtAtom_eq hp.two_le, ArithmeticFunction.vonMangoldt_apply_prime hp]
      unfold plateauSuccessorCorrelation
      field_simp [hc.ne', hN0.ne', hM.ne', (Real.sqrt_pos.mpr hp0).ne']
    _ ≤ _ := div_le_div_of_nonneg_right hterm hmass.le

private theorem sum_sq_le_of_injective {P I : Type*} [Fintype P] [Fintype I] [DecidableEq I]
    (f : P → I) (hf : Function.Injective f) (a : I → ℝ) :
    ∑ p, a (f p) ^ 2 ≤ ∑ i, a i ^ 2 := by
  classical
  calc
    _ = ∑ i ∈ univ.image f, a i ^ 2 := (sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
      (fun i _ _ => sq_nonneg (a i))

/-- The squared action on one unit coordinate contains the complete prime square sum. -/
theorem factorialSuccessor_action_sq_ge {c : ℝ} (hc : 0 < c) (Y : ℕ) :
    plateauSuccessorCorrelation c (factorialSuccessorHorizon Y) ^ 2 *
      (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) ^ 2 / (p : ℝ)) ≤
    ‖Matrix.toEuclideanLin
      (fullWeilNonRatioMatrix transMetzlerProfile c (factorialSuccessorHorizon Y))
      (EuclideanSpace.single (factorialSuccessorLast Y) 1)‖ ^ 2 := by
  classical
  let N := factorialSuccessorHorizon Y
  let A := fullWeilNonRatioMatrix transMetzlerProfile c N
  let q := plateauSuccessorCorrelation c N
  have hentry (p : ↥(Nat.primesLE Y)) :
      q * (Real.log (p.val : ℝ) / Real.sqrt p.val) ≤
        A (factorialPrimeCoordinate Y p) (factorialSuccessorLast Y) := by
    have h := fullWeilNonRatioMatrix_successor_entry_ge hc
      (factorialSuccessorLast Y) (factorialPrimeCoordinate Y p) rfl
      (Nat.prime_of_mem_primesLE p.property) (factorial_prime_index_ge_two p.property)
      (factorial_prime_product p.property)
    have hs := (fullWeilNonRatioMatrix_isHermitian transMetzlerProfile c N).apply
      (factorialSuccessorLast Y) (factorialPrimeCoordinate Y p)
    change A (factorialPrimeCoordinate Y p) (factorialSuccessorLast Y) =
      A (factorialSuccessorLast Y) (factorialPrimeCoordinate Y p) at hs
    rw [hs]
    exact h
  have hcol (i : PrimeHorizonIndex N) :
      Matrix.toEuclideanLin A (EuclideanSpace.single (factorialSuccessorLast Y) 1) i =
        A i (factorialSuccessorLast Y) := by
    simp [Matrix.toLpLin_apply]
  rw [EuclideanSpace.real_norm_sq_eq]
  change q ^ 2 * (∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) ^ 2 / (p : ℝ)) ≤
    ∑ i : PrimeHorizonIndex N,
      (Matrix.toEuclideanLin A (EuclideanSpace.single (factorialSuccessorLast Y) 1) i) ^ 2
  simp_rw [hcol]
  calc
    _ = ∑ p : ↥(Nat.primesLE Y), (q * (Real.log (p.val : ℝ) / Real.sqrt p.val)) ^ 2 := by
      rw [← sum_coe_sort (Nat.primesLE Y) (fun p => Real.log (p : ℝ) ^ 2 / (p : ℝ)), mul_sum]
      apply sum_congr rfl
      intro p hp
      rw [mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg p.val)]
    _ ≤ ∑ p : ↥(Nat.primesLE Y),
        A (factorialPrimeCoordinate Y p) (factorialSuccessorLast Y) ^ 2 := by
      apply sum_le_sum
      intro p hp
      exact pow_le_pow_left₀
        (mul_nonneg (plateauSuccessorCorrelation_nonneg c N)
          (div_nonneg (Real.log_natCast_nonneg p.val) (Real.sqrt_nonneg _))) (hentry p) 2
    _ ≤ _ := sum_sq_le_of_injective (factorialPrimeCoordinate Y)
      (factorialPrimeCoordinate_injective Y) (fun i => A i (factorialSuccessorLast Y))

private theorem factorialSuccessorHorizon_atTop :
    Tendsto factorialSuccessorHorizon atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_id
  exact Eventually.of_forall factorialSuccessorHorizon_ge

private theorem prime_log_sq_sum_atTop :
    Tendsto (fun Y : ℕ => ∑ p ∈ Nat.primesLE Y, Real.log (p : ℝ) ^ 2 / (p : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun Y : ℕ => Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [hlog.eventually_ge_atTop 100, eventually_ge_atTop (1 : ℕ)] with Y hL hY
  have hlower := _root_.RHTower.Sieve.sum_prime_log_sq_div_ge Y hY
  have hpoly : Real.log Y ≤ Real.log Y ^ 2 / 2 - 39 * Real.log Y - 25 := by
    nlinarith only [hL, sq_nonneg (Real.log Y - 100)]
  exact hpoly.trans hlower

private theorem tendsto_plateauSuccessorCorrelation (c : ℝ) :
    Tendsto (plateauSuccessorCorrelation c) atTop
      (𝓝 (bumpCorr transMetzlerProfile (1 / c) / (∫ u, transMetzlerProfile u ^ 2))) := by
  exact (((continuous_bumpCorr contDiff_transMetzlerProfile hasCompactSupport_transMetzlerProfile).tendsto
    (1 / c)).comp (tendsto_firstExteriorOverlap.div_const c)).div_const _

/-- At every fixed overlap above one, the actual prime correction sends a unit coordinate
to vectors of unbounded norm along the factorial successor horizons. -/
theorem factorialSuccessor_action_atTop {c : ℝ} (hc : 1 < c) :
    Tendsto (fun Y : ℕ => ‖Matrix.toEuclideanLin
      (fullWeilNonRatioMatrix transMetzlerProfile c (factorialSuccessorHorizon Y))
      (EuclideanSpace.single (factorialSuccessorLast Y) 1)‖) atTop atTop := by
  have hc0 := zero_lt_one.trans hc
  have hlag : |1 / c| < 1 := by
    rw [abs_of_pos (one_div_pos.mpr hc0)]
    exact (div_lt_one hc0).mpr hc
  have hqpos : 0 < bumpCorr transMetzlerProfile (1 / c) /
      (∫ u, transMetzlerProfile u ^ 2) :=
    div_pos (transMetzlerProfile_bumpCorr_pos hlag) integral_transMetzlerProfile_sq_pos
  have hq := (tendsto_plateauSuccessorCorrelation c).comp factorialSuccessorHorizon_atTop
  have hprod := Tendsto.pos_mul_atTop (sq_pos_of_pos hqpos) (hq.pow 2) prime_log_sq_sum_atTop
  have hsq : Tendsto (fun Y : ℕ => ‖Matrix.toEuclideanLin
      (fullWeilNonRatioMatrix transMetzlerProfile c (factorialSuccessorHorizon Y))
      (EuclideanSpace.single (factorialSuccessorLast Y) 1)‖ ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hprod
    exact Eventually.of_forall (factorialSuccessor_action_sq_ge hc0)
  apply tendsto_atTop.2
  intro B
  filter_upwards [hsq.eventually_gt_atTop (B ^ 2)] with Y hY
  by_contra h
  exact (not_le_of_gt hY) (pow_le_pow_left₀ (norm_nonneg _) (not_le.mp h).le 2)

/-- Arbitrarily late horizons violate every proposed uniform action bound. -/
theorem exists_large_fullWeilNonRatio_action {c : ℝ} (hc : 1 < c) (B : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖x‖ = 1 ∧ B < ‖Matrix.toEuclideanLin (fullWeilNonRatioMatrix transMetzlerProfile c N) x‖ := by
  obtain ⟨Y, hY, hlarge⟩ := ((eventually_ge_atTop N₀).and
    ((factorialSuccessor_action_atTop hc).eventually_gt_atTop B)).exists
  refine ⟨factorialSuccessorHorizon Y, hY.trans (factorialSuccessorHorizon_ge Y),
    EuclideanSpace.single (factorialSuccessorLast Y) 1, ?_, hlarge⟩
  simp

/-- Eventual Euclidean boundedness of the actual plateau prime correction has the sharp
boundary `c=1`; the operator even tends to zero throughout the bounded side. -/
theorem eventually_bounded_fullWeilNonRatio_action_iff {c : ℝ} (hc : 0 < c) :
    (∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ‖Matrix.toEuclideanLin (fullWeilNonRatioMatrix transMetzlerProfile c N) x‖ ≤ C * ‖x‖) ↔
      c ≤ 1 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hgt
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hC
    obtain ⟨N, hN, x, hx, hlarge⟩ := exists_large_fullWeilNonRatio_action (not_le.mp hgt) C N₀
    have hbound := hN₀ N hN x
    rw [hx, mul_one] at hbound
    exact (not_le_of_gt hlarge) hbound
  · intro hc1
    refine ⟨1, ?_⟩
    filter_upwards [eventually_fullWeilNonRatioMatrix_action_small_uniformly
      contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu)
      integral_transMetzlerProfile_sq_pos (by norm_num : (0 : ℝ) < 1)] with N hN
    exact hN c hc hc1

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.fullWeilNonRatioMatrix_successor_entry_ge
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.factorialSuccessor_action_sq_ge
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.factorialSuccessor_action_atTop
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_bounded_fullWeilNonRatio_action_iff
