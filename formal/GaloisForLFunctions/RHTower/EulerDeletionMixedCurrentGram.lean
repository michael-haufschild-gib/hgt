import GaloisForLFunctions.RHTower.EulerDeletionReflectedCurrentEnergy

/-!
# Full mixed deletion current and finite-channel rigidity

Complex superposition retains all mixed currents. At actual zeros its complete
quadratic current is a signed prefix Gram energy; arithmetic independence makes
the orientation strict for every nonzero finite coefficient vector.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionMixedCurrent
open DeletionReflectedGram DeletionReflectedCurrent DeletionReflectedEnergy
open DeletionChronologicalLimit DeletionJointCirculation

/-- The literal finite complex superposition of deletion paths. -/
def mixedPath (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ S, c p*eulerDeletionWeightedJump p s n

/-- The complete quadratic source current, including every off-diagonal term. -/
def quadraticCurrent (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ p ∈ S, ∑ q ∈ S, c p*star (c q)*variationCurrent p q s (partner s)

/-- Actual prefix Gram energy of the full superposition. -/
def mixedEnergy (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (n : ℕ) : ℝ :=
  (weight s (n+1)-weight s n)*‖endpoint (mixedPath S c s) (n+1)‖^2

private theorem mixed_endpoint (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    endpoint (mixedPath S c s) N =
      ∑ p ∈ S, c p*endpoint (eulerDeletionWeightedJump p s) N := by
  simp only [endpoint, mixedPath, Finset.mul_sum]
  exact Finset.sum_comm

/-- Scalar reflection acts on the whole complex superposition with the same real weight. -/
theorem mixedPath_partner (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    mixedPath S c (partner s) n=(weight s n:ℂ)*mixedPath S c s n := by
  simp only [mixedPath, reflected_jump_eq_weight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private theorem cross_mix (S : Finset ℕ) (c : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    chronologicalCrossPrefix (mixedPath S c s) (mixedPath S c (partner s)) N =
      ∑ p ∈ S, ∑ q ∈ S, c p*star (c q)*reflectedCross p q s N := by
  change (∑ n ∈ Finset.range N,
    endpoint (mixedPath S c s) n*star (mixedPath S c (partner s) n)) =
    ∑ p ∈ S, ∑ q ∈ S, c p*star (c q)*
      (∑ n ∈ Finset.range N, endpoint (eulerDeletionWeightedJump p s) n*
        star (eulerDeletionWeightedJump q (partner s) n))
  simp only [mixed_endpoint, mixedPath, Complex.star_def, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The full mixed quadratic current is the ordinary limit of the actual chronological difference. -/
theorem mixed_chronological_tendsto (S : Finset ℕ) (c : ℕ → ℂ) {s : ℂ}
    (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (fun N =>
      chronologicalCrossPrefix (mixedPath S c s) (mixedPath S c (partner s)) N-
      chronologicalCrossPrefix (mixedPath S c (partner s)) (mixedPath S c s) N)
      atTop (nhds (-quadraticCurrent S c s)) := by
  have hr : 0<(partner s).re ∧ (partner s).re<1 := by
    simp only [partner, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    constructor <;> linarith
  have ht := tendsto_finsetSum S (fun p hp => tendsto_finsetSum S (fun q hq =>
    ((variationCurrent_tendsto p q hs hs' hr.1 hr.2).2).const_mul (c p*star (c q))))
  have he (N : ℕ) :
      chronologicalCrossPrefix (mixedPath S c s) (mixedPath S c (partner s)) N-
      chronologicalCrossPrefix (mixedPath S c (partner s)) (mixedPath S c s) N =
      ∑ p ∈ S, ∑ q ∈ S,
        c p*star (c q)*(reflectedCross p q s N-reflectedCross p q (partner s) N) := by
    have hrev := cross_mix S c (partner s) N
    simp only [partner_partner] at hrev
    rw [cross_mix, hrev]
    simp only [mul_sub, Finset.sum_sub_distrib]
  simpa only [quadraticCurrent, mul_neg, Finset.sum_neg_distrib] using
    ht.congr (fun N => (he N).symm)

private theorem mixed_endpoint_zero (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (endpoint (mixedPath S c rho.1)) atTop (nhds 0) := by
  have ht := tendsto_finsetSum S (fun p hp =>
    (source_endpoint_tendsto p (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)).const_mul (c p))
  have hz (p : ℕ) : eulerDeletionDirichletSum p rho.1=0 := by
    rw [source_endpoint_value p (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
      rho.2.2.2, rho.2.1, mul_zero]
  simpa only [hz, mul_zero, Finset.sum_const_zero, ← mixed_endpoint] using ht

/-- The entire superposed prefix retains an explicit source tail bound at every zero. -/
theorem mixed_endpoint_bound (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) (N : ℕ) :
    ‖endpoint (mixedPath S c rho.1) N‖ ≤
      (∑ p ∈ S, ‖c p‖*eulerDeletionAbelTailConstant p rho.1)*((N:ℝ)+1)^(-rho.1.re) := by
  rw [mixed_endpoint, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero p N
      (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho) rho.2.2.2 rho.2.1) (norm_nonneg _)

private theorem weighted_mixed_endpoint_zero (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => ((weight rho.1 N*‖endpoint (mixedPath S c rho.1) N‖^2:ℝ):ℂ))
      atTop (nhds 0) := by
  let A : ℝ := ∑ p ∈ S, ‖c p‖*eulerDeletionAbelTailConstant p rho.1
  have ht : Tendsto (fun N : ℕ => 1/((N:ℝ)+1)) atTop (nhds (0:ℝ)) := by
    simpa only [norm_kernel, Complex.one_re, Real.rpow_neg_one, one_div, norm_zero] using
      (kernel_tendsto_zero (1:ℂ) (by norm_num)).norm
  apply squeeze_zero_norm' (Filter.Eventually.of_forall (fun N => ?_))
    (by simpa only [mul_zero, div_eq_mul_inv, one_mul] using ht.const_mul (A^2))
  have hx : 0<(N:ℝ)+1 := by positivity
  have hw : 0≤weight rho.1 N := Real.rpow_nonneg hx.le _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  calc
    _ ≤ weight rho.1 N*(A*((N:ℝ)+1)^(-rho.1.re))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (mixed_endpoint_bound S c rho N) 2) hw
    _ = A^2*(((N:ℝ)+1)^(exponent rho.1)*
      (((N:ℝ)+1)^(-rho.1.re)*((N:ℝ)+1)^(-rho.1.re))) := by unfold weight; ring
    _ = A^2*((N:ℝ)+1)^(-1:ℝ) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 2
      unfold exponent
      ring
    _ = _ := by rw [Real.rpow_neg_one]

/-- The complete complex quadratic current is the limit of the actual signed Gram prefixes. -/
theorem mixed_energy_tendsto (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    Tendsto (fun N => (((∑ n ∈ Finset.range N, mixedEnergy S c rho.1 n):ℝ):ℂ))
      atTop (nhds (quadraticCurrent S c rho.1)) := by
  have hx := mixed_endpoint_zero S c rho
  let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
  have hy := mixed_endpoint_zero S c r
  have hr : r.1=partner rho.1 := rfl
  rw [hr] at hy
  have hd := mixed_chronological_tendsto S c
    (RiemannGaussian.NontrivialZetaZero.zero_lt_re rho)
    (RiemannGaussian.NontrivialZetaZero.re_lt_one rho)
  have he (N : ℕ) := weighted_cross_identity (weight rho.1) (mixedPath S c rho.1) N
  have hf : (fun n => (weight rho.1 n:ℂ)*mixedPath S c rho.1 n)=mixedPath S c (partner rho.1) := by
    funext n
    exact (mixedPath_partner S c rho.1 n).symm
  simp only [hf, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at he
  have ht := ((weighted_mixed_endpoint_zero S c rho).sub (hy.mul hx.star)).sub hd
  simpa only [star_zero, mul_zero, sub_self, zero_sub, neg_neg] using
    ht.congr (fun N => by dsimp [mixedEnergy]; linear_combination -(he N))

private theorem mixedEnergy_nonneg (S : Finset ℕ) (c : ℕ → ℂ) {s : ℂ}
    (hs : 1/2 ≤ s.re) (n : ℕ) : 0 ≤ mixedEnergy S c s n := by
  apply mul_nonneg _ (sq_nonneg _)
  apply sub_nonneg.mpr
  exact Real.rpow_le_rpow (by positivity) (by push_cast; linarith)
    (by unfold exponent; linarith)

private theorem mixedEnergy_nonpos (S : Finset ℕ) (c : ℕ → ℂ) {s : ℂ}
    (hs : s.re ≤ 1/2) (n : ℕ) : mixedEnergy S c s n≤0 := by
  apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  apply sub_nonpos.mpr
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith)
    (by unfold exponent; linarith)

/-- The signed Gram series is genuinely summable for every finite coefficient vector. -/
theorem hasSum_mixedEnergy (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    HasSum (mixedEnergy S c rho.1) (quadraticCurrent S c rho.1).re := by
  have ht := (Complex.continuous_re.tendsto _).comp (mixed_energy_tendsto S c rho)
  simp only [Function.comp_def, Complex.ofReal_re] at ht
  by_cases hs : 1/2≤rho.1.re
  · exact (hasSum_iff_tendsto_nat_of_nonneg (mixedEnergy_nonneg S c hs) _).2 ht
  · have hn : ∀ n, 0≤ -mixedEnergy S c rho.1 n :=
      fun n => neg_nonneg.mpr (mixedEnergy_nonpos S c (le_of_not_ge hs) n)
    have hh := ((hasSum_iff_tendsto_nat_of_nonneg hn _).2
      (by simpa only [Finset.sum_neg_distrib] using ht.neg)).neg
    simpa only [neg_neg] using hh

/-- No imaginary component survives in the full mixed quadratic current at an actual zero. -/
theorem quadraticCurrent_eq_energy (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) :
    quadraticCurrent S c rho.1=((∑' n, mixedEnergy S c rho.1 n):ℝ) := by
  have ht := (Complex.continuous_ofReal.tendsto _).comp
    (hasSum_mixedEnergy S c rho).summable.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique (mixed_energy_tendsto S c rho) ht

/-- The initial coefficient segment through M already distinguishes every channel of index at most M. -/
theorem deletion_coefficients_independent_initial (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p)
    (M : ℕ) (hM : ∀ p ∈ S, p≤M)
    (hz : ∀ n : ℕ, n≤M → ∑ p ∈ S, c p*eulerDeletionDirichletCoefficient p n=0) :
    ∀ p ∈ S, c p=0 := by
  have hsum : ∑ p ∈ S, c p=0 := by
    calc
      _ = ∑ p ∈ S, c p*eulerDeletionDirichletCoefficient p 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hd : ¬(p+1)∣1 := by have := hS p hp; simp only [Nat.dvd_one]; omega
        simp [eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
      _ = 0 := hz 0 (Nat.zero_le M)
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    intro hp
    have hrest : (∑ q ∈ S, c q*(if (q+1)∣(p+1) then ((q+1:ℕ):ℂ) else 0)) =
        c p*((p+1:ℕ):ℂ) := by
      calc
        _ = c p*(if (p+1)∣(p+1) then ((p+1:ℕ):ℂ) else 0) := by
          apply Finset.sum_eq_single p
          · intro q hq hqp
            by_cases hd : (q+1)∣(p+1)
            · have hle := Nat.le_of_dvd (Nat.succ_pos p) hd
              have hlt : q<p := by omega
              rw [ih q hlt hq, zero_mul]
            · simp only [hd, if_false, mul_zero]
          · intro hnp
            exact False.elim (hnp hp)
        _ = _ := by simp
    have he : (∑ q ∈ S, c q*eulerDeletionDirichletCoefficient q p) =
        (∑ q ∈ S, c q)-
          ∑ q ∈ S, c q*(if (q+1)∣(p+1) then ((q+1:ℕ):ℂ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hd : (q+1)∣(p+1)
      all_goals simp [eulerDeletionDirichletCoefficient, blockDeletionCoefficient, hd]
      all_goals ring
    have h := hz p (hM p hp)
    rw [he, hsum, hrest, zero_sub, neg_eq_zero] at h
    exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast Nat.succ_ne_zero p)

/-- Distinct nontrivial deletion coefficient streams are independent over the complex numbers. -/
theorem deletion_coefficients_independent (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p)
    (hz : ∀ n : ℕ, ∑ p ∈ S, c p*eulerDeletionDirichletCoefficient p n=0) :
    ∀ p ∈ S, c p=0 :=
  deletion_coefficients_independent_initial S c hS (S.sup id)
    (fun _ hp => Finset.le_sup (f := id) hp) (fun n _ => hz n)

/-- A nonzero vector supported on indices at most M is detected by one of the first M+1 prefixes. -/
theorem exists_nonzero_mixed_prefix_initial (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0)
    (M : ℕ) (hM : ∀ p ∈ S, p≤M) (s : ℂ) :
    ∃ n : ℕ, n≤M ∧ endpoint (mixedPath S c s) (n+1)≠0 := by
  by_contra hn
  push Not at hn
  have hpref : ∀ N : ℕ, N≤M+1 → endpoint (mixedPath S c s) N=0 := by
    intro N hN
    cases N with
    | zero => simp [endpoint]
    | succ n => exact hn n (by omega)
  have hpath (n : ℕ) (hnM : n≤M) : mixedPath S c s n=0 := by
    have he := Finset.sum_range_succ (mixedPath S c s) n
    change endpoint (mixedPath S c s) (n+1)=endpoint (mixedPath S c s) n+mixedPath S c s n at he
    rw [hpref (n+1) (by omega), hpref n (by omega), zero_add] at he
    exact he.symm
  have hcoeff (n : ℕ) (hnM : n≤M) : ∑ p ∈ S, c p*eulerDeletionDirichletCoefficient p n=0 := by
    have he : mixedPath S c s n =
        (∑ p ∈ S, c p*eulerDeletionDirichletCoefficient p n)*kernel s n := by
      simp only [mixedPath, eulerDeletionWeightedJump, kernel, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    have hk : kernel s n≠0 := by
      apply Complex.cpow_ne_zero_iff.mpr
      left
      have hx : 0<(n:ℝ)+1 := by positivity
      exact_mod_cast hx.ne'
    have h := hpath n hnM
    rw [he] at h
    exact (mul_eq_zero.mp h).resolve_right hk
  obtain ⟨p,hp,hcp⟩ := hc
  exact hcp (deletion_coefficients_independent_initial S c hS M hM hcoeff p hp)

/-- A nonzero finite coefficient vector cannot annihilate every literal mixed prefix. -/
theorem exists_nonzero_mixed_prefix (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0) (s : ℂ) :
    ∃ n : ℕ, endpoint (mixedPath S c s) (n+1)≠0 := by
  obtain ⟨n,_,hn⟩ := exists_nonzero_mixed_prefix_initial S c hS hc
    (S.sup id) (fun _ hp => Finset.le_sup (f := id) hp) s
  exact ⟨n,hn⟩

/-- A fixed finite source head already has strictly positive Gram energy on the right. -/
theorem mixed_energy_initial_pos (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0)
    (M : ℕ) (hM : ∀ p ∈ S, p≤M) {s : ℂ} (hs : 1/2<s.re) :
    0 < ∑ n ∈ Finset.range (M+1), mixedEnergy S c s n := by
  obtain ⟨n,hnM,hn⟩ := exists_nonzero_mixed_prefix_initial S c hS hc M hM s
  have hw : 0<weight s (n+1)-weight s n := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow (by positivity) (by push_cast; linarith)
      (by unfold exponent; linarith)
  exact Finset.sum_pos' (fun n _ => mixedEnergy_nonneg S c hs.le n)
    ⟨n,Finset.mem_range.mpr (by omega),mul_pos hw (sq_pos_of_pos (norm_pos_iff.mpr hn))⟩

/-- The same finite source head has strictly negative Gram energy on the left. -/
theorem mixed_energy_initial_neg (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0)
    (M : ℕ) (hM : ∀ p ∈ S, p≤M) {s : ℂ} (hs : s.re<1/2) :
    (∑ n ∈ Finset.range (M+1), mixedEnergy S c s n)<0 := by
  obtain ⟨n,hnM,hn⟩ := exists_nonzero_mixed_prefix_initial S c hS hc M hM s
  have hw : weight s (n+1)-weight s n<0 := by
    apply sub_neg.mpr
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by push_cast; linarith)
      (by unfold exponent; linarith)
  have hp : mixedEnergy S c s n<0 :=
    mul_neg_of_neg_of_pos hw (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have h : 0 < ∑ i ∈ Finset.range (M+1), -mixedEnergy S c s i :=
    Finset.sum_pos' (fun i _ => neg_nonneg.mpr (mixedEnergy_nonpos S c hs.le i))
      ⟨n,Finset.mem_range.mpr (by omega),neg_pos.mpr hp⟩
  rw [Finset.sum_neg_distrib] at h
  linarith

/-- Every finite positive Gram prefix gives a lower bound for the complete source current at a zero. -/
theorem mixed_energy_prefix_le_current (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : 1/2≤rho.1.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, mixedEnergy S c rho.1 n) ≤ (quadraticCurrent S c rho.1).re := by
  have ht := hasSum_mixedEnergy S c rho
  simpa only [ht.tsum_eq] using ht.summable.sum_le_tsum (Finset.range N)
    (fun n _ => mixedEnergy_nonneg S c hs n)

/-- Every finite negative Gram prefix gives an upper bound for the complete source current at a zero. -/
theorem current_le_mixed_energy_prefix (S : Finset ℕ) (c : ℕ → ℂ)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : rho.1.re≤1/2) (N : ℕ) :
    (quadraticCurrent S c rho.1).re ≤ ∑ n ∈ Finset.range N, mixedEnergy S c rho.1 n := by
  have ht := (hasSum_mixedEnergy S c rho).neg
  have h := ht.summable.sum_le_tsum (Finset.range N)
    (fun n _ => neg_nonneg.mpr (mixedEnergy_nonpos S c hs n))
  rw [ht.tsum_eq, Finset.sum_neg_distrib] at h
  linarith

/-- Every nonzero finite complex superposition has strictly positive current at a right-half zero. -/
theorem quadraticCurrent_re_pos (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : 1/2<rho.1.re) :
    0<(quadraticCurrent S c rho.1).re := by
  obtain ⟨n,hn⟩ := exists_nonzero_mixed_prefix S c hS hc rho.1
  have hw : 0<weight rho.1 (n+1)-weight rho.1 n := by
    apply sub_pos.mpr
    exact Real.rpow_lt_rpow (by positivity) (by push_cast; linarith)
      (by unfold exponent; linarith)
  have hp : 0 < mixedEnergy S c rho.1 n :=
    mul_pos hw (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have ht := hasSum_mixedEnergy S c rho
  simpa only [ht.tsum_eq] using ht.summable.tsum_pos (mixedEnergy_nonneg S c hs.le) n hp

/-- Every nonzero finite complex superposition has strictly negative current at a left-half zero. -/
theorem quadraticCurrent_re_neg (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (hc : ∃ p ∈ S, c p≠0)
    (rho : RiemannGaussian.NontrivialZetaZero) (hs : rho.1.re<1/2) :
    (quadraticCurrent S c rho.1).re<0 := by
  obtain ⟨n,hn⟩ := exists_nonzero_mixed_prefix S c hS hc rho.1
  have hw : weight rho.1 (n+1)-weight rho.1 n<0 := by
    apply sub_neg.mpr
    exact Real.rpow_lt_rpow_of_neg (by positivity) (by push_cast; linarith)
      (by unfold exponent; linarith)
  have hp : mixedEnergy S c rho.1 n<0 :=
    mul_neg_of_neg_of_pos hw (sq_pos_of_pos (norm_pos_iff.mpr hn))
  have ht := (hasSum_mixedEnergy S c rho).neg
  have h := ht.summable.tsum_pos
    (fun n => neg_nonneg.mpr (mixedEnergy_nonpos S c hs.le n)) n (neg_pos.mpr hp)
  rw [ht.tsum_eq] at h
  linarith

/-- The entire quadratic current vanishes on the critical line before any zero specialization. -/
theorem quadraticCurrent_of_re_half (S : Finset ℕ) (c : ℕ → ℂ) {s : ℂ}
    (hs : s.re=1/2) : quadraticCurrent S c s=0 := by
  have hr : partner s=s := by
    apply Complex.ext <;> norm_num [partner, hs]
  simp [quadraticCurrent, variationCurrent, hr]

/-- Exact nullspace classification: away from the line only the zero coefficient vector is null. -/
theorem quadraticCurrent_eq_zero_iff (S : Finset ℕ) (c : ℕ → ℂ)
    (hS : ∀ p ∈ S, 0<p) (rho : RiemannGaussian.NontrivialZetaZero) :
    quadraticCurrent S c rho.1=0 ↔ rho.1.re=1/2 ∨ ∀ p ∈ S, c p=0 := by
  constructor
  · intro hz
    by_cases hr : rho.1.re=1/2
    · exact Or.inl hr
    · right
      by_contra hc
      push Not at hc
      rcases lt_or_gt_of_ne hr with hleft | hright
      · have h := quadraticCurrent_re_neg S c hS hc rho hleft
        rw [hz, Complex.zero_re] at h
        exact (lt_irrefl 0) h
      · have h := quadraticCurrent_re_pos S c hS hc rho hright
        rw [hz, Complex.zero_re] at h
        exact (lt_irrefl 0) h
  · rintro (hr | hc)
    · exact quadraticCurrent_of_re_half S c hr
    · unfold quadraticCurrent
      apply Finset.sum_eq_zero
      intro p hp
      simp only [hc p hp, zero_mul, Finset.sum_const_zero]

end RHTower.DeletionMixedCurrent
end
