import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorShell

/-!
# Cofinal cutoff commutators: uniform sieve density and the reciprocal-zeta current

Written with the flux atoms `F_d(y) = 2π d² e^{3y} e^{−πd² e^{2y}}`, the boundary profile is
`C_S = −Σ_{d | P} μ(d) F_d + E_S(1) F_1`; since `Σ_d F_d = H ≤ 1/2`, every `C_S` satisfies
`|C_S| ≤ 1`.  Along every prime exhaustion `S_N` (each prime eventually present, no growth
condition), `C_{S_N} → C_∞ = −Σ_{d ≥ 1} μ(d) F_d` uniformly on compact intervals; `C_∞` is bounded
by `1/2` and decays like a Gaussian at the physical end.

The rough-number density above the cutoff, `η_N = E_{S_N}(1) + sup_{X ≥ N} R_{S_N}(X)/X`, tends to
zero by Euler's reciprocal-prime divergence and the periodic count of integers coprime to a fixed
finite set.  With `|A_S(X)| ≤ X η` and `|H_{S,N}(t)| ≤ (Nη + 1) t`, the sieve discrepancy identity
gives the uniform estimate `sup_y |Δ_{S,N}(y)| ≤ C_h (η_{S,N} + 1/N)`.  Hence the simultaneous
prime/cutoff moving-boundary limit is always `C_∞`, locally uniformly, and every observation by an
`L¹` density against any measure (every finite complex Borel measure) converges to that of `C_∞`.
-/

open MeasureTheory Set Filter Topology ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## Squarefree products and the Möbius function -/

theorem moebius_prod_distinct_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    (moebius (∏ p ∈ T, p) : ℤ) = (-1) ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert p T hpT ih =>
    have hp := hT p (Finset.mem_insert_self p T)
    have hT' : ∀ q ∈ T, q.Prime := fun q hq => hT q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ T, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hT' q hq)).2 fun h => hpT (h ▸ hq)
    rw [Finset.prod_insert hpT, isMultiplicative_moebius.map_mul_of_coprime hcop,
      moebius_apply_prime hp, ih hT', Finset.card_insert_of_notMem hpT, pow_succ]
    ring

theorem prod_primes_injOn {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Set.InjOn (fun T : Finset ℕ => ∏ p ∈ T, p) (S.powerset : Set (Finset ℕ)) := fun T₁ h₁ T₂ h₂ h => by
  have h₁' : ∀ p ∈ T₁, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp h₁ hp)
  have h₂' : ∀ p ∈ T₂, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp h₂ hp)
  rw [← Nat.primeFactors_prod h₁', ← Nat.primeFactors_prod h₂']
  exact congrArg Nat.primeFactors h

/-- `Σ_{d | P} μ(d) f(d)` as a sum over the subsets of `S`, extended by zero to all `d`. -/
theorem sum_powerset_eq_tsum_moebius (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (f : ℕ → ℝ) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * f (∏ p ∈ T, p) =
      ∑' d : ℕ, if d ≠ 0 ∧ d.primeFactors ⊆ S then (moebius d : ℝ) * f d else 0 := by
  classical
  rw [tsum_eq_sum (s := S.powerset.image fun T => ∏ p ∈ T, p), Finset.sum_image (prod_primes_injOn hS)]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hT' : ∀ p ∈ T, p.Prime := fun p hp => hS p (Finset.mem_powerset.mp hT hp)
    have hne : (∏ p ∈ T, p) ≠ 0 := (Finset.prod_pos fun p hp => (hT' p hp).pos).ne'
    rw [if_pos ⟨hne, by rw [Nat.primeFactors_prod hT']; exact Finset.mem_powerset.mp hT⟩,
      show (moebius (∏ p ∈ T, p) : ℝ) = (((-1 : ℤ) ^ T.card : ℤ) : ℝ) by
        rw [moebius_prod_distinct_primes hT']]
    push_cast; ring
  · intro d hd
    split_ifs with h
    · by_cases hsq : Squarefree d
      · exact absurd (Finset.mem_image.2 ⟨d.primeFactors, Finset.mem_powerset.2 h.2,
          Nat.prod_primeFactors_of_squarefree hsq⟩) hd
      · rw [moebius_eq_zero_of_not_squarefree hsq]; simp
    · rfl

/-! ## Flux form of the boundary profile and the cofinal profile -/

theorem thetaFluxTerm_eq (y : ℝ) (n : ℕ) :
    thetaFluxTerm y n = 2 * Real.pi * (Real.exp (3 * y) *
      ((n : ℝ) ^ 2 * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * y))))) := by
  rw [thetaFluxTerm, rateFlux]; ring

/-- `C_S(y) = −Σ_{d|P} μ(d) F_d(y) + E_S(1) F_1(y)` with the flux atoms `F_d`. -/
theorem commutatorBoundaryProfile_eq_flux (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (y : ℝ) :
    commutatorBoundaryProfile S y =
      -(∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * thetaFluxTerm y (∏ p ∈ T, p)) +
        (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) * thetaFluxTerm y 1 := by
  rw [commutatorBoundaryProfile_eq S hS]
  simp only [thetaFluxTerm_eq, Nat.cast_one, one_pow, one_mul, mul_one]
  push_cast
  rw [mul_sub, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun T _ => by ring
  · ring

/-- **(4) The cofinal boundary current** `C_∞(y) = −2π e^{3y} Σ_{d ≥ 1} μ(d) d² e^{−πd² e^{2y}}`. -/
def cofinalBoundaryProfile (y : ℝ) : ℝ := -∑' d : ℕ, (moebius d : ℝ) * thetaFluxTerm y d

theorem abs_moebius_mul_thetaFluxTerm_le (y : ℝ) (d : ℕ) :
    |(moebius d : ℝ) * thetaFluxTerm y d| ≤ thetaFluxTerm y d := by
  rw [abs_mul, abs_of_nonneg (thetaFluxTerm_nonneg y d)]
  exact mul_le_of_le_one_left (thetaFluxTerm_nonneg y d) (by exact_mod_cast abs_moebius_le_one)

theorem summable_moebius_mul_thetaFluxTerm (y : ℝ) :
    Summable fun d : ℕ => (moebius d : ℝ) * thetaFluxTerm y d :=
  Summable.of_norm_bounded (summable_thetaFluxTerm y) fun d =>
    (Real.norm_eq_abs _).trans_le (abs_moebius_mul_thetaFluxTerm_le y d)

theorem tsum_thetaFluxTerm_le_half (y : ℝ) : ∑' d : ℕ, thetaFluxTerm y d ≤ 1 / 2 := by
  have h := indexFluxPotential_univ_le_half y
  rwa [indexFluxPotential, tsum_univ (f := fun n => thetaFluxTerm y n)] at h

/-- `C_∞` is bounded: `|C_∞(y)| ≤ 1/2` (in particular `O(1)` at the cusp). -/
theorem abs_cofinalBoundaryProfile_le (y : ℝ) : |cofinalBoundaryProfile y| ≤ 1 / 2 := by
  rw [cofinalBoundaryProfile, abs_neg]
  refine ((norm_tsum_le_tsum_norm (summable_moebius_mul_thetaFluxTerm y).norm).trans ?_).trans
    (tsum_thetaFluxTerm_le_half y)
  exact (summable_moebius_mul_thetaFluxTerm y).norm.tsum_le_tsum
    (fun d => (Real.norm_eq_abs _).trans_le (abs_moebius_mul_thetaFluxTerm_le y d))
    (summable_thetaFluxTerm y)

theorem prod_one_sub_inv_mem_Icc (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    0 ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ∧ ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ≤ 1 := by
  have h : ∀ p ∈ S, 0 ≤ 1 - (p : ℝ)⁻¹ ∧ 1 - (p : ℝ)⁻¹ ≤ 1 := fun p hp => by
    have : (1 : ℝ) ≤ p := by exact_mod_cast (hS p hp).one_lt.le
    exact ⟨sub_nonneg.2 (inv_le_one_of_one_le₀ this), sub_le_self _ (inv_nonneg.2 (by linarith))⟩
  exact ⟨Finset.prod_nonneg fun p hp => (h p hp).1, Finset.prod_le_one (fun p hp => (h p hp).1)
    fun p hp => (h p hp).2⟩

/-- **Uniform bound** `sup_{S,y} |C_S(y)| ≤ 1`. -/
theorem abs_commutatorBoundaryProfile_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (y : ℝ) :
    |commutatorBoundaryProfile S y| ≤ 1 := by
  classical
  rw [commutatorBoundaryProfile_eq_flux S hS]
  have hsum : |∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card * thetaFluxTerm y (∏ p ∈ T, p)| ≤ 1 / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∑ T ∈ S.powerset, |(-1 : ℝ) ^ T.card * thetaFluxTerm y (∏ p ∈ T, p)| ≤
        ∑' d : ℕ, thetaFluxTerm y d := by
      rw [show ∑ T ∈ S.powerset, |(-1 : ℝ) ^ T.card * thetaFluxTerm y (∏ p ∈ T, p)| =
          ∑ d ∈ S.powerset.image (fun T => ∏ p ∈ T, p), thetaFluxTerm y d by
        rw [Finset.sum_image (prod_primes_injOn hS)]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (thetaFluxTerm_nonneg _ _)]]
      exact (summable_thetaFluxTerm y).sum_le_tsum _ fun d _ => thetaFluxTerm_nonneg y d
    exact hle.trans (tsum_thetaFluxTerm_le_half y)
  have hE := prod_one_sub_inv_mem_Icc S hS
  have h1 : thetaFluxTerm y 1 ≤ 1 / 2 :=
    ((summable_thetaFluxTerm y).le_tsum 1 fun d _ => thetaFluxTerm_nonneg y d).trans
      (tsum_thetaFluxTerm_le_half y)
  have h10 := thetaFluxTerm_nonneg y 1
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_mul, abs_of_nonneg hE.1, abs_of_nonneg h10]
  nlinarith

/-- Gaussian decay of `C_∞` at the physical end. -/
theorem abs_cofinalBoundaryProfile_le_gaussian {y : ℝ} (hy : 0 ≤ y) :
    |cofinalBoundaryProfile y| ≤ (2 * Real.pi * ∑' d : ℕ, (d : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * (d : ℝ) ^ 2)) *
      (Real.exp (3 * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := by
  have hu : 1 ≤ Real.exp (2 * y) := Real.one_le_exp (by linarith)
  have hsum := summable_pow_mul_exp_neg_nat_sq 2 (show 0 < Real.pi / 2 by positivity)
  have hbound : ∀ d : ℕ, thetaFluxTerm y d ≤ (2 * Real.pi * (Real.exp (3 * y) *
      Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) *
        ((d : ℝ) ^ 2 * Real.exp (-(Real.pi / 2) * (d : ℝ) ^ 2)) := fun d => by
    rw [thetaFluxTerm_eq]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hexp : Real.exp (-(Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * y))) ≤
        Real.exp (-(Real.pi / 2 * Real.exp (2 * y))) * Real.exp (-(Real.pi / 2) * (d : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
      have key : Real.exp (2 * y) / 2 + (d : ℝ) ^ 2 / 2 ≤ (d : ℝ) ^ 2 * Real.exp (2 * y) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hd2) (sub_nonneg.2 hu)]
      nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left key Real.pi_pos.le]
    have := mul_le_mul_of_nonneg_left hexp (by positivity :
      (0 : ℝ) ≤ 2 * Real.pi * Real.exp (3 * y) * (d : ℝ) ^ 2)
    nlinarith [this]
  rw [cofinalBoundaryProfile, abs_neg]
  refine ((norm_tsum_le_tsum_norm (summable_moebius_mul_thetaFluxTerm y).norm).trans ?_)
  refine ((summable_moebius_mul_thetaFluxTerm y).norm.tsum_le_tsum (fun d =>
    ((Real.norm_eq_abs _).trans_le (abs_moebius_mul_thetaFluxTerm_le y d)).trans (hbound d))
      (hsum.mul_left _)).trans (le_of_eq ?_)
  rw [tsum_mul_left]
  ring

theorem prod_one_sub_inv_le_of_subset {F S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hFS : F ⊆ S) :
    ∏ p ∈ S, (1 - (p : ℝ)⁻¹) ≤ ∏ p ∈ F, (1 - (p : ℝ)⁻¹) := by
  classical
  rw [← Finset.prod_sdiff hFS]
  have h1 := prod_one_sub_inv_mem_Icc (S \ F) fun p hp => hS p (Finset.mem_sdiff.1 hp).1
  have h2 := prod_one_sub_inv_mem_Icc F fun p hp => hS p (hFS hp)
  nlinarith [h1.1, h1.2, h2.1]

/-- Euler's divergence: `E_{S_N}(1) → 0` along every prime exhaustion. -/
theorem PrimeExhaustion.tendsto_prod_one_sub_inv {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun N => ∏ p ∈ S N, (1 - (p : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun M : ℕ => ∏ p ∈ (M + 1).primesBelow, (1 - (p : ℝ)⁻¹)) atTop (𝓝 0) := by
    refine (tendsto_prod_one_sub_inv_primesBelow.inv_tendsto_atTop).congr fun M => ?_
    rw [Pi.inv_apply, ← Finset.prod_inv_distrib]
    simp only [inv_inv]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (hbase.eventually (gt_mem_nhds hε)).exists
  have hsub : ∀ᶠ N in atTop, ∀ p ∈ (M + 1).primesBelow, p ∈ S N :=
    (Filter.eventually_all_finset _).2 fun p hp => hS.eventually_mem p (Nat.prime_of_mem_primesBelow hp)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsub
  refine ⟨N₀, fun N hN => ?_⟩
  have hle := prod_one_sub_inv_le_of_subset (hS.prime N) (fun p hp => hN₀ N hN p hp)
  have h0 := (prod_one_sub_inv_mem_Icc (S N) (hS.prime N)).1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hle.trans_lt hM

/-- **(4) Cofinal classification.**  Along every prime exhaustion `C_{S_N} → C_∞` uniformly on
compact intervals. -/
theorem PrimeExhaustion.tendstoUniformlyOn_commutatorBoundaryProfile {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (R : ℝ) :
    TendstoUniformlyOn (fun N => commutatorBoundaryProfile (S N)) cofinalBoundaryProfile atTop
      (Icc (-R) R) := by
  classical
  set m : ℕ → ℝ := fun d => 2 * Real.pi * (Real.exp (3 * R) *
    ((d : ℝ) ^ 2 * Real.exp (-(Real.pi * Real.exp (-2 * R)) * (d : ℝ) ^ 2)))
  have hm : Summable m := ((summable_pow_mul_exp_neg_nat_sq 2 (by positivity :
    0 < Real.pi * Real.exp (-2 * R))).mul_left _).mul_left _
  have hFm : ∀ y ∈ Icc (-R) R, ∀ d : ℕ, thetaFluxTerm y d ≤ m d := fun y hy d => by
    rw [thetaFluxTerm_eq]
    simp only [m]
    have h3 : Real.exp (3 * y) ≤ Real.exp (3 * R) := Real.exp_le_exp.2 (by linarith [hy.2])
    have h2 : Real.exp (-2 * R) ≤ Real.exp (2 * y) := Real.exp_le_exp.2 (by linarith [hy.1])
    have hexp : Real.exp (-(Real.pi * (d : ℝ) ^ 2 * Real.exp (2 * y))) ≤
        Real.exp (-(Real.pi * Real.exp (-2 * R)) * (d : ℝ) ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos, sq_nonneg (d : ℝ), mul_le_mul_of_nonneg_left h2
        (by positivity : (0 : ℝ) ≤ Real.pi * (d : ℝ) ^ 2)]
    gcongr
  -- tails of the majorant
  have htail : Tendsto (fun M : ℕ => ∑' d : ℕ, if M < d then m d else 0) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (f := fun (M : ℕ) (d : ℕ) =>
      if M < d then m d else 0) (g := fun _ => (0 : ℝ)) (bound := m) hm
      (fun d => tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop d] with M hM
        rw [if_neg (by omega)]))
      (Eventually.of_forall fun M d => by
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        · rw [norm_zero]; positivity)
    simpa using h
  have hE := hS.tendsto_prod_one_sub_inv
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := (htail.eventually (gt_mem_nhds (half_pos hε))).exists
  have hprimes : ∀ᶠ N in atTop, ∀ p ∈ (Finset.range (M + 1)).filter Nat.Prime, p ∈ S N :=
    (Filter.eventually_all_finset _).2 fun p hp => hS.eventually_mem p (Finset.mem_filter.1 hp).2
  filter_upwards [hprimes, hE.eventually (gt_mem_nhds hε)] with N hN hEN y hy
  set F := fun d : ℕ => (moebius d : ℝ) * thetaFluxTerm y d
  have hFb : ∀ d, ‖F d‖ ≤ thetaFluxTerm y d := fun d =>
    (Real.norm_eq_abs _).trans_le (abs_moebius_mul_thetaFluxTerm_le y d)
  set c : ℕ → Prop := fun d => d ≠ 0 ∧ d.primeFactors ⊆ S N
  have hin : Summable fun d => if c d then F d else 0 :=
    Summable.of_norm_bounded (summable_thetaFluxTerm y) fun d => by
      split_ifs
      · exact hFb d
      · rw [norm_zero]; exact thetaFluxTerm_nonneg y d
  have hout : Summable fun d => if c d then 0 else F d :=
    Summable.of_norm_bounded (summable_thetaFluxTerm y) fun d => by
      split_ifs
      · rw [norm_zero]; exact thetaFluxTerm_nonneg y d
      · exact hFb d
  have hsplit : ∑' d, F d = (∑' d, if c d then F d else 0) + ∑' d, if c d then 0 else F d := by
    rw [← hin.tsum_add hout]
    exact tsum_congr fun d => by split_ifs <;> simp
  have hdiff : cofinalBoundaryProfile y - commutatorBoundaryProfile (S N) y =
      -(∑' d, if c d then 0 else F d) - (∏ p ∈ S N, (1 - (p : ℝ)⁻¹)) * thetaFluxTerm y 1 := by
    rw [cofinalBoundaryProfile, commutatorBoundaryProfile_eq_flux _ (hS.prime N),
      sum_powerset_eq_tsum_moebius _ (hS.prime N), hsplit]
    ring
  have hm0 : ∀ d, 0 ≤ m d := fun d => by simp only [m]; positivity
  have hle : ∀ d, ‖if c d then 0 else F d‖ ≤ if M < d then m d else 0 := fun d => by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have : F 0 = 0 := by simp [F, thetaFluxTerm_zero]
      split_ifs <;> simp [this, hm0]
    by_cases hc : c d
    · rw [if_pos hc, norm_zero]; split_ifs
      · exact hm0 d
      · exact le_rfl
    · rw [if_neg hc]
      by_cases hMd : M < d
      · rw [if_pos hMd]; exact (hFb d).trans (hFm y hy d)
      · exfalso
        refine hc ⟨hd.ne', fun p hp => ?_⟩
        have hpd := Nat.le_of_dvd hd (Nat.dvd_of_mem_primeFactors hp)
        exact hN p (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
          Nat.prime_of_mem_primeFactors hp⟩)
  have htail : |∑' d, if c d then 0 else F d| ≤ ∑' d : ℕ, if M < d then m d else 0 :=
    (norm_tsum_le_tsum_norm hout.norm).trans (hout.norm.tsum_le_tsum hle
      (hm.of_nonneg_of_le (fun d => by split_ifs <;> [exact hm0 d; exact le_rfl])
        fun d => by split_ifs <;> [exact le_rfl; exact hm0 d]))
  have h1 : thetaFluxTerm y 1 ≤ 1 / 2 :=
    ((summable_thetaFluxTerm y).le_tsum 1 fun d _ => thetaFluxTerm_nonneg y d).trans
      (tsum_thetaFluxTerm_le_half y)
  have hE0 := (prod_one_sub_inv_mem_Icc (S N) (hS.prime N)).1
  rw [Real.dist_eq, hdiff]
  calc |-(∑' d, if c d then 0 else F d) - (∏ p ∈ S N, (1 - (p : ℝ)⁻¹)) * thetaFluxTerm y 1|
      ≤ (∑' d : ℕ, if M < d then m d else 0) + (∏ p ∈ S N, (1 - (p : ℝ)⁻¹)) * (1 / 2) := by
        refine (abs_sub _ _).trans (add_le_add (by rw [abs_neg]; exact htail) ?_)
        rw [abs_mul, abs_of_nonneg hE0, abs_of_nonneg (thetaFluxTerm_nonneg y 1)]
        exact mul_le_mul_of_nonneg_left h1 hE0
    _ < ε / 2 + ε * (1 / 2) := by
        linarith [mul_lt_mul_of_pos_right hEN (by norm_num : (0:ℝ) < 1 / 2)]
    _ = ε := by ring

/-! ## Uniform rough-number density above the cutoff -/

/-- `η_{S,N} = E_S(1) + sup_{X ≥ N} R_S(X)/X`. -/
def roughDensity (S : Finset ℕ) (N : ℕ) : ℝ :=
  ∏ p ∈ S, (1 - (p : ℝ)⁻¹) + ⨆ X : Ici (N : ℝ), (roughCount S X : ℝ) / X

theorem roughCount_le {S : Finset ℕ} {X : ℝ} (hX : 0 ≤ X) : (roughCount S X : ℝ) ≤ X := by
  have h1 : roughCount S X ≤ ⌊X⌋₊ := by
    rw [roughCount]
    exact (Finset.card_filter_le _ _).trans (by simp)
  exact (Nat.cast_le.2 h1).trans (Nat.floor_le hX)

theorem roughCount_div_le_one (S : Finset ℕ) {X : ℝ} (hX : 0 ≤ X) : (roughCount S X : ℝ) / X ≤ 1 := by
  rcases hX.lt_or_eq with h | h
  · rw [div_le_one h]; exact roughCount_le hX
  · rw [← h, div_zero]; exact zero_le_one

theorem bddAbove_roughCount_div (S : Finset ℕ) (N : ℕ) :
    BddAbove (range fun X : Ici (N : ℝ) => (roughCount S X : ℝ) / X) :=
  ⟨1, by rintro _ ⟨X, rfl⟩; exact roughCount_div_le_one S ((Nat.cast_nonneg N).trans X.2)⟩

theorem roughCount_div_le_iSup (S : Finset ℕ) (N : ℕ) {X : ℝ} (hX : (N : ℝ) ≤ X) :
    (roughCount S X : ℝ) / X ≤ ⨆ X : Ici (N : ℝ), (roughCount S X : ℝ) / X :=
  le_ciSup (bddAbove_roughCount_div S N) ⟨X, hX⟩

theorem roughDensity_nonneg (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) : 0 ≤ roughDensity S N :=
  add_nonneg (prod_one_sub_inv_mem_Icc S hS).1 ((div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)).trans
    (roughCount_div_le_iSup S N le_rfl))

theorem roughCount_anti {F S : Finset ℕ} (hFS : F ⊆ S) (X : ℝ) : roughCount S X ≤ roughCount F X :=
  Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, fun p hp => hm.2 p (hFS hp)⟩

/-- **(3d)** Along every prime exhaustion the rough-number density vanishes uniformly above the
cutoff: `η_N = E_{S_N}(1) + sup_{X ≥ N} R_{S_N}(X)/X → 0`. -/
theorem PrimeExhaustion.tendsto_roughDensity {S : ℕ → Finset ℕ} (hS : PrimeExhaustion S) :
    Tendsto (fun N => roughDensity (S N) N) atTop (𝓝 0) := by
  have hbase : Tendsto (fun M : ℕ => ∏ p ∈ (M + 1).primesBelow, (1 - (p : ℝ)⁻¹)) atTop (𝓝 0) := by
    refine (tendsto_prod_one_sub_inv_primesBelow.inv_tendsto_atTop).congr fun M => ?_
    rw [Pi.inv_apply, ← Finset.prod_inv_distrib]
    simp only [inv_inv]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := (hbase.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  set F := (M + 1).primesBelow
  have hFp : ∀ p ∈ F, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow hp
  have hsub : ∀ᶠ N in atTop, ∀ p ∈ F, p ∈ S N :=
    (Filter.eventually_all_finset _).2 fun p hp => hS.eventually_mem p (hFp p hp)
  have hlim : Tendsto (fun N : ℕ => (F.powerset.card : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hsub.and ((hlim.eventually (gt_mem_nhds
    (by positivity : 0 < ε / 3))).and (eventually_ge_atTop 1)))
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hFS, hpow, hN1⟩ := hN₀ N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hE := prod_one_sub_inv_le_of_subset (hS.prime N) hFS
  have hEF0 := (prod_one_sub_inv_mem_Icc F hFp).1
  have hsup : (⨆ X : Ici (N : ℝ), (roughCount (S N) X : ℝ) / X) ≤ ε / 3 + ε / 3 := by
    refine ciSup_le fun X => ?_
    have hX : (N : ℝ) ≤ X := X.2
    have hX0 : 0 < (X : ℝ) := hNR.trans_le hX
    have h1 : (roughCount (S N) X : ℝ) ≤ roughCount F X := by exact_mod_cast roughCount_anti hFS X
    have h2 := roughDiscrepancy_eq F hFp hX0.le
    have h3 := abs_roughDiscrepancy_le F X
    rw [div_le_iff₀ hX0]
    have h4 : (F.powerset.card : ℝ) ≤ ε / 3 * X := by
      have := (div_lt_iff₀ hNR).1 hpow
      nlinarith
    nlinarith [abs_le.1 h3]
  have h0 := roughDensity_nonneg (S N) (hS.prime N) N
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0, roughDensity]
  linarith

theorem abs_roughDiscrepancy_le_mul_roughDensity (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 0 < N) {X : ℝ} (hX : (N : ℝ) ≤ X) : |roughDiscrepancy S X| ≤ X * roughDensity S N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hX0 : 0 < X := hNR.trans_le hX
  rw [roughDiscrepancy_eq S hS hX0.le]
  have hE := prod_one_sub_inv_mem_Icc S hS
  have hR := roughCount_div_le_iSup S N hX
  rw [div_le_iff₀ hX0] at hR
  rw [roughDensity, mul_add]
  have : (0 : ℝ) ≤ roughCount S X := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hX0.le hE.1]

theorem card_filter_prod_lt_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {t : ℝ} (ht : 0 ≤ t) :
    ((S.powerset.filter fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t).card : ℝ) ≤ t := by
  classical
  have hinj := prod_primes_injOn hS
  have hcard : (S.powerset.filter fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t).card =
      ((S.powerset.filter fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t).image fun T => ∏ p ∈ T, p).card :=
    (Finset.card_image_of_injOn (hinj.mono (by
      intro T hT; exact (Finset.mem_filter.1 hT).1))).symm
  have hsub : ((S.powerset.filter fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t).image fun T => ∏ p ∈ T, p) ⊆
      Finset.Icc 1 ⌊t⌋₊ := by
    intro d hd
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨hTS, hlt⟩ := Finset.mem_filter.1 hT
    have hpos : 0 < ∏ p ∈ T, p :=
      Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.1 hTS hp)).pos
    exact Finset.mem_Icc.2 ⟨hpos, Nat.le_floor hlt.le⟩
  rw [hcard]
  calc (((S.powerset.filter _).image _).card : ℝ) ≤ (Finset.Icc 1 ⌊t⌋₊).card := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ⌊t⌋₊ := by simp
    _ ≤ t := Nat.floor_le ht

theorem abs_roughTailDiscrepancy_le_density (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {N : ℕ}
    (hN : 0 < N) {t : ℝ} (ht : 1 ≤ t) :
    |roughTailDiscrepancy S N t| ≤ (N * roughDensity S N + 1) * t := by
  classical
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : roughTailDiscrepancy S N t = roughDiscrepancy S (N * t) -
      ∑ T ∈ S.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t),
        (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ)) := by
    rw [roughTailDiscrepancy, roughDiscrepancy, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : t ≤ ((∏ p ∈ T, p : ℕ) : ℝ)
    · rw [Set.indicator_of_mem (show t ∈ Iic _ from h), if_neg (not_lt.2 h), sub_zero]
    · rw [Set.indicator_of_notMem (show t ∉ Iic _ from h), if_pos (not_le.1 h), sub_self]
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  have hA := abs_roughDiscrepancy_le_mul_roughDensity S hS hN
    (show (N : ℝ) ≤ N * t by nlinarith)
  have hB : |∑ T ∈ S.powerset.filter (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < t),
      (-1 : ℝ) ^ T.card * Int.fract (N * t / (∏ p ∈ T, p : ℕ))| ≤ t := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun T _ => ?_).trans
      (le_of_eq_of_le (by rw [Finset.sum_const, nsmul_eq_mul, mul_one])
        (card_filter_prod_lt_le S hS (by linarith))))
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  nlinarith

/-- **(3e) Uniform joint-limit estimate.**  There is a constant `C_h` such that for every finite
prime set `S`, every `N ≥ 1` and every `y`, `|Δ_{S,N}(y)| ≤ C_h (η_{S,N} + 1/N)`. -/
theorem exists_abs_movingCommutatorDensity_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ {N : ℕ}, 0 < N → ∀ y : ℝ,
      |movingCommutatorDensity S N y - commutatorBoundaryProfile S y| ≤
        C * (roughDensity S N + 1 / N) := by
  obtain ⟨K, hK⟩ := exists_abs_mul_thetaCuspSeed_le
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hM0 : 0 ≤ seedDerivMoment := setIntegral_nonneg measurableSet_Ioi fun u hu =>
    mul_nonneg (le_of_lt hu) (abs_nonneg _)
  refine ⟨K + seedDerivMoment, add_nonneg hK0 hM0, fun S hS N hN y => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hη := roughDensity_nonneg S hS N
  have h := abs_movingCommutatorDensity_sub_le S hS hN y hK
    (B := N * roughDensity S N + 1) (fun t ht => abs_roughTailDiscrepancy_le_density S hS hN ht)
    (by positivity)
  have hA : |roughDiscrepancy S N| ≤ N * roughDensity S N :=
    abs_roughDiscrepancy_le_mul_roughDensity S hS hN le_rfl
  refine h.trans ?_
  have e1 : K * |roughDiscrepancy S N| / N ≤ K * roughDensity S N := by
    rw [div_le_iff₀ hNR]; nlinarith [mul_le_mul_of_nonneg_left hA hK0]
  have e2 : (N * roughDensity S N + 1) * seedDerivMoment / N =
      seedDerivMoment * (roughDensity S N + 1 / N) := by field_simp
  rw [e2]
  have hK1 : 0 ≤ K * (1 / N) := by positivity
  have expand : (K + seedDerivMoment) * (roughDensity S N + 1 / N) =
      K * roughDensity S N + K * (1 / N) + seedDerivMoment * (roughDensity S N + 1 / N) := by ring
  linarith

/-- Along every prime exhaustion the joint error vanishes uniformly on the whole line. -/
theorem PrimeExhaustion.tendstoUniformly_movingCommutatorDensity_sub {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) :
    TendstoUniformly (fun N y => movingCommutatorDensity (S N) N y -
      commutatorBoundaryProfile (S N) y) (fun _ => 0) atTop := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_movingCommutatorDensity_sub_le
  have hlim : Tendsto (fun N : ℕ => C * (roughDensity (S N) N + 1 / N)) atTop (𝓝 0) := by
    simpa using (hS.tendsto_roughDensity.add tendsto_one_div_atTop_nhds_zero_nat).const_mul C
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with N hN hN1 y
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact (hC (S N) (hS.prime N) hN1 y).trans_lt hN

/-- **The simultaneous prime/cutoff moving-boundary limit is always `C_∞`**, locally uniformly. -/
theorem PrimeExhaustion.tendstoUniformlyOn_movingCommutatorDensity {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) (R : ℝ) :
    TendstoUniformlyOn (fun N y => movingCommutatorDensity (S N) N y) cofinalBoundaryProfile atTop
      (Icc (-R) R) := by
  have h1 := hS.tendstoUniformlyOn_commutatorBoundaryProfile R
  have h2 := (hS.tendstoUniformly_movingCommutatorDensity_sub).tendstoUniformlyOn (s := Icc (-R) R)
  have h3 := h1.add h2
  have h4 : (cofinalBoundaryProfile + fun _ : ℝ => (0 : ℝ)) = cofinalBoundaryProfile := by
    funext y; simp
  rw [h4] at h3
  refine h3.congr (Eventually.of_forall fun N y _ => ?_)
  show commutatorBoundaryProfile (S N) y +
    (movingCommutatorDensity (S N) N y - commutatorBoundaryProfile (S N) y) = _
  ring

theorem continuous_cutoffCommutatorSource (S : Finset ℕ) (N : ℕ) :
    Continuous (cutoffCommutatorSource S N) :=
  (continuous_thetaPrimeDeletion S (continuous_finsetSum _ fun n _ =>
    continuous_thetaCuspSourceTerm n)).sub
      (continuous_finsetSum _ fun m _ => continuous_thetaCuspSourceTerm m)

theorem continuous_movingCommutatorDensity (S : Finset ℕ) (N : ℕ) :
    Continuous (movingCommutatorDensity S N) :=
  (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
    ((continuous_cutoffCommutatorSource S N).comp (continuous_id.sub continuous_const))

/-- **(3f) Every finite-variation observation sees the reciprocal-zeta current.**  For every
measure `μ` and every `h ∈ L¹(μ)` (in particular every finite complex Borel measure `h·|ν|`),
`∫ e^{(y−log N)/2} C_{S_N,N}(y − log N) h(y) dμ(y) → ∫ C_∞ h dμ` along every prime exhaustion. -/
theorem PrimeExhaustion.tendsto_integral_movingCommutatorDensity_mul {S : ℕ → Finset ℕ}
    (hS : PrimeExhaustion S) {μ : Measure ℝ} {h : ℝ → ℂ} (hh : Integrable h μ) :
    Tendsto (fun N => ∫ y, (movingCommutatorDensity (S N) N y : ℂ) * h y ∂μ) atTop
      (𝓝 (∫ y, (cofinalBoundaryProfile y : ℂ) * h y ∂μ)) := by
  have hunif := hS.tendstoUniformly_movingCommutatorDensity_sub
  rw [Metric.tendstoUniformly_iff] at hunif
  refine tendsto_integral_filter_of_dominated_convergence (fun y => 2 * ‖h y‖)
    (Eventually.of_forall fun N => ((Complex.continuous_ofReal.comp
      (continuous_movingCommutatorDensity (S N) N)).aestronglyMeasurable).mul hh.aestronglyMeasurable)
    ?_ (hh.norm.const_mul 2) (ae_of_all _ fun y => ?_)
  · filter_upwards [hunif 1 one_pos] with N hN
    refine ae_of_all _ fun y => ?_
    have hΔ := hN y
    rw [Real.dist_eq, zero_sub, abs_neg] at hΔ
    have hC := abs_commutatorBoundaryProfile_le (S N) (hS.prime N) y
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |movingCommutatorDensity (S N) N y|
        = |commutatorBoundaryProfile (S N) y +
            (movingCommutatorDensity (S N) N y - commutatorBoundaryProfile (S N) y)| := by ring_nf
      _ ≤ 1 + 1 := (abs_add_le _ _).trans (add_le_add hC hΔ.le)
      _ = 2 := by norm_num
  · have hy : y ∈ Icc (-|y|) |y| := abs_le.1 le_rfl
    have h1 := (hS.tendstoUniformlyOn_movingCommutatorDensity |y|).tendsto_at hy
    exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const (h y)

end

end RHTower
